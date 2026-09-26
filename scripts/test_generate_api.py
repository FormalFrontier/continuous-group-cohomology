#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only refusal and source-only replay checks for the frozen native adapter.

Adapted by worker-b Hive Task hive-request-cca415cd0c40e1f555e1a385d1289c4864a3aee4
(UID 39f509ab-c2e1-4b59-8573-31cc7b920eb9) from accepted
profinite-groups 79c4bcf23fa81319f9e3936be3f804421c7b98c3, authored by
worker-b Task hive-request-49578d0143b3fe26e93ee6e54fa1752f1d60bc26
(UID e4f64178-9024-4fe9-8eba-f63c724e7497), in turn from the accepted
finite-group Tate adapter by worker-b Task
hive-request-381dc6f93292eb39ea2d5b25f09baacdc8b20d9e
(UID cd8c84f8-2dbf-4399-9c70-1de364ffa99f).
"""

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import generate_api as api


ROOT = Path(__file__).resolve().parent.parent
PARSER = argparse.ArgumentParser(description=__doc__)
PARSER.add_argument("--native-data", type=Path, required=True)


class NativeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {path: (ROOT / path).read_bytes() for path in api.SOURCE_INPUT_SHA256}
        cls.original = {
            module: (ARGS.native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
            for module in api.MODULES
        }
        cls.records = {module: json.loads(raw) for module, raw in cls.original.items()}
        api.check_snapshot(api.SOURCE, cls.sources)
        api.validate(cls.records, cls.original, cls.sources, api.SOURCE)

    def corrupt(self, modify, diagnostic):
        records = copy.deepcopy(self.records)
        sources = dict(self.sources)
        modify(records, sources)
        raw = {module: json.dumps(record, ensure_ascii=False, sort_keys=True,
                                  separators=(",", ":")).encode("utf-8")
               for module, record in records.items()}
        with self.assertRaisesRegex(ValueError, diagnostic):
            api.render(records, raw, sources, api.SOURCE)

    def command(self, archive, native, check=True, optimized=False, tool=api.TOOL):
        args = [sys.executable, "-I", "-O" if optimized else "-B",
                str(archive / "scripts/generate_api.py"),
                "--native-data", str(native), "--source-revision", api.SOURCE,
                "--docgen-revision", tool]
        if check:
            args.append("--check")
        return subprocess.run(args, cwd=archive, env={"PATH": "/no-git-binary"},
                              capture_output=True, text=True, check=False)

    def archive(self, base):
        archive = base / "source-only"
        (archive / "scripts").mkdir(parents=True)
        (archive / "docs").mkdir()
        for path, raw in self.sources.items():
            target = archive / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        for path in ("scripts/generate_api.py", "scripts/test_generate_api.py",
                     "docs/README.md", "docs/attribution.md", "README.md"):
            (archive / path).write_bytes((ROOT / path).read_bytes())
        native = base / "external-native"
        native.mkdir()
        for module, raw in self.original.items():
            (native / ("declaration-data-" + module + ".bmp")).write_bytes(raw)
        return archive, native

    def test_manifest_and_full_unmodified_native(self):
        markdown, raw = api.render(self.records, self.original, self.sources, api.SOURCE)
        manifest = json.loads(raw)
        self.assertEqual(manifest["production_modules"], list(api.PRODUCTION))
        self.assertEqual(manifest["checked_use_client_modules"], list(api.CLIENTS))
        self.assertEqual(manifest["native_record_sha256"], api.NATIVE_RECORD_SHA256)
        self.assertEqual(manifest["inputs"], api.SOURCE_INPUT_SHA256)
        self.assertEqual(manifest["api_sha256"], api.digest(markdown))
        self.assertEqual(len(manifest["production_declarations"]),
                         sum(api.COUNTS[module] for module in api.PRODUCTION))
        self.assertEqual(len(manifest["checked_use_client_declarations"]),
                         sum(api.COUNTS[module] for module in api.CLIENTS))
        self.assertEqual(len(manifest["instance_table"]),
                         sum(len(instances) for instances in api.EXPECTED_INSTANCES.values()))
        self.assertEqual((ROOT / "docs/API.md").read_bytes(), markdown)
        self.assertEqual((ROOT / "docs/api-manifest.json").read_bytes(), raw)
        self.assertNotIn(b"example.invalid", markdown)
        self.assertFalse(manifest["proof_certification"] or manifest["release_acceptance"])

    def test_missing_extra_duplicate_name_kind_and_links(self):
        module = next(module for module in api.MODULES if api.COUNTS[module] > 1)
        first = self.records[module]["declarations"][0]
        controls = [
            ("missing/extra native declaration", lambda rows: rows.pop()),
            ("missing/extra native declaration", lambda rows: rows.append(copy.deepcopy(first))),
            ("duplicate native declaration", lambda rows: rows.__setitem__(1, copy.deepcopy(first))),
            ("wrong native name/kind", lambda rows: rows[0]["info"].__setitem__("kind", "axiom")),
            ("wrong native name/kind", lambda rows: rows[0]["info"].__setitem__("name", "Bad Name")),
            ("native source module/revision/path differs", lambda rows: rows[0]["info"].__setitem__(
                "sourceLink", "https://example.invalid/commit/main/Other.lean")),
            ("native self link differs", lambda rows: rows[0]["info"].__setitem__(
                "docLink", "./Other.html#Other")),
            ("invalid native source line", lambda rows: rows[0]["info"].__setitem__("line", 0)),
        ]
        for diagnostic, change in controls:
            with self.subTest(diagnostic=diagnostic):
                self.corrupt(lambda r, s: change(r[module]["declarations"]), diagnostic)
        self.corrupt(lambda r, s: r[module].__setitem__("name", "Other"),
                     "native module name differs")
        self.corrupt(lambda r, s: r[module]["imports"].append("Other"),
                     "native raw record differs")
        self.corrupt(lambda r, s: r.__setitem__("Extra", {}),
                     "native module inventory differs")
        self.corrupt(lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
            "kind", "structure" if first["info"]["kind"] != "structure" else "theorem"),
            "native signature identity/format differs|native declaration kinds differ")

    def test_instance_rows_and_generated_anchors(self):
        module = next(module for module in api.MODULES if api.EXPECTED_INSTANCES.get(module))
        for change, diagnostic in (
            (lambda r: r[module]["instances"].pop(), "missing/extra/wrong native instance table"),
            (lambda r: r[module]["instances"].append(copy.deepcopy(r[module]["instances"][0])),
             "duplicate native instance row"),
            (lambda r: r[module]["instances"][0].__setitem__("className", "Other"),
             "missing/extra/wrong native instance table"),
            (lambda r: r[module]["instances"][0].__setitem__("typeNames", ["Other"]),
             "missing/extra/wrong native instance table"),
        ):
            with self.subTest(diagnostic=diagnostic):
                self.corrupt(lambda r, s: change(r), diagnostic)
        name = next(iter(api.GENERATED_ANCHORS))
        generated_module = next(module for module, record in self.records.items()
                                if name in {row["info"]["name"] for row in record["declarations"]})
        self.corrupt(lambda r, s: next(row for row in r[generated_module]["declarations"]
                                           if row["info"]["name"] == name)["info"].__setitem__(
            "line", api.GENERATED_ANCHORS[name][0] + 1), "generated source anchor mismatch")

    def test_active_html_docstrings_and_raw_bytes(self):
        module = next(module for module in api.MODULES if api.COUNTS[module])
        for fragment in ("<script>alert(1)</script>", "<img src='x'>",
                         "<a href='javascript:evil'>x</a>", "<span onclick='evil'>x</span>",
                         "<div><span></div>", "<span id='bad' onclick='evil'>x</span>"):
            with self.subTest(fragment=fragment):
                self.corrupt(lambda r, s: r[module]["declarations"][0].__setitem__(
                    "header", fragment), "native header|active/unknown")
        self.corrupt(lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
            "doc", "<script>alert(1)</script>"), "active/unsupported native docstring")
        modified = dict(self.original)
        modified[module] += b" "
        with self.assertRaisesRegex(ValueError, "native raw record differs"):
            api.validate(self.records, modified, self.sources, api.SOURCE)

    def test_frozen_inputs_tool_optimization_and_prewrite_refusal(self):
        for path in self.sources:
            changed = dict(self.sources)
            changed[path] += b"\n"
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "source/pin drift"):
                api.check_snapshot(api.SOURCE, changed)
        with self.assertRaisesRegex(ValueError, "source/pin inventory differs"):
            api.check_snapshot(api.SOURCE, {**self.sources, "extra.lean": b""})
        with self.assertRaisesRegex(ValueError, "unexpected/stale analyzed source revision"):
            api.check_snapshot("main", self.sources)
        with tempfile.TemporaryDirectory() as temporary:
            archive, native = self.archive(Path(temporary))
            self.assertNotEqual(self.command(archive, native, optimized=True).returncode, 0)
            self.assertIn("optimized Python is not supported",
                          self.command(archive, native, optimized=True).stderr)
            result = self.command(archive, native, tool="wrong")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unexpected/stale doc-gen4 revision", result.stderr)
            (native / "unexpected.bmp").write_bytes(b"{}")
            result = self.command(archive, native, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing/extra native record file", result.stderr)
            self.assertFalse((archive / "docs/API.md").exists())

    def test_source_only_no_git_replay_and_stale_outputs(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, native = self.archive(Path(temporary))
            self.assertFalse((archive / ".git").exists())
            result = self.command(archive, native, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"status": "generated"', result.stdout)
            result = self.command(archive, native)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"status": "matched"', result.stdout)
            (archive / "docs/api-manifest.json").write_bytes(b"{}")
            result = self.command(archive, native, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("generated file differs/stale manifest", result.stderr)
            (archive / "docs/api-manifest.json").write_bytes(
                (ROOT / "docs/api-manifest.json").read_bytes())
            (archive / "docs/API.md").unlink()
            result = self.command(archive, native, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unexpected/missing documentation file", result.stderr)
            (archive / "docs/API.md").write_bytes((ROOT / "docs/API.md").read_bytes())
            (archive / "examples/Unexpected.lean").write_bytes(b"module\n")
            result = self.command(archive, native)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing/extra shipped Lean module", result.stderr)


if __name__ == "__main__":
    ARGS = PARSER.parse_args()
    unittest.main(argv=[sys.argv[0]], verbosity=2)
