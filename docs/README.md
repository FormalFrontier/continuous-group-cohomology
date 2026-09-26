# Native API reference: reproduction and limits

The [API index](API.md) and [JSON manifest](api-manifest.json) cover the
**historical analyzed graph** of 28 production modules (including the aggregate
public root and 27 leaves) and eight checked-use clients, with separate inventories.
They do **not** cover the current 35-leaf/thirteen-client graph, its eight additional
production modules, five direct clients or updated aggregate root. Consult the
[manual finite-deflation guide](FiniteDeflation.md),
[finite Tate diagrams guide](FiniteTateDiagrams.md),
[compact finite-bar guide](CompactBar.md),
[degree-one torsion guide](../README.md#degree-one-torsion) and current sources.
The JSON manifest preserves its historical generated `api_sha256`
(`c82dbaf5d9d0cab822c2b8226fbe687adcc0cba67cbb8fa5cbbfe3908e20b0ad`),
but a later manual historical-scope preface changes the checked-in `API.md`
file bytes. Only that preface is maintained for the current graph.
Thus the manifest's hash describes the original generated index, **not** the
current file bytes; neither it nor historical module counts certify later additions.
This historical snapshot is
a declaration and native instance-table index, **not** a full HTML website,
proof-body report or source-coverage claim. Module prose is in the Lean files;
private proof bodies and upstream dependency docstrings are not shipped here.
Undocumented entries carry clearly marked original catalogue prose rather than
invented Lean docstrings. Lean's native pretty-printer can abbreviate some
rendered types as `⋯`; follow the linked source for the unabbreviated source
statement and its exact hypotheses. The original source is not an expanded
elaborated type. Generated constructor/projection entries may link to their
parent structure instead of having a separately spelled source declaration.

## Frozen inputs

The **historically analyzed source**, not the current combined assembly, is the comment/notice-only native successor
`afd0296d5138cc87f365aebe1d6d6d33c5546ba9` (tree
`cfb84abe6f06142f5c898f22a5a2fe9760fbc6a6`) on Lean
`leanprover/lean4:v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and private official
finite-group Tate `19c1d8ce0f11e9ce7af8ce5ae1e2479aa7cd0796`.
The analyzed identity binds the 36 Lean module files and the three pinned
toolchain/Lake files by SHA-256 in the adapter and manifest. It does **not**
claim the later documentation commit has the same tree, and a source-only
archive does not need the historical Git object. The exact documentation
commit/tree must be bound separately by the maintainer's review and lifecycle
record. Do not update the pinned Lake manifest during reproduction.

**Native input provenance is mixed and explicit:** 35 records come from the
previous complete `f73154dfa181cc8fd00a102c58f221940a335ad0` extraction;
only `examples.NativeCore` was re-extracted against `afd0296`. The 35
reused signatures, import rows, native instance records and Lean declaration
docstrings still match the final source byte-for-byte where relevant. A
source-anchored line audit maps the nine declarations in `NestedInvariants`
and 18 in `TopModuleCatUlift` from native line `n` to final-source line
`n + 4`; every other reused declaration retains its line. `NativeCore` has
two revised source comments (one declaration docstring), so its record must
not be reused. The JSON manifest records both raw origins and every original
and final anchor; neither old native line numbers nor old source URLs are
passed off as newly extracted. The 35 externally retained raw files are
necessary inputs to replay this exact hybrid output, but their original Git
commit object is **not**.

The tool is genuine upstream `leanprover/doc-gen4` revision
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`, in an **independent**
checkout with its own pinned manifest and toolchain; it is not a new
dependency of this library. The adapter's revision arguments are mandatory
identity checks, not a substitute for verifying the actual tool executable.
`https://example.invalid/commit/...` inside the *external raw native data*
is only an inert exact-input marker; the shipped Markdown uses local relative
source links instead. No native raw data, SQLite or doc-gen website assets
belong in the source tree.

## Reproduce the historical snapshot

Use the **frozen analyzed source inputs and original manifest** described above,
not this current checkout's changed Lake pins/root/import graph, to reproduce
this generated snapshot. After obtaining authorized access to the official
private historical Tate dependency, use that source's pinned Lean/Lake toolchain
and fetch the matching mathlib cache
**successfully before any project build**. Build the root and clients once as
needed to obtain `.olean` files for the *renewed NativeCore module*. Keep builds
sequential and monitor actual memory and process use rather than assuming
`LEAN_NUM_THREADS` sets a process or memory cap:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build examples.NativeCore
```

In a separate checkout, verify the doc-gen4 commit/tree above, keep its pinned
Lean/manifest inputs intact, and build `lake build doc-gen4` in its own
environment. If `cc` is absent, prepend `$(dirname "$(elan which lean)")` to
`PATH`. Choose a fresh *external* directory (`OUT`) and re-extract only the
changed client record. Copy the 35 first-run records from the external
evidence packet to a second **external** `RAW` directory; no first-run
SQLite or website files are copied into the library:

```sh
TOOL=/path/to/doc-gen4/.lake/build/bin/doc-gen4
OUT=/path/to/fresh/external-output
RAW=/path/to/external-hybrid-raw
REV=afd0296d5138cc87f365aebe1d6d6d33c5546ba9
mkdir -p "$OUT/build" "$OUT/render" "$RAW"
cp /path/to/first-run/raw/declaration-data-*.bmp "$RAW/"
LEAN_NUM_THREADS=2 lake env "$TOOL" single --build "$OUT/build" examples.NativeCore \
  "$OUT/build/nativecore.db" "https://example.invalid/commit/$REV/examples/NativeCore.lean"
"$TOOL" bibPrepass --build "$OUT/render" --none
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/nativecore.db" examples.NativeCore
cp "$OUT/render/doc-data/declaration-data-examples.NativeCore.bmp" "$RAW/"
python3 -B scripts/test_generate_api.py --native-data "$RAW"
python3 -B scripts/generate_api.py --native-data "$RAW" \
  --source-revision "$REV" \
  --docgen-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

`lakefile.lean` is a hashed **build input**, not a documented Lean module.
For pure source-only/no-Git replay of the adapter, provide the 36 **already
captured external** raw records and the checked 39 source/pin files: no
historical source commit object, website build or network Git is required.
One complete original SQLite and the separately renewed NativeCore SQLite
are retained in the sibling evidence branch. The owner directed **no second
full extraction** while coordinating the source fix; thus two fresh full
native-directory/SQLite comparisons are **not performed** for this candidate,
and that gap is not a reproducibility pass. The adapter refuses altered
input bytes, revisions, unknown native shapes, declaration names/kinds/rows,
instances, import rows, links, active HTML, extra records, Python optimization
and stale generated output before writing. The data-only test suite cannot
certify that a third party truly ran doc-gen4: its preserved external raw
records, SQLite, logs and pinned tool build are separate evidence.

## Authorship and status

The Apache-2.0 mixed-kind generator/test design was adapted from the accepted
profinite-groups `79c4bcf23fa81319f9e3936be3f804421c7b98c3`, itself
adapted from the accepted finite-group Tate generator and earlier project
expressions; precise lineage is in the scripts and [attribution](attribution.md).
The original 2026-09-26 documentation preparation described an unaccepted
successor to the comment/notice-only native source. The prior native core is
subsequently accepted at `e7fc83dc3ab35aafde40ac55e3666dac9c2b9015`
and published in official `be74358d7b1140e76ab6b2ad72f6aa068138e687`
(same tree). This historical extraction does not certify the **current**
finite-deflation contribution's proof integrity, third-party rights, whole-release
readiness or source coverage. The combined finite-deflation contribution received
its own independent review and ordinary acceptance on 2026-09-26 at
`c0dae4cfc6d0a5c6065d9a6b7db1941a54b63b26`, using an applicable successful
build and the then-available transitive standard-axiom audit. Subsequent release
review found that ordinary imports had omitted private declarations from that
audit. An explicit full-module import audit corrected the omission before
publication: all 1,962 stored repository declarations, including private and
generated declarations, use only the three standard axioms. The earlier
incomplete output remains preserved in the review records. The diagram/client
predecessor received a separate private-inclusive 67-declaration standard-only
audit; its subsequent combined assembly still needs exact review and acceptance.
The historical
extraction limits above remain recorded; fresh documentation extraction is not
a release prerequisite. Exact release and publication decisions remain separate.
