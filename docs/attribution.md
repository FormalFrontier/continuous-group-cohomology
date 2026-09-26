# Attribution, origin and release-review boundaries

**Authors: Formal Frontier Agents.** This is collective formalization credit,
not an assertion of copyright ownership. Original authorized Formal Frontier
contributions are offered under the root [Apache-2.0 license](../LICENSE).
The unmodified root `LICENSE` matches the mathlib `LICENSE` blob at pinned
revision `e37d88a26f3791ed5a93daa1f949af1021b8d103` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`).
Neither that match, AI authorship nor a Git author field establishes ownership
or clearance of third-party expression in the entire artifact or dependency
closure. Preserve original file notices; the native-core preparation does not
remove or replace authentic third-party notices in retained files.

## Shipped project contributions

- **Beacon (Source Maintainer)** created the original continuous degree-one,
  transfer, normalization, compact additive-group and level-system mathematics
  and maintained integration. The original project `README.md` began at
  `f566d4642762e294daf0c3a0aa8c23254f02b9af`. Its prose here has been
  rewritten for the native core, not copied from a published reference.
- **Formalization Worker A** developed the shipped quotient conjugation,
  continuous group-extension, closed-coinvariant and closed topological
  modulo-`n` layers: introductions `7449c16e527eb37e259803e882aa3becf7c9a5d8`,
  `4598559dedbb2d7e6c8b71823cbfd1fa67b49614`,
  `5681fab7b7772c70734b1aa0c2703723cd764e10`, and
  `8cefbfebc2abb18e19e8791b913d5d3ad2421063` (corrected at
  `dd5ca87bb80d272a976d6f12e8e88890c801a944`). Worker B provided
  independent scoped reviews of the final PR #91–#94 heads; PR #92's
  earlier head was rejected and repaired. Worker A's scalar-extension modules
  and legacy clients occur in historical development **only**, not this tree.
- **Formalization Worker B** migrated existing compact, low-degree and level
  mathematics to native modules, adding seven native direct clients along
  the accepted lineage. `dce33a2`, `c336fd8`, `0a16a3e` and subsequent
  accepted F1/C0b/C1f/C1r commits are development evidence, not new
  whole-library rights or release decisions. The original eight legacy-client
  default target (`7739997`) and its subsequent assembly were superseded
  here; the excluded legacy client proofs keep their historical authorship.
- The finite negative-deflation leaf/client were accepted as ordinary code at
  `68eac88271dde4f787e2afa39748661573ad6a06` after independent Worker A
  PR #102 review (issue #95 comments 44502, 44564). The relative-norm native
  layer accepted at `8327f1d6bd86cf1f2e09fd8c02d12a2ea8101ad2` after
  Worker A PR #103 review (issue #95 comment 44789). Finite coinvariants
  accepted at `a170bd0b642fca57385b683f93c161f6696dfbcc` after independent
  PR #104 review (comment 44928); restricted level systems accepted at
  `9fbcd52d0fe4ce982ac506976542523d91dd84c4` after PR #105 review
  (comment 45133). These are **scoped ordinary-code** reviews, not a review
  of this native-root package or first-release readiness.
- This native-core root, seven-client default-target update, root-only
  `examples/NativeCore.lean`, documentation and bounded removal are prepared
  by Worker B Hive Task
  `hive-request-8944bf2a7ffaf993cffb9ddddf08e4c38e297ac6`, UID
  `93d98c92-2373-40f4-9ad4-9a954bfd9909`. This original authorship did not
  itself establish a review; the accepted predecessor core is
  `e7fc83dc3ab35aafde40ac55e3666dac9c2b9015` (tree
  `4a8ec8e5f448fa12f00385b30d0fc95b8ca79e65`), separately published as
  official `be74358d7b1140e76ab6b2ad72f6aa068138e687` with the same tree.
  That release and original authorship do not, by themselves, accept later
  contributions or establish source coverage.
- The exceptional finite-deflation and transitivity leaves and two direct
  clients preserve the original Beacon development from
  `29aa96b09294de3114b06da049d5e2f6b35fb56d` (tree
  `a3b7cac6c1bdc255cbd6c5dec18ccc4535de9f96`). Worker-a Hive Task
  `hive-request-d041f7d11e77baf304eff2577a5b7208816dee14` (UID
  `b057a504-ff63-42ee-9ff2-7e1032534587`) independently reviewed the
  **old, unaccepted P2** component at `612e93e532a639876bebcca34e040ad52a1c362e`
  (issue #95 comment 45223); comment 45222 records historical context.
  Its conditional component verdict is not a review of this combined candidate.
  Worker-b Hive Task `hive-request-1b2effb109cbe1c5d58d117c531264a233407f52`
  (UID `cce9d5e7-93b4-4389-8a9c-4243177704df`) selectively restored
  those exact four source blobs on accepted core
  `e7fc83dc3ab35aafde40ac55e3666dac9c2b9015`, wired native targets,
  updated the published Tate pin and wrote the manual guide. The exact combined
  contribution `c0dae4cfc6d0a5c6065d9a6b7db1941a54b63b26` then received
  fresh independent Worker-a review by Task
  `hive-request-f139e336e97ab3fe7242e258c5c79f30b9530847` (UID
  `76537da1-7962-450b-85e2-5acd85d95ca7`), native PR #110 review 3532,
  followed by Beacon's acceptance and integration on 2026-09-26. This review
  inspected the recovered APIs, whole file tree, provenance and notices; it
  reused the unchanged accepted core, applicable build and then-available axiom
  audit. Subsequent release review by Worker-a Task
  `hive-request-2b345f041f211b1b794c01595e841ebac6c2a4e2` (UID
  `24595926-70a1-46de-ad84-be62a8a36d4f`) found and corrected that audit's
  omitted private declarations using explicit full-module imports; the corrected
  1,962-declaration audit uses only the standard axioms. The original incomplete
  output and its correction remain distinct in the review records. The earlier
  PR #110 review did not approve an as-yet unconstructed successor release history.

These scoped author/reviewer roles come from the original files, accepted
Git history and issue #95's exact-candidate review records, not merely from
the author field of a later mechanical assembly commit.

## Dependency expression and original headers

The library imports and uses named definitions and theorems from pinned
Lean/mathlib (continuous cohomology, group homology, topological modules and
quotient actions) and the official private finite-group Tate library. In
particular, `FiniteNegativeDeflation.lean` imports the latter's
`Norm.lean` and uses its quotient norm construction. The declared official
dependency revision is `fda003db3d06774f28b47232e8248852ffdbfc0d`
(tree `858b405f7bad72e44285f0816cc6cd0607f24bec`), not the previous
official revision `19c1d8ce0f11e9ce7af8ce5ae1e2479aa7cd0796`
or a Forgejo development pin. Referencing these upstream APIs does not make
their underlying proof expression a new Formal Frontier contribution. Further
dependency-closure expression, license and notice assessment is part of each
applicable exact-release review, not implied by an API import alone.
At the **2026-09-26** documentation checkpoint, an independent source-quality
assessment identified adaptation in `TopModuleCatUlift.lean` lines 51–78 of
pinned mathlib `Mathlib/Algebra/Category/ModuleCat/Ulift.lean`, blob
`07439723cae766c30628fdc7123a3a1674733ae4` at mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. The final source input
`afd0296d5138cc87f365aebe1d6d6d33c5546ba9` preserves Nailin Guan's
2025 copyright and Apache notice alongside Formal Frontier/Beacon topological
development credit in the Lean file header. The earlier `f73154d` input did
not identify that adaptation. The repaired source was subsequently included
in the independently reviewed accepted native core; its scoped correction alone
was not an all-artifact clearance. New expression and release history still need
their applicable rights assessment.
No source PDF, extracted source passage or internal research file is shipped.

The accepted origin-header correction `031b20f4ffae4df8a287144e7df3c690e7ced249`
replaced an unsupported `Copyright (c) 2026 Formal Frontier. All rights reserved.`
label on these **retained** project-origin files, with their existing Apache
notice and author credit preserved. The bytes after each opening comment were
not changed by that correction:

| Retained production file | Original introduction |
| --- | --- |
| `ClosedTopologicalCoinvariants.lean` | `5681fab7b7772c70734b1aa0c2703723cd764e10` |
| `ContinuousCohomologyUlift.lean` | `fd46b5367afa3e8d7fc88fb30a37247ee8775011` |
| `ContinuousGroupExtension.lean` | `4598559dedbb2d7e6c8b71823cbfd1fa67b49614` |
| `GroupExtensionUlift.lean` | `0e4616408cfd9833bf45a1d6218d4ea8414b82d1` |
| `HomogeneousCochainsUlift.lean` | `af69479eaf5e555fa3e78442f8b8dccc4f36a6cc` |
| `NormalizedCohomology.lean` | `c9d88cf0153dfd2d8d34bce3a4968a99b5860fb2` |
| `QuotientConjugationAction.lean` | `7449c16e527eb37e259803e882aa3becf7c9a5d8` |
| `TopModuleCatUlift.lean` | `87b6856009dca58fafc13fcfc69413ae299f576c` |
| `TopRepUlift.lean` | `009fc272e08f85425ef18063fb18ccb66662905a` |
| `TopologicalModN.lean` | `8cefbfebc2abb18e19e8791b913d5d3ad2421063` |
| `TopologicalQuotientConjugationAction.lean` | `4598559dedbb2d7e6c8b71823cbfd1fa67b49614` |

The twelfth historical action-file header has an unresolved owner label in
`FiniteDimensionalScalarExtensionAction.lean`, which is **excluded** from
this native-core artifact. This does not clear its separate historical
rights question. The two historical design Markdown files and eight legacy
clients are likewise excluded; any claims or notices applicable solely to
them must be assessed if they are shipped in a later scope. Contributors to
surviving work remain credited above.

## Historical native API documentation (2026-09-26)

Worker-b Hive Task
`hive-request-cca415cd0c40e1f555e1a385d1289c4864a3aee4` (UID
`39f509ab-c2e1-4b59-8573-31cc7b920eb9`) prepared the source-only native
reference, generator, CGC catalogue prose, reproduction guide and data-only
tests, first against frozen **unaccepted** core
`f73154dfa181cc8fd00a102c58f221940a335ad0`, then rebinding the result
to the maintainer's comment/notice-only final source
`afd0296d5138cc87f365aebe1d6d6d33c5546ba9` with explicitly reused
native inputs and a renewed affected client record. That frozen index does not
analyze the subsequently recovered exceptional deflation/transitivity leaves,
clients, changed root or renewed Tate pin; the current manual API guide is
[FiniteDeflation.md](FiniteDeflation.md).
The Apache-2.0 donor is the accepted profinite-groups mixed-kind generator
and tests `79c4bcf23fa81319f9e3936be3f804421c7b98c3`, authored by
worker-b Hive Task `hive-request-49578d0143b3fe26e93ee6e54fa1752f1d60bc26`
(UID `e4f64178-9024-4fe9-8eba-f63c724e7497`). That expression adapts the
accepted finite-group Tate reference by worker-b Task
`hive-request-381dc6f93292eb39ea2d5b25f09baacdc8b20d9e`
(UID `cd8c84f8-2dbf-4399-9c70-1de364ffa99f`), with earlier
polynomial-root-stability `95ac896f81a3190b2634a4246a3e924d2a267a61`
and ideal-completion `f0c8c34386109116e4912fb425a8ad15d9dc42a4`
provenance. The scripts retain the authorship lineage and the root Apache
terms. Pinned upstream doc-gen4 runs as a separate tool; its external SQLite,
raw records, fonts, JavaScript, CSS and images are **not** shipped here.
Native displayed signatures are generated from the CGC source; source-file
docstrings remain attributable to their Lean authors, and independently
written catalogue notes are labeled as non-docstrings. Tool-output hashes
and this attribution do not establish rights in the complete release history.

## Exact release-review boundary

Before any release acceptance, inspect complete proposed source/history and
the dependency closure for copied or closely adapted Lean/prose expression,
preserve all applicable third-party notices (including a `NOTICE` if required
by the actual redistributed material), assess redistribution compatibility,
and reconcile author/reviewer credit for the exact future history. There is
no tracked `NOTICE` in this tree; absence alone proves nothing. Complete
semantic, ordinary-build/transitive-axiom, API documentation, style, performance
and independent candidate review remain distinct requirements, with unchanged
applicable evidence reused. Separate stored-proof replay is not required.
Neither accepted component code nor this ledger alone decides whole-artifact
rights or source coverage; the exact release acceptance records its disposition.
