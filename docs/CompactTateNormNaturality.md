# Coefficient naturality of the compact Tate norm row

Import `ContinuousGroupCohomology.CompactTateNormNaturality`
for the continuous coefficient maps and naturality of the *full* compact
Hausdorff additive norm row. The independent arbitrary-data client imports
only this producer in
`examples.CompactTateNormNaturalityNative` (namespace
`CGCExamples.CompactTateNormNaturalityNative`).

Fix `{R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}` and
`A B : LevelCompactRep.{u,u,u} R G` with `f : A ⟶ B`. Write `K∞(A)` for
the published `compactNegativeOneTateLimit`, `C∞(A)` for the actual
`compactFiniteCoinvariantsLimit`, `I(A)` for
`LevelCompact.group A.rep A.levelCompact ⊤`, and `Q∞(A)` for the published
`compactZeroTateLimit`. These fit the already-proved exact row

```text
K∞(A) → C∞(A) → I(A) → Q∞(A).
```

The diagrams are indexed by open normal `S ≤ T`, finer to coarser; coinvariant
deflation is the residual norm. `compactFiniteCoinvariantsDiagramFunctor` has
the genuine `finiteCoinvariantsMap f S` at each stage and commutes with the
actual finite deflation. `compactFiniteCoinvariantsLimitFunctor` applies `lim`
to that diagram; `compactFiniteCoinvariantsLimitFunctor_map_π` identifies
every stage projection. Identity/composition follow from these functors and
from `finiteCoinvariantsMap_id`/`finiteCoinvariantsMap_comp`. The degree `-1`
and `0` functors are the *existing*
`compactNegativeOneTateLimitFunctor` and `compactZeroTateLimitFunctor`, not
newly modeled Tate groups. The middle invariant map is
`LevelCompactRep.groupMap f (⊤ : OpenSubgroup G)`.

`compactTateLimitInclusion_naturality`,
`compactTateLimitNorm_naturality`, and
`compactTateLimitProjection_naturality` prove the three squares in the row.
They are also assembled into `compactTateLimitInclusionNat`,
`compactTateLimitNormNat`, and `compactTateLimitProjectionNat`. Their proof
uses the existing finite kernel inclusion, finite norm, and finite quotient
squares, together with the existing limit component equations. In
particular `I(A)` is **not** identified definitionally with the limit of its
constant diagram: the existing construction uses the canonical connected
constant-cone isomorphism.

The actual compact quotient object is
`CompHausAddCommGrp.quotient I(A)
(LevelCompact.compactUniversalNormClosedSubgroup A.rep A.levelCompact)`.
`compactUniversalNormQuotientMap f` descends `groupMap f ⊤` directly through
that quotient, and is continuous for its quotient topology; its representative
equation is `compactUniversalNormQuotientMap_mk`. The subgroup condition is
`mapInvariants_mem_universalNorm f (LevelCompact.fullOpenNormalSubgroup G)`,
specialized to the existing closed universal-norm subgroup; no additional
preservation hypothesis or surjectivity is assumed.
`compactUniversalNormQuotientMap_id` and
`compactUniversalNormQuotientMap_comp` make the quotient action a genuine
`compactUniversalNormQuotientFunctor`. Finally
`compactTateUniversalNormQuotientIso_naturality` identifies this independently
descended map with the existing projection under the existing
`compactTateUniversalNormQuotientIso`.
`compactTateUniversalNormQuotientNatIso` is its natural-isomorphism packaging,
and `compactTateUniversalNormQuotientNatIso_hom_app` gives its exact component;
`compactTateUniversalNormQuotientNatIso_hom_app_mk` states that on `[x]` it is
`compactTateLimitProjection A.rep A.levelCompact x`.

The topology on each invariant group is the chosen `A.levelCompact.topology S`;
the coinvariant groups have the native quotient topologies; inverse limits are
compact Hausdorff additive limits; and the final quotient uses the *actual*
closed universal-norm subgroup inside the chosen total-invariant topology.
There is no topology on `R` or the ambient representation, no scalar/topological
module claim, and no artificial surjectivity of coinvariant/kernel transitions.
The pinned mathlib does not have `(⊤ : OpenNormalSubgroup G)`; use the named
`LevelCompact.fullOpenNormalSubgroup G`. Restricted-system `B_top` is not
automatically total invariants.

This library pins Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and the official
finite-group Tate revision `fda003db3d06774f28b47232e8248852ffdbfc0d`.
Its finite norm row and full norm-limit sequence are available through the
imports of this producer. From the library root, install the pinned toolchain,
fetch the matching mathlib cache successfully, and build the root and named
client target (which also belongs to the default build):

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake build ContinuousGroupCohomology CGCExamples
```

The producer's original expression came from an incubator isolated leaf;
its complete declaration and proof bodies and the eight client examples are
preserved. At the **September 27, 2026 source-only handoff**, frozen incubator
revision `06f99031c7cf284320dc65fcaf787a569a791be4` (tree
`403dc2ea0ab2a1a9b35a5d263009cf59cabb48f9`) was **unaccepted**.
It built against a different mathlib pin, so neither its successful source
checks nor its isolated-leaf review establish compatibility with this library.
The destination copy starts from accepted CGC main
`62798e8559c7665f89e930fd0cd718ce9b5aa825` (tree
`54568aa46186e1b861db8956129e10fc35f55f30`); separately verified official
publication `130d8d776944e94871988a09ab01375d6dce49ca` has the same
tree. This new naturality copy is **not** thereby reviewed, accepted or released.

The reused finite norm row and full limit/quotient identification originated in
Hive Tasks `hive-request-e6d76bdf4dadaad23f990aa082128217880d7321`
(UID `b9bd4a7e-8ee1-4213-9075-d0ebba7ab03e`) and
`hive-request-a3c785c9e3c2568cbdb2e8592ff3c30ed2a0feee`
(UID `8642a473-88cb-463a-beca-1c6e7fc1b695`). The published coefficient
maps originate with Beacon and native adaptation Task
`hive-request-d61b09970e5688d0b1e0da08ec7719208350ad23`
(UID `b087c1ae-8092-47fc-ba95-7e8a338a0201`); the published
exceptional-limit functors have native adaptation Task
`hive-request-ec9bf361966f9bc5d2a422dd9e00cf39656f7a7c`
(UID `cd42fd3f-1546-42a4-b934-06eb5087858a`) and named-projection Task
`hive-request-c53967c3623f44154013d9f5cd5cd87a248da315`
(UID `fae3b9d5-de01-4c04-b9c0-a63cc9cafb6e`). The universal-norm
preservation used here was published with native adaptation Task
`hive-request-15de2e8fb886b8dfbc8a9e6096f6f9069aa1bc0c`
(UID `5a9907b2-d133-462a-bc07-ae576b5820b6`). All of these results are
reused, not claimed as new work. New implementation: worker-b Hive Task
`hive-request-1d0844eac48c5857a2e1cc8b56121d7b8571e14b`
(UID `a02c5d55-67a0-4421-a798-eebf69e9182a`), September 27, 2026.
Source registration was by worker-b Task
`hive-request-43c60eed6b2331151875ef6f0954f3562dbca09e` (UID
`0edbdd54-f20b-4f58-8fac-ed5f0ed613aa`); destination header,
client import/namespace and library registration by worker-b Task
`hive-request-89268f99753a32543c537bc946e6f0fdc94c084c` (UID
`6fb5a0a9-b048-4a08-ab62-90614094ecd7`). These are distinct contributors
and tasks, not a reassignment of mathematical authorship.

The original isolated leaf was independently reviewed by worker-a
Task `hive-request-4661f56c3281eda913c0a11cdf4eedbb6fda6a3f` (UID
`10398f84-5ce6-4c37-b9d5-a8aec6ae7a66`) approved the exact isolated
leaf at CGC issue #30 comment 53337; Beacon accepted isolated readiness only
in comment 53352. Separate complete private-inclusive focused evidence is at
incubator commit `dfbe0fa51529c1b7695d6bc2b63c711a530af077`; its
original public-import census alone was superseded. Worker-b Task
`hive-request-43c60eed6b2331151875ef6f0954f3562dbca09e` (UID
`0edbdd54-f20b-4f58-8fac-ed5f0ed613aa`) registered this producer/client on
the frozen, then-unaccepted source branch at the 2026-09-27 author handoff,
with ordered parents actual PR120
`6fd0dcc28775b804edde1c6b387a907720255942` and isolated leaf
`36b855eb9ae325c9669de7fd3264a1fb83ccef7a`. Those source review,
private-inclusive native and maintainer-acceptance gates, and the distinct
changed-pin destination gates, were pending at that handoff. Subsequently
source PR #121 passed affected review and native544 and was accepted and
integrated at `06f99031c7cf284320dc65fcaf787a569a791be4` (CGC #30/53761).
Destination PR #150 passed independent review and native547 full-root/client
build and complete private-inclusive standard-axiom checks, then was accepted
and integrated at `f37e95ea83e8477e84a58e327df7535cb93c12cc`
(CGC #30/53596, #30/53776, #30/53786). Independent final release review,
acceptance and verified GitHub publication remain pending. Any later incubator
removal/import replacement requires that publication and a separately agreed
source input. Neither handoff establishes source correspondence or coverage.
