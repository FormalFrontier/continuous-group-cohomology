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

The implementation combines the existing finite norm row, its full-system
limit and the coefficient maps on compact exceptional Tate groups. Original
contributors and upstream dependencies are credited in
[attribution](attribution.md); their exact hypotheses are in the linked Lean
modules and the client above.
