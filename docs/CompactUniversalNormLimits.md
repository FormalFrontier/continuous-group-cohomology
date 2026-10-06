# Universal norms in compact relative-norm limits

For a commutative ring `R`, a profinite group `G`, and a
`ContinuousGroupCohomology.LevelCompactRep.{u,u,u} R G`, each open normal
subgroup `U` has a *chosen* compact Hausdorff topology on its invariant module
`A^U`. Neither `R` nor the ambient representation is required to have a
topology. An arrow `V ⟶ U` between open normal levels means `V ≤ U`, and the
corresponding diagram map is the actual relative norm from `V` to `U`.

Import `ContinuousGroupCohomology.CompactUniversalNormLimits` (also reexported
by the `ContinuousGroupCohomology` public root).
Within `ContinuousGroupCohomology.RestrictedLevelCompactRep`, the API is:

* `fullNormLimit_projection_mem_iff`: a full-limit coordinate is in the
  projection's range exactly when its underlying invariant belongs to the
  previously defined `LevelCompact.universalNormSubmodule`. The proof uses
  `CompHausAddCommGrp.limit_π_range_eq_eventualRange`; its two-way bridge
  compares witnesses in the full `⊤` coefficient subtype with witnesses of
  the original linear relative norm. Compactness makes independent norm-range
  conditions compatible as a single full-limit family.
* `universalNorm_relativeNorm_surjective`: each *restricted linear* relative
  norm `N(V) → N(U)` is onto for `V ≤ U`. It chooses one full compatible family
  over the desired coordinate; that family's `V` coordinate lies in **every**
  deeper range and therefore in `N(V)`.
* `fullInclusion` is the existing identity-underlying coefficient map from
  any closed, norm-compatible restricted system `B` into `full
  B.toLevelCompactRep`. `restrictedNormLimitIso B` is its induced isomorphism
  **in `CompHausAddCommGrp`**, not merely a bijection of compatible sets.
  `fullInclusion_limitMap_bijective` identifies its underlying forward map
  with `lim.map (restrictedNormDiagramMap (fullInclusion B))`: every full
  compatible coordinate lies in `N(U) ≤ B(U)`, and its lifted coordinates
  obey the restricted norm equations. Continuity of the inverse follows from
  the compact-Hausdorff continuous-bijection theorem, and additivity from
  bijectivity of the additive forward map.
* `restrictedNormLimitIso_hom_π` and `restrictedNormLimitIso_inv_π` identify
  **both** projections with the actual levelwise inclusion. The inverse
  coordinate is uniquely specified after inclusion into the full level.
  `restrictedNormLimitIso_naturality` commutes with every *specified* morphism
  of restricted systems. Its `map_mem` condition preserves arbitrary chosen
  submodules; it is not automatic for an arbitrary coefficient map. For the
  universal-norm choice, `universalNorm_limitIso_naturality` accepts every
  level-compact coefficient morphism through the pre-existing
  `universalNormFunctor`, whose preservation is automatic.

The actual diagram, chosen compact groups, restricted systems, finite-sum
relative norms, and universal-norm submodules come from the published
`ContinuousGroupCohomology.RestrictedLevelCompact`,
`RestrictedLevelCompactFunctoriality`, `LevelCompactNorm`,
`LevelCompactFunctoriality`, and `CompactAddCommGroupLimits` modules. Their
original developments are credited to Beacon and Formal Frontier Agents;
the present bridge reuses their norm diagrams and restricted-system maps.
See [attribution](attribution.md) for contributor origins.

**Limits of the statement.** Full invariant norm transitions need not be
onto. For the trivial action of the finite group `C₂` on `ℤ/2`, the full norm
from the trivial subgroup to the whole group is multiplication by two and is
zero, while the target full invariants are nonzero; the target universal norms
are zero. Likewise arbitrary restricted choices need not have onto transitions,
and `B(G)` need not equal `A^G`. The relative-norm invariant diagram here is
not the finite-coinvariant/total-invariant/Tate norm row. No Tate-degree,
coinvariant/kernel-surjectivity, long-exact-sequence or source-coverage claim
follows.

## Reproducibility

This library pins Lean `v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and finite-group Tate
`d17f93bbc5b934f8b9f3cf077769a706a901608d`. From the repository root run:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake build ContinuousGroupCohomology CGCExamples
```

The matching mathlib cache must be fetched successfully before any build.
The [direct client](../examples/CompactUniversalNormLimitsNative.lean)
exercises the full projection range, norm surjectivity, compact-group
isomorphism and both projection/naturality equations. See
[attribution](attribution.md) for contributor origins.
