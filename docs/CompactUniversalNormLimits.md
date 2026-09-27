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
original developments are credited to Beacon and the Formal Frontier agents;
the native restricted functoriality adaptation credits
`hive-request-15de2e8fb886b8dfbc8a9e6096f6f9069aa1bc0c` and its norm
diagram development credits
`hive-request-c53967c3623f44154013d9f5cd5cd87a248da315`. The bridges
in this contribution were authored by worker-b Task
`hive-request-03e922288088a5d1c219136acc3e6c751b1deed4`, UID
`c434e120-0a6c-400b-8688-df1930ee09cf`.

**Limits of the statement.** Full invariant norm transitions need not be
onto. For the trivial action of the finite group `C₂` on `ℤ/2`, the full norm
from the trivial subgroup to the whole group is multiplication by two and is
zero, while the target full invariants are nonzero; the target universal norms
are zero. Likewise arbitrary restricted choices need not have onto transitions,
and `B(G)` need not equal `A^G`. The relative-norm invariant diagram here is
not the finite-coinvariant/total-invariant/Tate norm row. No Tate-degree,
coinvariant/kernel-surjectivity, long-exact-sequence or source-coverage claim
follows.

## Reproducibility and status

At its September 27, 2026 source-only handoff, this copy transferred the
reviewed incubator leaf
`a3a22a2ff480a29bf9c6bc65bdc3258318d0ddb5` (tree
`3aa7cb0c7bd4339bb1690cdc1e9bfda21f5b1ef6`) onto accepted destination
`0534608dbab4845ee3e356f4f79cc1422eff013c` (tree
`5f90272fefc84b2a24cd5d0f6eb7923a40c1e650`). At that handoff the source
was an unregistered, unintegrated successor to incubator
`ed9e33a55cc71125ad3350051096e2949959f9a5`; the fresh worker-a review
in CGC issue #30 comment 54289 approved its frozen leaf, and the maintainer
adopted *leaf readiness only* in comment 54295. Source focused builds and a
private-inclusive 46-origin standard-axiom audit are recorded at
`af111b8039277f3757173783a88390f88dddfd82` for source mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5` and official CGC
`130d8d776944e94871988a09ab01375d6dce49ca`; that evidence cannot certify
this destination. This library pins Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and official finite-group
Tate `fda003db3d06774f28b47232e8248852ffdbfc0d`. To reproduce the
*destination* build after installing the pinned toolchain, fetch the matching
mathlib cache successfully **before** building from this repository root:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
lake build ContinuousGroupCohomology CGCExamples
```

The direct client `examples/CompactUniversalNormLimitsNative.lean` imports only
the producer and contains seven named uses
over arbitrary coefficient data of norm surjectivity, full projection range,
the compact-group iso, both projection equations and both coefficient
naturality interfaces. These commands are reproduction instructions, **not**
checks performed for this prose-only release preparation. Subsequently, the
original source files were registered and protected-integrated in incubator
PR #131 at `74260f173dacd7fab9156b70ca427a96f83ea2f2` (tree
`afdce51bb31b86739736c52190693ea927c40cdc`; CGC #30/54932 and
incubator #131/54934). Independent destination review of PR #154 by worker-a
Task `hive-request-3c9cfef2b5e3ff3583db27d9833858f1b53e5c84` (UID
`5ee84ff8-274d-48d1-a7f1-d4bcdd39f1fe`; CGC #30/54424) and native603
both-root build and complete private-inclusive transitive standard-axiom audit
(CGC #30/54767) supported Beacon's acceptance and protected integration of
`157fbdc282f1697a857a9d552aa394f8a0214bba` (tree
`1fa60aafcfef4cfcbe31aae8ee07b85a6286522e`; CGC #30/54948).
The applicable destination native603 evidence uses this library's pinned
dependencies and covers 72 modules, including the new producer and client,
under only `propext`, `Classical.choice` and `Quot.sound`; the earlier
46-origin source evidence alone did not establish that compatibility.
This September 27 release-readiness snapshot is not an accepted release:
independent whole-artifact/history/rights review, separate owner release
acceptance, protected public promotion, verified private GitHub publication
and later reviewed incubator import conversion remain pending. Neither code
acceptance nor eventual release establishes source correspondence or coverage.
