# Compact finite-bar homology and negative Tate stages

Import `ContinuousGroupCohomology` for the public native core, or import
`ContinuousGroupCohomology.CompactBarFunctoriality` for the finite-bar API.
The latter publicly imports `CompactNegativeTate`. This guide describes the
current native declarations, rather than the [historical generated API
snapshot](API.md).

## Finite bar homology

Let `R` be a commutative ring, `H` a finite group (`[Group H] [Fintype H]`),
and `B : Rep R H` with a compact Hausdorff additive-group topology
(`[TopologicalSpace B] [CompactSpace B] [T2Space B]
[IsTopologicalAddGroup B]`). Supply `hρ : ∀ h, Continuous (B.ρ h)`;
no topological-module structure over `R` or topology on `H` is assumed.

- [`CompHausAddCommGrp.FiniteBar.chains`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L66)
  gives finite inhomogeneous chains with a finite-product topology;
  [`differential`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L104)
  is a continuous additive map and
  [`differential_apply`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L110)
  identifies its underlying map with mathlib's bar differential.
- [`positiveHomology B hρ n`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L116)
  is a compact Hausdorff additive group in degree `n + 1`, formed as cycles
  modulo the boundary range. The image of a compact group in a Hausdorff group
  is closed, so this is the closed-boundary quotient, not an unclosed algebraic
  quotient assigned an unsupported topology.
- [`groupHomologyAddEquivPositive B hρ n`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L202)
  is an *additive* equivalence from `groupHomology B (n + 1)` to the underlying
  group of `positiveHomology B hρ n`. The
  [`homologyπ` lemma](../ContinuousGroupCohomology/CompactNegativeTate.lean#L279)
  identifies the image of an algebraic cycle with its compact quotient class.
  It does not assert a topological equivalence for algebraic homology.

## Maps and naturality

For finite groups `H`, `K` and representations `B : Rep R H`, `C : Rep R K`,
supply the same compact Hausdorff additive hypotheses on **both** coefficients,
the action continuity witnesses `hB : ∀ h, Continuous (B.ρ h)` and
`hC : ∀ k, Continuous (C.ρ k)`, a group homomorphism `f : H →* K`, a
representation morphism `φ : B ⟶ Rep.res f C` (which supplies equivariance),
and an **independent** continuity witness `hφ : Continuous φ.hom`.

- [`chainsMap B C f φ hφ n`](../ContinuousGroupCohomology/CompactBarFunctoriality.lean#L45)
  is continuous; the [`single` lemma](../ContinuousGroupCohomology/CompactBarFunctoriality.lean#L77)
  sends `(i, x)` to `(f ∘ i, φ.hom x)`.
  [`chainsMap_differential`](../ContinuousGroupCohomology/CompactBarFunctoriality.lean#L85)
  proves compatibility with the finite bar differentials.
- [`positiveHomologyMap B C hB hC f φ hφ n`](../ContinuousGroupCohomology/CompactBarFunctoriality.lean#L132)
  descends to a continuous homomorphism of compact homology groups.
  [`groupHomologyAddEquivPositive_naturality`](../ContinuousGroupCohomology/CompactBarFunctoriality.lean#L162)
  identifies its underlying map with mathlib's algebraic `groupHomology.map`.

No continuity or equivariance is inferred from the other: both hypotheses are
required. The direct [native client](../examples/CompactNegativeBarNative.lean)
tests generic lemmas and specializes to the nontrivial group
`Multiplicative (ZMod 2)` and nonzero `ZMod 3` coefficients with trivial action;
its concrete map case is the identity, not a nontrivial-map construction.

## Finite Tate level

For a compact topological group `G`, a representation `A : Rep R G`,
`L : ContinuousGroupCohomology.LevelCompact A`, an open normal subgroup
`S : OpenNormalSubgroup G`, and `n : ℕ`,
[`LevelCompact.finiteTateNegative A L S n`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L349)
is the compact additive finite-bar homology for the finite quotient `G/S`
acting on `A^S`. With `[Fintype (G ⧸ S.toSubgroup)]`,
[`LevelCompact.tateCohomologyNegativeAddEquivFiniteTate`](../ContinuousGroupCohomology/CompactNegativeTate.lean#L370)
gives an *additive* equivalence from finite Tate cohomology in degree
`-(n + 2)` to this compact group. It starts at `-2`, not `-1`, and makes
**no** topological-module comparison without a scalar topology.

This layer establishes neither continuity of finite deflation across levels,
nor inverse-limit exactness, a completed continuous Tate theory, or a
source-coverage decision. See [attribution](attribution.md) for original
contributor credit.
