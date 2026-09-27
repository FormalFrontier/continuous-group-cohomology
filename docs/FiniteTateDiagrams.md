# Finite Tate deflation diagrams and limits

Import `ContinuousGroupCohomology`, or the three leaves
`ContinuousGroupCohomology.FiniteTateDiagrams`,
`ContinuousGroupCohomology.NonpositiveTateLimits` and
`ContinuousGroupCohomology.NonpositiveTateFunctoriality` as needed. These
constructions work with an **algebraic** representation `A : Rep.{u} R G` for
`[CommRing R]` and a profinite group `G : ProfiniteGrp.{u}`. The topological
diagrams and limits additionally require `[TopologicalSpace R]`; the ring,
group and representation carrier remain in the same universe `u`.

## Stages and transition maps

An index `S : OpenNormalSubgroup G` supplies a finite quotient `G ⧸ S` and
its invariant-coefficient representation `A.quotientToInvariants S.toSubgroup`.
The three covariant diagrams in [`FiniteTateDiagrams.lean`](../ContinuousGroupCohomology/FiniteTateDiagrams.lean)
are:

| Diagram | Stage at `S` | Meaning |
| --- | --- | --- |
| `finiteNegativeDeflationDiagram A n` | `groupHomology (A.quotientToInvariants S.toSubgroup) n` | For positive `n`, a finite homological model of Tate degree `-n-1`. |
| `finiteNegativeOneDeflationDiagram A` | `tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)` | Exceptional degree `-1`. |
| `finiteZeroDeflationDiagram A` | `tateCohomology (A.quotientToInvariants S.toSubgroup) 0` | Exceptional degree `0`. |

For `S ≤ T`, the arrow goes **from** the `G ⧸ S` stage **to** the `G ⧸ T`
stage by the corresponding finite deflation map. The definitions obtain actual
`Fintype` witnesses for finite quotients and intervening subgroup images from
openness and compactness of the profinite group. The functor laws use the
finite-deflation identity/composition results; they do not postulate additional
finiteness for an arbitrary normal subgroup of an arbitrary group. Consult
[`FiniteDeflation.md`](FiniteDeflation.md) for those finite-level maps.

## Topology and coefficient morphisms

[`NonpositiveTateLimits.lean`](../ContinuousGroupCohomology/NonpositiveTateLimits.lean)
postcomposes each diagram with `TopModuleCat.withModuleTopology.{u, u} R`.
`negativeDeflationLimit A n`, `negativeOneDeflationLimit A` and
`zeroDeflationLimit A` are categorical limits in `TopModuleCat`; their
`*LimitProjection` maps and `*LimitProjection_naturality` lemmas are the
canonical limit projections and cone identities.

[`NonpositiveTateFunctoriality.lean`](../ContinuousGroupCohomology/NonpositiveTateFunctoriality.lean)
defines coefficient-representation functors for all three algebraic diagrams,
their topological postcompositions and their limits. In particular,
`negativeDeflationLimitFunctor`, `negativeOneDeflationLimitFunctor` and
`zeroDeflationLimitFunctor` send representation morphisms to continuous
topological-module morphisms. The corresponding `*Functor_map_projection`
lemmas are the `limit.map_π` compatibility at each index. See the
[`NonpositiveTateDiagramsNative` client](../examples/NonpositiveTateDiagramsNative.lean)
for all three stages, functoriality and a strict inclusion between the open
normal subgroups of a two-element profinite group. This client checks typing
and deflation direction, **not** a numerical Tate-group computation.

These constructions do **not** establish discrete or compact stages,
topological exactness, cup compatibility, or an identification with completed
continuous Tate theory. They do not establish whole-source coverage. The
generated [API snapshot](API.md) indexes an older graph, not these leaves.

## Relation to chosen compact exceptional stages

The [compact exceptional Tate guide](FiniteTateTopology.md#compact-diagrams-and-limits)
covers the distinct `CompactExceptionalTateDiagrams` and
`CompactExceptionalTateLimits` leaves. Given an explicit `LevelCompact A`,
they assemble *actual compact kernel/quotient* stages in degrees `-1` and `0`
and deflate continuously in `CompHausAddCommGrp`. Their comparisons to the
degree-`-1` and degree-zero **algebraic** functors above are natural
isomorphisms only after forgetting to `AddCommGrpCat`. Their limits and
eventual-range projections live in `CompHausAddCommGrp`, not in the
`TopModuleCat` limits defined here. Neither layer identifies these two kinds
of limit or supplies inverse-limit exactness.
