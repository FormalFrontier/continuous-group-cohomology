<!-- SPDX-License-Identifier: Apache-2.0 -->
# Open-normal continuous-cohomology diagram

Import `ContinuousGroupCohomology.OpenNormalDiagram`.
For a ring with a topology `k`, a topological group `G`, and a native
`X : TopRep k G`, the functor `ContinuousCohomology.openNormalCohomologyDiagram X n`
has index `OrderDual (OpenNormalSubgroup G)` and target the **native**
`TopModuleCat k`, not the algebraic `ModuleCat k`. Its object at `M` is the
actual `continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X)`.
An arrow `M ⟶ N` is a refinement `N ≤ M`; it maps classes at `M` to classes
at `N` by `quotientTransitionHom N M` and `quotientTransitionIncl X`.

The `openNormalInflationCocone X n` has apex `continuousCohomology n X`.
Its `M`-leg is the native map along `openNormalQuotientHom M` and
`TopRep.quotientInvariantsIncl M.toSubgroup X`. Naturality reuses the
transition-inflation law. The theorem `isFiltered_orderDual_openNormalSubgroup G`
gives a filtered-index witness: intersection supplies common targets, and the
whole group supplies a stage. It requires no global top element instance for
`OpenNormalSubgroup G`.

No compactness of `G`, discreteness or joint continuity of `X`, separation of
`G`, or commutativity of `k` is required. Open-normal quotients need **not** be
finite in general; compactness of `G` makes the quotients finite. This diagram
and cocone assert **no colimit property**, finite-stage surjectivity, or
injectivity at a fixed positive-degree stage. The generic client is
`examples.OpenNormalDiagramNative`, which imports this production module and
`examples.FiniteStageResolutionNative` for arbitrary-degree diagram and
filtered-index examples.

The original contributors and upstream results are credited in
[attribution](attribution.md).
