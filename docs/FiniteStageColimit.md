<!-- SPDX-License-Identifier: Apache-2.0 -->
# Native open-normal inflation colimit

Import `ContinuousGroupCohomology.FiniteStageColimit`.
Let `k : Type u` have `[Ring k] [TopologicalSpace k]`, and let `G : Type v`
have `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`.
For `X : TopRep.{max v w} k G` with `[DiscreteTopology X]` and
`[TopRep.JointlyContinuous X]`, the definition
`ContinuousCohomology.openNormalInflationCoconeIsColimit X n` constructs
`IsColimit (ContinuousCohomology.openNormalInflationCocone X n)` for **every**
`n : ℕ`, including zero, in `TopModuleCat.{max v w} k`. The ring, group and
coefficient universes remain independent. No Hausdorff assumption on `G`,
commutativity of `k`, finiteness of the coefficients or uniform subgroup
refinement is required.

The existing diagram `openNormalCohomologyDiagram X n` is indexed by
`OrderDual (OpenNormalSubgroup G)`: an arrow `M ⟶ N` means `N ≤ M`.
Its `M`-object is the native cohomology of the quotient-invariant
representation, and its arrow is the native transition/inflation to a finer
stage. The existing cocone `openNormalInflationCocone X n` has apex the **actual**
native `continuousCohomology n X` with its given topology and cohomology
inflation legs. No alternative apex or homology construction is substituted.

For any cocone `s` into any topological `k`-module `s.pt`, use
`(openNormalInflationCoconeIsColimit X n).desc s` to obtain the unique
continuous `k`-linear map from that apex to `s.pt`; `.fac s M` gives its
factorization at stage `M`, and `.uniq s f hf` identifies any other map `f`
with the same factorizations. The ordinary-import private client
`examples.FiniteStageColimitNative`
checks the descendant, factorization and uniqueness for a generic `s`, as
well as the specialization to degree zero.

The underlying Type-level witness
`ContinuousCohomology.openNormalInflationCoconeIsColimit_type X n` uses
mathlib's filtered-colimit recognition: official finite-stage class lifting
covers the apex, while class-dependent same-stage eventual equality detects
when two stage elements have the same inflation. For arbitrary target cocones,
linearity of the unique Type descendant follows by moving two representatives
to the common refinement `M ⊓ L`; scalar compatibility is checked at one
stage. Native all-degree discreteness of the apex makes the linear descendant
continuous without modifying the topology on the coefficient ring or target.
This does not assert injectivity of inflation at a fixed stage or preservation
of colimits by the topological-module forgetful functor.

The original contributors and upstream results are credited in
[attribution](attribution.md).
