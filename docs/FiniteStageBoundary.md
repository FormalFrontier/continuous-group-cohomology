<!-- SPDX-License-Identifier: Apache-2.0 -->
# Class-dependent finite-stage zero detection

Import `ContinuousGroupCohomology.FiniteStageBoundary`.
Let `k` be a ring equipped with an arbitrary topology (`[Ring k]`
`[TopologicalSpace k]`), `G` a compact topological group, and
`X : TopRep k G` a discrete, jointly continuous
representation. For any open normal subgroup `M`, degree `n : ℕ` and native
continuous-cohomology class `a` of the quotient representation `X^M` over
`G/M`, `ContinuousCohomology.exists_refinement_class_eq_zero X M n a ha`
says: **if** the inflation of `a` to `Hⁿ(G,X)` is zero, **then** some
open normal `N ≤ M` has zero transition image of `a` in `Hⁿ(G/N,X^N)`.
This `N` can depend on `a`; the arrow goes from the coarser `M` stage to the
finer `N` stage. No uniform refinement or positive-degree injectivity of
inflation at a fixed stage is asserted.

`class_eq_zero_of_inflation_zero_degree_zero M X a ha` requires only a
topological group and a ring equipped with a topology, and gives `a = 0`
already at `M` in degree zero.
The positive-degree argument instead represents the zero inflated class by
an **actual boundary** in the native homogeneous complex of `G`, descends its
degree-`n` cochain below `M`, and reflects a degree-`n+1` equality through
injective cochain inflation from `N`. It uses the algebraic boundary criterion
for `TopModuleCat` homology, not closure of the boundary image or a stronger
coefficient-ring hypothesis. The helper comparing a complex with its explicit
`sc' n (n+1) (n+2)` short complex reuses mathlib's cycle/homology isomorphisms.

`exists_refinement_class_eq_of_inflation_eq` applies the zero theorem to the
difference of any two classes at **one common original stage**, giving equal
transition images at some common refinement. The ordinary-import client
`examples.FiniteStageBoundaryNative`
checks degree zero at `M` and degree two for arbitrary (potentially nonzero)
classes. Neither this theorem nor the clients construct a filtered colimit or
compare classes from different initial stages.

The original contributors and upstream results are credited in
[attribution](attribution.md).
