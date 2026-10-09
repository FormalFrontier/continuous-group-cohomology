<!-- SPDX-License-Identifier: Apache-2.0 -->
# Discrete native continuous cohomology

Import `ContinuousGroupCohomology.DiscreteCohomology`.
For any `n : ℕ`, the theorem
`ContinuousCohomology.discreteTopology_continuousCohomology X n` proves
`DiscreteTopology (continuousCohomology n X)` for a compact topological group
`G`, a discrete `X : TopRep.{max v w} k G`, and a possibly noncommutative
`[Ring k] [TopologicalSpace k]`. Its other group assumptions are `[Group G]`,
`[TopologicalSpace G]`, and `[IsTopologicalGroup G]`. The coefficient action need
not be jointly continuous; no `T2Space`, finite-coefficient, or closed-range
assumption is needed. The result includes degree zero and preserves independent
universes for the ring, group, and coefficient representation.

The proof reuses the published
`ContinuousCohomology.discreteTopology_resolutionX` and the compact-open lemma
behind it. Actual native homogeneous cochains are invariant submodules of
`TopRep.resolutionX X (n + 1)` with the subspace topology. The *chosen* cocycles
are identified through `ShortComplex.isoCyclesOfIsLimit` with the concrete
kernel of the differential, which has the subspace topology. The *chosen*
homology is identified through `IsColimit.coconePointUniqueUpToIso` with the
concrete `TopModuleCat.coker` of `toCycles`: the quotient by its **algebraic
range**, carrying the quotient topology. Subspaces and quotients of these
discrete spaces are discrete. Both identifications are actual `TopModuleCat`
isomorphisms, so the transport uses a continuous inverse, not just a
continuous bijection. The coefficient ring retains its given topology.

The arbitrary-degree and arbitrary-coefficient clients reside in
[`ContinuousTorsionNative`](../examples/ContinuousTorsionNative.lean), alongside
compact finite-quotient and degree-one torsion clients. The
[`DiscreteCohomologyNative` entrypoint](../examples/DiscreteCohomologyNative.lean)
imports this client and the production module. Import
`ContinuousGroupCohomology.DiscreteCohomology` to use the theorem.
This theorem neither constructs a finite-stage colimit nor assumes or proves
eventual vanishing of a class at a refined stage.

The original contributors and upstream results are credited in
[attribution](attribution.md).
