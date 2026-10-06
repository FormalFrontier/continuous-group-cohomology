<!-- SPDX-License-Identifier: Apache-2.0 -->
# Zero homology classes in topological modules

Import `ContinuousGroupCohomology.Algebra.Category.ModuleCat.Topology.HomologyBoundary` to use
`TopModuleCat.shortComplex_homologyπ_eq_zero_iff` for any short complex
`S : CategoryTheory.ShortComplex (TopModuleCat.{v} k)` and cycle `z : S.cycles`:

```lean
S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.toCycles.hom w = z
```

The coefficients require `[Ring k]` and `[TopologicalSpace k]`, with independent
coefficient and object universes. No compatible topological-ring laws,
commutativity, separation, closed-image or split-exactness assumptions are
needed. The quotient defining `TopModuleCat` homology uses the **algebraic**
range of the boundary map; the result does not characterize closure of the
range or a Hausdorff quotient.

The proof uses `ShortComplex.homologyIsCokernel` to compare the existing
homology projection to mathlib's `TopModuleCat.cokerπ`, which projects onto
`S.cycles ⧸ S.toCycles.hom.range`. Quotient-zero gives an actual range witness;
the converse follows from `S.toCycles_comp_homologyπ`. The ordinary-import
entrypoint `examples.HomologyBoundaryNative` retains the production import.
Its equal-class boundary proof, for arbitrary cycles of an arbitrary short
complex, elaborates in `examples.FiniteStageResolutionNative` alongside the
finite-stage boundary, colimit, resolution/sign, quotient-invariants,
resolution-image, cochain, seeded descent, transition, and diagram clients.
Seven current proof environments, comprising ten original environments, now
elaborate together there; importing the forwarding entrypoint tests its
current imports rather than the former isolated boundary-proof environment.

The original contributors and upstream results are credited in
[attribution](attribution.md).
