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
client `examples.HomologyBoundaryNative`
extracts a boundary for `z₁ - z₂` from equal homology images for arbitrary
cycles of an arbitrary short complex.

The original contributors and upstream results are credited in
[attribution](attribution.md).
