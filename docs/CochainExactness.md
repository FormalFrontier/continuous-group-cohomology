# Short exact sequences on continuous homogeneous cochains

Import `ContinuousGroupCohomology.CochainExactness`. Let `k` be a topologized
ring, `G` a topological group, and `i : A ⟶ B`, `p : B ⟶ C` morphisms of
`TopRep k G` with injective `i`, `Function.Exact i.hom p.hom`, and surjective
`p`. All three induced arrows are the existing `cochainsMap` at the identity
map on `G`, in each natural-number degree.

* Injectivity of the cochain map for `i` is the existing
  `ContinuousCohomology.cochainsMap_injective`. It needs no discreteness,
  compactness or joint continuity.
* `ContinuousCohomology.cochainsMap_exact` states exactness at the middle
  cochain term when `B` is discrete. Since `i` is continuous and injective,
  discreteness of `A` then follows automatically. Compactness and joint
  continuity are not assumptions here.
* `ContinuousCohomology.cochainsMap_surjective` states surjectivity of the
  cochain map for `p` when `G` is locally compact, `C` is discrete, and the action on
  `B` is jointly continuous. It does not assume `B` discrete or a linear or
  equivariant section. `cochainsMap_shortExact` combines the three claims for
  locally compact groups, adding discreteness of `B`. The theorem
  `cochainsMap_shortExact_of_compact` is its compact-group specialization:
  compact topological groups are locally compact without a Hausdorff assumption.

`cochainsMap_resolutionEval` describes evaluation of the existing induced
maps without unfolding the recursive resolution. The
[`ZMod 2` coefficient client](../CGCExamples/CochainExactness.lean) uses the
two-element group acting trivially on `ℤ --×2→ ℤ → ZMod 2`: its coefficient
maps are independently injective, exact and surjective, the quotient is
nonzero, and there is no integer-linear section. Evaluations of degree-zero
and degree-one cochain maps use only the proved evaluation formula, not either
cochain-exactness assertion. The separate degree-zero and degree-one short
exactness specializations use the general cochain-exactness assertions.

The statements do **not** say that invariant coefficients, cocycles or
cohomology preserve epimorphisms. For exactness in the middle, a pointwise
preimage of an element in the kernel is a continuous choice because the middle
coefficient is discrete. Lifting through each recursive compact-open mapping
space produces a resolution term; injectivity of the induced resolution map
then forces invariance. For surjectivity, a set-theoretic section onto the
discrete quotient is continuous without being linear or equivariant. It lifts
the quotient cochain's value at the identity one resolution level lower.
The degree-zero homogeneous-cochain equivalence for that level turns its
orbit map into an invariant lift. Local compactness supplies continuous
evaluation for the compact-open topology and hence joint continuity of the
iterated coinduced actions; without it this proof route does not establish
continuity of those actions. No assertion for arbitrary non-locally-compact
groups is made.

The mathematical antecedent is Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Chapter I, §3 (cochain exactness before Theorem 1.3.2).
The formalization follows Mathlib's `ContRepresentation.coind₁` and
`TopRep.homogeneousCochains`, and Formal Frontier's
`TopRep.resolutionEval_map`, finite-stage resolution discreteness and
cochain injectivity.
