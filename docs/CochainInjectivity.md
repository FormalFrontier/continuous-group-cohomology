# Injective restriction on native continuous cochains (2026-09-30)

Import `ContinuousGroupCohomology.CochainInjectivity`.
For topological groups `G`, `H` in the native same-universe setup, an arbitrary
topological `Ring k`, `φ : H →ₜ* G`, representations `X : TopRep k G` and
`Y : TopRep k H`, and `f : TopRep.res φ X ⟶ Y`, assume only
`Function.Surjective φ` and `Function.Injective f.hom`. There is **no** compactness,
discreteness, Hausdorff, finiteness, splitting or joint-continuity assumption.

* `ContinuousCohomology.resolutionMap_injective` proves injectivity at every
  resolution level, including level zero. At each successor, the formula
  `(coind₁ResMap φ f F) h = f (F (φ h))` and a preimage of every `g : G`
  provide pointwise injectivity of continuous maps; there is no topological
  inverse to `φ`.
* `ContinuousCohomology.cochainsMap_injective` restricts the level `n + 1`
  result to invariant elements of the native homogeneous complex in degree `n`.
* `ContinuousCohomology.cocyclesMap_injective` applies the native generic
  `HomologicalComplex.cyclesMap` monomorphism to an injective component;
  concrete injectivity is justified by the limit-preserving forgetful functor
  from topological modules to topological spaces and then to types.
* `ContinuousCohomology.cochainsMap_d_eq_zero_iff` reflects differential
  vanishing using the actual cochain-map square and injectivity in degree
  `n + 1`. It is the cocycle condition at the level of cochain elements.

The named ordinary-import clients in
`examples.CochainInjectivityNative`
check arbitrary-degree generic `Ring`/universe applications (including degrees
zero and two), and the surjection `G → G ⧸ N` for a normal subgroup, with
trivial-action integer coefficients injected into `ℤ × ℤ` by `a ↦ (a, 0)`.
The latter coefficient map is demonstrably not surjective.

**Boundary:** injectivity on cochains and cocycles does *not* prove injectivity
of `ContinuousCohomology.map` on cohomology. A cocycle that becomes a boundary
in the target need not lift a primitive in the source. No boundary lifting,
quotient descent, inflation isomorphism, compact/torsion conclusion or source
correspondence is supplied.

Upstream mathematical definitions and resolution/cochain maps are those of
mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`, especially
`Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality`
(Edison Xie and Richard Hill), `Mathlib.RepresentationTheory.Continuous.Basic`
and `Mathlib.RepresentationTheory.Continuous.TopRep`.

See [attribution](attribution.md) for contributor lineage and rights scope.
