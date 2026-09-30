# Finite averaging in native continuous cohomology

Import `ContinuousGroupCohomology.FiniteAveraging`.
This module uses mathlib's `TopRep` representations and
`continuousCohomology`; it does not define another cohomology theory.

For a finite topological group `G`, a topologized (possibly noncommutative)
ring `k`, and any `TopRep.{max v w} k G`, the public endpoint is
`ContinuousCohomology.finiteGroup_card_nsmul X n a`:

```lean
Nat.card G • a = 0
```

Here `[Finite G]`, `n : ℕ`, and
`a : continuousCohomology (n + 1) X`. The additive torsion consequence is
`ContinuousCohomology.finiteGroup_isAddTorsion X n`; no global torsion
instance is installed. No compactness, T2, discrete or torsion coefficients,
joint action continuity, trivial action, or invertibility of the order is
assumed. The assertions do **not** include degree zero.

The construction `TopRep.finiteSumCoind Y` is an equivariant continuous
linear morphism `Y.coind₁ ⟶ Y` evaluating and summing over `G`.
`TopRep.coind₁ι_comp_finiteSumCoind` gives the unit law
`ι ≫ S = Fintype.card G • 𝟙`, and
`TopRep.coind₁Map_comp_finiteSumCoind` is naturality. With mathlib's native
recursion `d (n+1) = ι - coind₁Map (d n)`, they yield
`TopRep.finiteSumCochain_comp_d_add_d_comp_finiteSumCochain` on shifted
invariant cochains in degree `n+1`. The identity states `s d + d s = |G|`
in that degree, *not* on the entire unaugmented complex.

`TopModuleCat.shortComplex_homologyπ_surjective` proves that the homology
projection has a genuinely surjective underlying function: a concrete
`TopModuleCat.cokerπ` is surjective and its cokernel is isomorphic to the
chosen native homology object. `ContinuousCohomology.π_surjective` specializes
it to continuous cohomology. Hence the boundary calculation for cocycles
applies to every class. The quotient is the algebraic kernel/image homology,
not a quotient by closure. Native cochains are iterated continuous maps,
not definitionally functions on Cartesian powers.

`examples.FiniteAveragingNative`
has named import-only clients in arbitrary positive degree, degree two,
arbitrary integral-coefficient representations, the trivial group, and an
indiscrete two-element group. Neither a compact-group extension nor a
finite-quotient comparison is asserted here.

See [attribution](attribution.md) for contributor lineage and rights scope.
