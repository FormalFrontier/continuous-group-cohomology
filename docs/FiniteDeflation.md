# Finite-level exceptional deflation

Import `ContinuousGroupCohomology` for the public native core, or import
`ContinuousGroupCohomology.ExceptionalDeflation` /
`ContinuousGroupCohomology.FiniteDeflationTransitivity` for these interfaces.
The definitions live in namespace `ContinuousGroupCohomology`. This is a
manually curated guide to the **current Lean sources**, not an extension of
the [historical generated API snapshot](API.md).

## Setup and hypotheses

Take `R G : Type u`, `[CommRing R]`, `[Group G]`, `A : Rep.{u} R G`,
normal subgroups `S ≤ T` of `G`, and the actual finite quotient-image
instance `[Fintype (T.map (QuotientGroup.mk' S))]`. The homology and
exceptional-degree interfaces use this **same universe** `u`. For Tate
degrees `-1` and `0` and the norm-kernel/cokernel maps, additionally supply
`[Fintype (G ⧸ S)]` and `[Fintype (G ⧸ T)]`. Check the linked declarations
for their precise typeclass and implicit binders; no finiteness is inferred
just from subgroup normality. `A.quotientToInvariants S` and
`A.quotientToInvariants T` are representations of the corresponding quotients.

## Maps and naturality

- [`finiteNegativeDeflationCoinvariants`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L42)
  transports degree-zero homology deflation to coinvariants;
  [`finiteNegativeDeflationCoinvariants_mk_hom`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L156)
  states its generator formula.
- [`finiteLevelTotalInvariantsEquiv`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L54)
  identifies the two total invariant modules;
  [`finiteNegativeDeflationCoinvariants_norm`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L230)
  relates it to the finite-group norm.
- [`finiteNegativeOneDeflationKernel`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L281)
  and [`finiteZeroDeflationCokernel`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L317)
  are the induced norm-kernel and norm-cokernel morphisms. Their
  [`kernel`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L387)
  and [`cokernel`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L433)
  naturality theorems handle representation morphisms.
- [`finiteNegativeOneDeflation`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L479)
  and [`finiteZeroDeflation`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L494)
  transport these maps through the finite-group Tate norm isomorphisms;
  their [`negative-one`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L575)
  and [`zero`](../ContinuousGroupCohomology/ExceptionalDeflation.lean#L627)
  naturality lemmas commute with coefficient morphisms.

The [direct client](../examples/ExceptionalDeflationNative.lean) checks
nontrivial bottom/top finite-group specializations, distinct coefficient
representations and the norm and naturality squares. The published Tate Basic
dependency supplies the exceptional Tate/norm identification bridges; its
Norm module agrees with the previous pinned revision.

## Transitivity and limits

For `S ≤ T ≤ U` normal in `G`, the laws below require *all three*
quotient-image finiteness instances for the pairs `(S,T)`, `(T,U)` and
`(S,U)`; Tate and kernel/cokernel laws also require finite `G ⧸ S`, `G ⧸ T`
and `G ⧸ U`. Identity statements have their own self-image finiteness
hypothesis. In the [transitivity source](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean):

- [`finiteDeflationGroupHom`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L70)
  is the quotient homomorphism, while
  [`finiteNegativeDeflationCoeffDirect`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L160)
  provides a direct coefficient map and
  [`finiteNegativeDeflation_eq_direct_map`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L196)
  identifies its homology action.
- [`finiteNegativeDeflation_comp`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L322)
  holds in each natural homology degree. Coinvariants have
  [`composition`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L385)
  and [`identity`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L402)
  laws; total invariants have the corresponding comparison laws.
- Norm-kernel and norm-cokernel maps have
  [`kernel composition`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L411)
  and [`cokernel composition`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L442),
  while Tate degrees `-1` and `0` have
  [`composition`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L474)
  and [`composition`](../ContinuousGroupCohomology/FiniteDeflationTransitivity.lean#L504)
  respectively, plus their adjacent `*_refl` lemmas.

The [three-level client](../examples/FiniteDeflationTransitivityNative.lean)
specializes to a proper intermediate subgroup of a four-element finite group.
The private auxiliary `prodEquivOfExact` is an equivalence of underlying
**sets**, not a group direct-product splitting. No compact inverse limit,
topological exactness, all-degree Tate equivalence or source coverage is claimed.
A source-specific coverage determination is separate from this mathematical
API and its current library review.
