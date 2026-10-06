# Classwise finite quotient descent and compact discrete torsion

Import `ContinuousGroupCohomology.CompactDiscreteTorsion`.
Let `k` be any ring equipped with a topology, `G` any compact topological group, and
`X : TopRep k G` a discrete representation with jointly continuous action.
In all degrees `n`, `ContinuousCohomology.exists_openNormal_quotient_class_lift`
expresses **each native class** as the image of a class over `G ⧸ N` for
some open normal subgroup `N`, with coefficients in the actual
`TopRep.quotientInvariants N.toSubgroup X`.

The group homomorphism `openNormalQuotientHom N : G →ₜ* G ⧸ N` induces
`ContinuousCohomology.map` in the **opposite** cohomological direction:
from the quotient-invariant coefficients on `G ⧸ N` to `X` on `G`.
The proof takes a cocycle representative using the concrete surjectivity of
`π`, lifts its closed homogeneous cochain via the existing finite-stage
theorem, packages the lifted cochain using the short complex's genuine
topological-module kernel, then uses `π_map` to identify the classes. This
is classwise surjectivity from *some* stage, not injectivity of any map.

For degree `n + 1`,
`ContinuousCohomology.exists_openNormal_quotient_card_nsmul_eq_zero`
produces `N` such that `Nat.card (G ⧸ N.toSubgroup) • a = 0`.
The quotient is finite because `N` is open and `G` compact; its natural
order is positive. Finite-group averaging annihilates the lifted class,
and its native additive cohomology map carries that equation to `a`.
`ContinuousCohomology.compactDiscrete_isAddTorsion` packages this as
`IsAddTorsion (continuousCohomology (n + 1) X)`.

The ordinary-import private clients in
[`ContinuousTorsionNative`](../examples/ContinuousTorsionNative.lean) test an
arbitrary ring and positive degree, degree-zero lifting of a difference,
degree-one sums, degree three with a genuinely nontrivial sign action, zero
coefficients and a zero class.
Neither the quotient nor its order is uniform across classes. Degree-zero
classes lift but need not be torsion (e.g. the trivial group with integral
coefficients). There is no cohomology injectivity, boundary lifting,
filtered-colimit comparison, inflation-restriction, acyclicity, vanishing,
or claim concerning a separately modeled explicit H¹.

The host also checks degree-one torsion and arbitrary-degree discreteness.
Its combined imports replace all three former independent proof-import
environments, including the degree-one torsion client's former Torsion-only
check; the [compact torsion entrypoint](../examples/CompactDiscreteTorsionNative.lean)
retains its original public producer and Mathlib imports and imports the host
ordinarily, without re-exporting it. To use the theorem, import
`ContinuousGroupCohomology.CompactDiscreteTorsion`, not the example module.

See [attribution](attribution.md) for contributor lineage and rights scope.
