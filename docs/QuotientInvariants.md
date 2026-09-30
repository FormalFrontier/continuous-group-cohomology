# Quotient representations on invariant topological submodules

SPDX-License-Identifier: Apache-2.0

Import `ContinuousGroupCohomology.QuotientInvariants` for the
following source-independent API. Let `k : Type u` have `[Ring k]` and
`[TopologicalSpace k]`, let `G : Type v` have `[Group G]`, let
`N : Subgroup G` have `[N.Normal]`, and let `X : TopRep.{w} k G`. The universes
of the coefficient ring, group and representation carrier are independent.
No group topology is needed for the pointwise-continuous construction:

* `TopRep.quotientInvariants N X` is a native `TopRep k (G ⧸ N)` on **exactly**
  `(X.ρ.restrict N.subtype).invariants`, equipped with the inherited submodule
  topology. `TopRep.quotientInvariants_ρ_mk N X g x` computes the quotient
  action at `QuotientGroup.mk' N g` as `X.ρ g x.1` after inclusion in `X`.
* `TopRep.quotientInvariantsIncl N X` is the continuous equivariant morphism
  `TopRep.res (QuotientGroup.mk' N) (TopRep.quotientInvariants N X) ⟶ X`.
  `TopRep.quotientInvariantsFunctor (k := k) N` acts on native TopRep morphisms.
  `TopRep.quotientInvariantsFunctor_map_val` and
  `TopRep.quotientInvariantsIncl_naturality` give its elementwise map and
  inclusion square.
* If `[TopologicalSpace G] [SeparatelyContinuousMul G]` and
  `[TopRep.JointlyContinuous X]` hold, then
  `TopRep.jointlyContinuous_quotientInvariants N X` gives joint continuity for
  arbitrary normal `N`: the proof uses the **open** quotient map on
  `G × (X.ρ.restrict N.subtype).invariants`. No open/closed/T2 condition on
  `N` is used.
* Alternatively, if `IsOpen (N : Set G)` and
  `[SeparatelyContinuousMul G]` hold, then
  `TopRep.jointlyContinuous_quotientInvariants_of_isOpen N X hN` gives joint
  continuity *without* assuming it of `X`: the existing quotient topology is
  discrete and every individual quotient operator is continuous. If `X`
  itself is discrete, the invariant carrier inherits discreteness independently
  of either joint-action result.

Pointwise-continuous `TopRep` operators do **not** imply a jointly continuous
action for arbitrary `N`. In cohomology, a future use of `cochainsMap` may require
the displayed inclusion as the coefficient arrow after restriction along the
quotient homomorphism; this module does not construct cochains, descent or an
inflation equivalence. Ordinary-import private clients cover the generic
noncommutative-ring signature, coefficient functor and naturality, the two
joint-continuity hypotheses, degenerate cases and a concrete open subgroup
with real (nondiscrete) coefficients.

See the [ordinary-import client](../examples/QuotientInvariantsNative.lean).

See [attribution](attribution.md) for contributor lineage and rights scope.
