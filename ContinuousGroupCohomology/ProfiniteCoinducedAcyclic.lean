/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ContinuousCohomologyFunctor
public import ContinuousGroupCohomology.CoinducedAcyclic
public import ContinuousGroupCohomology.ProfiniteCoinducedRestriction

/-!
# Positive cohomology of coinduction restricted to closed subgroups

Over a compact group, positive-degree continuous cohomology of a
representation isomorphic to coinduction from discrete coefficients vanishes.
For a closed subgroup of a compact Hausdorff totally disconnected group,
restriction of coinduction is again coinduction, now from the *entire*
continuous function space on the cosets with its pointwise subgroup action.
In particular its positive-degree continuous cohomology vanishes without
requiring the subgroup to be open or normal, or the coefficient action to be
trivial. The same conclusion holds after restricting an isomorphic ambient
representation.

The positive-degree condition is essential: the nonzero integral-coefficient
example `CGCExamples.twoGroup_degree_zero_nonzero` gives nonzero degree-zero
cohomology for coinduction even before restriction.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3, Proposition 1.3.7 (the positive-degree,
  closed-subgroup clause).
* Mathlib's `ContinuousCohomology.map` and its coefficient functoriality.
* `ContinuousGroupCohomology.CoinducedAcyclic` for the coinduced contraction;
  `ContinuousGroupCohomology.ProfiniteCoinducedRestriction` and
  `ProfiniteGroups.ContinuousCosetRepresentative` for the restriction isomorphism.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Positive continuous cohomology of coinduction restricted to *every*
closed subgroup vanishes. The restriction is coinduced from all of
`C(G ⧸ H, B)` with the pointwise `H`-action. This is the positive-degree,
all-closed-subgroup clause of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, I §3,
Proposition 1.3.7. -/
theorem res_coind₁_positive_eq_zero
    (H : Subgroup G) [IsClosed (H : Set G)]
    (B : TopRep.{max v w} k G) [DiscreteTopology B]
    (m : ℕ)
    (a : continuousCohomology (m + 1)
      (TopRep.res H.subtype (TopRep.coind₁ B))) : a = 0 := by
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact coind₁_isomorphic_positive_eq_zero
    (TopRep.pointwiseContinuousMap (G ⧸ H) (TopRep.res H.subtype B))
    (TopRep.profiniteCoind₁RestrictionIso H B) m a

/-- An ambient coefficient isomorphism preserves positive vanishing after
restriction to any closed subgroup of a compact Hausdorff totally
disconnected group. This is the isomorphic-coefficient form of the
positive-degree closed-subgroup clause of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, I §3,
Proposition 1.3.7. -/
theorem res_isomorphic_coind₁_positive_eq_zero
    (H : Subgroup G) [IsClosed (H : Set G)]
    (B : TopRep.{max v w} k G) [DiscreteTopology B]
    {M : TopRep.{max v w} k G} (e : M ≅ TopRep.coind₁ B)
    (m : ℕ)
    (a : continuousCohomology (m + 1) (TopRep.res H.subtype M)) : a = 0 := by
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact coind₁_isomorphic_positive_eq_zero
    (TopRep.pointwiseContinuousMap (G ⧸ H) (TopRep.res H.subtype B))
    (((TopRep.resFunctor H.subtype).mapIso e).trans
      (TopRep.profiniteCoind₁RestrictionIso H B)) m a

end ContinuousCohomology
