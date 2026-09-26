/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology

/-!
# Downstream client of the native core

Every proof below uses only the aggregate public import. The split sequence
requires joint continuity of both relevant actions, and degree-one transfer
requires a locally compact topological group. The compact quotient comparison
assumes a compact Hausdorff additive group; the final limit result concerns the
projection at a chosen object of a cofiltered-or-empty diagram of such groups.
-/

set_option autoImplicit false
set_option warningAsError true

public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace NativeCore

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exactness at invariant quotient coefficients in continuous degree one. -/
theorem split_connecting_exact
    {A B C : TopRep.{max v w} k G}
    (sequence : ContinuousCohomology.TopologicallySplitShortExact A B C)
    [LocallyCompactSpace G] [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    Function.Exact sequence.invariantsProjection sequence.connectingMap.hom :=
  sequence.exact_invariantsProjection_connectingMap

/-- For the full open subgroup, restriction followed by transfer is the identity. -/
theorem transfer_from_full_group (X : TopRep.{max v w} k G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    ContinuousCohomology.map
          (ContinuousCohomology.CorestrictionTransversal.openSubgroupInclusion
            (⊤ : OpenSubgroup G))
          (ContinuousCohomology.CorestrictionTransversal.restrictionCoeffHom X
            (⊤ : OpenSubgroup G)) 1 ≫
        ContinuousCohomology.CorestrictionTransversal.corestrictionOne X
          (⊤ : OpenSubgroup G) = 𝟙 _ :=
  ContinuousCohomology.CorestrictionTransversal.corestrictionOne_top X

/-- Finite orbit differences generate precisely the coinvariant relations. -/
theorem finite_orbit_relations
    {R : Type u} [CommRing R] {H : Type v} [Group H] [Fintype H]
    {M : Type w} [AddCommGroup M] [Module R M]
    (representation : Representation R H M) :
    (ContinuousGroupCohomology.finiteOrbitDifference representation).range =
      Representation.Coinvariants.ker representation :=
  ContinuousGroupCohomology.finiteOrbitDifference_range representation

/-- Closed reduction modulo `n` agrees with algebraic reduction on representatives
of a compact Hausdorff additive group. -/
theorem compact_mod_n_representative
    {A : Type u} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A]
    (n : ℕ) (a : A) :
    TopologicalModN.compactModNEquiv (A := A) n (TopologicalModN.mkQ n a) =
      ModN.mkQ n a :=
  TopologicalModN.compactModNEquiv_mk n a

/-- At any chosen object of a cofiltered-or-empty diagram of compact Hausdorff
additive groups, surjective transitions into that object imply a surjective
limit projection. An empty index category has no object at which to apply this. -/
theorem compact_limit_projection
    {J : Type v} [SmallCategory J] [IsCofilteredOrEmpty J]
    (diagram : J ⥤ CompHausAddCommGrp.{max u v}) (index : J)
    (surjective : ∀ {source : J} (arrow : source ⟶ index),
      Function.Surjective (diagram.map arrow)) :
    Function.Surjective (limit.π diagram index) :=
  CompHausAddCommGrp.limit_π_surjective_of_maps_surjective diagram index surjective

end NativeCore

#print axioms NativeCore.split_connecting_exact
#print axioms NativeCore.transfer_from_full_group
#print axioms NativeCore.finite_orbit_relations
#print axioms NativeCore.compact_mod_n_representative
#print axioms NativeCore.compact_limit_projection
