/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageBoundary

/-!
# Ordinary-import clients for eventual zero and equality

All representations and classes are arbitrary; in particular the degree-two
client does not assume that either cohomology group vanishes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem degree_zero_at_original_stage (X : TopRep.{max v w} k G)
    (M : OpenNormalSubgroup G)
    (a : continuousCohomology 0 (TopRep.quotientInvariants M.toSubgroup X))
    (ha : (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) 0).hom a = 0) :
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom M M le_rfl)
      (ContinuousCohomology.quotientTransitionIncl X le_rfl) 0).hom a = 0 := by
  have hz := ContinuousCohomology.class_eq_zero_of_inflation_zero_degree_zero M X a ha
  simp only [hz, map_zero]

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X]

private theorem degree_two_eventual_equality (M : OpenNormalSubgroup G)
    (a b : continuousCohomology 2 (TopRep.quotientInvariants M.toSubgroup X))
    (hab : (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) 2).hom a =
      (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) 2).hom b) :
    ∃ (N : OpenNormalSubgroup G) (hNM : N ≤ M),
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) 2).hom a =
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) 2).hom b :=
  ContinuousCohomology.exists_refinement_class_eq_of_inflation_eq X M 2 a b hab

end CGCExamples.ContinuousCohomology
