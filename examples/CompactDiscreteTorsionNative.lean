/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactDiscreteTorsion
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory ContinuousCohomology

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.CompactDiscreteTorsion

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
  [TopRep.JointlyContinuous X]

private theorem arbitrary_degree_difference (n : ℕ) (a b : continuousCohomology n X) :
    ∃ (N : OpenNormalSubgroup G)
      (c : continuousCohomology n (TopRep.quotientInvariants N.toSubgroup X)),
        (ContinuousCohomology.map (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom c = a - b :=
  exists_openNormal_quotient_class_lift X n (a - b)

private theorem degree_zero_difference (a b : continuousCohomology 0 X) :
    ∃ (N : OpenNormalSubgroup G)
      (c : continuousCohomology 0 (TopRep.quotientInvariants N.toSubgroup X)),
        (ContinuousCohomology.map (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 0).hom c = a - b :=
  exists_openNormal_quotient_class_lift X 0 (a - b)

private theorem degree_one_sum (a b : continuousCohomology 1 X) :
    ∃ N : OpenNormalSubgroup G, Nat.card (G ⧸ N.toSubgroup) • (a + b) = 0 :=
  exists_openNormal_quotient_card_nsmul_eq_zero X 0 (a + b)

private theorem arbitrary_positive_degree (n : ℕ)
    (a : continuousCohomology (n + 1) X) : IsOfFinAddOrder (2 • a) :=
  compactDiscrete_isAddTorsion X n (2 • a)

private theorem zero_class (n : ℕ) :
    ∃ N : OpenNormalSubgroup G,
      Nat.card (G ⧸ N.toSubgroup) • (0 : continuousCohomology (n + 1) X) = 0 :=
  exists_openNormal_quotient_card_nsmul_eq_zero X n 0

private abbrev signRepresentation : TopRep ℤ (Units ℤ) :=
  TopRep.of <| ContRepresentation.ofMonoidHom {
    toFun := fun unit => (unit : ℤ) • (1 : ℤ →L[ℤ] ℤ)
    map_one' := by
      ext
      simp
    map_mul' := by
      intro first second
      ext
      simp [Units.val_mul]
  }

private instance : TopRep.JointlyContinuous signRepresentation where
  continuous_action := continuous_of_discreteTopology

private theorem sign_action_nontrivial :
    signRepresentation.ρ (-1 : Units ℤ) (1 : signRepresentation) ≠
      (1 : signRepresentation) := by
  change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠ 1
  norm_num

private theorem sign_action_degree_zero (a : continuousCohomology 0 signRepresentation) :
    ∃ (N : OpenNormalSubgroup (Units ℤ))
      (c : continuousCohomology 0
        (TopRep.quotientInvariants N.toSubgroup signRepresentation)),
        (ContinuousCohomology.map (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup signRepresentation) 0).hom c = a :=
  exists_openNormal_quotient_class_lift signRepresentation 0 a

private theorem sign_action_degree_three (a : continuousCohomology 3 signRepresentation) :
    ∃ N : OpenNormalSubgroup (Units ℤ),
      Nat.card ((Units ℤ) ⧸ N.toSubgroup) • a = 0 := by
  simpa only [Nat.reduceAdd] using
    exists_openNormal_quotient_card_nsmul_eq_zero signRepresentation 2 a

private abbrev zeroRepresentation : TopRep ℤ PUnit :=
  TopRep.of (ContRepresentation.trivial ℤ PUnit PUnit)

private instance : TopRep.JointlyContinuous zeroRepresentation where
  continuous_action := continuous_of_discreteTopology

private theorem zero_coefficient_degree_one
    (a : continuousCohomology 1 zeroRepresentation) : IsOfFinAddOrder a := by
  simpa only [Nat.reduceAdd] using compactDiscrete_isAddTorsion zeroRepresentation 0 a

end IncubatorTest.RepresentationTheory.ContinuousCohomology.CompactDiscreteTorsion
