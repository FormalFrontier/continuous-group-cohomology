/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Torsion
import ContinuousGroupCohomology.CompactDiscreteTorsion
import ContinuousGroupCohomology.DiscreteCohomology
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Int.Order.Units

/-!
# Continuous cohomology clients for compact groups

The integral representation is arbitrary: the client does not assume its
coefficients are torsion, finite, finitely generated, or acted on trivially.
The compact finite-quotient, positive-degree torsion, and arbitrary-degree
discreteness clients below retain their own hypotheses. This module publicly
imports `ContinuousGroupCohomology.Torsion`, with the compact discrete torsion
and discreteness production modules imported for the clients. Import each
production module directly to use its mathematical API.
-/

set_option autoImplicit false

public section

universe v w

namespace ContinuousTorsionNative

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} ℤ G) [DiscreteTopology X]
    [TopRep.JointlyContinuous X] [CompactSpace G]

/-- Specialization of the public API to integral representations. -/
theorem integralDegreeOne : IsAddTorsion (continuousCohomology 1 X) :=
  ContinuousCohomology.isAddTorsion_degreeOne X

/-- An open subgroup of the compact acting group may act nontrivially too. -/
theorem openSubgroupDegreeOne (H : OpenSubgroup G) :
    IsAddTorsion (continuousCohomology 1 (TopRep.res H.subtype X)) := by
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact ContinuousCohomology.isAddTorsion_degreeOne (TopRep.res H.subtype X)

end ContinuousTorsionNative

end

@[expose] public section

set_option warningAsError true

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

end

@[expose] public section

set_option warningAsError true

universe u v w z

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

private theorem arbitrary_degree (n : ℕ) :
    DiscreteTopology (continuousCohomology n X) := by
  have : DiscreteTopology (continuousCohomology n X) :=
    ContinuousCohomology.discreteTopology_continuousCohomology X n
  exact inferInstance

private theorem arbitrary_function_is_continuous (n : ℕ)
    {Y : Type z} [TopologicalSpace Y] (f : continuousCohomology n X → Y) :
    Continuous f := by
  have : DiscreteTopology (continuousCohomology n X) := arbitrary_degree X n
  exact continuous_of_discreteTopology

end CGCExamples.ContinuousCohomology

end
