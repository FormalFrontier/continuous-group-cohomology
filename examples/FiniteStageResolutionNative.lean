module

public import ContinuousGroupCohomology.FiniteStageResolution
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units

set_option warningAsError true

@[expose] public section

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageResolution

open _root_.ContinuousCohomology CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

private theorem empty_refinement (N₀ : OpenNormalSubgroup G) (i : ℕ) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ a ∈ (∅ : Finset (TopRep.resolutionX X i)), StageDescends X N i a :=
  exists_common_stage_refinement X N₀ i ∅ (by simp)

private theorem singleton_refinement (N₀ M : OpenNormalSubgroup G) (i : ℕ)
    (a : TopRep.resolutionX X i) (ha : StageDescends X M i a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ b ∈ ({a} : Finset (TopRep.resolutionX X i)), StageDescends X N i b := by
  classical
  apply exists_common_stage_refinement X N₀ i {a}
  intro b hb
  obtain rfl := Finset.mem_singleton.mp hb
  exact ⟨M, ha⟩

section CompactCoefficients

variable [CompactSpace G] [DiscreteTopology X] [TopRep.JointlyContinuous X]

private theorem level_zero (a : X) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 0 a :=
  exists_openNormal_stage_descends X 0 a

private theorem level_one (a : TopRep.resolutionX X 1) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 1 a :=
  exists_openNormal_stage_descends X 1 a

private theorem level_three (a : TopRep.resolutionX X 3) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 3 a :=
  exists_openNormal_stage_descends X 3 a

private theorem level_three_lift (a : TopRep.resolutionX X 3) :
    ∃ (N : OpenNormalSubgroup G)
      (b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 3),
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 3).hom b = a :=
  exists_openNormal_resolution_lift X 3 a

end CompactCoefficients

private abbrev signRepresentation : TopRep ℤ (Units ℤ) :=
  TopRep.of <| ContRepresentation.ofMonoidHom {
    toFun := fun unit => (unit : ℤ) • (1 : ℤ →L[ℤ] ℤ)
    map_one' := by
      ext
      simp
    map_mul' := by
      intro a b
      ext
      simp [Units.val_mul]
  }

private instance : TopRep.JointlyContinuous signRepresentation where
  continuous_action := continuous_of_discreteTopology

private theorem sign_orbit_lift :
    ∃ (orbit : TopRep.resolutionX signRepresentation 1),
      (∀ g : Units ℤ, orbit g = signRepresentation.ρ g (1 : signRepresentation)) ∧
      orbit (-1 : Units ℤ) ≠ orbit 1 ∧ orbit (-1 : Units ℤ) ≠ 0 ∧
      ∃ (N : OpenNormalSubgroup (Units ℤ))
        (b : TopRep.resolutionX
          (TopRep.quotientInvariants N.toSubgroup signRepresentation) 1),
          (resolutionMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup signRepresentation) 1).hom b =
              orbit := by
  let orbit : TopRep.resolutionX signRepresentation 1 :=
    ⟨fun g => signRepresentation.ρ g (1 : signRepresentation),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hnonconstant : orbit (-1 : Units ℤ) ≠ orbit 1 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠
      ((1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1
    norm_num
  have hnonzero : orbit (-1 : Units ℤ) ≠ 0 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠ 0
    norm_num
  obtain ⟨N, b, hb⟩ := exists_openNormal_resolution_lift signRepresentation 1 orbit
  exact ⟨orbit, fun _ => rfl, hnonconstant, hnonzero, N, b, hb⟩

end IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageResolution
