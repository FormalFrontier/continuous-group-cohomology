module

public import ContinuousGroupCohomology.ResolutionImage
public import Mathlib.Data.Int.Order.Units

set_option warningAsError true

@[expose] public section

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.ResolutionImage

open _root_.ContinuousCohomology

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) (N : OpenNormalSubgroup G)

private theorem level_zero (x : X) :
    StageDescends X N 0 x ↔
      ∃ b : TopRep.quotientInvariants N.toSubgroup X,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 0).hom b = x :=
  stageDescends_iff_exists_lift X N 0 x

private theorem level_one (F : TopRep.resolutionX X 1) :
    ((∀ g : G, StageDescends X N 0 (F g)) ∧
      ∀ (g : G) (t : N.toSubgroup), F (g * t.1) = F g) ↔
      ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 1,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 1).hom b = F :=
  stageDescends_iff_exists_lift X N 1 F

private theorem level_three (F : TopRep.resolutionX X 3) :
    StageDescends X N 3 F ↔
      ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 3,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 3).hom b = F :=
  stageDescends_iff_exists_lift X N 3 F

private theorem refinement {M : OpenNormalSubgroup G} (h : N ≤ M)
    (F : TopRep.resolutionX X 3) (hF : StageDescends X M 3 F) :
    StageDescends X N 3 F :=
  stageDescends_antitone X h 3 F hF

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

private abbrev fullSubgroup : OpenNormalSubgroup (Units ℤ) :=
  ⟨⟨⊤, isOpen_discrete _⟩, inferInstance⟩

private theorem sign_action_nontrivial :
    signRepresentation.ρ (-1 : Units ℤ) (1 : signRepresentation) = -1 := by
  change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 = -1
  norm_num

private theorem sign_nonfixed :
    ¬ StageDescends signRepresentation fullSubgroup 0 (1 : signRepresentation) := by
  intro h
  have hneg := h ⟨(-1 : Units ℤ), Subgroup.mem_top _⟩
  change signRepresentation.ρ (-1 : Units ℤ) (1 : signRepresentation) = 1 at hneg
  rw [sign_action_nontrivial] at hneg
  norm_num at hneg

private abbrev nonfixedConstant : C(Units ℤ, ℤ) :=
  ContinuousMap.const _ (1 : ℤ)

private theorem constant_right_cosets (g : Units ℤ) (t : fullSubgroup.toSubgroup) :
    nonfixedConstant (g * t.1) = nonfixedConstant g := rfl

private theorem right_constant_not_liftable :
    ¬ ∃ b : TopRep.resolutionX
        (TopRep.quotientInvariants fullSubgroup.toSubgroup signRepresentation) 1,
      (resolutionMap (openNormalQuotientHom fullSubgroup)
        (TopRep.quotientInvariantsIncl fullSubgroup.toSubgroup signRepresentation) 1).hom b =
        nonfixedConstant := by
  intro h
  have hdescent := (stageDescends_iff_exists_lift signRepresentation fullSubgroup 1
    nonfixedConstant).mpr h
  exact sign_nonfixed (hdescent.1 1)

end IncubatorTest.RepresentationTheory.ContinuousCohomology.ResolutionImage
