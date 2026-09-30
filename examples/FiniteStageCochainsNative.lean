module

public import ContinuousGroupCohomology.FiniteStageCochains
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units

set_option warningAsError true

@[expose] public section

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageCochains

open _root_.ContinuousCohomology CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

section CompactCoefficients

variable [CompactSpace G] [DiscreteTopology X] [TopRep.JointlyContinuous X]

private theorem degree_zero (σ : (TopRep.homogeneousCochains X).X 0) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 0),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 0) τ = σ :=
  exists_openNormal_quotient_cochain_lift X 0 σ

private theorem degree_two (σ : (TopRep.homogeneousCochains X).X 2) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 2),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 2) τ = σ :=
  exists_openNormal_quotient_cochain_lift X 2 σ

private theorem degree_two_closed (σ : (TopRep.homogeneousCochains X).X 2)
    (hσ : (TopRep.homogeneousCochains X).d 2 3 σ = 0) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 2),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 2) τ = σ ∧
          (TopRep.homogeneousCochains
            (TopRep.quotientInvariants N.toSubgroup X)).d 2 3 τ = 0 :=
  exists_openNormal_quotient_closed_cochain_lift X 2 σ hσ

private theorem zero_closed :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 0),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 0) τ = 0 ∧
          (TopRep.homogeneousCochains
            (TopRep.quotientInvariants N.toSubgroup X)).d 0 1 τ = 0 := by
  apply exists_openNormal_quotient_closed_cochain_lift X 0 0
  simp

end CompactCoefficients

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

private theorem sign_orbit_cochain_lift :
    ∃ (σ : (TopRep.homogeneousCochains signRepresentation).X 0),
      (∀ g : Units ℤ, σ.1 g = signRepresentation.ρ g (1 : signRepresentation)) ∧
      σ.1 (-1 : Units ℤ) ≠ σ.1 1 ∧ σ.1 (-1 : Units ℤ) ≠ 0 ∧
      ∃ (N : OpenNormalSubgroup (Units ℤ))
        (τ : (TopRep.homogeneousCochains
          (TopRep.quotientInvariants N.toSubgroup signRepresentation)).X 0),
          ((cochainsMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup signRepresentation)).f 0) τ = σ := by
  let orbit : TopRep.resolutionX signRepresentation 1 :=
    ⟨fun g => signRepresentation.ρ g (1 : signRepresentation),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hfix : orbit ∈ (TopRep.resolutionX signRepresentation 1).ρ.invariants := by
    intro g
    apply ContinuousMap.ext
    intro h
    change signRepresentation.ρ g
      (signRepresentation.ρ (g⁻¹ * h) (1 : signRepresentation)) =
        signRepresentation.ρ h (1 : signRepresentation)
    change (signRepresentation.ρ g * signRepresentation.ρ (g⁻¹ * h))
      (1 : signRepresentation) = signRepresentation.ρ h (1 : signRepresentation)
    rw [← map_mul, mul_inv_cancel_left]
  let σ : (TopRep.homogeneousCochains signRepresentation).X 0 := ⟨orbit, hfix⟩
  have hnonconstant : σ.1 (-1 : Units ℤ) ≠ σ.1 1 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠
      ((1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1
    norm_num
  have hnonzero : σ.1 (-1 : Units ℤ) ≠ 0 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠ 0
    norm_num
  obtain ⟨N, τ, hτ⟩ := exists_openNormal_quotient_cochain_lift signRepresentation 0 σ
  exact ⟨σ, fun _ => rfl, hnonconstant, hnonzero, N, τ, hτ⟩

end IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageCochains
