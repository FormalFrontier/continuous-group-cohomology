module

public import ContinuousGroupCohomology.FiniteStageResolution
public import ContinuousGroupCohomology.CochainInjectivity

set_option warningAsError true

/-!
# Finite stages for homogeneous continuous cochains

Every native homogeneous cochain with discrete, jointly continuous coefficients over a
compact group comes from a cochain on one open-normal quotient with its genuine
quotient-invariant coefficients. If its differential vanishes, the same lift has
vanishing differential. These results do not assert descent of cohomology classes.
-/

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

/-- An invariant homogeneous cochain descends from the invariant coefficients of
one open-normal quotient. Degree `n` cochains use resolution level `n + 1`. -/
theorem exists_openNormal_quotient_cochain_lift [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X] (n : ℕ) (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X n),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n) τ = σ := by
  obtain ⟨N, b, hb⟩ := exists_openNormal_resolution_lift X (n + 1) σ.1
  have hsurj : Function.Surjective (openNormalQuotientHom N) :=
    QuotientGroup.mk'_surjective N.toSubgroup
  have hincl : Function.Injective
      (TopRep.quotientInvariantsIncl N.toSubgroup X).hom :=
    Subtype.val_injective
  have hmap := resolutionMap_injective (openNormalQuotientHom N)
    (TopRep.quotientInvariantsIncl N.toSubgroup X) hsurj hincl (n + 1)
  have hbinv : b ∈ (TopRep.resolutionX
      (TopRep.quotientInvariants N.toSubgroup X) (n + 1)).ρ.invariants := by
    intro q
    obtain ⟨g, rfl⟩ := hsurj q
    apply hmap
    calc
      (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) (n + 1)).hom
          ((TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X)
            (n + 1)).ρ (openNormalQuotientHom N g) b) =
        (TopRep.resolutionX X (n + 1)).ρ g
          ((resolutionMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup X) (n + 1)).hom b) :=
          (resolutionMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup X) (n + 1)).hom.isIntertwining g b
      _ = (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) (n + 1)).hom b := by
        rw [hb]
        exact σ.2 g
  exact ⟨N, ⟨b, hbinv⟩, Subtype.ext hb⟩

/-- A closed native homogeneous cochain admits a closed lift at the same open-normal
quotient stage. The vanishing differential lies in degree `n + 1`. -/
theorem exists_openNormal_quotient_closed_cochain_lift [CompactSpace G]
    [DiscreteTopology X] [TopRep.JointlyContinuous X] (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n)
    (hσ : (TopRep.homogeneousCochains X).d n (n + 1) σ = 0) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X n),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n) τ = σ ∧
          (TopRep.homogeneousCochains
            (TopRep.quotientInvariants N.toSubgroup X)).d n (n + 1) τ = 0 := by
  obtain ⟨N, τ, hτ⟩ := exists_openNormal_quotient_cochain_lift X n σ
  have hsurj : Function.Surjective (openNormalQuotientHom N) :=
    QuotientGroup.mk'_surjective N.toSubgroup
  have hincl : Function.Injective
      (TopRep.quotientInvariantsIncl N.toSubgroup X).hom :=
    Subtype.val_injective
  refine ⟨N, τ, hτ, ?_⟩
  exact ((cochainsMap_d_eq_zero_iff (openNormalQuotientHom N)
    (TopRep.quotientInvariantsIncl N.toSubgroup X) hsurj hincl n τ).mp
      (hτ ▸ hσ))

end ContinuousCohomology
