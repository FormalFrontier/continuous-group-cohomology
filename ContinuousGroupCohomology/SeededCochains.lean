/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageCochains

set_option warningAsError true

/-!
# Seeded finite-stage lifts of homogeneous cochains

A homogeneous cochain over a compact group with discrete, jointly continuous
coefficients descends to a quotient by an open normal subgroup contained in any
prescribed open normal subgroup. The subgroup may depend on the cochain and its degree.

The reflection of invariance through the resolution map adapts
`ContinuousGroupCohomology/FiniteStageCochains.lean` at the official
`continuous-group-cohomology` revision `820aae2fb4e8c486200cbc9d5dfeb964b6de6848`;
its original contributors retain credit.
-/

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

/-- A native homogeneous cochain lifts from an open-normal quotient refining the
prescribed subgroup, with the genuine quotient-invariant coefficients. -/
theorem exists_quotient_cochain_lift_below [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X] (M : OpenNormalSubgroup G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (N : OpenNormalSubgroup G), N ≤ M ∧
      ∃ (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X n),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n) τ = σ := by
  obtain ⟨P, hP⟩ := exists_openNormal_stage_descends X (n + 1) σ.1
  let N := M ⊓ P
  have hN : N ≤ M := inf_le_left
  have hdesc : StageDescends X N (n + 1) σ.1 :=
    stageDescends_antitone X inf_le_right (n + 1) σ.1 hP
  obtain ⟨b, hb⟩ := (stageDescends_iff_exists_lift X N (n + 1) σ.1).mp hdesc
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
  exact ⟨N, hN, ⟨b, hbinv⟩, Subtype.ext hb⟩

end ContinuousCohomology
