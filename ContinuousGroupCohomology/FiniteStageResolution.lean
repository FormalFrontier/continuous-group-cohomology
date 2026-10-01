/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ResolutionImage
public import ContinuousGroupCohomology.Topology.Algebra.CompactGroup.DiscreteFactor
public import ContinuousGroupCohomology.TopRepUlift

set_option warningAsError true

/-!
# Finite stages for discrete continuous resolutions

Every term in the native resolution of a discrete representation of a compact
group descends through an open normal quotient, provided the original action
is jointly continuous. At each successor, the finite range of the outer map
allows a single open normal subgroup to work for all its recursive values.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

/-- Every level of the actual native resolution is discrete when the group is
compact and the original coefficient representation is discrete. -/
theorem discreteTopology_resolutionX [CompactSpace G] [DiscreteTopology X]
    (i : ℕ) : DiscreteTopology (TopRep.resolutionX X i) := by
  induction i with
  | zero => infer_instance
  | succ i ih =>
    have : DiscreteTopology (TopRep.resolutionX X i) := ih
    exact ContinuousMap.discreteTopology_of_compactSpace

/-- A finite family of descending values has a common stage below a prescribed
open normal subgroup. The prescribed subgroup seeds the empty-family case. -/
theorem exists_common_stage_refinement (N₀ : OpenNormalSubgroup G) (i : ℕ)
    (S : Finset (TopRep.resolutionX X i))
    (hS : ∀ a ∈ S, ∃ N : OpenNormalSubgroup G, StageDescends X N i a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ a ∈ S, StageDescends X N i a := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨N₀, le_refl _, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨M, hM⟩ := hS a (by simp)
    obtain ⟨N, hN, hvalues⟩ := ih (by
      intro b hb
      exact hS b (by simp [hb]))
    refine ⟨N ⊓ M, le_trans inf_le_left hN, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hmem
    · exact stageDescends_antitone X inf_le_right i b hM
    · exact stageDescends_antitone X inf_le_left i b (hvalues b hmem)

/-- Every term in the native continuous resolution descends through one open
normal subgroup. Only the original representation's action needs to be jointly
continuous; no action-continuity assumption is imposed on coinduced levels. -/
theorem exists_openNormal_stage_descends [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X] (i : ℕ) (a : TopRep.resolutionX X i) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N i a := by
  induction i with
  | zero =>
    let W : Set G := {g | X.ρ g a = a}
    have horbit : Continuous (fun g : G => X.ρ g a) :=
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)
    have hclopen : IsClopen W :=
      ⟨(isClosed_discrete {a}).preimage horbit,
        (isOpen_discrete {a}).preimage horbit⟩
    have hone : (1 : G) ∈ W := by simp [W]
    obtain ⟨N, hN⟩ :=
      IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hclopen hone
    refine ⟨N, ?_⟩
    intro t
    exact hN t.2
  | succ i ih =>
    have : DiscreteTopology (TopRep.resolutionX X i) :=
      discreteTopology_resolutionX X i
    have hrange : (Set.range a).Finite :=
      (isCompact_range a.continuous).finite_of_discrete
    obtain ⟨N₀, fbar, hfbar⟩ := ContinuousMap.exists_openNormalSubgroup_factor a
    obtain ⟨N, hN, hvalues⟩ :=
      exists_common_stage_refinement X N₀ i hrange.toFinset (by
        intro b hb
        exact ih b)
    refine ⟨N, ?_⟩
    constructor
    · intro g
      exact hvalues (a g) (by simp [Set.Finite.mem_toFinset, Set.mem_range])
    · intro g t
      have ht : (t : G) ∈ N₀.toSubgroup := hN t.2
      have hquotient : openNormalQuotientHom N₀ (g * t.1) =
          openNormalQuotientHom N₀ g :=
        (QuotientGroup.mk'_eq_mk' N₀.toSubgroup).mpr
          ⟨t.1⁻¹, N₀.inv_mem ht, by group⟩
      calc
        a (g * t.1) = fbar (openNormalQuotientHom N₀ (g * t.1)) := (hfbar _).symm
        _ = fbar (openNormalQuotientHom N₀ g) := by rw [hquotient]
        _ = a g := hfbar _

/-- A native resolution term is the image of a term over a finite open-normal
quotient with quotient-invariant coefficients. -/
theorem exists_openNormal_resolution_lift [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X] (i : ℕ) (a : TopRep.resolutionX X i) :
    ∃ (N : OpenNormalSubgroup G)
      (b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) i),
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom b = a := by
  obtain ⟨N, hN⟩ := exists_openNormal_stage_descends X i a
  obtain ⟨b, hb⟩ := (stageDescends_iff_exists_lift X N i a).mp hN
  exact ⟨N, b, hb⟩

end ContinuousCohomology
