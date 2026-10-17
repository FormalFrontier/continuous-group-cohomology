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

Every invariant term in the resolution of a discrete representation of a compact
group descends through an open normal quotient, without joint continuity of the
action. For arbitrary resolution terms, joint continuity of the original action
ensures the required fixedness at level zero. At each successor, the finite range
of the outer map allows a single subgroup to work for all its recursive values.
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

omit [IsTopologicalGroup G] in
private theorem exists_common_refinement {A : Type*}
    (P : OpenNormalSubgroup G → A → Prop)
    (hmono : ∀ {N M : OpenNormalSubgroup G}, N ≤ M → ∀ a, P M a → P N a)
    (N₀ : OpenNormalSubgroup G) (S : Finset A)
    (hS : ∀ a ∈ S, ∃ N : OpenNormalSubgroup G, P N a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧ ∀ a ∈ S, P N a := by
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
    · exact hmono inf_le_right b hM
    · exact hmono inf_le_left b (hvalues b hmem)

/-- A finite family of descending values has a common stage below a prescribed
open normal subgroup. The prescribed subgroup seeds the empty-family case. -/
theorem exists_common_stage_refinement (N₀ : OpenNormalSubgroup G) (i : ℕ)
    (S : Finset (TopRep.resolutionX X i))
    (hS : ∀ a ∈ S, ∃ N : OpenNormalSubgroup G, StageDescends X N i a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ a ∈ S, StageDescends X N i a :=
  exists_common_refinement (fun N a => StageDescends X N i a)
    (fun h a ha => stageDescends_antitone X h i a ha) N₀ S hS

-- Share the finite-range selection between recursive right-coset constancy and
-- descent, whose level-zero conditions are different.
private theorem exists_successor_refinement [CompactSpace G] [DiscreteTopology X]
    (i : ℕ) (P : OpenNormalSubgroup G → TopRep.resolutionX X i → Prop)
    (hmono : ∀ {N M : OpenNormalSubgroup G}, N ≤ M → ∀ a, P M a → P N a)
    (M : OpenNormalSubgroup G) (a : TopRep.resolutionX X (i + 1))
    (hvalues : ∀ b, ∃ N : OpenNormalSubgroup G, P N b) :
    ∃ N : OpenNormalSubgroup G, N ≤ M ∧
      (∀ g : G, P N (a g)) ∧
        (∀ (g : G) (t : N.toSubgroup), a (g * t.1) = a g) := by
  have : DiscreteTopology (TopRep.resolutionX X i) :=
    discreteTopology_resolutionX X i
  have hrange : (Set.range a).Finite :=
    (isCompact_range a.continuous).finite_of_discrete
  obtain ⟨N₀, fbar, hfbar⟩ := ContinuousMap.exists_openNormalSubgroup_factor a
  obtain ⟨N, hN, hinner⟩ :=
    exists_common_refinement P hmono (M ⊓ N₀) hrange.toFinset (by
      intro b hb
      exact hvalues b)
  refine ⟨N, le_trans hN inf_le_left, ?_, ?_⟩
  · intro g
    exact hinner (a g) (by simp [Set.Finite.mem_toFinset, Set.mem_range])
  · intro g t
    have ht : (t : G) ∈ N₀.toSubgroup := (le_trans hN inf_le_right) t.2
    have hquotient : openNormalQuotientHom N₀ (g * t.1) =
        openNormalQuotientHom N₀ g :=
      (QuotientGroup.mk'_eq_mk' N₀.toSubgroup).mpr
        ⟨t.1⁻¹, N₀.inv_mem ht, by group⟩
    calc
      a (g * t.1) = fbar (openNormalQuotientHom N₀ (g * t.1)) := (hfbar _).symm
      _ = fbar (openNormalQuotientHom N₀ g) := by rw [hquotient]
      _ = a g := hfbar _

private def RightCosetConstant (N : OpenNormalSubgroup G) :
    (i : ℕ) → TopRep.resolutionX X i → Prop
  | 0, _ => True
  | i + 1, a =>
      (∀ g : G, RightCosetConstant N i (a g)) ∧
        (∀ (g : G) (t : N.toSubgroup), a (g * t.1) = a g)

private theorem rightCosetConstant_antitone {N M : OpenNormalSubgroup G} (h : N ≤ M)
    (i : ℕ) (a : TopRep.resolutionX X i) :
    RightCosetConstant X M i a → RightCosetConstant X N i a := by
  induction i with
  | zero => intro _; trivial
  | succ i ih =>
    rintro ⟨hvalues, hcoset⟩
    exact ⟨fun g => ih (a g) (hvalues g), fun g t => hcoset g ⟨t.1, h t.2⟩⟩

private theorem exists_rightCosetConstant_below [CompactSpace G] [DiscreteTopology X]
    (M : OpenNormalSubgroup G) (i : ℕ) (a : TopRep.resolutionX X i) :
    ∃ N : OpenNormalSubgroup G, N ≤ M ∧ RightCosetConstant X N i a := by
  induction i with
  | zero => exact ⟨M, le_refl _, trivial⟩
  | succ i ih =>
    apply exists_successor_refinement X i (fun N b => RightCosetConstant X N i b)
      (fun h b hb => rightCosetConstant_antitone X h i b hb) M a
    intro b
    obtain ⟨N, _, hN⟩ := ih b
    exact ⟨N, hN⟩

-- Right-coset constancy turns invariance of a function into invariance of each
-- value under the same normal subgroup, not under the whole group.
private theorem stageDescends_of_rightCosetConstant (N : OpenNormalSubgroup G)
    (i : ℕ) (a : TopRep.resolutionX X i) :
    RightCosetConstant X N i a →
      a ∈ ((TopRep.resolutionX X i).ρ.restrict N.toSubgroup.subtype).invariants →
        StageDescends X N i a := by
  induction i with
  | zero => intro _ hfixed; exact hfixed
  | succ i ih =>
    intro hcoset hfixed
    refine ⟨?_, hcoset.2⟩
    intro g
    apply ih (a g) (hcoset.1 g)
    intro t
    have ht : g⁻¹ * t.1⁻¹ * g ∈ N.toSubgroup := by
      simpa only [inv_inv] using
        (inferInstance : N.toSubgroup.Normal).conj_mem t.1⁻¹ (N.inv_mem t.2) g⁻¹
    have hright : a (t.1⁻¹ * g) = a g := by
      have h := hcoset.2 g ⟨g⁻¹ * t.1⁻¹ * g, ht⟩
      have hmul : g * (g⁻¹ * t.1⁻¹ * g) = t.1⁻¹ * g := by group
      rw [hmul] at h
      exact h
    have haction := congrArg (fun F : TopRep.resolutionX X (i + 1) => F g) (hfixed t)
    change (TopRep.resolutionX X i).ρ t.1 (a (t.1⁻¹ * g)) = a g at haction
    rw [hright] at haction
    exact haction

/-- An invariant resolution term with discrete coefficients over a compact group
descends through an open normal quotient. No joint continuity of the action is
needed: invariance supplies fixedness after recursive right-coset constancy. -/
theorem exists_openNormal_stage_descends_of_invariant [CompactSpace G] [DiscreteTopology X]
    (i : ℕ) (a : TopRep.resolutionX X i)
    (ha : a ∈ (TopRep.resolutionX X i).ρ.invariants) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N i a := by
  obtain ⟨N, _, hN⟩ := exists_rightCosetConstant_below X
    (⟨(⊤ : OpenSubgroup G),
      by change (⊤ : Subgroup G).Normal; infer_instance⟩ : OpenNormalSubgroup G) i a
  exact ⟨N, stageDescends_of_rightCosetConstant X N i a hN (fun t => ha t.1)⟩

/-- Every term in the continuous resolution descends through one open
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
    obtain ⟨N, _, hN⟩ := exists_successor_refinement X i
      (fun N b => StageDescends X N i b)
      (fun h b hb => stageDescends_antitone X h i b hb)
      (⟨(⊤ : OpenSubgroup G),
        by change (⊤ : Subgroup G).Normal; infer_instance⟩ : OpenNormalSubgroup G) a ih
    exact ⟨N, hN⟩

/-- A resolution term is the image of a term over a finite open-normal
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
