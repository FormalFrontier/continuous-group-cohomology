/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactBarFunctoriality
public import Mathlib.Topology.Instances.ZMod

/-!
# Compact finite bar homology and negative Tate: direct native client

Finite compact bar chains, their differential, the cycle-class comparison and
the negative Tate stage are tested independently of the source research project.
The common-universe finite Tate comparison starts at degree `-2` and homology
degree `1`, not at degree `-1`. Maps require an equivariant coefficient morphism
with its own continuity witness. The concrete test has a two-element acting
group and nonzero three-element coefficients with their discrete topology.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CompHausAddCommGrp CompHausAddCommGrp.FiniteBar
open ContinuousGroupCohomology

namespace CompactNegativeBarNative

universe u

variable {R H K : Type u} [CommRing R]
variable [Group H] [Fintype H] [Group K] [Fintype K]
variable (B : Rep.{u} R H) (C : Rep.{u} R K)
variable [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable [IsTopologicalAddGroup B]
variable [TopologicalSpace C] [CompactSpace C] [T2Space C]
variable [IsTopologicalAddGroup C]
variable (hB : ∀ h, Continuous (B.ρ h))
variable (hC : ∀ k, Continuous (C.ρ k))
variable (f : H →* K) (φ : B ⟶ Rep.res f C)
variable (hφ : Continuous φ.hom)

theorem differential_on_chains (n : ℕ) (x : chains B (n + 1)) :
    differential B hB n x = groupHomology.inhomogeneousChains.d B n x := by
  rw [differential_apply]

theorem cycle_class_comparison (n : ℕ)
    (z : (groupHomology.inhomogeneousChains B).cycles (n + 1)) :
    ∃ x : kernelGroup (differential B hB n),
      groupHomologyAddEquivPositive B hB n
          ((groupHomology.inhomogeneousChains B).homologyπ (n + 1) z) =
        QuotientAddGroup.mk x := by
  exact ⟨_, groupHomologyAddEquivPositive_homologyπ B hB n z⟩

theorem map_on_chains (n : ℕ) (x : chains B n) :
    chainsMap B C f φ hφ n x = (groupHomology.chainsMap f φ).f n x := by
  rw [chainsMap_apply]

theorem map_on_single (n : ℕ) (i : Fin n → H) (x : B) :
    chainsMap B C f φ hφ n (Finsupp.single i x) =
      Finsupp.single (f ∘ i) (φ.hom x) := by
  rw [chainsMap_single]

theorem map_commutes_with_differential (n : ℕ) :
    chainsMap B C f φ hφ (n + 1) ≫ differential C hC n =
      differential B hB n ≫ chainsMap B C f φ hφ n :=
  chainsMap_differential B C hB hC f φ hφ n

theorem comparison_natural (n : ℕ) (y : groupHomology B (n + 1)) :
    groupHomologyAddEquivPositive C hC n
        (groupHomology.map f φ (n + 1) y) =
      positiveHomologyMap B C hB hC f φ hφ n
        (groupHomologyAddEquivPositive B hB n y) :=
  groupHomologyAddEquivPositive_naturality B C hB hC f φ hφ n y

section FiniteTateStage

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

noncomputable def degree_negative_two (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)] :
    tateCohomology (A.quotientToInvariants S.toSubgroup) (-2 : ℤ) ≃+
      LevelCompact.finiteTateNegative A L S 0 := by
  simpa using
    LevelCompact.tateCohomologyNegativeAddEquivFiniteTate A L S 0

end FiniteTateStage

local notation "G₂" => Multiplicative (ZMod 2)

noncomputable abbrev finiteCoefficients : Rep.{0} ℤ G₂ :=
  Rep.trivial ℤ G₂ (ZMod 3)

theorem group_is_nontrivial : (⊥ : Subgroup G₂) < ⊤ := bot_lt_top

theorem coefficient_is_nonzero : (0 : ZMod 3) ≠ 1 := by decide

theorem finite_action_continuous (g : G₂) :
    Continuous (finiteCoefficients.ρ g) :=
  continuous_of_discreteTopology

theorem finite_differential_on_single (i : Fin 1 → G₂) (x : ZMod 3) :
    differential finiteCoefficients finite_action_continuous 0
        (Finsupp.single i x) =
      groupHomology.inhomogeneousChains.d finiteCoefficients 0
        (Finsupp.single i x) :=
  differential_on_chains finiteCoefficients finite_action_continuous 0 _

theorem finite_identity_map_on_single (i : Fin 1 → G₂) (x : ZMod 3) :
    chainsMap finiteCoefficients finiteCoefficients (MonoidHom.id G₂)
        (𝟙 finiteCoefficients) (by exact continuous_of_discreteTopology) 1
        (Finsupp.single i x) = Finsupp.single i x := by
  simpa using map_on_single finiteCoefficients finiteCoefficients
    (MonoidHom.id G₂) (𝟙 finiteCoefficients)
    (by exact continuous_of_discreteTopology) 1 i x

#print axioms differential_on_chains
#print axioms cycle_class_comparison
#print axioms map_on_chains
#print axioms map_on_single
#print axioms map_commutes_with_differential
#print axioms comparison_natural
#print axioms degree_negative_two
#print axioms group_is_nontrivial
#print axioms coefficient_is_nonzero
#print axioms finite_action_continuous
#print axioms finite_differential_on_single
#print axioms finite_identity_map_on_single

end CompactNegativeBarNative
