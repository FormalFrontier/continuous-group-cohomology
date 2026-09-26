/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteDeflationTransitivity
import Mathlib.Data.ZMod.Basic

/-!
# Native finite-deflation transitivity client

The direct coefficient formula and the composition and identity laws below
use only the public native module. For three levels the quotient-image
finiteness hypotheses are all present; the self-map cases require the
corresponding self-image hypothesis. The final specialization uses a proper
intermediate subgroup of a four-element finite group, with a representation
left arbitrary.

These finite-stage laws do not construct inverse limits, prove topological
exactness, or compute Tate groups.
-/

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

universe u

section Composition

variable {R G : Type u} [CommRing R] [Group G]
variable (A : Rep.{u} R G) (S T U : Subgroup G)
variable [S.Normal] [T.Normal] [U.Normal] (hST : S ≤ T) (hTU : T ≤ U)
variable [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (G ⧸ U)]
variable [Fintype (T.map (QuotientGroup.mk' S))]
variable [Fintype (U.map (QuotientGroup.mk' T))]
variable [Fintype (U.map (QuotientGroup.mk' S))]

example (x : A.quotientToInvariants S) :
    ((finiteNegativeDeflationCoeffDirect A S T hST).hom x).1 =
      ∑ q : T.map (QuotientGroup.mk' S),
        (((A.quotientToInvariants S).ρ q.1) x).1 :=
  finiteNegativeDeflationCoeffDirect_apply_val A S T hST x

example (n : ℕ) :
    finiteNegativeDeflation A S T hST n =
      groupHomology.map (finiteDeflationGroupHom S T hST)
        (finiteNegativeDeflationCoeffDirect A S T hST) n :=
  finiteNegativeDeflation_eq_direct_map A S T hST n

example (n : ℕ) :
    finiteNegativeDeflation A S T hST n ≫
        finiteNegativeDeflation A T U hTU n =
      finiteNegativeDeflation A S U (hST.trans hTU) n :=
  finiteNegativeDeflation_comp A S T U hST hTU n

example :
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
        (finiteLevelTotalInvariantsEquiv A T U hTU).toModuleIso.hom =
      (finiteLevelTotalInvariantsEquiv A S U (hST.trans hTU)).toModuleIso.hom :=
  finiteLevelTotalInvariantsEquiv_trans A S T U hST hTU

example :
    finiteNegativeDeflationCoinvariants A S T hST ≫
        finiteNegativeDeflationCoinvariants A T U hTU =
      finiteNegativeDeflationCoinvariants A S U (hST.trans hTU) :=
  finiteNegativeDeflationCoinvariants_comp A S T U hST hTU

example :
    finiteNegativeOneDeflationKernel A S T hST ≫
        finiteNegativeOneDeflationKernel A T U hTU =
      finiteNegativeOneDeflationKernel A S U (hST.trans hTU) :=
  finiteNegativeOneDeflationKernel_comp A S T U hST hTU

example :
    finiteZeroDeflationCokernel A S T hST ≫
        finiteZeroDeflationCokernel A T U hTU =
      finiteZeroDeflationCokernel A S U (hST.trans hTU) :=
  finiteZeroDeflationCokernel_comp A S T U hST hTU

example :
    finiteNegativeOneDeflation A S T hST ≫
        finiteNegativeOneDeflation A T U hTU =
      finiteNegativeOneDeflation A S U (hST.trans hTU) :=
  finiteNegativeOneDeflation_comp A S T U hST hTU

example :
    finiteZeroDeflation A S T hST ≫ finiteZeroDeflation A T U hTU =
      finiteZeroDeflation A S U (hST.trans hTU) :=
  finiteZeroDeflation_comp A S T U hST hTU

end Composition

section Identity

variable {R G : Type u} [CommRing R] [Group G]
variable (A : Rep.{u} R G) (S : Subgroup G) [S.Normal]
variable [Fintype (G ⧸ S)] [Fintype (S.map (QuotientGroup.mk' S))]

example (n : ℕ) : finiteNegativeDeflation A S S le_rfl n = 𝟙 _ :=
  finiteNegativeDeflation_refl A S n

example : (finiteLevelTotalInvariantsEquiv A S S le_rfl).toModuleIso.hom = 𝟙 _ :=
  finiteLevelTotalInvariantsEquiv_refl A S

example : finiteNegativeDeflationCoinvariants A S S le_rfl = 𝟙 _ :=
  finiteNegativeDeflationCoinvariants_refl A S

example : finiteNegativeOneDeflationKernel A S S le_rfl = 𝟙 _ :=
  finiteNegativeOneDeflationKernel_refl A S

example : finiteZeroDeflationCokernel A S S le_rfl = 𝟙 _ :=
  finiteZeroDeflationCokernel_refl A S

example : finiteNegativeOneDeflation A S S le_rfl = 𝟙 _ :=
  finiteNegativeOneDeflation_refl A S

example : finiteZeroDeflation A S S le_rfl = 𝟙 _ :=
  finiteZeroDeflation_refl A S

end Identity

section FourElementGroup

local notation "G₄" => Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

local notation "T₄" =>
  Subgroup.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))
    (⊥ : Subgroup (Multiplicative (ZMod 2)))

private theorem middleSubgroup_ne_bot : (T₄ : Subgroup G₄) ≠ ⊥ := by
  intro h
  have hmemT : ((Multiplicative.ofAdd (1 : ZMod 2), 1) : G₄) ∈ T₄ :=
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
  have hmem : ((Multiplicative.ofAdd (1 : ZMod 2), 1) : G₄) ∈
      (⊥ : Subgroup G₄) := h ▸ hmemT
  have heq : (1 : ZMod 2) = 0 := by
    have hp := congrArg (fun p : G₄ ↦ Multiplicative.toAdd p.1)
      (Subgroup.mem_bot.mp hmem)
    exact hp
  exact (by decide : (1 : ZMod 2) ≠ 0) heq

private theorem middleSubgroup_ne_top : (T₄ : Subgroup G₄) ≠ ⊤ := by
  intro h
  have hmem : ((1, Multiplicative.ofAdd (1 : ZMod 2)) : G₄) ∈ T₄ := by
    rw [h]
    exact Subgroup.mem_top _
  have hp := (Subgroup.mem_prod.mp hmem).2
  have heq : (1 : ZMod 2) = 0 := by
    simpa using congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp hp)
  exact (by decide : (1 : ZMod 2) ≠ 0) heq

noncomputable local instance : Fintype (G₄ ⧸ (⊥ : Subgroup G₄)) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (G₄ ⧸ T₄) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (G₄ ⧸ (⊤ : Subgroup G₄)) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype ((T₄).map (QuotientGroup.mk' ⊥)) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype ((⊤ : Subgroup G₄).map
    (QuotientGroup.mk' T₄)) := Fintype.ofFinite _

noncomputable local instance : Fintype ((⊤ : Subgroup G₄).map
    (QuotientGroup.mk' ⊥)) := Fintype.ofFinite _

example (A : Rep ℤ G₄) (n : ℕ) :
    finiteNegativeDeflation A ⊥ T₄ bot_le n ≫
        finiteNegativeDeflation A T₄ ⊤ le_top n =
      finiteNegativeDeflation A ⊥ ⊤ (bot_le : (⊥ : Subgroup G₄) ≤ ⊤) n := by
  exact finiteNegativeDeflation_comp A ⊥ T₄ ⊤ bot_le le_top n

end FourElementGroup
