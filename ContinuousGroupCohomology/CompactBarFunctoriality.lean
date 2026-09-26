/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactNegativeTate
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Continuous functoriality of compact finite bar homology

This file makes the usual map of finite inhomogeneous bar complexes continuous
when the coefficient map is continuous. It then descends that chain map to the
compact Hausdorff homology constructed in `CompactNegativeTate`.
-/

public section

set_option autoImplicit false

open CategoryTheory Topology

namespace CompHausAddCommGrp.FiniteBar

noncomputable section

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

/-- The continuous map on finite inhomogeneous bar chains induced by a group
homomorphism and a continuous coefficient morphism. -/
noncomputable def chainsMap (n : ℕ) : chains B n ⟶ chains C n :=
  finiteFinsuppMap (of B) (of C) (Fin n → H) (Fin n → K)
    ((groupHomology.chainsMap f φ).f n).hom.toAddMonoidHom (by
      intro i j
      by_cases hij : f ∘ i = j
      · change Continuous (fun x : B ↦
          ((groupHomology.chainsMap f φ).f n (Finsupp.single i x)) j)
        have heq : (fun x : B ↦
            ((groupHomology.chainsMap f φ).f n (Finsupp.single i x)) j) =
            fun x : B ↦ φ.hom x := by
          funext x
          rw [groupHomology.chainsMap_f_single]
          simp [hij]
        rw [heq]
        exact hφ
      · change Continuous (fun x : B ↦
          ((groupHomology.chainsMap f φ).f n (Finsupp.single i x)) j)
        have heq : (fun x : B ↦
            ((groupHomology.chainsMap f φ).f n (Finsupp.single i x)) j) =
            fun _ : B ↦ (0 : C) := by
          funext x
          rw [groupHomology.chainsMap_f_single]
          simp [hij]
        rw [heq]
        exact continuous_const)

@[simp]
lemma chainsMap_apply (n : ℕ) (x : chains B n) :
    chainsMap B C f φ hφ n x = (groupHomology.chainsMap f φ).f n x :=
  by rfl

@[simp]
lemma chainsMap_single (n : ℕ) (i : Fin n → H) (x : B) :
    chainsMap B C f φ hφ n (Finsupp.single i x) =
      Finsupp.single (f ∘ i) (φ.hom x) := by
  change (groupHomology.chainsMap f φ).f n (Finsupp.single i x) = _
  exact groupHomology.chainsMap_f_single f φ n i x

/-- The continuous maps induced on finite bar chains commute with the bar
differentials. -/
lemma chainsMap_differential (n : ℕ) :
    chainsMap B C f φ hφ (n + 1) ≫ differential C hC n =
      differential B hB n ≫ chainsMap B C f φ hφ n := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  simp only [comp_apply]
  rw [differential_apply, chainsMap_apply, chainsMap_apply,
    differential_apply]
  change groupHomology.inhomogeneousChains.d C n
      ((groupHomology.chainsMap f φ).f (n + 1) x) =
    (groupHomology.chainsMap f φ).f n
      (groupHomology.inhomogeneousChains.d B n x)
  have h := ModuleCat.hom_ext_iff.1
    ((groupHomology.chainsMap f φ).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  have hx := LinearMap.congr_fun h (show (Fin (n + 1) → H) →₀ B from x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
  simpa [groupHomology.inhomogeneousChains.d_def] using hx

private lemma differential_differential (n : ℕ) (x : chains B (n + 2)) :
    differential B hB n (differential B hB (n + 1) x) = 0 := by
  rw [differential_apply, differential_apply]
  change groupHomology.inhomogeneousChains.d B n
      (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
  exact congrArg (fun g ↦ g x)
    (ModuleCat.hom_ext_iff.1
      (groupHomology.inhomogeneousChains.d_comp_d B n))

omit [Fintype H] [Fintype K] [TopologicalSpace B] [CompactSpace B] [T2Space B]
    [IsTopologicalAddGroup B] [TopologicalSpace C] [CompactSpace C] [T2Space C]
    [IsTopologicalAddGroup C] in
private lemma chainsMap_differential_raw_apply (n : ℕ)
    (x : (Fin (n + 1) → H) →₀ B) :
    groupHomology.inhomogeneousChains.d C n
        ((groupHomology.chainsMap f φ).f (n + 1) x) =
      (groupHomology.chainsMap f φ).f n
        (groupHomology.inhomogeneousChains.d B n x) := by
  have h := ModuleCat.hom_ext_iff.1
    ((groupHomology.chainsMap f φ).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
  have hx := LinearMap.congr_fun h x
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hx
  simpa [groupHomology.inhomogeneousChains.d_def] using hx

/-- The continuous map on compact positive-degree finite-group homology induced
by a group homomorphism and a continuous coefficient morphism. -/
noncomputable def positiveHomologyMap (n : ℕ) :
    positiveHomology B hB n ⟶ positiveHomology C hC n := by
  unfold positiveHomology
  refine CompHausAddCommGrp.homologyMap
    (d₂ := differential B hB (n + 1)) (d₁ := differential B hB n)
    (e₂ := differential C hC (n + 1)) (e₁ := differential C hC n)
    (hd := differential_differential B hB n)
    (he := differential_differential C hC n)
    (p₂ := chainsMap B C f φ hφ (n + 2))
    (p₁ := chainsMap B C f φ hφ (n + 1))
    (p₀ := chainsMap B C f φ hφ n) ?_ ?_
  · intro x
    rw [differential_apply, chainsMap_apply, chainsMap_apply,
      differential_apply]
    change groupHomology.inhomogeneousChains.d C n
        ((groupHomology.chainsMap f φ).f (n + 1) x) =
      (groupHomology.chainsMap f φ).f n
        (groupHomology.inhomogeneousChains.d B n x)
    exact chainsMap_differential_raw_apply B C f φ n x
  · intro x
    rw [differential_apply, chainsMap_apply, chainsMap_apply,
      differential_apply]
    change groupHomology.inhomogeneousChains.d C (n + 1)
        ((groupHomology.chainsMap f φ).f (n + 2) x) =
      (groupHomology.chainsMap f φ).f (n + 1)
        (groupHomology.inhomogeneousChains.d B (n + 1) x)
    exact chainsMap_differential_raw_apply B C f φ (n + 1) x

/-- The algebraic-to-compact finite-bar homology comparison is natural in the
group homomorphism and continuous coefficient morphism. -/
lemma groupHomologyAddEquivPositive_naturality (n : ℕ)
    (y : groupHomology B (n + 1)) :
    groupHomologyAddEquivPositive C hC n
        (groupHomology.map f φ (n + 1) y) =
      positiveHomologyMap B C hB hC f φ hφ n
        (groupHomologyAddEquivPositive B hB n y) := by
  let KB := groupHomology.inhomogeneousChains B
  let KC := groupHomology.inhomogeneousChains C
  let SB := KB.sc' (n + 2) (n + 1) n
  let SC := KC.sc' (n + 2) (n + 1) n
  obtain ⟨z, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (KB.homologyπ (n + 1))).mp inferInstance y
  let xB : SB.moduleCatLeftHomologyData.K :=
    SB.moduleCatCyclesIso.hom
      ((KB.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)
  let zC : KC.cycles (n + 1) := groupHomology.cyclesMap f φ (n + 1) z
  let xC : SC.moduleCatLeftHomologyData.K :=
    SC.moduleCatCyclesIso.hom
      ((KC.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom zC)
  let xcB : kernelGroup (differential B hB n) := ⟨xB.1, by
    change differential B hB n xB.1 = 0
    have hx := xB.2
    change (groupHomology.inhomogeneousChains B).d (n + 1) n xB.1 = 0 at hx
    rw [groupHomology.inhomogeneousChains.d_def] at hx
    exact (differential_apply B hB n xB.1).trans hx⟩
  let xcC : kernelGroup (differential C hC n) := ⟨xC.1, by
    change differential C hC n xC.1 = 0
    have hx := xC.2
    change (groupHomology.inhomogeneousChains C).d (n + 1) n xC.1 = 0 at hx
    rw [groupHomology.inhomogeneousChains.d_def] at hx
    exact (differential_apply C hC n xC.1).trans hx⟩
  have hxB : xB.1 = KB.iCycles (n + 1) z := by
    have h₁ := ModuleCat.hom_ext_iff.1 SB.moduleCatCyclesIso_hom_i
    rw [ModuleCat.hom_comp] at h₁
    have h₁z := LinearMap.congr_fun h₁
      ((KB.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)
    rw [LinearMap.comp_apply] at h₁z
    have h₂ := ModuleCat.hom_ext_iff.1
      (KB.cyclesIsoSc'_hom_iCycles (n + 2) (n + 1) n (by simp) (by simp))
    rw [ModuleCat.hom_comp] at h₂
    have h₂z := LinearMap.congr_fun h₂ z
    rw [LinearMap.comp_apply] at h₂z
    change SB.moduleCatLeftHomologyData.i.hom
        (SB.moduleCatCyclesIso.hom.hom
          ((KB.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)) =
      (KB.iCycles (n + 1)).hom z
    exact h₁z.trans h₂z
  have hxC : xC.1 = KC.iCycles (n + 1) zC := by
    have h₁ := ModuleCat.hom_ext_iff.1 SC.moduleCatCyclesIso_hom_i
    rw [ModuleCat.hom_comp] at h₁
    have h₁z := LinearMap.congr_fun h₁
      ((KC.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom zC)
    rw [LinearMap.comp_apply] at h₁z
    have h₂ := ModuleCat.hom_ext_iff.1
      (KC.cyclesIsoSc'_hom_iCycles (n + 2) (n + 1) n (by simp) (by simp))
    rw [ModuleCat.hom_comp] at h₂
    have h₂z := LinearMap.congr_fun h₂ zC
    rw [LinearMap.comp_apply] at h₂z
    change SC.moduleCatLeftHomologyData.i.hom
        (SC.moduleCatCyclesIso.hom.hom
          ((KC.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom zC)) =
      (KC.iCycles (n + 1)).hom zC
    exact h₁z.trans h₂z
  have hxmap :
      KC.iCycles (n + 1) zC =
        (groupHomology.chainsMap f φ).f (n + 1) (KB.iCycles (n + 1) z) := by
    have h := ModuleCat.hom_ext_iff.1
      (HomologicalComplex.cyclesMap_i (groupHomology.chainsMap f φ) (n + 1))
    have hz := LinearMap.congr_fun h z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, zC,
      groupHomology.cyclesMap] using hz
  let hcomm : ∀ x,
      differential C hC n (chainsMap B C f φ hφ (n + 1) x) =
        chainsMap B C f φ hφ n (differential B hB n x) := fun x ↦ by
            rw [differential_apply, chainsMap_apply, chainsMap_apply,
              differential_apply]
            change (groupHomology.inhomogeneousChains.d C n).hom
                (((groupHomology.chainsMap f φ).f (n + 1)).hom x) =
              ((groupHomology.chainsMap f φ).f n).hom
                ((groupHomology.inhomogeneousChains.d B n).hom x)
            have h := ModuleCat.hom_ext_iff.1
              ((groupHomology.chainsMap f φ).comm (n + 1) n)
            rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
            rw [groupHomology.inhomogeneousChains.d_def,
              groupHomology.inhomogeneousChains.d_def] at h
            exact calc
              (groupHomology.inhomogeneousChains.d C n).hom
                    (((groupHomology.chainsMap f φ).f (n + 1)).hom x) =
                  ((groupHomology.inhomogeneousChains.d C n).hom.comp
                    ((groupHomology.chainsMap f φ).f (n + 1)).hom) x := rfl
              _ = (((groupHomology.chainsMap f φ).f n).hom.comp
                    (groupHomology.inhomogeneousChains.d B n).hom) x :=
                  LinearMap.congr_fun h x
              _ = ((groupHomology.chainsMap f φ).f n).hom
                    ((groupHomology.inhomogeneousChains.d B n).hom x) := rfl
  let q := kernelMap (chainsMap B C f φ hφ (n + 1))
    (chainsMap B C f φ hφ n)
    (differential B hB n) (differential C hC n) hcomm
  have hxc : q xcB = xcC := by
    apply Subtype.ext
    change (groupHomology.chainsMap f φ).f (n + 1) xB.1 = xC.1
    rw [hxB, hxC, hxmap]
  have hmap :
      groupHomology.map f φ (n + 1) (KB.homologyπ (n + 1) z) =
        KC.homologyπ (n + 1) zC := by
    have h := ModuleCat.hom_ext_iff.1 (groupHomology.π_map f φ (n + 1))
    have hz := LinearMap.congr_fun h z
    change (groupHomology.map f φ (n + 1)).hom
        ((groupHomology.π B (n + 1)).hom z) =
      (groupHomology.π C (n + 1)).hom
        ((groupHomology.cyclesMap f φ (n + 1)).hom z)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, zC] using hz
  rw [hmap]
  rw [show groupHomologyAddEquivPositive B hB n
        (KB.homologyπ (n + 1) z) = QuotientAddGroup.mk xcB by
    simpa [xcB, KB, hxB] using
      groupHomologyAddEquivPositive_homologyπ B hB n z]
  rw [show groupHomologyAddEquivPositive C hC n
        (KC.homologyπ (n + 1) zC) = QuotientAddGroup.mk xcC by
    simpa [xcC, KC, hxC] using
      groupHomologyAddEquivPositive_homologyπ C hC n zC]
  unfold positiveHomologyMap
  change QuotientAddGroup.mk xcC = QuotientAddGroup.mk (q xcB)
  exact congrArg QuotientAddGroup.mk hxc.symm

end

end CompHausAddCommGrp.FiniteBar
