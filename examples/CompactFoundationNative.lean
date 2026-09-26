/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Foundation mathematics and APIs: Beacon (six existing mathematical leaves)
Native client examples: worker-b Hive Task hive-request-3dd6d1127d8e9fa2263572b3d9b88fba1e4dab16
  (UID c022d295-e4c3-4eb1-8d62-fb9c9577d85d)
-/
module

import ContinuousGroupCohomology.CompactAddCommGroupLimits
import ContinuousGroupCohomology.CompactFiniteHomology
import ContinuousGroupCohomology.CompactTopModuleLimits
import Mathlib.Topology.Instances.ZMod

/-!
# Native compact-group foundation client

This file uses only native leaves. It tests compact Hausdorff additive-group
coercions and morphisms, closed-kernel and quotient representatives, finite
products, limit projections, cofiltered exactness including an empty category,
and explicit compact Hausdorff conclusions for topological-module limits.
-/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CompactFoundationNative

variable {A B C : CompHausAddCommGrp.{u}}

example (f : A ⟶ B) (g : B ⟶ C) (x : A) : (f ≫ g) x = g (f x) := by
  rfl

example (f : A ⟶ B) (x : CompHausAddCommGrp.kernelGroup f) :
    f (CompHausAddCommGrp.kernelι f x) = 0 := by
  simpa only using CompHausAddCommGrp.comp_kernelι_apply f x

example (f : A ⟶ B) (x : A) :
    CompHausAddCommGrp.quotientRangeπ f (f x) = 0 := by
  simpa only using CompHausAddCommGrp.quotientRangeπ_comp_apply f x

example (d₂ : A ⟶ B) (d₁ : B ⟶ C)
    (hd : ∀ x, d₁ (d₂ x) = 0) (x : A) :
    CompHausAddCommGrp.kernelι d₁
        (CompHausAddCommGrp.boundaryToKernel d₂ d₁ hd x) = d₂ x := by
  rfl

example (d₂ : A ⟶ B) (d₁ : B ⟶ C)
    (hd : ∀ x, d₁ (d₂ x) = 0) (x : A) :
    CompHausAddCommGrp.quotientRangeπ
        (CompHausAddCommGrp.boundaryToKernel d₂ d₁ hd)
        (CompHausAddCommGrp.boundaryToKernel d₂ d₁ hd x) = 0 := by
  simpa only using CompHausAddCommGrp.quotientRangeπ_comp_apply
    (CompHausAddCommGrp.boundaryToKernel d₂ d₁ hd) x

example (f : A ⟶ B) (y : B) :
    CompHausAddCommGrp.quotientRangeπ f y = QuotientAddGroup.mk y := by
  rfl

example (f : A ⟶ B) (g : A ⟶ B) (p : A ⟶ A) (q : B ⟶ B)
    (h : ∀ x, g (p x) = q (f x)) (y : B) :
    CompHausAddCommGrp.quotientRangeMap p q f g h
        (QuotientAddGroup.mk y) = QuotientAddGroup.mk (q y) := by
  simpa only using CompHausAddCommGrp.quotientRangeMap_mk p q f g h y

noncomputable abbrev threeElementGroup : CompHausAddCommGrp :=
  CompHausAddCommGrp.of (ZMod 3)

example (x : threeElementGroup) :
    CompHausAddCommGrp.quotientRangeπ (𝟙 threeElementGroup)
      ((𝟙 threeElementGroup) x) = 0 := by
  simpa only using CompHausAddCommGrp.quotientRangeπ_comp_apply
    (𝟙 threeElementGroup) x

example : (CompHausAddCommGrp.finiteFinsupp threeElementGroup (Fin 2) : Type) =
    (Fin 2 →₀ threeElementGroup) :=
  rfl

example (f : (Fin 2 →₀ threeElementGroup) →+
      (Fin 2 →₀ threeElementGroup))
    (hf : ∀ i j, Continuous (fun x ↦ f (Finsupp.single i x) j))
    (x : Fin 2 →₀ threeElementGroup) :
    CompHausAddCommGrp.finiteFinsuppMap threeElementGroup threeElementGroup
      (Fin 2) (Fin 2) f hf x = f x := by
  simpa only using CompHausAddCommGrp.finiteFinsuppMap_apply
    threeElementGroup threeElementGroup (Fin 2) (Fin 2) f hf x

example (x : Fin 2 →₀ threeElementGroup) :
    CompHausAddCommGrp.finiteFinsuppMap threeElementGroup threeElementGroup
        (Fin 2) (Fin 2) (AddMonoidHom.id _) (by
          intro i j
          exact continuous_of_discreteTopology) x = x := by
  rfl

noncomputable local instance {K : Type v} [SmallCategory K] :
    HasLimitsOfShape K CompHausAddCommGrp.{max u v} :=
  ⟨fun _ ↦ inferInstance⟩

variable {J : Type v} [SmallCategory J]
variable (F G H : J ⥤ CompHausAddCommGrp.{max u v})

example (j : J) (x : (CompHausAddCommGrp.limitCone F).pt) :
    (CompHausAddCommGrp.limitCone F).π.app j x = x.1 j := by
  rfl

example [IsCofilteredOrEmpty J] (j : J) (x : F.obj j)
    (hx : x ∈ (F ⋙ forget CompHausAddCommGrp).eventualRange j) :
    ∃ y : (limit F : CompHausAddCommGrp), limit.π F j y = x := by
  have hr := CompHausAddCommGrp.limit_π_range_eq_eventualRange F j
  exact hr.symm.subset hx

example [IsCofilteredOrEmpty J] (η : F ⟶ G)
    (hη : ∀ k, Function.Surjective (η.app k)) :
    Function.Surjective (lim.map η) :=
  CompHausAddCommGrp.limit_map_surjective F G η hη

example [IsCofilteredOrEmpty J] (η : F ⟶ G) (θ : G ⟶ H)
    (h : ∀ k, Function.Exact (η.app k) (θ.app k)) :
    Function.Exact (lim.map η) (lim.map θ) :=
  CompHausAddCommGrp.limit_map_exact F G η H θ h

local instance : IsCofilteredOrEmpty PEmpty.{1} where
  cone_objs x := isEmptyElim x
  cone_maps := by intro x; exact isEmptyElim x

example (F G : PEmpty.{1} ⥤ CompHausAddCommGrp.{0}) (η : F ⟶ G) :
    Function.Surjective (lim.map η) := by
  exact CompHausAddCommGrp.limit_map_surjective F G η
    (fun k ↦ isEmptyElim k)

example {R : Type u} [Ring R] [TopologicalSpace R]
    {K : Type v} [SmallCategory K]
    (D : K ⥤ TopModuleCat.{max u v} R)
    [∀ k, CompactSpace (D.obj k)] [∀ k, T2Space (D.obj k)] :
    CompactSpace ↥(limit D) ∧ T2Space ↥(limit D) :=
  ⟨TopModuleCat.compactSpace_limit_of_compact_t2 D,
    TopModuleCat.t2Space_limit_of_compact_t2 D⟩

end CompactFoundationNative
