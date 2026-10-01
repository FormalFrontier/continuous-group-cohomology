/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Injectivity of native continuous cochain restriction

Surjective group homomorphisms and injective coefficient morphisms induce injective maps
on each term of the standard resolution, on homogeneous cochains, and on cocycles.
The cochain map also reflects vanishing of the differential. No assertion about
injectivity on cohomology follows: a cochain becoming a boundary after restriction
need not have been a boundary beforehand.
-/

@[expose] public section

universe u v

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep k G} {Y : TopRep k H}

/-- A surjective group homomorphism and an injective coefficient map give an
injective map at every level of the native continuous resolution. -/
theorem resolutionMap_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (i : ℕ) :
    Function.Injective (resolutionMap φ f i).hom := by
  induction i with
  | zero => exact hf
  | succ i hi =>
    intro a b hab
    apply ContinuousMap.ext
    intro g
    obtain ⟨h, rfl⟩ := hφ g
    apply hi
    have heval := congrArg (fun F => F h) hab
    simpa only [resolutionMap_succ, TopRep.hom_ofHom, coind₁ResMap_apply] using heval

/-- Homogeneous cochains are invariant elements of level `n + 1` of the resolution;
the restriction of an injective resolution map remains injective. -/
theorem cochainsMap_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective ((cochainsMap φ f).f n) := by
  intro a b hab
  apply Subtype.ext
  apply resolutionMap_injective φ f hφ hf (n + 1)
  exact congrArg Subtype.val hab

/-- The restriction map on native continuous cocycles is injective. -/
theorem cocyclesMap_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective (cocyclesMap φ f n) := by
  have : Mono ((cochainsMap φ f).f n) :=
    ConcreteCategory.mono_of_injective _ (cochainsMap_injective φ f hφ hf n)
  let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (forget (TopModuleCat k)) := by
    rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
    infer_instance
  exact ConcreteCategory.injective_of_mono_of_preservesPullback (cocyclesMap φ f n)

/-- Native cochain restriction reflects being a cocycle: vanishing of a differential
is equivalent to vanishing before applying the injective cochain map. -/
theorem cochainsMap_d_eq_zero_iff (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hφ : Function.Surjective φ) (hf : Function.Injective f.hom) (n : ℕ)
    (σ : (homogeneousCochains X).X n) :
    (homogeneousCochains Y).d n (n + 1) ((cochainsMap φ f).f n σ) = 0 ↔
      (homogeneousCochains X).d n (n + 1) σ = 0 := by
  have hcomm := congrArg (fun g => g σ) ((cochainsMap φ f).comm n (n + 1))
  constructor
  · intro hd
    apply cochainsMap_injective φ f hφ hf (n + 1)
    simpa only [ConcreteCategory.comp_apply, map_zero] using hcomm.symm.trans hd
  · intro hd
    simpa only [ConcreteCategory.comp_apply, hd, map_zero] using hcomm

end ContinuousCohomology
