/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CGCExamples.TopRepDiscrete.SignAction
public import ContinuousGroupCohomology.FiniteStageColimit
import examples.FiniteStageResolutionNative

/-!
# Colimit clients and a nonconstant sign cochain

The sign action of integer units on the discrete integers supplies a nonzero,
nonconstant homogeneous cochain. It has a unique lift at a chosen quotient
stage, that lift is compatible with every refinement, and the cochain-colimit
descendant into any cocone has the prescribed value on it. No closedness or
cohomology-class assertion is made about this cochain.

The existing arbitrary-degree cohomology comparison and arbitrary-target clients
reside in `examples.FiniteStageResolutionNative`. This example reuses Formal
Frontier's sign representation and Mathlib's homogeneous cochain construction.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace CGCExamples

open CategoryTheory CategoryTheory.Limits _root_.ContinuousCohomology

private instance : CompactSpace ℤˣ := Finite.compactSpace

/-- The sign orbit of `1` is a nonconstant, nonzero cochain on which the
cochain-colimit descendant satisfies its universal factorization equation.
Its lift is unique at the selected stage and remains a lift after refinement. -/
theorem signedIntegers_nonconstant_cochain_descendant
    (s : Cocone (openNormalCochainDiagram signedIntegers)) :
    ∃ (σ : (TopRep.homogeneousCochains signedIntegers).X 0),
      σ.1 (-1 : ℤˣ) ≠ σ.1 1 ∧ σ.1 (-1 : ℤˣ) ≠ 0 ∧
      ∃ (U : OpenNormalSubgroup ℤˣ)
        (τ : ((openNormalCochainDiagram signedIntegers).obj U).X 0),
        ((openNormalCochainInflationCocone signedIntegers).ι.app U).f 0 τ = σ ∧
        ((openNormalCochainInflationCoconeIsColimit signedIntegers).desc s).f 0 σ =
          (s.ι.app U).f 0 τ ∧
        (∀ υ : ((openNormalCochainDiagram signedIntegers).obj U).X 0,
          ((openNormalCochainInflationCocone signedIntegers).ι.app U).f 0 υ = σ → υ = τ) ∧
        (∀ (V : OrderDual (OpenNormalSubgroup ℤˣ))
          (f : OrderDual.toDual U ⟶ V),
          ((openNormalCochainInflationCocone signedIntegers).ι.app V).f 0
            (((openNormalCochainDiagram signedIntegers).map f).f 0 τ) = σ) := by
  let orbit : TopRep.resolutionX signedIntegers 1 :=
    ⟨fun g => signedIntegers.ρ g (1 : ℤ),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hfix : orbit ∈ (TopRep.resolutionX signedIntegers 1).ρ.invariants := by
    intro g
    apply ContinuousMap.ext
    intro h
    change signedIntegers.ρ g (signedIntegers.ρ (g⁻¹ * h) (1 : ℤ)) =
      signedIntegers.ρ h (1 : ℤ)
    change (signedIntegers.ρ g * signedIntegers.ρ (g⁻¹ * h)) (1 : ℤ) =
      signedIntegers.ρ h (1 : ℤ)
    rw [← map_mul, mul_inv_cancel_left]
  let σ : (TopRep.homogeneousCochains signedIntegers).X 0 := ⟨orbit, hfix⟩
  have hnonconstant : σ.1 (-1 : ℤˣ) ≠ σ.1 1 := by
    change signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) ≠ signedIntegers.ρ 1 (1 : ℤ)
    simpa only [signedIntegers_ρ_apply, one_smul] using
      signedIntegers_negative_one_not_fixed
  have hnonzero : σ.1 (-1 : ℤˣ) ≠ 0 := by
    change signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) ≠ (0 : ℤ)
    rw [signedIntegers_negative_one]
    exact neg_ne_zero.mpr (one_ne_zero (α := ℤ))
  obtain ⟨U, τ, hτ⟩ :=
    openNormalCochainInflationCocone_jointly_surjective signedIntegers 0 σ
  refine ⟨σ, hnonconstant, hnonzero, U, τ, hτ, ?_, ?_, ?_⟩
  · simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply, hτ] using
      congrArg
        (fun f : (openNormalCochainDiagram signedIntegers).obj U ⟶ s.pt => f.f 0 τ)
        ((openNormalCochainInflationCoconeIsColimit signedIntegers).fac s U)
  · intro υ hυ
    exact openNormalCochainInflationCocone_ι_app_f_injective signedIntegers U 0
      (hυ.trans hτ.symm)
  · intro V f
    exact (openNormalCochainInflationCocone_naturality_f_apply signedIntegers f 0 τ).trans hτ

end CGCExamples
