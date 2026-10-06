/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.TopRepDiscrete
public import CGCExamples.TopRepDiscrete.SignAction
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Topology.Instances.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sign actions on discrete direct sums and tensors

Integer units act on the integers by signs. Restricting this action to each
coordinate of a countable product gives a genuinely infinite-index sum client.
The pure tensor of two units is nonzero, while two sign changes cancel on it.
Empty sums and zero tensor factors give the complementary degenerate cases.
The diagonal tensor action is the one in `TopRep.discreteTensor`.
-/

open DirectSum TensorProduct

namespace CGCExamples

/-- The sign action of the `i`th factor of a product of unit groups. -/
private def signedCoordinate (i : ℕ) : TopRep ℤ (ℕ → ℤˣ) :=
  TopRep.res (Pi.evalMonoidHom (fun _ : ℕ => ℤˣ) i) signedIntegers

private instance signedCoordinate_discrete (i : ℕ) :
    DiscreteTopology (signedCoordinate i) := by
  change DiscreteTopology ℤ
  infer_instance

private instance signedCoordinate_jointlyContinuous (i : ℕ) :
    TopRep.JointlyContinuous (signedCoordinate i) where
  continuous_action := by
    have h : Continuous (fun p : (ℕ → ℤˣ) × ℤ => (p.1 i, p.2)) :=
      ((continuous_apply i).comp continuous_fst).prodMk continuous_snd
    change Continuous (fun p : (ℕ → ℤˣ) × ℤ => p.1 i • p.2)
    exact continuous_smul.comp h

private theorem signedInfiniteSum_nonzero :
    (DirectSum.of (fun i : ℕ => signedCoordinate i) 0 (1 : ℤ) :
      TopRep.discreteDirectSum signedCoordinate) ≠ 0 := by
  intro h
  have h₀ := congrArg (fun x : ⨁ i : ℕ, signedCoordinate i => x 0) h
  simp only [DirectSum.zero_apply] at h₀
  exact (one_ne_zero : (1 : ℤ) ≠ 0) h₀

private theorem signedInfiniteSum_jointlyContinuous :
    TopRep.JointlyContinuous (TopRep.discreteDirectSum signedCoordinate) :=
  TopRep.discreteDirectSum_jointlyContinuous signedCoordinate

private theorem signedTensor_nonzero :
    ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) : TopRep.discreteTensor signedIntegers signedIntegers) ≠ 0 := by
  intro h
  have hraw : ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) : ℤ ⊗[ℤ] ℤ) = 0 := h
  have h₀ := congrArg (TensorProduct.lid ℤ ℤ) hraw
  simp at h₀

private theorem signedTensor_signs_cancel :
    ((-1 : ℤ) ⊗ₜ[ℤ] (-1 : ℤ) : ℤ ⊗[ℤ] ℤ) =
      (1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) := by
  simp only [neg_tmul, tmul_neg, neg_neg]

/-- The pure tensor `1 ⊗ 1` is nonzero and fixed by simultaneous sign change,
although the negative unit moves `1` in each factor. -/
public theorem signedTensor_negative_one_fixes_nonzero :
    ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) : TopRep.discreteTensor signedIntegers signedIntegers) ≠ 0 ∧
      (TopRep.discreteTensor signedIntegers signedIntegers).ρ (-1 : ℤˣ)
        ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) = (1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) ∧
      signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) ≠ (1 : ℤ) := by
  refine ⟨signedTensor_nonzero, ?_, signedIntegers_negative_one_not_fixed⟩
  have h := TopRep.discreteTensor_ρ_tmul signedIntegers signedIntegers
    (-1 : ℤˣ) (1 : ℤ) (1 : ℤ)
  rw [signedIntegers_negative_one] at h
  exact h.trans signedTensor_signs_cancel

private theorem signedTensor_jointlyContinuous :
    TopRep.JointlyContinuous (TopRep.discreteTensor signedIntegers signedIntegers) :=
  TopRep.discreteTensor_jointlyContinuous signedIntegers signedIntegers

private theorem emptySum_zero
    (x : TopRep.discreteDirectSum (fun _ : Empty => signedIntegers)) : x = 0 := by
  apply DirectSum.ext
  intro i
  exact i.elim

/-- The trivial unit action on the zero integer module. -/
private def zeroIntegers : TopRep ℤ ℤˣ :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (1 : ℤˣ →* (PUnit →L[ℤ] PUnit)))

private instance zeroIntegers_discrete : DiscreteTopology zeroIntegers := by
  change DiscreteTopology PUnit
  infer_instance

private theorem zeroFactorTensor_zero
    (x : TopRep.discreteTensor zeroIntegers signedIntegers) : x = 0 := by
  exact Subsingleton.elim (α := PUnit ⊗[ℤ] ℤ) _ _

end CGCExamples
