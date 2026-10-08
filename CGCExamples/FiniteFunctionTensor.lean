/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteFunctionTensor
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.ZMod.Basic

/-!
# Finite-group tensor conventions

A four-cycle and a transposition in `S₄` distinguish left multiplication,
right multiplication, inverse-left multiplication, and the right-precomposition
action of ordinary coinduction. Delta functions and their tensor images are
nonzero; basis and coefficient evaluations distinguish the twisted left action
from ordinary right precomposition.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct

namespace CGCExamples

universe u v w w'

private theorem finiteIndex_inverse_basis_coefficient
    (R : Type u) (I : Type v) (M : Type w)
    [CommSemiring R] [Finite I]
    [AddCommMonoid M] [Module R M] (s : I) (m : M) :
    ((MonoidAlgebra.finiteFunctionTensorLinearEquiv R I M).symm
      (m ⊗ₜ[R] MonoidAlgebra.single s 1)) s = m := by
  classical
  simp

private theorem finiteIndex_constant_expansion
    (R : Type u) (I : Type v) (M : Type w)
    [CommSemiring R] [Fintype I] [AddCommMonoid M] [Module R M] (m : M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R I M (fun _ : I => m) =
      ∑ s : I, m ⊗ₜ[R] MonoidAlgebra.single s 1 :=
  MonoidAlgebra.finiteFunctionTensorLinearEquiv_apply R I M _

private theorem finiteIndex_constant_naturality
    (R : Type u) (I : Type v) (M : Type w) (N : Type w')
    [CommSemiring R] [Finite I]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (linearMap : M →ₗ[R] N) (m : M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R I N (fun _ : I => linearMap m) =
      TensorProduct.map linearMap (LinearMap.id : R[I] →ₗ[R] R[I])
        (MonoidAlgebra.finiteFunctionTensorLinearEquiv R I M (fun _ : I => m)) :=
  MonoidAlgebra.finiteFunctionTensorLinearEquiv_naturality linearMap (fun _ : I => m)

private abbrev fourCycle : Equiv.Perm (Fin 4) := Fin.cycleRange 3
private abbrev transposition : Equiv.Perm (Fin 4) := Equiv.swap 0 1

private theorem four_supports_distinct :
    List.Nodup [fourCycle * transposition, transposition * fourCycle,
      fourCycle⁻¹ * transposition, transposition * fourCycle⁻¹] := by
  decide

/-- In `S₄`, a four-cycle sends the transposition basis index to a different
index from ordinary right-precomposition coinduction. -/
theorem fourCycle_leftSupport_ne_rightSupport :
    Fin.cycleRange (3 : Fin 4) * Equiv.swap (0 : Fin 4) 1 ≠
      Equiv.swap (0 : Fin 4) 1 * (Fin.cycleRange (3 : Fin 4))⁻¹ := by
  decide

private theorem signed_cycle : (Equiv.Perm.sign fourCycle : ℤ) = -1 := by
  rw [Fin.sign_cycleRange]
  norm_num

private def signedPermutation : Representation ℤ (Equiv.Perm (Fin 4)) ℤ :=
  (Representation.ofDistribMulAction ℤ ℤˣ ℤ).comp Equiv.Perm.sign

private theorem signedPermutation_cycle : signedPermutation fourCycle (1 : ℤ) = -1 := by
  change (Equiv.Perm.sign fourCycle : ℤ) * (1 : ℤ) = -1
  simp

private theorem delta_nonzero :
    (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ) ≠ 0 := by
  intro h
  have := congrFun h transposition
  norm_num at this

private theorem delta_nonconstant :
    (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ) transposition ≠
      (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ) 1 := by
  have h : transposition ≠ (1 : Equiv.Perm (Fin 4)) := by decide
  simp [h]

private theorem delta_forward :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ
      (Pi.single transposition 1) =
      (1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single transposition 1 := by
  simp

private theorem delta_inverse :
    (MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ).symm
        ((1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single transposition 1) =
      Pi.single transposition 1 := by
  simp

private theorem basis_tensor_nonzero :
    ((1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single transposition 1 :
      ℤ ⊗[ℤ] ℤ[Equiv.Perm (Fin 4)]) ≠ 0 := by
  intro h
  have hdelta := delta_inverse
  rw [h, map_zero] at hdelta
  exact delta_nonzero hdelta.symm

private theorem twisted_delta_value :
    ((fun t : Equiv.Perm (Fin 4) => (Equiv.Perm.sign fourCycle : ℤ) *
      (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ) (fourCycle⁻¹ * t))
        (fourCycle * transposition)) = -1 := by
  rw [signed_cycle]
  simp

private theorem ordinary_right_delta_value :
    ((fun t : Equiv.Perm (Fin 4) =>
      (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ) (t * fourCycle))
        (transposition * fourCycle⁻¹)) = 1 := by
  simp

private theorem twisted_tensor_basis :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ
        (fun t => signedPermutation fourCycle
          ((Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ)
            (fourCycle⁻¹ * t))) =
      (-1 : ℤ) ⊗ₜ[ℤ]
        MonoidAlgebra.single (fourCycle * transposition) 1 := by
  rw [Representation.finiteFunctionTensorLinearEquiv_twisted_single,
    signedPermutation_cycle]

private theorem twisted_tensor_coefficient :
    ((MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ).symm
        ((-1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single (fourCycle * transposition) 1))
          (fourCycle * transposition) = -1 := by
  simp

private theorem ordinary_right_tensor_basis :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ
        (fun t => (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ)
          (t * fourCycle)) =
      (1 : ℤ) ⊗ₜ[ℤ]
        MonoidAlgebra.single (transposition * fourCycle⁻¹) 1 := by
  classical
  have hfun : (fun t : Equiv.Perm (Fin 4) =>
      (Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ)
        (t * fourCycle)) =
        Pi.single (transposition * fourCycle⁻¹) (1 : ℤ) := by
    funext t
    by_cases ht : t = transposition * fourCycle⁻¹
    · subst t
      simp [mul_assoc]
    · have hne : t * fourCycle ≠ transposition := by
        intro h
        apply ht
        calc t = (t * fourCycle) * fourCycle⁻¹ := by simp
          _ = transposition * fourCycle⁻¹ := by rw [h]
      simp [ht, hne]
  rw [hfun]
  simp

private theorem signed_equivariance_client :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ (Equiv.Perm (Fin 4)) ℤ
        (fun t => signedPermutation fourCycle
          ((Pi.single transposition (1 : ℤ) : Equiv.Perm (Fin 4) → ℤ)
            (fourCycle⁻¹ * t))) =
      (signedPermutation.tprod (Representation.leftRegular ℤ (Equiv.Perm (Fin 4))))
        fourCycle (MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ
          (Equiv.Perm (Fin 4)) ℤ (Pi.single transposition 1)) :=
  Representation.finiteFunctionTensorLinearEquiv_twisted signedPermutation
    fourCycle (Pi.single transposition 1)

private theorem zero_coefficient_boundary (f : Unit → ZMod 1) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv ℤ Unit (ZMod 1) f = 0 := by
  have : f = 0 := Subsingleton.elim _ _
  simp [this]

end CGCExamples
