/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Functions on a finite group as tensors with its group algebra

For a finite group, coefficient evaluation identifies a tensor with a function;
the inverse takes the finite sum of the values tensored with the corresponding
group-algebra basis elements. The diagonal left-regular action corresponds to
the twisted left action, not to ordinary right-translation coinduction.

The underlying linear equivalence and its coefficient API are obtained from
existing Mathlib equivalences and require only a finite index type. Its inverse
evaluates pure tensors coefficientwise and maps basis tensors to delta functions.

## Limitations

For an infinite group the tensor construction still has finite support;
a constant function with a nonzero value does not. No identification with
continuous maps or discrete topological representations is asserted here.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, second edition,
  Chapter I §3, for the integral finite-group formula with the twisted action.
* Mathlib's `MonoidAlgebra.coeffLinearEquiv`,
  `TensorProduct.finsuppScalarRight`, and `Finsupp.linearEquivFunOnFinite`.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct

universe u v w w'

namespace MonoidAlgebra

variable (R : Type u) (G : Type v) (M : Type w)
  [CommSemiring R] [Finite G] [AddCommMonoid M] [Module R M]

/-- Finite functions are linearly equivalent to the coefficient module tensored
with the group algebra, with the coefficient module on the left. -/
noncomputable def finiteFunctionTensorLinearEquiv :
    (G → M) ≃ₗ[R] (M ⊗[R] R[G]) := by
  classical
  exact ((TensorProduct.congr (LinearEquiv.refl R M) (coeffLinearEquiv R)) ≪≫ₗ
    TensorProduct.finsuppScalarRight R R M G ≪≫ₗ
    Finsupp.linearEquivFunOnFinite R M G).symm

/-- Evaluation of the inverse on a pure tensor is coefficient evaluation. -/
@[simp] theorem finiteFunctionTensorLinearEquiv_symm_tmul_apply
    (m : M) (p : R[G]) (t : G) :
    ((finiteFunctionTensorLinearEquiv R G M).symm (m ⊗ₜ[R] p)) t = p.coeff t • m := by
  classical
  simp [finiteFunctionTensorLinearEquiv]

section

variable [DecidableEq G]

/-- A delta function maps to the corresponding pure group-algebra tensor. -/
@[simp] theorem finiteFunctionTensorLinearEquiv_single (s : G) (m : M) :
    finiteFunctionTensorLinearEquiv R G M (Pi.single s m) =
      m ⊗ₜ[R] single s 1 := by
  classical
  simp [finiteFunctionTensorLinearEquiv]

/-- The inverse on a group-algebra basis tensor is a delta function. -/
@[simp] theorem finiteFunctionTensorLinearEquiv_symm_single (s : G) (m : M) :
    (finiteFunctionTensorLinearEquiv R G M).symm (m ⊗ₜ[R] single s 1) =
      Pi.single s m := by
  classical
  simpa only [finiteFunctionTensorLinearEquiv_single] using
    (finiteFunctionTensorLinearEquiv R G M).symm_apply_apply (Pi.single s m)

end

variable [Fintype G]

/-- The forward equivalence is the finite sum of coefficient tensors. -/
theorem finiteFunctionTensorLinearEquiv_apply (f : G → M) :
    finiteFunctionTensorLinearEquiv R G M f =
      ∑ s : G, f s ⊗ₜ[R] single s 1 := by
  classical
  calc
    finiteFunctionTensorLinearEquiv R G M f =
        finiteFunctionTensorLinearEquiv R G M (∑ s : G, Pi.single s (f s)) := by
      congr 1
      ext t
      simp
    _ = ∑ s : G, finiteFunctionTensorLinearEquiv R G M (Pi.single s (f s)) := by
      simp
    _ = ∑ s : G, f s ⊗ₜ[R] single s 1 := by simp

end MonoidAlgebra

namespace MonoidAlgebra

variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}
  [CommSemiring R] [Finite G]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Coefficientwise linear maps commute with the finite function–tensor
equivalence. In particular this does not require an action on either module. -/
theorem finiteFunctionTensorLinearEquiv_naturality
    (v : M →ₗ[R] N) (f : G → M) :
    finiteFunctionTensorLinearEquiv R G N (v ∘ f) =
      TensorProduct.map v (LinearMap.id : R[G] →ₗ[R] R[G])
        (finiteFunctionTensorLinearEquiv R G M f) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  rw [finiteFunctionTensorLinearEquiv_apply R G N,
    finiteFunctionTensorLinearEquiv_apply R G M]
  simp only [Function.comp_apply, map_sum, TensorProduct.map_tmul, LinearMap.id_apply]

end MonoidAlgebra

namespace Representation

variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}
  [CommSemiring R] [Group G] [Finite G]
  [AddCommMonoid M] [Module R M]

/-- Under the finite function–tensor equivalence, the twisted action
`t ↦ ρ(g)(f(g⁻¹t))` equals the diagonal action with the **left** regular
action on `R[G]`. This generalizes the integral finite-group formula of
Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I §3;
the left-regular factor action is inferred from the published formula and
twisted action, not specified separately there. This is not ordinary
right-translation coinduction. -/
theorem finiteFunctionTensorLinearEquiv_twisted (ρ : Representation R G M)
    (g : G) (f : G → M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M
        (fun t => ρ g (f (g⁻¹ * t))) =
      (ρ.tprod (Representation.leftRegular R G)) g
        (MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M f) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  calc
    _ = ∑ t : G, ρ g (f (g⁻¹ * t)) ⊗ₜ[R] MonoidAlgebra.single t 1 :=
      MonoidAlgebra.finiteFunctionTensorLinearEquiv_apply R G M _
    _ = ∑ s : G, ρ g (f s) ⊗ₜ[R] MonoidAlgebra.single (g * s) 1 := by
      exact (Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _
        (by intro s; simp)).symm
    _ = _ := by
      rw [MonoidAlgebra.finiteFunctionTensorLinearEquiv_apply R G M f, map_sum]
      simp only [Representation.tprod_apply, TensorProduct.map_tmul,
        Representation.ofMulAction_single, smul_eq_mul]

/-- On a delta function, the explicit twisted action shifts the index on the
left and acts on its coefficient; its image is a pure basis tensor. -/
theorem finiteFunctionTensorLinearEquiv_twisted_single
    [DecidableEq G] (ρ : Representation R G M) (g s : G) (m : M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M
        (fun t => ρ g ((Pi.single s m : G → M) (g⁻¹ * t))) =
      ρ g m ⊗ₜ[R] MonoidAlgebra.single (g * s) 1 := by
  classical
  have hfun : (fun t => ρ g ((Pi.single s m : G → M) (g⁻¹ * t))) =
      Pi.single (g * s) (ρ g m) := by
    funext t
    by_cases ht : t = g * s
    · subst t
      simp
    · have hne : g⁻¹ * t ≠ s := by
        intro h
        apply ht
        calc t = g * (g⁻¹ * t) := by simp
          _ = g * s := by rw [h]
      simp [ht, hne]
  rw [hfun]
  exact MonoidAlgebra.finiteFunctionTensorLinearEquiv_single R G M (g * s) (ρ g m)

omit [Finite G] in
/-- The diagonal left-regular action shifts a group-algebra basis element
on the left. -/
@[simp] theorem tprod_leftRegular_single (ρ : Representation R G M)
    (g s : G) (m : M) :
    (ρ.tprod (Representation.leftRegular R G)) g
        (m ⊗ₜ[R] MonoidAlgebra.single s 1) =
      ρ g m ⊗ₜ[R] MonoidAlgebra.single (g * s) 1 := by
  simp [Representation.tprod_apply, Representation.ofMulAction_single]

/-- The twisted and diagonal actions agree on each group-algebra basis tensor,
as given by the explicit delta and left-regular basis formulas. -/
theorem finiteFunctionTensorLinearEquiv_twisted_basis
    [DecidableEq G] (ρ : Representation R G M) (g s : G) (m : M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M
        (fun t => ρ g ((Pi.single s m : G → M) (g⁻¹ * t))) =
      (ρ.tprod (Representation.leftRegular R G)) g
        (MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M (Pi.single s m)) := by
  rw [finiteFunctionTensorLinearEquiv_twisted_single,
    MonoidAlgebra.finiteFunctionTensorLinearEquiv_single,
    tprod_leftRegular_single]

end Representation
