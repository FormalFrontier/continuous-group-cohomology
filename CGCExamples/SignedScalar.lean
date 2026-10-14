/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.ZMod
import Mathlib.Tactic.NormNum

/-!
# Signed scalar representations modulo four

Integer units act on `ZMod 4` and on its square by scalar multiplication through
`ℤ →+* ZMod 4`. The sum of two identity morphisms is multiplication by two; the
diagonal is an equivariant continuous linear map. Multiplication by two is neither
zero nor identity, although it kills the nonzero residue two. The diagonal sends
that residue to the nonzero pair `(2, 2)`.

## References

* `CGCExamples.TopRepDiscrete.SignAction`, by Formal Frontier Agents, supplies the
  integer-unit sign convention. Beacon's continuous-representation development
  provides the surrounding library context.
* Mathlib's continuous representations and `TopRep`, by Edison Xie and Richard Hill,
  supply the representation and morphism constructors.
* Mathlib's continuous-linear-map development, by Jan-David Salchow, Sébastien
  Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth, supplies
  the scalar-endomorphism algebra and product map.
* Mathlib's integer, units and modular-arithmetic APIs, including work by Jeremy
  Avigad, Johannes Hölzl, Mario Carneiro, Chris Hughes, Eric Rodriguez and David Loeffler, supply
  the canonical algebraic structures and topologies.

These examples were developed with AI assistance.

## Limitations

The coefficient ring here is `ZMod 4`: its regular module and square are free over
that ring. Scalar restriction to `ℤ`, where a nonfree module can occur, is not part
of these constructions. No invariant-subtype object or cohomology comparison is
constructed in this module.
-/

@[expose] public section

open CategoryTheory

namespace CGCExamples

noncomputable section

/-- Integer units act on the regular `ZMod 4` module by their scalar signs. -/
abbrev signedFour : TopRep.{0} (ZMod 4) ℤˣ :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (((algebraMap (ZMod 4) ((ZMod 4) →L[ZMod 4] (ZMod 4))).toMonoidHom).comp
      (((Int.castRingHom (ZMod 4)).toMonoidHom).comp (Units.coeHom ℤ))))

/-- Integer units act on the square of `ZMod 4` by the same sign in each coordinate. -/
abbrev signedFourProduct : TopRep.{0} (ZMod 4) ℤˣ :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (((algebraMap (ZMod 4)
      ((ZMod 4 × ZMod 4) →L[ZMod 4] (ZMod 4 × ZMod 4))).toMonoidHom).comp
      (((Int.castRingHom (ZMod 4)).toMonoidHom).comp (Units.coeHom ℤ))))

/-- The carrier of the signed scalar representation is `ZMod 4`. -/
@[simp] theorem signedFour_V : signedFour.V = ZMod 4 := rfl

/-- The carrier of the product representation is the square of `ZMod 4`. -/
@[simp] theorem signedFourProduct_V : signedFourProduct.V = (ZMod 4 × ZMod 4) := rfl

/-- An integer unit acts by multiplication by its residue modulo four. -/
@[simp] theorem signedFour_ρ_apply (g : ℤˣ) (x : ZMod 4) :
    signedFour.ρ g x = ((g : ℤ) : ZMod 4) * x := by
  change algebraMap (ZMod 4) ((ZMod 4) →L[ZMod 4] (ZMod 4))
    (((g : ℤ) : ZMod 4)) x = _
  exact ContinuousLinearMap.algebraMap_apply _ x

/-- The product action is scalar multiplication in both coordinates. -/
@[simp] theorem signedFourProduct_ρ_apply (g : ℤˣ) (x : ZMod 4 × ZMod 4) :
    signedFourProduct.ρ g x =
      (((g : ℤ) : ZMod 4) * x.1, ((g : ℤ) : ZMod 4) * x.2) := by
  change algebraMap (ZMod 4)
    ((ZMod 4 × ZMod 4) →L[ZMod 4] (ZMod 4 × ZMod 4))
    (((g : ℤ) : ZMod 4)) x = _
  exact ContinuousLinearMap.algebraMap_apply _ x

/-- Every sign operator sends zero to zero. -/
@[simp] theorem signedFour_ρ_zero (g : ℤˣ) : signedFour.ρ g (0 : ZMod 4) = 0 := by
  exact (signedFour_ρ_apply g 0).trans (mul_zero _)

/-- Multiplication by two on `ZMod 4`, as a continuous linear map. -/
def twiceFourCLM : (ZMod 4) →L[ZMod 4] (ZMod 4) :=
  (2 : ZMod 4) • ContinuousLinearMap.id (ZMod 4) (ZMod 4)

/-- The continuous linear map `twiceFourCLM` multiplies by two. -/
@[simp] theorem twiceFourCLM_apply (x : ZMod 4) : twiceFourCLM x = 2 * x := rfl

/-- The sum of two identity morphisms of the signed scalar representation. -/
def twiceFour : signedFour ⟶ signedFour := 𝟙 signedFour + 𝟙 signedFour

/-- The continuous linear map underlying the doubled identity is multiplication by two. -/
theorem twiceFour_hom : twiceFour.hom.toContinuousLinearMap = twiceFourCLM := by
  apply ContinuousLinearMap.ext
  intro x
  change x + x = (2 : ZMod 4) * x
  exact (two_mul x).symm

/-- The doubled identity sends `x` to `2 * x`. -/
@[simp] theorem twiceFour_apply (x : ZMod 4) : twiceFour x = 2 * x := by
  change twiceFour.hom.toContinuousLinearMap x = _
  rw [twiceFour_hom, twiceFourCLM_apply]

/-- The diagonal continuous linear map from `ZMod 4` to its square. -/
def diagonalFourCLM : (ZMod 4) →L[ZMod 4] (ZMod 4 × ZMod 4) :=
  (ContinuousLinearMap.id (ZMod 4) (ZMod 4)).prod
    (ContinuousLinearMap.id (ZMod 4) (ZMod 4))

/-- The continuous linear diagonal sends `x` to `(x, x)`. -/
@[simp] theorem diagonalFourCLM_apply (x : ZMod 4) : diagonalFourCLM x = (x, x) := rfl

/-- The diagonal morphism intertwines the scalar sign actions. -/
def diagonalFour : signedFour ⟶ signedFourProduct :=
  TopRep.ofHom {
    toContinuousLinearMap := diagonalFourCLM
    isIntertwining' := fun g => by
      apply ContinuousLinearMap.ext
      intro x
      change diagonalFourCLM (signedFour.ρ g x) =
        signedFourProduct.ρ g (diagonalFourCLM x)
      calc
        diagonalFourCLM (signedFour.ρ g x) =
            (signedFour.ρ g x, signedFour.ρ g x) :=
          diagonalFourCLM_apply (signedFour.ρ g x)
        _ = (((g : ℤ) : ZMod 4) * x, ((g : ℤ) : ZMod 4) * x) :=
          congrArg (fun y : ZMod 4 => (y, y)) (signedFour_ρ_apply g x)
        _ = signedFourProduct.ρ g (x, x) :=
          (signedFourProduct_ρ_apply g (x, x)).symm
        _ = signedFourProduct.ρ g (diagonalFourCLM x) :=
          congrArg (fun y => signedFourProduct.ρ g y) (diagonalFourCLM_apply x).symm
  }

/-- The continuous linear map underlying the diagonal morphism is `diagonalFourCLM`. -/
theorem diagonalFour_hom : diagonalFour.hom.toContinuousLinearMap = diagonalFourCLM := rfl

/-- The equivariant diagonal sends `x` to `(x, x)`. -/
@[simp] theorem diagonalFour_apply (x : ZMod 4) : diagonalFour x = (x, x) := by
  change diagonalFour.hom.toContinuousLinearMap x = _
  rw [diagonalFour_hom, diagonalFourCLM_apply]

/-- The residue two modulo four is nonzero. -/
theorem two_four_ne_zero : (2 : ZMod 4) ≠ 0 := by
  intro h
  have hdiv : (4 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 4).mp h
  norm_num at hdiv

/-- The negative integer unit moves the residue one, so the sign action is nontrivial. -/
theorem signedFour_negative_one_moves_one :
    signedFour.ρ (-1 : ℤˣ) (1 : ZMod 4) ≠ (1 : ZMod 4) := by
  rw [signedFour_ρ_apply]
  simp only [Units.coe_neg_one, Int.cast_neg, Int.cast_one, mul_one]
  intro h
  have hmod := ZMod.neg_one_eq_one_iff.mp h
  norm_num at hmod

/-- Multiplication by two sends one to the nonzero residue two. -/
@[simp] theorem twiceFour_one : twiceFour (1 : ZMod 4) = 2 := by
  exact (twiceFour_apply 1).trans (mul_one _)

/-- Multiplication by two sends zero to zero. -/
@[simp] theorem twiceFour_zero : twiceFour (0 : ZMod 4) = 0 := by
  exact (twiceFour_apply 0).trans (mul_zero _)

/-- Multiplication by two kills the nonzero residue two modulo four. -/
@[simp] theorem twiceFour_two : twiceFour (2 : ZMod 4) = 0 := by
  calc
    twiceFour (2 : ZMod 4) = (2 : ZMod 4) * 2 := twiceFour_apply 2
    _ = (4 : ZMod 4) := by norm_num
    _ = 0 := ZMod.natCast_self 4

/-- The doubled identity is not the identity morphism. -/
theorem twiceFour_nonidentity : twiceFour ≠ 𝟙 signedFour := by
  intro h
  have hval := congrArg (fun f : signedFour ⟶ signedFour => f (1 : ZMod 4)) h
  change twiceFour (1 : ZMod 4) = (1 : ZMod 4) at hval
  rw [twiceFour_one] at hval
  have hmod := (ZMod.natCast_eq_natCast_iff' 2 1 4).mp hval
  norm_num at hmod

/-- Multiplication by two is a nonzero equivariant morphism. -/
theorem twiceFour_ne_zero : twiceFour ≠ 0 := by
  intro h
  have hval := congrArg (fun f : signedFour ⟶ signedFour => f (1 : ZMod 4)) h
  change twiceFour (1 : ZMod 4) = (0 : ZMod 4) at hval
  rw [twiceFour_one] at hval
  exact two_four_ne_zero hval

/-- The diagonal sends the residue two to `(2, 2)`. -/
@[simp] theorem diagonalFour_two : diagonalFour (2 : ZMod 4) = (2, 2) :=
  diagonalFour_apply 2

/-- The diagonal has a nonzero value at the residue two. -/
theorem diagonalFour_two_ne_zero : diagonalFour (2 : ZMod 4) ≠ 0 := by
  intro h
  rw [diagonalFour_apply] at h
  exact two_four_ne_zero (congrArg Prod.fst h)

/-- The equivariant diagonal is a nonzero morphism. -/
theorem diagonalFour_ne_zero : diagonalFour ≠ 0 := by
  intro h
  apply diagonalFour_two_ne_zero
  have hval := congrArg
    (fun f : signedFour ⟶ signedFourProduct => f (2 : ZMod 4)) h
  exact hval

end

end CGCExamples
