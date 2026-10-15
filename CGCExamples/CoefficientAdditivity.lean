/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ContinuousCohomologyFunctor
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Mathlib.Topology.Instances.Int

/-!
# Doubling a nonzero integer cohomology class

For the trivial group acting trivially on the integers, the degree-zero class
corresponding to the invariant `1` is sent by the sum of two identity coefficient
morphisms to a class corresponding to `2`, which is nonzero. The calculation uses
the additive coefficient functor in arbitrary degree before specializing to zero.

## References

* Mathlib's continuous representations and continuous cohomology, by Edison Xie,
  Richard Hill, Andrew Yang and the Mathlib contributors, supply the trivial
  representation and the degree-zero isomorphism with invariants.
* Mathlib's additive functor API and canonical integer and one-element-group
  structures supply the coefficient-map calculation and the concrete coefficients.

These examples were developed with AI assistance.
-/

@[expose] public section

open CategoryTheory

namespace CGCExamples

/-- The integers with trivial action of the one-element group. -/
abbrev trivialIntegers : TopRep.{0} ℤ PUnit :=
  TopRep.of (ContRepresentation.trivial ℤ PUnit ℤ)

/-- The carrier of the trivial integer representation is the integers. -/
@[simp] theorem trivialIntegers_V : trivialIntegers.V = ℤ := rfl

/-- Every group element acts as the identity on the integer coefficients. -/
@[simp] theorem trivialIntegers_ρ_apply (g : PUnit) (x : ℤ) :
    trivialIntegers.ρ g x = x := rfl

/-- The degree-zero class corresponding to the invariant integer `1`. -/
noncomputable def integerOneClass : continuousCohomology 0 trivialIntegers :=
  (ContinuousCohomology.zeroIso trivialIntegers).inv.hom
    ⟨1, fun _ => rfl⟩

/-- The invariant value of the selected degree-zero integer class is `1`. -/
@[simp] theorem zeroIso_integerOneClass_val :
    ((ContinuousCohomology.zeroIso trivialIntegers).hom.hom integerOneClass : ℤ) = 1 := by
  exact congrArg Subtype.val
    ((ContinuousCohomology.zeroIso trivialIntegers).toContinuousLinearEquiv.apply_symm_apply
      (⟨1, fun _ => rfl⟩ : trivialIntegers.ρ.invariants))

/-- The selected degree-zero integer class is nonzero. -/
theorem integerOneClass_ne_zero : integerOneClass ≠ 0 := by
  intro h
  let z := (ContinuousCohomology.zeroIso trivialIntegers).hom.hom
  have hval : (z integerOneClass : ℤ) = (z 0 : ℤ) :=
    congrArg (fun x : continuousCohomology 0 trivialIntegers => (z x : ℤ)) h
  have hz : (z (0 : continuousCohomology 0 trivialIntegers) : ℤ) = 0 :=
    congrArg Subtype.val (_root_.map_zero z)
  have hone : (1 : ℤ) = 0 := by
    calc
      1 = (z integerOneClass : ℤ) := zeroIso_integerOneClass_val.symm
      _ = (z 0 : ℤ) := hval
      _ = 0 := hz
  exact (by decide : (1 : ℤ) ≠ 0) hone

/-- In every degree, the sum of two identity coefficient morphisms doubles each class. -/
theorem trivialIntegers_map_twice_identity (n : ℕ) (x : continuousCohomology n trivialIntegers) :
    ((ContinuousCohomology.coefficientFunctor (k := ℤ) (G := PUnit) n).map
      (𝟙 trivialIntegers + 𝟙 trivialIntegers)).hom x = x + x := by
  let F := ContinuousCohomology.coefficientFunctor (k := ℤ) (G := PUnit) n
  have hadd : F.map (𝟙 trivialIntegers + 𝟙 trivialIntegers) =
      𝟙 (F.obj trivialIntegers) + 𝟙 (F.obj trivialIntegers) := by
    calc
      F.map (𝟙 trivialIntegers + 𝟙 trivialIntegers) =
          F.map (𝟙 trivialIntegers) + F.map (𝟙 trivialIntegers) := F.map_add
      _ = 𝟙 (F.obj trivialIntegers) + 𝟙 (F.obj trivialIntegers) :=
        congrArg₂ (fun f g : F.obj trivialIntegers ⟶ F.obj trivialIntegers => f + g)
          (F.map_id trivialIntegers) (F.map_id trivialIntegers)
  have heval := congrArg
    (fun f : F.obj trivialIntegers ⟶ F.obj trivialIntegers => f.hom x) hadd
  simp only [TopModuleCat.hom_add, TopModuleCat.hom_id] at heval
  dsimp only [F, ContinuousCohomology.coefficientFunctor_obj,
    ContinuousCohomology.coefficientFunctor_map] at heval ⊢
  exact heval

/-- Doubling the chosen class has invariant value `2`. -/
theorem integerOneClass_twice_identity_value :
    ((ContinuousCohomology.zeroIso trivialIntegers).hom.hom
      (((ContinuousCohomology.coefficientFunctor (k := ℤ) (G := PUnit) 0).map
        (𝟙 trivialIntegers + 𝟙 trivialIntegers)).hom integerOneClass) : ℤ) = 2 := by
  have htwice := trivialIntegers_map_twice_identity 0 integerOneClass
  dsimp only [ContinuousCohomology.coefficientFunctor_obj,
    ContinuousCohomology.coefficientFunctor_map] at htwice ⊢
  rw [htwice]
  let z := (ContinuousCohomology.zeroIso trivialIntegers).hom.hom
  change (z (integerOneClass + integerOneClass) : ℤ) = 2
  calc
    (z (integerOneClass + integerOneClass) : ℤ) =
        (z integerOneClass : ℤ) + (z integerOneClass : ℤ) := by
      rw [_root_.map_add, Submodule.coe_add]
    _ = 1 + 1 := congrArg₂ (fun a b : ℤ => a + b)
      zeroIso_integerOneClass_val zeroIso_integerOneClass_val
    _ = 2 := rfl

/-- The sum of two identity coefficient morphisms acts nontrivially on degree-zero cohomology. -/
theorem integerOneClass_twice_identity_ne_zero :
    ((ContinuousCohomology.coefficientFunctor (k := ℤ) (G := PUnit) 0).map
      (𝟙 trivialIntegers + 𝟙 trivialIntegers)).hom integerOneClass ≠ 0 := by
  intro h
  have hval := integerOneClass_twice_identity_value
  dsimp only [ContinuousCohomology.coefficientFunctor_obj,
    ContinuousCohomology.coefficientFunctor_map] at h hval
  rw [h] at hval
  let z := (ContinuousCohomology.zeroIso trivialIntegers).hom.hom
  have hz : (z (0 : continuousCohomology 0 trivialIntegers) : ℤ) = 0 :=
    congrArg Subtype.val (_root_.map_zero z)
  have htwo : (0 : ℤ) = 2 := hz.symm.trans hval
  exact (by decide : (0 : ℤ) ≠ 2) htwo

end CGCExamples
