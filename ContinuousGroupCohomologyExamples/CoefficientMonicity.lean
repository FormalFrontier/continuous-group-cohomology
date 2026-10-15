/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.InitialInvariantsExactSequence
public import CGCExamples.CochainExactness

/-!
# Injective coefficient doubling in degree zero

The constant-one endomorphism of the two-element group is not surjective.
Restricting the trivial integer representation along it leaves the coefficient
carrier unchanged. The restricted multiplication-by-two morphism is injective,
and its degree-zero cohomology map sends the class corresponding to the invariant
integer `1` to the nonzero class corresponding to `2`.

## References

* `CGCExamples.CochainExactness`, by Formal Frontier Agents, supplies the
  two-element group, the trivial integer coefficients, and multiplication by two.
* Mathlib's continuous representations and continuous-cohomology constructions,
  by Richard Hill, Andrew Yang and Edison Xie, supply restriction and `zeroIso`.
* Beacon's continuous-cohomology development provides the surrounding project API.

These examples were developed with AI assistance.
-/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology

namespace CoefficientMonicityExamples

local instance : TopologicalSpace CGCExamples.TwoGroup := ⊥
local instance : DiscreteTopology CGCExamples.TwoGroup := ⟨rfl⟩
local instance : IsTopologicalGroup CGCExamples.TwoGroup := inferInstance

/-- The constant-one continuous endomorphism of the two-element group. -/
abbrev collapseTwoGroup : CGCExamples.TwoGroup →ₜ* CGCExamples.TwoGroup := 1

/-- The group endomorphism used for restriction is not surjective. -/
theorem collapseTwoGroup_not_surjective : ¬ Function.Surjective collapseTwoGroup := by
  intro hsurj
  obtain ⟨g, hg⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod 2))
  change (Multiplicative.ofAdd (0 : ZMod 2) : CGCExamples.TwoGroup) =
    Multiplicative.ofAdd (1 : ZMod 2) at hg
  exact CGCExamples.evenSequence_group_nontrivial hg

/-- The trivial integer coefficients restricted along the constant-one map. -/
abbrev restrictedIntegers : TopRep.{0} ℤ CGCExamples.TwoGroup :=
  res collapseTwoGroup CGCExamples.evenSequenceIntegers

/-- Restriction of multiplication by two on the trivial integer coefficients. -/
def restrictedDoubling : restrictedIntegers ⟶ restrictedIntegers :=
  (resFunctor (collapseTwoGroup : CGCExamples.TwoGroup →* CGCExamples.TwoGroup)).map
    CGCExamples.evenSequenceInclusion

/-- The restricted coefficient morphism still sends `x` to `2 * x`. -/
@[simp] theorem restrictedDoubling_apply (x : ℤ) : restrictedDoubling x = 2 * x :=
  CGCExamples.evenSequenceInclusion_apply x

/-- The coefficient morphism is injective independently of cohomology. -/
theorem restrictedDoubling_injective : Function.Injective restrictedDoubling.hom :=
  CGCExamples.evenSequenceInclusion_injective

/-- The invariant integer `1` in the source coefficient representation. -/
def invariantOne : CGCExamples.evenSequenceIntegers.ρ.invariants :=
  ⟨1, by intro g; exact ContRepresentation.trivial_apply g 1⟩

/-- The invariant integer `2` in the restricted coefficient representation. -/
def invariantTwo : restrictedIntegers.ρ.invariants :=
  ⟨2, by intro g; exact ContRepresentation.trivial_apply (collapseTwoGroup g) 2⟩

/-- The invariants map sends the chosen source coefficient to the chosen target
coefficient. -/
@[simp] theorem invariantsResMap_one :
    (invariantsResMap (X := CGCExamples.evenSequenceIntegers)
      collapseTwoGroup restrictedDoubling).hom invariantOne = invariantTwo := by
  apply Subtype.ext
  rfl

/-- The chosen source invariant is nonzero. -/
theorem invariantOne_ne_zero : invariantOne ≠ 0 := by
  intro h
  have hval : (1 : ℤ) = 0 := congrArg Subtype.val h
  exact one_ne_zero hval

/-- The chosen target invariant is nonzero. -/
theorem invariantTwo_ne_zero : invariantTwo ≠ 0 := by
  intro h
  have hval : (2 : ℤ) = 0 := congrArg Subtype.val h
  omega

/-- The degree-zero source class corresponding to the invariant integer `1`. -/
noncomputable def classOne : continuousCohomology 0 CGCExamples.evenSequenceIntegers :=
  (zeroIso CGCExamples.evenSequenceIntegers).inv.hom invariantOne

/-- The degree-zero target class corresponding to the invariant integer `2`. -/
noncomputable def classTwo : continuousCohomology 0 restrictedIntegers :=
  (zeroIso restrictedIntegers).inv.hom invariantTwo

/-- The source cohomology class is nonzero independently of the induced map. -/
theorem classOne_ne_zero : classOne ≠ 0 := by
  intro h
  apply invariantOne_ne_zero
  have hinv := congrArg
    (fun z => (zeroIso CGCExamples.evenSequenceIntegers).hom.hom z) h
  simpa [classOne] using hinv

/-- The target cohomology class is nonzero independently of the induced map. -/
theorem classTwo_ne_zero : classTwo ≠ 0 := by
  intro h
  apply invariantTwo_ne_zero
  have hinv := congrArg (fun z => (zeroIso restrictedIntegers).hom.hom z) h
  simpa [classTwo] using hinv

/-- Despite the nonsurjective group map, coefficient doubling induces an
injection in degree zero and sends the class of `1` to the nonzero class of `2`. -/
theorem doubling_degreeZero_injective_nonzero :
    Function.Injective
        (map (X := CGCExamples.evenSequenceIntegers) collapseTwoGroup restrictedDoubling 0).hom ∧
      (map (X := CGCExamples.evenSequenceIntegers)
        collapseTwoGroup restrictedDoubling 0).hom classOne = classTwo ∧
      (map (X := CGCExamples.evenSequenceIntegers)
        collapseTwoGroup restrictedDoubling 0).hom classOne ≠ 0 := by
  have hclass :
      (map (X := CGCExamples.evenSequenceIntegers)
        collapseTwoGroup restrictedDoubling 0).hom classOne = classTwo := by
    have hsource := congrArg (fun q => q.hom invariantOne)
      (zeroIso CGCExamples.evenSequenceIntegers).inv_hom_id
    have htarget := congrArg
      (fun q => q.hom
        ((map (X := CGCExamples.evenSequenceIntegers)
          collapseTwoGroup restrictedDoubling 0).hom classOne))
      (zeroIso restrictedIntegers).hom_inv_id
    simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
      TopModuleCat.hom_id, ContinuousLinearMap.id_apply] at hsource htarget
    have hnat := congrArg
      (fun q => (zeroIso restrictedIntegers).inv.hom (q.hom classOne))
      (zeroIso_naturality_res (X := CGCExamples.evenSequenceIntegers)
        collapseTwoGroup restrictedDoubling)
    simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at hnat
    change (zeroIso CGCExamples.evenSequenceIntegers).hom.hom classOne =
      invariantOne at hsource
    rw [hsource, invariantsResMap_one, htarget] at hnat
    exact hnat.symm
  refine ⟨map_zero_injective collapseTwoGroup restrictedDoubling
    restrictedDoubling_injective, hclass, ?_⟩
  rw [hclass]
  exact classTwo_ne_zero

end CoefficientMonicityExamples
