/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CohomologyExactSequence
public import CGCExamples.CochainExactness
public import CGCExamples.TopRepDiscrete.SignAction

/-!
# A nonzero connecting phenomenon for the sign action

The two-element group `ℤˣ` acts by sign on both copies of the discrete integers
in `ℤ --×2→ ℤ → ZMod 2`; reduction modulo two has trivial action. The integer
invariants vanish, whereas `1` is a nonzero quotient invariant. Thus this
short exact sequence cannot be surjective on invariant coefficients, and its
degree-zero connecting class is nonzero by exactness. The coefficient-level
facts are proved independently of the long exact sequence.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3 and Exercise 1.
-/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology ContRepresentation

namespace CGCExamples

/-- The reduction-mod-two quotient of the integer sign representation. -/
abbrev signedQuotient : TopRep ℤ ℤˣ :=
  TopRep.of (ContRepresentation.trivial ℤ ℤˣ (ZMod 2))

instance : DiscreteTopology signedQuotient := by
  change DiscreteTopology (ZMod 2)
  infer_instance

private instance signedIntegers_noZeroSMulDivisors :
    NoZeroSMulDivisors ℤ signedIntegers := by
  change NoZeroSMulDivisors ℤ ℤ
  infer_instance

/-- Multiplication by two intertwines the integer sign action. -/
def signedInclusion : signedIntegers ⟶ signedIntegers :=
  TopRep.ofHom {
    toContinuousLinearMap := (2 : ℤ) • ContinuousLinearMap.id ℤ signedIntegers
    isIntertwining' := by
      intro g
      apply ContinuousLinearMap.ext
      intro x
      change (2 : ℤ) • (signedIntegers.ρ g x) =
        signedIntegers.ρ g ((2 : ℤ) • x)
      exact ((signedIntegers.ρ g).map_smul (2 : ℤ) x).symm
  }

/-- Mod-two reduction is equivariant from sign to trivial action. -/
def signedProjection : signedIntegers ⟶ signedQuotient :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.mk
      (Int.castAddHom (ZMod 2)).toIntLinearMap continuous_of_discreteTopology
    isIntertwining' := by
      intro g
      apply ContinuousLinearMap.ext
      intro x
      obtain rfl | rfl := Int.units_eq_one_or g
      · simp
      · change (((-1 : ℤˣ) • x : ℤ) : ZMod 2) = (x : ZMod 2)
        simp [Units.smul_def, ZMod.neg_eq_self_mod_two]
  }

@[simp] theorem signedInclusion_apply (x : ℤ) : signedInclusion x = 2 * x := rfl

@[simp] theorem signedProjection_apply (x : ℤ) :
    signedProjection x = (x : ZMod 2) := rfl

/-- The integer sign coefficient sequence is injective at the left. -/
theorem signedInclusion_injective : Function.Injective signedInclusion := by
  change Function.Injective (fun x : ℤ => 2 * x)
  intro x y h
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h

/-- The image of multiplication by two is the kernel of mod-two reduction. -/
theorem signedSequence_exact : Function.Exact signedInclusion signedProjection := by
  change Function.Exact (fun x : ℤ => 2 * x) (fun x : ℤ => (x : ZMod 2))
  exact evenSequence_exact

/-- The quotient map is surjective, although it has no integer-linear section. -/
theorem signedProjection_surjective : Function.Surjective signedProjection := by
  change Function.Surjective (fun x : ℤ => (x : ZMod 2))
  exact evenSequenceProjection_surjective

/-- The only integer fixed by the full sign action is zero. -/
theorem signedIntegers_invariant_eq_zero (x : signedIntegers.ρ.invariants) : x = 0 := by
  apply Subtype.ext
  have hx := x.2 (-1 : ℤˣ)
  change (-1 : ℤˣ) • (x.1 : ℤ) = (x.1 : ℤ) at hx
  have hx' : -(x.1 : signedIntegers) = x.1 := by
    simpa only [Units.smul_def, Units.val_neg, Units.val_one,
      neg_one_smul (R := ℤ)] using hx
  have htwo : (2 : ℤ) • (x.1 : signedIntegers) = 0 := by
    calc
      (2 : ℤ) • (x.1 : signedIntegers) = x.1 + x.1 := two_smul ℤ x.1
      _ = -x.1 + x.1 := congrArg (fun y : signedIntegers => y + x.1) hx'.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The class of one is a nonzero invariant in the mod-two quotient. -/
def signedQuotientInvariantOne : signedQuotient.ρ.invariants :=
  ⟨1, by intro g; simp⟩

theorem signedQuotientInvariantOne_ne_zero : signedQuotientInvariantOne ≠ 0 := by
  intro h
  have h' : (1 : ZMod 2) = 0 := congrArg Subtype.val h
  exact one_ne_zero h'

/-- The nonzero quotient invariant has no invariant integer lift, independently
of any long-exact-sequence theorem. -/
theorem signedQuotientInvariantOne_not_lifted :
    ¬∃ x : signedIntegers.ρ.invariants,
      (signedProjection.hom.mapInvariants x : signedQuotient.ρ.invariants) =
        signedQuotientInvariantOne := by
  rintro ⟨x, hx⟩
  rw [signedIntegers_invariant_eq_zero x, map_zero] at hx
  exact signedQuotientInvariantOne_ne_zero hx.symm

/-- At the negative unit, the differential of the integer lift `1` is
`-2`, the image under multiplication by two of `-1`. -/
theorem signedInclusion_boundary_at_negative_one :
    signedInclusion (-1 : ℤ) =
      signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) -
        signedIntegers.ρ (1 : ℤˣ) (1 : ℤ) := by
  rw [signedInclusion_apply, signedIntegers_negative_one, map_one]
  change (2 : ℤ) * -1 = (-1 : ℤ) - 1
  norm_num

/-- The lifted boundary coefficient `-1` is not principal: every sign-action
principal defect at the negative unit is an even integer. This independent
obstruction also detects why the lifted boundary cannot be principal. -/
theorem signedBoundary_not_principal :
    ¬∃ x : ℤ, signedIntegers.ρ (-1 : ℤˣ) x -
      signedIntegers.ρ (1 : ℤˣ) x = signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) := by
  rintro ⟨x, hx⟩
  rw [signedIntegers_ρ_apply, signedIntegers_ρ_apply,
    signedIntegers_negative_one] at hx
  simp only [Units.smul_def, Units.val_neg, Units.val_one,
    neg_one_smul, one_smul] at hx
  change -x - x = (-1 : ℤ) at hx
  omega

/-- The degree-zero connecting map sends the invariant quotient class `1`
to a nonzero degree-one cohomology class. The independent obstruction is
`signedBoundary_not_principal`. -/
theorem signedConnecting_one_ne_zero :
    (connecting signedInclusion signedProjection signedInclusion_injective
      signedSequence_exact signedProjection_surjective 0).hom
        ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne) ≠ 0 := by
  intro hzero
  have hmiddle (x : continuousCohomology 0 signedIntegers) : x = 0 := by
    have hz := signedIntegers_invariant_eq_zero ((zeroIso signedIntegers).hom x)
    have hz' := congrArg (fun y => (zeroIso signedIntegers).inv y) hz
    simpa only [Iso.hom_inv_id_apply, map_zero] using hz'
  obtain ⟨x, hx⟩ := ((exact_map_connecting signedInclusion signedProjection
    signedInclusion_injective signedSequence_exact signedProjection_surjective 0)
    ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne)).mp hzero
  have hsource : (zeroIso signedQuotient).inv.hom signedQuotientInvariantOne = 0 := by
    simpa [hmiddle x] using hx.symm
  apply signedQuotientInvariantOne_ne_zero
  have h := congrArg (fun y => (zeroIso signedQuotient).hom.hom y) hsource
  simpa using h

end CGCExamples
