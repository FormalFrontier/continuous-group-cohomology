/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CoinductionExactness
public import CGCExamples.TopRepDiscrete.SignAction
public import CGCExamples.CochainExactness
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Signed discrete coefficients under continuous coinduction

Doubling the integers with the sign action, followed by reduction modulo two
with the trivial action, is a nonsplit short exact row. Nonconstant continuous
functions on the two-element unit group exhibit a quotient lift and a lift from
the middle kernel without using coinduction exactness.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3, Proposition (1.3.6)(i).
* Mathlib's continuous coinduction and the integer-unit sign action.
-/

@[expose] public section

open CategoryTheory TopRep ContRepresentation

namespace CGCExamples

private instance : CompactSpace ℤˣ := inferInstance
private instance : DiscreteTopology ℤˣ := inferInstance

/-- The trivial action of integer units on the discrete residue ring. -/
private abbrev signedResidues : TopRep ℤ ℤˣ :=
  TopRep.of (ContRepresentation.trivial ℤ ℤˣ (ZMod 2))

private instance : DiscreteTopology signedResidues := by
  change DiscreteTopology (ZMod 2)
  infer_instance

private instance : TopRep.JointlyContinuous signedResidues where
  continuous_action := by
    change Continuous (fun point : ℤˣ × ZMod 2 => point.2)
    exact continuous_snd

/-- The sign-equivariant doubling map on discrete integers. -/
private def signedDouble : signedIntegers ⟶ signedIntegers :=
  (2 : ℤ) • 𝟙 signedIntegers

/-- Reduction modulo two kills the sign of an integer. -/
private def signedReduction : signedIntegers ⟶ signedResidues :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.mk
      (Int.castAddHom (ZMod 2)).toIntLinearMap continuous_of_discreteTopology
    isIntertwining' := by
      intro g
      apply ContinuousLinearMap.ext
      intro n
      obtain rfl | rfl := Int.units_eq_one_or g
      · simp
      · change (((-1 : ℤˣ) • n : ℤ) : ZMod 2) = (n : ZMod 2)
        simp
  }

@[simp] private theorem signedDouble_apply (n : ℤ) : signedDouble n = 2 * n := by
  rfl

@[simp] private theorem signedReduction_apply (n : ℤ) :
    signedReduction n = (n : ZMod 2) := rfl

private theorem double_eq_evenSequenceInclusion :
    (fun n : ℤ => (2 : ℤ) * n) = (evenSequenceInclusion : ℤ → ℤ) :=
  funext fun n => (evenSequenceInclusion_apply n).symm

private theorem reduction_eq_evenSequenceProjection :
    (fun n : ℤ => (n : ZMod 2)) = (evenSequenceProjection : ℤ → ZMod 2) :=
  funext fun n => (evenSequenceProjection_apply n).symm

private theorem signedDouble_injective : Function.Injective signedDouble := by
  change Function.Injective (fun n : ℤ => (2 : ℤ) * n)
  rw [double_eq_evenSequenceInclusion]
  exact evenSequenceInclusion_injective

private theorem signedRow_exact : Function.Exact signedDouble signedReduction := by
  change Function.Exact (fun n : ℤ => (2 : ℤ) * n) (fun n : ℤ => (n : ZMod 2))
  rw [double_eq_evenSequenceInclusion, reduction_eq_evenSequenceProjection]
  exact evenSequence_exact

private theorem signedReduction_surjective : Function.Surjective signedReduction := by
  intro b
  exact evenSequenceProjection_surjective b

private theorem signedRow_no_additive_section :
    ¬∃ s : signedResidues →ₗ[ℤ] signedIntegers,
      ∀ c, signedReduction (s c) = c := by
  exact evenSequence_no_linear_section

private theorem signedRow_no_equivariant_set_section :
    ¬∃ s : ZMod 2 → ℤ,
      (∀ c, signedReduction (s c) = c) ∧
      (∀ g : ℤˣ, ∀ c : ZMod 2, s c = g • s c) := by
  rintro ⟨selected, hselected, hequiv⟩
  have hfixed : selected 1 = -selected 1 := by
    simpa [Units.smul_def] using hequiv (-1) 1
  have hzero : selected 1 = 0 := by omega
  have hone := hselected 1
  rw [hzero, signedReduction_apply] at hone
  norm_num at hone

/-- The quotient function has values `(1,0)` at `(1,-1)`. -/
private def residuePair : C(ℤˣ, ZMod 2) :=
  ⟨fun g => if g = 1 then 1 else 0, continuous_of_discreteTopology⟩

/-- The integral lift has values `(1,0)` at `(1,-1)`. -/
private def integerPair : C(ℤˣ, ℤ) :=
  ⟨fun g => if g = 1 then 1 else 0, continuous_of_discreteTopology⟩

/-- A middle-space kernel element has values `(2,0)` at `(1,-1)`. -/
private def evenPair : C(ℤˣ, ℤ) :=
  ⟨fun g => if g = 1 then 2 else 0, continuous_of_discreteTopology⟩

private theorem residuePair_values : residuePair 1 = 1 ∧ residuePair (-1) = 0 := by
  simp [residuePair]

private theorem integerPair_values : integerPair 1 = 1 ∧ integerPair (-1) = 0 := by
  simp [integerPair]

private theorem evenPair_values : evenPair 1 = 2 ∧ evenPair (-1) = 0 := by
  simp [evenPair]

private theorem residuePair_nonconstant : residuePair 1 ≠ residuePair (-1) := by
  rw [residuePair_values.1, residuePair_values.2]
  decide

private theorem integerPair_nonconstant : integerPair 1 ≠ integerPair (-1) := by
  rw [integerPair_values.1, integerPair_values.2]
  decide

private theorem evenPair_nonconstant : evenPair 1 ≠ evenPair (-1) := by
  rw [evenPair_values.1, evenPair_values.2]
  decide

private theorem signedCoinduction_twisted_action (F : TopRep.coind₁ signedIntegers) :
    signedIntegers.ρ.coind₁ (-1 : ℤˣ) F 1 = signedIntegers.ρ (-1) (F (-1)) ∧
      signedIntegers.ρ.coind₁ (-1 : ℤˣ) F (-1) = signedIntegers.ρ (-1) (F 1) := by
  constructor
  · simpa using (ContRepresentation.coind₁_apply_apply signedIntegers.ρ (-1) F 1)
  · simpa using (ContRepresentation.coind₁_apply_apply signedIntegers.ρ (-1) F (-1))

private theorem residuePair_twisted_action :
    signedResidues.ρ.coind₁ (-1 : ℤˣ) residuePair 1 = 0 ∧
      signedResidues.ρ.coind₁ (-1 : ℤˣ) residuePair (-1) = 1 := by
  constructor
  · rw [ContRepresentation.coind₁_apply_apply]
    simpa using residuePair_values.2
  · rw [ContRepresentation.coind₁_apply_apply]
    simpa using residuePair_values.1

private theorem signedPair_quotient_lift :
    ((TopRep.coind₁Functor ℤ ℤˣ).map signedReduction).hom integerPair = residuePair := by
  ext g
  change signedReduction (integerPair g) = residuePair g
  change ((if g = 1 then (1 : ℤ) else 0 : ℤ) : ZMod 2) =
    (if g = 1 then 1 else 0 : ZMod 2)
  by_cases hg : g = 1 <;> simp [hg]

private theorem signedPair_middle_lift :
    ((TopRep.coind₁Functor ℤ ℤˣ).map signedDouble).hom integerPair = evenPair := by
  ext g
  change signedDouble (integerPair g) = evenPair g
  change (2 : ℤ) * (if g = 1 then 1 else 0) =
    (if g = 1 then 2 else 0 : ℤ)
  by_cases hg : g = 1 <;> simp [hg]

private theorem signedPair_middle_kernel :
    ((TopRep.coind₁Functor ℤ ℤˣ).map signedReduction).hom evenPair = 0 := by
  ext g
  change signedReduction (evenPair g) = (0 : ZMod 2)
  rw [signedReduction_apply]
  by_cases hg : g = 1 <;> simp [evenPair, hg, show (2 : ZMod 2) = 0 by decide]

/-- An empty domain makes postcomposition injective even for a noninjective
coefficient map; no converse without a nonempty domain is valid. -/
private theorem emptyDomain_postcomp_injective [TopologicalSpace PEmpty] :
    Function.Injective
      (ContinuousMap.comp (ContinuousMap.const ℤ (0 : ℤ)) :
        C(PEmpty, ℤ) → C(PEmpty, ℤ)) := by
  intro F H _
  ext x
  exact x.elim

private theorem emptyDomain_coefficient_not_injective :
    ¬ Function.Injective (ContinuousMap.const ℤ (0 : ℤ)) := by
  intro h
  have hone : (0 : ℤ) = 1 := h rfl
  norm_num at hone

/-- This postcomposition-exactness client needs no discrete topology on its
source coefficient space. -/
private theorem nondiscreteSource_postcomp_exact :
    Function.Exact
      (ContinuousMap.comp (ContinuousMap.const ℝ (0 : ℤ)) :
        C(ℤˣ, ℝ) → C(ℤˣ, ℤ))
      (ContinuousMap.comp (ContinuousMap.id ℤ) :
        C(ℤˣ, ℤ) → C(ℤˣ, ℤ)) := by
  apply ContinuousMap.postcomp_exact
  intro n
  simp

/-- This postcomposition-surjectivity client needs no discrete topology on the
domain of its coefficient surjection. -/
private theorem nondiscreteMiddle_postcomp_surjective :
    Function.Surjective
      (ContinuousMap.comp
        (⟨Prod.snd, continuous_snd⟩ : C(ℝ × ZMod 2, ZMod 2)) :
          C(ℤˣ, ℝ × ZMod 2) → C(ℤˣ, ZMod 2)) := by
  apply ContinuousMap.postcomp_surjective
  intro residue
  exact ⟨(0, residue), rfl⟩

/-- The signed, nonsplit two-element row instantiates coinduction short exactness. -/
private theorem signedRow_coind₁_shortExact :
    Function.Injective (((TopRep.coind₁Functor ℤ ℤˣ).map signedDouble).hom) ∧
      Function.Exact (((TopRep.coind₁Functor ℤ ℤˣ).map signedDouble).hom)
        (((TopRep.coind₁Functor ℤ ℤˣ).map signedReduction).hom) ∧
      Function.Surjective (((TopRep.coind₁Functor ℤ ℤˣ).map signedReduction).hom) :=
  TopRep.coind₁Functor_shortExact signedDouble signedReduction
    signedDouble_injective signedRow_exact signedReduction_surjective

end CGCExamples
