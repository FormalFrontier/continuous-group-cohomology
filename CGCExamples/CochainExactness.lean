/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CochainExactness
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Data.ZMod.Basic

/-!
# Nonsplit discrete coefficients for homogeneous cochains

The two-element group acts trivially on the sequence
`ℤ ⟶ ℤ ⟶ ZMod 2`, with first map multiplication by two and second map
reduction modulo two. The quotient is nonzero, the coefficient sequence is
exact, and it has no integer-linear section. Concrete cochains in degrees
zero and one exercise the existing induced maps without using cochain
exactness or surjectivity.
-/

@[expose] public section

open CategoryTheory ContRepresentation TopRep

namespace CGCExamples

/-- The two-element group acting on the integer coefficient sequence. -/
abbrev TwoGroup := Multiplicative (ZMod 2)

local instance : TopologicalSpace TwoGroup := ⊥
local instance : DiscreteTopology TwoGroup := ⟨rfl⟩
local instance : IsTopologicalGroup TwoGroup := inferInstance
local instance : CompactSpace TwoGroup := inferInstance

/-- The acting group has two distinct elements. -/
theorem evenSequence_group_nontrivial :
    (Multiplicative.ofAdd (0 : ZMod 2) : TwoGroup) ≠
      Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

/-- The integers with the discrete topology and trivial two-element action. -/
abbrev evenSequenceIntegers : TopRep ℤ TwoGroup :=
  TopRep.of (ContRepresentation.trivial ℤ TwoGroup ℤ)

/-- The mod-two integers with their discrete topology and trivial action. -/
abbrev evenSequenceQuotient : TopRep ℤ TwoGroup :=
  TopRep.of (ContRepresentation.trivial ℤ TwoGroup (ZMod 2))

instance : DiscreteTopology evenSequenceIntegers := by
  change DiscreteTopology ℤ
  infer_instance

instance : DiscreteTopology evenSequenceQuotient := by
  change DiscreteTopology (ZMod 2)
  infer_instance

instance : TopRep.JointlyContinuous evenSequenceIntegers where
  continuous_action := by
    change Continuous (fun p : TwoGroup × ℤ => p.2)
    exact continuous_snd

/-- Multiplication by two on the integer coefficient representation. -/
def evenSequenceInclusion : evenSequenceIntegers ⟶ evenSequenceIntegers :=
  TopRep.ofHom {
    toContinuousLinearMap := (2 : ℤ) • ContinuousLinearMap.id ℤ ℤ
    isIntertwining' := by
      intro g
      ext
      simp
  }

/-- Reduction modulo two on the integer coefficient representation. -/
def evenSequenceProjection : evenSequenceIntegers ⟶ evenSequenceQuotient :=
  TopRep.ofHom {
    toContinuousLinearMap := ContinuousLinearMap.mk
      (Int.castAddHom (ZMod 2)).toIntLinearMap continuous_of_discreteTopology
    isIntertwining' := by
      intro g
      ext
      simp
  }

@[simp] theorem evenSequenceInclusion_apply (x : ℤ) :
    evenSequenceInclusion x = 2 * x := by
  rfl

@[simp] theorem evenSequenceProjection_apply (x : ℤ) :
    evenSequenceProjection x = (x : ZMod 2) := rfl

/-- Multiplication by two is injective on the integers. -/
theorem evenSequenceInclusion_injective :
    Function.Injective evenSequenceInclusion := by
  intro x y h
  change (2 : ℤ) * x = 2 * y at h
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h

/-- The even integers are exactly the kernel of reduction modulo two. -/
theorem evenSequence_exact :
    Function.Exact evenSequenceInclusion evenSequenceProjection := by
  intro x
  change ((x : ZMod 2) = 0) ↔ ∃ y : ℤ, 2 * y = x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    simp [show (2 : ZMod 2) = 0 by decide]

/-- Reduction modulo two is surjective. -/
theorem evenSequenceProjection_surjective :
    Function.Surjective evenSequenceProjection := by
  intro x
  obtain ⟨y, rfl⟩ := ZMod.intCast_surjective (n := 2) (x : ZMod 2)
  exact ⟨y, rfl⟩

/-- The quotient element `1` is nonzero. -/
theorem evenSequenceQuotient_one_ne_zero :
    (1 : evenSequenceQuotient) ≠ 0 := by
  decide

/-- Reduction modulo two has no section linear over the integers. -/
theorem evenSequence_no_linear_section :
    ¬∃ s : evenSequenceQuotient →ₗ[ℤ] evenSequenceIntegers,
      ∀ x, evenSequenceProjection (s x) = x := by
  rintro ⟨s, hs⟩
  have htwo : (2 : ℤ) • s (1 : evenSequenceQuotient) = 0 := by
    rw [← map_smul, show (2 : ℤ) • (1 : evenSequenceQuotient) = 0 by decide, map_zero]
  have hone : s (1 : evenSequenceQuotient) = 0 := by
    change 2 * s (1 : evenSequenceQuotient) = 0 at htwo
    exact (mul_eq_zero.mp htwo).resolve_left (by decide)
  apply evenSequenceQuotient_one_ne_zero
  calc
    (1 : evenSequenceQuotient) = evenSequenceProjection (s 1) := (hs 1).symm
    _ = 0 := by rw [hone]; simp

/-- The constant-one invariant homogeneous cochain in degree zero. -/
def evenSequenceDegreeZero : (homogeneousCochains evenSequenceIntegers).X 0 := by
  refine ⟨ContinuousMap.const TwoGroup (1 : ℤ), ?_⟩
  intro g
  ext t
  simp only [coind₁_apply_apply, ContinuousMap.const_apply]
  exact ContRepresentation.trivial_apply g (1 : ℤ)

/-- The constant-one invariant homogeneous cochain in degree one. -/
def evenSequenceDegreeOne : (homogeneousCochains evenSequenceIntegers).X 1 := by
  refine ⟨ContinuousMap.const TwoGroup (ContinuousMap.const TwoGroup (1 : ℤ)), ?_⟩
  intro g
  ext t s
  simp only [coind₁_apply_apply, ContinuousMap.const_apply]
  exact ContRepresentation.trivial_apply g (1 : ℤ)

/-- Degree-zero reduction sends a concrete cochain to the nonzero residue. -/
theorem evenSequence_degreeZero_projection :
    resolutionEval evenSequenceQuotient 1
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id TwoGroup)
        evenSequenceProjection).f 0 evenSequenceDegreeZero).1
      (Fin.cons 1 (Fin.elim0)) = (1 : ZMod 2) := by
  rw [ContinuousCohomology.cochainsMap_resolutionEval]
  rfl

/-- Degree-one reduction sends a concrete cochain to the nonzero residue. -/
theorem evenSequence_degreeOne_projection :
    resolutionEval evenSequenceQuotient 2
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id TwoGroup)
        evenSequenceProjection).f 1 evenSequenceDegreeOne).1
      (Fin.cons 1 (Fin.cons 1 (Fin.elim0))) = (1 : ZMod 2) := by
  rw [ContinuousCohomology.cochainsMap_resolutionEval]
  rfl

/-- Degree-zero multiplication by two is visible after cochain evaluation. -/
theorem evenSequence_degreeZero_inclusion :
    resolutionEval evenSequenceIntegers 1
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id TwoGroup)
        evenSequenceInclusion).f 0 evenSequenceDegreeZero).1
      (Fin.cons 1 (Fin.elim0)) = (2 : ℤ) := by
  rw [ContinuousCohomology.cochainsMap_resolutionEval]
  rfl

/-- Degree-one multiplication by two is visible after cochain evaluation. -/
theorem evenSequence_degreeOne_inclusion :
    resolutionEval evenSequenceIntegers 2
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id TwoGroup)
        evenSequenceInclusion).f 1 evenSequenceDegreeOne).1
      (Fin.cons 1 (Fin.cons 1 (Fin.elim0))) = (2 : ℤ) := by
  rw [ContinuousCohomology.cochainsMap_resolutionEval]
  rfl

/-- The concrete nonsplit coefficient sequence specializes the compact-group
short exactness assertion at cochain degree zero. -/
theorem evenSequence_degreeZero_shortExact :
    Function.Injective
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceInclusion).f 0) ∧
      Function.Exact
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceInclusion).f 0)
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceProjection).f 0) ∧
      Function.Surjective
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceProjection).f 0) :=
  ContinuousCohomology.cochainsMap_shortExact_of_compact
    evenSequenceInclusion evenSequenceProjection
    evenSequenceInclusion_injective evenSequence_exact
    evenSequenceProjection_surjective 0

/-- The same nonsplit sequence also specializes at the positive degree one. -/
theorem evenSequence_degreeOne_shortExact :
    Function.Injective
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceInclusion).f 1) ∧
      Function.Exact
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceInclusion).f 1)
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceProjection).f 1) ∧
      Function.Surjective
        ((ContinuousCohomology.cochainsMap (X := evenSequenceIntegers)
          (ContinuousMonoidHom.id TwoGroup)
          evenSequenceProjection).f 1) :=
  ContinuousCohomology.cochainsMap_shortExact_of_compact
    evenSequenceInclusion evenSequenceProjection
    evenSequenceInclusion_injective evenSequence_exact
    evenSequenceProjection_surjective 1

end CGCExamples
