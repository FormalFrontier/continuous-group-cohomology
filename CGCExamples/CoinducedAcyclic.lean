/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CoinducedAcyclic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Instances.Int

/-!
# Two-element group with nonzero coinduced coefficients

The nontrivial finite group `Multiplicative (ZMod 2)` acts trivially on the
nonzero discrete integer module. A constant nonzero cochain demonstrates
diagonal insertion. The zeroth cohomology retains a nonzero class, so the
positive-degree boundary cannot be dropped.
-/

@[expose] public section

open CategoryTheory TopRep

namespace CGCExamples

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
local instance : IsTopologicalGroup (Multiplicative (ZMod 2)) := inferInstance
local instance : CompactSpace (Multiplicative (ZMod 2)) := inferInstance

/-- The discrete integers with the trivial action of the two-element group. -/
abbrev integerCoefficients : TopRep ℤ (Multiplicative (ZMod 2)) :=
  TopRep.of (ContRepresentation.trivial ℤ (Multiplicative (ZMod 2)) ℤ)

/-- The integer coefficient representation has a discrete carrier. -/
instance integerCoefficients_discrete : DiscreteTopology integerCoefficients := by
  change DiscreteTopology ℤ
  infer_instance

private theorem twoGroup_nontrivial :
    (Multiplicative.ofAdd (0 : ZMod 2) : Multiplicative (ZMod 2)) ≠
      Multiplicative.ofAdd (1 : ZMod 2) := by
  decide

private theorem integerCoefficients_nonzero : Nontrivial integerCoefficients := by
  change Nontrivial ℤ
  infer_instance

/-- The invariant homogeneous cochain that is constantly equal to `1`. -/
def constantOneCochain :
    (TopRep.homogeneousCochains (TopRep.coind₁ integerCoefficients)).X 1 := by
  refine ⟨ContinuousMap.const (Multiplicative (ZMod 2))
    (ContinuousMap.const (Multiplicative (ZMod 2))
      (ContinuousMap.const (Multiplicative (ZMod 2)) (1 : ℤ))), ?_⟩
  intro g
  ext h t s
  simp only [ContRepresentation.coind₁_apply_apply, ContinuousMap.const_apply]
  exact ContRepresentation.trivial_apply g (1 : ℤ)

/-- Inserting a variable into a nonzero constant cochain evaluates to `1`. -/
theorem twoGroup_insert_one (h t : Multiplicative (ZMod 2)) :
    (TopRep.resolutionEval (TopRep.coind₁ integerCoefficients) 1
      ((ContinuousCohomology.coind₁Insert integerCoefficients 0).hom
        constantOneCochain).1 (Fin.cons h (Fin.elim0))) t = (1 : ℤ) := by
  rw [ContinuousCohomology.coind₁Insert_apply]
  rfl

/-- The positive-degree coinduced-coefficient assertion specializes to a
two-element group and nonzero integral coefficients. -/
theorem twoGroup_positive_eq_zero
    (a : continuousCohomology 1 (TopRep.coind₁ integerCoefficients)) : a = 0 := by
  exact ContinuousCohomology.coind₁_positive_eq_zero integerCoefficients 0 a

/-- The degree-zero cohomology of these coinduced integer coefficients is
nonzero: the constant-one function is invariant. -/
theorem twoGroup_degree_zero_nonzero :
    ∃ a : continuousCohomology 0 (TopRep.coind₁ integerCoefficients), a ≠ 0 := by
  let v : (TopRep.coind₁ integerCoefficients).ρ.invariants :=
    ⟨ContinuousMap.const (Multiplicative (ZMod 2)) (1 : ℤ), by
      intro g
      ext t
      rw [ContRepresentation.coind₁_apply_apply]
      change (ContRepresentation.trivial ℤ (Multiplicative (ZMod 2)) ℤ) g (1 : ℤ) = 1
      exact ContRepresentation.trivial_apply g (1 : ℤ)⟩
  have hv : v ≠ 0 := by
    intro eq_zero
    have h := congrArg
      (fun f : C(Multiplicative (ZMod 2), ℤ) => f 1) (congrArg Subtype.val eq_zero)
    simp [v, integerCoefficients] at h
  refine ⟨(ContinuousCohomology.zeroIso (TopRep.coind₁ integerCoefficients)).inv.hom v,
    ?_⟩
  intro eq_zero
  apply hv
  have h := congrArg
    (fun a => (ContinuousCohomology.zeroIso (TopRep.coind₁ integerCoefficients)).hom.hom a)
    eq_zero
  simpa using h

end CGCExamples
