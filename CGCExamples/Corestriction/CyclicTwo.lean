/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Corestriction
public import Mathlib.Data.ZMod.Basic

/-!
# Degree-one corestriction for a cyclic group

The cyclic group of order two acts trivially on the integers modulo two. The
corestriction computation square, independence of a transversal, and the identity
for the whole subgroup can all be used on this representation.
-/

@[expose] public section

open CategoryTheory

namespace ContinuousCohomology.Examples

open CorestrictionTransversal

/-- The discrete topology on the coefficient group of order two. -/
local instance cyclicTwoCoefficientsTopology : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
/-- The discrete topology on the multiplicative cyclic group of order two. -/
local instance cyclicTwoGroupTopology : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
local instance : Finite (Multiplicative (ZMod 2)) := inferInstanceAs (Finite (ZMod 2))

/-- The trivial representation of the discrete cyclic group of order two
on the discrete integers modulo two. -/
noncomputable def trivialCyclicTwo : TopRep ℤ (Multiplicative (ZMod 2)) where
  V := TopModuleCat.of ℤ (ZMod 2)
  ρ :=
    { toMonoidHom :=
        { toFun := fun _ => ContinuousLinearMap.id ℤ _
          map_one' := rfl
          map_mul' := fun _ _ => rfl } }

instance : TopRep.JointlyContinuous trivialCyclicTwo := by
  constructor
  exact continuous_snd

example : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
  intro h
  have h' : (0 : ZMod 2) = 1 := congrArg Multiplicative.toAdd h
  exact (by decide : (0 : ZMod 2) ≠ 1) h'

example : (0 : ZMod 2) ≠ 1 := by decide

example :
    (degreeOneIso (TopRep.res (⊤ : OpenSubgroup (Multiplicative (ZMod 2))).subtype
        trivialCyclicTwo)).hom ≫
      corestrictionOneOfRightTransversal trivialCyclicTwo ⊤ default =
    TopModuleCat.ofHom (transferQuotient trivialCyclicTwo ⊤ default) ≫
      (degreeOneIso trivialCyclicTwo).hom :=
  corestrictionOneOfRightTransversal_spec trivialCyclicTwo ⊤ default

example (S : (⊤ : OpenSubgroup (Multiplicative (ZMod 2))).toSubgroup.RightTransversal) :
    corestrictionOneOfRightTransversal trivialCyclicTwo ⊤ default =
      corestrictionOneOfRightTransversal trivialCyclicTwo ⊤ S :=
  corestrictionOneOfRightTransversal_eq trivialCyclicTwo ⊤ default S

example :
    map (openSubgroupInclusion (⊤ : OpenSubgroup (Multiplicative (ZMod 2))))
        (restrictionCoeffHom trivialCyclicTwo ⊤) 1 ≫
      corestrictionOneOfRightTransversal trivialCyclicTwo ⊤ default =
    𝟙 (continuousCohomology 1 trivialCyclicTwo) := by
  have h := restriction_corestrictionOne trivialCyclicTwo
    (⊤ : OpenSubgroup (Multiplicative (ZMod 2))) default
  rw [corestrictionOne_eq_withTransversal trivialCyclicTwo
      (⊤ : OpenSubgroup (Multiplicative (ZMod 2))) default,
    corestrictionOneWithTransversal_eq_ofRightTransversal] at h
  simpa using h

end ContinuousCohomology.Examples
