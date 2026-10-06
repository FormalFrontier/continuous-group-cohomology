/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.TopRepDiscrete
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Topology.Instances.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The sign action of integer units

The usual action of integer units on the discrete integers gives a jointly
continuous topological representation. The unit `-1` moves `1`, providing a
nontrivial sign action for direct-sum and tensor constructions.

This construction uses Mathlib's `Representation.ofDistribMulAction` and the
continuous-representation interface used by `TopRep`.
-/

@[expose] public section

namespace CGCExamples

/-- The integer units act on the discrete integers by their usual sign action. -/
def signedIntegers : TopRep ℤ ℤˣ := by
  let representation : Representation ℤ ℤˣ ℤ :=
    Representation.ofDistribMulAction ℤ ℤˣ ℤ
  exact .of <| .ofMonoidHom {
    toFun := fun g => ContinuousLinearMap.mk (representation g) (continuous_const_smul g)
    map_one' := by
      apply ContinuousLinearMap.ext
      intro n
      change representation 1 n = n
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro n
      change representation (g * h) n = representation g (representation h n)
      rw [map_mul]
      rfl
  }

/-- The carrier of the integer-unit sign representation is `ℤ`. -/
@[simp] theorem signedIntegers_V : signedIntegers.V = ℤ := rfl

/-- The integer carrier of the sign representation has the discrete topology. -/
instance signedIntegers_discrete : DiscreteTopology signedIntegers := by
  change DiscreteTopology ℤ
  infer_instance

/-- The action of an integer unit is multiplication by that unit on integers. -/
@[simp] theorem signedIntegers_ρ_apply (g : ℤˣ) (n : ℤ) :
    signedIntegers.ρ g n = g • n := by
  rfl

/-- The negative unit sends `1` to `-1` in the sign representation. -/
theorem signedIntegers_negative_one :
    signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) = (-1 : ℤ) := by
  simp
  rfl

/-- The negative unit acts nontrivially on the sign representation. -/
theorem signedIntegers_negative_one_not_fixed :
    signedIntegers.ρ (-1 : ℤˣ) (1 : ℤ) ≠ (1 : ℤ) := by
  rw [signedIntegers_negative_one]
  change (-1 : ℤ) ≠ 1
  norm_num

/-- The integer-unit sign action is jointly continuous. -/
instance signedIntegers_jointlyContinuous :
    TopRep.JointlyContinuous signedIntegers where
  continuous_action := by
    change Continuous (fun p : ℤˣ × ℤ => p.1 • p.2)
    exact continuous_smul

end CGCExamples
