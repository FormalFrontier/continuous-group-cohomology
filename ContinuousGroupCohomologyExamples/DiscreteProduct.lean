/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ContinuousGroupCohomology.DiscreteProduct

/-!
# A nonzero vector in the sign-product boundary example

One sign change moves the constant-one vector. The action on its chosen-discrete
carrier is not jointly continuous even though every fixed actor acts continuously;
the ordinary product topology, conversely, is not discrete.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SignProductExamples

open SignProduct

private theorem nonzero_vector_boundary (index : ℕ) :
    discreteOneVector ≠ (0 : DiscreteProduct) ∧
      (flip index) • discreteOneVector ≠ discreteOneVector ∧
      ¬ Continuous (fun pair : SignGroup × DiscreteProduct => pair.1 • pair.2) := by
  constructor
  · intro equality
    apply oneVector_ne_zero
    simpa only [discreteOneVector_equiv, discrete_zero] using
      congrArg discreteProductEquiv equality
  constructor
  · intro equality
    have moved : (discreteProductEquiv ((flip index) • discreteOneVector)) index = -1 := by
      simpa only [discrete_action_coordinate, discreteOneVector_equiv, oneVector_apply,
        product_action_coordinate] using flip_acts_nontrivially index
    rw [equality, discreteOneVector_equiv, oneVector_apply] at moved
    norm_num at moved
  · intro hcontinuous
    exact discrete_product_not_jointly_continuous ⟨hcontinuous⟩

private theorem ordinary_product_has_nonisolated_vector :
    ¬ ∀ vector : IntegerProduct, IsOpen ({vector} : Set IntegerProduct) := by
  intro isolated
  exact product_not_discrete (discreteTopology_iff_isOpen_singleton.mpr isolated)

private theorem fixed_operators_do_not_restore_joint_continuity (actor : SignGroup) :
    Continuous (fun vector : DiscreteProduct => actor • vector) ∧
      ¬ Continuous (fun pair : SignGroup × DiscreteProduct => pair.1 • pair.2) :=
  ⟨discrete_action_operator_continuous actor,
    fun hcontinuous => discrete_product_not_jointly_continuous ⟨hcontinuous⟩⟩

end SignProductExamples
