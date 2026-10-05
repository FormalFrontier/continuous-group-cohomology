/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.TransferInstance
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Order
public import Mathlib.Topology.WithTopology

/-!
# A sign action on an infinite product of discrete modules

The product of countably many integer-unit groups acts by signs on the
coordinatewise product of copies of `ℤ`. With the ordinary product topology,
the action is jointly continuous, but the integer product is not discrete.
With the *separate* discrete topology on the same algebraic product, each
actor acts continuously, but the action is not jointly continuous.
Integer units carry Mathlib's induced topology, which is discrete here.

The source discusses the possibility that an infinite product of discrete
modules is not discrete without specifying a topology on that product. These
two explicit topology choices give an existential example, not an assertion
about every infinite product or about a categorical product.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1.1 (product observation).
* Mathlib's Pi actions, topology of units, `WithDiscreteTopology`,
  `isOpen_pi_iff`, and `stabilizer_isOpen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

/-- The countable product of the finite, discrete integer-unit groups. -/
abbrev SignGroup := ℕ → ℤˣ

/-- The integer sequences with their ordinary product topology. -/
abbrev IntegerProduct := ℕ → ℤ

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

/-- The sign product is a compact Hausdorff totally disconnected topological group. -/
theorem signGroup_topological :
    IsTopologicalGroup SignGroup ∧ CompactSpace SignGroup ∧
      T2Space SignGroup ∧ TotallyDisconnectedSpace SignGroup := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The action of the sign at one coordinate on the corresponding integer. -/
def coordinateAction (index : ℕ) (actor : SignGroup) (value : ℤ) : ℤ :=
  (actor index) • value

@[simp] theorem coordinateAction_eq_smul (index : ℕ) (actor : SignGroup) (value : ℤ) :
    coordinateAction index actor value = (actor index) • value := rfl

/-- Each discrete integer coordinate has a jointly continuous sign action. -/
theorem coordinateAction_continuous (index : ℕ) :
    Continuous (fun pair : SignGroup × ℤ =>
      coordinateAction index pair.1 pair.2) := by
  exact ((continuous_apply index).comp continuous_fst).smul continuous_snd

/-- The ordinary product action is the coordinatewise sign action. -/
@[simp] theorem product_action_coordinate (actor : SignGroup)
    (vector : IntegerProduct) (index : ℕ) :
    (actor • vector) index = coordinateAction index actor (vector index) := by
  rfl

/-- The action on the ordinary topological product is jointly continuous. -/
theorem product_action_continuous : ContinuousSMul SignGroup IntegerProduct :=
  inferInstance

/-- The constant-one vector in the ordinary product. -/
def oneVector : IntegerProduct := fun _ => 1

@[simp] theorem oneVector_apply (index : ℕ) : oneVector index = 1 := rfl

/-- The actor that changes just the sign at one index. -/
def flip (index : ℕ) : SignGroup :=
  Function.update (1 : SignGroup) index (-1)

@[simp] theorem flip_apply_self (index : ℕ) : flip index index = -1 := by
  simp [flip]

/-- The constant-one vector witnesses nontriviality of the integer product. -/
theorem oneVector_ne_zero : oneVector ≠ (0 : IntegerProduct) := by
  intro equality
  have atZero := congrFun equality 0
  norm_num [oneVector] at atZero

/-- Flipping any coordinate moves the constant-one vector. -/
theorem flip_acts_nontrivially (index : ℕ) :
    ((flip index) • oneVector) index = -1 := by
  simp [flip, oneVector, Units.smul_def]

/-- A separately chosen discrete topology on the algebraic integer product. -/
def DiscreteProduct : Type := WithDiscreteTopology IntegerProduct

instance : TopologicalSpace DiscreteProduct := ⊥

instance : DiscreteTopology DiscreteProduct := ⟨rfl⟩

/-- Forget the chosen discrete topology, retaining the underlying sequence. -/
def discreteProductEquiv : DiscreteProduct ≃ IntegerProduct :=
  WithTopology.equiv IntegerProduct ⊥

instance : AddCommGroup DiscreteProduct :=
  discreteProductEquiv.addCommGroup

/-- The additive equivalence transporting the coordinatewise sign action. -/
def discreteProductAddEquiv : DiscreteProduct ≃+ IntegerProduct where
  __ := discreteProductEquiv
  map_add' _ _ := rfl

@[simp] theorem discreteProductAddEquiv_apply (vector : DiscreteProduct) :
    discreteProductAddEquiv vector = discreteProductEquiv vector := rfl

instance : DistribMulAction SignGroup DiscreteProduct :=
  discreteProductAddEquiv.distribMulAction SignGroup

@[simp] theorem discrete_zero : discreteProductEquiv (0 : DiscreteProduct) = 0 :=
  discreteProductAddEquiv.map_zero

@[simp] theorem discrete_add (left right : DiscreteProduct) :
    discreteProductEquiv (left + right) =
      discreteProductEquiv left + discreteProductEquiv right :=
  discreteProductAddEquiv.map_add left right

@[simp] theorem discrete_zsmul (scalar : ℤ) (vector : DiscreteProduct) :
    discreteProductEquiv (scalar • vector) = scalar • discreteProductEquiv vector :=
  discreteProductAddEquiv.toAddMonoidHom.map_zsmul scalar vector

/-- The constant-one vector in the separately discrete product. -/
def discreteOneVector : DiscreteProduct :=
  discreteProductEquiv.symm oneVector

@[simp] theorem discreteOneVector_equiv :
    discreteProductEquiv discreteOneVector = oneVector :=
  discreteProductEquiv.apply_symm_apply oneVector

/-- Transporting the sign action preserves its underlying product action. -/
@[simp] theorem discrete_action_map (actor : SignGroup) (vector : DiscreteProduct) :
    discreteProductAddEquiv (actor • vector) =
      actor • discreteProductAddEquiv vector := by
  simp only [Equiv.smul_def]
  rfl

/-- On the discrete copy, the action remains coordinatewise. -/
theorem discrete_action_coordinate (actor : SignGroup)
    (vector : DiscreteProduct) (index : ℕ) :
    (discreteProductEquiv (actor • vector)) index =
      coordinateAction index actor ((discreteProductEquiv vector) index) := by
  exact congrFun (discrete_action_map actor vector) index

private theorem discrete_action_zero (actor : SignGroup) :
    actor • (0 : DiscreteProduct) = 0 :=
  smul_zero actor

private theorem discrete_action_add (actor : SignGroup)
    (left right : DiscreteProduct) :
    actor • (left + right) = actor • left + actor • right :=
  smul_add actor left right

private theorem discrete_action_zsmul (actor : SignGroup)
    (scalar : ℤ) (vector : DiscreteProduct) :
    actor • (scalar • vector) = scalar • (actor • vector) :=
  smul_comm actor scalar vector

/-- Each fixed actor acts continuously on the discrete product. -/
theorem discrete_action_operator_continuous (actor : SignGroup) :
    Continuous (fun vector : DiscreteProduct => actor • vector) :=
  continuous_of_discreteTopology

private theorem pi_singleton_not_open {α : Type*} [TopologicalSpace α] [Nontrivial α]
    (vector : ℕ → α) : ¬ IsOpen ({vector} : Set (ℕ → α)) := by
  intro hopen
  obtain ⟨indices, neighborhoods, hmem, hsubset⟩ :=
    isOpen_pi_iff.mp hopen vector (Set.mem_singleton vector)
  have exists_free : ∃ index : ℕ, index ∉ indices := by
    by_contra h
    have hall : ∀ index : ℕ, index ∈ indices := by
      intro index
      by_contra hindex
      exact h ⟨index, hindex⟩
    exact Set.infinite_univ (indices.finite_toSet.subset (by
      intro index _
      exact hall index))
  obtain ⟨index, hindex⟩ := exists_free
  obtain ⟨value, hvalue⟩ := exists_ne (vector index)
  let altered := Function.update vector index value
  have haltered : altered ∈ (indices : Set ℕ).pi neighborhoods := by
    intro coordinate hcoordinate
    have hneq : coordinate ≠ index := by
      intro equality
      exact hindex (equality ▸ hcoordinate)
    simpa [altered, Function.update_of_ne hneq] using (hmem coordinate hcoordinate).2
  have heq : altered = vector := Set.mem_singleton_iff.mp (hsubset haltered)
  exact hvalue (by simpa [altered] using congrFun heq index)

/-- The constant-one vector in the discrete copy has trivial sign stabilizer. -/
theorem fixed_one_stabilizer :
    (MulAction.stabilizer SignGroup discreteOneVector : Set SignGroup) = {1} := by
  ext actor
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_singleton_iff]
  constructor
  · intro fixed
    funext index
    have hcoord : (actor index) • (1 : ℤ) = 1 := by
      have h := congrArg (fun vector : DiscreteProduct => (discreteProductEquiv vector) index) fixed
      simpa [discrete_action_coordinate, coordinateAction, discreteOneVector, oneVector] using h
    exact Units.ext (by simpa [Units.smul_def] using hcoord)
  · intro heq
    subst actor
    exact one_smul SignGroup discreteOneVector

/-- The identity is not isolated in the infinite product of sign groups. -/
theorem singleton_not_open :
    ¬ IsOpen ({1} : Set SignGroup) := by
  have : Nontrivial ℤˣ := ⟨⟨1, -1, by
    intro heq
    have hval := congrArg (fun unit : ℤˣ => (unit : ℤ)) heq
    norm_num at hval⟩⟩
  exact pi_singleton_not_open (1 : SignGroup)

/-- The ordinary product of discrete integer coordinates is not discrete.
The product observation of Neukirch--Schmidt--Wingberg does not choose this topology. -/
theorem product_not_discrete : ¬ DiscreteTopology IntegerProduct := by
  intro hdiscrete
  let : DiscreteTopology IntegerProduct := hdiscrete
  exact pi_singleton_not_open (0 : IntegerProduct) (isOpen_discrete _)

/-- The coordinatewise action on the *separately discrete* integer product is not
jointly continuous. Each fixed actor still acts continuously; the choice of
topology is not specified in the product observation of Neukirch--Schmidt--Wingberg. -/
theorem discrete_product_not_jointly_continuous :
    ¬ ContinuousSMul SignGroup DiscreteProduct := by
  intro hcontinuous
  let : ContinuousSMul SignGroup DiscreteProduct := hcontinuous
  apply singleton_not_open
  simpa only [fixed_one_stabilizer] using stabilizer_isOpen SignGroup discreteOneVector

end

end SignProduct
