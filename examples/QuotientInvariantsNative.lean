/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientInvariants
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ClusterPt

set_option warningAsError true

universe u v w

open CategoryTheory

namespace IncubatorTest.RepresentationTheory.Continuous.QuotientInvariants

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] (N : Subgroup G) [N.Normal]

private theorem generic_quotient_action (X : TopRep.{w} k G) (g : G)
    (x : TopRep.quotientInvariants N X) :
    ((TopRep.quotientInvariants N X).ρ (QuotientGroup.mk' N g) x).1 = X.ρ g x.1 :=
  TopRep.quotientInvariants_ρ_mk N X g x

private def generic_continuous_inclusion (X : TopRep.{w} k G) :
    TopRep.res (QuotientGroup.mk' N) (TopRep.quotientInvariants N X) ⟶ X :=
  TopRep.quotientInvariantsIncl N X

private theorem generic_inclusion_evaluation (X : TopRep.{w} k G)
    (x : TopRep.quotientInvariants N X) :
    (generic_continuous_inclusion N X).hom x = x.1 :=
  rfl

private def generic_coefficient_functor :
    TopRep.{w} k G ⥤ TopRep.{w} k (G ⧸ N) :=
  TopRep.quotientInvariantsFunctor (k := k) N

private theorem coefficient_map_evaluation {X Y : TopRep.{w} k G}
    (f : X ⟶ Y) (x : TopRep.quotientInvariants N X) :
    (((generic_coefficient_functor (k := k) N).map f) x).1 = f.hom x.1 :=
  TopRep.quotientInvariantsFunctor_map_val N f x

private theorem coefficient_map_on_fixed_vector {X Y : TopRep.{w} k G}
    (f : X ⟶ Y) (x : X) (hx : x ∈ (X.ρ.restrict N.subtype).invariants) :
    (((TopRep.quotientInvariantsFunctor (k := k) N).map f) ⟨x, hx⟩).1 = f.hom x :=
  TopRep.quotientInvariantsFunctor_map_val N f ⟨x, hx⟩

private theorem coefficient_inclusion_naturality {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    (TopRep.resFunctor (QuotientGroup.mk' N)).map
      ((TopRep.quotientInvariantsFunctor (k := k) N).map f) ≫
        TopRep.quotientInvariantsIncl N Y =
      TopRep.quotientInvariantsIncl N X ≫ f :=
  TopRep.quotientInvariantsIncl_naturality N f

private theorem arbitrary_normal_joint_continuity [TopologicalSpace G]
    [SeparatelyContinuousMul G] (X : TopRep.{w} k G) [TopRep.JointlyContinuous X] :
    TopRep.JointlyContinuous (TopRep.quotientInvariants N X) :=
  TopRep.jointlyContinuous_quotientInvariants N X

private theorem open_normal_joint_continuity [TopologicalSpace G]
    [SeparatelyContinuousMul G] (X : TopRep.{w} k G) (hN : IsOpen (N : Set G)) :
    TopRep.JointlyContinuous (TopRep.quotientInvariants N X) :=
  TopRep.jointlyContinuous_quotientInvariants_of_isOpen N X hN

private theorem inherited_discrete_carrier (X : TopRep.{w} k G)
    [DiscreteTopology X] :
    DiscreteTopology (TopRep.quotientInvariants N X) := by
  change DiscreteTopology (X.ρ.restrict N.subtype).invariants
  infer_instance

private theorem bottom_subgroup_action (X : TopRep.{w} k G) (g : G)
    (x : TopRep.quotientInvariants (⊥ : Subgroup G) X) :
    ((TopRep.quotientInvariants (⊥ : Subgroup G) X).ρ
      (QuotientGroup.mk' (⊥ : Subgroup G) g) x).1 = X.ρ g x.1 :=
  TopRep.quotientInvariants_ρ_mk (⊥ : Subgroup G) X g x

private theorem top_subgroup_trivial_action (X : TopRep.{w} k G) (g : G)
    (x : TopRep.quotientInvariants (⊤ : Subgroup G) X) :
    ((TopRep.quotientInvariants (⊤ : Subgroup G) X).ρ
      (QuotientGroup.mk' (⊤ : Subgroup G) g) x).1 = x.1 := by
  rw [TopRep.quotientInvariants_ρ_mk]
  exact x.2 ⟨g, Subgroup.mem_top g⟩

private def zero_carrier : TopRep.{0} k G :=
  .of (.ofMonoidHom (1 : G →* PUnit →L[k] PUnit))

private theorem zero_carrier_action (g : G) :
    (TopRep.quotientInvariants N (zero_carrier (k := k) (G := G))).ρ
      (QuotientGroup.mk' N g) (0 : TopRep.quotientInvariants N (zero_carrier (k := k) (G := G))) =
    0 := by
  exact map_zero _

private def real_trivial_representation : TopRep ℝ (Multiplicative ℤ) :=
  .of (.ofMonoidHom (1 : Multiplicative ℤ →* ℝ →L[ℝ] ℝ))

private theorem real_coefficients_nondiscrete : ¬ DiscreteTopology ℝ := by
  intro _
  exact not_isOpen_singleton (0 : ℝ) (isOpen_discrete _)

private theorem real_coefficients_open_normal_subgroup :
    TopRep.JointlyContinuous
      (TopRep.quotientInvariants (⊥ : Subgroup (Multiplicative ℤ))
        real_trivial_representation) :=
  TopRep.jointlyContinuous_quotientInvariants_of_isOpen
    (⊥ : Subgroup (Multiplicative ℤ)) real_trivial_representation (isOpen_discrete _)

end IncubatorTest.RepresentationTheory.Continuous.QuotientInvariants
