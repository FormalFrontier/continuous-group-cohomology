/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageResolution
public import CGCExamples.TopRepDiscrete.SignAction
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units
import ContinuousGroupCohomology.Algebra.Category.ModuleCat.Topology.HomologyBoundary
import ContinuousGroupCohomology.FiniteStageBoundary
import ContinuousGroupCohomology.FiniteStageColimit
import ContinuousGroupCohomology.QuotientInvariants
import ContinuousGroupCohomology.ResolutionImage
import ContinuousGroupCohomology.FiniteStageCochains
import ContinuousGroupCohomology.SeededCochains
import ContinuousGroupCohomology.QuotientTransitions
import ContinuousGroupCohomology.OpenNormalDiagram
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ClusterPt

set_option warningAsError true

/-!
# A sign orbit at a finite resolution stage

The action of integer units on the discrete integers has a nonconstant,
nonzero degree-one orbit that lifts from quotient-invariant coefficients over
an open normal quotient.

The sign representation is `CGCExamples.signedIntegers`; its action uses
Mathlib's `Representation.ofDistribMulAction`. The finite-stage lift uses
`ContinuousCohomology.exists_openNormal_resolution_lift`.

This module contains resolution/sign, topological-module boundary, finite-stage
boundary, colimit, quotient-invariants, resolution-image, cochain, seeded
descent, transition and open-normal diagram clients. The example entrypoints
import this module alongside their respective production modules. The sign
example uses an open-normal quotient, and the boundary clients use actual
homology boundaries rather than closure of the boundary range. Import the
corresponding `ContinuousGroupCohomology` modules to use their APIs.
-/

@[expose] public section

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageResolution

open _root_.ContinuousCohomology CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

private theorem empty_refinement (N₀ : OpenNormalSubgroup G) (i : ℕ) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ a ∈ (∅ : Finset (TopRep.resolutionX X i)), StageDescends X N i a :=
  exists_common_stage_refinement X N₀ i ∅ (by simp)

private theorem singleton_refinement (N₀ M : OpenNormalSubgroup G) (i : ℕ)
    (a : TopRep.resolutionX X i) (ha : StageDescends X M i a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ b ∈ ({a} : Finset (TopRep.resolutionX X i)), StageDescends X N i b := by
  classical
  apply exists_common_stage_refinement X N₀ i {a}
  intro b hb
  obtain rfl := Finset.mem_singleton.mp hb
  exact ⟨M, ha⟩

section CompactCoefficients

variable [CompactSpace G] [DiscreteTopology X] [TopRep.JointlyContinuous X]

private theorem level_zero (a : X) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 0 a :=
  exists_openNormal_stage_descends X 0 a

private theorem level_one (a : TopRep.resolutionX X 1) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 1 a :=
  exists_openNormal_stage_descends X 1 a

private theorem level_three (a : TopRep.resolutionX X 3) :
    ∃ N : OpenNormalSubgroup G, StageDescends X N 3 a :=
  exists_openNormal_stage_descends X 3 a

private theorem level_three_lift (a : TopRep.resolutionX X 3) :
    ∃ (N : OpenNormalSubgroup G)
      (b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 3),
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 3).hom b = a :=
  exists_openNormal_resolution_lift X 3 a

end CompactCoefficients

private abbrev signRepresentation : TopRep ℤ (Units ℤ) :=
  TopRep.of <| ContRepresentation.ofMonoidHom {
    toFun := fun unit => (unit : ℤ) • (1 : ℤ →L[ℤ] ℤ)
    map_one' := by
      ext
      simp
    map_mul' := by
      intro a b
      ext
      simp [Units.val_mul]
  }

private instance : TopRep.JointlyContinuous signRepresentation where
  continuous_action := continuous_of_discreteTopology

private theorem sign_orbit_lift :
    ∃ (orbit : TopRep.resolutionX signRepresentation 1),
      (∀ g : Units ℤ, orbit g = signRepresentation.ρ g (1 : signRepresentation)) ∧
      orbit (-1 : Units ℤ) ≠ orbit 1 ∧ orbit (-1 : Units ℤ) ≠ 0 ∧
      ∃ (N : OpenNormalSubgroup (Units ℤ))
        (b : TopRep.resolutionX
          (TopRep.quotientInvariants N.toSubgroup signRepresentation) 1),
          (resolutionMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup signRepresentation) 1).hom b =
              orbit := by
  let orbit : TopRep.resolutionX signRepresentation 1 :=
    ⟨fun g => signRepresentation.ρ g (1 : signRepresentation),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hnonconstant : orbit (-1 : Units ℤ) ≠ orbit 1 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠
      ((1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1
    norm_num
  have hnonzero : orbit (-1 : Units ℤ) ≠ 0 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠ 0
    norm_num
  obtain ⟨N, b, hb⟩ := exists_openNormal_resolution_lift signRepresentation 1 orbit
  exact ⟨orbit, fun _ => rfl, hnonconstant, hnonzero, N, b, hb⟩

end IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageResolution

namespace CGCExamples.FiniteStageResolution

open _root_.ContinuousCohomology

/-- The orbit of `1` under the integer-unit sign action is nonconstant and nonzero
at the negative unit, and lifts through a finite open-normal quotient at degree one. -/
theorem exists_signedIntegers_orbit_lift :
    ∃ (orbit : TopRep.resolutionX signedIntegers 1),
      (∀ g : Units ℤ, orbit g = signedIntegers.ρ g (1 : ℤ)) ∧
      orbit (-1 : Units ℤ) ≠ orbit 1 ∧ orbit (-1 : Units ℤ) ≠ 0 ∧
      ∃ (N : OpenNormalSubgroup (Units ℤ))
        (b : TopRep.resolutionX
          (TopRep.quotientInvariants N.toSubgroup signedIntegers) 1),
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup signedIntegers) 1).hom b =
            orbit := by
  let : CompactSpace (Units ℤ) := Finite.compactSpace
  let orbit : TopRep.resolutionX signedIntegers 1 :=
    ⟨fun g => signedIntegers.ρ g (1 : ℤ),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hnonconstant : orbit (-1 : Units ℤ) ≠ orbit 1 := by
    change signedIntegers.ρ (-1 : Units ℤ) (1 : ℤ) ≠
      signedIntegers.ρ 1 (1 : ℤ)
    simpa only [signedIntegers_ρ_apply, one_smul] using
      signedIntegers_negative_one_not_fixed
  have hnonzero : orbit (-1 : Units ℤ) ≠ 0 := by
    change signedIntegers.ρ (-1 : Units ℤ) (1 : ℤ) ≠ (0 : ℤ)
    rw [signedIntegers_negative_one]
    change (-1 : ℤ) ≠ (0 : ℤ)
    norm_num
  obtain ⟨N, b, hb⟩ := exists_openNormal_resolution_lift signedIntegers 1 orbit
  exact ⟨orbit, fun _ => rfl, hnonconstant, hnonzero, N, b, hb⟩

example : signedIntegers.ρ (-1 : Units ℤ) (0 : ℤ) = 0 ∧
    signedIntegers.ρ (-1 : Units ℤ) (1 : ℤ) ≠ (1 : ℤ) := by
  constructor
  · simp only [signedIntegers_ρ_apply, smul_zero]
    rfl
  · exact signedIntegers_negative_one_not_fixed

end CGCExamples.FiniteStageResolution

namespace CGCExamples.TopModuleCat

open CategoryTheory

universe u v

section HomologyBoundary

private theorem equal_classes_have_difference_boundary
    {k : Type u} [Ring k] [TopologicalSpace k]
    (S : ShortComplex (TopModuleCat.{v} k)) (z₁ z₂ : S.cycles)
    (h : S.homologyπ.hom z₁ = S.homologyπ.hom z₂) :
    ∃ w : S.X₁, S.toCycles.hom w = z₁ - z₂ := by
  apply (TopModuleCat.shortComplex_homologyπ_eq_zero_iff S (z₁ - z₂)).mp
  simpa only [map_sub, sub_eq_zero] using h

end HomologyBoundary

end CGCExamples.TopModuleCat

namespace CGCExamples.ContinuousCohomology

open CategoryTheory TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section FiniteStageBoundary

section DegreeZero

private theorem degree_zero_at_original_stage (X : TopRep.{max v w} k G)
    (M : OpenNormalSubgroup G)
    (a : continuousCohomology 0 (TopRep.quotientInvariants M.toSubgroup X))
    (ha : (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) 0).hom a = 0) :
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom M M le_rfl)
      (ContinuousCohomology.quotientTransitionIncl X le_rfl) 0).hom a = 0 := by
  have hz := ContinuousCohomology.class_eq_zero_of_inflation_zero_degree_zero M X a ha
  simp only [hz, map_zero]

end DegreeZero

section DegreeTwo

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X]

private theorem degree_two_eventual_equality (M : OpenNormalSubgroup G)
    (a b : continuousCohomology 2 (TopRep.quotientInvariants M.toSubgroup X))
    (hab : (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) 2).hom a =
      (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) 2).hom b) :
    ∃ (N : OpenNormalSubgroup G) (hNM : N ≤ M),
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) 2).hom a =
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) 2).hom b :=
  ContinuousCohomology.exists_refinement_class_eq_of_inflation_eq X M 2 a b hab

end DegreeTwo

end FiniteStageBoundary

end CGCExamples.ContinuousCohomology

open CategoryTheory CategoryTheory.Limits TopRep

namespace CGCExamples.ContinuousCohomology

universe u v w

section FiniteStageColimit

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
  [TopRep.JointlyContinuous X] (n : ℕ)

private noncomputable def descendant
    (s : Cocone (ContinuousCohomology.openNormalCohomologyDiagram X n)) :
    (ContinuousCohomology.openNormalInflationCocone X n).pt ⟶ s.pt :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).desc s

private theorem descendant_factorization
    (s : Cocone (ContinuousCohomology.openNormalCohomologyDiagram X n))
    (M : OrderDual (OpenNormalSubgroup G)) :
    (ContinuousCohomology.openNormalInflationCocone X n).ι.app M ≫
      descendant X n s = s.ι.app M :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).fac s M

private theorem descendant_unique
    (s : Cocone (ContinuousCohomology.openNormalCohomologyDiagram X n))
    (f : (ContinuousCohomology.openNormalInflationCocone X n).pt ⟶ s.pt)
    (hf : ∀ M, (ContinuousCohomology.openNormalInflationCocone X n).ι.app M ≫
      f = s.ι.app M) :
    f = descendant X n s :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).uniq s f hf

private noncomputable def zero_degree :
    IsColimit (ContinuousCohomology.openNormalInflationCocone X 0) :=
  ContinuousCohomology.openNormalInflationCoconeIsColimit X 0

end FiniteStageColimit

end CGCExamples.ContinuousCohomology

namespace IncubatorTest.RepresentationTheory.Continuous.QuotientInvariants

universe u v w

open CategoryTheory

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

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.ResolutionImage

open _root_.ContinuousCohomology

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) (N : OpenNormalSubgroup G)

private theorem level_zero (x : X) :
    StageDescends X N 0 x ↔
      ∃ b : TopRep.quotientInvariants N.toSubgroup X,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 0).hom b = x :=
  stageDescends_iff_exists_lift X N 0 x

private theorem level_one (F : TopRep.resolutionX X 1) :
    ((∀ g : G, StageDescends X N 0 (F g)) ∧
      ∀ (g : G) (t : N.toSubgroup), F (g * t.1) = F g) ↔
      ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 1,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 1).hom b = F :=
  stageDescends_iff_exists_lift X N 1 F

private theorem level_three (F : TopRep.resolutionX X 3) :
    StageDescends X N 3 F ↔
      ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) 3,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) 3).hom b = F :=
  stageDescends_iff_exists_lift X N 3 F

private theorem refinement {M : OpenNormalSubgroup G} (h : N ≤ M)
    (F : TopRep.resolutionX X 3) (hF : StageDescends X M 3 F) :
    StageDescends X N 3 F :=
  stageDescends_antitone X h 3 F hF

private abbrev signRepresentation : TopRep ℤ (Units ℤ) :=
  TopRep.of <| ContRepresentation.ofMonoidHom {
    toFun := fun unit => (unit : ℤ) • (1 : ℤ →L[ℤ] ℤ)
    map_one' := by
      ext
      simp
    map_mul' := by
      intro a b
      ext
      simp [Units.val_mul]
  }

private abbrev fullSubgroup : OpenNormalSubgroup (Units ℤ) :=
  ⟨⟨⊤, isOpen_discrete _⟩, inferInstance⟩

private theorem sign_action_nontrivial :
    signRepresentation.ρ (-1 : Units ℤ) (1 : signRepresentation) = -1 := by
  change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 = -1
  norm_num

private theorem sign_nonfixed :
    ¬ StageDescends signRepresentation fullSubgroup 0 (1 : signRepresentation) := by
  intro h
  have hneg := h ⟨(-1 : Units ℤ), Subgroup.mem_top _⟩
  change signRepresentation.ρ (-1 : Units ℤ) (1 : signRepresentation) = 1 at hneg
  rw [sign_action_nontrivial] at hneg
  norm_num at hneg

private abbrev nonfixedConstant : C(Units ℤ, ℤ) :=
  ContinuousMap.const _ (1 : ℤ)

private theorem constant_right_cosets (g : Units ℤ) (t : fullSubgroup.toSubgroup) :
    nonfixedConstant (g * t.1) = nonfixedConstant g := rfl

private theorem right_constant_not_liftable :
    ¬ ∃ b : TopRep.resolutionX
        (TopRep.quotientInvariants fullSubgroup.toSubgroup signRepresentation) 1,
      (resolutionMap (openNormalQuotientHom fullSubgroup)
        (TopRep.quotientInvariantsIncl fullSubgroup.toSubgroup signRepresentation) 1).hom b =
        nonfixedConstant := by
  intro h
  have hdescent := (stageDescends_iff_exists_lift signRepresentation fullSubgroup 1
    nonfixedConstant).mpr h
  exact sign_nonfixed (hdescent.1 1)

end IncubatorTest.RepresentationTheory.ContinuousCohomology.ResolutionImage

namespace IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageCochains

open _root_.ContinuousCohomology CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

section CompactCoefficients

variable [CompactSpace G] [DiscreteTopology X] [TopRep.JointlyContinuous X]

private theorem degree_zero (σ : (TopRep.homogeneousCochains X).X 0) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 0),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 0) τ = σ :=
  exists_openNormal_quotient_cochain_lift X 0 σ

private theorem degree_two (σ : (TopRep.homogeneousCochains X).X 2) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 2),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 2) τ = σ :=
  exists_openNormal_quotient_cochain_lift X 2 σ

private theorem degree_two_closed (σ : (TopRep.homogeneousCochains X).X 2)
    (hσ : (TopRep.homogeneousCochains X).d 2 3 σ = 0) :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 2),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 2) τ = σ ∧
          (TopRep.homogeneousCochains
            (TopRep.quotientInvariants N.toSubgroup X)).d 2 3 τ = 0 :=
  exists_openNormal_quotient_closed_cochain_lift X 2 σ hσ

private theorem zero_closed :
    ∃ (N : OpenNormalSubgroup G)
      (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X 0),
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f 0) τ = 0 ∧
          (TopRep.homogeneousCochains
            (TopRep.quotientInvariants N.toSubgroup X)).d 0 1 τ = 0 := by
  apply exists_openNormal_quotient_closed_cochain_lift X 0 0
  simp

end CompactCoefficients

private abbrev signRepresentation : TopRep ℤ (Units ℤ) :=
  TopRep.of <| ContRepresentation.ofMonoidHom {
    toFun := fun unit => (unit : ℤ) • (1 : ℤ →L[ℤ] ℤ)
    map_one' := by
      ext
      simp
    map_mul' := by
      intro first second
      ext
      simp [Units.val_mul]
  }

private instance : TopRep.JointlyContinuous signRepresentation where
  continuous_action := continuous_of_discreteTopology

private theorem sign_orbit_cochain_lift :
    ∃ (σ : (TopRep.homogeneousCochains signRepresentation).X 0),
      (∀ g : Units ℤ, σ.1 g = signRepresentation.ρ g (1 : signRepresentation)) ∧
      σ.1 (-1 : Units ℤ) ≠ σ.1 1 ∧ σ.1 (-1 : Units ℤ) ≠ 0 ∧
      ∃ (N : OpenNormalSubgroup (Units ℤ))
        (τ : (TopRep.homogeneousCochains
          (TopRep.quotientInvariants N.toSubgroup signRepresentation)).X 0),
          ((cochainsMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup signRepresentation)).f 0) τ = σ := by
  let orbit : TopRep.resolutionX signRepresentation 1 :=
    ⟨fun g => signRepresentation.ρ g (1 : signRepresentation),
      TopRep.JointlyContinuous.continuous_action.comp
        (continuous_id.prodMk continuous_const)⟩
  have hfix : orbit ∈ (TopRep.resolutionX signRepresentation 1).ρ.invariants := by
    intro g
    apply ContinuousMap.ext
    intro h
    change signRepresentation.ρ g
      (signRepresentation.ρ (g⁻¹ * h) (1 : signRepresentation)) =
        signRepresentation.ρ h (1 : signRepresentation)
    change (signRepresentation.ρ g * signRepresentation.ρ (g⁻¹ * h))
      (1 : signRepresentation) = signRepresentation.ρ h (1 : signRepresentation)
    rw [← map_mul, mul_inv_cancel_left]
  let σ : (TopRep.homogeneousCochains signRepresentation).X 0 := ⟨orbit, hfix⟩
  have hnonconstant : σ.1 (-1 : Units ℤ) ≠ σ.1 1 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠
      ((1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1
    norm_num
  have hnonzero : σ.1 (-1 : Units ℤ) ≠ 0 := by
    change ((-1 : ℤ) • (1 : ℤ →L[ℤ] ℤ)) 1 ≠ 0
    norm_num
  obtain ⟨N, τ, hτ⟩ := exists_openNormal_quotient_cochain_lift signRepresentation 0 σ
  exact ⟨σ, fun _ => rfl, hnonconstant, hnonzero, N, τ, hτ⟩

end IncubatorTest.RepresentationTheory.ContinuousCohomology.FiniteStageCochains

namespace CGCExamples.ContinuousCohomology

section SeededCochains

universe u v w

open CategoryTheory TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X]

/-- Refine any stage while preserving the exact native inflation equation. -/
private theorem cochain_descends_below (M : OpenNormalSubgroup G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (N : OpenNormalSubgroup G), N ≤ M ∧
      ∃ (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X n),
        ((ContinuousCohomology.cochainsMap
          (ContinuousCohomology.openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n) τ = σ :=
  ContinuousCohomology.exists_quotient_cochain_lift_below X M n σ

end SeededCochains

end CGCExamples.ContinuousCohomology

namespace CGCExamples.ContinuousCohomology

section QuotientTransitions

universe u v w

open CategoryTheory TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)
variable {N M L : OpenNormalSubgroup G} (hNM : N ≤ M) (hML : M ≤ L) (n : ℕ)

private theorem composite_cochain
    (σ : (TopRep.homogeneousCochains
      (TopRep.quotientInvariants L.toSubgroup X)).X n) :
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.quotientTransitionHom N L (hNM.trans hML))
      (ContinuousCohomology.quotientTransitionIncl X (hNM.trans hML))).f n) σ =
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.quotientTransitionHom N M hNM)
      (ContinuousCohomology.quotientTransitionIncl X hNM)).f n)
      (((ContinuousCohomology.cochainsMap
        (ContinuousCohomology.quotientTransitionHom M L hML)
        (ContinuousCohomology.quotientTransitionIncl X hML)).f n) σ) := by
  rw [ContinuousCohomology.quotientTransition_cochainsMap_comp X hNM hML]
  rfl

private theorem composite_class
    (a : continuousCohomology n
      (TopRep.quotientInvariants L.toSubgroup X)) :
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom N L (hNM.trans hML))
      (ContinuousCohomology.quotientTransitionIncl X (hNM.trans hML)) n).hom a =
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom N M hNM)
      (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom
      ((ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom M L hML)
        (ContinuousCohomology.quotientTransitionIncl X hML) n).hom a) := by
  rw [ContinuousCohomology.quotientTransition_map_comp X hNM hML n]
  rfl

private theorem inflation_triangle_cochain
    (σ : (TopRep.homogeneousCochains
      (TopRep.quotientInvariants M.toSubgroup X)).X n) :
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X)).f n) σ =
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n)
      (((ContinuousCohomology.cochainsMap
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM)).f n) σ) := by
  rw [ContinuousCohomology.quotientTransition_cochainsMap_inflate X hNM]
  rfl

private theorem inflation_triangle_class
    (a : continuousCohomology n
      (TopRep.quotientInvariants M.toSubgroup X)) :
    (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) n).hom a =
    (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom
      ((ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom a) := by
  rw [ContinuousCohomology.quotientTransition_map_inflate X hNM n]
  rfl

end QuotientTransitions

end CGCExamples.ContinuousCohomology

namespace CGCExamples.ContinuousCohomology

section OpenNormalDiagram

universe u v w

open CategoryTheory TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) (n : ℕ)
variable {N M L : OpenNormalSubgroup G} (hNM : N ≤ M) (hML : M ≤ L)

private theorem refinement_direction
    (a : continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X)) :
    ((ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM)).hom a =
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom a := rfl

private theorem composition :
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ L N (hNM.trans hML)) =
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ L M hML) ≫
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM) := by
  exact (ContinuousCohomology.openNormalCohomologyDiagram X n).map_comp _ _

private theorem inflation_triangle :
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
        (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM) ≫
      (ContinuousCohomology.openNormalInflationCocone X n).ι.app N =
    (ContinuousCohomology.openNormalInflationCocone X n).ι.app M := by
  exact (ContinuousCohomology.openNormalInflationCocone X n).ι.naturality _

omit [IsTopologicalGroup G] in
private theorem filtered_index :
    IsFiltered (OrderDual (OpenNormalSubgroup G)) :=
  ContinuousCohomology.isFiltered_orderDual_openNormalSubgroup G

end OpenNormalDiagram

end CGCExamples.ContinuousCohomology
