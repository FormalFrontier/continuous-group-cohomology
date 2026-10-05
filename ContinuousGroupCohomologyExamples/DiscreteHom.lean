/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ContinuousGroupCohomology.TopRepDiscreteHom
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Topology.Algebra.Group.Units

/-!
# Discrete linear Hom examples

Integer units act by signs on `ℤ`. The Hom from this sign action to the
trivial action has a nonfixed identity map, while the identity of the sign
action is fixed. An infinite-rank source indexed by `ℕ` exercises the finite
group statement. An infinite product of sign groups, acting through its
first coordinate, exercises finite generation of the source independently
of discreteness or finiteness of the acting group.

As a mathematical boundary (not a compiled negative client), let an
infinite product of sign groups act trivially on a source `ℕ →₀ ℤ` and
coordinatewise by signs on a target `ℕ →₀ ℤ`. The diagonal map
`f(e_n) = e_n` has a non-open singleton stabilizer, so conjugation on
the discrete Hom carrier need not be jointly continuous without finite
generation. This is an existential example, not a failure for every
infinite-rank source. Independently, a finite acting group cannot by
itself guarantee scalar continuity on the discrete Hom carrier over a
non-discrete scalar ring.
-/

set_option warningAsError true

namespace ContinuousGroupCohomologyExamples.DiscreteHom

private noncomputable def ofDiscreteRepresentation {G M : Type*} [Group G]
    [AddCommGroup M] [Module ℤ M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation ℤ G M) : TopRep ℤ G := by
  letI : SMul ℤ M := (@Module.toDistribMulAction ℤ M _ _ ‹Module ℤ M›).toDistribSMul.toSMul
  haveI : ContinuousSMul ℤ M := ⟨continuous_of_discreteTopology⟩
  exact @TopRep.of ℤ G M _ _ _ ‹AddCommGroup M› ‹Module ℤ M› ‹TopologicalSpace M› _
    ‹ContinuousSMul ℤ M›
    (ContRepresentation.ofMonoidHom
      { toFun := fun g => { toLinearMap := ρ g, cont := continuous_of_discreteTopology }
        map_one' := by
          apply ContinuousLinearMap.coe_injective
          exact ρ.map_one
        map_mul' := by
          intro g h
          apply ContinuousLinearMap.coe_injective
          exact ρ.map_mul g h })

private noncomputable def sign : TopRep ℤ (Units ℤ) :=
  ofDiscreteRepresentation (Representation.ofDistribMulAction ℤ (Units ℤ) ℤ)

private noncomputable def trivialRep : TopRep ℤ (Units ℤ) :=
  ofDiscreteRepresentation (Representation.trivial ℤ (Units ℤ) ℤ)

private theorem sign_ρ (g : Units ℤ) (a : ℤ) : sign.ρ g a = g • a := rfl

private theorem trivial_ρ (g : Units ℤ) (a : ℤ) : trivialRep.ρ g a = a := rfl

private noncomputable def signToTrivial : sign.discreteLinHom trivialRep :=
  TopRep.discreteLinHomOfLinearMap sign trivialRep (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

private theorem signToTrivial_apply (a : ℤ) :
    (TopRep.discreteLinHomToLinearMap sign trivialRep signToTrivial) a = a := rfl

/-- The sign conjugation sends a nonzero map to a different nonzero map. -/
theorem signEvaluation :
    (TopRep.discreteLinHomToLinearMap sign trivialRep
      (((sign.discreteLinHom trivialRep).ρ (-1 : Units ℤ)) signToTrivial))
        (show sign from (1 : ℤ)) = (show trivialRep from (-1 : ℤ)) := by
  rw [TopRep.discreteLinHom_ρ_apply]
  simp [sign_ρ, trivial_ρ, signToTrivial_apply]
  rfl

/-- The identity map from the sign action to the trivial action is not fixed. -/
theorem signToTrivial_not_fixed :
    ¬ signToTrivial ∈ (sign.discreteLinHom trivialRep).ρ.toRepresentation.invariants := by
  intro hf
  have h := (TopRep.mem_discreteLinHom_invariants_iff sign trivialRep signToTrivial).mp hf
  have hneg := h (-1 : Units ℤ) (show sign from (1 : ℤ))
  change (-1 : ℤ) = 1 at hneg
  omega

private noncomputable def signIdentity : sign.discreteLinHom sign :=
  TopRep.discreteLinHomOfLinearMap sign sign (LinearMap.id : ℤ →ₗ[ℤ] ℤ)

/-- The nonzero identity map of the sign action is fixed. -/
theorem signIdentity_fixed :
    signIdentity ∈ (sign.discreteLinHom sign).ρ.toRepresentation.invariants := by
  apply (TopRep.mem_discreteLinHom_invariants_iff sign sign signIdentity).mpr
  intro g a
  rfl

/-- The nontrivial sign action also exercises the discrete-group route. -/
theorem discreteGroup_sign_jointlyContinuous :
    TopRep.JointlyContinuous (sign.discreteLinHom trivialRep) :=
  TopRep.discreteLinHom_jointlyContinuous_of_discreteGroup sign trivialRep

private noncomputable def trivialInfiniteRank : TopRep ℤ (Units ℤ) := by
  letI : TopologicalSpace (ℕ →₀ ℤ) := ⊥
  letI : DiscreteTopology (ℕ →₀ ℤ) := ⟨rfl⟩
  exact ofDiscreteRepresentation (Representation.trivial ℤ (Units ℤ) (ℕ →₀ ℤ))

private noncomputable def coordinateProjection : trivialInfiniteRank.discreteLinHom sign :=
  TopRep.discreteLinHomOfLinearMap trivialInfiniteRank sign
    (Finsupp.lapply 0 : (ℕ →₀ ℤ) →ₗ[ℤ] ℤ)

/-- The source indexed by `ℕ` is not finitely generated over `ℤ`. -/
theorem infiniteRank_not_finite : ¬ Module.Finite ℤ (ℕ →₀ ℤ) := by
  intro hfinite
  have hlt : Module.rank ℤ (ℕ →₀ ℤ) < Cardinal.aleph0 :=
    (Module.rank_lt_aleph0_iff).mpr hfinite
  simp at hlt

/-- A coordinate projection from an infinite-rank source is nonzero. -/
theorem infiniteRank_projection :
    (TopRep.discreteLinHomToLinearMap trivialInfiniteRank sign coordinateProjection)
      (show trivialInfiniteRank from Finsupp.single 0 (1 : ℤ)) =
        (show sign from (1 : ℤ)) := by
  have hprojection : TopRep.discreteLinHomToLinearMap trivialInfiniteRank sign
      coordinateProjection = (Finsupp.lapply 0 : (ℕ →₀ ℤ) →ₗ[ℤ] ℤ) :=
    TopRep.discreteLinHomToLinearMap_ofLinearMap _ _ _
  rw [hprojection]
  change (Finsupp.single 0 (1 : ℤ) : ℕ →₀ ℤ) 0 = 1
  simp

/-- Finiteness of the group, not finite generation of the source, supplies
joint continuity for Hom from the discrete infinite-rank module. -/
theorem finiteGroup_infiniteRank_jointlyContinuous :
    TopRep.JointlyContinuous (trivialInfiniteRank.discreteLinHom sign) :=
  TopRep.discreteLinHom_jointlyContinuous_of_finiteGroup _ _

private def FiniteIndiscreteGroup := Units ℤ

private instance : Group FiniteIndiscreteGroup := inferInstanceAs (Group (Units ℤ))
private instance : Finite FiniteIndiscreteGroup := inferInstanceAs (Finite (Units ℤ))
private instance : TopologicalSpace FiniteIndiscreteGroup := ⊤
private instance : IndiscreteTopology FiniteIndiscreteGroup := ⟨rfl⟩

private noncomputable def trivialIndiscrete : TopRep ℤ FiniteIndiscreteGroup :=
  ofDiscreteRepresentation (Representation.trivial ℤ FiniteIndiscreteGroup ℤ)

private instance : DiscreteTopology trivialIndiscrete := ⟨rfl⟩

private instance : TopRep.JointlyContinuous trivialIndiscrete := by
  refine ⟨?_⟩
  change Continuous fun pair : FiniteIndiscreteGroup × ℤ => pair.2
  exact continuous_snd

/-- This finite group carries a genuinely non-`T₁` topology. -/
theorem finiteIndiscreteGroup_not_t1 : ¬ T1Space FiniteIndiscreteGroup := by
  intro hsep
  have hsub : Subsingleton FiniteIndiscreteGroup :=
    (@subsingleton_iff_indiscreteTopology FiniteIndiscreteGroup _
      (@T1Space.t0Space FiniteIndiscreteGroup _ hsep)).mpr inferInstance
  have heq : (1 : Units ℤ) = -1 := hsub.elim _ _
  have hval := congrArg (fun unit : Units ℤ => (unit : ℤ)) heq
  norm_num at hval

/-- The jointly-continuous-input finite-group route applies with no `T₁`
assumption on the acting group. The carriers are nonzero copies of `ℤ`. -/
theorem finiteNonT1_jointlyContinuous :
    TopRep.JointlyContinuous (trivialIndiscrete.discreteLinHom trivialIndiscrete) :=
  TopRep.discreteLinHom_jointlyContinuous_of_finiteGroup_of_jointlyContinuous _ _

private def firstSign : Representation ℤ (ℕ → Units ℤ) ℤ :=
  (Representation.ofDistribMulAction ℤ (Units ℤ) ℤ).comp
    (Pi.evalMonoidHom (fun _ : ℕ => Units ℤ) 0)

private noncomputable def signProduct : TopRep ℤ (ℕ → Units ℤ) :=
  ofDiscreteRepresentation firstSign

private noncomputable def trivialProduct : TopRep ℤ (ℕ → Units ℤ) :=
  ofDiscreteRepresentation (Representation.trivial ℤ (ℕ → Units ℤ) ℤ)

private instance : Nontrivial (Units ℤ) := by
  refine ⟨⟨1, -1, ?_⟩⟩
  intro h
  have hval := congrArg (fun unit : Units ℤ => (unit : ℤ)) h
  norm_num at hval

/-- The product group in the finite-source example is infinite. -/
theorem infinite_product_sign_group : Infinite (ℕ → Units ℤ) := inferInstance

private theorem signProduct_jointlyContinuous : TopRep.JointlyContinuous signProduct := by
  refine ⟨?_⟩
  change Continuous fun pair : (ℕ → Units ℤ) × ℤ => pair.1 0 • pair.2
  exact continuous_smul.comp
    (((continuous_apply 0).comp continuous_fst).prodMk continuous_snd)

private theorem trivialProduct_jointlyContinuous : TopRep.JointlyContinuous trivialProduct := by
  refine ⟨?_⟩
  change Continuous fun pair : (ℕ → Units ℤ) × ℤ => pair.2
  exact continuous_snd

private instance : TopRep.JointlyContinuous signProduct := signProduct_jointlyContinuous
private instance : TopRep.JointlyContinuous trivialProduct := trivialProduct_jointlyContinuous
private instance : DiscreteTopology signProduct := ⟨rfl⟩
private instance : DiscreteTopology trivialProduct := ⟨rfl⟩

/-- Finite generation of `ℤ` gives joint continuity for a nontrivial sign
action of an infinite product group with its product topology. -/
theorem infiniteGroup_finiteSource_jointlyContinuous :
    TopRep.JointlyContinuous (signProduct.discreteLinHom trivialProduct) := by
  exact @TopRep.discreteLinHom_jointlyContinuous_of_finiteSource
    ℤ _ _ (ℕ → Units ℤ) _ signProduct trivialProduct _ _ _ _ _ _ (by
      change Module.Finite ℤ ℤ
      infer_instance)

end ContinuousGroupCohomologyExamples.DiscreteHom
