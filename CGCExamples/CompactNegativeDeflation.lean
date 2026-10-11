/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology
public import Mathlib.Algebra.CharP.Two
public import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Instances.ZMod

/-!
# Compact negative Tate deflation for a two-element group

The trivial representation of the cyclic group of order two on `ZMod 2`
has compact discrete invariant coefficients at every open subgroup. At the
bottom open normal subgroup its degree-`-2` compact Tate stage contains a
nonzero class. The identity deflation fixes this class, and the comparison
square also applies to the proper inclusion into the full subgroup.

The nonzero class uses mathlib's finite-cyclic homology quotient map in
homological degree one. It is not inferred merely from nonzero coefficients.

## References

The cyclic quotient computation uses
`Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic` by
Amelia Livingston. The compact comparisons use `CompactNegativeTate` and
mathlib's Tate-to-homology comparison by Yunzhou Xie and Yaël Dillies;
`CompactNegativeDeflation` supplies the continuous finite-bar norm transport.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace CGCExamples.CompactNegativeDeflation

section Diagrams

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

example (n : ℕ) {S T U : OpenNormalSubgroup G} (f : S ⟶ T) (g : T ⟶ U) :
    (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map f ≫
        (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map g =
      (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map (f ≫ g) :=
  ((LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map_comp f g).symm

example (n : ℕ) {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    ((finiteNegativeDeflationDiagram A (n + 1) ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f) ≫
        (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.app T =
      (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.app S ≫
        ((LevelCompact.compactFiniteNegativeDeflationDiagram A L n ⋙
          forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u}).map f) :=
  (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.naturality f

/-- Deflating a Tate-labelled class can be computed through the forward
component of the homological diagram comparison. -/
example (n : ℕ) {S T : OpenNormalSubgroup G} [Fintype (G ⧸ S.toSubgroup)]
    (f : S ⟶ T)
    (x : tateCohomology (A.quotientToInvariants S.toSubgroup) (-(n + 2 : ℤ))) :
    (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map f
        (LevelCompact.tateCohomologyNegativeAddEquivFiniteTate A L S n x) =
      (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.app T
        ((finiteNegativeDeflationDiagram A (n + 1)).map f
          (((TateCohomology.isoGroupHomology (R := R) (G := G ⧸ S.toSubgroup)
            (-(n + 2 : ℤ)) (n + 1) (by omega)).app
              (A.quotientToInvariants S.toSubgroup)).hom x)) := by
  let y : groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1) :=
    ((TateCohomology.isoGroupHomology (R := R) (G := G ⧸ S.toSubgroup)
      (-(n + 2 : ℤ)) (n + 1) (by omega)).app
        (A.quotientToInvariants S.toSubgroup)).hom x
  have hcompare :
      ((LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.app S y :
        (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).obj S) =
      LevelCompact.tateCohomologyNegativeAddEquivFiniteTate A L S n x :=
    (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso_hom_app_apply A L n S y).trans
      (LevelCompact.groupHomologyAddEquivFiniteTateNegative_isoGroupHomology_apply A L S n x)
  exact (congrArg
    (fun z : (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).obj S ↦
      (LevelCompact.compactFiniteNegativeDeflationDiagram A L n).map f z)
    hcompare.symm).trans
      ((LevelCompact.finiteNegativeDeflationAdditiveDiagramIso A L n).hom.naturality_apply
        f y).symm

end Diagrams

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩

private abbrev twoElementGroup : ProfiniteGrp := ProfiniteGrp.of G₂

private abbrev coefficients : Rep (ZMod 2) twoElementGroup :=
  Rep.trivial (ZMod 2) twoElementGroup (ZMod 2)

private def compactLevels : LevelCompact coefficients where
  topology _ := ⊥
  compact U := by
    let : TopologicalSpace (openSubgroupInvariants coefficients U) := ⊥
    have : Finite (openSubgroupInvariants coefficients U) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    infer_instance
  t2 U := by
    let : TopologicalSpace (openSubgroupInvariants coefficients U) := ⊥
    have : DiscreteTopology (openSubgroupInvariants coefficients U) := ⟨rfl⟩
    infer_instance
  topologicalAddGroup U := by
    let : TopologicalSpace (openSubgroupInvariants coefficients U) := ⊥
    have : DiscreteTopology (openSubgroupInvariants coefficients U) := ⟨rfl⟩
    infer_instance
  continuous_transport U V _ _ := by
    let : TopologicalSpace (openSubgroupInvariants coefficients U) := ⊥
    let : TopologicalSpace (openSubgroupInvariants coefficients V) := ⊥
    have : DiscreteTopology (openSubgroupInvariants coefficients U) := ⟨rfl⟩
    exact continuous_of_discreteTopology

private def properLevel : OpenNormalSubgroup twoElementGroup :=
  ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩

private def fullLevel : OpenNormalSubgroup twoElementGroup := ⟨⊤, inferInstance⟩

private theorem properLevel_lt_fullLevel : properLevel < fullLevel := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

private abbrev quotientGroup := twoElementGroup ⧸ properLevel.toSubgroup

private instance : Fintype quotientGroup := Fintype.ofFinite _
private instance : DecidableEq quotientGroup := Classical.decEq _

private instance : IsCyclic quotientGroup :=
  isCyclic_of_surjective (QuotientGroup.mk' properLevel.toSubgroup)
    (QuotientGroup.mk'_surjective _)

private def generator : quotientGroup := IsCyclic.exists_generator.choose

private theorem generator_generates : ∀ x : quotientGroup, x ∈ Subgroup.zpowers generator :=
  IsCyclic.exists_generator.choose_spec

private theorem quotientGroup_card : Fintype.card quotientGroup = 2 := by
  let : Fintype (G₂ ⧸ (⊥ : Subgroup G₂)) := Fintype.ofFinite _
  change Fintype.card (G₂ ⧸ (⊥ : Subgroup G₂)) = 2
  rw [Fintype.card_congr (QuotientGroup.quotientBot (G := G₂)).toEquiv]
  exact ZMod.card 2

private abbrev stageCoefficients := coefficients.quotientToInvariants properLevel.toSubgroup

private theorem stage_action (g : quotientGroup) (x : stageCoefficients) :
    stageCoefficients.ρ g x = x := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    apply Subtype.ext
    rfl

private theorem stage_norm_eq_zero : stageCoefficients.ρ.norm = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply]
  calc
    stageCoefficients.ρ.norm x = ∑ g : quotientGroup, stageCoefficients.ρ g x := by
      rw [Representation.norm, LinearMap.sum_apply]
    _ = (2 : ℕ) • x :=
      (Finset.sum_eq_card_nsmul (fun (g : quotientGroup) _ => stage_action g x)).trans
        (congrArg (fun n : ℕ => n • x)
          ((Finset.card_univ :
            (Finset.univ : Finset quotientGroup).card = Fintype.card quotientGroup).trans
            quotientGroup_card))
    _ = (2 : ZMod 2) • x := (ofNat_smul_eq_nsmul (ZMod 2) 2 x).symm
    _ = 0 :=
      (congrArg (fun r : ZMod 2 => r • x)
        (CharTwo.two_eq_zero (R := ZMod 2))).trans (zero_smul (ZMod 2) x)

private abbrev residualGroup :=
  fullLevel.toSubgroup.map (QuotientGroup.mk' properLevel.toSubgroup)

private instance : Fintype residualGroup := Fintype.ofFinite _

private theorem residualGroup_card : Fintype.card residualGroup = 2 := by
  have htop : residualGroup = (⊤ : Subgroup quotientGroup) :=
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  calc
    Fintype.card residualGroup = Fintype.card quotientGroup :=
      Fintype.card_congr ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).toEquiv
    _ = 2 := quotientGroup_card

private theorem proper_deflation_coeff_eq_zero :
    finiteNegativeDeflationCoeffDirect coefficients properLevel.toSubgroup
      fullLevel.toSubgroup (le_of_lt properLevel_lt_fullLevel) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [Representation.IntertwiningMap.toLinearMap_apply,
    finiteNegativeDeflationCoeffDirect_apply_val]
  calc
    (∑ q : residualGroup, (stageCoefficients.ρ q.1 x : ZMod 2)) =
        (2 : ℕ) • (x : ZMod 2) :=
      (Finset.sum_eq_card_nsmul (fun (q : residualGroup) _ =>
        congrArg (fun y : stageCoefficients => (y : ZMod 2)) (stage_action q.1 x))).trans
        (congrArg (fun n : ℕ => n • (x : ZMod 2))
          ((Finset.card_univ :
            (Finset.univ : Finset residualGroup).card = Fintype.card residualGroup).trans
            residualGroup_card))
    _ = 0 := CharTwo.two_nsmul (x : ZMod 2)

private theorem proper_algebraic_deflation_eq_zero :
    finiteNegativeDeflation coefficients properLevel.toSubgroup fullLevel.toSubgroup
      (le_of_lt properLevel_lt_fullLevel) 1 = 0 := by
  rw [finiteNegativeDeflation_eq_direct_map, proper_deflation_coeff_eq_zero]
  exact (congrArg (fun f ↦ HomologicalComplex.homologyMap f 1)
    (groupHomology.chainsMap_zero (A := stageCoefficients)
      (B := coefficients.quotientToInvariants fullLevel.toSubgroup)
      (finiteDeflationGroupHom properLevel.toSubgroup fullLevel.toSubgroup
        (le_of_lt properLevel_lt_fullLevel)))).trans
    (HomologicalComplex.homologyMap_zero _ _ 1)

private def oneVector : stageCoefficients := ⟨1, by intro _; rfl⟩

private def cycleVector : LinearMap.ker
    (Rep.applyAsHom stageCoefficients generator - 𝟙 stageCoefficients).hom.toLinearMap :=
  ⟨oneVector, by
    change stageCoefficients.ρ generator oneVector - oneVector = 0
    rw [stage_action, sub_self]⟩

private def homologyClass : groupHomology stageCoefficients 1 :=
  Rep.FiniteCyclicGroup.groupHomologyπOdd stageCoefficients generator
    generator_generates 1 (by exact ⟨0, rfl⟩) cycleVector

private theorem homologyClass_ne_zero : homologyClass ≠ 0 := by
  intro h
  have hx := (Rep.FiniteCyclicGroup.groupHomologyπOdd_eq_zero_iff
    stageCoefficients generator generator_generates 1 (by exact ⟨0, rfl⟩) cycleVector).mp h
  change oneVector ∈ LinearMap.range stageCoefficients.ρ.norm at hx
  rw [stage_norm_eq_zero, LinearMap.range_zero, Submodule.mem_bot] at hx
  have hv := congrArg (fun x : stageCoefficients ↦ (x : ZMod 2)) hx
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hv

private def compactClass :
    LevelCompact.finiteTateNegative coefficients compactLevels properLevel 0 :=
  LevelCompact.groupHomologyAddEquivFiniteTateNegative coefficients compactLevels
    properLevel 0 homologyClass

private theorem compactClass_ne_zero : compactClass ≠ 0 := by
  intro h
  apply homologyClass_ne_zero
  exact (LevelCompact.groupHomologyAddEquivFiniteTateNegative coefficients compactLevels
    properLevel 0).injective (h.trans (map_zero _).symm)

/-- The concrete degree-`-2` stage contains a class fixed by identity deflation
which is not zero. -/
example : ∃ x : LevelCompact.finiteTateNegative coefficients compactLevels properLevel 0,
    x ≠ 0 ∧
      (LevelCompact.compactFiniteNegativeDeflationDiagram coefficients compactLevels 0).map
        (𝟙 properLevel) x = x := by
  refine ⟨compactClass, compactClass_ne_zero, ?_⟩
  rw [LevelCompact.compactFiniteNegativeDeflationDiagram_map,
    LevelCompact.finiteTateNegativeDeflation_refl]
  rfl

example : properLevel < fullLevel := properLevel_lt_fullLevel

example :
    ((finiteNegativeDeflationDiagram coefficients 1 ⋙
      forget₂ (ModuleCat (ZMod 2)) AddCommGrpCat).map
        (homOfLE (le_of_lt properLevel_lt_fullLevel))) ≫
      (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso coefficients compactLevels 0).hom.app
        fullLevel =
      (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso coefficients compactLevels 0).hom.app
        properLevel ≫
      ((LevelCompact.compactFiniteNegativeDeflationDiagram coefficients compactLevels 0 ⋙
        forget₂ CompHausAddCommGrp AddCommGrpCat).map
          (homOfLE (le_of_lt properLevel_lt_fullLevel))) :=
  (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso
    coefficients compactLevels 0).hom.naturality _

/-- The proper inclusion sends the nonzero degree-`-2` class to zero:
its coefficient norm sums two identical vectors in characteristic two. -/
example :
    (LevelCompact.compactFiniteNegativeDeflationDiagram coefficients compactLevels 0).map
      (homOfLE (le_of_lt properLevel_lt_fullLevel)) compactClass = 0 := by
  let : Fintype (twoElementGroup ⧸ fullLevel.toSubgroup) := Fintype.ofFinite _
  have hvalue :
      LevelCompact.finiteTateNegativeDeflation coefficients compactLevels
        properLevel fullLevel (le_of_lt properLevel_lt_fullLevel) 0 compactClass = 0 := by
    calc
      LevelCompact.finiteTateNegativeDeflation coefficients compactLevels
          properLevel fullLevel (le_of_lt properLevel_lt_fullLevel) 0 compactClass =
          LevelCompact.groupHomologyAddEquivFiniteTateNegative coefficients compactLevels
            fullLevel 0
            (finiteNegativeDeflation coefficients properLevel.toSubgroup fullLevel.toSubgroup
              (le_of_lt properLevel_lt_fullLevel) 1 homologyClass) :=
        (LevelCompact.groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
          coefficients compactLevels properLevel fullLevel
          (le_of_lt properLevel_lt_fullLevel) 0 homologyClass).symm
      _ = 0 := by
        rw [proper_algebraic_deflation_eq_zero]
        exact map_zero _
  exact (CategoryTheory.congr_fun
    (LevelCompact.compactFiniteNegativeDeflationDiagram_map coefficients compactLevels
      0 (homOfLE (le_of_lt properLevel_lt_fullLevel))) compactClass).trans hvalue

/-- The inverse diagram component recovers the nonzero cyclic homology class
from its compact representative. -/
example :
    (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso
      coefficients compactLevels 0).inv.app properLevel compactClass ≠ 0 := by
  intro h
  apply compactClass_ne_zero
  let e := (LevelCompact.finiteNegativeDeflationAdditiveDiagramIso
    coefficients compactLevels 0).app properLevel
  have h' : e.inv compactClass = e.inv 0 := h.trans (map_zero e.inv.hom).symm
  exact e.symm.addCommGroupIsoToAddEquiv.injective h'

end CGCExamples.CompactNegativeDeflation
