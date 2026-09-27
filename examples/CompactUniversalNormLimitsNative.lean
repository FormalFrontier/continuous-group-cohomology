/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Implementation: hive-request-03e922288088a5d1c219136acc3e6c751b1deed4
  (c434e120-0a6c-400b-8688-df1930ee09cf)
Destination transfer: hive-request-e9e4a4d665612156fc293987266d82d3095b832f
  (7b81731e-77c0-4035-b4f8-486145079158)
-/
module

public import ContinuousGroupCohomology.CompactUniversalNormLimits

public section

/-!
# Client of compact universal-norm limits

These examples use only the new producer, arbitrary coefficient data, and the
actual compact additive-group limit and restricted linear norm interfaces.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CGCExamples.CompactUniversalNormLimitsNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

open ContinuousGroupCohomology
open ContinuousGroupCohomology.RestrictedLevelCompactRep

theorem chosenUniversalNormsAreReachable
    (A : LevelCompactRep.{u,u,u} R G) (U V : OpenNormalSubgroup G)
    (hVU : V ≤ U) :
    Function.Surjective ((universalNorm A).system.relativeNorm U V hVU) := by
  exact universalNorm_relativeNorm_surjective A U V hVU

theorem fullProjectionDetectsUniversalNorms
    (A : LevelCompactRep.{u,u,u} R G) (U : OpenNormalSubgroup G)
    (x : (full A).system.coefficients U) :
    x ∈ Set.range (limit.π (restrictedNormDiagram (full A)) U) ↔
      (x.1 : openSubgroupInvariants A.rep U.toOpenSubgroup) ∈
        LevelCompact.universalNormSubmodule A.rep U := by
  exact fullNormLimit_projection_mem_iff A U x

def compactComparisonForAnyRestrictedSystem (B : RestrictedLevelCompactRep R G) :
    CategoryTheory.Limits.limit (restrictedNormDiagram B) ≅
      CategoryTheory.Limits.limit (restrictedNormDiagram (full B.toLevelCompactRep)) := by
  exact restrictedNormLimitIso B

theorem forwardCoordinateIsTheActualInclusion (B : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G)
    (x : (CategoryTheory.Limits.limit (restrictedNormDiagram B) : CompHausAddCommGrp)) :
    limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U
        ((restrictedNormLimitIso B).hom x) =
      groupMap (fullInclusion B) U (limit.π (restrictedNormDiagram B) U x) := by
  exact ConcreteCategory.congr_hom (restrictedNormLimitIso_hom_π B U) x

theorem inverseCoordinateIsTheUniqueRestrictedLift
    (B : RestrictedLevelCompactRep R G) (U : OpenNormalSubgroup G)
    (x : (CategoryTheory.Limits.limit
      (restrictedNormDiagram (full B.toLevelCompactRep)) : CompHausAddCommGrp)) :
    groupMap (fullInclusion B) U
        (limit.π (restrictedNormDiagram B) U ((restrictedNormLimitIso B).inv x)) =
      limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U x := by
  exact ConcreteCategory.congr_hom (restrictedNormLimitIso_inv_π B U) x

theorem coefficientMorphismCommutesWithComparison
    {B C : RestrictedLevelCompactRep R G} (f : B ⟶ C)
    (x : (CategoryTheory.Limits.limit (restrictedNormDiagram B) : CompHausAddCommGrp)) :
    (restrictedNormLimitIso C).hom (lim.map (restrictedNormDiagramMap f) x) =
      lim.map (restrictedNormDiagramMap (fullFunctor.map (forget.map f)))
        ((restrictedNormLimitIso B).hom x) := by
  exact ConcreteCategory.congr_hom (restrictedNormLimitIso_naturality f) x

theorem everyCoefficientMorphismPreservesUniversalComparison
    {A C : LevelCompactRep.{u,u,u} R G} (f : A ⟶ C)
    (x : (CategoryTheory.Limits.limit
      (restrictedNormDiagram (universalNormFunctor.obj A)) : CompHausAddCommGrp)) :
    (restrictedNormLimitIso (universalNormFunctor.obj C)).hom
        (lim.map (restrictedNormDiagramMap (universalNormFunctor.map f)) x) =
      lim.map (restrictedNormDiagramMap
        (fullFunctor.map (forget.map (universalNormFunctor.map f))))
          ((restrictedNormLimitIso (universalNormFunctor.obj A)).hom x) := by
  exact ConcreteCategory.congr_hom (universalNorm_limitIso_naturality f) x

end CGCExamples.CompactUniversalNormLimitsNative
