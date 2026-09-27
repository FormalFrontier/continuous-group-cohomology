/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactExceptionalTateCoefficientMaps
public import Mathlib.Data.ZMod.Basic

/-!
# Clients for compact exceptional Tate coefficient maps

The generic client exercises continuity, norm naturality, actual kernel and
quotient maps, identity, composition and both deflation squares. A finite
two-element group, its proper trivial subgroup and multiplication by two on
the nonzero finite coefficient module `ZMod 3` supply a nonidentity morphism.
Native adaptation by `hive-request-d61b09970e5688d0b1e0da08ec7719208350ad23`
(`b087c1ae-8092-47fc-ba95-7e8a338a0201`).
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace CGCExamples.CompactExceptionalTateCoefficientMapsNative

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable {A B C : LevelCompactRep.{u, u, u} R G}
variable (f : A ⟶ B) (g : B ⟶ C)
variable (S T : OpenNormalSubgroup G) (hST : S ≤ T)
variable [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]

example (U : OpenSubgroup G) :
    Continuous (LevelCompactRep.groupMap f U) :=
  (LevelCompactRep.groupMap f U).hom.continuous

example : Continuous (LevelCompactRep.finiteCoinvariantsMap f S) :=
  (LevelCompactRep.finiteCoinvariantsMap f S).hom.continuous

example (x : openSubgroupInvariants A.rep S.toOpenSubgroup) :
    LevelCompactRep.finiteCoinvariantsMap f S
      (LevelCompact.finiteCoinvariantsMk A.rep A.levelCompact S x) =
        LevelCompact.finiteCoinvariantsMk B.rep B.levelCompact S
          (LevelCompactRep.mapInvariants f S.toOpenSubgroup x) :=
  LevelCompactRep.finiteCoinvariantsMap_mk f S x

example (x : LevelCompact.finiteCoinvariants A.rep A.levelCompact S) :
    LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S
        (LevelCompactRep.finiteCoinvariantsMap f S x) =
      LevelCompactRep.groupMap f ⊤
        (LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S x) :=
  LevelCompactRep.normFromFiniteCoinvariants_naturality f S x

example : Continuous (LevelCompactRep.finiteTateNegOneMap f S) :=
  (LevelCompactRep.finiteTateNegOneMap f S).hom.continuous

example : Continuous (LevelCompactRep.finiteTateZeroMap f S) :=
  (LevelCompactRep.finiteTateZeroMap f S).hom.continuous

example (x : LevelCompact.finiteTateNegOne A.rep A.levelCompact S) :
    LevelCompact.finiteTateNegOneι B.rep B.levelCompact S
        (LevelCompactRep.finiteTateNegOneMap f S x) =
      LevelCompactRep.finiteCoinvariantsMap f S
        (LevelCompact.finiteTateNegOneι A.rep A.levelCompact S x) :=
  LevelCompactRep.finiteTateNegOneι_finiteTateNegOneMap_apply f S x

example (x : LevelCompact.group A.rep A.levelCompact ⊤) :
    LevelCompactRep.finiteTateZeroMap f S
        (LevelCompact.finiteTateZeroπ A.rep A.levelCompact S x) =
      LevelCompact.finiteTateZeroπ B.rep B.levelCompact S
        (LevelCompactRep.groupMap f ⊤ x) :=
  LevelCompactRep.finiteTateZeroMap_finiteTateZeroπ_apply f S x

example : LevelCompactRep.finiteTateNegOneMap (𝟙 A) S = 𝟙 _ :=
  LevelCompactRep.finiteTateNegOneMap_id A S

example : LevelCompactRep.finiteTateZeroMap (f ≫ g) S =
    LevelCompactRep.finiteTateZeroMap f S ≫ LevelCompactRep.finiteTateZeroMap g S :=
  LevelCompactRep.finiteTateZeroMap_comp f g S

example : LevelCompactRep.finiteCoinvariantsMap f S ≫
      LevelCompact.finiteCoinvariantDeflation B.rep B.levelCompact S T hST =
    LevelCompact.finiteCoinvariantDeflation A.rep A.levelCompact S T hST ≫
      LevelCompactRep.finiteCoinvariantsMap f T :=
  LevelCompactRep.finiteCoinvariantsMap_deflation f S T hST

example : LevelCompactRep.finiteTateNegOneMap f S ≫
      LevelCompact.finiteTateNegOneDeflation B.rep B.levelCompact S T hST =
    LevelCompact.finiteTateNegOneDeflation A.rep A.levelCompact S T hST ≫
      LevelCompactRep.finiteTateNegOneMap f T :=
  LevelCompactRep.finiteTateNegOneMap_deflation f S T hST

example : LevelCompactRep.finiteTateZeroMap f S ≫
      LevelCompact.finiteTateZeroDeflation B.rep B.levelCompact S T hST =
    LevelCompact.finiteTateZeroDeflation A.rep A.levelCompact S T hST ≫
      LevelCompactRep.finiteTateZeroMap f T :=
  LevelCompactRep.finiteTateZeroMap_deflation f S T hST

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩
local instance : IsTopologicalGroup G₂ := inferInstance
local instance : CompactSpace G₂ := inferInstance

private def finiteRep : Rep (ZMod 3) G₂ :=
  Rep.trivial (ZMod 3) G₂ (ZMod 3)

set_option linter.style.haveILetI false in
private def finiteLevels : LevelCompact finiteRep := by
  letI : Finite finiteRep := by
    change Finite (ZMod 3)
    infer_instance
  exact
    { topology := fun _ ↦ ⊥
      compact := by
        intro U
        letI : TopologicalSpace (openSubgroupInvariants finiteRep U) := ⊥
        letI : Finite (openSubgroupInvariants finiteRep U) :=
          Finite.of_injective Subtype.val Subtype.val_injective
        infer_instance
      t2 := by
        intro U
        letI : TopologicalSpace (openSubgroupInvariants finiteRep U) := ⊥
        letI : DiscreteTopology (openSubgroupInvariants finiteRep U) := ⟨rfl⟩
        infer_instance
      topologicalAddGroup := by
        intro U
        letI : TopologicalSpace (openSubgroupInvariants finiteRep U) := ⊥
        letI : DiscreteTopology (openSubgroupInvariants finiteRep U) := ⟨rfl⟩
        infer_instance
      continuous_transport := by
        intro U V _ _
        letI : TopologicalSpace (openSubgroupInvariants finiteRep U) := ⊥
        letI : TopologicalSpace (openSubgroupInvariants finiteRep V) := ⊥
        letI : DiscreteTopology (openSubgroupInvariants finiteRep U) := ⟨rfl⟩
        exact continuous_of_discreteTopology }

private def finiteObject : LevelCompactRep (ZMod 3) G₂ :=
  ⟨finiteRep, finiteLevels⟩

set_option linter.style.haveILetI false in
/-- Scalar two is a genuine continuous coefficient morphism, not identity. -/
private def scalarTwo : finiteObject ⟶ finiteObject where
  hom := (Rep.trivialFunctor (ZMod 3) G₂).map
    (ModuleCat.ofHom ((2 : ZMod 3) • (LinearMap.id : ZMod 3 →ₗ[ZMod 3] ZMod 3)))
  continuous_invariants := by
    intro U
    letI : TopologicalSpace (openSubgroupInvariants finiteObject.rep U) :=
      finiteObject.levelCompact.topology U
    letI : DiscreteTopology (openSubgroupInvariants finiteObject.rep U) := ⟨rfl⟩
    exact continuous_of_discreteTopology

private theorem scalarTwo_ne_id : scalarTwo ≠ 𝟙 finiteObject := by
  intro h
  have hv := congrArg (fun φ : finiteObject ⟶ finiteObject ↦
    φ.hom (1 : ZMod 3)) h
  change (2 : ZMod 3) = 1 at hv
  exact (by decide : (2 : ZMod 3) ≠ 1) hv

example : scalarTwo ≠ 𝟙 finiteObject := scalarTwo_ne_id

private def properLevel : OpenNormalSubgroup G₂ :=
  ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩

private def fullLevel : OpenNormalSubgroup G₂ :=
  ⟨⊤, inferInstance⟩

private theorem properLevel_lt_fullLevel : properLevel < fullLevel := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

private instance : Fintype (fullLevel.toSubgroup.map
    (QuotientGroup.mk' properLevel.toSubgroup)) := Fintype.ofFinite _

private def generator : openSubgroupInvariants finiteRep properLevel.toOpenSubgroup :=
  ⟨(1 : ZMod 3), by intro _; change (1 : ZMod 3) = 1; rfl⟩

example : LevelCompactRep.finiteCoinvariantsMap scalarTwo properLevel
      (LevelCompact.finiteCoinvariantsMk finiteRep finiteLevels properLevel generator) =
    LevelCompact.finiteCoinvariantsMk finiteRep finiteLevels properLevel
      (LevelCompactRep.mapInvariants scalarTwo properLevel.toOpenSubgroup generator) :=
  LevelCompactRep.finiteCoinvariantsMap_mk scalarTwo properLevel generator

example (x : LevelCompact.finiteCoinvariants finiteRep finiteLevels properLevel) :
    LevelCompact.normFromFiniteCoinvariants finiteRep finiteLevels properLevel
        (LevelCompactRep.finiteCoinvariantsMap scalarTwo properLevel x) =
      LevelCompactRep.groupMap scalarTwo ⊤
        (LevelCompact.normFromFiniteCoinvariants finiteRep finiteLevels properLevel x) :=
  LevelCompactRep.normFromFiniteCoinvariants_naturality scalarTwo properLevel x

example : LevelCompactRep.finiteCoinvariantsMap (𝟙 finiteObject) properLevel = 𝟙 _ :=
  LevelCompactRep.finiteCoinvariantsMap_id finiteObject properLevel

example : LevelCompactRep.finiteTateNegOneMap (scalarTwo ≫ scalarTwo) properLevel =
    LevelCompactRep.finiteTateNegOneMap scalarTwo properLevel ≫
      LevelCompactRep.finiteTateNegOneMap scalarTwo properLevel :=
  LevelCompactRep.finiteTateNegOneMap_comp scalarTwo scalarTwo properLevel

example : LevelCompactRep.finiteCoinvariantsMap scalarTwo properLevel ≫
      LevelCompact.finiteCoinvariantDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) =
    LevelCompact.finiteCoinvariantDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) ≫
      LevelCompactRep.finiteCoinvariantsMap scalarTwo fullLevel :=
  LevelCompactRep.finiteCoinvariantsMap_deflation scalarTwo properLevel
    fullLevel (le_of_lt properLevel_lt_fullLevel)

example : LevelCompactRep.finiteTateNegOneMap scalarTwo properLevel ≫
      LevelCompact.finiteTateNegOneDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) =
    LevelCompact.finiteTateNegOneDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) ≫
      LevelCompactRep.finiteTateNegOneMap scalarTwo fullLevel :=
  LevelCompactRep.finiteTateNegOneMap_deflation scalarTwo properLevel
    fullLevel (le_of_lt properLevel_lt_fullLevel)

example : LevelCompactRep.finiteTateZeroMap scalarTwo properLevel ≫
      LevelCompact.finiteTateZeroDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) =
    LevelCompact.finiteTateZeroDeflation finiteRep finiteLevels properLevel
        fullLevel (le_of_lt properLevel_lt_fullLevel) ≫
      LevelCompactRep.finiteTateZeroMap scalarTwo fullLevel :=
  LevelCompactRep.finiteTateZeroMap_deflation scalarTwo properLevel
    fullLevel (le_of_lt properLevel_lt_fullLevel)

end CGCExamples.CompactExceptionalTateCoefficientMapsNative
