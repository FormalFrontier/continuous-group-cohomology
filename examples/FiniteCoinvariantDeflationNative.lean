/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.FiniteCoinvariantDeflation
public import Mathlib.Data.ZMod.Basic

/-!
# Public client for continuous finite coinvariant deflation

These examples use the actual algebraic deflation on compact coinvariants and
exercise its representative formula, common-target norm square, and level laws.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

example (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : finiteCoinvariants A (L := L) S) :
    finiteCoinvariantDeflation A L S T hST x =
      finiteNegativeDeflationCoinvariants A S.toSubgroup T.toSubgroup hST x :=
  rfl

example (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    finiteCoinvariantDeflation A L S T hST (finiteCoinvariantsMk A L S x) =
      finiteCoinvariantsMk A L T
        ((nestedQuotientInvariantsRepIso A S.toSubgroup T.toSubgroup hST).hom
          (FiniteGroupTateCohomology.quotientNorm
            (A.quotientToInvariants S.toSubgroup)
            (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))
            (Representation.Coinvariants.mk
              ((A.quotientToInvariants S.toSubgroup).ρ.comp
                (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)).subtype) x))) :=
  finiteCoinvariantDeflation_mk A L S T hST x

example (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : finiteCoinvariants A (L := L) S) :
    normFromFiniteCoinvariants A L T (finiteCoinvariantDeflation A L S T hST x) =
      normFromFiniteCoinvariants A L S x :=
  normFromFiniteCoinvariants_finiteCoinvariantDeflation A L S T hST x

example (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantDeflation A L S S le_rfl = 𝟙 _ :=
  finiteCoinvariantDeflation_refl A L S

example (S T U : OpenNormalSubgroup G) (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantDeflation A L S T hST ≫
        finiteCoinvariantDeflation A L T U hTU =
      finiteCoinvariantDeflation A L S U (hST.trans hTU) :=
  finiteCoinvariantDeflation_comp A L S T U hST hTU

set_option linter.style.haveILetI false in
private def finiteDiscreteLevelCompact (A : Rep.{u} R G) [Finite A] :
    LevelCompact A where
  topology := fun _ ↦ ⊥
  compact := by
    intro U
    letI : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    letI : Finite (openSubgroupInvariants A U) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    infer_instance
  t2 := by
    intro U
    letI : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    letI : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    infer_instance
  topologicalAddGroup := by
    intro U
    letI : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    letI : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    infer_instance
  continuous_transport := by
    intro U V _ _
    letI : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    letI : TopologicalSpace (openSubgroupInvariants A V) := ⊥
    letI : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    exact continuous_of_discreteTopology

section FiniteExample

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
local instance : IsTopologicalGroup (Multiplicative (ZMod 2)) := inferInstance
local instance : CompactSpace (Multiplicative (ZMod 2)) := inferInstance

private def cyclicTwoFiniteRep : Rep (ZMod 3) (Multiplicative (ZMod 2)) :=
  Rep.trivial (ZMod 3) (Multiplicative (ZMod 2)) (ZMod 3)

private def cyclicTwoFiniteLevels : LevelCompact cyclicTwoFiniteRep := by
  letI : Finite cyclicTwoFiniteRep := by
    change Finite (ZMod 3)
    infer_instance
  exact finiteDiscreteLevelCompact cyclicTwoFiniteRep

private def cyclicTwoSmall : OpenNormalSubgroup (Multiplicative (ZMod 2)) :=
  ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩

private def cyclicTwoBig : OpenNormalSubgroup (Multiplicative (ZMod 2)) :=
  ⟨⊤, inferInstance⟩

private lemma cyclicTwoSmall_le_big : cyclicTwoSmall ≤ cyclicTwoBig := by
  intro g hg
  exact Subgroup.mem_top g

private def cyclicTwoGenerator :
    openSubgroupInvariants cyclicTwoFiniteRep cyclicTwoSmall.toOpenSubgroup := by
  refine ⟨(1 : ZMod 3), ?_⟩
  ·
    intro g
    change (1 : ZMod 3) = 1
    rfl

example : cyclicTwoGenerator ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  change (1 : ZMod 3) = 0 at hv
  exact one_ne_zero hv

private instance : Fintype ((cyclicTwoBig.toSubgroup).map
    (QuotientGroup.mk' cyclicTwoSmall.toSubgroup)) :=
  Fintype.ofFinite _

example :
    normFromFiniteCoinvariants cyclicTwoFiniteRep cyclicTwoFiniteLevels
        cyclicTwoBig
        (finiteCoinvariantDeflation cyclicTwoFiniteRep cyclicTwoFiniteLevels
          cyclicTwoSmall cyclicTwoBig cyclicTwoSmall_le_big
          (finiteCoinvariantsMk cyclicTwoFiniteRep cyclicTwoFiniteLevels
            cyclicTwoSmall cyclicTwoGenerator)) =
      relativeNorm cyclicTwoFiniteRep ⊤ cyclicTwoSmall.toOpenSubgroup
        le_top cyclicTwoGenerator := by
  rw [normFromFiniteCoinvariants_finiteCoinvariantDeflation]
  exact normFromFiniteCoinvariants_mk cyclicTwoFiniteRep cyclicTwoFiniteLevels
    cyclicTwoSmall cyclicTwoGenerator

end FiniteExample

end ContinuousGroupCohomology.LevelCompact
