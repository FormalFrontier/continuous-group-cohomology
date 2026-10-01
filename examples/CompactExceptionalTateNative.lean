/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactExceptionalTateLimits
public import Mathlib.Data.ZMod.Basic

/-!
# Clients for compact exceptional Tate diagrams and limits

Exercise actual stage maps, composable two- and three-level arrows, additive
natural-isomorphism components and naturality, and compact-limit projections
and eventual ranges using public imports. A two-element finite profinite group
provides a proper open normal level, without any nonvanishing claim.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace CGCExamples.CompactExceptionalTateNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

example (S : OpenNormalSubgroup G) :
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).obj S =
      LevelCompact.finiteTateNegOne A L S := rfl

example (S : OpenNormalSubgroup G) :
    (LevelCompact.compactFiniteZeroDeflationDiagram A L).obj S =
      LevelCompact.finiteTateZero A L S := rfl

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map f =
      (by
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact LevelCompact.finiteTateNegOneDeflation A L S T (leOfHom f)) := rfl

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    (LevelCompact.compactFiniteZeroDeflationDiagram A L).map f =
      (by
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact LevelCompact.finiteTateZeroDeflation A L S T (leOfHom f)) := rfl

example {S T U : OpenNormalSubgroup G} (f : S ⟶ T) (g : T ⟶ U) :
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map f ≫
        (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map g =
      (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map (f ≫ g) :=
  ((LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map_comp f g).symm

example {S T U : OpenNormalSubgroup G} (f : S ⟶ T) (g : T ⟶ U) :
    (LevelCompact.compactFiniteZeroDeflationDiagram A L).map f ≫
        (LevelCompact.compactFiniteZeroDeflationDiagram A L).map g =
      (LevelCompact.compactFiniteZeroDeflationDiagram A L).map (f ≫ g) :=
  ((LevelCompact.compactFiniteZeroDeflationDiagram A L).map_comp f g).symm

example (S : OpenNormalSubgroup G) :
    (LevelCompact.finiteNegativeOneDeflationAdditiveDiagramIso A L).hom.app S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (LevelCompact.tateCohomologyNegOneAddEquivFiniteTate A L S).toAddCommGrpIso.hom) :=
  rfl

example (S : OpenNormalSubgroup G) :
    (LevelCompact.finiteZeroDeflationAdditiveDiagramIso A L).hom.app S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (LevelCompact.tateCohomologyZeroAddEquivFiniteTate A L S).toAddCommGrpIso.hom) :=
  rfl

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    ((finiteNegativeOneDeflationDiagram A ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f) ≫
        (LevelCompact.finiteNegativeOneDeflationAdditiveDiagramIso A L).hom.app T =
      (LevelCompact.finiteNegativeOneDeflationAdditiveDiagramIso A L).hom.app S ≫
        ((LevelCompact.compactFiniteNegativeOneDeflationDiagram A L ⋙
          forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u}).map f) :=
  (LevelCompact.finiteNegativeOneDeflationAdditiveDiagramIso A L).hom.naturality f

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    ((finiteZeroDeflationDiagram A ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f) ≫
        (LevelCompact.finiteZeroDeflationAdditiveDiagramIso A L).hom.app T =
      (LevelCompact.finiteZeroDeflationAdditiveDiagramIso A L).hom.app S ≫
        ((LevelCompact.compactFiniteZeroDeflationDiagram A L ⋙
          forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u}).map f) :=
  (LevelCompact.finiteZeroDeflationAdditiveDiagramIso A L).hom.naturality f

example (S : OpenNormalSubgroup G) :
    LevelCompact.compactNegativeOneTateLimit A L ⟶
      LevelCompact.finiteTateNegOne A L S :=
  LevelCompact.compactNegativeOneTateLimitπ A L S

example (S : OpenNormalSubgroup G) :
    LevelCompact.compactZeroTateLimit A L ⟶
      LevelCompact.finiteTateZero A L S :=
  LevelCompact.compactZeroTateLimitπ A L S

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

/-- The public bridge lets an ordinary module client state the categorical
limit-map equation using the named degree-`-1` projections. -/
theorem negativeOne_limit_map_named_projection
    (B : Rep.{u} R G) (M : LevelCompact B)
    (f : LevelCompact.compactFiniteNegativeOneDeflationDiagram A L ⟶
      LevelCompact.compactFiniteNegativeOneDeflationDiagram B M)
    (S : OpenNormalSubgroup G) :
    lim.map f ≫ LevelCompact.compactNegativeOneTateLimitπ B M S =
      LevelCompact.compactNegativeOneTateLimitπ A L S ≫ f.app S := by
  rw [LevelCompact.compactNegativeOneTateLimitπ_eq_limit_π,
    LevelCompact.compactNegativeOneTateLimitπ_eq_limit_π]
  exact limit.map_π f S

/-- The same ordinary-import client equation for degree-zero projections. -/
theorem zero_limit_map_named_projection
    (B : Rep.{u} R G) (M : LevelCompact B)
    (f : LevelCompact.compactFiniteZeroDeflationDiagram A L ⟶
      LevelCompact.compactFiniteZeroDeflationDiagram B M)
    (S : OpenNormalSubgroup G) :
    lim.map f ≫ LevelCompact.compactZeroTateLimitπ B M S =
      LevelCompact.compactZeroTateLimitπ A L S ≫ f.app S := by
  rw [LevelCompact.compactZeroTateLimitπ_eq_limit_π,
    LevelCompact.compactZeroTateLimitπ_eq_limit_π]
  exact limit.map_π f S

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    LevelCompact.compactNegativeOneTateLimitπ A L S ≫
        (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map f =
      LevelCompact.compactNegativeOneTateLimitπ A L T :=
  LevelCompact.compactNegativeOneTateLimitπ_naturality A L f

example {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    LevelCompact.compactZeroTateLimitπ A L S ≫
        (LevelCompact.compactFiniteZeroDeflationDiagram A L).map f =
      LevelCompact.compactZeroTateLimitπ A L T :=
  LevelCompact.compactZeroTateLimitπ_naturality A L f

example (S : OpenNormalSubgroup G) :
    Set.range (LevelCompact.compactNegativeOneTateLimitπ A L S) =
      ((LevelCompact.compactFiniteNegativeOneDeflationDiagram A L) ⋙
        forget CompHausAddCommGrp.{u}).eventualRange S :=
  LevelCompact.compactNegativeOneTateLimitπ_range_eq_eventualRange A L S

example (S : OpenNormalSubgroup G) :
    Set.range (LevelCompact.compactZeroTateLimitπ A L S) =
      ((LevelCompact.compactFiniteZeroDeflationDiagram A L) ⋙
        forget CompHausAddCommGrp.{u}).eventualRange S :=
  LevelCompact.compactZeroTateLimitπ_range_eq_eventualRange A L S

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

private abbrev twoElementGroup : ProfiniteGrp :=
  ProfiniteGrp.of (Multiplicative (ZMod 2))

/-- A proper open normal subgroup of a nontrivial finite profinite group. -/
private def properLevel : OpenNormalSubgroup twoElementGroup :=
  ⟨⟨⊥, isOpen_discrete _⟩, inferInstance⟩

private def topLevel : OpenNormalSubgroup twoElementGroup :=
  ⟨⊤, inferInstance⟩

private theorem properLevel_lt_top : properLevel < topLevel := by
  change (⊥ : Subgroup (Multiplicative (ZMod 2))) < ⊤
  exact bot_lt_top

example (A : Rep (ZMod 3) twoElementGroup) (L : LevelCompact A) :
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).obj properLevel =
      LevelCompact.finiteTateNegOne A L properLevel := rfl

example (A : Rep (ZMod 3) twoElementGroup) (L : LevelCompact A) :
    (LevelCompact.compactFiniteZeroDeflationDiagram A L).obj properLevel =
      LevelCompact.finiteTateZero A L properLevel := rfl

example (A : Rep (ZMod 3) twoElementGroup) (L : LevelCompact A) :
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map
        (homOfLE (le_of_lt properLevel_lt_top)) =
      (by
        let _ : Fintype (topLevel.toSubgroup.map (QuotientGroup.mk' properLevel.toSubgroup)) :=
          Fintype.ofFinite _
        exact LevelCompact.finiteTateNegOneDeflation A L properLevel topLevel
          (le_of_lt properLevel_lt_top)) := rfl

end CGCExamples.CompactExceptionalTateNative
