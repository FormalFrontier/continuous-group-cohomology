/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Native adaptation: hive-request-ec9bf361966f9bc5d2a422dd9e00cf39656f7a7c
  (cd42fd3f-1546-42a4-b934-06eb5087858a)
Named projections: hive-request-c53967c3623f44154013d9f5cd5cd87a248da315
  (fae3b9d5-de01-4c04-b9c0-a63cc9cafb6e)
-/
module

public import ContinuousGroupCohomology.CompactExceptionalTateLimitFunctoriality

/-!
# Clients for compact exceptional Tate limit functoriality

These examples exercise actual level-compact coefficient morphisms, their
finite-stage components and induced maps on the published compact limits.
They do not assert that a particular coefficient morphism acts nontrivially
on a Tate stage or limit.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace CGCExamples.CompactExceptionalTateLimitFunctorialityNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable {A B C : LevelCompactRep.{u, u, u} R G}
variable (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G)

example : A ⟶ B := f

example : (LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor
    (R := R) (G := G)).obj A =
      LevelCompact.compactFiniteNegativeOneDeflationDiagram A.rep A.levelCompact :=
  LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor_obj A

example : (LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor
    (R := R) (G := G)).obj A =
      LevelCompact.compactFiniteZeroDeflationDiagram A.rep A.levelCompact :=
  LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor_obj A

example : (LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor.map f).app S =
    LevelCompactRep.finiteTateNegOneMap f S :=
  LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor_map_app f S

example : (LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor.map f).app S =
    LevelCompactRep.finiteTateZeroMap f S :=
  LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor_map_app f S

example : (LevelCompactRep.compactNegativeOneTateLimitFunctor
    (R := R) (G := G)).obj A =
      LevelCompact.compactNegativeOneTateLimit A.rep A.levelCompact :=
  LevelCompactRep.compactNegativeOneTateLimitFunctor_obj A

example : (LevelCompactRep.compactZeroTateLimitFunctor
    (R := R) (G := G)).obj A =
      LevelCompact.compactZeroTateLimit A.rep A.levelCompact :=
  LevelCompactRep.compactZeroTateLimitFunctor_obj A

example : Continuous (LevelCompactRep.compactNegativeOneTateLimitFunctor.map f) :=
  (LevelCompactRep.compactNegativeOneTateLimitFunctor.map f).hom.continuous

example : Continuous (LevelCompactRep.compactZeroTateLimitFunctor.map f) :=
  (LevelCompactRep.compactZeroTateLimitFunctor.map f).hom.continuous

example : LevelCompactRep.compactNegativeOneTateLimitFunctor.map f ≫
      limit.π (LevelCompact.compactFiniteNegativeOneDeflationDiagram
        B.rep B.levelCompact) S =
    limit.π (LevelCompact.compactFiniteNegativeOneDeflationDiagram
        A.rep A.levelCompact) S ≫
      LevelCompactRep.finiteTateNegOneMap f S :=
  LevelCompactRep.compactNegativeOneTateLimitFunctor_map_π f S

example : LevelCompactRep.compactZeroTateLimitFunctor.map f ≫
      limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
        B.rep B.levelCompact) S =
    limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
        A.rep A.levelCompact) S ≫
      LevelCompactRep.finiteTateZeroMap f S :=
  LevelCompactRep.compactZeroTateLimitFunctor_map_π f S

example : LevelCompactRep.compactNegativeOneTateLimitFunctor.map f ≫
      LevelCompact.compactNegativeOneTateLimitπ B.rep B.levelCompact S =
    LevelCompact.compactNegativeOneTateLimitπ A.rep A.levelCompact S ≫
      LevelCompactRep.finiteTateNegOneMap f S :=
  LevelCompactRep.compactNegativeOneTateLimitFunctor_map_namedπ f S

example : LevelCompactRep.compactZeroTateLimitFunctor.map f ≫
      LevelCompact.compactZeroTateLimitπ B.rep B.levelCompact S =
    LevelCompact.compactZeroTateLimitπ A.rep A.levelCompact S ≫
      LevelCompactRep.finiteTateZeroMap f S :=
  LevelCompactRep.compactZeroTateLimitFunctor_map_namedπ f S

example : LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor.map
      (𝟙 A) = 𝟙 _ :=
  (LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor
    (R := R) (G := G)).map_id A

example : LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor.map
      (f ≫ g) =
    LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor.map f ≫
      LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor.map g :=
  (LevelCompactRep.compactFiniteZeroDeflationDiagramFunctor
    (R := R) (G := G)).map_comp f g

example : LevelCompactRep.compactNegativeOneTateLimitFunctor.map (𝟙 A) = 𝟙 _ :=
  (LevelCompactRep.compactNegativeOneTateLimitFunctor
    (R := R) (G := G)).map_id A

example : LevelCompactRep.compactZeroTateLimitFunctor.map (f ≫ g) =
    LevelCompactRep.compactZeroTateLimitFunctor.map f ≫
      LevelCompactRep.compactZeroTateLimitFunctor.map g :=
  (LevelCompactRep.compactZeroTateLimitFunctor
    (R := R) (G := G)).map_comp f g

end CGCExamples.CompactExceptionalTateLimitFunctorialityNative
