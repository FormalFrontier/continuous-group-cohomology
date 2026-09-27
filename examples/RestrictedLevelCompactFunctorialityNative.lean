/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Native adaptation: hive-request-15de2e8fb886b8dfbc8a9e6096f6f9069aa1bc0c
  (5a9907b2-d133-462a-bc07-ae576b5820b6)
Native norm diagrams: hive-request-c53967c3623f44154013d9f5cd5cd87a248da315
  (fae3b9d5-de01-4c04-b9c0-a63cc9cafb6e)
-/
module

public import ContinuousGroupCohomology.RestrictedLevelCompactFunctoriality

/-!
# Restricted level-compact coefficient maps: public API client

Exercises native compact-group maps, their norm squares and natural
transformations for arbitrary morphisms preserving chosen restricted systems.
Full and universal-norm specializations need no extra preservation assumption.
-/

public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory ContinuousGroupCohomology

noncomputable section

namespace CGCExamples.RestrictedLevelCompactFunctorialityNative

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable {A B C : RestrictedLevelCompactRep R G}
variable (f : A ⟶ B) (g : B ⟶ C)
variable (U V : OpenNormalSubgroup G) (hVU : V ≤ U)

example (x : A.system.coefficients U) :
    (RestrictedLevelCompactRep.coefficientMap f U x :
        openSubgroupInvariants B.rep U.toOpenSubgroup) =
      LevelCompactRep.mapInvariants f.hom U.toOpenSubgroup x :=
  RestrictedLevelCompactRep.coefficientMap_coe f U x

example : @Continuous (A.system.coefficients U) (B.system.coefficients U)
    (A.system.topology U) (B.system.topology U)
    (RestrictedLevelCompactRep.coefficientMap f U) :=
  RestrictedLevelCompactRep.continuous_coefficientMap f U

example : RestrictedLevelCompactRep.coefficientMap (𝟙 A) U = LinearMap.id :=
  RestrictedLevelCompactRep.coefficientMap_id A U

example : RestrictedLevelCompactRep.coefficientMap (f ≫ g) U =
    (RestrictedLevelCompactRep.coefficientMap g U).comp
      (RestrictedLevelCompactRep.coefficientMap f U) :=
  RestrictedLevelCompactRep.coefficientMap_comp f g U

example (x : A.system.coefficients V) :
    RestrictedLevelCompactRep.coefficientMap f U
        (A.system.relativeNorm U V hVU x) =
      B.system.relativeNorm U V hVU
        (RestrictedLevelCompactRep.coefficientMap f V x) :=
  RestrictedLevelCompactRep.coefficientMap_relativeNorm f U V hVU x

example : (B.system.relativeNorm U V hVU).comp
      (RestrictedLevelCompactRep.coefficientMap f V) =
    (RestrictedLevelCompactRep.coefficientMap f U).comp
      (A.system.relativeNorm U V hVU) :=
  RestrictedLevelCompactRep.coefficientMap_relativeNorm_linear f U V hVU

example (x : A.system.coefficients U) :
    RestrictedLevelCompactRep.groupMap f U x =
      RestrictedLevelCompactRep.coefficientMap f U x :=
  RestrictedLevelCompactRep.groupMap_apply f U x

example : RestrictedLevelCompactRep.groupMap (𝟙 A) U =
    𝟙 (A.system.group U) :=
  RestrictedLevelCompactRep.groupMap_id A U

example : RestrictedLevelCompactRep.groupMap (f ≫ g) U =
    RestrictedLevelCompactRep.groupMap f U ≫
      RestrictedLevelCompactRep.groupMap g U :=
  RestrictedLevelCompactRep.groupMap_comp f g U

example : A.system.relativeNormHom U V hVU ≫
      RestrictedLevelCompactRep.groupMap f U =
    RestrictedLevelCompactRep.groupMap f V ≫
      B.system.relativeNormHom U V hVU :=
  RestrictedLevelCompactRep.groupMap_relativeNorm f U V hVU

example (h : V ⟶ U) :
    (RestrictedLevelCompactRep.restrictedNormDiagram A).map h =
      A.system.relativeNormHom U V (leOfHom h) :=
  RestrictedLevelCompactRep.restrictedNormDiagram_map A h

example : (RestrictedLevelCompactRep.restrictedNormDiagramFunctor.map f).app U =
    RestrictedLevelCompactRep.groupMap f U :=
  RestrictedLevelCompactRep.restrictedNormDiagramFunctor_map_app f U

example : RestrictedLevelCompactRep.restrictedNormDiagramFunctor.map (𝟙 A) = 𝟙 _ :=
  (RestrictedLevelCompactRep.restrictedNormDiagramFunctor (R := R) (G := G)).map_id A

example : RestrictedLevelCompactRep.restrictedNormDiagramFunctor.map (f ≫ g) =
    RestrictedLevelCompactRep.restrictedNormDiagramFunctor.map f ≫
      RestrictedLevelCompactRep.restrictedNormDiagramFunctor.map g :=
  (RestrictedLevelCompactRep.restrictedNormDiagramFunctor (R := R) (G := G)).map_comp f g

variable {D E : LevelCompactRep.{u, u, u} R G} (k : D ⟶ E)

example : RestrictedLevelCompactRep.full D ⟶ RestrictedLevelCompactRep.full E :=
  (RestrictedLevelCompactRep.fullFunctor (R := R) (G := G)).map k

example :
    ((RestrictedLevelCompactRep.restrictedNormDiagramFunctor (R := R) (G := G)).map
      ((RestrictedLevelCompactRep.fullFunctor (R := R) (G := G)).map k)).app U =
        RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.fullFunctor (R := R) (G := G)).map k) U :=
  RestrictedLevelCompactRep.restrictedNormDiagramFunctor_map_app _ U

example :
    (RestrictedLevelCompactRep.full D).system.relativeNormHom U V hVU ≫
        RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.fullFunctor (R := R) (G := G)).map k) U =
      RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.fullFunctor (R := R) (G := G)).map k) V ≫
        (RestrictedLevelCompactRep.full E).system.relativeNormHom U V hVU :=
  RestrictedLevelCompactRep.groupMap_relativeNorm _ U V hVU

example (x : openSubgroupInvariants D.rep U.toOpenSubgroup)
    (hx : x ∈ LevelCompact.universalNormSubmodule D.rep U) :
    LevelCompactRep.mapInvariants k U.toOpenSubgroup x ∈
      LevelCompact.universalNormSubmodule E.rep U :=
  RestrictedLevelCompactRep.mapInvariants_mem_universalNorm k U hx

example (x : (RestrictedLevelCompactRep.universalNorm D).system.coefficients U) :
    ((RestrictedLevelCompactRep.coefficientMap
          ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k)
          U x).1 : openSubgroupInvariants E.rep U.toOpenSubgroup) =
      LevelCompactRep.mapInvariants k U.toOpenSubgroup x.1 := by
  rfl

example : @Continuous
    ((RestrictedLevelCompactRep.universalNorm D).system.coefficients U)
    ((RestrictedLevelCompactRep.universalNorm E).system.coefficients U)
    ((RestrictedLevelCompactRep.universalNorm D).system.topology U)
    ((RestrictedLevelCompactRep.universalNorm E).system.topology U)
    (RestrictedLevelCompactRep.coefficientMap
      ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k)
        U) :=
  RestrictedLevelCompactRep.continuous_coefficientMap _ U

example : (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map
    (𝟙 D) =
    𝟙 (RestrictedLevelCompactRep.universalNorm D) :=
  (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map_id D

example {F : LevelCompactRep.{u, u, u} R G} (ell : E ⟶ F) :
    (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map
        (k ≫ ell) =
      (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k ≫
        (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map ell :=
  (RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map_comp k ell

example (x : (RestrictedLevelCompactRep.universalNorm D).system.coefficients V) :
    RestrictedLevelCompactRep.coefficientMap
        ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k) U
        ((RestrictedLevelCompactRep.universalNorm D).system.relativeNorm U V hVU x) =
      (RestrictedLevelCompactRep.universalNorm E).system.relativeNorm U V hVU
        (RestrictedLevelCompactRep.coefficientMap
          ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k)
            V x) :=
  RestrictedLevelCompactRep.coefficientMap_relativeNorm _ U V hVU x

example :
    (RestrictedLevelCompactRep.universalNorm D).system.relativeNormHom U V hVU ≫
        RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k) U =
      RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k) V ≫
        (RestrictedLevelCompactRep.universalNorm E).system.relativeNormHom U V hVU :=
  RestrictedLevelCompactRep.groupMap_relativeNorm _ U V hVU

example :
    ((RestrictedLevelCompactRep.restrictedNormDiagramFunctor (R := R) (G := G)).map
      ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k)).app U =
        RestrictedLevelCompactRep.groupMap
          ((RestrictedLevelCompactRep.universalNormFunctor (R := R) (G := G)).map k) U :=
  RestrictedLevelCompactRep.restrictedNormDiagramFunctor_map_app _ U

end CGCExamples.RestrictedLevelCompactFunctorialityNative
