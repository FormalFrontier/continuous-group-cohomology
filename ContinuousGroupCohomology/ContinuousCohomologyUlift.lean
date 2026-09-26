/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.HomogeneousCochainsUlift

/-!
# Universe lifts of continuous cohomology

This file compares continuous cohomology with the continuous cohomology of a
universe-raised topological representation. The result uses one common small
universe, matching the boundary of mathlib's recursive homogeneous-cochain API.
-/

set_option warningAsError true

@[expose] public section

universe u v

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In one common small universe, continuous cohomology commutes with raising
the acting group and coefficient carrier. -/
noncomputable def continuousCohomologyUliftIsoSameUniverse
    (X : TopRep.{v} k G) (n : ℕ) :
    (TopModuleCat.uliftFunctor.{v, v} k).obj (continuousCohomology n X) ≅
      continuousCohomology n (TopRep.ulift.{u, v, v, v, v} X) :=
  ((X.homogeneousCochains.sc n).mapHomologyIso
      (TopModuleCat.uliftFunctor.{v, v} k)).symm ≪≫
    HomologicalComplex.homologyMapIso
      (homogeneousCochainsUliftIsoSameUniverse X) n

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

/-- The same-universe continuous-cohomology comparison is natural in the
coefficient representation. -/
@[reassoc]
lemma continuousCohomologyUliftIsoSameUniverse_naturality
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) (n : ℕ) :
    (TopModuleCat.uliftFunctor.{v, v} k).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f n) ≫
        (continuousCohomologyUliftIsoSameUniverse Y n).hom =
      (continuousCohomologyUliftIsoSameUniverse X n).hom ≫
        ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v} G))
          (TopRep.uliftMap.{u, v, v, v, v} f) n := by
  have hhom := congrArg (fun q => HomologicalComplex.homologyMap q n)
    (homogeneousCochainsUliftIsoSameUniverse_naturality f)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hhom
  let f' : TopRep.res (ContinuousMonoidHom.id G) X ⟶ Y := f
  let uf : TopRep.res (ContinuousMonoidHom.id (ULift.{v} G))
      (TopRep.ulift.{u, v, v, v, v} X) ⟶
        TopRep.ulift.{u, v, v, v, v} Y :=
    TopRep.uliftMap.{u, v, v, v, v} f
  change (TopModuleCat.uliftFunctor.{v, v} k).map
      (ContinuousCohomology.map (ContinuousMonoidHom.id G) f' n) ≫
        (continuousCohomologyUliftIsoSameUniverse Y n).hom =
    (continuousCohomologyUliftIsoSameUniverse X n).hom ≫
      ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v} G)) uf n
  unfold continuousCohomologyUliftIsoSameUniverse
  dsimp only [Iso.trans, Iso.symm, HomologicalComplex.homologyMapIso,
    ContinuousCohomology.map, continuousCohomology,
    HomologicalComplex.homology, HomologicalComplex.homologyMap]
  erw [ShortComplex.mapHomologyIso_inv_naturality_assoc]
  erw [hhom]
  erw [Category.assoc]

/-- Transport a coefficient map through the same-universe continuous-
cohomology comparison. -/
noncomputable def continuousCohomologyUliftMapSameUniverse
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) (n : ℕ) :
    continuousCohomology n (TopRep.ulift.{u, v, v, v, v} X) ⟶
      continuousCohomology n (TopRep.ulift.{u, v, v, v, v} Y) :=
  (continuousCohomologyUliftIsoSameUniverse X n).inv ≫
    (TopModuleCat.uliftFunctor.{v, v} k).map
      (ContinuousCohomology.map (ContinuousMonoidHom.id G) f n) ≫
    (continuousCohomologyUliftIsoSameUniverse Y n).hom

/-- The transported same-universe coefficient map is exactly mathlib's native
continuous-cohomology map on the raised representations. -/
@[simp]
lemma continuousCohomologyUliftMapSameUniverse_eq_map
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) (n : ℕ) :
    continuousCohomologyUliftMapSameUniverse f n =
      ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v} G))
        (TopRep.uliftMap.{u, v, v, v, v} f) n := by
  rw [← cancel_epi (continuousCohomologyUliftIsoSameUniverse X n).hom]
  simpa only [continuousCohomologyUliftMapSameUniverse,
    Iso.hom_inv_id_assoc] using
      continuousCohomologyUliftIsoSameUniverse_naturality f n

/-- The transported same-universe coefficient map preserves identities. -/
@[simp]
lemma continuousCohomologyUliftMapSameUniverse_id
    (X : TopRep.{v} k G) (n : ℕ) :
    continuousCohomologyUliftMapSameUniverse (𝟙 X) n = 𝟙 _ := by
  rw [continuousCohomologyUliftMapSameUniverse_eq_map]
  have h : TopRep.uliftMap.{u, v, v, v, v} (𝟙 X) =
      𝟙 (TopRep.ulift.{u, v, v, v, v} X) :=
    (TopRep.uliftFunctor.{u, v, v, v, v} (k := k) (G := G)).map_id X
  rw [h, ContinuousCohomology.map_id]

/-- The transported same-universe coefficient map preserves composition. -/
@[reassoc]
lemma continuousCohomologyUliftMapSameUniverse_comp
    {X Y Z : TopRep.{v} k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    continuousCohomologyUliftMapSameUniverse (f ≫ g) n =
      continuousCohomologyUliftMapSameUniverse f n ≫
        continuousCohomologyUliftMapSameUniverse g n := by
  rw [continuousCohomologyUliftMapSameUniverse_eq_map,
    continuousCohomologyUliftMapSameUniverse_eq_map,
    continuousCohomologyUliftMapSameUniverse_eq_map]
  have h : TopRep.uliftMap.{u, v, v, v, v} (f ≫ g) =
      TopRep.uliftMap.{u, v, v, v, v} f ≫
        TopRep.uliftMap.{u, v, v, v, v} g :=
    (TopRep.uliftFunctor.{u, v, v, v, v} (k := k) (G := G)).map_comp f g
  rw [h]
  have hmap := ContinuousCohomology.map_comp
    (X := TopRep.ulift.{u, v, v, v, v} X)
    (Y := TopRep.ulift.{u, v, v, v, v} Y)
    (Z := TopRep.ulift.{u, v, v, v, v} Z)
    (ContinuousMonoidHom.id (ULift.{v} G))
    (ContinuousMonoidHom.id (ULift.{v} G))
    (TopRep.uliftMap.{u, v, v, v, v} f)
    (TopRep.uliftMap.{u, v, v, v, v} g) n
  have hres : (TopRep.resFunctor
      ((ContinuousMonoidHom.id (ULift.{v} G)) : ULift.{v} G →* ULift.{v} G)).map
        (TopRep.uliftMap.{u, v, v, v, v} f) =
      TopRep.uliftMap.{u, v, v, v, v} f := by
    ext x
    rfl
  erw [hres] at hmap
  exact hmap

end TopRep
