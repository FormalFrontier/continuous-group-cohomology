/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.NonpositiveTateLimits
public import Mathlib.CategoryTheory.Whiskering

/-!
# Coefficient functoriality for nonpositive Tate limits

This file makes the three finite Tate deflation diagrams functorial
in their coefficient representation.  It then postcomposes them with
`TopModuleCat.withModuleTopology` and applies the categorical limit functor.
The resulting morphisms of limits are therefore continuous by construction,
and their compatibility with every stage projection is `limit.map_π`.

The object values are definitionally the diagrams and limits from
`FiniteTateDiagrams` and `NonpositiveTateLimits`.  No replacement topology or
set-theoretic inverse limit is introduced.  This file does not assert
exactness, compactness, or the existence of a completed all-degree profinite
Tate theory.

The current finite-level homology APIs place the coefficient ring, group, and
representation carrier in one universe.  The definitions here retain that
same-universe boundary.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{u}}

/-- The homological finite negative-deflation diagrams, functorial in the
coefficient representation. -/
@[expose] noncomputable def finiteNegativeDeflationDiagramFunctor (n : ℕ) :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ ModuleCat R) where
  obj A := finiteNegativeDeflationDiagram A n
  map {A B} f :=
    { app := fun S =>
        (groupHomology.functor R (G ⧸ S.toSubgroup) n).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f)
      naturality := by
        intro S T hST
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteNegativeDeflation_naturality f S.toSubgroup T.toSubgroup
          (leOfHom hST) n).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    change (groupHomology.functor R (G ⧸ S.toSubgroup) n).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (𝟙 A)) =
      𝟙 ((groupHomology.functor R (G ⧸ S.toSubgroup) n).obj
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).obj A))
    rw [(Rep.quotientToInvariantsFunctor R S.toSubgroup).map_id,
      (groupHomology.functor R (G ⧸ S.toSubgroup) n).map_id]
  map_comp f g := by
    apply NatTrans.ext
    funext S
    change (groupHomology.functor R (G ⧸ S.toSubgroup) n).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (f ≫ g)) =
      (groupHomology.functor R (G ⧸ S.toSubgroup) n).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f) ≫
        (groupHomology.functor R (G ⧸ S.toSubgroup) n).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map g)
    rw [Functor.map_comp, Functor.map_comp]

/-- The finite degree-`-1` deflation diagrams, functorial in the coefficient
representation. -/
@[expose] noncomputable def finiteNegativeOneDeflationDiagramFunctor :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ ModuleCat R) where
  obj A := finiteNegativeOneDeflationDiagram A
  map {A B} f :=
    { app := fun S => by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f)
      naturality := by
        intro S T hST
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteNegativeOneDeflation_naturality f S.toSubgroup T.toSubgroup
          (leOfHom hST)).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    change (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (𝟙 A)) =
      𝟙 ((tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).obj
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).obj A))
    rw [(Rep.quotientToInvariantsFunctor R S.toSubgroup).map_id,
      (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map_id]
  map_comp f g := by
    apply NatTrans.ext
    funext S
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    change (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (f ≫ g)) =
      (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f) ≫
        (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map g)
    rw [Functor.map_comp, Functor.map_comp]

/-- The finite degree-zero deflation diagrams, functorial in the coefficient
representation. -/
@[expose] noncomputable def finiteZeroDeflationDiagramFunctor :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ ModuleCat R) where
  obj A := finiteZeroDeflationDiagram A
  map {A B} f :=
    { app := fun S => by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f)
      naturality := by
        intro S T hST
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteZeroDeflation_naturality f S.toSubgroup T.toSubgroup
          (leOfHom hST)).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    change (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (𝟙 A)) =
      𝟙 ((tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).obj
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).obj A))
    rw [(Rep.quotientToInvariantsFunctor R S.toSubgroup).map_id,
      (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map_id]
  map_comp f g := by
    apply NatTrans.ext
    funext S
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    change (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map (f ≫ g)) =
      (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f) ≫
        (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map g)
    rw [Functor.map_comp, Functor.map_comp]

/-- The topologized homological negative-deflation diagrams, functorial in the
coefficient representation. -/
@[expose] noncomputable def topologicalFiniteNegativeDeflationDiagramFunctor (n : ℕ) :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ TopModuleCat.{u} R) :=
  finiteNegativeDeflationDiagramFunctor n ⋙
    (Functor.whiskeringRight (OpenNormalSubgroup G) (ModuleCat R)
      (TopModuleCat.{u} R)).obj (TopModuleCat.withModuleTopology R)

/-- The topologized finite degree-`-1` diagrams, functorial in the coefficient
representation. -/
@[expose] noncomputable def topologicalFiniteNegativeOneDeflationDiagramFunctor :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ TopModuleCat.{u} R) :=
  finiteNegativeOneDeflationDiagramFunctor ⋙
    (Functor.whiskeringRight (OpenNormalSubgroup G) (ModuleCat R)
      (TopModuleCat.{u} R)).obj (TopModuleCat.withModuleTopology R)

/-- The topologized finite degree-zero diagrams, functorial in the coefficient
representation. -/
@[expose] noncomputable def topologicalFiniteZeroDeflationDiagramFunctor :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ TopModuleCat.{u} R) :=
  finiteZeroDeflationDiagramFunctor ⋙
    (Functor.whiskeringRight (OpenNormalSubgroup G) (ModuleCat R)
      (TopModuleCat.{u} R)).obj (TopModuleCat.withModuleTopology R)

/-- The topological homological negative-deflation limit, functorial in the
coefficient representation. -/
@[expose] noncomputable def negativeDeflationLimitFunctor (n : ℕ) :
    Rep.{u} R G ⥤ TopModuleCat.{u} R :=
  topologicalFiniteNegativeDeflationDiagramFunctor n ⋙ lim

/-- The topological degree-`-1` deflation limit, functorial in the coefficient
representation. -/
@[expose] noncomputable def negativeOneDeflationLimitFunctor :
    Rep.{u} R G ⥤ TopModuleCat.{u} R :=
  topologicalFiniteNegativeOneDeflationDiagramFunctor ⋙ lim

/-- The topological degree-zero deflation limit, functorial in the coefficient
representation. -/
@[expose] noncomputable def zeroDeflationLimitFunctor :
    Rep.{u} R G ⥤ TopModuleCat.{u} R :=
  topologicalFiniteZeroDeflationDiagramFunctor ⋙ lim

/-- A coefficient map on homological negative-deflation limits commutes with
every canonical stage projection. -/
@[reassoc]
theorem negativeDeflationLimitFunctor_map_projection {A B : Rep.{u} R G}
    (f : A ⟶ B) (n : ℕ) (S : OpenNormalSubgroup G) :
    (negativeDeflationLimitFunctor n).map f ≫
        negativeDeflationLimitProjection B n S =
      negativeDeflationLimitProjection A n S ≫
        ((topologicalFiniteNegativeDeflationDiagramFunctor n).map f).app S := by
  exact limit.map_π ((topologicalFiniteNegativeDeflationDiagramFunctor n).map f) S

/-- A coefficient map on degree-`-1` deflation limits commutes with every
canonical stage projection. -/
@[reassoc]
theorem negativeOneDeflationLimitFunctor_map_projection {A B : Rep.{u} R G}
    (f : A ⟶ B) (S : OpenNormalSubgroup G) :
    negativeOneDeflationLimitFunctor.map f ≫
        negativeOneDeflationLimitProjection B S =
      negativeOneDeflationLimitProjection A S ≫
        (topologicalFiniteNegativeOneDeflationDiagramFunctor.map f).app S := by
  exact limit.map_π (topologicalFiniteNegativeOneDeflationDiagramFunctor.map f) S

/-- A coefficient map on degree-zero deflation limits commutes with every
canonical stage projection. -/
@[reassoc]
theorem zeroDeflationLimitFunctor_map_projection {A B : Rep.{u} R G}
    (f : A ⟶ B) (S : OpenNormalSubgroup G) :
    zeroDeflationLimitFunctor.map f ≫ zeroDeflationLimitProjection B S =
      zeroDeflationLimitProjection A S ≫
        (topologicalFiniteZeroDeflationDiagramFunctor.map f).app S := by
  exact limit.map_π (topologicalFiniteZeroDeflationDiagramFunctor.map f) S

end ContinuousGroupCohomology
