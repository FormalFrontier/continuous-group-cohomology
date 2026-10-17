/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientTransitions
public import ContinuousGroupCohomology.CochainInjectivity

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cochains and cohomology over open-normal quotient stages

The order-dual index directs the coarser quotient stage toward its finer
refinements. Homogeneous cochains form a diagram of complexes of topological
modules, with a canonical inflation cocone and functorial coefficient maps.
The analogous degreewise cohomology diagram is also provided. Neither
construction requires compactness, discreteness, or joint continuity of the
action. Colimit assertions are in `FiniteStageColimit`.

## References

The constructions reuse the continuous-cochain functoriality of Mathlib
(Richard Hill, Andrew Yang, Edison Xie and contributors) and the quotient
invariants and transitions of Formal Frontier. The finite-quotient description
of continuous cohomology in Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, §2, motivates the diagrams.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The order dual of the open normal subgroups is filtered: intersections are
common refinements, and the whole group gives a nonempty stage. -/
theorem isFiltered_orderDual_openNormalSubgroup (G : Type v) [Group G]
    [TopologicalSpace G] : IsFiltered (OrderDual (OpenNormalSubgroup G)) := by
  refine { toIsFilteredOrEmpty := inferInstance, nonempty := ?_ }
  exact ⟨⟨(⊤ : OpenSubgroup G), by change (⊤ : Subgroup G).Normal; infer_instance⟩⟩

variable (X : TopRep.{max v w} k G)

/-- Homogeneous cochains on open-normal quotients, directed by refinement.
An arrow `U ⟶ V` means `V ≤ U`: the group map is `G/V → G/U`, and the
coefficient map includes `U`-invariants into `V`-invariants. -/
def openNormalCochainDiagram :
    OrderDual (OpenNormalSubgroup G) ⥤
      CochainComplex (TopModuleCat.{max v w} k) ℕ where
  obj U := TopRep.homogeneousCochains (TopRep.quotientInvariants U.toSubgroup X)
  map {U V} f := cochainsMap (quotientTransitionHom V U (leOfHom f))
    (quotientTransitionIncl X (leOfHom f))
  map_id U := quotientTransition_cochainsMap_id X U
  map_comp f g := quotientTransition_cochainsMap_comp X (leOfHom g) (leOfHom f)

/-- Inflation from quotient-invariant coefficients gives a cocone of
homogeneous cochain complexes with apex the cochains of `X`. -/
def openNormalCochainInflationCocone : Cocone (openNormalCochainDiagram X) where
  pt := TopRep.homogeneousCochains X
  ι := {
    app U := cochainsMap (openNormalQuotientHom U)
      (TopRep.quotientInvariantsIncl U.toSubgroup X)
    naturality := by
      intro U V f
      exact (quotientTransition_cochainsMap_inflate X (leOfHom f)).symm
  }

@[simp] theorem openNormalCochainDiagram_obj (U : OpenNormalSubgroup G) :
    (openNormalCochainDiagram X).obj U =
      TopRep.homogeneousCochains (TopRep.quotientInvariants U.toSubgroup X) := rfl

@[simp] theorem openNormalCochainDiagram_map
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) :
    (openNormalCochainDiagram X).map f =
      cochainsMap (quotientTransitionHom V U (leOfHom f))
        (quotientTransitionIncl X (leOfHom f)) := rfl

@[simp] theorem openNormalCochainDiagram_map_f
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) (n : ℕ) :
    ((openNormalCochainDiagram X).map f).f n =
      TopRep.invariantsResMap (quotientTransitionHom V U (leOfHom f))
        (resolutionMap (quotientTransitionHom V U (leOfHom f))
          (quotientTransitionIncl X (leOfHom f)) (n + 1)) := rfl

@[simp] theorem openNormalCochainDiagram_map_f_apply_val
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) (n : ℕ)
    (τ : ((openNormalCochainDiagram X).obj U).X n) :
    (((openNormalCochainDiagram X).map f).f n τ).1 =
      (resolutionMap (quotientTransitionHom V U (leOfHom f))
        (quotientTransitionIncl X (leOfHom f)) (n + 1)).hom τ.1 := rfl

@[simp] theorem openNormalCochainInflationCocone_pt :
    (openNormalCochainInflationCocone X).pt = TopRep.homogeneousCochains X := rfl

@[simp] theorem openNormalCochainInflationCocone_ι_app (U : OpenNormalSubgroup G) :
    (openNormalCochainInflationCocone X).ι.app U =
      cochainsMap (openNormalQuotientHom U)
        (TopRep.quotientInvariantsIncl U.toSubgroup X) := rfl

@[simp] theorem openNormalCochainInflationCocone_ι_app_f
    (U : OpenNormalSubgroup G) (n : ℕ) :
    ((openNormalCochainInflationCocone X).ι.app U).f n =
      TopRep.invariantsResMap (openNormalQuotientHom U)
        (resolutionMap (openNormalQuotientHom U)
          (TopRep.quotientInvariantsIncl U.toSubgroup X) (n + 1)) := rfl

@[simp] theorem openNormalCochainInflationCocone_ι_app_f_apply_val
    (U : OpenNormalSubgroup G) (n : ℕ)
    (τ : ((openNormalCochainDiagram X).obj U).X n) :
    (((openNormalCochainInflationCocone X).ι.app U).f n τ).1 =
      (resolutionMap (openNormalQuotientHom U)
        (TopRep.quotientInvariantsIncl U.toSubgroup X) (n + 1)).hom τ.1 := rfl

/-- Refining a stage does not change its inflated cochain. -/
theorem openNormalCochainInflationCocone_naturality_f_apply
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) (n : ℕ)
    (τ : ((openNormalCochainDiagram X).obj U).X n) :
    ((openNormalCochainInflationCocone X).ι.app V).f n
        (((openNormalCochainDiagram X).map f).f n τ) =
      ((openNormalCochainInflationCocone X).ι.app U).f n τ := by
  simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom
      (congrArg
        (fun a : (openNormalCochainDiagram X).obj U ⟶
          (openNormalCochainInflationCocone X).pt => a.f n)
        ((openNormalCochainInflationCocone X).w f)) τ

/-- Every refinement map is injective in each cochain degree. -/
theorem openNormalCochainDiagram_map_f_injective
    {U V : OrderDual (OpenNormalSubgroup G)} (f : U ⟶ V) (n : ℕ) :
    Function.Injective (((openNormalCochainDiagram X).map f).f n) :=
  cochainsMap_injective _ _ (quotientTransitionHom_surjective V U (leOfHom f))
    (quotientTransitionIncl_injective X (leOfHom f)) n

/-- Inflation reflects equality of cochains at a fixed stage, without a
compactness or continuity assumption on the group action in both variables. -/
theorem openNormalCochainInflationCocone_ι_app_f_injective
    (U : OpenNormalSubgroup G) (n : ℕ) :
    Function.Injective (((openNormalCochainInflationCocone X).ι.app U).f n) :=
  cochainsMap_injective _ _ (QuotientGroup.mk'_surjective U.toSubgroup)
    Subtype.val_injective n

@[simp] theorem openNormalCochainInflationCocone_ι_app_f_eq_iff
    (U : OpenNormalSubgroup G) (n : ℕ)
    (τ υ : ((openNormalCochainDiagram X).obj U).X n) :
    ((openNormalCochainInflationCocone X).ι.app U).f n τ =
        ((openNormalCochainInflationCocone X).ι.app U).f n υ ↔ τ = υ :=
  (openNormalCochainInflationCocone_ι_app_f_injective X U n).eq_iff

/-- At the whole-group stage, an inflated degree-zero cochain is constant.
This concerns cochains only and does not assert that they are cocycles. -/
theorem openNormalCochainInflationCocone_whole_group_apply
    (U : OpenNormalSubgroup G) (hU : U.toSubgroup = ⊤)
    (τ : ((openNormalCochainDiagram X).obj U).X 0) (g h : G) :
    ((((openNormalCochainInflationCocone X).ι.app U).f 0 τ).1 g) =
      ((((openNormalCochainInflationCocone X).ι.app U).f 0 τ).1 h) := by
  change (τ.1 (openNormalQuotientHom U g)).1 = (τ.1 (openNormalQuotientHom U h)).1
  exact congrArg (fun q : G ⧸ U.toSubgroup => (τ.1 q).1)
    (@Subsingleton.elim (G ⧸ U.toSubgroup)
      (QuotientGroup.subsingleton_iff.mpr hU) _ _)

variable {X} {Y Z : TopRep.{max v w} k G}

/-- A coefficient morphism induces a natural transformation of quotient
cochain diagrams, using the canonical maps on invariant submodules. -/
def openNormalCochainDiagramMap (a : X ⟶ Y) :
    openNormalCochainDiagram X ⟶ openNormalCochainDiagram Y where
  app U := cochainsMap (ContinuousMonoidHom.id (G ⧸ U.toSubgroup))
    (TopRep.quotientInvariantsMap U.toSubgroup a)
  naturality {U V} f := by
    let φ := quotientTransitionHom V U (leOfHom f)
    have hcoeff :
        (TopRep.resFunctor (MonoidHom.id (G ⧸ V.toSubgroup))).map
            (quotientTransitionIncl X (leOfHom f)) ≫
          TopRep.quotientInvariantsMap V.toSubgroup a =
        (TopRep.resFunctor (φ : G ⧸ V.toSubgroup →* G ⧸ U.toSubgroup)).map
            (TopRep.quotientInvariantsMap U.toSubgroup a) ≫
          quotientTransitionIncl Y (leOfHom f) := by
      ext x
      rfl
    change cochainsMap φ (quotientTransitionIncl X (leOfHom f)) ≫
        cochainsMap (ContinuousMonoidHom.id _) (TopRep.quotientInvariantsMap V.toSubgroup a) =
      cochainsMap (ContinuousMonoidHom.id _) (TopRep.quotientInvariantsMap U.toSubgroup a) ≫
        cochainsMap φ (quotientTransitionIncl Y (leOfHom f))
    calc
      _ = cochainsMap φ
          ((TopRep.resFunctor (MonoidHom.id (G ⧸ V.toSubgroup))).map
            (quotientTransitionIncl X (leOfHom f)) ≫
              TopRep.quotientInvariantsMap V.toSubgroup a) :=
        (cochainsMap_comp φ (ContinuousMonoidHom.id _) _ _).symm
      _ = _ := congrArg (cochainsMap φ) hcoeff
      _ = _ := cochainsMap_comp (ContinuousMonoidHom.id _) φ _ _

@[simp] theorem openNormalCochainDiagramMap_app (a : X ⟶ Y)
    (U : OpenNormalSubgroup G) :
    (openNormalCochainDiagramMap a).app U =
      cochainsMap (ContinuousMonoidHom.id (G ⧸ U.toSubgroup))
        (TopRep.quotientInvariantsMap U.toSubgroup a) := rfl

@[simp] theorem openNormalCochainDiagramMap_id :
    openNormalCochainDiagramMap (𝟙 X) = 𝟙 (openNormalCochainDiagram X) := by
  apply NatTrans.ext
  funext U
  rw [openNormalCochainDiagramMap_app, NatTrans.id_app]
  rw [show TopRep.quotientInvariantsMap U.toSubgroup (𝟙 X) = 𝟙 _ from
    (TopRep.quotientInvariantsFunctor (k := k) U.toSubgroup).map_id X]
  exact cochainsMap_id (TopRep.quotientInvariants U.toSubgroup X)

@[simp] theorem openNormalCochainDiagramMap_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    openNormalCochainDiagramMap (a ≫ b) =
      openNormalCochainDiagramMap a ≫ openNormalCochainDiagramMap b := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.comp_app]
  simp only [openNormalCochainDiagramMap_app]
  let Q : Type v := G ⧸ U.toSubgroup
  let A : TopRep.{max v w} k Q := TopRep.quotientInvariants U.toSubgroup X
  let B : TopRep.{max v w} k Q := TopRep.quotientInvariants U.toSubgroup Y
  let C : TopRep.{max v w} k Q := TopRep.quotientInvariants U.toSubgroup Z
  let idQ : Q →ₜ* Q := ContinuousMonoidHom.id Q
  let aU : A ⟶ B := TopRep.quotientInvariantsMap U.toSubgroup a
  let bU : B ⟶ C := TopRep.quotientInvariantsMap U.toSubgroup b
  have hcoeff : TopRep.quotientInvariantsMap U.toSubgroup (a ≫ b) = aU ≫ bU :=
    (TopRep.quotientInvariantsFunctor (k := k) U.toSubgroup).map_comp a b
  have hid : idQ = idQ.comp idQ := by
    ext x
    rfl
  have hcomp :
      cochainsMap (idQ.comp idQ) (X := A)
          ((TopRep.resFunctor (idQ : Q →* Q)).map aU ≫ bU) =
        cochainsMap idQ (X := A) aU ≫ cochainsMap idQ (X := B) bU :=
    cochainsMap_comp (X := A) (Y := B) (Z := C) idQ idQ aU bU
  calc
    cochainsMap idQ (X := A) (TopRep.quotientInvariantsMap U.toSubgroup (a ≫ b)) =
        cochainsMap (idQ.comp idQ) (X := A)
          ((TopRep.resFunctor (idQ : Q →* Q)).map aU ≫ bU) := by
      apply cochainsMap_congr (A := A) (B := C) (φ := idQ) (ψ := idQ.comp idQ)
        (TopRep.quotientInvariantsMap U.toSubgroup (a ≫ b))
        ((TopRep.resFunctor (idQ : Q →* Q)).map aU ≫ bU) hid
      intro x
      change (TopRep.quotientInvariantsMap U.toSubgroup (a ≫ b)).hom x =
        (aU ≫ bU).hom x
      exact congrArg (fun f : A ⟶ C => f.hom x) hcoeff
    _ = cochainsMap idQ (X := A) aU ≫ cochainsMap idQ (X := B) bU := hcomp

/-- The coefficient transformation commutes with inflation as a map of complexes. -/
theorem openNormalCochainDiagramMap_inflation (a : X ⟶ Y) (U : OpenNormalSubgroup G) :
    (openNormalCochainDiagramMap a).app U ≫
        (openNormalCochainInflationCocone Y).ι.app U =
      (openNormalCochainInflationCocone X).ι.app U ≫
        cochainsMap (ContinuousMonoidHom.id G) a := by
  let Q : Type v := G ⧸ U.toSubgroup
  let q : G →ₜ* Q := openNormalQuotientHom U
  let A : TopRep.{max v w} k Q := TopRep.quotientInvariants U.toSubgroup X
  let B : TopRep.{max v w} k Q := TopRep.quotientInvariants U.toSubgroup Y
  let idQ : Q →ₜ* Q := ContinuousMonoidHom.id Q
  let idG : G →ₜ* G := ContinuousMonoidHom.id G
  let aU : A ⟶ B := TopRep.quotientInvariantsMap U.toSubgroup a
  let iX : TopRep.res q A ⟶ X := TopRep.quotientInvariantsIncl U.toSubgroup X
  let iY : TopRep.res q B ⟶ Y := TopRep.quotientInvariantsIncl U.toSubgroup Y
  -- Normalize restriction identities on coefficients before passing to complexes.
  have hcoeff : (TopRep.resFunctor (q : G →* Q)).map aU ≫ iY = iX ≫ a :=
    TopRep.quotientInvariantsIncl_naturality U.toSubgroup a
  have hleft : idQ.comp q = q := by
    ext g
    rfl
  have hright : q = q.comp idG := by
    ext g
    rfl
  have hcompLeft :
      cochainsMap (idQ.comp q) (X := A)
          ((TopRep.resFunctor (q : G →* Q)).map aU ≫ iY) =
        cochainsMap idQ (X := A) aU ≫ cochainsMap q (X := B) iY :=
    cochainsMap_comp (X := A) (Y := B) (Z := Y) idQ q aU iY
  have hcompRight :
      cochainsMap (q.comp idG) (X := A)
          ((TopRep.resFunctor (idG : G →* G)).map iX ≫ a) =
        cochainsMap q (X := A) iX ≫ cochainsMap idG (X := X) a :=
    cochainsMap_comp (X := A) (Y := X) (Z := Y) q idG iX a
  simp only [openNormalCochainDiagramMap_app, openNormalCochainInflationCocone_ι_app]
  calc
    cochainsMap idQ (X := A) aU ≫ cochainsMap q (X := B) iY =
        cochainsMap (idQ.comp q) (X := A)
          ((TopRep.resFunctor (q : G →* Q)).map aU ≫ iY) := hcompLeft.symm
    _ = cochainsMap q (X := A) (iX ≫ a) := by
      apply cochainsMap_congr (A := A) (B := Y)
        ((TopRep.resFunctor (q : G →* Q)).map aU ≫ iY) (iX ≫ a) hleft
      intro x
      exact congrArg (fun f : TopRep.res q A ⟶ Y => f.hom x) hcoeff
    _ = cochainsMap (q.comp idG) (X := A)
        ((TopRep.resFunctor (idG : G →* G)).map iX ≫ a) := by
      apply cochainsMap_congr (A := A) (B := Y) (iX ≫ a)
        ((TopRep.resFunctor (idG : G →* G)).map iX ≫ a) hright
      intro x
      rfl
    _ = cochainsMap q (X := A) iX ≫ cochainsMap idG (X := X) a := hcompRight

variable (X) (n : ℕ)

/-- The degree-`n` continuous-cohomology diagram: a morphism from `M` to
`N` means `N ≤ M`, and maps classes from `M`-invariants to `N`-invariants. -/
noncomputable def openNormalCohomologyDiagram :
    OrderDual (OpenNormalSubgroup G) ⥤ TopModuleCat.{max v w} k where
  obj M := continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X)
  map {M N} f :=
    map (quotientTransitionHom N M (leOfHom f))
      (quotientTransitionIncl X (leOfHom f)) n
  map_id M := by
    exact quotientTransition_map_id X M n
  map_comp f g := by
    exact quotientTransition_map_comp X (leOfHom g) (leOfHom f) n

/-- The canonical cocone whose legs inflate the classes of open-normal
quotients to continuous cohomology of the original representation. -/
noncomputable def openNormalInflationCocone : Cocone (openNormalCohomologyDiagram X n) where
  pt := continuousCohomology n X
  ι := {
    app M := map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) n
    naturality := by
      intro M N f
      exact (quotientTransition_map_inflate X (leOfHom f) n).symm
  }

@[simp] theorem openNormalCohomologyDiagram_obj (M : OpenNormalSubgroup G) :
    (openNormalCohomologyDiagram X n).obj M =
      continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X) := rfl

@[simp] theorem openNormalCohomologyDiagram_map
    {M N : OrderDual (OpenNormalSubgroup G)} (f : M ⟶ N) :
    (openNormalCohomologyDiagram X n).map f =
      map (quotientTransitionHom N M (leOfHom f))
        (quotientTransitionIncl X (leOfHom f)) n := rfl

@[simp] theorem openNormalInflationCocone_ι_app (M : OpenNormalSubgroup G) :
    (openNormalInflationCocone X n).ι.app M =
      map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) n := rfl

end ContinuousCohomology
