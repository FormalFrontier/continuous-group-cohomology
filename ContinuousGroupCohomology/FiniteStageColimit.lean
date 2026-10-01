/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.OpenNormalDiagram
public import ContinuousGroupCohomology.DiscreteCohomology
public import ContinuousGroupCohomology.FiniteStageBoundary
public import Mathlib.CategoryTheory.Limits.Types.Filtered

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Open-normal inflation as a colimit

For a compact topological group acting jointly continuously on a discrete
representation, the canonical inflation cocone of native continuous cohomology
is a colimit in the category of topological modules in every degree.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
  [TopRep.JointlyContinuous X] (n : ℕ)

/-- The underlying Type-valued inflation cocone is filtered-colimiting. -/
noncomputable def openNormalInflationCoconeIsColimit_type :
    IsColimit ((forget (TopModuleCat.{max v w} k)).mapCocone
      (openNormalInflationCocone X n)) := by
  letI := isFiltered_orderDual_openNormalSubgroup G
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    obtain ⟨M, b, hb⟩ := exists_openNormal_quotient_class_lift X n a
    exact ⟨M, b, hb.symm⟩
  · intro M a b hab
    change ((openNormalInflationCocone X n).ι.app M).hom a =
      ((openNormalInflationCocone X n).ι.app M).hom b at hab
    obtain ⟨N, hNM, heq⟩ :=
      exists_refinement_class_eq_of_inflation_eq X M n a b hab
    exact ⟨N, homOfLE hNM, heq⟩

/-- For a compact group and a discrete jointly continuous representation,
the native continuous-cohomology inflation cocone over open-normal quotient
stages is a colimit in topological modules, in every degree. -/
noncomputable def openNormalInflationCoconeIsColimit :
    IsColimit (openNormalInflationCocone X n) := by
  let F := openNormalCohomologyDiagram X n
  let c : Cocone F := openNormalInflationCocone X n
  let hc : IsColimit ((forget (TopModuleCat.{max v w} k)).mapCocone c) :=
    openNormalInflationCoconeIsColimit_type X n
  let descendant (s : Cocone F) : c.pt → s.pt :=
    hc.desc ((forget (TopModuleCat.{max v w} k)).mapCocone s)
  have hfac (s : Cocone F) (M : OpenNormalSubgroup G) (a : F.obj M) :
      descendant s ((c.ι.app M).hom a) = (s.ι.app M).hom a := by
    simpa only [Functor.mapCocone_ι_app, ConcreteCategory.forget_map_eq_ofHom,
      ConcreteCategory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply,
      TypeCat.Fun.coe_mk] using
      ConcreteCategory.congr_hom
        (hc.fac ((forget (TopModuleCat.{max v w} k)).mapCocone s) M) a
  have hsurj (z : c.pt) : ∃ (M : OpenNormalSubgroup G) (a : F.obj M),
      (c.ι.app M).hom a = z := by
    exact exists_openNormal_quotient_class_lift X n z
  have h_add (s : Cocone F) (x y : c.pt) :
      descendant s (x + y) = descendant s x + descendant s y := by
    obtain ⟨M, a, ha⟩ := hsurj x
    obtain ⟨L, b, hb⟩ := hsurj y
    let Q : OrderDual (OpenNormalSubgroup G) := (M ⊓ L : OpenNormalSubgroup G)
    let fM := @homOfLE (OrderDual (OpenNormalSubgroup G)) _ M Q (by
        change (M ⊓ L : OpenNormalSubgroup G) ≤ M
        exact inf_le_left)
    let fL := @homOfLE (OrderDual (OpenNormalSubgroup G)) _ L Q (by
        change (M ⊓ L : OpenNormalSubgroup G) ≤ L
        exact inf_le_right)
    let aQ : F.obj Q := (F.map fM).hom a
    let bQ : F.obj Q := (F.map fL).hom b
    have hcM : (c.ι.app Q).hom aQ = (c.ι.app M).hom a := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        congrArg (fun f : F.obj M ⟶ c.pt => f.hom a) (c.ι.naturality fM)
    have hcL : (c.ι.app Q).hom bQ = (c.ι.app L).hom b := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        congrArg (fun f : F.obj L ⟶ c.pt => f.hom b) (c.ι.naturality fL)
    have hsM : (s.ι.app Q).hom aQ = (s.ι.app M).hom a := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        congrArg (fun f : F.obj M ⟶ s.pt => f.hom a) (s.ι.naturality fM)
    have hsL : (s.ι.app Q).hom bQ = (s.ι.app L).hom b := by
      simpa only [Functor.const_obj_obj, Functor.const_obj_map, ConcreteCategory.comp_apply,
        CategoryTheory.id_apply] using
        congrArg (fun f : F.obj L ⟶ s.pt => f.hom b) (s.ι.naturality fL)
    calc
      descendant s (x + y) = descendant s ((c.ι.app Q).hom (aQ + bQ)) := by
        rw [map_add, hcM, hcL, ha, hb]
      _ = (s.ι.app Q).hom (aQ + bQ) := hfac s Q _
      _ = (s.ι.app Q).hom aQ + (s.ι.app Q).hom bQ := by rw [map_add]
      _ = descendant s x + descendant s y := by
        rw [hsM, hsL, ← hfac s M a, ← hfac s L b, ha, hb]
  have h_smul (s : Cocone F) (r : k) (x : c.pt) :
      descendant s (r • x) = r • descendant s x := by
    obtain ⟨M, a, ha⟩ := hsurj x
    calc
      descendant s (r • x) = descendant s ((c.ι.app M).hom (r • a)) := by
        rw [map_smul, ha]
      _ = (s.ι.app M).hom (r • a) := hfac s M _
      _ = r • descendant s x := by rw [map_smul, ← hfac s M a, ha]
  let topDesc (s : Cocone F) : c.pt ⟶ s.pt :=
    TopModuleCat.ofHom
      { toLinearMap :=
          { toFun := descendant s
            map_add' := h_add s
            map_smul' := h_smul s }
        cont := by
          exact @continuous_of_discreteTopology c.pt _
            (discreteTopology_continuousCohomology X n) s.pt _ (descendant s) }
  refine { desc := topDesc, fac := ?_, uniq := ?_ }
  · intro s M
    apply ConcreteCategory.hom_ext
    intro a
    exact hfac s M a
  · intro s morphism hm
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨M, a, ha⟩ := hsurj z
    calc
      morphism.hom z = morphism.hom ((c.ι.app M).hom a) := by rw [ha]
      _ = (s.ι.app M).hom a := by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (fun f : F.obj M ⟶ s.pt => f.hom a) (hm M)
      _ = descendant s ((c.ι.app M).hom a) := (hfac s M a).symm
      _ = (topDesc s).hom z := by rw [ha]; rfl

end ContinuousCohomology
