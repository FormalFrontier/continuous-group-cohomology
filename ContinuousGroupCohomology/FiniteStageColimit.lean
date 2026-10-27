/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.OpenNormalDiagram
public import ContinuousGroupCohomology.DiscreteCohomology
public import ContinuousGroupCohomology.FiniteStageBoundary
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Open-normal inflation as a colimit

For a compact topological group and a discrete representation, the canonical
inflation cocone of homogeneous cochain complexes is a colimit, both degreewise
in topological modules and in the category of cochain complexes. The action
need only be continuous for each fixed group element.

The continuous-cohomology inflation cocone is also a colimit without joint
continuity. Its equality-detection argument uses boundaries, whereas the cochain
colimit uses injectivity of inflation at the original stage.

## References

The finite-stage lifts and quotient-invariant constructions are due to Formal
Frontier. The proofs reuse Mathlib's filtered colimits of types (Kim Morrison,
Reid Barton and contributors), topological modules (Richard Hill, Andrew Yang
and contributors), and degreewise colimits of complexes (Joël Riou).
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, §2, supplies the
finite-quotient motivation.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

section

universe uJ vJ uM

/-- A filtered cocone with discrete apex is colimiting in topological modules
if its underlying cocone of types is colimiting. -/
private noncomputable def isColimitOfUnderlyingTypeOfDiscrete
    {J : Type uJ} [Category.{vJ} J] [IsFilteredOrEmpty J]
    {F : J ⥤ TopModuleCat.{uM} k} (c : Cocone F) [DiscreteTopology c.pt]
    (hc : IsColimit ((forget (TopModuleCat.{uM} k)).mapCocone c)) : IsColimit c := by
  let descendant (s : Cocone F) : c.pt → s.pt :=
    hc.desc ((forget (TopModuleCat.{uM} k)).mapCocone s)
  have hfac (s : Cocone F) (j : J) (a : F.obj j) :
      descendant s ((c.ι.app j).hom a) = (s.ι.app j).hom a := by
    simpa only [Functor.mapCocone_ι_app, ConcreteCategory.forget_map_eq_ofHom,
      ConcreteCategory.comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply,
      TypeCat.Fun.coe_mk] using
      ConcreteCategory.congr_hom
        (hc.fac ((forget (TopModuleCat.{uM} k)).mapCocone s) j) a
  have hsurj (z : c.pt) : ∃ (j : J) (a : F.obj j), (c.ι.app j).hom a = z := by
    obtain ⟨j, a, ha⟩ := Types.jointly_surjective_of_isColimit hc z
    change (c.ι.app j).hom a = z at ha
    exact ⟨j, a, ha⟩
  have h_add (s : Cocone F) (x y : c.pt) :
      descendant s (x + y) = descendant s x + descendant s y := by
    -- Put both representatives at one stage before using linearity of the legs.
    obtain ⟨j, a, b, ha, hb⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    change F.obj j at a b
    change (c.ι.app j).hom a = x at ha
    change (c.ι.app j).hom b = y at hb
    calc
      descendant s (x + y) = descendant s ((c.ι.app j).hom (a + b)) := by
        rw [map_add, ha, hb]
      _ = (s.ι.app j).hom (a + b) := hfac s j _
      _ = (s.ι.app j).hom a + (s.ι.app j).hom b := by rw [map_add]
      _ = descendant s x + descendant s y := by
        rw [← hfac s j a, ← hfac s j b, ha, hb]
  have h_smul (s : Cocone F) (r : k) (x : c.pt) :
      descendant s (r • x) = r • descendant s x := by
    obtain ⟨j, a, ha⟩ := hsurj x
    calc
      descendant s (r • x) = descendant s ((c.ι.app j).hom (r • a)) := by
        rw [map_smul, ha]
      _ = (s.ι.app j).hom (r • a) := hfac s j _
      _ = r • descendant s x := by rw [map_smul, ← hfac s j a, ha]
  let topDesc (s : Cocone F) : c.pt ⟶ s.pt :=
    TopModuleCat.ofHom
      { toLinearMap :=
          { toFun := descendant s
            map_add' := h_add s
            map_smul' := h_smul s }
        cont := continuous_of_discreteTopology }
  refine { desc := topDesc, fac := ?_, uniq := ?_ }
  · intro s j
    apply ConcreteCategory.hom_ext
    intro a
    exact hfac s j a
  · intro s morphism hm
    apply ConcreteCategory.hom_ext
    intro z
    obtain ⟨j, a, ha⟩ := hsurj z
    calc
      morphism.hom z = morphism.hom ((c.ι.app j).hom a) := by rw [ha]
      _ = (s.ι.app j).hom a := by
        simpa only [ConcreteCategory.comp_apply] using
          congrArg (fun f : F.obj j ⟶ s.pt => f.hom a) (hm j)
      _ = descendant s ((c.ι.app j).hom a) := (hfac s j a).symm
      _ = (topDesc s).hom z := by rw [ha]; rfl

end

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

/-- Every homogeneous cochain is in the image of a leg of the inflation cocone.
The stage may depend on the cochain and its degree. -/
theorem openNormalCochainInflationCocone_jointly_surjective (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (U : OpenNormalSubgroup G) (τ : ((openNormalCochainDiagram X).obj U).X n),
      ((openNormalCochainInflationCocone X).ι.app U).f n τ = σ :=
  exists_openNormal_quotient_cochain_lift X n σ

private noncomputable def openNormalCochainInflationCoconeIsColimitType (n : ℕ) :
    IsColimit ((forget (TopModuleCat.{max v w} k)).mapCocone
      ((HomologicalComplex.eval (TopModuleCat.{max v w} k) (ComplexShape.up ℕ) n).mapCocone
        (openNormalCochainInflationCocone X))) := by
  letI := isFiltered_orderDual_openNormalSubgroup G
  apply Types.FilteredColimit.isColimitOf'
  · intro σ
    obtain ⟨U, τ, hτ⟩ := openNormalCochainInflationCocone_jointly_surjective X n σ
    exact ⟨U, τ, hτ.symm⟩
  · intro U a b hab
    change ((openNormalCochainInflationCocone X).ι.app U).f n a =
      ((openNormalCochainInflationCocone X).ι.app U).f n b at hab
    have heq := openNormalCochainInflationCocone_ι_app_f_injective X U n hab
    subst b
    refine ⟨U, 𝟙 U, ?_⟩
    simp only

/-- For a compact group and discrete coefficients, inflation is colimiting in
every cochain degree, with continuous linear descendants into arbitrary
topological modules. No joint continuity of the action is required. -/
noncomputable def openNormalCochainInflationCoconeIsColimitEval (n : ℕ) :
    IsColimit ((HomologicalComplex.eval (TopModuleCat.{max v w} k)
      (ComplexShape.up ℕ) n).mapCocone (openNormalCochainInflationCocone X)) := by
  letI := isFiltered_orderDual_openNormalSubgroup G
  exact IsColimit.ofExistsUnique (by
    intro s
    exact IsColimit.existsUnique
      (@isColimitOfUnderlyingTypeOfDiscrete k _ _ _ _ _ _
        ((HomologicalComplex.eval (TopModuleCat.{max v w} k) (ComplexShape.up ℕ) n).mapCocone
          (openNormalCochainInflationCocone X))
        (discreteTopology_homogeneousCochains X n)
        (openNormalCochainInflationCoconeIsColimitType X n)) s)

/-- Homogeneous cochains with discrete coefficients over a compact topological
group are the colimit of the open-normal quotient cochain complexes. This is
a colimit in complexes of topological modules, not a cohomology assertion. -/
noncomputable def openNormalCochainInflationCoconeIsColimit :
    IsColimit (openNormalCochainInflationCocone X) :=
  HomologicalComplex.isColimitOfEval (openNormalCochainDiagram X)
    (openNormalCochainInflationCocone X)
    (openNormalCochainInflationCoconeIsColimitEval X)

variable (n : ℕ)

/-- The underlying Type-valued cohomology inflation cocone is filtered-colimiting.
No joint continuity of the action is required. -/
noncomputable def openNormalInflationCoconeIsColimitType :
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

@[deprecated openNormalInflationCoconeIsColimitType (since := "2026-10-21"),
  nolint defsWithUnderscore]
alias openNormalInflationCoconeIsColimit_type := openNormalInflationCoconeIsColimitType

/-- For a compact group and a discrete representation, the continuous-cohomology
inflation cocone over open-normal quotient stages is a colimit in topological
modules, in every degree. No joint continuity of the action is required. -/
noncomputable def openNormalInflationCoconeIsColimit :
    IsColimit (openNormalInflationCocone X n) := by
  letI := isFiltered_orderDual_openNormalSubgroup G
  exact IsColimit.ofExistsUnique (by
    intro s
    exact IsColimit.existsUnique
      (@isColimitOfUnderlyingTypeOfDiscrete k _ _ _ _ _ _ (openNormalInflationCocone X n)
        (discreteTopology_continuousCohomology X n)
        (openNormalInflationCoconeIsColimitType X n)) s)

end ContinuousCohomology
