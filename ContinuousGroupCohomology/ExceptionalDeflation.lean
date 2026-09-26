/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.FiniteNegativeDeflation
public import FiniteGroupTateCohomology.Basic

/-!
# Exceptional-degree finite deflation

For nested normal subgroups `S ≤ T` of `G`, this module constructs finite-level
deflation in Tate degrees `-1` and `0` between the quotients `G ⧸ S` and
`G ⧸ T`, with coefficients in `A^S` and `A^T`.

The common input is the degree-zero-homology component of
`finiteNegativeDeflation`, transported to coinvariants. Its compatibility with
the two finite-group norms gives maps between their kernels and cokernels.
Transport through the standard exceptional-degree Tate-cohomology
identifications then gives the public deflation maps. All layers are natural in
the coefficient representation.

As in `FiniteNegativeDeflation`, the group-homology API requires the
coefficient ring, group, and representation carrier to lie in one universe.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- The coinvariant map underlying exceptional-degree finite deflation. This is
exactly `finiteNegativeDeflation A S T hST 0` under the standard degree-zero
group-homology/coinvariants isomorphisms. -/
noncomputable def finiteNegativeDeflationCoinvariants (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Rep.coinvariantsFunctor R (G ⧸ S)).obj (A.quotientToInvariants S) ⟶
      (Rep.coinvariantsFunctor R (G ⧸ T)).obj (A.quotientToInvariants T) :=
  (groupHomology.H0Iso (A.quotientToInvariants S)).inv ≫
    finiteNegativeDeflation A S T hST 0 ≫
    (groupHomology.H0Iso (A.quotientToInvariants T)).hom

/-- The canonical identification between the total invariants of `A^S` as a
`G ⧸ S`-representation and those of `A^T` as a `G ⧸ T`-representation. -/
@[expose]
noncomputable def finiteLevelTotalInvariantsEquiv (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    Representation.invariants (A.quotientToInvariants S).ρ ≃ₗ[R]
      Representation.invariants (A.quotientToInvariants T).ρ where
  toFun x := ⟨⟨x.1.1, fun t ↦ by
    change A.ρ t.1 x.1.1 = x.1.1
    exact congrArg Subtype.val (x.2 (QuotientGroup.mk' S t.1))⟩,
    fun q ↦ QuotientGroup.induction_on q fun g ↦ by
      apply Subtype.ext
      change A.ρ g x.1.1 = x.1.1
      exact congrArg Subtype.val (x.2 (QuotientGroup.mk' S g))⟩
  invFun y := ⟨⟨y.1.1, fun s ↦ y.1.2 ⟨s.1, hST s.2⟩⟩,
    fun q ↦ QuotientGroup.induction_on q fun g ↦ by
      apply Subtype.ext
      change A.ρ g y.1.1 = y.1.1
      exact congrArg Subtype.val (y.2 (QuotientGroup.mk' T g))⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The total-invariants identification preserves the underlying vector. -/
@[simp]
lemma finiteLevelTotalInvariantsEquiv_apply_val (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    (x : Representation.invariants (A.quotientToInvariants S).ρ) :
    (finiteLevelTotalInvariantsEquiv A S T hST x).1.1 = x.1.1 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identification of total invariants through nested normal subgroups is
natural in the coefficient representation. -/
@[reassoc]
lemma finiteLevelTotalInvariantsEquiv_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (Rep.invariantsFunctor R (G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      (finiteLevelTotalInvariantsEquiv B S T hST).toModuleIso.hom =
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
      (Rep.invariantsFunctor R (G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  ext x
  rfl

private lemma norm_quotientToInvariants_apply {H : Type u} [Group H]
    [Fintype H] (B : Rep R H) (K : Subgroup H) [K.Normal]
    [Fintype K] [Fintype (H ⧸ K)] (x : B) :
    ((Representation.norm (B.quotientToInvariants K).ρ)
        ⟨Representation.norm (B.ρ.comp K.subtype) x,
          fun k ↦ Representation.self_norm_apply (B.ρ.comp K.subtype) k x⟩).1 =
      Representation.norm B.ρ x := by
  classical
  let e : H ≃ (H ⧸ K) × K :=
    { toFun := fun h ↦
        ⟨QuotientGroup.mk' K h,
          ⟨(QuotientGroup.mk' K h).out⁻¹ * h,
            QuotientGroup.eq.mp (QuotientGroup.out_eq' _)⟩⟩
      invFun := fun p ↦ p.1.out * p.2.1
      left_inv := fun h ↦ by simp
      right_inv := fun p ↦ by
        rcases p with ⟨q, k⟩
        apply Prod.ext
        · simp
        · apply Subtype.ext
          simp }
  simp only [Representation.norm, LinearMap.sum_apply]
  rw [Submodule.coe_sum]
  change (∑ q : H ⧸ K,
      (((B.quotientToInvariants K).ρ q)
        ⟨∑ k : K, B.ρ k.1 x,
          fun k ↦ by simpa [Representation.norm] using
            Representation.self_norm_apply (B.ρ.comp K.subtype) k x⟩).1) =
    ∑ h : H, B.ρ h x
  have action_out (q : H ⧸ K)
      (y : B.quotientToInvariants K) :
      (((B.quotientToInvariants K).ρ q) y).1 = B.ρ q.out y.1 := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp_rw [action_out, map_sum]
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp e.symm
    (fun h : H ↦ B.ρ h x)]
  apply Finset.sum_congr rfl
  intro p _
  change B.ρ p.1.out (B.ρ p.2.1 x) = B.ρ (p.1.out * p.2.1) x
  simp

private lemma norm_equiv_apply {H K : Type u} [Group H] [Group K]
    [Fintype H] [Fintype K] (e : H ≃* K) (B : Rep R H) (C : Rep R K)
    (f : B ≅ Rep.res e.toMonoidHom C) (x : B) :
    Representation.norm C.ρ (f.hom x) =
      f.hom (Representation.norm B.ρ x) := by
  classical
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  rw [← Equiv.sum_comp e.toEquiv (fun k : K ↦ C.ρ k (f.hom x))]
  apply Finset.sum_congr rfl
  intro h _
  exact (Rep.hom_comm_apply f.hom h x).symm

/-- On coinvariant generators, exceptional deflation is the residual `T / S`
norm followed by nested-invariants and third-isomorphism transport. -/
lemma finiteNegativeDeflationCoinvariants_mk_hom (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Rep.coinvariantsMk R (G ⧸ S)).app (A.quotientToInvariants S) ≫
        finiteNegativeDeflationCoinvariants A S T hST =
      (Rep.toCoinvariantsMkQ (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S))).toModuleCatHom ≫
        (FiniteGroupTateCohomology.quotientNorm
          (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S))).toModuleCatHom ≫
        (nestedQuotientInvariantsRepIso A S T hST).hom.toModuleCatHom ≫
        (Rep.coinvariantsMk R (G ⧸ T)).app (A.quotientToInvariants T) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [finiteNegativeDeflationCoinvariants, finiteNegativeDeflation_formula]

set_option backward.isDefEq.respectTransparency false in
private lemma H0Iso_hom_naturality {H : Type u} [Group H]
    {A B : Rep.{u} R H} (f : A ⟶ B) :
    (groupHomology.functor R H 0).map f ≫ (groupHomology.H0Iso B).hom =
      (groupHomology.H0Iso A).hom ≫
        (Rep.coinvariantsFunctor R H).map f := by
  apply (cancel_epi (groupHomology.H0π A)).1
  simp only [← Category.assoc, groupHomology.functor_map]
  rw [groupHomology.H0π_comp_map]
  simp only [Category.assoc, groupHomology.H0π_comp_H0Iso_hom]
  simpa using (Rep.coinvariantsMk R H).naturality f

set_option backward.isDefEq.respectTransparency false in
private lemma H0Iso_inv_naturality {H : Type u} [Group H]
    {A B : Rep.{u} R H} (f : A ⟶ B) :
    (Rep.coinvariantsFunctor R H).map f ≫ (groupHomology.H0Iso B).inv =
      (groupHomology.H0Iso A).inv ≫
        (groupHomology.functor R H 0).map f := by
  exact (CommSq.vert_inv ⟨H0Iso_hom_naturality f⟩).w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero-homology realization of finite negative deflation is
natural in the coefficient representation. -/
@[reassoc]
lemma finiteNegativeDeflationCoinvariants_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Rep.coinvariantsFunctor R (G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeDeflationCoinvariants B S T hST =
    finiteNegativeDeflationCoinvariants A S T hST ≫
      (Rep.coinvariantsFunctor R (G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  dsimp only [Rep.quotientToInvariantsFunctor, groupHomology.functor,
    groupHomology.H0]
  simp only [finiteNegativeDeflationCoinvariants, Category.assoc]
  rw [← Category.assoc]
  erw [H0Iso_inv_naturality
    (A := A.quotientToInvariants S) (B := B.quotientToInvariants S)]
  have hnat := finiteNegativeDeflation_naturality f S T hST 0
  dsimp only [Rep.quotientToInvariantsFunctor] at hnat
  simp only [groupHomology.functor_map] at hnat
  have hhom := H0Iso_hom_naturality
    ((Rep.quotientToInvariantsFunctor R T).map f)
  dsimp only [Rep.quotientToInvariantsFunctor] at hhom
  simp only [groupHomology.functor_map] at hhom
  have h₁ := congrArg (fun k ↦
      (groupHomology.H0Iso (A.quotientToInvariants S)).inv ≫ k ≫
        (groupHomology.H0Iso (B.quotientToInvariants T)).hom) hnat
  have h₂ := congrArg (fun k ↦
      (groupHomology.H0Iso (A.quotientToInvariants S)).inv ≫
        finiteNegativeDeflation A S T hST 0 ≫ k) hhom
  simpa only [Category.assoc, groupHomology.functor_map] using h₁.trans h₂

set_option linter.style.haveILetI false in
/-- Exceptional deflation commutes with the norm from coinvariants to
invariants, after canonically identifying the total invariants. -/
lemma finiteNegativeDeflationCoinvariants_norm (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeDeflationCoinvariants A S T hST ≫
        FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants T) =
      FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S) ≫
        (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom := by
  letI : Fintype ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) :=
    Fintype.ofFinite _
  apply Rep.coinvariantsFunctor_hom_ext
  rw [← Category.assoc, finiteNegativeDeflationCoinvariants_mk_hom]
  ext x
  apply Subtype.ext
  apply Subtype.ext
  change
    ((Representation.norm (A.quotientToInvariants T).ρ)
      ((nestedQuotientInvariantsRepIso A S T hST).hom
        ⟨Representation.norm
            ((A.quotientToInvariants S).ρ.comp
              (T.map (QuotientGroup.mk' S)).subtype) x,
          fun k ↦ Representation.self_norm_apply
            ((A.quotientToInvariants S).ρ.comp
              (T.map (QuotientGroup.mk' S)).subtype) k x⟩)).1 =
      (Representation.norm (A.quotientToInvariants S).ρ x).1
  rw [norm_equiv_apply
    (QuotientGroup.quotientQuotientEquivQuotient S T hST)
    ((A.quotientToInvariants S).quotientToInvariants
      (T.map (QuotientGroup.mk' S)))
    (A.quotientToInvariants T)
    (nestedQuotientInvariantsRepIso A S T hST)]
  exact congrArg Subtype.val (norm_quotientToInvariants_apply
    (A.quotientToInvariants S) (T.map (QuotientGroup.mk' S)) x)

private noncomputable def kernelMapOfSquare
    {X Y X' Y' : ModuleCat.{u} R} (p : X ⟶ X') (q : Y ⟶ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (w : p ≫ g = f ≫ q) :
    kernel f ⟶ kernel g :=
  kernel.map f g p q w.symm

private noncomputable def cokernelMapOfSquare
    {X Y X' Y' : ModuleCat.{u} R} (p : X ⟶ X') (q : Y ⟶ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (w : p ≫ g = f ≫ q) :
    cokernel f ⟶ cokernel g :=
  cokernel.map f g p q w.symm

set_option backward.isDefEq.respectTransparency false in
/-- The map between kernels of the two finite-group norms induced by the norm
compatibility square. -/
noncomputable def finiteNegativeOneDeflationKernel (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    kernel (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)) ⟶
      kernel (FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants T)) := by
  let p := finiteNegativeDeflationCoinvariants A S T hST
  let q := (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom
  let f := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S)
  let g := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants T)
  have w : p ≫ g = f ≫ q := finiteNegativeDeflationCoinvariants_norm A S T hST
  exact kernelMapOfSquare p q f g w

set_option backward.isDefEq.respectTransparency false in
/-- The kernel map followed by the target kernel inclusion is the underlying
coinvariant deflation after the source kernel inclusion. -/
@[reassoc]
lemma finiteNegativeOneDeflationKernel_ι (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S T hST ≫
        kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants T)) =
      kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S)) ≫
        finiteNegativeDeflationCoinvariants A S T hST := by
  simp [finiteNegativeOneDeflationKernel, kernelMapOfSquare]

set_option backward.isDefEq.respectTransparency false in
/-- The map between cokernels of the two finite-group norms induced by the norm
compatibility square. -/
noncomputable def finiteZeroDeflationCokernel (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    cokernel (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)) ⟶
      cokernel (FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants T)) := by
  let p := finiteNegativeDeflationCoinvariants A S T hST
  let q := (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom
  let f := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S)
  let g := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants T)
  have w : p ≫ g = f ≫ q := finiteNegativeDeflationCoinvariants_norm A S T hST
  exact cokernelMapOfSquare p q f g w

set_option backward.isDefEq.respectTransparency false in
/-- The source cokernel projection followed by the cokernel map is the total
invariants identification followed by the target cokernel projection. -/
@[reassoc]
lemma finiteZeroDeflationCokernel_π (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    cokernel.π (FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants S)) ≫
      finiteZeroDeflationCokernel A S T hST =
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
      cokernel.π (FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants T)) := by
  simp [finiteZeroDeflationCokernel, cokernelMapOfSquare]

set_option backward.isDefEq.respectTransparency false in
private lemma finiteNegativeOneDeflationKernel_ι_functor
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S T hST ≫
        (Limits.ker.ι (ModuleCat R)).app
          ((FiniteGroupTateCohomology.normArrowFunctor
            (R := R) (G := G ⧸ T)).obj (A.quotientToInvariants T)) =
      (Limits.ker.ι (ModuleCat R)).app
          ((FiniteGroupTateCohomology.normArrowFunctor
            (R := R) (G := G ⧸ S)).obj (A.quotientToInvariants S)) ≫
        finiteNegativeDeflationCoinvariants A S T hST :=
  finiteNegativeOneDeflationKernel_ι A S T hST

set_option backward.isDefEq.respectTransparency false in
private lemma finiteZeroDeflationCokernel_π_functor
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Limits.coker.π (ModuleCat R)).app
        ((FiniteGroupTateCohomology.normArrowFunctor
          (R := R) (G := G ⧸ S)).obj (A.quotientToInvariants S)) ≫
      finiteZeroDeflationCokernel A S T hST =
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
      (Limits.coker.π (ModuleCat R)).app
        ((FiniteGroupTateCohomology.normArrowFunctor
          (R := R) (G := G ⧸ T)).obj (A.quotientToInvariants T)) :=
  finiteZeroDeflationCokernel_π A S T hST

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The kernel realization of degree `-1` deflation is natural in the
coefficient representation. -/
@[reassoc]
lemma finiteNegativeOneDeflationKernel_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (FiniteGroupTateCohomology.normKernelFunctor
        (R := R) (G := G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeOneDeflationKernel B S T hST =
    finiteNegativeOneDeflationKernel A S T hST ≫
      (FiniteGroupTateCohomology.normKernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  dsimp only [Rep.quotientToInvariantsFunctor]
  let _ : Mono ((Limits.ker.ι (ModuleCat R)).app
      ((FiniteGroupTateCohomology.normArrowFunctor
        (R := R) (G := G ⧸ T)).obj (B.quotientToInvariants T))) := by
    dsimp [Limits.ker.ι, FiniteGroupTateCohomology.normArrowFunctor]
    infer_instance
  apply (cancel_mono ((Limits.ker.ι (ModuleCat R)).app
    ((FiniteGroupTateCohomology.normArrowFunctor
      (R := R) (G := G ⧸ T)).obj (B.quotientToInvariants T)))).1
  simp only [Category.assoc, finiteNegativeOneDeflationKernel_ι_functor]
  rw [← Category.assoc,
    FiniteGroupTateCohomology.normKernelFunctor_map_ι]
  have hcoinv := finiteNegativeDeflationCoinvariants_naturality f S T hST
  dsimp only [Rep.quotientToInvariantsFunctor] at hcoinv
  rw [Category.assoc, hcoinv]
  have hdef := finiteNegativeOneDeflationKernel_ι_functor A S T hST
  have htarget := FiniteGroupTateCohomology.normKernelFunctor_map_ι
    ((Rep.quotientToInvariantsFunctor R T).map f)
  dsimp only [Rep.quotientToInvariantsFunctor] at htarget
  have e₁ := congrArg (fun k ↦ k ≫
      (Rep.coinvariantsFunctor R (G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f)) hdef.symm
  have e₂ := congrArg (fun k ↦
      finiteNegativeOneDeflationKernel A S T hST ≫ k) htarget.symm
  dsimp only [Rep.quotientToInvariantsFunctor] at e₁ e₂
  simp only [Category.assoc] at e₁ e₂ ⊢
  exact e₁.trans e₂

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The cokernel realization of degree `0` deflation is natural in the
coefficient representation. -/
@[reassoc]
lemma finiteZeroDeflationCokernel_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteZeroDeflationCokernel B S T hST =
    finiteZeroDeflationCokernel A S T hST ≫
      (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  dsimp only [Rep.quotientToInvariantsFunctor]
  let _ : Epi ((Limits.coker.π (ModuleCat R)).app
      ((FiniteGroupTateCohomology.normArrowFunctor
        (R := R) (G := G ⧸ S)).obj (A.quotientToInvariants S))) := by
    dsimp [Limits.coker.π, FiniteGroupTateCohomology.normArrowFunctor]
    infer_instance
  apply (cancel_epi ((Limits.coker.π (ModuleCat R)).app
    ((FiniteGroupTateCohomology.normArrowFunctor
      (R := R) (G := G ⧸ S)).obj (A.quotientToInvariants S)))).1
  simp only [← Category.assoc,
    FiniteGroupTateCohomology.normCokernelFunctor_π_map]
  rw [Category.assoc, finiteZeroDeflationCokernel_π_functor]
  have hinv := finiteLevelTotalInvariantsEquiv_naturality f S T hST
  dsimp only [Rep.quotientToInvariantsFunctor] at hinv
  rw [← Category.assoc, hinv]
  have htarget := FiniteGroupTateCohomology.normCokernelFunctor_π_map
    ((Rep.quotientToInvariantsFunctor R T).map f)
  have hdef := finiteZeroDeflationCokernel_π_functor A S T hST
  dsimp only [Rep.quotientToInvariantsFunctor] at htarget
  have e₁ := congrArg (fun k ↦
      (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫ k)
    htarget.symm
  have e₂ := congrArg (fun k ↦ k ≫
      (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f)) hdef.symm
  dsimp only [Rep.quotientToInvariantsFunctor] at e₁ e₂
  simp only [Category.assoc] at e₁ e₂ ⊢
  exact e₁.trans e₂

set_option backward.isDefEq.respectTransparency false in
/-- Finite-level deflation in Tate degree `-1`, obtained from the induced map
between kernels of finite-group norms. -/
noncomputable def finiteNegativeOneDeflation (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    tateCohomology (A.quotientToInvariants S) (-1) ⟶
      tateCohomology (A.quotientToInvariants T) (-1) :=
  (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
      (A.quotientToInvariants S)).hom ≫
    finiteNegativeOneDeflationKernel A S T hST ≫
    (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
      (A.quotientToInvariants T)).inv

set_option backward.isDefEq.respectTransparency false in
/-- Finite-level deflation in Tate degree `0`, obtained from the induced map
between cokernels of finite-group norms. -/
noncomputable def finiteZeroDeflation (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    tateCohomology (A.quotientToInvariants S) 0 ⟶
      tateCohomology (A.quotientToInvariants T) 0 :=
  (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
      (A.quotientToInvariants S)).hom ≫
    finiteZeroDeflationCokernel A S T hST ≫
    (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
      (A.quotientToInvariants T)).inv

/-- Degree `-1` deflation agrees with the map between kernels of the two
finite-group norms. -/
@[reassoc]
lemma finiteNegativeOneDeflation_comp_kernelNormIso_hom
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants T)).hom =
      (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants S)).hom ≫
        finiteNegativeOneDeflationKernel A S T hST := by
  simp [finiteNegativeOneDeflation]

/-- Degree `0` deflation agrees with the map between cokernels of the two
finite-group norms. -/
@[reassoc]
lemma finiteZeroDeflation_comp_cokernelNormIso_hom
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteZeroDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants T)).hom =
      (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants S)).hom ≫
        finiteZeroDeflationCokernel A S T hST := by
  simp [finiteZeroDeflation]

set_option backward.isDefEq.respectTransparency false in
private lemma finiteNegativeOneDeflation_comp_kernelNormNatIso_hom_app
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
          (R := R) (G := G ⧸ T)).hom.app (A.quotientToInvariants T) =
      (FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
          (R := R) (G := G ⧸ S)).hom.app (A.quotientToInvariants S) ≫
        finiteNegativeOneDeflationKernel A S T hST :=
  by
    simpa only [FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm_hom_app]
      using finiteNegativeOneDeflation_comp_kernelNormIso_hom A S T hST

set_option backward.isDefEq.respectTransparency false in
private lemma finiteZeroDeflation_comp_cokernelNormNatIso_hom_app
    (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteZeroDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
          (R := R) (G := G ⧸ T)).hom.app (A.quotientToInvariants T) =
      (FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
          (R := R) (G := G ⧸ S)).hom.app (A.quotientToInvariants S) ≫
        finiteZeroDeflationCokernel A S T hST :=
  by
    simpa only [FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm_hom_app]
      using finiteZeroDeflation_comp_cokernelNormIso_hom A S T hST

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-level degree `-1` deflation is natural in the coefficient
representation. -/
@[reassoc]
lemma finiteNegativeOneDeflation_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (tateCohomologyFunctor (R := R) (G := G ⧸ S) (-1)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeOneDeflation B S T hST =
    finiteNegativeOneDeflation A S T hST ≫
      (tateCohomologyFunctor (R := R) (G := G ⧸ T) (-1)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  dsimp only [Rep.quotientToInvariantsFunctor]
  apply (cancel_mono
    ((FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
      (R := R) (G := G ⧸ T)).hom.app (B.quotientToInvariants T))).1
  have hB := finiteNegativeOneDeflation_comp_kernelNormNatIso_hom_app
    B S T hST
  have hS :=
    (FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
      (R := R) (G := G ⧸ S)).hom.naturality
        ((Rep.quotientToInvariantsFunctor R S).map f)
  have hD := finiteNegativeOneDeflationKernel_naturality f S T hST
  have hA := finiteNegativeOneDeflation_comp_kernelNormNatIso_hom_app
    A S T hST
  have hT :=
    (FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
      (R := R) (G := G ⧸ T)).hom.naturality
        ((Rep.quotientToInvariantsFunctor R T).map f)
  dsimp only [Rep.quotientToInvariantsFunctor] at hS hD hT
  have e₁ := congrArg (fun k ↦
      (tateCohomologyFunctor (R := R) (G := G ⧸ S) (-1)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫ k) hB
  have e₂ := congrArg (fun k ↦ k ≫
      finiteNegativeOneDeflationKernel B S T hST) hS
  have e₃ := congrArg (fun k ↦
      (FiniteGroupTateCohomology.tateCohomologyNegOneNatIsoKernelNorm
        (R := R) (G := G ⧸ S)).hom.app (A.quotientToInvariants S) ≫ k) hD
  have e₄ := congrArg (fun k ↦ k ≫
      (FiniteGroupTateCohomology.normKernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f)) hA.symm
  have e₅ := congrArg (fun k ↦
      finiteNegativeOneDeflation A S T hST ≫ k) hT.symm
  dsimp only [Rep.quotientToInvariantsFunctor] at e₁ e₄ e₅
  simp only [Category.assoc] at e₁ e₂ e₃ e₄ e₅ ⊢
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-level degree `0` deflation is natural in the coefficient
representation. -/
@[reassoc]
lemma finiteZeroDeflation_naturality
    {A B : Rep.{u} R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (tateCohomologyFunctor (R := R) (G := G ⧸ S) 0).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteZeroDeflation B S T hST =
    finiteZeroDeflation A S T hST ≫
      (tateCohomologyFunctor (R := R) (G := G ⧸ T) 0).map
        ((Rep.quotientToInvariantsFunctor R T).map f) := by
  dsimp only [Rep.quotientToInvariantsFunctor]
  apply (cancel_mono
    ((FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
      (R := R) (G := G ⧸ T)).hom.app (B.quotientToInvariants T))).1
  have hB := finiteZeroDeflation_comp_cokernelNormNatIso_hom_app B S T hST
  have hS :=
    (FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
      (R := R) (G := G ⧸ S)).hom.naturality
        ((Rep.quotientToInvariantsFunctor R S).map f)
  have hD := finiteZeroDeflationCokernel_naturality f S T hST
  have hA := finiteZeroDeflation_comp_cokernelNormNatIso_hom_app A S T hST
  have hT :=
    (FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
      (R := R) (G := G ⧸ T)).hom.naturality
        ((Rep.quotientToInvariantsFunctor R T).map f)
  dsimp only [Rep.quotientToInvariantsFunctor] at hS hD hT
  have e₁ := congrArg (fun k ↦
      (tateCohomologyFunctor (R := R) (G := G ⧸ S) 0).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫ k) hB
  have e₂ := congrArg (fun k ↦ k ≫
      finiteZeroDeflationCokernel B S T hST) hS
  have e₃ := congrArg (fun k ↦
      (FiniteGroupTateCohomology.tateCohomologyZeroNatIsoCokernelNorm
        (R := R) (G := G ⧸ S)).hom.app (A.quotientToInvariants S) ≫ k) hD
  have e₄ := congrArg (fun k ↦ k ≫
      (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f)) hA.symm
  have e₅ := congrArg (fun k ↦
      finiteZeroDeflation A S T hST ≫ k) hT.symm
  dsimp only [Rep.quotientToInvariantsFunctor] at e₁ e₄ e₅
  simp only [Category.assoc] at e₁ e₂ e₃ e₄ e₅ ⊢
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

end ContinuousGroupCohomology
