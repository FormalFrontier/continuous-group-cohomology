/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import ContinuousGroupCohomology.TopRepUlift

/-!
# Continuous cohomology in degree one

This file packages continuous crossed homomorphisms and principal cocycles for
a topological representation whose represented action is jointly continuous.
It also gives the functorial continuous maps on crossed homomorphisms and their
quotients induced by coefficient morphisms.
The comparison `degreeOneIso` requires joint continuity of the action and
local compactness of the group.
-/

set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

/-- Continuous additive crossed homomorphisms for the action carried by `X`.
The defining relation is needed to construct functorial crossed maps. -/
@[expose]
def continuousCrossedHom : Submodule k C(G, X) where
  carrier := {f | ∀ g h, f (g * h) = X.ρ g (f h) + f g}
  zero_mem' := by simp
  add_mem' := by
    intro f f' hf hf' g h
    simp only [ContinuousMap.add_apply]
    rw [hf g h, hf' g h, map_add]
    abel
  smul_mem' := by
    intro r f hf g h
    simp only [ContinuousMap.smul_apply]
    rw [hf g h, map_smul, smul_add]

/-- The continuous principal crossed homomorphism attached to a coefficient.
Its orbit-map formula is needed by the continuous principal-cocycle comparison. -/
@[expose]
def principalMap [TopRep.JointlyContinuous X] : X →ₗ[k] C(G, X) where
  toFun x :=
    ⟨fun g => X.ρ g x - x,
      (TopRep.JointlyContinuous.continuous_action (X := X)).comp
          (continuous_id.prodMk continuous_const) |>.sub continuous_const⟩
  map_add' x y := by
    ext g
    change X.ρ g (x + y) - (x + y) = (X.ρ g x - x) + (X.ρ g y - y)
    rw [map_add]
    abel
  map_smul' r x := by
    ext g
    change X.ρ g (r • x) - r • x = r • (X.ρ g x - x)
    rw [map_smul, smul_sub]

/-- Principal crossed homomorphisms, regarded inside all continuous crossed homomorphisms.
The underlying map is used to establish continuity of `principalToCrossedL`. -/
@[expose]
def principalToCrossed [TopRep.JointlyContinuous X] :
    X →ₗ[k] continuousCrossedHom X where
  toFun x := ⟨principalMap X x, by
    intro g h
    change X.ρ (g * h) x - x = X.ρ g (X.ρ h x - x) + (X.ρ g x - x)
    rw [map_mul]
    change X.ρ g (X.ρ h x) - x = X.ρ g (X.ρ h x - x) + (X.ρ g x - x)
    rw [map_sub]
    abel⟩
  map_add' x y := by
    ext g
    change X.ρ g (x + y) - (x + y) = (X.ρ g x - x) + (X.ρ g y - y)
    rw [map_add]
    abel
  map_smul' r x := by
    ext g
    change X.ρ g (r • x) - r • x = r • (X.ρ g x - x)
    rw [map_smul, smul_sub]

/-- The submodule of principal continuous crossed homomorphisms.
Its range presentation reduces when comparing quotient maps. -/
@[expose]
def principalCocycles [TopRep.JointlyContinuous X] :
    Submodule k (continuousCrossedHom X) :=
  LinearMap.range (principalToCrossed X)

variable {A B C : TopRep.{max v w} k G}

/-- A coefficient morphism sends continuous crossed homomorphisms forward.
Its application to a cocycle computes pointwise in external clients. -/
@[expose]
def crossedMap (q : A ⟶ B) :
    continuousCrossedHom A →L[k] continuousCrossedHom B :=
  ((ContinuousLinearMap.compLeftContinuous k G q.hom.toContinuousLinearMap).comp
      (Submodule.subtypeL (continuousCrossedHom A))).codRestrict
    (continuousCrossedHom B) fun f g h => by
      change q (f.1 (g * h)) = B.ρ g (q (f.1 h)) + q (f.1 g)
      rw [f.2, map_add, TopRep.hom_comm_apply]

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedMap_apply (q : A ⟶ B) (f : continuousCrossedHom A) (g : G) :
    (crossedMap q f).1 g = q (f.1 g) := rfl

omit [IsTopologicalGroup G] in
lemma crossedMap_principal (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (x : A) :
    crossedMap q (principalToCrossed A x) = principalToCrossed B (q x) := by
  ext g
  change q (A.ρ g x - x) = B.ρ g (q x) - q x
  rw [map_sub, TopRep.hom_comm_apply]

/-- A coefficient morphism descends to continuous crossed homomorphisms modulo principals.
Its lift computes on quotient representatives. -/
@[expose]
def crossedQuotientMap (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    (continuousCrossedHom A ⧸ principalCocycles A) →L[k]
      (continuousCrossedHom B ⧸ principalCocycles B) :=
  (principalCocycles A).liftQL
    ((principalCocycles B).mkQL.comp (crossedMap q)) <| by
      intro f hf
      rw [LinearMap.mem_ker]
      change (principalCocycles B).mkQL (crossedMap q f) = 0
      change f ∈ LinearMap.range (principalToCrossed A) at hf
      rcases hf with ⟨x, rfl⟩
      rw [crossedMap_principal]
      exact (Submodule.Quotient.mk_eq_zero (principalCocycles B)).2 ⟨q x, rfl⟩

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedQuotientMap_mk (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (f : continuousCrossedHom A) :
    crossedQuotientMap q ((principalCocycles A).mkQ f) =
      (principalCocycles B).mkQ (crossedMap q f) := rfl

omit [IsTopologicalGroup G] in
lemma crossedMap_id : crossedMap (𝟙 A) = ContinuousLinearMap.id k _ := by
  ext f g
  rfl

omit [IsTopologicalGroup G] in
lemma crossedMap_comp (q : A ⟶ B) (r : B ⟶ C) :
    crossedMap (q ≫ r) = (crossedMap r).comp (crossedMap q) := by
  ext f g
  rfl

omit [IsTopologicalGroup G] in
lemma crossedQuotientMap_id [TopRep.JointlyContinuous A] :
    crossedQuotientMap (𝟙 A) = ContinuousLinearMap.id k _ := by
  apply ContinuousLinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  rfl

omit [IsTopologicalGroup G] in
lemma crossedQuotientMap_comp (q : A ⟶ B) (r : B ⟶ C)
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous C] :
    crossedQuotientMap (q ≫ r) =
      (crossedQuotientMap r).comp (crossedQuotientMap q) := by
  apply ContinuousLinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  rfl

/-- The orbit map of a coefficient, regarded as a continuous map on the group.
Its pointwise action formula identifies continuous principal cocycles. -/
@[expose]
def orbitMap [TopRep.JointlyContinuous X] : X →L[k] C(G, X) where
  toFun x := ⟨fun g => X.ρ g x,
    (TopRep.JointlyContinuous.continuous_action (X := X)).comp
      (continuous_id.prodMk continuous_const)⟩
  map_add' x y := by ext g; exact map_add (X.ρ g) x y
  map_smul' r x := by ext g; exact map_smul (X.ρ g) r x
  cont := ContinuousMap.continuous_of_continuous_uncurry _ <|
    (TopRep.JointlyContinuous.continuous_action (X := X)).comp
      (continuous_snd.prodMk continuous_fst)

/-- Evaluation at the identity identifies homogeneous degree-zero cochains
with their coefficient representation when the represented action is jointly
continuous. -/
@[expose]
def cochainsZeroEquiv [TopRep.JointlyContinuous X] :
    (TopRep.homogeneousCochains X).X 0 ≃L[k] X where
  toFun σ := σ.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨orbitMap X x, by
        intro g
        apply DFunLike.ext _ _
        intro h
        simp only [ContRepresentation.coind₁_apply_apply, orbitMap,
          ContinuousLinearMap.coe_mk']
        change X.ρ g (X.ρ (g⁻¹ * h) x) = X.ρ h x
        calc
          _ = (X.ρ g * X.ρ (g⁻¹ * h)) x :=
            (mul_apply_eq_comp _ _ _).symm
          _ = X.ρ (g * (g⁻¹ * h)) x := by
            rw [← map_mul X.ρ g (g⁻¹ * h)]
          _ = _ := by simp⟩
  left_inv σ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    change X.ρ g (σ.1 1) = σ.1 g
    simpa [ContRepresentation.coind₁_apply_apply] using DFunLike.congr_fun (σ.2 g) g
  right_inv x := by
    change X.ρ 1 x = x
    simp
  continuous_toFun := (continuous_eval_const 1).comp continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 (orbitMap X).continuous

@[simp]
theorem cochainsZeroEquiv_apply [TopRep.JointlyContinuous X]
    (σ : (TopRep.homogeneousCochains X).X 0) :
    cochainsZeroEquiv X σ = σ.1 1 := rfl

@[simp]
theorem cochainsZeroEquiv_symm_apply [TopRep.JointlyContinuous X]
    (x : X) (g : G) :
    ((cochainsZeroEquiv X).symm x).1 g = X.ρ g x := rfl

/-- The homogeneous degree-one cochain associated to a continuous crossed
homomorphism. -/
def homogeneousOne [TopRep.JointlyContinuous X] (f : continuousCrossedHom X) :
    C(G, C(G, X)) where
  toFun g := ⟨fun h => X.ρ g (f.1 (g⁻¹ * h)),
    (X.ρ g).continuous.comp (f.1.continuous.comp (continuous_const.inv.mul continuous_id))⟩
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _ <|
    (TopRep.JointlyContinuous.continuous_action (X := X)).comp <|
      continuous_fst.prodMk <| f.1.continuous.comp (continuous_fst.inv.mul continuous_snd)

lemma homogeneousOne_mem_invariants [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom X) :
    homogeneousOne X f ∈ ((TopRep.resolution' X).X 1).ρ.invariants := by
  intro a
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  simp only [ContRepresentation.coind₁_apply_apply, homogeneousOne]
  change X.ρ a (X.ρ (a⁻¹ * g) (f.1 ((a⁻¹ * g)⁻¹ * (a⁻¹ * h)))) =
    X.ρ g (f.1 (g⁻¹ * h))
  calc
    _ = (X.ρ a * X.ρ (a⁻¹ * g)) (f.1 ((a⁻¹ * g)⁻¹ * (a⁻¹ * h))) :=
      (mul_apply_eq_comp _ _ _).symm
    _ = X.ρ (a * (a⁻¹ * g)) (f.1 ((a⁻¹ * g)⁻¹ * (a⁻¹ * h))) := by
      rw [← map_mul X.ρ]
    _ = _ := by simp

lemma homogeneousOne_mem_ker [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom X) :
    ⟨homogeneousOne X f, homogeneousOne_mem_invariants X f⟩ ∈
      ((TopRep.homogeneousCochains X).d 1 2).hom.ker := by
  rw [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.coe_coe,
    TopRep.homogeneousCochains.d_apply]
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  apply ContinuousMap.ext
  intro j
  change X.ρ h (f.1 (h⁻¹ * j)) -
    (X.ρ g (f.1 (g⁻¹ * j)) - X.ρ g (f.1 (g⁻¹ * h))) = 0
  have hf : f.1 (g⁻¹ * j) =
      X.ρ (g⁻¹ * h) (f.1 (h⁻¹ * j)) + f.1 (g⁻¹ * h) := by
    simpa [mul_assoc] using f.2 (g⁻¹ * h) (h⁻¹ * j)
  have haction (y : X) : X.ρ g (X.ρ (g⁻¹ * h) y) = X.ρ h y := by
    calc
      _ = (X.ρ g * X.ρ (g⁻¹ * h)) y := (mul_apply_eq_comp _ _ _).symm
      _ = X.ρ (g * (g⁻¹ * h)) y := by rw [← map_mul X.ρ]
      _ = _ := by simp
  have hf' := congrArg (fun y : X => X.ρ g y) hf
  rw [map_add, haction] at hf'
  rw [hf']
  abel

lemma oneKer_isCrossed
    (σ : ((TopRep.homogeneousCochains X).d 1 2).hom.ker) (g h : G) :
    σ.1.1 1 (g * h) = X.ρ g (σ.1.1 1 h) + σ.1.1 1 g := by
  have hinv := congrArg (fun F : C(G, C(G, X)) => F g (g * h)) (σ.1.2 g)
  simp only [ContRepresentation.coind₁_apply_apply] at hinv
  have hinv' : X.ρ g (σ.1.1 1 h) = σ.1.1 g (g * h) := by simpa using hinv
  have hcycle := σ.2
  rw [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.coe_coe,
    TopRep.homogeneousCochains.d_apply] at hcycle
  have hcycle' := congrArg (fun F : C(G, C(G, C(G, X))) => F 1 g (g * h)) hcycle
  change σ.1.1 g (g * h) - (σ.1.1 1 (g * h) - σ.1.1 1 g) = 0 at hcycle'
  rw [hinv']
  rw [sub_eq_zero] at hcycle'
  rw [hcycle']
  abel

/-- Evaluation at `(1, ·)` sends homogeneous degree-one cocycles to continuous
crossed homomorphisms. -/
def oneKerToCrossed :
    ((TopRep.homogeneousCochains X).d 1 2).hom.ker →ₗ[k] continuousCrossedHom X where
  toFun σ := ⟨σ.1.1 1, oneKer_isCrossed X σ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A continuous crossed homomorphism, regarded as a homogeneous degree-one
cocycle. -/
def crossedToOneKer [TopRep.JointlyContinuous X] :
    continuousCrossedHom X →ₗ[k]
      ((TopRep.homogeneousCochains X).d 1 2).hom.ker where
  toFun f := ⟨⟨homogeneousOne X f, homogeneousOne_mem_invariants X f⟩,
    homogeneousOne_mem_ker X f⟩
  map_add' f f' := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    simp [homogeneousOne, map_add]
  map_smul' r f := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    simp [homogeneousOne, map_smul]

/-- Algebraically, homogeneous degree-one cocycles are continuous crossed
homomorphisms. -/
def oneKerLinearEquiv [TopRep.JointlyContinuous X] :
    ((TopRep.homogeneousCochains X).d 1 2).hom.ker ≃ₗ[k] continuousCrossedHom X where
  __ := oneKerToCrossed X
  invFun := crossedToOneKer X
  left_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    have hinv := congrArg (fun F : C(G, C(G, X)) => F g h) (σ.1.2 g)
    simp only [ContRepresentation.coind₁_apply_apply] at hinv
    change X.ρ g (σ.1.1 1 (g⁻¹ * h)) = σ.1.1 g h
    simpa using hinv
  right_inv f := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    simp [oneKerToCrossed, crossedToOneKer, homogeneousOne]

lemma continuous_homogeneousOne [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    Continuous fun f : continuousCrossedHom X => homogeneousOne X f := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun p : (continuousCrossedHom X × G) × G =>
    X.ρ p.1.2 (p.1.1.1 (p.1.2⁻¹ * p.2))
  exact (TopRep.JointlyContinuous.continuous_action (X := X)).comp <|
    (continuous_snd.comp continuous_fst).prodMk <|
      continuous_eval.comp <|
        (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk <|
          (continuous_snd.comp continuous_fst).inv.mul continuous_snd

/-- For a locally compact group, homogeneous degree-one cocycles and continuous
crossed homomorphisms are continuously linearly equivalent. -/
def oneKerEquiv [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    ((TopRep.homogeneousCochains X).d 1 2).hom.ker ≃L[k] continuousCrossedHom X where
  __ := oneKerLinearEquiv X
  continuous_toFun := continuous_induced_rng.2 <| (continuous_eval_const 1).comp <|
    continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 <| continuous_induced_rng.2 <|
    continuous_homogeneousOne X

noncomputable def cochainsZeroIso [TopRep.JointlyContinuous X] :
    (TopRep.homogeneousCochains X).X 0 ≅ TopModuleCat.of k X :=
  TopModuleCat.ofIso (cochainsZeroEquiv X)

@[simp]
theorem cochainsZeroIso_hom_apply [TopRep.JointlyContinuous X]
    (σ : (TopRep.homogeneousCochains X).X 0) :
    (cochainsZeroIso X).hom.hom σ = σ.1 1 :=
  cochainsZeroEquiv_apply X σ

@[simp]
theorem cochainsZeroIso_inv_apply [TopRep.JointlyContinuous X]
    (x : X) (g : G) : ((cochainsZeroIso X).inv.hom x).1 g = X.ρ g x :=
  cochainsZeroEquiv_symm_apply X x g

noncomputable def oneKerCrossedIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] :
    TopModuleCat.of k ((TopRep.homogeneousCochains X).d 1 2).hom.ker ≅
      TopModuleCat.of k (continuousCrossedHom X) :=
  TopModuleCat.ofIso (oneKerEquiv X)

/-- The principal-cocycle map as a continuous linear map.
Its underlying linear map reduces to `principalToCrossed`. -/
@[expose]
def principalToCrossedL [TopRep.JointlyContinuous X] :
    X →L[k] continuousCrossedHom X where
  __ := principalToCrossed X
  cont := continuous_induced_rng.2 <|
    (orbitMap X).continuous.sub ContinuousMap.continuous_const'

omit [IsTopologicalGroup G] in
lemma principalToCrossedL_toLinearMap [TopRep.JointlyContinuous X] :
    (principalToCrossedL X).toLinearMap = principalToCrossed X := rfl

omit [IsTopologicalGroup G] in
lemma crossedMap_comp_mkQL (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    TopModuleCat.ofHom (crossedMap q) ≫
        TopModuleCat.ofHom (principalCocycles B).mkQL =
      TopModuleCat.ofHom (principalCocycles A).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientMap q) := by
  ext f
  rfl

/-- The abstract degree-one cocycles of the homogeneous complex, identified
with the explicit kernel of its degree-one differential. -/
noncomputable abbrev cocyclesOneIso : cocycles X 1 ≅
    ↧((TopRep.homogeneousCochains X).d 1 2).hom.ker :=
  Limits.KernelFork.mapIsoOfIsLimit
    ((TopRep.homogeneousCochains X).cyclesIsKernel 1 2 (by simp))
    (TopModuleCat.isLimitKer _) (Iso.refl _)

/-- Degree-one homogeneous cocycles and continuous crossed homomorphisms as
topological modules. -/
noncomputable def cocyclesOneCrossedIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] : cocycles X 1 ≅ ↧(continuousCrossedHom X) :=
  cocyclesOneIso X ≪≫ oneKerCrossedIso X

/-- The degree-zero differential, with codomain restricted to the explicit
kernel of the degree-one differential. -/
noncomputable def boundaryToOneKer :
    (TopRep.homogeneousCochains X).X 0 ⟶
      ↧((TopRep.homogeneousCochains X).d 1 2).hom.ker :=
  TopModuleCat.ofHom <| ((TopRep.homogeneousCochains X).d 0 1).hom.codRestrict
    ((TopRep.homogeneousCochains X).d 1 2).hom.ker fun σ => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        ← ConcreteCategory.comp_apply ((TopRep.homogeneousCochains X).d 0 1)
          ((TopRep.homogeneousCochains X).d 1 2),
        (TopRep.homogeneousCochains X).d_comp_d, TopModuleCat.hom_zero_apply]

lemma cocyclesOneIso_hom_comp_kerι :
    (cocyclesOneIso X).hom ≫ TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 1 2) =
      (TopRep.homogeneousCochains X).iCycles 1 := by
  ext σ
  rfl

lemma cocyclesOneCrossedIso_hom_apply [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] (σ : cocycles X 1) (g : G) :
    ((cocyclesOneCrossedIso X).hom σ).1 g =
      ((TopRep.homogeneousCochains X).iCycles 1 σ).1 1 g := by
  change (((cocyclesOneIso X).hom σ).1.1 1 g) = _
  have h := ConcreteCategory.congr_hom (cocyclesOneIso_hom_comp_kerι (X := X)) σ
  exact congrArg (fun τ => τ.1 1 g) h

/-- The identification of homogeneous one-cocycles with continuous crossed
homomorphisms commutes with coefficient morphisms. -/
lemma cocyclesOneCrossedIso_natural (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] [LocallyCompactSpace G] :
    cocyclesMap (ContinuousMonoidHom.id G) q 1 ≫
        (cocyclesOneCrossedIso B).hom =
      (cocyclesOneCrossedIso A).hom ≫ TopModuleCat.ofHom (crossedMap q) := by
  ext σ g
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom, crossedMap_apply]
  rw [cocyclesOneCrossedIso_hom_apply, cocyclesOneCrossedIso_hom_apply]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) q) 1) σ
  exact congrArg (fun τ => τ.1 1 g) h

lemma toCycles_comp_cocyclesOneIso :
    (TopRep.homogeneousCochains X).toCycles 0 1 ≫ (cocyclesOneIso X).hom =
      boundaryToOneKer X := by
  rw [← cancel_mono (TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 1 2)),
    Category.assoc, cocyclesOneIso_hom_comp_kerι,
    HomologicalComplex.toCycles_i]
  rfl

lemma boundaryToOneKer_comm [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    boundaryToOneKer X ≫ (oneKerCrossedIso X).hom =
      (cochainsZeroIso X).hom ≫
        TopModuleCat.ofHom (principalToCrossedL X) := by
  ext σ g
  change σ.1 g - σ.1 1 = X.ρ g (σ.1 1) - σ.1 1
  have hinv := congrArg (fun f : C(G, X) => f g) (σ.2 g)
  simp only [ContRepresentation.coind₁_apply_apply] at hinv
  rw [← hinv]
  simp

lemma toCycles_comp_cocyclesOneCrossedIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] :
    (TopRep.homogeneousCochains X).toCycles 0 1 ≫ (cocyclesOneCrossedIso X).hom =
      (cochainsZeroIso X).hom ≫ TopModuleCat.ofHom (principalToCrossedL X) := by
  rw [cocyclesOneCrossedIso, Iso.trans_hom, ← Category.assoc,
    toCycles_comp_cocyclesOneIso, boundaryToOneKer_comm]

noncomputable def boundaryArrowIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] :
    Arrow.mk ((TopRep.homogeneousCochains X).toCycles 0 1) ≅
      Arrow.mk (TopModuleCat.ofHom (principalToCrossedL X)) :=
  Arrow.isoMk (cochainsZeroIso X) (cocyclesOneCrossedIso X)
    (toCycles_comp_cocyclesOneCrossedIso X).symm

/-- The first continuous cohomology object, identified with the quotient of
continuous crossed homomorphisms by principal cocycles. The canonical inverse
computes in the corestriction comparison. -/
@[expose]
noncomputable def homologyQuotientIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] :
    continuousCohomology 1 X ≅
      TopModuleCat.of k (continuousCrossedHom X ⧸ principalCocycles X) :=
  Limits.CokernelCofork.mapIsoOfIsColimit
    ((TopRep.homogeneousCochains X).homologyIsCokernel 0 1 (by simp))
    (TopModuleCat.isColimitCoker (TopModuleCat.ofHom (principalToCrossedL X)))
    (boundaryArrowIso X)

set_option backward.isDefEq.respectTransparency false in
lemma π_comp_homologyQuotientIso [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] :
    π X 1 ≫ (homologyQuotientIso X).hom =
      (cocyclesOneCrossedIso X).hom ≫
        TopModuleCat.ofHom (principalCocycles X).mkQL := by
  have h := Limits.CokernelCofork.π_mapOfIsColimit
    ((TopRep.homogeneousCochains X).homologyIsCokernel 0 1 (by simp))
    (Limits.CokernelCofork.ofπ
      (TopModuleCat.cokerπ (TopModuleCat.ofHom (principalToCrossedL X))) (by simp))
    (boundaryArrowIso X).hom
  simpa [homologyQuotientIso, boundaryArrowIso, TopModuleCat.cokerπ,
    principalCocycles, Submodule.mkQL, principalToCrossedL_toLinearMap] using h

set_option backward.isDefEq.respectTransparency false in
/-- The degree-one cohomology-to-crossed-quotient identification commutes with
mathlib's native coefficient map. -/
@[reassoc]
lemma homologyQuotientIso_natural (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] [LocallyCompactSpace G] :
    map (ContinuousMonoidHom.id G) q 1 ≫ (homologyQuotientIso B).hom =
      (homologyQuotientIso A).hom ≫ TopModuleCat.ofHom (crossedQuotientMap q) := by
  apply (cancel_epi (π A 1)).1
  rw [← Category.assoc, π_map, Category.assoc, π_comp_homologyQuotientIso,
    ← Category.assoc, cocyclesOneCrossedIso_natural, Category.assoc,
    crossedMap_comp_mkQL, ← Category.assoc, ← π_comp_homologyQuotientIso,
    Category.assoc]

/-- Continuous crossed homomorphisms modulo principal cocycles compute first
continuous cohomology. Its inverse computes as `homologyQuotientIso`. -/
@[expose]
noncomputable def degreeOneIso [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    TopModuleCat.of k (continuousCrossedHom X ⧸ principalCocycles X) ≅
      continuousCohomology 1 X :=
  (homologyQuotientIso X).symm

lemma degreeOneIso_inv [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    (degreeOneIso X).inv = (homologyQuotientIso X).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The crossed-quotient-to-degree-one-cohomology identification commutes with
mathlib's native coefficient map. -/
@[reassoc]
lemma degreeOneIso_natural (q : A ⟶ B) [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] [LocallyCompactSpace G] :
    TopModuleCat.ofHom (crossedQuotientMap q) ≫ (degreeOneIso B).hom =
      (degreeOneIso A).hom ≫ map (ContinuousMonoidHom.id G) q 1 := by
  apply (cancel_mono (homologyQuotientIso B).hom).1
  rw [degreeOneIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, homologyQuotientIso_natural, ← Category.assoc,
    degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

end ContinuousCohomology
