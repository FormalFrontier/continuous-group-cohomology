/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactAddCommGroup
public import ContinuousGroupCohomology.LevelCompactNorm
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# Compact topologies on finite-group coinvariants

For a finite group acting continuously on a compact Hausdorff additive
commutative group, the algebraic coinvariants carry a canonical compact
Hausdorff quotient topology.  The relation submodule is closed because it is
the range of one continuous orbit-difference map out of a finite product.

This file also packages continuous invariant homomorphisms out of the
representation as continuous homomorphisms out of the resulting coinvariants.
The construction uses no topology on the coefficient ring.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology

universe uR uH uM

variable {R : Type uR} [CommRing R]
variable {H : Type uH} [Group H] [Fintype H]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The finite orbit-difference map
`(x_g)_g ↦ ∑ g, (g x_g - x_g)`. -/
@[expose] def finiteOrbitDifference (ρ : Representation R H M) :
    (Fin (Fintype.card H) → M) →ₗ[R] M where
  toFun x := ∑ i : Fin (Fintype.card H),
    ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i)
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' r x := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub, Finset.smul_sum]

@[simp]
lemma finiteOrbitDifference_apply (ρ : Representation R H M)
    (x : Fin (Fintype.card H) → M) :
    finiteOrbitDifference ρ x = ∑ i : Fin (Fintype.card H),
      ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i) :=
  rfl

@[simp]
lemma finiteOrbitDifference_single (ρ : Representation R H M) (g : H) (x : M) :
    finiteOrbitDifference ρ (Pi.single (Fintype.equivFin H g) x) = ρ g x - x := by
  classical
  rw [finiteOrbitDifference_apply,
    Finset.sum_eq_single (Fintype.equivFin H g)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

/-- The range of the finite orbit-difference map is exactly the relation
submodule defining algebraic coinvariants. -/
lemma finiteOrbitDifference_range (ρ : Representation R H M) :
    (finiteOrbitDifference ρ).range = Representation.Coinvariants.ker ρ := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change (∑ i : Fin (Fintype.card H),
      ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i)) ∈
        Representation.Coinvariants.ker ρ
    exact Submodule.sum_mem (Representation.Coinvariants.ker ρ) fun i _ ↦
      Representation.Coinvariants.sub_mem_ker
        ((Fintype.equivFin H).symm i) (x i)
  · rw [Representation.Coinvariants.ker, Submodule.span_le]
    rintro y ⟨⟨g, x⟩, rfl⟩
    exact ⟨Pi.single (Fintype.equivFin H g) x,
      finiteOrbitDifference_single ρ g x⟩

section Topology

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M]
  [T2Space M]

/-- The orbit-difference map as a continuous additive homomorphism. -/
def finiteOrbitDifferenceContinuousHom (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    (Fin (Fintype.card H) → M) →ₜ+ M where
  toAddMonoidHom := (finiteOrbitDifference ρ).toAddMonoidHom
  continuous_toFun := by
    change Continuous (fun x : Fin (Fintype.card H) → M ↦
      ∑ i : Fin (Fintype.card H),
        ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i))
    exact continuous_finsetSum Finset.univ fun i _ ↦
      ((hρ ((Fintype.equivFin H).symm i)).comp (continuous_apply i)).sub
        (continuous_apply i)

/-- The orbit-difference map in the category of compact Hausdorff additive
commutative groups. -/
def finiteOrbitDifferenceHom (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    CompHausAddCommGrp.of (Fin (Fintype.card H) → M) ⟶
      CompHausAddCommGrp.of M :=
  CompHausAddCommGrp.ofHom (finiteOrbitDifferenceContinuousHom ρ hρ)

lemma finiteOrbitDifferenceHom_range (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    (finiteOrbitDifferenceHom ρ hρ).hom.range =
      (Representation.Coinvariants.ker ρ).toAddSubgroup := by
  ext x
  change x ∈ (finiteOrbitDifference ρ).range ↔
    x ∈ Representation.Coinvariants.ker ρ
  rw [finiteOrbitDifference_range]

/-- The coinvariant relation subgroup is closed: it is the range of the
continuous finite orbit-difference map from a compact source. -/
@[expose] def coinvariantsClosedAddSubgroup (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) : ClosedAddSubgroup M where
  toAddSubgroup := (Representation.Coinvariants.ker ρ).toAddSubgroup
  isClosed' := by
    rw [← finiteOrbitDifferenceHom_range ρ hρ]
    exact (CompHausAddCommGrp.rangeClosedAddSubgroup
      (finiteOrbitDifferenceHom ρ hρ)).isClosed'

/-- Algebraic coinvariants equipped with their compact Hausdorff quotient
topology. -/
abbrev finiteCoinvariants (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) : CompHausAddCommGrp :=
  CompHausAddCommGrp.quotient (CompHausAddCommGrp.of M)
    (coinvariantsClosedAddSubgroup ρ hρ)

/-- The canonical continuous projection to finite coinvariants. -/
@[expose] def finiteCoinvariantsMk (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    CompHausAddCommGrp.of M ⟶ finiteCoinvariants ρ hρ :=
  ConcreteCategory.ofHom
    { toAddMonoidHom :=
        QuotientAddGroup.mk' (Representation.Coinvariants.ker ρ).toAddSubgroup
      continuous_toFun := QuotientAddGroup.continuous_mk }

@[simp]
lemma finiteCoinvariantsMk_apply (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (x : M) :
    finiteCoinvariantsMk ρ hρ x = Representation.Coinvariants.mk ρ x :=
  rfl

variable {N : Type uM} [AddCommGroup N] [Module R N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N]

/-- A continuous invariant linear map out of a finite-group representation
descends continuously to its compact coinvariants. -/
@[expose] def finiteCoinvariantsDesc (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (f : M →ₗ[R] N)
    (hf : Continuous f) (hinv : ∀ g : H, f ∘ₗ ρ g = f) :
    finiteCoinvariants ρ hρ ⟶ CompHausAddCommGrp.of N := by
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom :=
        (Representation.Coinvariants.lift ρ f hinv).toAddMonoidHom
      continuous_toFun := ?_ }
  exact continuous_coinduced_dom.2 hf

@[simp]
lemma finiteCoinvariantsDesc_mk (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (f : M →ₗ[R] N)
    (hf : Continuous f) (hinv : ∀ g : H, f ∘ₗ ρ g = f) (x : M) :
    finiteCoinvariantsDesc ρ hρ f hf hinv (Representation.Coinvariants.mk ρ x) =
      f x :=
  rfl

/-- A continuous intertwining map between finite-group representations induces
a continuous map on their compact coinvariants. -/
@[expose] noncomputable def finiteCoinvariantsMap (ρ : Representation R H M)
    (τ : Representation R H N) (hρ : ∀ g : H, Continuous (ρ g))
    (hτ : ∀ g : H, Continuous (τ g)) (f : ρ.IntertwiningMap τ)
    (hf : Continuous f) :
    finiteCoinvariants ρ hρ ⟶ finiteCoinvariants τ hτ := by
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom := (Representation.Coinvariants.map ρ τ f).toAddMonoidHom
      continuous_toFun := ?_ }
  apply continuous_coinduced_dom.2
  exact (finiteCoinvariantsMk τ hτ).hom.continuous.comp hf

@[simp]
lemma finiteCoinvariantsMap_mk (ρ : Representation R H M)
    (τ : Representation R H N) (hρ : ∀ g : H, Continuous (ρ g))
    (hτ : ∀ g : H, Continuous (τ g)) (f : ρ.IntertwiningMap τ)
    (hf : Continuous f) (x : M) :
    finiteCoinvariantsMap ρ τ hρ hτ f hf
        (Representation.Coinvariants.mk ρ x) =
      Representation.Coinvariants.mk τ (f x) :=
  rfl

end Topology

section Transversal

variable {G : Type uH} [Group G] (S : Subgroup G) [S.Normal]

/-- A right transversal of a normal subgroup is indexed by the usual quotient
group after inverting its representatives. -/
private noncomputable def rightTransversalQuotientEquiv
    (T : S.RightTransversal) : ↥(T : Set G) ≃ G ⧸ S :=
  T.2.rightQuotientEquiv.symm.trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)

@[simp]
private lemma rightTransversalQuotientEquiv_apply
    (T : S.RightTransversal) (t : ↥(T : Set G)) :
    rightTransversalQuotientEquiv S T t =
      QuotientGroup.mk' S ((t : G)⁻¹) :=
  rfl

end Transversal

namespace LevelCompact

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (A : Rep.{uA} R G) (L : LevelCompact A)

private lemma normal_le_map_conj (S : OpenNormalSubgroup G) (g : G) :
    S.toSubgroup ≤ S.toSubgroup.map (MulAut.conj g) := by
  intro s hs
  refine ⟨g⁻¹ * s * g, ?_, ?_⟩
  · change g⁻¹ * s * g ∈ S.toSubgroup
    simpa only [inv_inv] using
      (Subgroup.Normal.conj_mem (H := S.toSubgroup) (self := inferInstance)
        s hs g⁻¹)
  · simp [MulAut.conj_apply, mul_assoc]

/-- The compact Hausdorff additive group at one level of a `LevelCompact`
coefficient system. -/
@[expose] def group (U : OpenSubgroup G) : CompHausAddCommGrp.{uA} := by
  letI : TopologicalSpace (openSubgroupInvariants A U) := L.topology U
  letI : CompactSpace (openSubgroupInvariants A U) := L.compact U
  letI : T2Space (openSubgroupInvariants A U) := L.t2 U
  letI : IsTopologicalAddGroup (openSubgroupInvariants A U) :=
    L.topologicalAddGroup U
  exact CompHausAddCommGrp.of (openSubgroupInvariants A U)

/-- The residual `G / S`-action on `A^S` is continuous for the level topology. -/
lemma continuous_quotientToInvariants_action (S : OpenNormalSubgroup G)
    (q : G ⧸ S.toSubgroup) :
    @Continuous (A.quotientToInvariants S.toSubgroup)
      (A.quotientToInvariants S.toSubgroup) (L.topology S.toOpenSubgroup)
      (L.topology S.toOpenSubgroup)
      ((A.quotientToInvariants S.toSubgroup).ρ q) := by
  let g : G := q.out
  have hconj := normal_le_map_conj S g
  have heq : (A.quotientToInvariants S.toSubgroup).ρ q =
      openSubgroupInvariantsTransport A S.toOpenSubgroup S.toOpenSubgroup g hconj := by
    have hrep : (A.quotientToInvariants S.toSubgroup).ρ q =
        (A.quotientToInvariants S.toSubgroup).ρ
          (QuotientGroup.mk' S.toSubgroup g) :=
      congrArg (A.quotientToInvariants S.toSubgroup).ρ
        (Quotient.out_eq q).symm
    ext x
    change ((A.quotientToInvariants S.toSubgroup).ρ q x : A) = A.ρ g x
    rw [hrep]
    rfl
  rw [heq]
  exact L.continuous_transport S.toOpenSubgroup S.toOpenSubgroup g hconj

/-- The action of the full open subgroup on `S`-invariants. -/
private def topInvariantRepresentation (S : OpenNormalSubgroup G) :
    Representation R (⊤ : OpenSubgroup G)
      (openSubgroupInvariants A S.toOpenSubgroup) where
  toFun g := openSubgroupInvariantsTransport A S.toOpenSubgroup S.toOpenSubgroup
    (g : G) (normal_le_map_conj S g)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    change A.ρ ((g : G) * (h : G)) x = A.ρ (g : G) (A.ρ (h : G) x)
    rw [← Module.End.mul_apply, ← map_mul]

private instance topRelativeNormSubgroup_normal (S : OpenNormalSubgroup G) :
    (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup.Normal := by
  change (S.toSubgroup.comap (⊤ : OpenSubgroup G).subtype).Normal
  infer_instance

/-- The action on `S`-invariants factored through the finite quotient of the
full open subgroup by the pullback of `S`. -/
private def topQuotientInvariantRepresentation (S : OpenNormalSubgroup G) :
    Representation R
      ((⊤ : OpenSubgroup G) ⧸
        (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup)
      (openSubgroupInvariants A S.toOpenSubgroup) := by
  let K := relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup
  letI : Representation.IsTrivial
      ((topInvariantRepresentation (A := A) S).comp K.toSubgroup.subtype) :=
    { out := fun k ↦ by
        ext x
        change A.ρ (((k : K.toSubgroup) : (⊤ : OpenSubgroup G)) : G) x = x
        exact x.2 ⟨(((k : K.toSubgroup) : (⊤ : OpenSubgroup G)) : G), k.2⟩ }
  exact (topInvariantRepresentation (A := A) S).ofQuotient K.toSubgroup

variable [IsTopologicalGroup G] [CompactSpace G]

private noncomputable def topQuotientNorm (S : OpenNormalSubgroup G) :
    openSubgroupInvariants A S.toOpenSubgroup →ₗ[R]
      openSubgroupInvariants A S.toOpenSubgroup := by
  letI : Fintype ((⊤ : OpenSubgroup G) ⧸
      (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup) :=
    Fintype.ofFinite _
  exact Representation.norm (topQuotientInvariantRepresentation (A := A) S)

private lemma relativeNormWithTransversal_eq_topQuotientNorm
    (S : OpenNormalSubgroup G)
    (T : (relativeNormSubgroup (⊤ : OpenSubgroup G)
      S.toOpenSubgroup).toSubgroup.RightTransversal)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    (relativeNormWithTransversal A (⊤ : OpenSubgroup G) S.toOpenSubgroup
        le_top T x : A) =
      topQuotientNorm A S x := by
  let U : OpenSubgroup G := ⊤
  let K : OpenSubgroup U := relativeNormSubgroup U S.toOpenSubgroup
  let _ : K.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(T : Set U) := T.2.finite_right.fintype
  let _ : Fintype (U ⧸ K.toSubgroup) := Fintype.ofFinite _
  let e : ↥(T : Set U) ≃ U ⧸ K.toSubgroup :=
    rightTransversalQuotientEquiv K.toSubgroup T
  simp only [relativeNormWithTransversal_coe, topQuotientNorm,
    Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
  change (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) =
    ∑ q : U ⧸ K.toSubgroup,
      ((topQuotientInvariantRepresentation (A := A) S q x :
        openSubgroupInvariants A S.toOpenSubgroup) : A)
  have happ (t : ↥(T : Set U)) :
      ((topQuotientInvariantRepresentation (A := A) S (e t) x :
        openSubgroupInvariants A S.toOpenSubgroup) : A) =
        A.ρ (((t : U) : G)⁻¹) x := by
    rw [show e t = QuotientGroup.mk' K.toSubgroup (t : U)⁻¹ by rfl]
    rfl
  calc
    (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) =
        ∑ t : ↥(T : Set U),
          ((topQuotientInvariantRepresentation (A := A) S (e t) x :
            openSubgroupInvariants A S.toOpenSubgroup) : A) := by
      apply Finset.sum_congr rfl
      intro t _
      exact (happ t).symm
    _ = ∑ q : U ⧸ K.toSubgroup,
          ((topQuotientInvariantRepresentation (A := A) S q x :
            openSubgroupInvariants A S.toOpenSubgroup) : A) :=
      e.sum_comp (fun q : U ⧸ K.toSubgroup ↦
        ((topQuotientInvariantRepresentation (A := A) S q x :
          openSubgroupInvariants A S.toOpenSubgroup) : A))

private lemma relativeNorm_eq_topQuotientNorm
    (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x : A) =
      topQuotientNorm A S x := by
  rw [relativeNorm_eq_withTransversal A (⊤ : OpenSubgroup G)
    S.toOpenSubgroup le_top default]
  exact relativeNormWithTransversal_eq_topQuotientNorm A S default x

/-- The relative norm from `A^S` to `A^G` is the ordinary finite-group norm
for the residual `G / S`-action, after forgetting the redundant outer
invariance proof in its target. -/
lemma relativeNorm_eq_quotientToInvariants_norm
    (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)]
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x : A) =
      (Representation.norm (A.quotientToInvariants S.toSubgroup).ρ x :
        A.quotientToInvariants S.toSubgroup) := by
  let U : OpenSubgroup G := ⊤
  let K : OpenSubgroup U := relativeNormSubgroup U S.toOpenSubgroup
  let e : U ≃* G :=
    { toFun := fun g ↦ g
      invFun := fun g ↦ ⟨g, trivial⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  have he : K.toSubgroup.map (e : U →* G) = S.toSubgroup := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hg
      exact ⟨⟨g, trivial⟩, hg, rfl⟩
  let qEquiv : U ⧸ K.toSubgroup ≃ G ⧸ S.toSubgroup :=
    (QuotientGroup.congr K.toSubgroup S.toSubgroup e he).toEquiv
  let _ : Fintype (U ⧸ K.toSubgroup) := Fintype.ofFinite _
  rw [relativeNorm_eq_topQuotientNorm A S x]
  simp only [topQuotientNorm, Representation.norm, LinearMap.sum_apply]
  simp only [Submodule.coe_sum]
  change (∑ q : U ⧸ K.toSubgroup,
      ((topQuotientInvariantRepresentation (A := A) S q x :
        openSubgroupInvariants A S.toOpenSubgroup) : A)) =
    ∑ q : G ⧸ S.toSubgroup,
      (((A.quotientToInvariants S.toSubgroup).ρ q x :
        A.quotientToInvariants S.toSubgroup) : A)
  calc
    _ = ∑ q : U ⧸ K.toSubgroup,
        (((A.quotientToInvariants S.toSubgroup).ρ (qEquiv q) x :
          A.quotientToInvariants S.toSubgroup) : A) := by
      apply Finset.sum_congr rfl
      intro q _
      refine QuotientGroup.induction_on q ?_
      intro g
      rfl
    _ = _ := qEquiv.sum_comp fun q : G ⧸ S.toSubgroup ↦
      (((A.quotientToInvariants S.toSubgroup).ρ q x :
        A.quotientToInvariants S.toSubgroup) : A)

private lemma topQuotientNorm_self_apply (S : OpenNormalSubgroup G)
    (q : (⊤ : OpenSubgroup G) ⧸
      (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    topQuotientNorm A S
        (topQuotientInvariantRepresentation (A := A) S q x) =
      topQuotientNorm A S x := by
  let _ : Fintype ((⊤ : OpenSubgroup G) ⧸
      (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup) :=
    Fintype.ofFinite _
  exact Representation.norm_self_apply
    (topQuotientInvariantRepresentation (A := A) S) q x

omit [IsTopologicalGroup G] [CompactSpace G] in
private lemma topQuotientInvariantRepresentation_mk_apply
    (S : OpenNormalSubgroup G) (g : G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    topQuotientInvariantRepresentation (A := A) S
        (QuotientGroup.mk'
          (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup
          (⟨g, trivial⟩ : (⊤ : OpenSubgroup G))) x =
      (A.quotientToInvariants S.toSubgroup).ρ
        (QuotientGroup.mk' S.toSubgroup g) x := by
  apply Subtype.ext
  rfl

/-- The accepted continuous relative norm from `A^S` to `A^G` is invariant
under the residual finite quotient action on its source. -/
lemma relativeNorm_quotientToInvariants_action (S : OpenNormalSubgroup G)
    (q : G ⧸ S.toSubgroup) (x : openSubgroupInvariants A S.toOpenSubgroup) :
    relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top
        ((A.quotientToInvariants S.toSubgroup).ρ q x) =
      relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x := by
  refine QuotientGroup.induction_on q ?_
  intro g
  apply Subtype.ext
  let q' := QuotientGroup.mk'
    (relativeNormSubgroup (⊤ : OpenSubgroup G) S.toOpenSubgroup).toSubgroup
    (⟨g, trivial⟩ : (⊤ : OpenSubgroup G))
  calc
    (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top
        ((A.quotientToInvariants S.toSubgroup).ρ
          (QuotientGroup.mk' S.toSubgroup g) x) : A) =
      topQuotientNorm A S
        ((A.quotientToInvariants S.toSubgroup).ρ
          (QuotientGroup.mk' S.toSubgroup g) x) :=
      relativeNorm_eq_topQuotientNorm A S _
    _ = topQuotientNorm A S
        (topQuotientInvariantRepresentation (A := A) S q' x) := by
      rw [topQuotientInvariantRepresentation_mk_apply A S g x]
    _ = topQuotientNorm A S x :=
      congrArg Subtype.val (topQuotientNorm_self_apply A S q' x)
    _ = (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x : A) :=
      (relativeNorm_eq_topQuotientNorm A S x).symm

/-- The algebraic coinvariants `(A^S)_{G/S}` with the compact Hausdorff
quotient topology supplied by the level-compact structure. -/
@[expose] def finiteCoinvariants (S : OpenNormalSubgroup G) : CompHausAddCommGrp.{uA} := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  exact ContinuousGroupCohomology.finiteCoinvariants
    (A.quotientToInvariants S.toSubgroup).ρ
    (continuous_quotientToInvariants_action A (L := L) S)

/-- The canonical continuous map `A^S → (A^S)_{G/S}`. -/
@[expose] def finiteCoinvariantsMk (S : OpenNormalSubgroup G) :
    group A L S.toOpenSubgroup ⟶ finiteCoinvariants A (L := L) S := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  exact ContinuousGroupCohomology.finiteCoinvariantsMk
    (A.quotientToInvariants S.toSubgroup).ρ
    (continuous_quotientToInvariants_action A (L := L) S)

@[simp]
lemma finiteCoinvariantsMk_apply (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    finiteCoinvariantsMk A (L := L) S x =
      Representation.Coinvariants.mk
        (A.quotientToInvariants S.toSubgroup).ρ x :=
  rfl

/-- The accepted continuous relative norm `A^S → A^G`, descended to the
compact Hausdorff coinvariants `(A^S)_{G/S}`. -/
@[expose] def normFromFiniteCoinvariants (S : OpenNormalSubgroup G) :
    finiteCoinvariants A (L := L) S ⟶ group A L (⊤ : OpenSubgroup G) := by
  let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  letI : TopologicalSpace (openSubgroupInvariants A (⊤ : OpenSubgroup G)) :=
    L.topology ⊤
  letI : CompactSpace (openSubgroupInvariants A (⊤ : OpenSubgroup G)) :=
    L.compact ⊤
  letI : T2Space (openSubgroupInvariants A (⊤ : OpenSubgroup G)) :=
    L.t2 ⊤
  letI : IsTopologicalAddGroup
      (openSubgroupInvariants A (⊤ : OpenSubgroup G)) :=
    L.topologicalAddGroup ⊤
  apply ContinuousGroupCohomology.finiteCoinvariantsDesc
    (A.quotientToInvariants S.toSubgroup).ρ
    (continuous_quotientToInvariants_action A (L := L) S)
    (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top)
    (continuous_relativeNorm A L (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top)
  intro q
  apply LinearMap.ext
  intro x
  exact relativeNorm_quotientToInvariants_action A S q x

@[simp]
lemma normFromFiniteCoinvariants_mk (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    normFromFiniteCoinvariants A L S
        (Representation.Coinvariants.mk
          (A.quotientToInvariants S.toSubgroup).ρ x) =
      relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x :=
  rfl

end LevelCompact

end ContinuousGroupCohomology
