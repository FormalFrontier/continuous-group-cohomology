/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Composition
public import ContinuousGroupCohomology.LevelCompact
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Relative norms on level-compact invariants

For open subgroups `V ≤ U` of a compact topological group, this file defines
the finite relative norm from `V`-invariants to `U`-invariants. It proves
choice-independence, composition through towers, equivariance for the residual
actions at normal levels, and continuity for a `LevelCompact` system.

The continuity proof does not assume a topology on the ambient coefficient
module.  It passes to the open normal core of `V` inside `U`, where every
transversal summand is one of the continuous transports supplied by
`LevelCompact`, and reflects continuity through the closed embedding back into
the `U`-invariants.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace LevelCompact

/-- The pullback of `V` to the open subgroup `U`.  When `V ≤ U`, this is the
copy of `V` used to choose relative norm representatives inside `U`. -/
@[expose] def relativeNormSubgroup (U V : OpenSubgroup G) : OpenSubgroup U :=
  V.comap U.subtype continuous_subtype_val

local instance relativeNormSubgroup_finiteIndex (U V : OpenSubgroup G) :
    (relativeNormSubgroup U V).toSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

local instance relativeNormTransversalFintype (U V : OpenSubgroup G)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    Fintype ↥(T : Set U) :=
  T.2.finite_right.fintype

open ContinuousCohomology.CorestrictionTransversal

/-- The relative norm computed using a right transversal inside `U`.

The inverse in the summand matches the right-transversal convention. -/
@[expose] def relativeNormWithTransversal (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (_h : V ≤ U)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    openSubgroupInvariants A V →ₗ[R] openSubgroupInvariants A U where
  toFun x := ⟨∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x, fun g ↦ by
    change A.ρ (g : G) (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) = _
    rw [map_sum]
    calc
      (∑ t : ↥(T : Set U), A.ρ (g : G) (A.ρ (((t : U) : G)⁻¹) x)) =
          ∑ t : ↥(T : Set U),
            A.ρ (g : G) (A.ρ (((next T t g : U) : G)⁻¹) x) := by
        simpa [nextEquiv] using
          (Equiv.sum_comp (nextEquiv T g)
            (fun t : ↥(T : Set U) ↦
              A.ρ (g : G) (A.ρ (((t : U) : G)⁻¹) x))).symm
      _ = ∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x := by
        apply Finset.sum_congr rfl
        intro t _
        have hfactor :
            A.ρ (((factor T t g : relativeNormSubgroup U V) : U) : G) x = x :=
          x.2 ⟨((factor T t g : relativeNormSubgroup U V) : U),
            (factor T t g).2⟩
        calc
          A.ρ (g : G) (A.ρ (((next T t g : U) : G)⁻¹) x) =
              A.ρ ((g : G) * ((next T t g : U) : G)⁻¹) x := by
            rw [← Module.End.mul_apply, ← map_mul]
          _ = A.ρ (((t : U) : G)⁻¹ *
                ((factor T t g : relativeNormSubgroup U V) : U)) x := by
            congr 2
            exact congrArg (fun z : U ↦ (z : G)) (inv_mul_factor T t g).symm
          _ = A.ρ (((t : U) : G)⁻¹)
                (A.ρ (((factor T t g : relativeNormSubgroup U V) : U) : G) x) := by
            rw [← Module.End.mul_apply, ← map_mul]
          _ = A.ρ (((t : U) : G)⁻¹) x := by rw [hfactor]
    ⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [map_add, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' r x := by
    apply Subtype.ext
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply,
      Submodule.coe_smul_of_tower]

@[simp]
lemma relativeNormWithTransversal_coe (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (h : V ≤ U)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal)
    (x : openSubgroupInvariants A V) :
    (relativeNormWithTransversal A U V h T x : A) =
      ∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x :=
  rfl

/-- The relative norm is independent of the chosen right transversal. -/
lemma relativeNormWithTransversal_eq (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (h : V ≤ U)
    (T S : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    relativeNormWithTransversal A U V h T =
      relativeNormWithTransversal A U V h S := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) =
    ∑ s : ↥(S : Set U), A.ρ (((s : U) : G)⁻¹) x
  calc
    (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) =
        ∑ t : ↥(T : Set U), A.ρ (((changeRep T S t : U) : G)⁻¹) x := by
      apply Finset.sum_congr rfl
      intro t _
      have hfix :
          A.ρ ((((changeFactor T S t)⁻¹ : relativeNormSubgroup U V) : U) : G) x = x :=
        x.2 ⟨(((changeFactor T S t)⁻¹ : relativeNormSubgroup U V) : U),
          (relativeNormSubgroup U V).inv_mem (changeFactor T S t).2⟩
      calc
        A.ρ (((t : U) : G)⁻¹) x =
            A.ρ (((changeRep T S t : U) : G)⁻¹ *
              ((((changeFactor T S t)⁻¹ : relativeNormSubgroup U V) : U) : G)) x := by
          rw [← changeFactor_mul_changeRep T S t]
          simp
        _ = A.ρ (((changeRep T S t : U) : G)⁻¹)
              (A.ρ ((((changeFactor T S t)⁻¹ : relativeNormSubgroup U V) : U) : G) x) := by
          rw [← Module.End.mul_apply, ← map_mul]
        _ = A.ρ (((changeRep T S t : U) : G)⁻¹) x := by rw [hfix]
    _ = ∑ s : ↥(S : Set U), A.ρ (((s : U) : G)⁻¹) x := by
      simpa [changeRepEquiv] using
        Equiv.sum_comp (changeRepEquiv T S)
          (fun s : ↥(S : Set U) ↦ A.ρ (((s : U) : G)⁻¹) x)

/-- The canonical relative norm from `V`-invariants to `U`-invariants. -/
def relativeNorm (A : Rep.{uA} R G) (U V : OpenSubgroup G) (h : V ≤ U) :
    openSubgroupInvariants A V →ₗ[R] openSubgroupInvariants A U :=
  relativeNormWithTransversal A U V h default

/-- The canonical relative norm can be computed with any right transversal. -/
lemma relativeNorm_eq_withTransversal (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (h : V ≤ U)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    relativeNorm A U V h = relativeNormWithTransversal A U V h T :=
  relativeNormWithTransversal_eq A U V h default T

private noncomputable def rightTransversalComapMulEquiv
    {K L : Type*} [Group K] [Group L] (e : K ≃* L) (H : Subgroup L)
    (T : H.RightTransversal) :
    (H.comap e.toMonoidHom).RightTransversal := by
  refine ⟨e.symm '' (T : Set L), ?_⟩
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro y
  obtain ⟨t, ht, ht_unique⟩ :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp T.2) (e y)
  refine ⟨⟨e.symm t, ⟨t, t.2, rfl⟩⟩, ?_, ?_⟩
  · change e (y * (e.symm t : K)⁻¹) ∈ H
    simpa using ht
  · rintro ⟨s', ⟨s, hs, rfl⟩⟩ hs_mem
    apply Subtype.ext
    exact congrArg e.symm (congrArg Subtype.val (ht_unique ⟨s, hs⟩ (by
      change e (y * (e.symm s : K)⁻¹) ∈ H at hs_mem
      simpa using hs_mem)))

private def relativeNormSubgroupEquiv (U V : OpenSubgroup G) (h : V ≤ U) :
    relativeNormSubgroup U V ≃ₜ* V := by
  let e : relativeNormSubgroup U V ≃* V := {
    toFun x := ⟨(x : G), x.2⟩
    invFun x := ⟨⟨(x : G), h x.2⟩, x.2⟩
    left_inv x := rfl
    right_inv x := rfl
    map_mul' x y := rfl }
  exact ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfContinuousOpen
      (by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val)
      (by
        apply IsOpenMap.subtype_mk
        exact U.isOpen.isOpenMap_subtype_val.comp
          (relativeNormSubgroup U V).isOpen.isOpenMap_subtype_val))
    e.map_mul

private def relativeNormTowerSubgroup (U V W : OpenSubgroup G)
    (hVU : V ≤ U) : OpenSubgroup (relativeNormSubgroup U V) :=
  (relativeNormSubgroup V W).comap
    (relativeNormSubgroupEquiv U V hVU).toMonoidHom
    (relativeNormSubgroupEquiv U V hVU).continuous

private noncomputable def relativeNormTowerTransversal
    (U V W : OpenSubgroup G) (hVU : V ≤ U)
    (S : (relativeNormSubgroup V W).toSubgroup.RightTransversal) :
    (relativeNormTowerSubgroup U V W hVU).toSubgroup.RightTransversal :=
  rightTransversalComapMulEquiv
    (relativeNormSubgroupEquiv U V hVU).toMulEquiv
    (relativeNormSubgroup V W).toSubgroup S

omit [IsTopologicalGroup G] [CompactSpace G] in
private lemma relativeNormTower_trans_eq (U V W : OpenSubgroup G)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    OpenSubgroup.trans (relativeNormSubgroup U V)
      (relativeNormTowerSubgroup U V W hVU) = relativeNormSubgroup U W := by
  ext x
  change x ∈ (relativeNormTowerSubgroup U V W hVU).toSubgroup.map
      (relativeNormSubgroup U V).subtype ↔ (x : G) ∈ W
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (y : G) ∈ W at hy
    exact hy
  · intro hx
    let y : relativeNormSubgroup U V := ⟨x, hWV hx⟩
    refine ⟨y, ?_, rfl⟩
    change (x : G) ∈ W
    exact hx

private noncomputable def relativeNormTransRightTransversal
    (U V W : OpenSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U)
    (S : (relativeNormSubgroup V W).toSubgroup.RightTransversal)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    (relativeNormSubgroup U W).toSubgroup.RightTransversal := by
  let P := transRightTransversal (relativeNormSubgroup U V)
    (relativeNormTowerSubgroup U V W hVU)
    (relativeNormTowerTransversal U V W hVU S) T
  refine ⟨(P : Set U), ?_⟩
  rw [← relativeNormTower_trans_eq U V W hWV hVU]
  exact P.2

private lemma relativeNormWithTransversal_comp
    (A : Rep.{uA} R G) (U V W : OpenSubgroup G)
    (hWV : W ≤ V) (hVU : V ≤ U)
    (S : (relativeNormSubgroup V W).toSubgroup.RightTransversal)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    (relativeNormWithTransversal A U V hVU T).comp
        (relativeNormWithTransversal A V W hWV S) =
      relativeNormWithTransversal A U W (hWV.trans hVU)
        (relativeNormTransRightTransversal U V W hWV hVU S T) := by
  let H := relativeNormSubgroup U V
  let K := relativeNormTowerSubgroup U V W hVU
  let S' := relativeNormTowerTransversal U V W hVU S
  let P := relativeNormTransRightTransversal U V W hWV hVU S T
  let e := relativeNormSubgroupEquiv U V hVU
  let ES : ↥(S : Set V) ≃ ↥(S' : Set H) := by
    change ↥(S : Set V) ≃ ↥(e.symm '' (S : Set V))
    exact e.toMulEquiv.symm.image (S : Set V)
  let E : (↥(S : Set V) × ↥(T : Set U)) ≃ ↥(P : Set U) := by
    change (↥(S : Set V) × ↥(T : Set U)) ≃
      ↥(transRightTransversal H K S' T : Set U)
    exact (Equiv.prodCongr ES (Equiv.refl _)).trans
      (transRightRepEquiv H K S' T)
  have hE (p : ↥(S : Set V) × ↥(T : Set U)) :
      ((E p : U) : G) = ((p.1 : V) : G) * ((p.2 : U) : G) := by
    change (((transRightRepEquiv H K S' T (ES p.1, p.2) : U) : G)) = _
    rw [transRightRepEquiv_apply_coe]
    change (((ES p.1 : H) : U) : G) * ((p.2 : U) : G) = _
    congr 1
  let _ : (relativeNormSubgroup V W).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : (relativeNormSubgroup U V).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : (relativeNormSubgroup U W).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(S : Set V) := S.2.finite_right.fintype
  let _ : Fintype ↥(T : Set U) := T.2.finite_right.fintype
  let _ : Fintype ↥(P : Set U) := P.2.finite_right.fintype
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹)
      (∑ s : ↥(S : Set V), A.ρ (((s : V) : G)⁻¹) x)) =
    ∑ p : ↥(P : Set U), A.ρ (((p : U) : G)⁻¹) x
  simp_rw [map_sum]
  have hright := E.sum_comp
    (fun p : ↥(P : Set U) ↦ A.ρ (((p : U) : G)⁻¹) x)
  rw [← hright]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [hE]
  rw [mul_inv_rev, map_mul]
  rfl

/-- Relative norms compose through a tower of open subgroups. -/
theorem relativeNorm_comp
    (A : Rep.{uA} R G) (U V W : OpenSubgroup G)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    (relativeNorm A U V hVU).comp (relativeNorm A V W hWV) =
      relativeNorm A U W (hWV.trans hVU) := by
  let S : (relativeNormSubgroup V W).toSubgroup.RightTransversal := default
  let T : (relativeNormSubgroup U V).toSubgroup.RightTransversal := default
  let P := relativeNormTransRightTransversal U V W hWV hVU S T
  rw [relativeNorm_eq_withTransversal A U V hVU T,
    relativeNorm_eq_withTransversal A V W hWV S,
    relativeNorm_eq_withTransversal A U W (hWV.trans hVU) P]
  exact relativeNormWithTransversal_comp A U V W hWV hVU S T

/-- The relative norm from an open subgroup to itself is the identity. -/
@[simp]
theorem relativeNorm_refl (A : Rep.{uA} R G) (U : OpenSubgroup G) :
    relativeNorm A U U le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let T : (relativeNormSubgroup U U).toSubgroup.RightTransversal := default
  rw [relativeNorm_eq_withTransversal A U U le_rfl T]
  rw [relativeNormWithTransversal_coe]
  have hterm (t : ↥(T : Set U)) :
      A.ρ (((t : U) : G)⁻¹) x = x := by
    exact x.2 ⟨((t : U)⁻¹), U.inv_mem (t : U).2⟩
  simp_rw [hterm]
  have htop : (relativeNormSubgroup U U).toSubgroup = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro y _
      exact y.2
  let _ : (relativeNormSubgroup U U).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(T : Set U) := T.2.finite_right.fintype
  let _ : Fintype (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    Fintype.ofEquiv _ T.2.rightQuotientEquiv.symm
  let _ : Subsingleton (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | _ a =>
        induction b using Quotient.inductionOn with
        | _ b =>
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [htop]
          trivial⟩
  let _ : Unique (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    { default := Quotient.mk'' (1 : U)
      uniq := fun _ => Subsingleton.elim _ _ }
  have hcard : Fintype.card ↥(T : Set U) = 1 := by
    rw [← Fintype.card_congr T.2.rightQuotientEquiv]
    exact Fintype.card_unique
  rw [Finset.sum_const, Finset.card_univ, hcard, one_nsmul]
  rfl

private def conjugationMulEquiv (U : OpenNormalSubgroup G) (g : G) : U ≃* U where
  toFun u := ⟨g * (u : G) * g⁻¹, by
    exact Subgroup.Normal.conj_mem (H := U.toSubgroup) (self := inferInstance)
      (u : G) u.2 g⟩
  invFun u := ⟨g⁻¹ * (u : G) * g, by
    show g⁻¹ * (u : G) * g ∈ U.toSubgroup
    simpa only [inv_inv] using
      (Subgroup.Normal.conj_mem (H := U.toSubgroup) (self := inferInstance)
        (u : G) u.2 g⁻¹)⟩
  left_inv u := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv u := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

omit [IsTopologicalGroup G] [CompactSpace G] in
private lemma conjugationMulEquiv_mem_relativeNormSubgroup_iff
    (U V : OpenNormalSubgroup G) (g : G) (x : U) :
    conjugationMulEquiv U g x ∈
        (relativeNormSubgroup U.toOpenSubgroup V.toOpenSubgroup).toSubgroup ↔
      x ∈ (relativeNormSubgroup U.toOpenSubgroup V.toOpenSubgroup).toSubgroup := by
  change g * (x : G) * g⁻¹ ∈ V.toSubgroup ↔ (x : G) ∈ V.toSubgroup
  constructor
  · intro hx
    have := Subgroup.Normal.conj_mem (H := V.toSubgroup) (self := inferInstance)
      (g * (x : G) * g⁻¹) hx g⁻¹
    simpa [mul_assoc] using this
  · intro hx
    exact Subgroup.Normal.conj_mem (H := V.toSubgroup) (self := inferInstance)
      (x : G) hx g

private noncomputable def conjugateRightTransversal
    (U V : OpenNormalSubgroup G) (g : G)
    (T : (relativeNormSubgroup U.toOpenSubgroup
      V.toOpenSubgroup).toSubgroup.RightTransversal) :
    (relativeNormSubgroup U.toOpenSubgroup
      V.toOpenSubgroup).toSubgroup.RightTransversal := by
  let K := (relativeNormSubgroup U.toOpenSubgroup V.toOpenSubgroup).toSubgroup
  let e := conjugationMulEquiv U g
  refine ⟨e '' (T : Set U), ?_⟩
  rw [Subgroup.isComplement_iff_existsUnique_mul_inv_mem]
  intro y
  obtain ⟨t, ht, ht_unique⟩ :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp T.2) (e.symm y)
  refine ⟨⟨e t, ⟨t, t.2, rfl⟩⟩, ?_, ?_⟩
  · have hmem :=
      (conjugationMulEquiv_mem_relativeNormSubgroup_iff U V g
        (e.symm y * (t : U)⁻¹)).mpr ht
    simpa [e] using hmem
  · rintro ⟨s', ⟨s, hs, rfl⟩⟩ hs_mem
    apply Subtype.ext
    exact congrArg e (congrArg Subtype.val (ht_unique ⟨s, hs⟩ (by
      have hpre : e.symm (y * (e s)⁻¹) ∈ K :=
        (conjugationMulEquiv_mem_relativeNormSubgroup_iff U V g
          (e.symm (y * (e s)⁻¹))).mp (by simpa [e] using hs_mem)
      simpa [K, e] using hpre)))

private lemma relativeNormWithTransversal_quotientToInvariants_action_mk
    (A : Rep.{uA} R G) (U V : OpenNormalSubgroup G) (h : V ≤ U)
    (g : G)
    (T : (relativeNormSubgroup U.toOpenSubgroup
      V.toOpenSubgroup).toSubgroup.RightTransversal)
    (x : openSubgroupInvariants A V.toOpenSubgroup) :
    (A.quotientToInvariants U.toSubgroup).ρ
        (QuotientGroup.mk' U.toSubgroup g)
        (relativeNormWithTransversal A U.toOpenSubgroup V.toOpenSubgroup h T x) =
      relativeNormWithTransversal A U.toOpenSubgroup V.toOpenSubgroup h
        (conjugateRightTransversal U V g T)
        ((A.quotientToInvariants V.toSubgroup).ρ
          (QuotientGroup.mk' V.toSubgroup g) x) := by
  let e := conjugationMulEquiv U g
  let S := conjugateRightTransversal U V g T
  let K := (relativeNormSubgroup U.toOpenSubgroup V.toOpenSubgroup).toSubgroup
  let _ : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(T : Set U) := T.2.finite_right.fintype
  let _ : Fintype ↥(S : Set U) := S.2.finite_right.fintype
  let E : ↥(T : Set U) ≃ ↥(S : Set U) := by
    change ↥(T : Set U) ≃ ↥(e '' (T : Set U))
    exact e.image (T : Set U)
  apply Subtype.ext
  change A.ρ g (∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x) =
    ∑ s : ↥(S : Set U), A.ρ (((s : U) : G)⁻¹) (A.ρ g x)
  rw [map_sum]
  calc
    (∑ t : ↥(T : Set U), A.ρ g (A.ρ (((t : U) : G)⁻¹) x)) =
        ∑ t : ↥(T : Set U),
          A.ρ (((E t : U) : G)⁻¹) (A.ρ g x) := by
      apply Finset.sum_congr rfl
      intro t _
      have hE : (E t : U) = e t := rfl
      rw [hE]
      simp only [e, conjugationMulEquiv]
      rw [← Module.End.mul_apply, ← map_mul,
        ← Module.End.mul_apply, ← map_mul]
      congr 2
      simp [mul_assoc]
    _ = ∑ s : ↥(S : Set U),
          A.ρ (((s : U) : G)⁻¹) (A.ρ g x) :=
      E.sum_comp (fun s : ↥(S : Set U) ↦
        A.ρ (((s : U) : G)⁻¹) (A.ρ g x))

/-- Relative norms between open normal levels commute with the residual quotient
actions, evaluated on representatives in the ambient group. -/
lemma relativeNorm_quotientToInvariants_action_mk
    (A : Rep.{uA} R G) (U V : OpenNormalSubgroup G) (h : V ≤ U)
    (g : G) (x : openSubgroupInvariants A V.toOpenSubgroup) :
    (A.quotientToInvariants U.toSubgroup).ρ
        (QuotientGroup.mk' U.toSubgroup g)
        (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x) =
      relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h
        ((A.quotientToInvariants V.toSubgroup).ρ
          (QuotientGroup.mk' V.toSubgroup g) x) := by
  let T : (relativeNormSubgroup U.toOpenSubgroup
    V.toOpenSubgroup).toSubgroup.RightTransversal := default
  let S := conjugateRightTransversal U V g T
  calc
    _ = relativeNormWithTransversal A U.toOpenSubgroup V.toOpenSubgroup h S
        ((A.quotientToInvariants V.toSubgroup).ρ
          (QuotientGroup.mk' V.toSubgroup g) x) := by
      simpa [relativeNorm, T, S] using
        relativeNormWithTransversal_quotientToInvariants_action_mk A U V h g T x
    _ = _ := congrArg (fun f => f
        ((A.quotientToInvariants V.toSubgroup).ρ
          (QuotientGroup.mk' V.toSubgroup g) x))
      (relativeNorm_eq_withTransversal A U.toOpenSubgroup
        V.toOpenSubgroup h S).symm

/-- The range of a relative norm between open normal levels is stable under
the residual action on its target. -/
theorem relativeNorm_range_quotientToInvariants_stable
    (A : Rep.{uA} R G) (U V : OpenNormalSubgroup G) (h : V ≤ U)
    (q : G ⧸ U.toSubgroup)
    {y : openSubgroupInvariants A U.toOpenSubgroup}
    (hy : y ∈ LinearMap.range
      (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h)) :
    (A.quotientToInvariants U.toSubgroup).ρ q y ∈ LinearMap.range
      (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) := by
  obtain ⟨x, rfl⟩ := hy
  refine QuotientGroup.induction_on q ?_
  intro g
  refine ⟨(A.quotientToInvariants V.toSubgroup).ρ
    (QuotientGroup.mk' V.toSubgroup g) x, ?_⟩
  exact (relativeNorm_quotientToInvariants_action_mk A U V h g x).symm

private def relativeNormNormalCore (U V : OpenSubgroup G) : OpenSubgroup U := by
  let K := relativeNormSubgroup U V
  exact
    { toSubgroup := K.toSubgroup.normalCore
      isOpen' := K.toSubgroup.normalCore.isOpen_of_isClosed_of_finiteIndex
        (K.toSubgroup.normalCore_isClosed K.isClosed) }

private def relativeNormCommonLevel (U V : OpenSubgroup G) : OpenSubgroup G :=
  OpenSubgroup.trans U (relativeNormNormalCore U V)

private lemma relativeNormCommonLevel_le_left (U V : OpenSubgroup G) :
    relativeNormCommonLevel U V ≤ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

private lemma relativeNormCommonLevel_le_right (U V : OpenSubgroup G) :
    relativeNormCommonLevel U V ≤ V := by
  rintro _ ⟨x, hx, rfl⟩
  exact (relativeNormSubgroup U V).toSubgroup.normalCore_le hx

private lemma relativeNormCommonLevel_le_conj (U V : OpenSubgroup G) (s : U) :
    (relativeNormCommonLevel U V).toSubgroup ≤
      V.toSubgroup.map (MulAut.conj (s : G)) := by
  rintro _ ⟨w, hw, rfl⟩
  let K := relativeNormSubgroup U V
  have hwcore : w ∈ K.toSubgroup.normalCore := hw
  let v : U := s⁻¹ * w * s
  have hvK : v ∈ K.toSubgroup := by
    simpa only [v, inv_inv] using hwcore (s : U)⁻¹
  exact ⟨(v : G), hvK, by simp [v, MulAut.conj_apply, mul_assoc]⟩

/-- A relative norm computed with any right transversal is continuous for the
levelwise compact topologies. -/
lemma continuous_relativeNormWithTransversal (A : Rep.{uA} R G) (L : LevelCompact A)
    (U V : OpenSubgroup G) (h : V ≤ U)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    @Continuous (openSubgroupInvariants A V) (openSubgroupInvariants A U)
      (L.topology V) (L.topology U) (relativeNormWithTransversal A U V h T) := by
  let W := relativeNormCommonLevel U V
  let hWU : W ≤ U := relativeNormCommonLevel_le_left U V
  let _ : TopologicalSpace (openSubgroupInvariants A V) := L.topology V
  let _ : TopologicalSpace (openSubgroupInvariants A W) := L.topology W
  let _ : TopologicalSpace (openSubgroupInvariants A U) := L.topology U
  let _ : IsTopologicalAddGroup (openSubgroupInvariants A W) := L.topologicalAddGroup W
  let f : openSubgroupInvariants A V → openSubgroupInvariants A W := fun x ↦
    ∑ t : ↥(T : Set U),
      openSubgroupInvariantsTransport A V W (((t : U) : G)⁻¹)
        (relativeNormCommonLevel_le_conj U V (t : U)⁻¹) x
  have hf : Continuous f := by
    exact continuous_finsetSum Finset.univ fun t _ ↦
      L.continuous_transport V W (((t : U) : G)⁻¹)
        (relativeNormCommonLevel_le_conj U V (t : U)⁻¹)
  have hcomp :
      (inclusion A U W hWU : openSubgroupInvariants A U → openSubgroupInvariants A W) ∘
          relativeNormWithTransversal A U V h T = f := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, inclusion_coe, relativeNormWithTransversal_coe,
      f, Submodule.coe_sum, openSubgroupInvariantsTransport_coe]
  apply (inclusion_isClosedEmbedding A L U W hWU).isInducing.continuous_iff.mpr
  rw [hcomp]
  exact hf

/-- The canonical relative norm is continuous for a `LevelCompact` system. -/
lemma continuous_relativeNorm (A : Rep.{uA} R G) (L : LevelCompact A)
    (U V : OpenSubgroup G) (h : V ≤ U) :
    @Continuous (openSubgroupInvariants A V) (openSubgroupInvariants A U)
      (L.topology V) (L.topology U) (relativeNorm A U V h) :=
  continuous_relativeNormWithTransversal A L U V h default

end LevelCompact

end ContinuousGroupCohomology
