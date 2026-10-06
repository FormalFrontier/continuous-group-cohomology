/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Corestriction

/-!
# Composition of degree-one corestriction

This file proves transitivity of canonical degree-one corestriction through
nested open finite-index subgroups.  It flattens an open subgroup of an open
subgroup, identifies the nested and flattened topological groups, constructs
the product of two compatible right transversals, and proves directly that the
iterated finite-sum transfer equals transfer for the product transversal.

The crossed-homomorphism calculation is descended through principal cocycles
and compared with mathlib's native continuous-cohomology map along the
flattening equivalence.  Thus the final statement is independent of all
transversal choices and uses the public cohomology functoriality API.
-/

set_option autoImplicit false
set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace OpenSubgroup

/-- Flatten an open subgroup of an open subgroup into the ambient group.
Its underlying subgroup computes as the image of the nested subgroup. -/
@[expose]
def trans (H : OpenSubgroup G) (K : OpenSubgroup H) : OpenSubgroup G where
  toSubgroup := K.toSubgroup.map H.subtype
  isOpen' := by
    change IsOpen (H.subtype '' (K : Set H))
    exact H.isOpen.isOpenMap_subtype_val (K : Set H) K.isOpen

omit [IsTopologicalGroup G] in
@[simp]
lemma trans_toSubgroup (H : OpenSubgroup G) (K : OpenSubgroup H) :
    (trans H K).toSubgroup = K.toSubgroup.map H.subtype := rfl

/-- The flattened subgroup has the same topological group as the nested subgroup.
The equivalence computes on subgroup elements. -/
@[expose]
noncomputable def transEquiv (H : OpenSubgroup G) (K : OpenSubgroup H) :
    K ≃ₜ* trans H K :=
  let e := K.toSubgroup.equivMapOfInjective H.subtype H.subtype_injective
  ContinuousMulEquiv.mk'
    (e.toEquiv.toHomeomorphOfContinuousOpen
      (by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val)
      (by
        apply IsOpenMap.subtype_mk
        exact H.isOpen.isOpenMap_subtype_val.comp
          K.isOpen.isOpenMap_subtype_val))
    e.map_mul

omit [IsTopologicalGroup G] in
@[simp]
lemma transEquiv_apply (H : OpenSubgroup G) (K : OpenSubgroup H) (x : K) :
    ((transEquiv H K x : trans H K) : G) = (x : H) := rfl

omit [IsTopologicalGroup G] in
@[simp]
lemma transEquiv_symm_apply (H : OpenSubgroup G) (K : OpenSubgroup H)
    (x : trans H K) : (((transEquiv H K).symm x : K) : H) = (x : G) := by
  calc
    (((transEquiv H K).symm x : K) : H) =
        ((transEquiv H K ((transEquiv H K).symm x) : trans H K) : G) :=
      (transEquiv_apply H K _).symm
    _ = (x : G) := congrArg (fun y : trans H K => (y : G))
      ((transEquiv H K).apply_symm_apply x)

omit [IsTopologicalGroup G] in
instance transFiniteIndex (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex] :
    (trans H K).toSubgroup.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, trans_toSubgroup, Subgroup.index_map_subtype]
  exact Nat.mul_ne_zero
    (Subgroup.finiteIndex_iff.mp inferInstance)
    (Subgroup.finiteIndex_iff.mp inferInstance)

end OpenSubgroup

namespace TopRep

/-- Local joint-continuity synthesis through two nested open-subgroup
restrictions. -/
private instance jointlyContinuous_res_res_open (H : OpenSubgroup G) (K : OpenSubgroup H)
    (X : TopRep.{w} k G) [JointlyContinuous X] :
    JointlyContinuous (res K.subtype (res H.subtype X)) := by
  let _ : JointlyContinuous (res H.subtype X) :=
    jointlyContinuous_res H.toSubgroup X
  exact jointlyContinuous_res K.toSubgroup (res H.subtype X)

omit [IsTopologicalGroup G] in
/-- Joint continuity of an action persists under two nested open-subgroup
restrictions. This proof is the existing private local instance, made available
to exported compositions without changing the instance search of importers. -/
theorem jointlyContinuous_res_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    (X : TopRep.{w} k G) [JointlyContinuous X] :
    JointlyContinuous (res K.subtype (res H.subtype X)) :=
  jointlyContinuous_res_res_open H K X

end TopRep

attribute [local instance] TopRep.jointlyContinuous_res_trans

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

/-- The continuous homomorphism identifying a nested open subgroup with its
flattening in the ambient group. Its value computes via `transEquiv`. -/
@[expose]
noncomputable def transContinuousHom (H : OpenSubgroup G) (K : OpenSubgroup H) :
    K →ₜ* OpenSubgroup.trans H K :=
  ContinuousMonoidHom.toContinuousMonoidHom (OpenSubgroup.transEquiv H K)

/-- Identity on coefficients, comparing direct and iterated restriction. -/
noncomputable def transCoeffHom (H : OpenSubgroup G) (K : OpenSubgroup H) :
    TopRep.res (transContinuousHom H K : K →* OpenSubgroup.trans H K)
        (TopRep.res (OpenSubgroup.trans H K).subtype X) ⟶
      TopRep.res K.subtype (TopRep.res H.subtype X) :=
  TopRep.ofHom {
    __ := ContinuousLinearMap.id k X
    isIntertwining' := by intro g; rfl }

/-- Pull a crossed homomorphism for the flattened subgroup back to the nested
subgroup through the canonical equivalence. Evaluation computes by pullback. -/
@[expose]
noncomputable def crossedTrans (H : OpenSubgroup G) (K : OpenSubgroup H) :
    continuousCrossedHom (TopRep.res (OpenSubgroup.trans H K).subtype X) →L[k]
      continuousCrossedHom (TopRep.res K.subtype (TopRep.res H.subtype X)) :=
  ((ContinuousMap.compCLM k X
      ⟨transContinuousHom H K, (transContinuousHom H K).continuous⟩).comp
        (Submodule.subtypeL
          (continuousCrossedHom
            (TopRep.res (OpenSubgroup.trans H K).subtype X)))).codRestrict
    (continuousCrossedHom (TopRep.res K.subtype (TopRep.res H.subtype X)))
      fun f g h => by
        change f.1 (OpenSubgroup.transEquiv H K (g * h)) =
          X.ρ ((g : H) : G) (f.1 (OpenSubgroup.transEquiv H K h)) +
            f.1 (OpenSubgroup.transEquiv H K g)
        rw [map_mul]
        exact f.2 _ _

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedTrans_apply (H : OpenSubgroup G) (K : OpenSubgroup H)
    (f : continuousCrossedHom
      (TopRep.res (OpenSubgroup.trans H K).subtype X)) (g : K) :
    (crossedTrans X H K f).1 g = f.1 (OpenSubgroup.transEquiv H K g) := rfl

namespace CorestrictionTransversal

/-- The representative `u * t` obtained from nested right transversals.
Its multiplication computes in the transversal product equivalence. -/
@[expose]
def towerRep (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) : G :=
  (p.1 : H) * (p.2 : G)

omit [IsTopologicalGroup G] in
lemma towerRep_injective (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    Function.Injective (towerRep H K U T) := by
  intro a b hab
  have hpair : ((a.1 : H), a.2) = ((b.1 : H), b.2) := T.2.1 hab
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun p => (p.1 : H)) hpair)
  · exact congrArg (fun p : H × ↥(T : Set G) => p.2) hpair

/-- The canonical indexing equivalence for the product transversal.
Evaluation computes to the product representative. -/
@[expose]
noncomputable def towerRepEquiv (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    (↥(U : Set H) × ↥(T : Set G)) ≃ Set.range (towerRep H K U T) :=
  Equiv.ofInjective (towerRep H K U T) (towerRep_injective H K U T)

omit [IsTopologicalGroup G] in
@[simp]
lemma towerRepEquiv_apply_coe (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) :
    (towerRepEquiv H K U T p : G) = towerRep H K U T p := rfl

/-- Decomposition of the ambient group through two nested right transversals.
The inverse computes when constructing the composite right transversal. -/
@[expose]
noncomputable def towerDecompositionEquiv (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    G ≃ K × (↥(U : Set H) × ↥(T : Set G)) :=
  T.2.equiv |>.trans <|
    (Equiv.prodCongr U.2.equiv (Equiv.refl _)).trans
      (Equiv.prodAssoc K ↥(U : Set H) ↥(T : Set G))

/-- Products of representatives for `K` in `H` and `H` in `G` form a
right transversal for the flattened copy of `K` in `G`. Its carrier computes
as the range of the representative-product map. -/
@[expose]
noncomputable def transRightTransversal (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    (OpenSubgroup.trans H K).toSubgroup.RightTransversal := by
  let P : Set G := Set.range (towerRep H K U T)
  let eP : (↥(U : Set H) × ↥(T : Set G)) ≃ P :=
    towerRepEquiv H K U T
  let eD : K × (↥(U : Set H) × ↥(T : Set G)) ≃
      OpenSubgroup.trans H K × P :=
    Equiv.prodCongr (OpenSubgroup.transEquiv H K).toEquiv eP
  refine ⟨P, ?_⟩
  change Function.Bijective (fun p : OpenSubgroup.trans H K × P =>
    (p.1 : G) * (p.2 : G))
  have hb := (eD.symm.trans (towerDecompositionEquiv H K U T).symm).bijective
  convert hb using 1
  funext p
  rcases p with ⟨k, p⟩
  rcases p.2 with ⟨ut, hut⟩
  have hp : eP ut = p := Subtype.ext hut
  subst p
  change ((k : OpenSubgroup.trans H K) : G) *
      towerRep H K U T ut = _
  simp only [eD, eP, towerDecompositionEquiv, Equiv.trans_apply,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.prodAssoc_symm_apply, Prod.map_apply', Equiv.symm_apply_apply,
    Equiv.refl_symm, Equiv.refl_apply]
  rw [T.2.equiv_symm_apply, U.2.equiv_symm_apply]
  change (k : G) * ((ut.1 : H) * (ut.2 : G)) =
    ((((OpenSubgroup.transEquiv H K).symm k : K) : H) * (ut.1 : H)) *
      (ut.2 : G)
  rw [OpenSubgroup.transEquiv_symm_apply]
  rw [mul_assoc]

omit [IsTopologicalGroup G] in
@[simp]
lemma coe_transRightTransversal (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    (transRightTransversal H K U T : Set G) =
      Set.range (towerRep H K U T) := rfl

/-- The product indexing equivalence with the actual composite transversal.
Its application computes the representative product. -/
@[expose]
noncomputable def transRightRepEquiv (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal) :
    (↥(U : Set H) × ↥(T : Set G)) ≃
      ↥(transRightTransversal H K U T : Set G) :=
  Equiv.ofBijective
    (fun p => ⟨towerRep H K U T p, by
      rw [coe_transRightTransversal]
      exact ⟨p, rfl⟩⟩)
    ⟨fun _ _ h => towerRep_injective H K U T (Subtype.ext_iff.mp h),
      fun q => by
        have hq : (q : G) ∈ Set.range (towerRep H K U T) := by
          rw [← coe_transRightTransversal]
          exact q.2
        rcases hq with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        apply Subtype.ext
        exact hp⟩

omit [IsTopologicalGroup G] in
@[simp]
lemma transRightRepEquiv_apply_coe (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) :
    (transRightRepEquiv H K U T p : G) = towerRep H K U T p := rfl

omit [IsTopologicalGroup G] in
lemma transRightTransversal_equiv (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) (g : G) :
    (transRightTransversal H K U T).2.equiv
        ((transRightRepEquiv H K U T p : G) * g) =
      (OpenSubgroup.transEquiv H K
          (factor U p.1 (factor T p.2 g)),
        transRightRepEquiv H K U T
          (next U p.1 (factor T p.2 g), next T p.2 g)) := by
  apply (transRightTransversal H K U T).2.equiv.symm.injective
  rw [Equiv.symm_apply_apply]
  rw [(transRightTransversal H K U T).2.equiv_symm_apply]
  change ((p.1 : H) : G) * (p.2 : G) * g =
    (((factor U p.1 (factor T p.2 g) : K) : H) : G) *
      (((next U p.1 (factor T p.2 g) : H) : G) * (next T p.2 g : G))
  rw [mul_assoc, ← factor_mul_next T, ← mul_assoc]
  have hU := congrArg H.subtype (factor_mul_next U p.1 (factor T p.2 g))
  change (((factor U p.1 (factor T p.2 g) : K) : H) : G) *
      ((next U p.1 (factor T p.2 g) : H) : G) =
    ((p.1 : H) : G) * ((factor T p.2 g : H) : G) at hU
  rw [← hU, mul_assoc]

omit [IsTopologicalGroup G] in
lemma factor_transRightTransversal (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) (g : G) :
    factor (transRightTransversal H K U T) (transRightRepEquiv H K U T p) g =
      OpenSubgroup.transEquiv H K (factor U p.1 (factor T p.2 g)) :=
  congrArg Prod.fst (transRightTransversal_equiv H K U T p g)

omit [IsTopologicalGroup G] in
lemma next_transRightTransversal (H : OpenSubgroup G) (K : OpenSubgroup H)
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (p : ↥(U : Set H) × ↥(T : Set G)) (g : G) :
    next (transRightTransversal H K U T) (transRightRepEquiv H K U T p) g =
      transRightRepEquiv H K U T
        (next U p.1 (factor T p.2 g), next T p.2 g) :=
  congrArg Prod.snd (transRightTransversal_equiv H K U T p g)

lemma transferCrossed_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex]
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom
      (TopRep.res (OpenSubgroup.trans H K).subtype X)) :
    transferCrossed X H T
        (transferCrossed (TopRep.res H.subtype X) K U (crossedTrans X H K f)) =
      transferCrossed X (OpenSubgroup.trans H K)
        (transRightTransversal H K U T) f := by
  let _ : Fintype ↥(U : Set H) := U.2.finite_right.fintype
  let _ : Fintype ↥(T : Set G) := T.2.finite_right.fintype
  let _ : Fintype ↥(transRightTransversal H K U T : Set G) :=
    (transRightTransversal H K U T).2.finite_right.fintype
  ext g
  rw [transferCrossed_apply, transferCrossed_apply]
  simp_rw [transferCrossed_apply (TopRep.res H.subtype X) K U]
  simp_rw [map_sum]
  change (∑ t : ↥(T : Set G), ∑ u : ↥(U : Set H),
      X.ρ ((t : G)⁻¹)
        (X.ρ (((u : H) : G)⁻¹)
          (f.1 (OpenSubgroup.transEquiv H K
            (factor U u (factor T t g)))))) =
    ∑ p : ↥(transRightTransversal H K U T : Set G),
      X.ρ ((p : G)⁻¹)
        (f.1 (factor (transRightTransversal H K U T) p g))
  have hright := Equiv.sum_comp (transRightRepEquiv H K U T)
    (fun p : ↥(transRightTransversal H K U T : Set G) =>
      X.ρ ((p : G)⁻¹)
        (f.1 (factor (transRightTransversal H K U T) p g)))
  rw [← hright]
  simp_rw [transRightRepEquiv_apply_coe, factor_transRightTransversal]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro t _
  change X.ρ ((t : G)⁻¹)
      (X.ρ (((u : H) : G)⁻¹)
        (f.1 (OpenSubgroup.transEquiv H K
          (factor U u (factor T t g))))) =
    X.ρ ((((u : H) : G) * (t : G))⁻¹)
      (f.1 (OpenSubgroup.transEquiv H K
        (factor U u (factor T t g))))
  rw [mul_inv_rev, map_mul]
  rfl

omit [IsTopologicalGroup G] in
lemma crossedTrans_principal (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] (x : X) :
    crossedTrans X H K
        (principalToCrossed
          (TopRep.res (OpenSubgroup.trans H K).subtype X) x) =
      principalToCrossed
        (TopRep.res K.subtype (TopRep.res H.subtype X)) x := by
  ext g
  rfl

/-- Pullback along the nested/flattened equivalence descends modulo principal
cocycles. Its lift computes on quotient representatives. -/
@[expose]
noncomputable def crossedQuotientTrans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom
        (TopRep.res (OpenSubgroup.trans H K).subtype X) ⧸
      principalCocycles
        (TopRep.res (OpenSubgroup.trans H K).subtype X)) →L[k]
    (continuousCrossedHom
        (TopRep.res K.subtype (TopRep.res H.subtype X)) ⧸
      principalCocycles
        (TopRep.res K.subtype (TopRep.res H.subtype X))) :=
  (principalCocycles
      (TopRep.res (OpenSubgroup.trans H K).subtype X)).liftQL
    ((principalCocycles
        (TopRep.res K.subtype (TopRep.res H.subtype X))).mkQL.comp
      (crossedTrans X H K)) <| by
        intro f hf
        rw [LinearMap.mem_ker]
        change (principalCocycles
          (TopRep.res K.subtype (TopRep.res H.subtype X))).mkQL
            (crossedTrans X H K f) = 0
        change f ∈ LinearMap.range (principalToCrossed
          (TopRep.res (OpenSubgroup.trans H K).subtype X)) at hf
        rcases hf with ⟨x, rfl⟩
        rw [crossedTrans_principal]
        exact (Submodule.Quotient.mk_eq_zero
          (principalCocycles
            (TopRep.res K.subtype (TopRep.res H.subtype X)))).2 ⟨x, rfl⟩

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedQuotientTrans_mk (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom
      (TopRep.res (OpenSubgroup.trans H K).subtype X)) :
    crossedQuotientTrans X H K
        ((principalCocycles
          (TopRep.res (OpenSubgroup.trans H K).subtype X)).mkQ f) =
      (principalCocycles
        (TopRep.res K.subtype (TopRep.res H.subtype X))).mkQ
          (crossedTrans X H K f) := rfl

omit [IsTopologicalGroup G] in
lemma crossedTrans_comp_mkQL (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (crossedTrans X H K) ≫
        TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res K.subtype (TopRep.res H.subtype X))).mkQL =
      TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res (OpenSubgroup.trans H K).subtype X)).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientTrans X H K) := by
  ext f
  rfl

set_option maxHeartbeats 800000 in
-- The two-stage transversal calculation expands both quotient transfers.
lemma transferQuotient_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex]
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    (transferQuotient X H T).comp
        ((transferQuotient (TopRep.res H.subtype X) K U).comp
          (crossedQuotientTrans X H K)) =
      transferQuotient X (OpenSubgroup.trans H K)
        (transRightTransversal H K U T) := by
  apply ContinuousLinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro f
  change (principalCocycles X).mkQ
      (transferCrossed X H T
        (transferCrossed (TopRep.res H.subtype X) K U
          (crossedTrans X H K f))) =
    (principalCocycles X).mkQ
      (transferCrossed X (OpenSubgroup.trans H K)
        (transRightTransversal H K U T) f)
  rw [transferCrossed_trans]

set_option maxHeartbeats 800000 in
-- Evaluating the composed cocycle comparisons unfolds both restriction maps.
lemma cocyclesOneCrossedIso_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] [LocallyCompactSpace K] :
    cocyclesMap (transContinuousHom H K) (transCoeffHom X H K) 1 ≫
        (cocyclesOneCrossedIso
          (TopRep.res K.subtype (TopRep.res H.subtype X))).hom =
      (cocyclesOneCrossedIso
        (TopRep.res (OpenSubgroup.trans H K).subtype X)).hom ≫
        TopModuleCat.ofHom (crossedTrans X H K) := by
  ext σ h
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom]
  change
    (((cocyclesOneCrossedIso
        (TopRep.res K.subtype (TopRep.res H.subtype X))).hom
      (cocyclesMap (transContinuousHom H K) (transCoeffHom X H K) 1 σ)).1 h) =
      (((cocyclesOneCrossedIso
        (TopRep.res (OpenSubgroup.trans H K).subtype X)).hom σ).1
          (OpenSubgroup.transEquiv H K h))
  rw [cocyclesOneCrossedIso_hom_apply, cocyclesOneCrossedIso_hom_apply]
  have hh := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (transContinuousHom H K) (transCoeffHom X H K)) 1) σ
  exact congrArg (fun τ => τ.1 1 h) hh

set_option maxHeartbeats 3000000 in
-- Transporting the quotient comparison requires reassociating the cohomology isomorphisms.
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homologyQuotientIso_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] [LocallyCompactSpace K] :
    map (transContinuousHom H K) (transCoeffHom X H K) 1 ≫
        (homologyQuotientIso
          (TopRep.res K.subtype (TopRep.res H.subtype X))).hom =
      (homologyQuotientIso
        (TopRep.res (OpenSubgroup.trans H K).subtype X)).hom ≫
        TopModuleCat.ofHom (crossedQuotientTrans X H K) := by
  apply (cancel_epi
    (π (TopRep.res (OpenSubgroup.trans H K).subtype X) 1)).1
  rw [← Category.assoc, π_map, Category.assoc,
    π_comp_homologyQuotientIso, ← Category.assoc,
    cocyclesOneCrossedIso_trans, Category.assoc,
    crossedTrans_comp_mkQL, ← Category.assoc,
    ← π_comp_homologyQuotientIso, Category.assoc]

set_option maxHeartbeats 3000000 in
-- The degree-one comparison composes nested crossed and native cohomology isomorphisms.
set_option backward.isDefEq.respectTransparency false in
lemma degreeOneIso_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] [LocallyCompactSpace K] :
    TopModuleCat.ofHom (crossedQuotientTrans X H K) ≫
        (degreeOneIso
          (TopRep.res K.subtype (TopRep.res H.subtype X))).hom =
      (degreeOneIso
        (TopRep.res (OpenSubgroup.trans H K).subtype X)).hom ≫
        map (transContinuousHom H K) (transCoeffHom X H K) 1 := by
  apply (cancel_mono
    (homologyQuotientIso
      (TopRep.res K.subtype (TopRep.res H.subtype X))).hom).1
  rw [degreeOneIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [Category.assoc, homologyQuotientIso_trans, ← Category.assoc,
    degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

/-- Degree-one transport from a flattened subgroup to the corresponding
nested subgroup, expressed through crossed homomorphisms. -/
noncomputable def transDegreeOne (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace (OpenSubgroup.trans H K)]
    [LocallyCompactSpace K] :
    continuousCohomology 1
        (TopRep.res (OpenSubgroup.trans H K).subtype X) ⟶
      continuousCohomology 1
        (TopRep.res K.subtype (TopRep.res H.subtype X)) :=
  (degreeOneIso
      (TopRep.res (OpenSubgroup.trans H K).subtype X)).inv ≫
    TopModuleCat.ofHom (crossedQuotientTrans X H K) ≫
      (degreeOneIso
        (TopRep.res K.subtype (TopRep.res H.subtype X))).hom

set_option maxHeartbeats 800000 in
-- Normalizing the nested degree-one map expands the quotient comparisons.
lemma transDegreeOne_eq_map (H : OpenSubgroup G) (K : OpenSubgroup H)
    [TopRep.JointlyContinuous X]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] [LocallyCompactSpace K] :
    transDegreeOne X H K =
      map (transContinuousHom H K) (transCoeffHom X H K) 1 := by
  simp only [transDegreeOne]
  rw [degreeOneIso_trans]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

set_option maxHeartbeats 800000 in
-- Transversal corestriction transitivity compares the flattened and nested sums.
lemma corestrictionOneWithTransversal_trans
    (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex]
    (U : K.toSubgroup.RightTransversal) (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] [LocallyCompactSpace K]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] :
    transDegreeOne X H K ≫
        corestrictionOneWithTransversal (TopRep.res H.subtype X) K U ≫
      corestrictionOneWithTransversal X H T =
    corestrictionOneWithTransversal X (OpenSubgroup.trans H K)
      (transRightTransversal H K U T) := by
  simp only [transDegreeOne, corestrictionOneWithTransversal, Category.assoc]
  rw [Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  have hq :
      TopModuleCat.ofHom (crossedQuotientTrans X H K) ≫
          TopModuleCat.ofHom
            (transferQuotient (TopRep.res H.subtype X) K U) ≫
        TopModuleCat.ofHom (transferQuotient X H T) =
      TopModuleCat.ofHom
        (transferQuotient X (OpenSubgroup.trans H K)
          (transRightTransversal H K U T)) := by
    ext q
    exact DFunLike.congr_fun (transferQuotient_trans X H K U T) q
  simpa only [Category.assoc] using congrArg
    (fun m =>
      (degreeOneIso
        (TopRep.res (OpenSubgroup.trans H K).subtype X)).inv ≫
        m ≫ (degreeOneIso X).hom) hq

set_option maxHeartbeats 800000 in
-- Flattening both crossed-homomorphism transfers expands the transversal formulas.
/-- Degree-one corestriction is transitive through nested open finite-index
subgroups, after the canonical flattened/nested identification. -/
lemma corestrictionOne_trans_crossed (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] [LocallyCompactSpace K]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] :
    transDegreeOne X H K ≫
        corestrictionOne (TopRep.res H.subtype X) K ≫
      corestrictionOne X H =
    corestrictionOne X (OpenSubgroup.trans H K) := by
  let U : K.toSubgroup.RightTransversal := default
  let T : H.toSubgroup.RightTransversal := default
  rw [corestrictionOne_eq_withTransversal
    (TopRep.res H.subtype X) K U]
  rw [corestrictionOne_eq_withTransversal X H T]
  rw [corestrictionOne_eq_withTransversal X (OpenSubgroup.trans H K)
    (transRightTransversal H K U T)]
  exact corestrictionOneWithTransversal_trans X H K U T

set_option maxHeartbeats 800000 in
-- The native transitivity proof transports the crossed result through subgroup equivalences.
/-- Degree-one corestriction is transitive through nested open finite-index
subgroups, using native continuous-cohomology transport along the canonical
equivalence with the flattened subgroup. -/
lemma corestrictionOne_trans (H : OpenSubgroup G) (K : OpenSubgroup H)
    [H.toSubgroup.FiniteIndex] [K.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] [LocallyCompactSpace K]
    [LocallyCompactSpace (OpenSubgroup.trans H K)] :
    map (transContinuousHom H K) (transCoeffHom X H K) 1 ≫
        corestrictionOne (TopRep.res H.subtype X) K ≫
      corestrictionOne X H =
    corestrictionOne X (OpenSubgroup.trans H K) := by
  rw [← transDegreeOne_eq_map]
  exact corestrictionOne_trans_crossed X H K


end CorestrictionTransversal

end ContinuousCohomology

end
