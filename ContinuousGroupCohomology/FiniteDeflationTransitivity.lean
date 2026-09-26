/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.ExceptionalDeflation

/-!
# Transitivity of finite-level deflation

For normal subgroups `S ≤ T ≤ U`, finite-level negative deflation is
functorial: the map from `S` to `U` is the composite through `T`. The same
composition and identity laws are propagated to degree-zero coinvariants,
the total-invariants comparison, norm kernels and cokernels, and Tate
degrees `-1` and `0`.

No inverse system or inverse limit is constructed here.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

private noncomputable def prodEquivOfExact
    {K H L : Type u} [Group K] [Group H] [Group L]
    (p : K →* H) (hp : Function.Surjective p)
    (i : L →* K) (hi : Function.Injective i) (hker : i.range = p.ker) :
    H × L ≃ K :=
  Equiv.ofBijective
    (fun ql ↦ hp.hasRightInverse.choose ql.1 * i ql.2)
    ⟨by
      rintro ⟨q, l⟩ ⟨q', l'⟩ h
      have hil (z : L) : p (i z) = 1 :=
        MonoidHom.mem_ker.1 (hker ▸ (⟨z, rfl⟩ : i z ∈ i.range))
      have hq : q = q' := by
        have := congrArg p h
        rw [map_mul, map_mul, hil, hil, mul_one, mul_one,
          hp.hasRightInverse.choose_spec q,
          hp.hasRightInverse.choose_spec q'] at this
        exact this
      subst q'
      have hli : i l = i l' := mul_left_cancel h
      exact Prod.ext rfl (hi hli),
    by
      intro k
      let q := p k
      let s := hp.hasRightInverse.choose
      have hs : Function.RightInverse s p := hp.hasRightInverse.choose_spec
      have hk : (s q)⁻¹ * k ∈ p.ker := by
        apply MonoidHom.mem_ker.2
        rw [map_mul, map_inv, hs q]
        simp [q]
      have hki : (s q)⁻¹ * k ∈ i.range := hker.symm ▸ hk
      rcases hki with ⟨l, hl⟩
      refine ⟨(q, l), ?_⟩
      change s q * i l = k
      rw [hl]
      exact mul_inv_cancel_left (s q) k⟩

/-- The direct quotient homomorphism from `G / S` to `G / T`. -/
@[expose]
def finiteDeflationGroupHom (S T : Subgroup G) [S.Normal] [T.Normal]
    (hST : S ≤ T) : G ⧸ S →* G ⧸ T :=
  QuotientGroup.map S T (MonoidHom.id G) hST

/-- The direct quotient homomorphism restricted to the image of a larger
subgroup. -/
private def finiteDeflationSubgroupHom (S T U : Subgroup G)
    [S.Normal] [T.Normal] (hST : S ≤ T) :
    U.map (QuotientGroup.mk' S) →* U.map (QuotientGroup.mk' T) where
  toFun q := ⟨finiteDeflationGroupHom S T hST q.1, by
    rcases q.2 with ⟨u, hu, hq⟩
    refine ⟨u, hu, ?_⟩
    rw [← hq]
    rfl⟩
  map_one' := Subtype.ext (map_one (finiteDeflationGroupHom S T hST))
  map_mul' x y := Subtype.ext (map_mul (finiteDeflationGroupHom S T hST) x.1 y.1)

private lemma quotientToInvariants_action_finiteDeflationGroupHom
    (A : Rep.{u} R G) (S T : Subgroup G) [S.Normal] [T.Normal]
    (hST : S ≤ T) (q : G ⧸ S) (z : A.quotientToInvariants T) :
    (((A.quotientToInvariants T).ρ (finiteDeflationGroupHom S T hST q)) z).1 =
      (((A.quotientToInvariants S).ρ q)
        ⟨z.1, fun s ↦ z.2 ⟨s.1, hST s.2⟩⟩).1 := by
  refine QuotientGroup.induction_on q ?_
  intro g
  rfl

private lemma finiteDeflationSubgroupHom_surjective (S T U : Subgroup G)
    [S.Normal] [T.Normal] (hST : S ≤ T) :
    Function.Surjective (finiteDeflationSubgroupHom S T U hST) := by
  intro q
  rcases q.2 with ⟨u, hu, hq⟩
  refine ⟨⟨QuotientGroup.mk' S u, ⟨u, hu, rfl⟩⟩, Subtype.ext ?_⟩
  exact hq

private lemma finiteDeflationSubgroupHom_range_inclusion_eq_ker
    (S T U : Subgroup G) [S.Normal] [T.Normal]
    (hST : S ≤ T) (hTU : T ≤ U) :
    (Subgroup.inclusion (Subgroup.map_mono hTU) :
      T.map (QuotientGroup.mk' S) →*
        U.map (QuotientGroup.mk' S)).range =
      (finiteDeflationSubgroupHom S T U hST).ker := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    apply MonoidHom.mem_ker.2
    apply Subtype.ext
    rcases t.2 with ⟨g, hg, htg⟩
    change finiteDeflationGroupHom S T hST t.1 = 1
    rw [← htg]
    change QuotientGroup.mk' T g = 1
    exact (QuotientGroup.eq_one_iff g).mpr hg
  · intro hq
    rcases q.2 with ⟨g, hgU, hqg⟩
    have hgT : g ∈ T := by
      have hmk := congrArg Subtype.val (MonoidHom.mem_ker.1 hq)
      change finiteDeflationGroupHom S T hST q.1 = 1 at hmk
      rw [← hqg] at hmk
      change QuotientGroup.mk' T g = 1 at hmk
      exact (QuotientGroup.eq_one_iff g).mp hmk
    refine ⟨⟨q.1, ⟨g, hgT, hqg⟩⟩, rfl⟩

private lemma thirdIso_comp_quotient_mk (S T : Subgroup G) [S.Normal] [T.Normal]
    (hST : S ≤ T) :
    (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom.comp
        (QuotientGroup.mk' (T.map (QuotientGroup.mk' S))) =
      finiteDeflationGroupHom S T hST := by
  ext g
  rfl

/-- The coefficient-level finite norm from `S`-invariants to `T`-invariants,
viewed over the composite quotient homomorphism. -/
private noncomputable def finiteNegativeDeflationCoeff (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    A.quotientToInvariants S ⟶
      Rep.res
        ((QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom.comp
          (QuotientGroup.mk' (T.map (QuotientGroup.mk' S))))
        (A.quotientToInvariants T) :=
  Rep.toCoinvariantsMkQ (A.quotientToInvariants S)
      (T.map (QuotientGroup.mk' S)) ≫
    (Rep.resFunctor (QuotientGroup.mk' (T.map (QuotientGroup.mk' S)))).map
      (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S)) ≫
        (nestedQuotientInvariantsRepIso A S T hST).hom)

/-- The coefficient norm for finite negative deflation, typed over the direct
quotient homomorphism from `G / S` to `G / T`. -/
@[expose]
noncomputable def finiteNegativeDeflationCoeffDirect (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    A.quotientToInvariants S ⟶
      Rep.res (finiteDeflationGroupHom S T hST) (A.quotientToInvariants T) :=
  let coeff := Rep.toCoinvariantsMkQ (A.quotientToInvariants S)
      (T.map (QuotientGroup.mk' S)) ≫
    (Rep.resFunctor (QuotientGroup.mk' (T.map (QuotientGroup.mk' S)))).map
      (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S)) ≫
        (nestedQuotientInvariantsRepIso A S T hST).hom)
  Rep.ofHom ⟨coeff.hom.toLinearMap, fun g ↦ by
    change _ =
      (A.quotientToInvariants T).ρ (finiteDeflationGroupHom S T hST g) ∘ₗ _
    rw [← thirdIso_comp_quotient_mk S T hST]
    exact coeff.hom.isIntertwining' g⟩

set_option backward.isDefEq.respectTransparency false in
private lemma finiteNegativeDeflation_eq_map (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    finiteNegativeDeflation A S T hST n =
      groupHomology.map
        ((QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom.comp
          (QuotientGroup.mk' (T.map (QuotientGroup.mk' S))))
        (finiteNegativeDeflationCoeff A S T hST) n := by
  rw [finiteNegativeDeflation_formula]
  rw [groupHomology.coinfNatTrans_app, groupHomology.functor_map]
  rw [← groupHomology.map_comp]
  rw [← groupHomology.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false

/-- Finite negative deflation is the group-homology map induced by the direct
quotient homomorphism and the direct coefficient norm. -/
lemma finiteNegativeDeflation_eq_direct_map (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    finiteNegativeDeflation A S T hST n =
      groupHomology.map (finiteDeflationGroupHom S T hST)
        (finiteNegativeDeflationCoeffDirect A S T hST) n := by
  rw [finiteNegativeDeflation_eq_map]
  apply groupHomology.map_congr (thirdIso_comp_quotient_mk S T hST)
  rfl

private lemma finiteDeflationGroupHom_comp (S T U : Subgroup G)
    [S.Normal] [T.Normal] [U.Normal] (hST : S ≤ T) (hTU : T ≤ U) :
    (finiteDeflationGroupHom T U hTU).comp
        (finiteDeflationGroupHom S T hST) =
      finiteDeflationGroupHom S U (hST.trans hTU) := by
  ext g
  rfl

private lemma finiteDeflationGroupHom_refl (S : Subgroup G) [S.Normal] :
    finiteDeflationGroupHom S S le_rfl = MonoidHom.id (G ⧸ S) := by
  ext q
  rfl

/-- The direct coefficient norm is the sum over the residual quotient image. -/
@[simp]
lemma finiteNegativeDeflationCoeffDirect_apply_val (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))]
    (x : A.quotientToInvariants S) :
    ((finiteNegativeDeflationCoeffDirect A S T hST).hom x).1 =
      ∑ q : T.map (QuotientGroup.mk' S),
        (((A.quotientToInvariants S).ρ q.1) x).1 := by
  change (((nestedQuotientInvariantsRepIso A S T hST).hom.hom)
      (FiniteGroupTateCohomology.quotientNorm
        (A.quotientToInvariants S) (T.map (QuotientGroup.mk' S))
        (Representation.Coinvariants.mk _ x))).1 = _
  rw [FiniteGroupTateCohomology.quotientNorm_mk]
  simp only [Representation.norm, LinearMap.sum_apply]
  change (↑(∑ q : T.map (QuotientGroup.mk' S),
    ((A.quotientToInvariants S).ρ q.1) x) : A) = _
  simp only [Submodule.coe_sum]

private lemma finiteNegativeDeflationCoeffDirect_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (S.map (QuotientGroup.mk' S))] :
    (finiteNegativeDeflationCoeffDirect A S S le_rfl).hom.toLinearMap =
      ((𝟙 (A.quotientToInvariants S)) :
        A.quotientToInvariants S ⟶ A.quotientToInvariants S).hom.toLinearMap := by
  have hbot : S.map (QuotientGroup.mk' S) = ⊥ := by
    apply le_antisymm
    · rintro q ⟨s, hs, rfl⟩
      exact (QuotientGroup.eq_one_iff s).mpr hs
    · exact bot_le
  let _ : Unique (S.map (QuotientGroup.mk' S)) := by
    rw [hbot]
    infer_instance
  ext x
  change ((finiteNegativeDeflationCoeffDirect A S S le_rfl).hom x).1 = x.1
  rw [finiteNegativeDeflationCoeffDirect_apply_val]
  rw [Fintype.sum_unique]
  have hdefault : (default : S.map (QuotientGroup.mk' S)) = 1 :=
    Subsingleton.elim _ _
  rw [hdefault]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma finiteNegativeDeflationCoeffDirect_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    (finiteNegativeDeflationCoeffDirect A S T hST ≫
        (Rep.resFunctor (finiteDeflationGroupHom S T hST)).map
          (finiteNegativeDeflationCoeffDirect A T U hTU)).hom.toLinearMap =
      (finiteNegativeDeflationCoeffDirect A S U (hST.trans hTU)).hom.toLinearMap := by
  ext x
  change ((finiteNegativeDeflationCoeffDirect A T U hTU).hom
      ((finiteNegativeDeflationCoeffDirect A S T hST).hom x)).1 =
    ((finiteNegativeDeflationCoeffDirect A S U (hST.trans hTU)).hom x).1
  rw [finiteNegativeDeflationCoeffDirect_apply_val,
    finiteNegativeDeflationCoeffDirect_apply_val]
  let p := finiteDeflationSubgroupHom S T U hST
  let hp : Function.Surjective p :=
    finiteDeflationSubgroupHom_surjective S T U hST
  let i : T.map (QuotientGroup.mk' S) →*
      U.map (QuotientGroup.mk' S) :=
    Subgroup.inclusion (Subgroup.map_mono hTU)
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : U.map (QuotientGroup.mk' S) ↦ z.1) hab
  have hker : i.range = p.ker := by
    exact finiteDeflationSubgroupHom_range_inclusion_eq_ker S T U hST hTU
  let e : U.map (QuotientGroup.mk' T) ×
      T.map (QuotientGroup.mk' S) ≃ U.map (QuotientGroup.mk' S) :=
    prodEquivOfExact p hp i hi hker
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro q
  let s : U.map (QuotientGroup.mk' S) := hp.hasRightInverse.choose q
  have hs : p s = q := hp.hasRightInverse.choose_spec q
  have hsval : finiteDeflationGroupHom S T hST s.1 = q.1 :=
    congrArg Subtype.val hs
  rw [← hsval]
  rw [quotientToInvariants_action_finiteDeflationGroupHom]
  let y := (finiteNegativeDeflationCoeffDirect A S T hST).hom x
  have hy : (⟨y.1, fun z ↦ y.2 ⟨z.1, hST z.2⟩⟩ :
      A.quotientToInvariants S) =
      ∑ l : T.map (QuotientGroup.mk' S),
        (A.quotientToInvariants S).ρ l.1 x := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact finiteNegativeDeflationCoeffDirect_apply_val A S T hST x
  change (((A.quotientToInvariants S).ρ s.1)
    ⟨y.1, fun z ↦ y.2 ⟨z.1, hST z.2⟩⟩).1 = _
  rw [hy, map_sum, Submodule.coe_sum]
  apply Fintype.sum_congr
  intro l
  rw [← Module.End.mul_apply, ← map_mul]
  change (((A.quotientToInvariants S).ρ (s.1 * i l)) x).1 = _
  congr 3

/-- Finite negative deflation through `T` is direct finite negative deflation
from `S` to `U`. -/
lemma finiteNegativeDeflation_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] (n : ℕ) :
    finiteNegativeDeflation A S T hST n ≫
        finiteNegativeDeflation A T U hTU n =
      finiteNegativeDeflation A S U (hST.trans hTU) n := by
  rw [finiteNegativeDeflation_eq_direct_map,
    finiteNegativeDeflation_eq_direct_map,
    finiteNegativeDeflation_eq_direct_map]
  rw [← groupHomology.map_comp]
  apply groupHomology.map_congr
  · exact finiteDeflationGroupHom_comp S T U hST hTU
  · exact finiteNegativeDeflationCoeffDirect_comp A S T U hST hTU

/-- Finite negative deflation from a normal subgroup to itself is the identity. -/
lemma finiteNegativeDeflation_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (S.map (QuotientGroup.mk' S))] (n : ℕ) :
    finiteNegativeDeflation A S S le_rfl n = 𝟙 _ := by
  rw [finiteNegativeDeflation_eq_direct_map]
  rw [← groupHomology.map_id]
  apply groupHomology.map_congr
  · exact finiteDeflationGroupHom_refl S
  · exact finiteNegativeDeflationCoeffDirect_refl A S

private lemma finiteNegativeDeflationCoinvariants_H0Iso_hom (A : Rep.{u} R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (groupHomology.H0Iso (A.quotientToInvariants S)).hom ≫
        finiteNegativeDeflationCoinvariants A S T hST =
      finiteNegativeDeflation A S T hST 0 ≫
        (groupHomology.H0Iso (A.quotientToInvariants T)).hom := by
  apply (cancel_epi (groupHomology.H0π (A.quotientToInvariants S))).1
  rw [← Category.assoc, groupHomology.H0π_comp_H0Iso_hom]
  rw [finiteNegativeDeflationCoinvariants_mk_hom]
  rw [finiteNegativeDeflation_eq_direct_map]
  conv_rhs => rw [← Category.assoc, groupHomology.H0π_comp_map]
  conv_rhs => rw [Category.assoc, groupHomology.H0π_comp_H0Iso_hom]
  rfl

/-- The canonical total-invariants identifications compose through nested
normal subgroups. -/
lemma finiteLevelTotalInvariantsEquiv_trans (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U) :
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
        (finiteLevelTotalInvariantsEquiv A T U hTU).toModuleIso.hom =
      (finiteLevelTotalInvariantsEquiv A S U (hST.trans hTU)).toModuleIso.hom := by
  ext x
  rfl

/-- The canonical total-invariants identification at one level is the identity. -/
lemma finiteLevelTotalInvariantsEquiv_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal] :
    (finiteLevelTotalInvariantsEquiv A S S le_rfl).toModuleIso.hom = 𝟙 _ := by
  ext x
  rfl

/-- The coinvariant realizations of finite negative deflation compose through
nested normal subgroups. -/
lemma finiteNegativeDeflationCoinvariants_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    finiteNegativeDeflationCoinvariants A S T hST ≫
        finiteNegativeDeflationCoinvariants A T U hTU =
      finiteNegativeDeflationCoinvariants A S U (hST.trans hTU) := by
  apply (cancel_epi (groupHomology.H0Iso (A.quotientToInvariants S)).hom).1
  conv_rhs => rw [finiteNegativeDeflationCoinvariants_H0Iso_hom]
  rw [← Category.assoc, finiteNegativeDeflationCoinvariants_H0Iso_hom]
  rw [Category.assoc, finiteNegativeDeflationCoinvariants_H0Iso_hom]
  rw [← Category.assoc, finiteNegativeDeflation_comp]

/-- The coinvariant realization of finite negative deflation at one level is
the identity. -/
lemma finiteNegativeDeflationCoinvariants_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (S.map (QuotientGroup.mk' S))] :
    finiteNegativeDeflationCoinvariants A S S le_rfl = 𝟙 _ := by
  apply (cancel_epi (groupHomology.H0Iso (A.quotientToInvariants S)).hom).1
  rw [finiteNegativeDeflationCoinvariants_H0Iso_hom, finiteNegativeDeflation_refl]
  simp

/-- The maps induced on norm kernels compose through nested normal subgroups. -/
lemma finiteNegativeOneDeflationKernel_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (G ⧸ U)]
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S T hST ≫
        finiteNegativeOneDeflationKernel A T U hTU =
      finiteNegativeOneDeflationKernel A S U (hST.trans hTU) := by
  apply (cancel_mono (kernel.ι
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants U)))).1
  rw [Category.assoc, finiteNegativeOneDeflationKernel_ι]
  rw [← Category.assoc, finiteNegativeOneDeflationKernel_ι]
  rw [Category.assoc, finiteNegativeDeflationCoinvariants_comp]
  rw [← finiteNegativeOneDeflationKernel_ι]

/-- The map induced on a norm kernel at one level is the identity. -/
lemma finiteNegativeOneDeflationKernel_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (G ⧸ S)] [Fintype (S.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S S le_rfl = 𝟙 _ := by
  apply (cancel_mono (kernel.ι
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)))).1
  rw [finiteNegativeOneDeflationKernel_ι,
    finiteNegativeDeflationCoinvariants_refl]
  simp

/-- The maps induced on norm cokernels compose through nested normal subgroups. -/
lemma finiteZeroDeflationCokernel_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (G ⧸ U)]
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    finiteZeroDeflationCokernel A S T hST ≫
        finiteZeroDeflationCokernel A T U hTU =
      finiteZeroDeflationCokernel A S U (hST.trans hTU) := by
  apply (cancel_epi (cokernel.π
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)))).1
  rw [← Category.assoc, finiteZeroDeflationCokernel_π]
  rw [Category.assoc, finiteZeroDeflationCokernel_π]
  rw [← Category.assoc, finiteLevelTotalInvariantsEquiv_trans]
  rw [← finiteZeroDeflationCokernel_π]

/-- The map induced on a norm cokernel at one level is the identity. -/
lemma finiteZeroDeflationCokernel_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (G ⧸ S)] [Fintype (S.map (QuotientGroup.mk' S))] :
    finiteZeroDeflationCokernel A S S le_rfl = 𝟙 _ := by
  apply (cancel_epi (cokernel.π
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S)))).1
  rw [finiteZeroDeflationCokernel_π,
    finiteLevelTotalInvariantsEquiv_refl]
  simp

/-- Finite-level Tate deflation in degree `-1` composes through nested normal
subgroups. -/
lemma finiteNegativeOneDeflation_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (G ⧸ U)]
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflation A S T hST ≫
        finiteNegativeOneDeflation A T U hTU =
      finiteNegativeOneDeflation A S U (hST.trans hTU) := by
  apply (cancel_mono (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
    (A.quotientToInvariants U)).hom).1
  rw [Category.assoc, finiteNegativeOneDeflation_comp_kernelNormIso_hom]
  rw [← Category.assoc, finiteNegativeOneDeflation_comp_kernelNormIso_hom]
  rw [Category.assoc, finiteNegativeOneDeflationKernel_comp]
  rw [← finiteNegativeOneDeflation_comp_kernelNormIso_hom]

/-- Finite-level Tate deflation in degree `-1` at one level is the identity. -/
lemma finiteNegativeOneDeflation_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (G ⧸ S)] [Fintype (S.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflation A S S le_rfl = 𝟙 _ := by
  apply (cancel_mono (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
    (A.quotientToInvariants S)).hom).1
  rw [finiteNegativeOneDeflation_comp_kernelNormIso_hom,
    finiteNegativeOneDeflationKernel_refl]
  simp

/-- Finite-level Tate deflation in degree `0` composes through nested normal
subgroups. -/
lemma finiteZeroDeflation_comp (A : Rep.{u} R G)
    (S T U : Subgroup G) [S.Normal] [T.Normal] [U.Normal]
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)] [Fintype (G ⧸ U)]
    [Fintype (T.map (QuotientGroup.mk' S))]
    [Fintype (U.map (QuotientGroup.mk' T))]
    [Fintype (U.map (QuotientGroup.mk' S))] :
    finiteZeroDeflation A S T hST ≫ finiteZeroDeflation A T U hTU =
      finiteZeroDeflation A S U (hST.trans hTU) := by
  apply (cancel_mono (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
    (A.quotientToInvariants U)).hom).1
  rw [Category.assoc, finiteZeroDeflation_comp_cokernelNormIso_hom]
  rw [← Category.assoc, finiteZeroDeflation_comp_cokernelNormIso_hom]
  rw [Category.assoc, finiteZeroDeflationCokernel_comp]
  rw [← finiteZeroDeflation_comp_cokernelNormIso_hom]

/-- Finite-level Tate deflation in degree `0` at one level is the identity. -/
lemma finiteZeroDeflation_refl (A : Rep.{u} R G)
    (S : Subgroup G) [S.Normal]
    [Fintype (G ⧸ S)] [Fintype (S.map (QuotientGroup.mk' S))] :
    finiteZeroDeflation A S S le_rfl = 𝟙 _ := by
  apply (cancel_mono (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
    (A.quotientToInvariants S)).hom).1
  rw [finiteZeroDeflation_comp_cokernelNormIso_hom,
    finiteZeroDeflationCokernel_refl]
  simp


end ContinuousGroupCohomology
