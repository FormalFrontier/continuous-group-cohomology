/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.FiniteCoinvariants
public import ContinuousGroupCohomology.ExceptionalDeflation
public import ContinuousGroupCohomology.FiniteDeflationTransitivity

/-!
# Continuous finite coinvariant deflation

For nested open normal subgroups `S ≤ T` of a compact topological group,
the algebraic finite negative deflation on coinvariants is continuous for the
canonical compact quotient topologies. Its residual-quotient-norm formula
commutes with the relative norms into the common total-invariants group.

The coefficient ring has no specified topology. The construction retains the
common-universe and finite residual-kernel hypotheses of algebraic deflation.
It makes no identification with a Tate cohomology group.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The published algebraic finite negative deflation, continuously bundled
between the canonical compact finite coinvariants for `S ≤ T`. -/
@[expose] noncomputable def finiteCoinvariantDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariants A (L := L) S ⟶ finiteCoinvariants A (L := L) T := by
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom :=
        (finiteNegativeDeflationCoinvariants A S.toSubgroup T.toSubgroup hST).hom.toAddMonoidHom
      continuous_toFun := ?_ }
  let K := T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)
  let n : openSubgroupInvariants A S.toOpenSubgroup →
      openSubgroupInvariants A T.toOpenSubgroup := fun x ↦
    (nestedQuotientInvariantsRepIso A S.toSubgroup T.toSubgroup hST).hom
      (FiniteGroupTateCohomology.quotientNorm
        (A.quotientToInvariants S.toSubgroup) K
        (Representation.Coinvariants.mk
          ((A.quotientToInvariants S.toSubgroup).ρ.comp K.subtype) x))
  let _ : TopologicalSpace (openSubgroupInvariants A S.toOpenSubgroup) :=
    L.topology S.toOpenSubgroup
  let _ : TopologicalSpace (openSubgroupInvariants A T.toOpenSubgroup) :=
    L.topology T.toOpenSubgroup
  let _ : IsTopologicalAddGroup
      (openSubgroupInvariants A S.toOpenSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  have hn : Continuous n := by
    let sumMap : openSubgroupInvariants A S.toOpenSubgroup →
        openSubgroupInvariants A S.toOpenSubgroup := fun x ↦
      ∑ k : K, (A.quotientToInvariants S.toSubgroup).ρ k x
    have hsum : Continuous sumMap :=
      continuous_finsetSum Finset.univ fun k _ ↦
        continuous_quotientToInvariants_action A (L := L) S k
    have hcomp :
        (inclusion A T.toOpenSubgroup S.toOpenSubgroup hST) ∘ n = sumMap := by
      funext x
      apply Subtype.ext
      simp only [Function.comp_apply, inclusion_coe]
      dsimp only [n, sumMap]
      change
        ((nestedQuotientInvariantsRepIso A S.toSubgroup T.toSubgroup hST).hom
          (FiniteGroupTateCohomology.quotientNorm
            (A.quotientToInvariants S.toSubgroup) K
            (Representation.Coinvariants.mk
              ((A.quotientToInvariants S.toSubgroup).ρ.comp K.subtype) x)) : A) = _
      rw [FiniteGroupTateCohomology.quotientNorm_mk]
      change
        (Representation.norm
          ((A.quotientToInvariants S.toSubgroup).ρ.comp K.subtype) x : A) = _
      simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
      rfl
    apply
      (inclusion_isClosedEmbedding A L T.toOpenSubgroup S.toOpenSubgroup
        hST).isInducing.continuous_iff.mpr
    rw [hcomp]
    exact hsum
  apply continuous_coinduced_dom.2
  have htarget : Continuous (fun x : openSubgroupInvariants A S.toOpenSubgroup ↦
      finiteCoinvariantsMk A L T (n x)) :=
    (finiteCoinvariantsMk A L T).hom.continuous.comp hn
  convert htarget using 1
  funext x
  exact CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_mk_hom
      A S.toSubgroup T.toSubgroup hST) x

/-- On a representative, continuous finite coinvariant deflation is the
residual `T / S` norm followed by nested-invariants transport. -/
lemma finiteCoinvariantDeflation_mk
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    finiteCoinvariantDeflation A L S T hST (finiteCoinvariantsMk A L S x) =
      finiteCoinvariantsMk A L T
        ((nestedQuotientInvariantsRepIso A S.toSubgroup T.toSubgroup hST).hom
          (FiniteGroupTateCohomology.quotientNorm
            (A.quotientToInvariants S.toSubgroup)
            (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))
            (Representation.Coinvariants.mk
              ((A.quotientToInvariants S.toSubgroup).ρ.comp
                (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)).subtype) x))) := by
  exact CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_mk_hom
      A S.toSubgroup T.toSubgroup hST) x

private lemma normFromFiniteCoinvariants_val
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)]
    (x : finiteCoinvariants A (L := L) S) :
    ((normFromFiniteCoinvariants A L S x).1 : A) =
      ((FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants S.toSubgroup)).hom x).1.1 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ((normFromFiniteCoinvariants A L S
      (Representation.Coinvariants.mk
        (A.quotientToInvariants S.toSubgroup).ρ a)).1 : A) =
    ((FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S.toSubgroup)).hom
        (Representation.Coinvariants.mk
          (A.quotientToInvariants S.toSubgroup).ρ a)).1.1
  rw [normFromFiniteCoinvariants_mk A L S a]
  rw [relativeNorm_eq_quotientToInvariants_norm A S a]
  rfl

/-- The continuous norm square for the *actual* algebraic deflation:
`norm_T (deflation x) = norm_S x`, in the same total-invariants group. -/
lemma normFromFiniteCoinvariants_finiteCoinvariantDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : finiteCoinvariants A (L := L) S) :
    normFromFiniteCoinvariants A L T (finiteCoinvariantDeflation A L S T hST x) =
      normFromFiniteCoinvariants A L S x := by
  let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
  apply Subtype.ext
  rw [normFromFiniteCoinvariants_val A L T,
    normFromFiniteCoinvariants_val A L S]
  have h := CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_norm
      A S.toSubgroup T.toSubgroup hST) x
  change
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants T.toSubgroup)).hom
        (finiteNegativeDeflationCoinvariants
          A S.toSubgroup T.toSubgroup hST x) =
    finiteLevelTotalInvariantsEquiv A S.toSubgroup T.toSubgroup hST
      ((FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants S.toSubgroup)).hom x) at h
  exact (congrArg (fun y ↦ y.1.1) h).trans
    (finiteLevelTotalInvariantsEquiv_apply_val
      A S.toSubgroup T.toSubgroup hST _)

/-- Finite coinvariant deflation at a level is the identity, by algebraic
reflexivity. -/
@[simp] lemma finiteCoinvariantDeflation_refl
    (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantDeflation A L S S le_rfl = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_refl A S.toSubgroup) x

/-- Finite coinvariant deflations compose through nested levels, by algebraic
transitivity (with all three finite residual kernels). -/
lemma finiteCoinvariantDeflation_comp
    (S T U : OpenNormalSubgroup G) (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantDeflation A L S T hST ≫
        finiteCoinvariantDeflation A L T U hTU =
      finiteCoinvariantDeflation A L S U (hST.trans hTU) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.congr_fun
    (finiteNegativeDeflationCoinvariants_comp
      A S.toSubgroup T.toSubgroup U.toSubgroup hST hTU) x

end ContinuousGroupCohomology.LevelCompact
