/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.FiniteTateTopology
public import ContinuousGroupCohomology.FiniteCoinvariantDeflation

/-!
# Compact exceptional Tate deflation

The continuous deflation of finite coinvariants commutes with the norm into
the common total-invariants group. Its induced maps on the compact kernel in
degree `-1` and the compact quotient in degree `0` agree with algebraic Tate
deflation under the additive comparisons. Neither the coefficient ring nor
the algebraic Tate groups are given an additional topology.
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

/-- The compact degree `-1` map induced by coinvariant deflation and the
identity on the common total-invariants target. -/
@[expose] noncomputable def finiteTateNegOneDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateNegOne A L S ⟶ finiteTateNegOne A L T :=
  CompHausAddCommGrp.kernelMap
    (finiteCoinvariantDeflation A L S T hST)
    (𝟙 (group A L (⊤ : OpenSubgroup G)))
    (normFromFiniteCoinvariants A L S)
    (normFromFiniteCoinvariants A L T)
    (normFromFiniteCoinvariants_finiteCoinvariantDeflation A L S T hST)

/-- The compact degree `0` map induced by coinvariant deflation and the
identity on the common total-invariants target. -/
@[expose] noncomputable def finiteTateZeroDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateZero A L S ⟶ finiteTateZero A L T :=
  CompHausAddCommGrp.quotientRangeMap
    (finiteCoinvariantDeflation A L S T hST)
    (𝟙 (group A L (⊤ : OpenSubgroup G)))
    (normFromFiniteCoinvariants A L S)
    (normFromFiniteCoinvariants A L T)
    (normFromFiniteCoinvariants_finiteCoinvariantDeflation A L S T hST)

/-- Inclusion of the deflated kernel equals deflation of its inclusion. -/
@[simp] lemma finiteTateNegOneι_finiteTateNegOneDeflation_apply
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : finiteTateNegOne A L S) :
    finiteTateNegOneι A L T (finiteTateNegOneDeflation A L S T hST x) =
      finiteCoinvariantDeflation A L S T hST (finiteTateNegOneι A L S x) :=
  rfl

/-- On total-invariant representatives, degree-zero deflation is identity. -/
@[simp] lemma finiteTateZeroDeflation_finiteTateZeroπ_apply
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : group A L (⊤ : OpenSubgroup G)) :
    finiteTateZeroDeflation A L S T hST (finiteTateZeroπ A L S x) =
      finiteTateZeroπ A L T x :=
  rfl

/-- Compact degree `-1` deflation is the identity at equal levels. -/
@[simp] lemma finiteTateNegOneDeflation_refl (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateNegOneDeflation A L S S le_rfl = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change finiteCoinvariantDeflation A L S S le_rfl x.1 = x.1
  rw [finiteCoinvariantDeflation_refl]
  rfl

/-- Compact degree `0` deflation is the identity at equal levels. -/
@[simp] lemma finiteTateZeroDeflation_refl (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateZeroDeflation A L S S le_rfl = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change finiteTateZeroDeflation A L S S le_rfl
        (finiteTateZeroπ A L S x) = finiteTateZeroπ A L S x
    exact finiteTateZeroDeflation_finiteTateZeroπ_apply A L S S le_rfl x

/-- Compact degree `-1` deflation composes through nested levels. -/
lemma finiteTateNegOneDeflation_comp (S T U : OpenNormalSubgroup G)
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateNegOneDeflation A L S T hST ≫
        finiteTateNegOneDeflation A L T U hTU =
      finiteTateNegOneDeflation A L S U (hST.trans hTU) := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change finiteCoinvariantDeflation A L T U hTU
      (finiteCoinvariantDeflation A L S T hST x.1) =
    finiteCoinvariantDeflation A L S U (hST.trans hTU) x.1
  have h := finiteCoinvariantDeflation_comp A L S T U hST hTU
  exact CategoryTheory.congr_fun h x.1

/-- Compact degree `0` deflation composes through nested levels. -/
lemma finiteTateZeroDeflation_comp (S T U : OpenNormalSubgroup G)
    (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateZeroDeflation A L S T hST ≫
        finiteTateZeroDeflation A L T U hTU =
      finiteTateZeroDeflation A L S U (hST.trans hTU) := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change finiteTateZeroDeflation A L T U hTU
        (finiteTateZeroDeflation A L S T hST (finiteTateZeroπ A L S x)) =
      finiteTateZeroDeflation A L S U (hST.trans hTU)
        (finiteTateZeroπ A L S x)
    rw [finiteTateZeroDeflation_finiteTateZeroπ_apply,
      finiteTateZeroDeflation_finiteTateZeroπ_apply,
      finiteTateZeroDeflation_finiteTateZeroπ_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Continuous coinvariant deflation agrees with algebraic deflation under
the explicit additive comparison, checked on quotient representatives. -/
lemma finiteCoinvariantDeflation_algebraicCoinvariantsAddEquivFiniteCoinvariants
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : (Rep.coinvariantsFunctor R (G ⧸ S.toSubgroup)).obj
      (A.quotientToInvariants S.toSubgroup)) :
    finiteCoinvariantDeflation A L S T hST
        (algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x) =
      algebraicCoinvariantsAddEquivFiniteCoinvariants A L T
        (finiteNegativeDeflationCoinvariants A S.toSubgroup T.toSubgroup hST x) := by
  induction x using Representation.Coinvariants.induction_on with
  | _ representative =>
      let targetRepresentative : openSubgroupInvariants A T.toOpenSubgroup :=
        (nestedQuotientInvariantsRepIso A S.toSubgroup T.toSubgroup hST).hom
          (FiniteGroupTateCohomology.quotientNorm
            (A.quotientToInvariants S.toSubgroup)
            (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))
            (Representation.Coinvariants.mk
              ((A.quotientToInvariants S.toSubgroup).ρ.comp
                (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)).subtype)
                  representative))
      have hSource := algebraicCoinvariantsAddEquivFiniteCoinvariants_mk
        A L S representative
      have hTarget := algebraicCoinvariantsAddEquivFiniteCoinvariants_mk
        A L T targetRepresentative
      have hContinuous : finiteCoinvariantDeflation A L S T hST
          (finiteCoinvariantsMk A L S representative) =
          finiteCoinvariantsMk A L T targetRepresentative :=
        finiteCoinvariantDeflation_mk A L S T hST representative
      have hAlgebraic : finiteNegativeDeflationCoinvariants A
          S.toSubgroup T.toSubgroup hST
            (Representation.Coinvariants.mk
              (A.quotientToInvariants S.toSubgroup).ρ representative) =
          Representation.Coinvariants.mk
            (A.quotientToInvariants T.toSubgroup).ρ targetRepresentative := by
        have hraw := CategoryTheory.congr_fun
          (finiteNegativeDeflationCoinvariants_mk_hom
            A S.toSubgroup T.toSubgroup hST) representative
        change finiteNegativeDeflationCoinvariants A S.toSubgroup T.toSubgroup hST
            (Representation.Coinvariants.mk
              (A.quotientToInvariants S.toSubgroup).ρ representative) =
          Representation.Coinvariants.mk
            (A.quotientToInvariants T.toSubgroup).ρ targetRepresentative at hraw
        exact hraw
      calc
        _ = finiteCoinvariantDeflation A L S T hST
            (finiteCoinvariantsMk A L S representative) :=
          congrArg _ hSource
        _ = finiteCoinvariantsMk A L T targetRepresentative := hContinuous
        _ = algebraicCoinvariantsAddEquivFiniteCoinvariants A L T
            (Representation.Coinvariants.mk
              (A.quotientToInvariants T.toSubgroup).ρ targetRepresentative) :=
          hTarget.symm
        _ = _ := congrArg
          (algebraicCoinvariantsAddEquivFiniteCoinvariants A L T) hAlgebraic.symm

/-- The compact degree `-1` map agrees with algebraic finite deflation under
the explicit additive Tate comparisons. -/
lemma tateCohomologyNegOneAddEquivFiniteTate_finiteNegativeOneDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (G ⧸ S.toSubgroup)] [Fintype (G ⧸ T.toSubgroup)]
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)) :
    tateCohomologyNegOneAddEquivFiniteTate A L T
        (finiteNegativeOneDeflation A S.toSubgroup T.toSubgroup hST x) =
      finiteTateNegOneDeflation A L S T hST
        (tateCohomologyNegOneAddEquivFiniteTate A L S x) := by
  apply Subtype.ext
  change finiteTateNegOneι A L T
      (tateCohomologyNegOneAddEquivFiniteTate A L T
        (finiteNegativeOneDeflation A S.toSubgroup T.toSubgroup hST x)) =
    finiteTateNegOneι A L T
      (finiteTateNegOneDeflation A L S T hST
        (tateCohomologyNegOneAddEquivFiniteTate A L S x))
  rw [finiteTateNegOneι_finiteTateNegOneDeflation_apply,
    finiteTateNegOneι_tateCohomologyNegOneAddEquivFiniteTate,
    finiteTateNegOneι_tateCohomologyNegOneAddEquivFiniteTate]
  have hdef := CategoryTheory.congr_fun
    (finiteNegativeOneDeflation_comp_kernelNormIso_hom
      A S.toSubgroup T.toSubgroup hST) x
  change
    (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
      (A.quotientToInvariants T.toSubgroup)).hom
        (finiteNegativeOneDeflation A S.toSubgroup T.toSubgroup hST x) =
      finiteNegativeOneDeflationKernel A S.toSubgroup T.toSubgroup hST
        ((FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants S.toSubgroup)).hom x) at hdef
  rw [hdef]
  rw [ModuleCat.kernelIsoKer_hom_ker_subtype_apply]
  rw [ModuleCat.kernelIsoKer_hom_ker_subtype_apply]
  have hι := CategoryTheory.congr_fun
    (finiteNegativeOneDeflationKernel_ι
      A S.toSubgroup T.toSubgroup hST)
    ((FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
      (A.quotientToInvariants S.toSubgroup)).hom x)
  simp only [CategoryTheory.comp_apply] at hι
  exact (congrArg (algebraicCoinvariantsAddEquivFiniteCoinvariants A L T) hι).trans
    (finiteCoinvariantDeflation_algebraicCoinvariantsAddEquivFiniteCoinvariants
      A L S T hST _).symm

/-- The compact degree `0` map agrees with algebraic finite deflation under
the explicit additive Tate comparisons. The residual algebraic targets have
different nested subtype data, reconciled in the common total-invariants group. -/
lemma tateCohomologyZeroAddEquivFiniteTate_finiteZeroDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (G ⧸ S.toSubgroup)] [Fintype (G ⧸ T.toSubgroup)]
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (x : tateCohomology (A.quotientToInvariants S.toSubgroup) 0) :
    tateCohomologyZeroAddEquivFiniteTate A L T
        (finiteZeroDeflation A S.toSubgroup T.toSubgroup hST x) =
      finiteTateZeroDeflation A L S T hST
        (tateCohomologyZeroAddEquivFiniteTate A L S x) := by
  let nS := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S.toSubgroup)
  let nT := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants T.toSubgroup)
  let iS := FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
    (A.quotientToInvariants S.toSubgroup)
  let iT := FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
    (A.quotientToInvariants T.toSubgroup)
  have hsur : Function.Surjective (cokernel.π nS) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨y, hy⟩ := hsur (iS.hom x)
  have hx : x = iS.inv (cokernel.π nS y) := by
    calc
      x = iS.inv (iS.hom x) := (Iso.hom_inv_id_apply iS x).symm
      _ = iS.inv (cokernel.π nS y) := congrArg (fun z ↦ iS.inv z) hy.symm
  rw [hx]
  have hdef := CategoryTheory.congr_fun
    (finiteZeroDeflation_comp_cokernelNormIso_hom
      A S.toSubgroup T.toSubgroup hST)
    (iS.inv (cokernel.π nS y))
  change
    (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
      (A.quotientToInvariants T.toSubgroup)).hom
        (finiteZeroDeflation A S.toSubgroup T.toSubgroup hST
          (iS.inv (cokernel.π nS y))) =
      finiteZeroDeflationCokernel A S.toSubgroup T.toSubgroup hST
        (iS.hom (iS.inv (cokernel.π nS y))) at hdef
  rw [Iso.inv_hom_id_apply] at hdef
  have hπ := CategoryTheory.congr_fun
    (finiteZeroDeflationCokernel_π
      A S.toSubgroup T.toSubgroup hST) y
  change
    finiteZeroDeflationCokernel A S.toSubgroup T.toSubgroup hST
        (cokernel.π nS y) =
      cokernel.π nT
        ((finiteLevelTotalInvariantsEquiv
          A S.toSubgroup T.toSubgroup hST).toModuleIso.hom y) at hπ
  let φS : ↑(cokernel nS : ModuleCat R) → finiteTateZero A L S := fun z ↦
    tateCohomologyZeroAddEquivFiniteTate A L S (iS.inv z)
  let φT : ↑(cokernel nT : ModuleCat R) → finiteTateZero A L T := fun z ↦
    tateCohomologyZeroAddEquivFiniteTate A L T (iT.inv z)
  calc
    tateCohomologyZeroAddEquivFiniteTate A L T
        (finiteZeroDeflation A S.toSubgroup T.toSubgroup hST
          (iS.inv (cokernel.π nS y))) =
      φT (iT.hom (finiteZeroDeflation A S.toSubgroup T.toSubgroup hST
        (iS.inv (cokernel.π nS y)))) := by simp [φT]
    _ = φT (finiteZeroDeflationCokernel A S.toSubgroup T.toSubgroup hST
        (cokernel.π nS y)) := congrArg φT hdef
    _ = φT (cokernel.π nT
        ((finiteLevelTotalInvariantsEquiv
          A S.toSubgroup T.toSubgroup hST).toModuleIso.hom y)) :=
      congrArg φT hπ
    _ = finiteTateZeroDeflation A L S T hST (φS (cokernel.π nS y)) := by
      dsimp only [φS, φT]
      rw [tateCohomologyZeroAddEquivFiniteTate_cokernelπ]
      rw [tateCohomologyZeroAddEquivFiniteTate_cokernelπ]
      rw [finiteTateZeroDeflation_finiteTateZeroπ_apply]
      congr 1
      apply Subtype.ext
      rw [finiteNormTargetAddEquivGroup_apply_val,
        finiteNormTargetAddEquivGroup_apply_val]
      exact finiteLevelTotalInvariantsEquiv_apply_val
        A S.toSubgroup T.toSubgroup hST y

end ContinuousGroupCohomology.LevelCompact
