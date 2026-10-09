/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.ExceptionalDeflation
public import ContinuousGroupCohomology.FiniteCoinvariants

/-!
# Compact topologies on the exceptional finite Tate stages

For a level-compact coefficient representation, this file packages Tate
degrees `-1` and `0` at an open normal level as compact Hausdorff additive
commutative groups.  They are respectively the closed kernel and the quotient
by the compact, hence closed, range of the continuous norm from
finite coinvariants to total invariants.

The comparison with algebraic Tate cohomology is only an additive equivalence.
No topology on the coefficient ring, topological-module structure, or
comparison with `TopModuleCat.withModuleTopology` is asserted.
The algebraic comparison inherits the common-universe restriction of the
finite-group Tate-cohomology API.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe uR uG uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{uA} R G) (L : LevelCompact A)

/-- Tate degree `-1` at `S`, topologized as the closed kernel of the
continuous norm from finite coinvariants. -/
noncomputable abbrev finiteTateNegOne (S : OpenNormalSubgroup G) :
    CompHausAddCommGrp.{uA} :=
  CompHausAddCommGrp.kernelGroup (normFromFiniteCoinvariants A L S)

/-- Tate degree `0` at `S`, topologized as the compact Hausdorff quotient of
total invariants by the range of the continuous norm from finite
coinvariants. -/
noncomputable abbrev finiteTateZero (S : OpenNormalSubgroup G) :
    CompHausAddCommGrp.{uA} :=
  CompHausAddCommGrp.quotientRange (normFromFiniteCoinvariants A L S)

/-- The canonical continuous inclusion of compact degree `-1` into finite
coinvariants. -/
@[expose] noncomputable def finiteTateNegOneι (S : OpenNormalSubgroup G) :
    finiteTateNegOne A L S ⟶ finiteCoinvariants A (L := L) S :=
  CompHausAddCommGrp.kernelι (normFromFiniteCoinvariants A L S)

/-- The canonical continuous projection from total invariants to compact
degree `0`. -/
@[expose] noncomputable def finiteTateZeroπ (S : OpenNormalSubgroup G) :
    group A L (⊤ : OpenSubgroup G) ⟶ finiteTateZero A L S :=
  CompHausAddCommGrp.quotientRangeπ (normFromFiniteCoinvariants A L S)

@[simp]
lemma finiteTateNegOneι_apply (S : OpenNormalSubgroup G)
    (x : finiteTateNegOne A L S) : finiteTateNegOneι A L S x = x :=
  rfl

@[simp]
lemma normFromFiniteCoinvariants_finiteTateNegOneι_apply
    (S : OpenNormalSubgroup G) (x : finiteTateNegOne A L S) :
    normFromFiniteCoinvariants A L S (finiteTateNegOneι A L S x) = 0 :=
  x.2

@[simp]
lemma finiteTateZeroπ_apply (S : OpenNormalSubgroup G)
    (x : group A L (⊤ : OpenSubgroup G)) :
    finiteTateZeroπ A L S x = QuotientAddGroup.mk x :=
  rfl

@[simp]
lemma finiteTateZeroπ_normFromFiniteCoinvariants_apply
    (S : OpenNormalSubgroup G) (x : finiteCoinvariants A (L := L) S) :
    finiteTateZeroπ A L S (normFromFiniteCoinvariants A L S x) = 0 :=
  CompHausAddCommGrp.quotientRangeπ_comp_apply
    (normFromFiniteCoinvariants A L S) x

section AlgebraicComparison

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Total invariants for the residual `G / S`-action are linearly equivalent
to the invariants of the original representation under the full open
subgroup.  The map forgets only redundant nested subtype data. -/
@[expose] def finiteNormTargetEquiv (S : OpenNormalSubgroup G) :
    Representation.invariants (A.quotientToInvariants S.toSubgroup).ρ ≃ₗ[R]
      openSubgroupInvariants A (⊤ : OpenSubgroup G) where
  toFun x := ⟨x.1.1, fun g ↦ by
    exact congrArg Subtype.val
      (x.2 (QuotientGroup.mk' S.toSubgroup (g : G)))⟩
  invFun x :=
    ⟨⟨x.1, fun s ↦ x.2 ⟨s.1, trivial⟩⟩,
      fun q ↦ QuotientGroup.induction_on q fun g ↦ by
        apply Subtype.ext
        exact x.2 ⟨g, trivial⟩⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
lemma finiteNormTargetEquiv_apply_val (S : OpenNormalSubgroup G)
    (x : Representation.invariants
      (A.quotientToInvariants S.toSubgroup).ρ) :
    (finiteNormTargetEquiv A S x : A) = x.1.1 :=
  rfl

/-- The carrier of the compact finite coinvariants is the algebraic
coinvariant quotient.  This additive equivalence records that identification
without identifying any topology. -/
def algebraicCoinvariantsAddEquivFiniteCoinvariants
    (S : OpenNormalSubgroup G) :
    (Rep.coinvariantsFunctor R (G ⧸ S.toSubgroup)).obj
        (A.quotientToInvariants S.toSubgroup) ≃+
      finiteCoinvariants A (L := L) S := by
  change Representation.Coinvariants
      (A.quotientToInvariants S.toSubgroup).ρ ≃+
    Representation.Coinvariants
      (A.quotientToInvariants S.toSubgroup).ρ
  exact AddEquiv.refl _

/-- The additive comparison of algebraic and compact coinvariants preserves
the canonical quotient representative. -/
@[simp] lemma algebraicCoinvariantsAddEquivFiniteCoinvariants_mk
    (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    algebraicCoinvariantsAddEquivFiniteCoinvariants A L S
        (Representation.Coinvariants.mk
          (A.quotientToInvariants S.toSubgroup).ρ x) =
      finiteCoinvariantsMk A L S x := by
  rfl

/-- The compact group at an open level has the corresponding invariant submodule
as its underlying additive group. -/
def openSubgroupInvariantsAddEquivGroup (U : OpenSubgroup G) :
    openSubgroupInvariants A U ≃+ group A L U := by
  change openSubgroupInvariants A U ≃+ openSubgroupInvariants A U
  exact AddEquiv.refl _

/-- The additive target equivalence combining residual total invariants with
the underlying additive group at the full open subgroup. -/
def finiteNormTargetAddEquivGroup (S : OpenNormalSubgroup G) :
    (Rep.invariantsFunctor R (G ⧸ S.toSubgroup)).obj
        (A.quotientToInvariants S.toSubgroup) ≃+
      group A L (⊤ : OpenSubgroup G) := by
  change Representation.invariants
      (A.quotientToInvariants S.toSubgroup).ρ ≃+
    group A L (⊤ : OpenSubgroup G)
  exact (finiteNormTargetEquiv A S).toAddEquiv.trans
    (openSubgroupInvariantsAddEquivGroup A L ⊤)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The additive comparison to common total invariants preserves the underlying
coefficient vector, independently of the residual quotient level. -/
@[simp] lemma finiteNormTargetAddEquivGroup_apply_val
    (S : OpenNormalSubgroup G)
    (x : (Rep.invariantsFunctor R (G ⧸ S.toSubgroup)).obj
      (A.quotientToInvariants S.toSubgroup)) :
    ((finiteNormTargetAddEquivGroup A L S x).1 : A) = x.1.1 := by
  change (finiteNormTargetEquiv A S x : A) = x.1.1
  exact finiteNormTargetEquiv_apply_val A S x

/-- After the explicit target equivalence, the algebraic finite-group norm is
the underlying additive map of the continuous norm. -/
lemma finiteNormTargetEquiv_normFromCoinvariants
    (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)]
    (x : (Rep.coinvariantsFunctor R (G ⧸ S.toSubgroup)).obj
      (A.quotientToInvariants S.toSubgroup)) :
    openSubgroupInvariantsAddEquivGroup A L ⊤
        (finiteNormTargetEquiv A S
          ((FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup)).hom x)) =
      normFromFiniteCoinvariants A L S
        (algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x) := by
  induction x using Representation.Coinvariants.induction_on with
  | _ x =>
      apply (openSubgroupInvariantsAddEquivGroup A L ⊤).symm.injective
      simp only [AddEquiv.symm_apply_apply]
      apply Subtype.ext
      change
        ((Representation.norm
          (A.quotientToInvariants S.toSubgroup).ρ x :
            A.quotientToInvariants S.toSubgroup) : A) =
          (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top x : A)
      exact (relativeNorm_eq_quotientToInvariants_norm A S x).symm

/-- The target equivalence sends the algebraic norm range exactly to the
range of the continuous norm. -/
private lemma finiteNormRange_map (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)] :
    AddSubgroup.map (finiteNormTargetAddEquivGroup A L S).toAddMonoidHom
        (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S.toSubgroup)).hom.range.toAddSubgroup =
      (normFromFiniteCoinvariants A L S).hom.range := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x, ?_⟩
    exact (finiteNormTargetEquiv_normFromCoinvariants A L S x).symm
  · rintro ⟨x, rfl⟩
    let x' := (algebraicCoinvariantsAddEquivFiniteCoinvariants A L S).symm x
    refine ⟨(FiniteGroupTateCohomology.normFromCoinvariants
        (A.quotientToInvariants S.toSubgroup)).hom x', ⟨x', rfl⟩, ?_⟩
    change openSubgroupInvariantsAddEquivGroup A L ⊤
        (finiteNormTargetEquiv A S
          ((FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup)).hom x')) =
        normFromFiniteCoinvariants A L S x
    rw [finiteNormTargetEquiv_normFromCoinvariants A L S]
    simp only [x', AddEquiv.apply_symm_apply]

/-- The concrete kernel of the algebraic norm is additively equivalent to the
closed kernel carrying the compact topology. -/
private def finiteNormKernelAddEquiv (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)] :
    (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S.toSubgroup)).hom.ker ≃+
      finiteTateNegOne A L S where
  toFun x :=
    ⟨algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x.1, by
    change normFromFiniteCoinvariants A L S
      (algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x.1) = 0
    rw [← finiteNormTargetEquiv_normFromCoinvariants A L S x.1]
    have hx := x.2
    change (FiniteGroupTateCohomology.normFromCoinvariants
      (A.quotientToInvariants S.toSubgroup)).hom x.1 = 0 at hx
    rw [hx]
    exact map_zero _⟩
  invFun x :=
    ⟨(algebraicCoinvariantsAddEquivFiniteCoinvariants A L S).symm x.1, by
    apply (finiteNormTargetEquiv A S).injective
    apply (openSubgroupInvariantsAddEquivGroup A L ⊤).injective
    rw [finiteNormTargetEquiv_normFromCoinvariants A L S]
    have hx := x.2
    change normFromFiniteCoinvariants A L S x.1 = 0 at hx
    simp only [AddEquiv.apply_symm_apply, hx, map_zero]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

/-- Algebraic Tate cohomology in degree `-1` is additively equivalent to the
compact closed-kernel presentation.  This is an explicit additive
equivalence, not a definitional equality or a topological-module
identification. -/
def tateCohomologyNegOneAddEquivFiniteTate
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)] :
    tateCohomology (A.quotientToInvariants S.toSubgroup) (-1) ≃+
      finiteTateNegOne A L S := by
  exact
    ((FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants S.toSubgroup) ≪≫
        ModuleCat.kernelIsoKer
          (FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup))).toLinearEquiv.toAddEquiv).trans
      (finiteNormKernelAddEquiv A L S)

/-- The algebraic degree `-1` comparison followed by compact-kernel inclusion
is the algebraic kernel inclusion followed by the coinvariant comparison.
This public equation avoids unfolding the private concrete-kernel comparison
across module boundaries. -/
@[simp] lemma finiteTateNegOneι_tateCohomologyNegOneAddEquivFiniteTate
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)]
    (x : tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)) :
    finiteTateNegOneι A L S (tateCohomologyNegOneAddEquivFiniteTate A L S x) =
      algebraicCoinvariantsAddEquivFiniteCoinvariants A L S
        (((ModuleCat.kernelIsoKer
          (FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup))).hom
          ((FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
            (A.quotientToInvariants S.toSubgroup)).hom x)).1) := by
  rfl

/-- Algebraic Tate cohomology in degree `0` is additively equivalent to the
compact quotient-by-norm-range presentation.  This is an explicit additive
equivalence, not a definitional equality or a topological-module
identification. -/
def tateCohomologyZeroAddEquivFiniteTate
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)] :
    tateCohomology (A.quotientToInvariants S.toSubgroup) 0 ≃+
      finiteTateZero A L S := by
  let f := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S.toSubgroup)
  exact
    ((FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants S.toSubgroup) ≪≫
        ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.toAddEquiv).trans
      (QuotientAddGroup.congr f.hom.range.toAddSubgroup
        (normFromFiniteCoinvariants A L S).hom.range
        (finiteNormTargetAddEquivGroup A L S)
        (finiteNormRange_map A L S))

/-- On a cokernel representative, the degree-zero algebraic comparison is the
canonical compact quotient projection after the explicit target
identification. -/
@[simp]
lemma tateCohomologyZeroAddEquivFiniteTate_cokernelπ
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)]
    (x : (Rep.invariantsFunctor R (G ⧸ S.toSubgroup)).obj
      (A.quotientToInvariants S.toSubgroup)) :
    tateCohomologyZeroAddEquivFiniteTate A L S
        ((FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants S.toSubgroup)).inv
          (cokernel.π (FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup)) x)) =
      finiteTateZeroπ A L S (finiteNormTargetAddEquivGroup A L S x) := by
  let f := FiniteGroupTateCohomology.normFromCoinvariants
    (A.quotientToInvariants S.toSubgroup)
  change
    (QuotientAddGroup.congr f.hom.range.toAddSubgroup
      (normFromFiniteCoinvariants A L S).hom.range
      (finiteNormTargetAddEquivGroup A L S)
      (finiteNormRange_map A L S))
        ((ModuleCat.cokernelIsoRangeQuotient f).hom
          ((FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
            (A.quotientToInvariants S.toSubgroup)).hom
            ((FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
              (A.quotientToInvariants S.toSubgroup)).inv
              (cokernel.π f x)))) =
      QuotientAddGroup.mk (finiteNormTargetAddEquivGroup A L S x)
  rw [Iso.inv_hom_id_apply]
  rw [ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply]
  rfl

end AlgebraicComparison

end ContinuousGroupCohomology.LevelCompact
