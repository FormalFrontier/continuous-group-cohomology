/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactBarFunctoriality
public import ContinuousGroupCohomology.FiniteDeflationTransitivity

/-!
# Continuous negative deflation at compact finite levels

For nested open normal subgroups, this file bundles finite negative deflation
below degree `-1` as a continuous morphism between the compact finite-bar
models.  The construction is the continuous finite-bar map induced by the
direct quotient homomorphism and the finite coefficient norm.

Only compact Hausdorff additive-group topologies are used.  There is no
topology on the coefficient ring and no topological-module assertion.  The
common-universe restriction is inherited from the finite-group homology API.

## References

The coefficient norm and its homology map use this library's
`FiniteNegativeDeflation` and `FiniteDeflationTransitivity`. The continuous bar
transport uses `CompactBarFunctoriality`, following mathlib's
`Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality`
by Amelia Livingston.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The direct coefficient norm underlying finite negative deflation is
continuous for the levelwise compact topologies. -/
lemma continuous_finiteNegativeDeflationCoeffDirect
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    @Continuous (A.quotientToInvariants S.toSubgroup)
      (A.quotientToInvariants T.toSubgroup)
      (L.topology S.toOpenSubgroup) (L.topology T.toOpenSubgroup)
      (finiteNegativeDeflationCoeffDirect A S.toSubgroup T.toSubgroup hST).hom := by
  let K := T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)
  let _ : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  let _ : TopologicalSpace (A.quotientToInvariants T.toSubgroup) :=
    L.topology T.toOpenSubgroup
  let _ : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  let n : A.quotientToInvariants S.toSubgroup →
      A.quotientToInvariants T.toSubgroup :=
    (finiteNegativeDeflationCoeffDirect
      A S.toSubgroup T.toSubgroup hST).hom
  let sumMap : A.quotientToInvariants S.toSubgroup →
      A.quotientToInvariants S.toSubgroup := fun x ↦
    ∑ k : K, (A.quotientToInvariants S.toSubgroup).ρ k x
  have hsum : Continuous sumMap :=
    continuous_finsetSum Finset.univ fun k _ ↦
      continuous_quotientToInvariants_action A (L := L) S k
  have hcomp :
      (inclusion A T.toOpenSubgroup S.toOpenSubgroup hST) ∘ n = sumMap := by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, inclusion_coe]
    dsimp only [n, sumMap, K]
    rw [finiteNegativeDeflationCoeffDirect_apply_val]
    simp only [Submodule.coe_sum]
  have hIncl := inclusion_isClosedEmbedding A L T.toOpenSubgroup S.toOpenSubgroup hST
  apply hIncl.isInducing.continuous_iff.mpr
  rw [hcomp]
  exact hsum

/-- Continuous finite negative deflation on the compact finite Tate model in
degree `-(n + 2)`. -/
noncomputable def finiteTateNegativeDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] (n : ℕ) :
    finiteTateNegative A L S n ⟶ finiteTateNegative A L T n := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  letI : TopologicalSpace (A.quotientToInvariants T.toSubgroup) :=
    L.topology T.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants T.toSubgroup) :=
    L.compact T.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants T.toSubgroup) :=
    L.t2 T.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants T.toSubgroup) :=
    L.topologicalAddGroup T.toOpenSubgroup
  exact (finiteTateNegativeIsoPositiveHomology A L S n).hom ≫
    CompHausAddCommGrp.FiniteBar.positiveHomologyMap
      (A.quotientToInvariants S.toSubgroup)
      (A.quotientToInvariants T.toSubgroup)
      (continuous_quotientToInvariants_action A L S)
      (continuous_quotientToInvariants_action A L T)
      (finiteDeflationGroupHom S.toSubgroup T.toSubgroup hST)
      (finiteNegativeDeflationCoeffDirect A S.toSubgroup T.toSubgroup hST)
      (continuous_finiteNegativeDeflationCoeffDirect A L S T hST) n ≫
      (finiteTateNegativeIsoPositiveHomology A L T n).inv

/-- Compact finite negative deflation is the continuous finite-bar map
transported through the canonical presentation isomorphisms. -/
lemma finiteTateNegativeDeflation_positiveHomology_apply
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (n : ℕ) (x : finiteTateNegative A L S n) :
    finiteTateNegativeDeflation A L S T hST n x =
      (finiteTateNegativeIsoPositiveHomology A L T n).inv
        (@CompHausAddCommGrp.FiniteBar.positiveHomologyMap
          R (G ⧸ S.toSubgroup) (G ⧸ T.toSubgroup) _ _ (Fintype.ofFinite _)
          _ (Fintype.ofFinite _)
          (A.quotientToInvariants S.toSubgroup)
          (A.quotientToInvariants T.toSubgroup)
          (L.topology S.toOpenSubgroup) (L.compact S.toOpenSubgroup)
          (L.t2 S.toOpenSubgroup) (L.topologicalAddGroup S.toOpenSubgroup)
          (L.topology T.toOpenSubgroup) (L.compact T.toOpenSubgroup)
          (L.t2 T.toOpenSubgroup) (L.topologicalAddGroup T.toOpenSubgroup)
          (continuous_quotientToInvariants_action A L S)
          (continuous_quotientToInvariants_action A L T)
          (finiteDeflationGroupHom S.toSubgroup T.toSubgroup hST)
          (finiteNegativeDeflationCoeffDirect A S.toSubgroup T.toSubgroup hST)
          (continuous_finiteNegativeDeflationCoeffDirect A L S T hST) n
          ((finiteTateNegativeIsoPositiveHomology A L S n).hom x)) := rfl

/-- The compact finite negative-deflation map is the algebraic finite
negative-deflation map under the finite-bar comparisons. -/
lemma groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (n : ℕ) (x : groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1)) :
    groupHomologyAddEquivFiniteTateNegative A L T n
        (finiteNegativeDeflation A S.toSubgroup T.toSubgroup hST (n + 1) x) =
      finiteTateNegativeDeflation A L S T hST n
        (groupHomologyAddEquivFiniteTateNegative A L S n x) := by
  let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
  let _ : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  let _ : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  let _ : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  let _ : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  let _ : TopologicalSpace (A.quotientToInvariants T.toSubgroup) :=
    L.topology T.toOpenSubgroup
  let _ : CompactSpace (A.quotientToInvariants T.toSubgroup) :=
    L.compact T.toOpenSubgroup
  let _ : T2Space (A.quotientToInvariants T.toSubgroup) :=
    L.t2 T.toOpenSubgroup
  let _ : IsTopologicalAddGroup (A.quotientToInvariants T.toSubgroup) :=
    L.topologicalAddGroup T.toOpenSubgroup
  rw [finiteNegativeDeflation_eq_direct_map]
  simpa only [groupHomologyAddEquivFiniteTateNegative_apply,
    finiteTateNegativeDeflation_positiveHomology_apply, Iso.inv_hom_id_apply] using
    congrArg (finiteTateNegativeIsoPositiveHomology A L T n).inv
      (CompHausAddCommGrp.FiniteBar.groupHomologyAddEquivPositive_naturality
        (A.quotientToInvariants S.toSubgroup)
        (A.quotientToInvariants T.toSubgroup)
        (continuous_quotientToInvariants_action A L S)
        (continuous_quotientToInvariants_action A L T)
        (finiteDeflationGroupHom S.toSubgroup T.toSubgroup hST)
        (finiteNegativeDeflationCoeffDirect A S.toSubgroup T.toSubgroup hST)
        (continuous_finiteNegativeDeflationCoeffDirect A L S T hST) n x)

/-- The value of compact finite negative deflation can be computed by the
algebraic deflation map and the two additive finite-bar comparisons. -/
lemma finiteTateNegativeDeflation_apply
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (n : ℕ) (x : finiteTateNegative A L S n) :
    finiteTateNegativeDeflation A L S T hST n x =
      groupHomologyAddEquivFiniteTateNegative A L T n
        (finiteNegativeDeflation A S.toSubgroup T.toSubgroup hST (n + 1)
          ((groupHomologyAddEquivFiniteTateNegative A L S n).symm x)) := by
  obtain ⟨y, rfl⟩ :=
    (groupHomologyAddEquivFiniteTateNegative A L S n).surjective x
  simpa only [AddEquiv.symm_apply_apply] using
    (groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
      A L S T hST n y).symm

/-- Compact finite negative deflation through an intermediate open normal
subgroup is direct compact finite negative deflation. -/
lemma finiteTateNegativeDeflation_comp
    (S T U : OpenNormalSubgroup G) (hST : S ≤ T) (hTU : T ≤ U)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
    [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
    (n : ℕ) :
    finiteTateNegativeDeflation A L S T hST n ≫
        finiteTateNegativeDeflation A L T U hTU n =
      finiteTateNegativeDeflation A L S U (hST.trans hTU) n := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    (groupHomologyAddEquivFiniteTateNegative A L S n).surjective x
  change
    finiteTateNegativeDeflation A L T U hTU n
        (finiteTateNegativeDeflation A L S T hST n
          (groupHomologyAddEquivFiniteTateNegative A L S n y)) =
      finiteTateNegativeDeflation A L S U (hST.trans hTU) n
        (groupHomologyAddEquivFiniteTateNegative A L S n y)
  rw [← groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    A L S T hST n y]
  rw [← groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    A L T U hTU n
      (finiteNegativeDeflation A S.toSubgroup T.toSubgroup hST (n + 1) y)]
  rw [← groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    A L S U (hST.trans hTU) n y]
  exact congrArg (groupHomologyAddEquivFiniteTateNegative A L U n)
    (CategoryTheory.congr_fun
      (finiteNegativeDeflation_comp A S.toSubgroup T.toSubgroup U.toSubgroup
        hST hTU (n + 1)) y)

/-- Compact finite negative deflation from an open normal subgroup to itself
is the identity. -/
lemma finiteTateNegativeDeflation_refl
    (S : OpenNormalSubgroup G)
    [Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] (n : ℕ) :
    finiteTateNegativeDeflation A L S S le_rfl n = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ :=
    (groupHomologyAddEquivFiniteTateNegative A L S n).surjective x
  change
    finiteTateNegativeDeflation A L S S le_rfl n
        (groupHomologyAddEquivFiniteTateNegative A L S n y) =
      groupHomologyAddEquivFiniteTateNegative A L S n y
  rw [← groupHomologyAddEquivFiniteTateNegative_finiteNegativeDeflation
    A L S S le_rfl n y]
  simpa using congrArg (groupHomologyAddEquivFiniteTateNegative A L S n)
    (CategoryTheory.congr_fun
      (finiteNegativeDeflation_refl A S.toSubgroup (n + 1)) y)

end ContinuousGroupCohomology.LevelCompact
