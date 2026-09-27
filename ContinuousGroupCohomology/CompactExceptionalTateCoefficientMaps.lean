/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.LevelCompactFunctoriality
public import ContinuousGroupCohomology.ExceptionalTateDeflationTopology

/-!
# Coefficient maps on compact exceptional Tate stages

For morphisms of level-compact representations, continuous maps on the actual
compact finite coinvariants and the compact Tate groups in degrees `-1` and `0`.
The topology is chosen separately on every open-subgroup invariant module;
neither the ambient coefficient module nor the ring is given a topology.
Naturality of the relative norm and of exceptional finite deflation is proved
from the representation morphism and the published representative formulas.

Native adaptation of Beacon's historical `CompactTateCoefficientMaps` by
`hive-request-d61b09970e5688d0b1e0da08ec7719208350ad23`
(`b087c1ae-8092-47fc-ba95-7e8a338a0201`).
-/

public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable {A B : LevelCompactRep.{u, u, u} R G}

/-- The continuous additive map on one invariant level induced by a
level-compact coefficient morphism. -/
@[expose] def groupMap (f : A ⟶ B) (U : OpenSubgroup G) :
    LevelCompact.group A.rep A.levelCompact U ⟶
      LevelCompact.group B.rep B.levelCompact U := by
  apply ConcreteCategory.ofHom
  exact
    { toAddMonoidHom := (mapInvariants f U).toAddMonoidHom
      continuous_toFun := continuous_mapInvariants f U }

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
lemma groupMap_apply (f : A ⟶ B) (U : OpenSubgroup G)
    (x : openSubgroupInvariants A.rep U) :
    groupMap f U x = mapInvariants f U x :=
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
lemma groupMap_id (A : LevelCompactRep.{u, u, u} R G)
    (U : OpenSubgroup G) :
    groupMap (𝟙 A) U = 𝟙 (LevelCompact.group A.rep A.levelCompact U) := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp, reassoc]
lemma groupMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (U : OpenSubgroup G) :
    groupMap (f ≫ g) U = groupMap f U ≫ groupMap g U := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  rfl

/-- An equivariant morphism commutes with relative norms, written on
invariant-level representatives. -/
lemma mapInvariants_relativeNorm (f : A ⟶ B) (U V : OpenSubgroup G)
    (h : V ≤ U) (x : openSubgroupInvariants A.rep V) :
    mapInvariants f U (LevelCompact.relativeNorm A.rep U V h x) =
      LevelCompact.relativeNorm B.rep U V h (mapInvariants f V x) := by
  let transversal : (LevelCompact.relativeNormSubgroup U V).toSubgroup.RightTransversal :=
    default
  let _ : (LevelCompact.relativeNormSubgroup U V).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(transversal : Set U) := transversal.2.finite_right.fintype
  rw [LevelCompact.relativeNorm_eq_withTransversal A.rep U V h transversal,
    LevelCompact.relativeNorm_eq_withTransversal B.rep U V h transversal]
  apply Subtype.ext
  simp only [mapInvariants_coe,
    LevelCompact.relativeNormWithTransversal_coe, map_sum]
  apply Finset.sum_congr rfl
  intro representative _
  exact Rep.hom_comm_apply f.hom _ _

/-- The continuous coefficient map on the actual compact coinvariants of
`G/S`. This reuses the finite-representation coinvariant map, with the
specified levelwise topologies and their residual actions. -/
@[expose] def finiteCoinvariantsMap (f : A ⟶ B) (S : OpenNormalSubgroup G) :
    LevelCompact.finiteCoinvariants A.rep A.levelCompact S ⟶
      LevelCompact.finiteCoinvariants B.rep B.levelCompact S := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.rep.quotientToInvariants S.toSubgroup) :=
    A.levelCompact.topology S.toOpenSubgroup
  letI : CompactSpace (A.rep.quotientToInvariants S.toSubgroup) :=
    A.levelCompact.compact S.toOpenSubgroup
  letI : T2Space (A.rep.quotientToInvariants S.toSubgroup) :=
    A.levelCompact.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.rep.quotientToInvariants S.toSubgroup) :=
    A.levelCompact.topologicalAddGroup S.toOpenSubgroup
  letI : TopologicalSpace (B.rep.quotientToInvariants S.toSubgroup) :=
    B.levelCompact.topology S.toOpenSubgroup
  letI : CompactSpace (B.rep.quotientToInvariants S.toSubgroup) :=
    B.levelCompact.compact S.toOpenSubgroup
  letI : T2Space (B.rep.quotientToInvariants S.toSubgroup) :=
    B.levelCompact.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (B.rep.quotientToInvariants S.toSubgroup) :=
    B.levelCompact.topologicalAddGroup S.toOpenSubgroup
  exact ContinuousGroupCohomology.finiteCoinvariantsMap
    (A.rep.quotientToInvariants S.toSubgroup).ρ
    (B.rep.quotientToInvariants S.toSubgroup).ρ
    (LevelCompact.continuous_quotientToInvariants_action A.rep A.levelCompact S)
    (LevelCompact.continuous_quotientToInvariants_action B.rep B.levelCompact S)
    ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map f.hom).hom
    (continuous_mapInvariants f S.toOpenSubgroup)

@[simp]
lemma finiteCoinvariantsMap_mk (f : A ⟶ B) (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A.rep S.toOpenSubgroup) :
    finiteCoinvariantsMap f S
        (Representation.Coinvariants.mk
          (A.rep.quotientToInvariants S.toSubgroup).ρ x) =
      Representation.Coinvariants.mk
        (B.rep.quotientToInvariants S.toSubgroup).ρ
        (mapInvariants f S.toOpenSubgroup x) := by
  rfl

@[simp]
lemma finiteCoinvariantsMap_id (A : LevelCompactRep.{u, u, u} R G)
    (S : OpenNormalSubgroup G) :
    finiteCoinvariantsMap (𝟙 A) S =
      𝟙 (LevelCompact.finiteCoinvariants A.rep A.levelCompact S) := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | _ x => rfl

@[simp, reassoc]
lemma finiteCoinvariantsMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G) :
    finiteCoinvariantsMap (f ≫ g) S =
      finiteCoinvariantsMap f S ≫ finiteCoinvariantsMap g S := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | _ x => rfl

/-- The coefficient square for the actual continuous norm out of compact
finite coinvariants. Its proof is the relative-norm finite-sum computation. -/
lemma normFromFiniteCoinvariants_naturality (f : A ⟶ B)
    (S : OpenNormalSubgroup G)
    (x : LevelCompact.finiteCoinvariants A.rep A.levelCompact S) :
    LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S
        (finiteCoinvariantsMap f S x) =
      groupMap f (⊤ : OpenSubgroup G)
        (LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S x) := by
  induction x using Representation.Coinvariants.induction_on with
  | _ x =>
      change LevelCompact.relativeNorm B.rep (⊤ : OpenSubgroup G)
          S.toOpenSubgroup le_top (mapInvariants f S.toOpenSubgroup x) =
        mapInvariants f (⊤ : OpenSubgroup G)
          (LevelCompact.relativeNorm A.rep (⊤ : OpenSubgroup G)
            S.toOpenSubgroup le_top x)
      exact (mapInvariants_relativeNorm f (⊤ : OpenSubgroup G)
        S.toOpenSubgroup le_top x).symm

/-- The continuous norm square as an equality of compact-group morphisms. -/
@[reassoc]
lemma normFromFiniteCoinvariants_naturality_hom (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    finiteCoinvariantsMap f S ≫
        LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S =
      LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S ≫
        groupMap f (⊤ : OpenSubgroup G) := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  exact normFromFiniteCoinvariants_naturality f S x

/-- The continuous coefficient map on compact Tate degree `-1`. -/
@[expose] def finiteTateNegOneMap (f : A ⟶ B) (S : OpenNormalSubgroup G) :
    LevelCompact.finiteTateNegOne A.rep A.levelCompact S ⟶
      LevelCompact.finiteTateNegOne B.rep B.levelCompact S :=
  CompHausAddCommGrp.kernelMap
    (finiteCoinvariantsMap f S) (groupMap f (⊤ : OpenSubgroup G))
    (LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S)
    (LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S)
    (normFromFiniteCoinvariants_naturality f S)

/-- The continuous coefficient map on compact Tate degree `0`. -/
@[expose] def finiteTateZeroMap (f : A ⟶ B) (S : OpenNormalSubgroup G) :
    LevelCompact.finiteTateZero A.rep A.levelCompact S ⟶
      LevelCompact.finiteTateZero B.rep B.levelCompact S :=
  CompHausAddCommGrp.quotientRangeMap
    (finiteCoinvariantsMap f S) (groupMap f (⊤ : OpenSubgroup G))
    (LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S)
    (LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S)
    (normFromFiniteCoinvariants_naturality f S)

/-- Coefficient maps preserve the canonical compact kernel inclusion. -/
@[simp]
lemma finiteTateNegOneι_finiteTateNegOneMap_apply (f : A ⟶ B)
    (S : OpenNormalSubgroup G)
    (x : LevelCompact.finiteTateNegOne A.rep A.levelCompact S) :
    LevelCompact.finiteTateNegOneι B.rep B.levelCompact S
        (finiteTateNegOneMap f S x) =
      finiteCoinvariantsMap f S
        (LevelCompact.finiteTateNegOneι A.rep A.levelCompact S x) :=
  rfl

/-- Coefficient maps preserve the canonical compact quotient projection. -/
@[simp]
lemma finiteTateZeroMap_finiteTateZeroπ_apply (f : A ⟶ B)
    (S : OpenNormalSubgroup G)
    (x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)) :
    finiteTateZeroMap f S (LevelCompact.finiteTateZeroπ A.rep A.levelCompact S x) =
      LevelCompact.finiteTateZeroπ B.rep B.levelCompact S
        (groupMap f (⊤ : OpenSubgroup G) x) :=
  rfl

@[simp]
lemma finiteTateNegOneMap_id (A : LevelCompactRep.{u, u, u} R G)
    (S : OpenNormalSubgroup G) :
    finiteTateNegOneMap (𝟙 A) S =
      𝟙 (LevelCompact.finiteTateNegOne A.rep A.levelCompact S) := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change finiteCoinvariantsMap (𝟙 A) S x.1 = x.1
  rw [finiteCoinvariantsMap_id]
  rfl

@[simp, reassoc]
lemma finiteTateNegOneMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G) :
    finiteTateNegOneMap (f ≫ g) S =
      finiteTateNegOneMap f S ≫ finiteTateNegOneMap g S := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change finiteCoinvariantsMap (f ≫ g) S x.1 =
    finiteCoinvariantsMap g S (finiteCoinvariantsMap f S x.1)
  rw [finiteCoinvariantsMap_comp]
  rfl

@[simp]
lemma finiteTateZeroMap_id (A : LevelCompactRep.{u, u, u} R G)
    (S : OpenNormalSubgroup G) :
    finiteTateZeroMap (𝟙 A) S =
      𝟙 (LevelCompact.finiteTateZero A.rep A.levelCompact S) := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ x => rfl

@[simp, reassoc]
lemma finiteTateZeroMap_comp {C : LevelCompactRep.{u, u, u} R G}
    (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G) :
    finiteTateZeroMap (f ≫ g) S =
      finiteTateZeroMap f S ≫ finiteTateZeroMap g S := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ x => rfl

/-- Continuous coefficient maps commute with finite coinvariant deflation,
on the native quotient topologies. -/
lemma finiteCoinvariantsMap_deflation (f : A ⟶ B)
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteCoinvariantsMap f S ≫
        LevelCompact.finiteCoinvariantDeflation
          B.rep B.levelCompact S T hST =
      LevelCompact.finiteCoinvariantDeflation
          A.rep A.levelCompact S T hST ≫
        finiteCoinvariantsMap f T := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using Representation.Coinvariants.induction_on with
  | _ x =>
    change LevelCompact.finiteCoinvariantDeflation B.rep B.levelCompact S T hST
        (finiteCoinvariantsMap f S (LevelCompact.finiteCoinvariantsMk
          A.rep A.levelCompact S x)) =
      finiteCoinvariantsMap f T
        (LevelCompact.finiteCoinvariantDeflation A.rep A.levelCompact S T hST
          (LevelCompact.finiteCoinvariantsMk A.rep A.levelCompact S x))
    rw [LevelCompact.finiteCoinvariantsMk_apply,
      finiteCoinvariantsMap_mk]
    change LevelCompact.finiteCoinvariantDeflation B.rep B.levelCompact S T hST
        (LevelCompact.finiteCoinvariantsMk B.rep B.levelCompact S
          (mapInvariants f S.toOpenSubgroup x)) =
      finiteCoinvariantsMap f T
        (LevelCompact.finiteCoinvariantDeflation A.rep A.levelCompact S T hST
          (LevelCompact.finiteCoinvariantsMk A.rep A.levelCompact S x))
    rw [LevelCompact.finiteCoinvariantDeflation_mk B.rep B.levelCompact S T hST,
      LevelCompact.finiteCoinvariantDeflation_mk A.rep A.levelCompact S T hST]
    simp only [LevelCompact.finiteCoinvariantsMk_apply]
    change Representation.Coinvariants.mk
        (B.rep.quotientToInvariants T.toSubgroup).ρ _ =
      Representation.Coinvariants.mk
        (B.rep.quotientToInvariants T.toSubgroup).ρ _
    congr 1
    let K := T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)
    let fS := (Rep.quotientToInvariantsFunctor R S.toSubgroup).map f.hom
    let normA := FiniteGroupTateCohomology.quotientNorm
      (A.rep.quotientToInvariants S.toSubgroup) K
    let normB := FiniteGroupTateCohomology.quotientNorm
      (B.rep.quotientToInvariants S.toSubgroup) K
    let witnessA := Representation.Coinvariants.mk
      ((A.rep.quotientToInvariants S.toSubgroup).ρ.comp K.subtype) x
    have hnorm :
        normB (Representation.Coinvariants.mk
          ((B.rep.quotientToInvariants S.toSubgroup).ρ.comp K.subtype)
          (mapInvariants f S.toOpenSubgroup x)) =
          ((Rep.quotientToInvariantsFunctor R K).map fS).hom (normA witnessA) := by
      exact (CategoryTheory.congr_fun
        (FiniteGroupTateCohomology.quotientNorm_naturality
          (A.rep.quotientToInvariants S.toSubgroup) K fS) witnessA).symm
    have hnested :
        (nestedQuotientInvariantsRepIso B.rep S.toSubgroup T.toSubgroup hST).hom
          (((Rep.quotientToInvariantsFunctor R K).map fS).hom (normA witnessA)) =
          ((Rep.quotientToInvariantsFunctor R T.toSubgroup).map f.hom).hom
            ((nestedQuotientInvariantsRepIso A.rep S.toSubgroup T.toSubgroup hST).hom
              (normA witnessA)) := by
      exact CategoryTheory.congr_fun
        (nestedQuotientInvariantsRepIso_naturality f.hom
          S.toSubgroup T.toSubgroup hST) (normA witnessA)
    exact (congrArg
      (nestedQuotientInvariantsRepIso B.rep S.toSubgroup T.toSubgroup hST).hom
      hnorm).trans hnested

/-- The compact degree `-1` coefficient and deflation square. -/
@[reassoc]
lemma finiteTateNegOneMap_deflation (f : A ⟶ B)
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateNegOneMap f S ≫
        LevelCompact.finiteTateNegOneDeflation B.rep B.levelCompact S T hST =
      LevelCompact.finiteTateNegOneDeflation A.rep A.levelCompact S T hST ≫
        finiteTateNegOneMap f T := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change
    LevelCompact.finiteCoinvariantDeflation B.rep B.levelCompact S T hST
        (finiteCoinvariantsMap f S x.1) =
      finiteCoinvariantsMap f T
        (LevelCompact.finiteCoinvariantDeflation A.rep A.levelCompact S T hST x.1)
  exact CategoryTheory.congr_fun (finiteCoinvariantsMap_deflation f S T hST) x.1

/-- The compact degree `0` coefficient and deflation square. -/
@[reassoc]
lemma finiteTateZeroMap_deflation (f : A ⟶ B)
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    finiteTateZeroMap f S ≫
        LevelCompact.finiteTateZeroDeflation B.rep B.levelCompact S T hST =
      LevelCompact.finiteTateZeroDeflation A.rep A.levelCompact S T hST ≫
        finiteTateZeroMap f T := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ x => rfl

end ContinuousGroupCohomology.LevelCompactRep
