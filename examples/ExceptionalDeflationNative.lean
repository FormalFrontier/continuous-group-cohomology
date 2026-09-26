/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ExceptionalDeflation
import Mathlib.Data.ZMod.Basic

/-!
# Native client of exceptional-degree finite deflation

The named proofs use only the public exceptional-deflation leaf. They test the
coinvariant generator formula, the norm square, the induced kernel and cokernel
maps, the exceptional Tate comparisons, and coefficient naturality at every
layer. The concrete bottom/top quotient of a two-element group supplies finite
instances and allows arbitrary morphisms between distinct coefficient
representations. These results do not compute Tate groups or assert topological
exactness, transitivity, or mixed-universe generality.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace ExceptionalDeflationNativeClient

universe u

variable {R G : Type u} [CommRing R] [Group G]

theorem coinvariant_generator (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Rep.coinvariantsMk R (G ⧸ S)).app (A.quotientToInvariants S) ≫
        finiteNegativeDeflationCoinvariants A S T hST =
      (Rep.toCoinvariantsMkQ (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S))).toModuleCatHom ≫
        (FiniteGroupTateCohomology.quotientNorm
          (A.quotientToInvariants S)
          (T.map (QuotientGroup.mk' S))).toModuleCatHom ≫
        (nestedQuotientInvariantsRepIso A S T hST).hom.toModuleCatHom ≫
        (Rep.coinvariantsMk R (G ⧸ T)).app (A.quotientToInvariants T) :=
  finiteNegativeDeflationCoinvariants_mk_hom A S T hST

theorem total_invariants (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    (x : Representation.invariants (A.quotientToInvariants S).ρ) :
    (finiteLevelTotalInvariantsEquiv A S T hST x).1.1 = x.1.1 :=
  finiteLevelTotalInvariantsEquiv_apply_val A S T hST x

theorem norm_square (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeDeflationCoinvariants A S T hST ≫
        FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants T) =
      FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S) ≫
        (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom :=
  finiteNegativeDeflationCoinvariants_norm A S T hST

theorem kernel_inclusion (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflationKernel A S T hST ≫
        kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants T)) =
      kernel.ι (FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants S)) ≫
        finiteNegativeDeflationCoinvariants A S T hST :=
  finiteNegativeOneDeflationKernel_ι A S T hST

theorem cokernel_projection (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    type_of% (finiteZeroDeflationCokernel_π A S T hST) :=
  finiteZeroDeflationCokernel_π A S T hST

theorem negative_one_comparison (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteNegativeOneDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants T)).hom =
      (FiniteGroupTateCohomology.tateCohomologyNegOneIsoKernelNorm
          (A.quotientToInvariants S)).hom ≫
        finiteNegativeOneDeflationKernel A S T hST :=
  finiteNegativeOneDeflation_comp_kernelNormIso_hom A S T hST

theorem zero_comparison (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    finiteZeroDeflation A S T hST ≫
        (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants T)).hom =
      (FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants S)).hom ≫
        finiteZeroDeflationCokernel A S T hST :=
  finiteZeroDeflation_comp_cokernelNormIso_hom A S T hST

theorem coinvariant_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (Rep.coinvariantsFunctor R (G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeDeflationCoinvariants B S T hST =
    finiteNegativeDeflationCoinvariants A S T hST ≫
      (Rep.coinvariantsFunctor R (G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteNegativeDeflationCoinvariants_naturality f S T hST

theorem invariant_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) :
    (Rep.invariantsFunctor R (G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      (finiteLevelTotalInvariantsEquiv B S T hST).toModuleIso.hom =
    (finiteLevelTotalInvariantsEquiv A S T hST).toModuleIso.hom ≫
      (Rep.invariantsFunctor R (G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteLevelTotalInvariantsEquiv_naturality f S T hST

theorem kernel_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (FiniteGroupTateCohomology.normKernelFunctor
        (R := R) (G := G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeOneDeflationKernel B S T hST =
    finiteNegativeOneDeflationKernel A S T hST ≫
      (FiniteGroupTateCohomology.normKernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteNegativeOneDeflationKernel_naturality f S T hST

theorem cokernel_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ S)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteZeroDeflationCokernel B S T hST =
    finiteZeroDeflationCokernel A S T hST ≫
      (FiniteGroupTateCohomology.normCokernelFunctor
        (R := R) (G := G ⧸ T)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteZeroDeflationCokernel_naturality f S T hST

theorem negative_one_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (tateCohomologyFunctor (R := R) (G := G ⧸ S) (-1)).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeOneDeflation B S T hST =
    finiteNegativeOneDeflation A S T hST ≫
      (tateCohomologyFunctor (R := R) (G := G ⧸ T) (-1)).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteNegativeOneDeflation_naturality f S T hST

theorem zero_coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (G ⧸ S)] [Fintype (G ⧸ T)]
    [Fintype (T.map (QuotientGroup.mk' S))] :
    (tateCohomologyFunctor (R := R) (G := G ⧸ S) 0).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteZeroDeflation B S T hST =
    finiteZeroDeflation A S T hST ≫
      (tateCohomologyFunctor (R := R) (G := G ⧸ T) 0).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteZeroDeflation_naturality f S T hST

local notation "G₂" => Multiplicative (ZMod 2)

theorem bottom_lt_top : (⊥ : Subgroup G₂) < ⊤ := bot_lt_top

noncomputable local instance : Fintype (G₂ ⧸ (⊥ : Subgroup G₂)) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (G₂ ⧸ (⊤ : Subgroup G₂)) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype
    ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) :=
  Fintype.ofFinite _

def doubleCoefficient : Rep.trivial ℤ G₂ ℤ ⟶ Rep.trivial ℤ G₂ ℤ :=
  (2 : ℤ) • 𝟙 _

theorem doubleCoefficient_ne_id :
    doubleCoefficient ≠ (𝟙 (Rep.trivial ℤ G₂ ℤ)) := by
  intro h
  have h1 := congrArg (fun f : Rep.trivial ℤ G₂ ℤ ⟶ Rep.trivial ℤ G₂ ℤ =>
    f.hom (1 : ℤ)) h
  have hne : (2 : ℤ) ≠ 1 := by decide
  apply hne
  exact h1

theorem concrete_norm_square (A : Rep.{0} ℤ G₂) :
    finiteNegativeDeflationCoinvariants A ⊥ ⊤ bot_le ≫
        FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants ⊤) =
      FiniteGroupTateCohomology.normFromCoinvariants
          (A.quotientToInvariants ⊥) ≫
        (finiteLevelTotalInvariantsEquiv A ⊥ ⊤ bot_le).toModuleIso.hom :=
  norm_square A ⊥ ⊤ bot_le

theorem concrete_negative_one_naturality
    {A B : Rep.{0} ℤ G₂} (f : A ⟶ B) :
    (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊥ : Subgroup G₂)) (-1)).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊥ : Subgroup G₂)).map f) ≫
      finiteNegativeOneDeflation B ⊥ ⊤ bot_le =
    finiteNegativeOneDeflation A ⊥ ⊤ bot_le ≫
      (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊤ : Subgroup G₂)) (-1)).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊤ : Subgroup G₂)).map f) :=
  negative_one_coefficient_naturality f ⊥ ⊤ bot_le

theorem concrete_zero_naturality
    {A B : Rep.{0} ℤ G₂} (f : A ⟶ B) :
    (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊥ : Subgroup G₂)) 0).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊥ : Subgroup G₂)).map f) ≫
      finiteZeroDeflation B ⊥ ⊤ bot_le =
    finiteZeroDeflation A ⊥ ⊤ bot_le ≫
      (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊤ : Subgroup G₂)) 0).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊤ : Subgroup G₂)).map f) :=
  zero_coefficient_naturality f ⊥ ⊤ bot_le

theorem concrete_negative_one_double_naturality :
    (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊥ : Subgroup G₂)) (-1)).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊥ : Subgroup G₂)).map doubleCoefficient) ≫
      finiteNegativeOneDeflation (Rep.trivial ℤ G₂ ℤ) ⊥ ⊤ bot_le =
    finiteNegativeOneDeflation (Rep.trivial ℤ G₂ ℤ) ⊥ ⊤ bot_le ≫
      (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊤ : Subgroup G₂)) (-1)).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊤ : Subgroup G₂)).map doubleCoefficient) :=
  concrete_negative_one_naturality doubleCoefficient

theorem concrete_zero_double_naturality :
    (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊥ : Subgroup G₂)) 0).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊥ : Subgroup G₂)).map doubleCoefficient) ≫
      finiteZeroDeflation (Rep.trivial ℤ G₂ ℤ) ⊥ ⊤ bot_le =
    finiteZeroDeflation (Rep.trivial ℤ G₂ ℤ) ⊥ ⊤ bot_le ≫
      (tateCohomologyFunctor (R := ℤ) (G := G₂ ⧸ (⊤ : Subgroup G₂)) 0).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊤ : Subgroup G₂)).map doubleCoefficient) :=
  concrete_zero_naturality doubleCoefficient

end ExceptionalDeflationNativeClient
