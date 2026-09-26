/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteNegativeDeflation
import Mathlib.Data.ZMod.Basic

/-!
# Native client of finite negative deflation

These named examples use only the public finite-negative leaf. The general
transport, factorization and coefficient naturality statements are tested in
the common universe required by group homology. The concrete quotient of the
two-element group is nontrivial; degrees zero and one are ordinary homological
degrees. Only positive homological degrees model Tate degrees below `-1`.
Neither an exceptional-degree kernel nor transitivity or topological exactness
is asserted here.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace FiniteNegativeNativeClient

universe u

variable {R G : Type u} [CommRing R] [Group G]

theorem transport_component (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) :
    (nestedQuotientInvariantsHomologyNatTrans S T hST n).app A =
      groupHomology.map
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom
        (nestedQuotientInvariantsRepIso A S T hST).hom n :=
  nestedQuotientInvariantsHomologyNatTrans_app A S T hST n

theorem factorization (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    finiteNegativeDeflation A S T hST n =
      (groupHomology.coinfNatTrans R
          (T.map (QuotientGroup.mk' S)) n).app
            (A.quotientToInvariants S) ≫
        (groupHomology.functor R
          ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n).map
            (FiniteGroupTateCohomology.quotientNorm
              (A.quotientToInvariants S)
              (T.map (QuotientGroup.mk' S))) ≫
        groupHomology.map
          (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom
          (nestedQuotientInvariantsRepIso A S T hST).hom n :=
  finiteNegativeDeflation_formula A S T hST n

theorem coefficient_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    (groupHomology.functor R (G ⧸ S) n).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeDeflation B S T hST n =
    finiteNegativeDeflation A S T hST n ≫
      (groupHomology.functor R (G ⧸ T) n).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  finiteNegativeDeflation_naturality f S T hST n

local notation "G₂" => Multiplicative (ZMod 2)

theorem bottom_lt_top : (⊥ : Subgroup G₂) < ⊤ := bot_lt_top

noncomputable local instance : Fintype
    ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) :=
  Fintype.ofFinite _

theorem concrete_degree_zero (A : Rep.{0} ℤ G₂) :
    finiteNegativeDeflation A ⊥ ⊤ bot_le 0 =
      (groupHomology.coinfNatTrans ℤ
        ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) 0).app
          (A.quotientToInvariants ⊥) ≫
        (groupHomology.functor ℤ
          ((G₂ ⧸ (⊥ : Subgroup G₂)) ⧸
            (⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) 0).map
          (FiniteGroupTateCohomology.quotientNorm
            (A.quotientToInvariants ⊥)
            ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂)))) ≫
        groupHomology.map
          (QuotientGroup.quotientQuotientEquivQuotient
            (⊥ : Subgroup G₂) ⊤ bot_le).toMonoidHom
          (nestedQuotientInvariantsRepIso A ⊥ ⊤ bot_le).hom 0 :=
  factorization A ⊥ ⊤ bot_le 0

theorem concrete_positive_degree (A : Rep.{0} ℤ G₂) :
    finiteNegativeDeflation A ⊥ ⊤ bot_le 1 =
      (groupHomology.coinfNatTrans ℤ
        ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) 1).app
          (A.quotientToInvariants ⊥) ≫
        (groupHomology.functor ℤ
          ((G₂ ⧸ (⊥ : Subgroup G₂)) ⧸
            (⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))) 1).map
          ((FiniteGroupTateCohomology.quotientNormNatTrans
            (R := ℤ) (S := (⊤ : Subgroup G₂).map
              (QuotientGroup.mk' (⊥ : Subgroup G₂)))).app
                (A.quotientToInvariants ⊥)) ≫
        groupHomology.map
          (QuotientGroup.quotientQuotientEquivQuotient
            (⊥ : Subgroup G₂) ⊤ bot_le).toMonoidHom
          (nestedQuotientInvariantsRepIso A ⊥ ⊤ bot_le).hom 1 := by
  rw [FiniteGroupTateCohomology.quotientNormNatTrans_app]
  exact factorization A ⊥ ⊤ bot_le 1

theorem concrete_positive_naturality {A B : Rep.{0} ℤ G₂} (f : A ⟶ B) :
    (groupHomology.functor ℤ (G₂ ⧸ (⊥ : Subgroup G₂)) 1).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊥ : Subgroup G₂)).map f) ≫
      finiteNegativeDeflation B ⊥ ⊤ bot_le 1 =
    finiteNegativeDeflation A ⊥ ⊤ bot_le 1 ≫
      (groupHomology.functor ℤ (G₂ ⧸ (⊤ : Subgroup G₂)) 1).map
        ((Rep.quotientToInvariantsFunctor ℤ (⊤ : Subgroup G₂)).map f) :=
  coefficient_naturality f ⊥ ⊤ bot_le 1

end FiniteNegativeNativeClient
