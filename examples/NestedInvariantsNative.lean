/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Native client by worker-b Hive Task
hive-request-d2af742e44a5a0d1ef011810e719a1ab0abdf38b,
UID 88d05553-3c39-40c0-9c53-1b25f0339af5.
-/
module

import ContinuousGroupCohomology.NestedInvariants
import FiniteGroupTateCohomology.Norm
import Mathlib.Data.ZMod.Basic

/-!
# Nested invariants over a nontrivial finite quotient

The quotient by the bottom subgroup of the two-element cyclic group is
nontrivial. These anonymous examples check native reductions of nested
invariants, representation transport and its naturality, without importing
the legacy aggregate root or asserting a finite-negative-deflation theorem.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace NestedInvariantsNativeClient

local notation "G₂" => Multiplicative (ZMod 2)

example : (⊥ : Subgroup G₂) < ⊤ := bot_lt_top

universe u

variable {R : Type u} [CommRing R] (A : Rep.{0} R G₂)

example (g : G₂) :
    (QuotientGroup.quotientQuotientEquivQuotient
      (⊥ : Subgroup G₂) ⊤ bot_le)
        (QuotientGroup.mk' ((⊤ : Subgroup G₂).map
          (QuotientGroup.mk' (⊥ : Subgroup G₂)))
          (QuotientGroup.mk' (⊥ : Subgroup G₂) g)) =
      QuotientGroup.mk' (⊤ : Subgroup G₂) g := rfl

example (x : Representation.invariants
    ((A.quotientToInvariants (⊥ : Subgroup G₂)).ρ.comp
      ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂))).subtype)) :
    (nestedQuotientInvariantsEquiv A (⊥ : Subgroup G₂) ⊤ bot_le x).1 = x.1.1 :=
  nestedQuotientInvariantsEquiv_apply_val A ⊥ ⊤ bot_le x

example (x : Representation.invariants (A.ρ.comp (⊤ : Subgroup G₂).subtype)) :
    ((nestedQuotientInvariantsEquiv A (⊥ : Subgroup G₂) ⊤ bot_le).symm x).1.1 = x.1 :=
  nestedQuotientInvariantsEquiv_symm_apply_val A ⊥ ⊤ bot_le x

example (x : (A.quotientToInvariants (⊥ : Subgroup G₂)).quotientToInvariants
    ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂)))) :
    ((nestedQuotientInvariantsRepIso A (⊥ : Subgroup G₂) ⊤ bot_le).hom x).1 =
      x.1.1 :=
  nestedQuotientInvariantsRepIso_hom_apply_val A ⊥ ⊤ bot_le x

example [Fintype ((⊤ : Subgroup G₂).map
    (QuotientGroup.mk' (⊥ : Subgroup G₂)))]
    (x : A.quotientToInvariants (⊥ : Subgroup G₂)) :
    ((nestedQuotientInvariantsRepIso A (⊥ : Subgroup G₂) ⊤ bot_le).hom.hom
      (FiniteGroupTateCohomology.quotientNorm
        (A.quotientToInvariants (⊥ : Subgroup G₂))
        ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂)))
        (Representation.Coinvariants.mk _ x))).1 =
      ∑ q : (⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂)),
        (((A.quotientToInvariants (⊥ : Subgroup G₂)).ρ q.1) x).1 := by
  rw [nestedQuotientInvariantsRepIso_hom_apply_val,
    FiniteGroupTateCohomology.quotientNorm_mk]
  simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum,
    MonoidHom.comp_apply]
  apply Finset.sum_congr rfl
  intro q _
  rfl

example :
    (nestedQuotientInvariantsRepNatTrans (R := R)
      (⊥ : Subgroup G₂) ⊤ bot_le).app A =
      (nestedQuotientInvariantsRepIso A (⊥ : Subgroup G₂) ⊤ bot_le).hom :=
  nestedQuotientInvariantsRepNatTrans_app A ⊥ ⊤ bot_le

example {B : Rep.{0} R G₂} (f : A ⟶ B) :
    (Rep.quotientToInvariantsFunctor R
      ((⊤ : Subgroup G₂).map (QuotientGroup.mk' (⊥ : Subgroup G₂)))).map
        ((Rep.quotientToInvariantsFunctor R (⊥ : Subgroup G₂)).map f) ≫
      (nestedQuotientInvariantsRepIso B ⊥ ⊤ bot_le).hom =
    (nestedQuotientInvariantsRepIso A ⊥ ⊤ bot_le).hom ≫
      (Rep.resFunctor
        (QuotientGroup.quotientQuotientEquivQuotient
          (⊥ : Subgroup G₂) ⊤ bot_le).toMonoidHom).map
        ((Rep.quotientToInvariantsFunctor R ⊤).map f) :=
  nestedQuotientInvariantsRepIso_naturality f ⊥ ⊤ bot_le

end NestedInvariantsNativeClient
