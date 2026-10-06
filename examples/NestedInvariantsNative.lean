/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
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

example : (⊥ : Subgroup (Multiplicative (ZMod 2))) < ⊤ := bot_lt_top

universe u

variable {R : Type u} [CommRing R] (A : Rep.{0} R (Multiplicative (ZMod 2)))

example (g : Multiplicative (ZMod 2)) :
    (QuotientGroup.quotientQuotientEquivQuotient
      (⊥ : Subgroup (Multiplicative (ZMod 2))) ⊤ bot_le)
        (QuotientGroup.mk' ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
          (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))))
          (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2))) g)) =
      QuotientGroup.mk' (⊤ : Subgroup (Multiplicative (ZMod 2))) g := rfl

example (x : Representation.invariants
    ((A.quotientToInvariants (⊥ : Subgroup (Multiplicative (ZMod 2)))).ρ.comp
      ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
        (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2))))).subtype)) :
    (nestedQuotientInvariantsEquiv A (⊥ : Subgroup (Multiplicative (ZMod 2)))
      ⊤ bot_le x).1 = x.1.1 :=
  nestedQuotientInvariantsEquiv_apply_val A ⊥ ⊤ bot_le x

example (x : Representation.invariants
    (A.ρ.comp (⊤ : Subgroup (Multiplicative (ZMod 2))).subtype)) :
    ((nestedQuotientInvariantsEquiv A (⊥ : Subgroup (Multiplicative (ZMod 2)))
      ⊤ bot_le).symm x).1.1 = x.1 :=
  nestedQuotientInvariantsEquiv_symm_apply_val A ⊥ ⊤ bot_le x

example (x : (A.quotientToInvariants
    (⊥ : Subgroup (Multiplicative (ZMod 2)))).quotientToInvariants
    ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
      (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))))) :
    ((nestedQuotientInvariantsRepIso A (⊥ : Subgroup (Multiplicative (ZMod 2)))
      ⊤ bot_le).hom x).1 = x.1.1 :=
  nestedQuotientInvariantsRepIso_hom_apply_val A ⊥ ⊤ bot_le x

example [Fintype ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
    (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))))]
    (x : A.quotientToInvariants (⊥ : Subgroup (Multiplicative (ZMod 2)))) :
    ((nestedQuotientInvariantsRepIso A (⊥ : Subgroup (Multiplicative (ZMod 2)))
      ⊤ bot_le).hom.hom
      (FiniteGroupTateCohomology.quotientNorm
        (A.quotientToInvariants (⊥ : Subgroup (Multiplicative (ZMod 2))))
        ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
          (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))))
        (Representation.Coinvariants.mk _ x))).1 =
      ∑ q : (⊤ : Subgroup (Multiplicative (ZMod 2))).map
        (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))),
        (((A.quotientToInvariants (⊥ : Subgroup (Multiplicative (ZMod 2)))).ρ q.1) x).1 := by
  rw [nestedQuotientInvariantsRepIso_hom_apply_val,
    FiniteGroupTateCohomology.quotientNorm_mk]
  simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum,
    MonoidHom.comp_apply]
  apply Finset.sum_congr rfl
  intro q _
  rfl

example :
    (nestedQuotientInvariantsRepNatTrans (R := R)
      (⊥ : Subgroup (Multiplicative (ZMod 2))) ⊤ bot_le).app A =
      (nestedQuotientInvariantsRepIso A
        (⊥ : Subgroup (Multiplicative (ZMod 2))) ⊤ bot_le).hom :=
  nestedQuotientInvariantsRepNatTrans_app A ⊥ ⊤ bot_le

example {B : Rep.{0} R (Multiplicative (ZMod 2))} (f : A ⟶ B) :
    (Rep.quotientToInvariantsFunctor R
      ((⊤ : Subgroup (Multiplicative (ZMod 2))).map
        (QuotientGroup.mk' (⊥ : Subgroup (Multiplicative (ZMod 2)))))).map
        ((Rep.quotientToInvariantsFunctor R
          (⊥ : Subgroup (Multiplicative (ZMod 2)))).map f) ≫
      (nestedQuotientInvariantsRepIso B ⊥ ⊤ bot_le).hom =
    (nestedQuotientInvariantsRepIso A ⊥ ⊤ bot_le).hom ≫
      (Rep.resFunctor
        (QuotientGroup.quotientQuotientEquivQuotient
          (⊥ : Subgroup (Multiplicative (ZMod 2))) ⊤ bot_le).toMonoidHom).map
        ((Rep.quotientToInvariantsFunctor R ⊤).map f) :=
  nestedQuotientInvariantsRepIso_naturality f ⊥ ⊤ bot_le

end NestedInvariantsNativeClient
