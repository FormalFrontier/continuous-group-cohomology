/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.NestedInvariants
public import FiniteGroupTateCohomology.Norm
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.CategoryTheory.Whiskering

/-!
# Finite-level negative deflation

For normal subgroups `S ≤ T` of `G`, with finite intervening quotient
`T / S`, this file constructs the homology map

`H_n(G / S, A^S) ⟶ H_n(G / T, A^T)`.

It is the composite of coinflation from `T / S`, the residual-equivariant
finite-group norm from coinvariants to invariants, and the homology map induced
by the third-isomorphism equivalence and the nested-invariants representation
isomorphism. For positive `n`, this is the usual finite-level deflation in Tate
degree `-n-1`. The degree `-1` kernel construction is not defined here.

Mathlib's group-homology functor currently places the coefficient ring, group,
and representation carrier in one universe. The definitions below retain that
constraint rather than claiming mixed-universe generality.
-/

public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G]

/-- Homology transport from iterated invariants to direct invariants through
the third-isomorphism equivalence. -/
noncomputable def nestedQuotientInvariantsHomologyNatTrans
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) :
    Rep.quotientToInvariantsFunctor R S ⋙
        Rep.quotientToInvariantsFunctor R (T.map (QuotientGroup.mk' S)) ⋙
        groupHomology.functor R
          ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n ⟶
      Rep.quotientToInvariantsFunctor R T ⋙
        groupHomology.functor R (G ⧸ T) n :=
  Functor.whiskerRight (nestedQuotientInvariantsRepNatTrans S T hST)
      (groupHomology.functor R
        ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n) ≫
    Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R T)
      (groupHomology.coresNatTrans R
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom n)

private lemma nestedQuotientInvariantsHomologyMap_eq (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) :
    groupHomology.map
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom
        (nestedQuotientInvariantsRepIso A S T hST).hom n =
      (groupHomology.functor R
        ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n).map
          (nestedQuotientInvariantsRepIso A S T hST).hom ≫
        (groupHomology.coresNatTrans R
          (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom n).app
            (A.quotientToInvariants T) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [groupHomology.functor_map, groupHomology.coresNatTrans_app]
    rw [← groupHomology.map_comp]
    apply groupHomology.map_congr
    · ext
      rfl
    · rfl

/-- The homology transport component is the single map induced by the
third-isomorphism equivalence and the nested-invariants representation map. -/
@[simp]
lemma nestedQuotientInvariantsHomologyNatTrans_app (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) :
    (nestedQuotientInvariantsHomologyNatTrans S T hST n).app A =
      groupHomology.map
        (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom
        (nestedQuotientInvariantsRepIso A S T hST).hom n := by
  set_option backward.isDefEq.respectTransparency false in
    rw [nestedQuotientInvariantsHomologyNatTrans]
    exact (nestedQuotientInvariantsHomologyMap_eq A S T hST n).symm

/-- Finite-level negative deflation, natural in the coefficient
representation. In positive homological degree `n`, its components model Tate
deflation in degree `-n-1`. -/
noncomputable def finiteNegativeDeflationNatTrans
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    Rep.quotientToInvariantsFunctor R S ⋙
        groupHomology.functor R (G ⧸ S) n ⟶
      Rep.quotientToInvariantsFunctor R T ⋙
        groupHomology.functor R (G ⧸ T) n :=
  Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R S)
      (groupHomology.coinfNatTrans R
        (T.map (QuotientGroup.mk' S)) n) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (Rep.quotientToInvariantsFunctor R S)
        (FiniteGroupTateCohomology.quotientNormNatTrans
          (R := R) (S := T.map (QuotientGroup.mk' S))))
      (groupHomology.functor R
        ((G ⧸ S) ⧸ T.map (QuotientGroup.mk' S)) n) ≫
    nestedQuotientInvariantsHomologyNatTrans S T hST n

/-- The component of finite-level negative deflation at `A`. -/
noncomputable def finiteNegativeDeflation (A : Rep R G)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    groupHomology (A.quotientToInvariants S) n ⟶
      groupHomology (A.quotientToInvariants T) n :=
  (finiteNegativeDeflationNatTrans S T hST n).app A

/-- Finite-level negative deflation is coinflation, followed by the quotient
norm, followed by transport through the third-isomorphism equivalence. -/
lemma finiteNegativeDeflation_formula (A : Rep R G)
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
          (nestedQuotientInvariantsRepIso A S T hST).hom n := by
  set_option backward.isDefEq.respectTransparency false in
    rw [finiteNegativeDeflation, finiteNegativeDeflationNatTrans]
    change _ ≫ _ ≫
        (nestedQuotientInvariantsHomologyNatTrans S T hST n).app A = _
    rw [nestedQuotientInvariantsHomologyNatTrans_app]
    rfl

/-- Finite-level negative deflation commutes with coefficient morphisms. -/
@[reassoc]
lemma finiteNegativeDeflation_naturality {A B : Rep R G} (f : A ⟶ B)
    (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T)
    [Fintype (T.map (QuotientGroup.mk' S))] (n : ℕ) :
    (groupHomology.functor R (G ⧸ S) n).map
        ((Rep.quotientToInvariantsFunctor R S).map f) ≫
      finiteNegativeDeflation B S T hST n =
    finiteNegativeDeflation A S T hST n ≫
      (groupHomology.functor R (G ⧸ T) n).map
        ((Rep.quotientToInvariantsFunctor R T).map f) :=
  (finiteNegativeDeflationNatTrans S T hST n).naturality f

end ContinuousGroupCohomology
