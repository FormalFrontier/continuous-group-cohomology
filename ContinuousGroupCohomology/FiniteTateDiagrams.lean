/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteDeflationTransitivity
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Finite Tate deflation diagrams

For a profinite group `G` and an algebraic representation `A`, this
file packages finite-level deflation maps as functors indexed by
mathlib's `OpenNormalSubgroup G`. An inclusion `S ≤ T` is sent in the
covariant direction from the `G / S` level to the `G / T` level.

The homological diagram models negative Tate degrees below `-1`; the other two
diagrams package the exceptional degrees `-1` and `0`. Finiteness of every
quotient and intervening subgroup is obtained from the open-subgroup condition
and is used only to supply the `Fintype` witnesses required by the finite Tate
APIs.

At every stage the quotient group is definitionally the underlying group of
`(ProfiniteGrp.toFiniteQuotientFunctor G).obj S`; this file introduces neither
a replacement stage type nor a replacement quotient transition.

No inverse limit or topology on a limit is constructed here.
-/

public section

open CategoryTheory

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

/-- The finite-level negative-deflation diagram in homological degree `n`.

Its value at `S` is `H_n(G / S, A^S)`, which models Tate degree `-n-1` when
`n` is positive. -/
@[expose] noncomputable def finiteNegativeDeflationDiagram (A : Rep.{u} R G) (n : ℕ) :
    OpenNormalSubgroup G ⥤ ModuleCat R where
  obj S := groupHomology (A.quotientToInvariants S.toSubgroup) n
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteNegativeDeflation A S.toSubgroup T.toSubgroup (leOfHom f) n
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteNegativeDeflation_refl A S.toSubgroup n
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteNegativeDeflation_comp A S.toSubgroup T.toSubgroup U.toSubgroup
      (leOfHom f) (leOfHom g) n).symm

/-- The finite-level Tate deflation diagram in degree `-1`.

Its value at `S` is `TateH^{-1}(G / S, A^S)`. -/
@[expose] noncomputable def finiteNegativeOneDeflationDiagram (A : Rep.{u} R G) :
    OpenNormalSubgroup G ⥤ ModuleCat R where
  obj S := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    exact tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)
  map {S T} f := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteNegativeOneDeflation A S.toSubgroup T.toSubgroup (leOfHom f)
  map_id S := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteNegativeOneDeflation_refl A S.toSubgroup
  map_comp {S T U} f g := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ U.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteNegativeOneDeflation_comp A S.toSubgroup T.toSubgroup U.toSubgroup
      (leOfHom f) (leOfHom g)).symm

/-- The finite-level Tate deflation diagram in degree `0`.

Its value at `S` is `TateH^0(G / S, A^S)`. -/
@[expose] noncomputable def finiteZeroDeflationDiagram (A : Rep.{u} R G) :
    OpenNormalSubgroup G ⥤ ModuleCat R where
  obj S := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    exact tateCohomology (A.quotientToInvariants S.toSubgroup) 0
  map {S T} f := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteZeroDeflation A S.toSubgroup T.toSubgroup (leOfHom f)
  map_id S := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteZeroDeflation_refl A S.toSubgroup
  map_comp {S T U} f g := by
    let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (G ⧸ U.toSubgroup) := Fintype.ofFinite _
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteZeroDeflation_comp A S.toSubgroup T.toSubgroup U.toSubgroup
      (leOfHom f) (leOfHom g)).symm

end ContinuousGroupCohomology
