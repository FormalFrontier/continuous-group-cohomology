/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.ExceptionalTateDeflationTopology
public import ContinuousGroupCohomology.FiniteTateDiagrams

/-!
# Compact exceptional Tate deflation diagrams

The compact finite Tate kernel and quotient in degrees `-1` and `0` form
covariant diagrams over open normal subgroups: `S ≤ T` sends the `G / S`
stage to the `G / T` stage by continuous deflation. Forgetting topology and
scalars gives additive natural isomorphisms with the algebraic Tate diagrams.

The compact structures use a chosen `LevelCompact`; no topology on the
coefficient ring, canonical topological module, or inverse-limit exactness is
asserted. Adapted from Beacon's compact exceptional Tate diagrams in the
continuous-group-cohomology source research at commit
`9fbcd52d0fe4ce982ac506976542523d91dd84c4`.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Compact finite Tate stages in degree `-1`, with continuous deflation. -/
@[expose] noncomputable def compactFiniteNegativeOneDeflationDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj S := finiteTateNegOne A L S
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegOneDeflation A L S T (leOfHom f)
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateNegOneDeflation_refl A L S
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteTateNegOneDeflation_comp A L S T U (leOfHom f) (leOfHom g)).symm

/-- Compact finite Tate stages in degree `0`, with continuous deflation. -/
@[expose] noncomputable def compactFiniteZeroDeflationDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj S := finiteTateZero A L S
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateZeroDeflation A L S T (leOfHom f)
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteTateZeroDeflation_refl A L S
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteTateZeroDeflation_comp A L S T U (leOfHom f) (leOfHom g)).symm

/-- Stagewise additive Tate comparisons commute with degree-`-1` deflation. -/
@[expose] noncomputable def finiteNegativeOneDeflationAdditiveDiagramIso :
    finiteNegativeOneDeflationDiagram A ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      compactFiniteNegativeOneDeflationDiagram A L ⋙
        forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun S ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      exact (tateCohomologyNegOneAddEquivFiniteTate A L S).toAddCommGrpIso)
    (fun {S T} f ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
        Fintype.ofFinite _
      ext x
      exact tateCohomologyNegOneAddEquivFiniteTate_finiteNegativeOneDeflation
        A L S T (leOfHom f) x)

/-- Stagewise additive Tate comparisons commute with degree-zero deflation. -/
@[expose] noncomputable def finiteZeroDeflationAdditiveDiagramIso :
    finiteZeroDeflationDiagram A ⋙
        forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      compactFiniteZeroDeflationDiagram A L ⋙
        forget₂ CompHausAddCommGrp.{u} AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun S ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      exact (tateCohomologyZeroAddEquivFiniteTate A L S).toAddCommGrpIso)
    (fun {S T} f ↦ by
      let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (G ⧸ T.toSubgroup) := Fintype.ofFinite _
      let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
        Fintype.ofFinite _
      ext x
      exact tateCohomologyZeroAddEquivFiniteTate_finiteZeroDeflation
        A L S T (leOfHom f) x)

end ContinuousGroupCohomology.LevelCompact
