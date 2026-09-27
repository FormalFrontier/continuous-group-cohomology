/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Implementation: hive-request-e6d76bdf4dadaad23f990aa082128217880d7321
  (b9bd4a7e-8ee1-4213-9075-d0ebba7ab03e)
-/
module

public import ContinuousGroupCohomology.CompactFiniteTateNormSequence

/-!
# Downstream use of the compact finite Tate norm row

These examples access the producer through an ordinary module import at
arbitrary levels and representations. The diagram has identity transitions
on total invariants and uses actual coinvariant deflation elsewhere.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace CGCExamples.CompactFiniteTateNormSequenceNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)
variable (S T : OpenNormalSubgroup G) (f : S ⟶ T)

example : (LevelCompact.compactFiniteCoinvariantsDiagram A L).obj S =
    LevelCompact.finiteCoinvariants A (L := L) S :=
  LevelCompact.compactFiniteCoinvariantsDiagram_obj A L S

example : (LevelCompact.compactTotalInvariantsDiagram A L).obj S =
    LevelCompact.group A L (⊤ : OpenSubgroup G) :=
  LevelCompact.compactTotalInvariantsDiagram_obj A L S

example : (LevelCompact.compactTotalInvariantsDiagram A L).map f =
    𝟙 (LevelCompact.group A L (⊤ : OpenSubgroup G)) := rfl

example : (LevelCompact.compactFiniteTateNegOneInclusion A L).app S =
    LevelCompact.finiteTateNegOneι A L S :=
  LevelCompact.compactFiniteTateNegOneInclusion_app A L S

example : (LevelCompact.compactFiniteTateNorm A L).app S =
    LevelCompact.normFromFiniteCoinvariants A L S :=
  LevelCompact.compactFiniteTateNorm_app A L S

example : (LevelCompact.compactFiniteTateZeroProjection A L).app S =
    LevelCompact.finiteTateZeroπ A L S :=
  LevelCompact.compactFiniteTateZeroProjection_app A L S

example : (LevelCompact.compactFiniteTateNegOneInclusion A L).app S ≫
      (LevelCompact.compactFiniteCoinvariantsDiagram A L).map f =
    (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L).map f ≫
      (LevelCompact.compactFiniteTateNegOneInclusion A L).app T :=
  ((LevelCompact.compactFiniteTateNegOneInclusion A L).naturality f).symm

example : (LevelCompact.compactFiniteCoinvariantsDiagram A L).map f ≫
      (LevelCompact.compactFiniteTateNorm A L).app T =
    (LevelCompact.compactFiniteTateNorm A L).app S ≫
      (LevelCompact.compactTotalInvariantsDiagram A L).map f :=
  (LevelCompact.compactFiniteTateNorm A L).naturality f

example : (LevelCompact.compactTotalInvariantsDiagram A L).map f ≫
      (LevelCompact.compactFiniteTateZeroProjection A L).app T =
    (LevelCompact.compactFiniteTateZeroProjection A L).app S ≫
      (LevelCompact.compactFiniteZeroDeflationDiagram A L).map f :=
  (LevelCompact.compactFiniteTateZeroProjection A L).naturality f

example : Function.Exact
    ((LevelCompact.compactFiniteTateNegOneInclusion A L).app S)
    ((LevelCompact.compactFiniteTateNorm A L).app S) :=
  LevelCompact.finiteTateNorm_exact_left A L S

example : Function.Exact
    ((LevelCompact.compactFiniteTateNorm A L).app S)
    ((LevelCompact.compactFiniteTateZeroProjection A L).app S) :=
  LevelCompact.finiteTateNorm_exact_right A L S

example : Function.Injective
    ((LevelCompact.compactFiniteTateNegOneInclusion A L).app S) :=
  LevelCompact.finiteTateNegOneι_injective A L S

example : Function.Surjective
    ((LevelCompact.compactFiniteTateZeroProjection A L).app S) :=
  LevelCompact.finiteTateZeroπ_surjective A L S

example : Function.Surjective
    ((LevelCompact.compactFiniteZeroDeflationDiagram A L).map f) := by
  let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
    Fintype.ofFinite _
  exact LevelCompact.finiteTateZeroDeflation_surjective A L S T (leOfHom f)

end CGCExamples.CompactFiniteTateNormSequenceNative
