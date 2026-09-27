/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Native adaptation: hive-request-4672f7979360ce22ac8097377a50a3fe1875b240
  (bc9a1c76-5840-44a1-bbc3-48aaf2836c2a)
-/
module

public import ContinuousGroupCohomology.ExceptionalTateDeflationTopology

/-!
# Public clients for compact exceptional Tate deflation

These examples check the continuous maps, their representative equations,
comparison with the actual algebraic finite deflations, and composition
through three open normal levels. They assert no nonzero Tate group.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace CGCExamples.ExceptionalTateDeflationTopologyNative

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)
variable (S T U : OpenNormalSubgroup G) (hST : S ≤ T) (hTU : T ≤ U)
variable [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]
variable [Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup))]
variable [Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]

example : Continuous (LevelCompact.finiteTateNegOneDeflation A L S T hST) :=
  (LevelCompact.finiteTateNegOneDeflation A L S T hST).hom.continuous

example : Continuous (LevelCompact.finiteTateZeroDeflation A L S T hST) :=
  (LevelCompact.finiteTateZeroDeflation A L S T hST).hom.continuous

example (x : LevelCompact.finiteTateNegOne A L S) :
    LevelCompact.finiteTateNegOneι A L T
        (LevelCompact.finiteTateNegOneDeflation A L S T hST x) =
      LevelCompact.finiteCoinvariantDeflation A L S T hST
        (LevelCompact.finiteTateNegOneι A L S x) :=
  LevelCompact.finiteTateNegOneι_finiteTateNegOneDeflation_apply A L S T hST x

example (x : LevelCompact.group A L (⊤ : OpenSubgroup G)) :
    LevelCompact.finiteTateZeroDeflation A L S T hST
        (LevelCompact.finiteTateZeroπ A L S x) =
      LevelCompact.finiteTateZeroπ A L T x :=
  LevelCompact.finiteTateZeroDeflation_finiteTateZeroπ_apply A L S T hST x

example : LevelCompact.finiteTateNegOneDeflation A L S T hST ≫
      LevelCompact.finiteTateNegOneDeflation A L T U hTU =
    LevelCompact.finiteTateNegOneDeflation A L S U (hST.trans hTU) :=
  LevelCompact.finiteTateNegOneDeflation_comp A L S T U hST hTU

example : LevelCompact.finiteTateZeroDeflation A L S T hST ≫
      LevelCompact.finiteTateZeroDeflation A L T U hTU =
    LevelCompact.finiteTateZeroDeflation A L S U (hST.trans hTU) :=
  LevelCompact.finiteTateZeroDeflation_comp A L S T U hST hTU

variable [Fintype (G ⧸ S.toSubgroup)] [Fintype (G ⧸ T.toSubgroup)]

example (x : tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)) :
    LevelCompact.tateCohomologyNegOneAddEquivFiniteTate A L T
        (finiteNegativeOneDeflation A S.toSubgroup T.toSubgroup hST x) =
      LevelCompact.finiteTateNegOneDeflation A L S T hST
        (LevelCompact.tateCohomologyNegOneAddEquivFiniteTate A L S x) :=
  LevelCompact.tateCohomologyNegOneAddEquivFiniteTate_finiteNegativeOneDeflation
    A L S T hST x

example (x : tateCohomology (A.quotientToInvariants S.toSubgroup) 0) :
    LevelCompact.tateCohomologyZeroAddEquivFiniteTate A L T
        (finiteZeroDeflation A S.toSubgroup T.toSubgroup hST x) =
      LevelCompact.finiteTateZeroDeflation A L S T hST
        (LevelCompact.tateCohomologyZeroAddEquivFiniteTate A L S x) :=
  LevelCompact.tateCohomologyZeroAddEquivFiniteTate_finiteZeroDeflation
    A L S T hST x

end CGCExamples.ExceptionalTateDeflationTopologyNative
