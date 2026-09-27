/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteTateTopology
public import Mathlib.Data.ZMod.Basic

/-!
# Public clients for compact finite Tate degrees

These examples exercise continuous kernel and quotient maps, their norm
equations and the algebraic cokernel representative equation. The two-element
acting group supplies a proper finite level; this client typechecks the API
and does not compute or assert nonvanishing of a Tate group.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace CGCExamples.FiniteTateTopologyNative

universe uR uG uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{uA} R G) (L : LevelCompact A) (S : OpenNormalSubgroup G)

/-- The public inclusion and projection are continuous morphisms of compact groups. -/
example : Continuous (LevelCompact.finiteTateNegOneι A L S) :=
  (LevelCompact.finiteTateNegOneι A L S).hom.continuous

example : Continuous (LevelCompact.finiteTateZeroπ A L S) :=
  (LevelCompact.finiteTateZeroπ A L S).hom.continuous

example (x : LevelCompact.finiteTateNegOne A L S) :
    LevelCompact.normFromFiniteCoinvariants A L S
      (LevelCompact.finiteTateNegOneι A L S x) = 0 :=
  LevelCompact.normFromFiniteCoinvariants_finiteTateNegOneι_apply A L S x

example (x : LevelCompact.finiteCoinvariants A (L := L) S) :
    LevelCompact.finiteTateZeroπ A L S
      (LevelCompact.normFromFiniteCoinvariants A L S x) = 0 :=
  LevelCompact.finiteTateZeroπ_normFromFiniteCoinvariants_apply A L S x

section AlgebraicComparison

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A) (S : OpenNormalSubgroup G)
variable [Fintype (G ⧸ S.toSubgroup)]

example : tateCohomology (A.quotientToInvariants S.toSubgroup) (-1) ≃+
    LevelCompact.finiteTateNegOne A L S :=
  LevelCompact.tateCohomologyNegOneAddEquivFiniteTate A L S

example : tateCohomology (A.quotientToInvariants S.toSubgroup) 0 ≃+
    LevelCompact.finiteTateZero A L S :=
  LevelCompact.tateCohomologyZeroAddEquivFiniteTate A L S

example (x : (Rep.coinvariantsFunctor R (G ⧸ S.toSubgroup)).obj
    (A.quotientToInvariants S.toSubgroup)) :
    LevelCompact.openSubgroupInvariantsAddEquivGroup A L ⊤
        (LevelCompact.finiteNormTargetEquiv A S
          ((FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup)).hom x)) =
      LevelCompact.normFromFiniteCoinvariants A L S
        (LevelCompact.algebraicCoinvariantsAddEquivFiniteCoinvariants A L S x) :=
  LevelCompact.finiteNormTargetEquiv_normFromCoinvariants A L S x

example (x : (Rep.invariantsFunctor R (G ⧸ S.toSubgroup)).obj
    (A.quotientToInvariants S.toSubgroup)) :
    LevelCompact.tateCohomologyZeroAddEquivFiniteTate A L S
        ((FiniteGroupTateCohomology.tateCohomologyZeroIsoCokernelNorm
          (A.quotientToInvariants S.toSubgroup)).inv
          (cokernel.π (FiniteGroupTateCohomology.normFromCoinvariants
            (A.quotientToInvariants S.toSubgroup)) x)) =
      LevelCompact.finiteTateZeroπ A L S
        (LevelCompact.finiteNormTargetAddEquivGroup A L S x) :=
  LevelCompact.tateCohomologyZeroAddEquivFiniteTate_cokernelπ A L S x

end AlgebraicComparison

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩

/-- A proper open normal level of a genuinely two-element compact group. -/
def properLevel : OpenNormalSubgroup G₂ where
  toOpenSubgroup := { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
  isNormal' := by
    change (⊥ : Subgroup G₂).Normal
    infer_instance

theorem properLevel_lt_top :
    properLevel.toOpenSubgroup < (⊤ : OpenSubgroup G₂) := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

/-- The negative-degree norm equation applies at this nontrivial finite quotient. -/
example (A : Rep.{0} (ZMod 2) G₂) (L : LevelCompact A)
    (x : LevelCompact.finiteTateNegOne A L properLevel) :
    LevelCompact.normFromFiniteCoinvariants A L properLevel
      (LevelCompact.finiteTateNegOneι A L properLevel x) = 0 :=
  LevelCompact.normFromFiniteCoinvariants_finiteTateNegOneι_apply A L properLevel x

end CGCExamples.FiniteTateTopologyNative
