/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Underlying finite-coinvariant development: Beacon
-/
module

public import ContinuousGroupCohomology.FiniteCoinvariants
public import Mathlib.Data.ZMod.Basic

/-!
# Finite coinvariants: direct native client

The orbit-difference map, algebraic relation quotient and compact Hausdorff
descent require only a finite acting group and continuity of its individual
action maps. The levelwise norm examples use a proper open normal level of a
two-element group. No topology on the coefficient ring or ambient coefficient
module, nonzero quotient, norm surjectivity or continuous joint action is
asserted.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory ContinuousGroupCohomology

namespace FiniteCoinvariantsNative

universe uR uH uM uG uA

variable {R : Type uR} [CommRing R]
variable {H : Type uH} [Group H] [Fintype H]
variable {M : Type uM} [AddCommGroup M] [Module R M]

theorem orbit_single (ρ : Representation R H M) (g : H) (x : M) :
    finiteOrbitDifference ρ (Pi.single (Fintype.equivFin H g) x) = ρ g x - x :=
  finiteOrbitDifference_single ρ g x

theorem orbit_range (ρ : Representation R H M) :
    (finiteOrbitDifference ρ).range = Representation.Coinvariants.ker ρ :=
  finiteOrbitDifference_range ρ

section Topology

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M]

theorem orbit_range_closed (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) :
    (finiteOrbitDifferenceHom ρ hρ).hom.range =
      (Representation.Coinvariants.ker ρ).toAddSubgroup :=
  finiteOrbitDifferenceHom_range ρ hρ

theorem quotient_projection (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (x : M) :
    finiteCoinvariantsMk ρ hρ x = Representation.Coinvariants.mk ρ x :=
  finiteCoinvariantsMk_apply ρ hρ x

variable {N : Type uM} [AddCommGroup N] [Module R N]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N]

theorem invariant_descends_on_generators (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (f : M →ₗ[R] N)
    (hf : Continuous f) (hinv : ∀ g : H, f ∘ₗ ρ g = f) (x : M) :
    finiteCoinvariantsDesc ρ hρ f hf hinv (Representation.Coinvariants.mk ρ x) =
      f x :=
  finiteCoinvariantsDesc_mk ρ hρ f hf hinv x

theorem invariant_descent_continuous (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) (f : M →ₗ[R] N)
    (hf : Continuous f) (hinv : ∀ g : H, f ∘ₗ ρ g = f) :
    Continuous (finiteCoinvariantsDesc ρ hρ f hf hinv :
      finiteCoinvariants ρ hρ → N) :=
  (finiteCoinvariantsDesc ρ hρ f hf hinv).hom.continuous

theorem intertwining_map_on_generators (ρ : Representation R H M)
    (τ : Representation R H N) (hρ : ∀ g : H, Continuous (ρ g))
    (hτ : ∀ g : H, Continuous (τ g)) (f : ρ.IntertwiningMap τ)
    (hf : Continuous f) (x : M) :
    finiteCoinvariantsMap ρ τ hρ hτ f hf (Representation.Coinvariants.mk ρ x) =
      Representation.Coinvariants.mk τ (f x) :=
  finiteCoinvariantsMap_mk ρ τ hρ hτ f hf x

end Topology

section Level

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{uA} R G) (L : LevelCompact A)

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem residual_action_continuous (S : OpenNormalSubgroup G)
    (q : G ⧸ S.toSubgroup) :
    @Continuous (A.quotientToInvariants S.toSubgroup)
      (A.quotientToInvariants S.toSubgroup) (L.topology S.toOpenSubgroup)
      (L.topology S.toOpenSubgroup)
      ((A.quotientToInvariants S.toSubgroup).ρ q) :=
  LevelCompact.continuous_quotientToInvariants_action A L S q

theorem full_level_norm_comparison (S : OpenNormalSubgroup G)
    [Fintype (G ⧸ S.toSubgroup)]
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    (LevelCompact.relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup
        le_top x : A) =
      (Representation.norm (A.quotientToInvariants S.toSubgroup).ρ x :
        A.quotientToInvariants S.toSubgroup) :=
  LevelCompact.relativeNorm_eq_quotientToInvariants_norm A S x

theorem descended_norm_on_generators (S : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A S.toOpenSubgroup) :
    LevelCompact.normFromFiniteCoinvariants A L S
        (Representation.Coinvariants.mk
          (A.quotientToInvariants S.toSubgroup).ρ x) =
      LevelCompact.relativeNorm A (⊤ : OpenSubgroup G)
        S.toOpenSubgroup le_top x :=
  LevelCompact.normFromFiniteCoinvariants_mk A L S x

theorem descended_norm_continuous (S : OpenNormalSubgroup G) :
    Continuous (LevelCompact.normFromFiniteCoinvariants A L S :
      LevelCompact.finiteCoinvariants A L S →
        LevelCompact.group A L (⊤ : OpenSubgroup G)) :=
  (LevelCompact.normFromFiniteCoinvariants A L S).hom.continuous

end Level

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩

def properNormalLevel : OpenNormalSubgroup G₂ where
  toOpenSubgroup := { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
  isNormal' := by
    change (⊥ : Subgroup G₂).Normal
    infer_instance

theorem properNormalLevel_lt_top :
    properNormalLevel.toOpenSubgroup < (⊤ : OpenSubgroup G₂) := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

theorem descended_norm_proper_level (A : Rep.{uA} R G₂) (L : LevelCompact A)
    (x : openSubgroupInvariants A properNormalLevel.toOpenSubgroup) :
    LevelCompact.normFromFiniteCoinvariants A L properNormalLevel
        (Representation.Coinvariants.mk
          (A.quotientToInvariants properNormalLevel.toSubgroup).ρ x) =
      LevelCompact.relativeNorm A (⊤ : OpenSubgroup G₂)
        properNormalLevel.toOpenSubgroup le_top x :=
  descended_norm_on_generators A L properNormalLevel x

#print axioms orbit_single
#print axioms orbit_range
#print axioms orbit_range_closed
#print axioms quotient_projection
#print axioms invariant_descends_on_generators
#print axioms invariant_descent_continuous
#print axioms intertwining_map_on_generators
#print axioms residual_action_continuous
#print axioms full_level_norm_comparison
#print axioms descended_norm_on_generators
#print axioms descended_norm_continuous
#print axioms properNormalLevel_lt_top
#print axioms descended_norm_proper_level

end FiniteCoinvariantsNative
