/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.LevelCompactNorm

/-!
# Native relative-norm client

Direct clients can compute relative norms using a chosen right transversal,
compose norms through a tower, use residual actions at normal levels, and
obtain continuity solely from the levelwise topology data.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open ContinuousGroupCohomology

namespace LevelCompactNormNative

universe uR uG uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The subgroup used for the relative norm is the pullback inside `U`. -/
theorem relativeNormSubgroup_comap (U V : OpenSubgroup G) :
    LevelCompact.relativeNormSubgroup U V =
      V.comap U.subtype continuous_subtype_val := rfl

local instance normClientTransversalFintype (U V : OpenSubgroup G)
    (T : (LevelCompact.relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    Fintype ↥(T : Set U) :=
  LevelCompact.relativeNormTransversalFintype U V T

theorem norm_with_choice (A : Rep.{uA} R G) (U V : OpenSubgroup G)
    (h : V ≤ U)
    (T : (LevelCompact.relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    LevelCompact.relativeNorm A U V h =
      LevelCompact.relativeNormWithTransversal A U V h T :=
  LevelCompact.relativeNorm_eq_withTransversal A U V h T

theorem norm_two_choices (A : Rep.{uA} R G) (U V : OpenSubgroup G)
    (h : V ≤ U)
    (T S : (LevelCompact.relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    LevelCompact.relativeNormWithTransversal A U V h T =
      LevelCompact.relativeNormWithTransversal A U V h S :=
  LevelCompact.relativeNormWithTransversal_eq A U V h T S

theorem norm_with_choice_coe (A : Rep.{uA} R G) (U V : OpenSubgroup G)
    (h : V ≤ U)
    (T : (LevelCompact.relativeNormSubgroup U V).toSubgroup.RightTransversal)
    (x : openSubgroupInvariants A V) :
    (LevelCompact.relativeNorm A U V h x : A) =
      ∑ t : ↥(T : Set U), A.ρ (((t : U) : G)⁻¹) x := by
  rw [norm_with_choice A U V h T]
  exact LevelCompact.relativeNormWithTransversal_coe A U V h T x

theorem norm_tower (A : Rep.{uA} R G) (U V W : OpenSubgroup G)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    (LevelCompact.relativeNorm A U V hVU).comp
        (LevelCompact.relativeNorm A V W hWV) =
      LevelCompact.relativeNorm A U W (hWV.trans hVU) :=
  LevelCompact.relativeNorm_comp A U V W hWV hVU

theorem norm_same_level (A : Rep.{uA} R G) (U : OpenSubgroup G) :
    LevelCompact.relativeNorm A U U le_rfl = LinearMap.id :=
  LevelCompact.relativeNorm_refl A U

theorem norm_residual_action (A : Rep.{uA} R G)
    (U V : OpenNormalSubgroup G) (h : V ≤ U)
    (g : G) (x : openSubgroupInvariants A V.toOpenSubgroup) :
    (A.quotientToInvariants U.toSubgroup).ρ
        (QuotientGroup.mk' U.toSubgroup g)
        (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x) =
      LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h
        ((A.quotientToInvariants V.toSubgroup).ρ
          (QuotientGroup.mk' V.toSubgroup g) x) :=
  LevelCompact.relativeNorm_quotientToInvariants_action_mk A U V h g x

theorem norm_range_residual_stable (A : Rep.{uA} R G)
    (U V : OpenNormalSubgroup G) (h : V ≤ U)
    (q : G ⧸ U.toSubgroup)
    {y : openSubgroupInvariants A U.toOpenSubgroup}
    (hy : y ∈ LinearMap.range
      (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h)) :
    (A.quotientToInvariants U.toSubgroup).ρ q y ∈ LinearMap.range
      (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) :=
  LevelCompact.relativeNorm_range_quotientToInvariants_stable A U V h q hy

theorem norm_continuous (A : Rep.{uA} R G) (L : LevelCompact A)
    (U V : OpenSubgroup G) (h : V ≤ U) :
    @Continuous (openSubgroupInvariants A V) (openSubgroupInvariants A U)
      (L.topology V) (L.topology U) (LevelCompact.relativeNorm A U V h) :=
  LevelCompact.continuous_relativeNorm A L U V h

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩

def twoElementBottom : OpenSubgroup G₂ where
  toSubgroup := ⊥
  isOpen' := isOpen_discrete _

theorem twoElementBottom_lt_top : twoElementBottom < ⊤ := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

theorem norm_twoElement_proper_level (A : Rep.{uA} R G₂)
    (T : (LevelCompact.relativeNormSubgroup (⊤ : OpenSubgroup G₂)
      twoElementBottom).toSubgroup.RightTransversal)
    (x : openSubgroupInvariants A twoElementBottom) :
    (LevelCompact.relativeNorm A ⊤ twoElementBottom le_top x : A) =
      ∑ t : ↥(T : Set (⊤ : OpenSubgroup G₂)), A.ρ (((t : (⊤ : OpenSubgroup G₂)) : G₂)⁻¹) x :=
  norm_with_choice_coe A ⊤ twoElementBottom le_top T x

#print axioms relativeNormSubgroup_comap
#print axioms norm_with_choice
#print axioms norm_two_choices
#print axioms norm_with_choice_coe
#print axioms norm_tower
#print axioms norm_same_level
#print axioms norm_residual_action
#print axioms norm_range_residual_stable
#print axioms norm_continuous
#print axioms twoElementBottom_lt_top
#print axioms norm_twoElement_proper_level

end LevelCompactNormNative
