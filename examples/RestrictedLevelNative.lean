/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.RestrictedLevelCompact
public import Mathlib.Data.ZMod.Basic

/-!
# Native restricted-level client

Every universal norm lies in the range of the relative norm from each deeper
open normal level. The full and universal-norm choices give two restricted
systems, with the latter contained in any restricted system. Restricted norms
are linear and continuous between induced compact Hausdorff additive groups.
No topology on the coefficient ring or ambient representation is required.

The finite-group test constructs proper open normal levels in
`Multiplicative (ZMod 2)` and tests range containment across them. It does not
assert that the universal-norm submodule is the entire invariant module or
that it has a nonzero element. It does not test restricted Tate stages.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open ContinuousGroupCohomology

namespace RestrictedLevelNative

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

theorem universal_membership (U : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A U.toOpenSubgroup) :
    x ∈ LevelCompact.universalNormSubmodule A U ↔
      ∀ (V : OpenNormalSubgroup G) (h : V ≤ U),
        x ∈ LinearMap.range
          (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) := by
  exact LevelCompact.mem_universalNormSubmodule_iff A U x

theorem universal_in_each_norm_range (U V : OpenNormalSubgroup G) (h : V ≤ U)
    {x : openSubgroupInvariants A U.toOpenSubgroup}
    (hx : x ∈ LevelCompact.universalNormSubmodule A U) :
    x ∈ LinearMap.range
      (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) := by
  exact LevelCompact.universalNormSubmodule_le_range A U V h hx

theorem universal_stable (U : OpenNormalSubgroup G) (q : G ⧸ U.toSubgroup)
    {x : openSubgroupInvariants A U.toOpenSubgroup}
    (hx : x ∈ LevelCompact.universalNormSubmodule A U) :
    (A.quotientToInvariants U.toSubgroup).ρ q x ∈
      LevelCompact.universalNormSubmodule A U := by
  exact LevelCompact.universalNormSubmodule_stable A U q hx

theorem universal_norm_preservation (U V : OpenNormalSubgroup G) (h : V ≤ U)
    {x : openSubgroupInvariants A V.toOpenSubgroup}
    (hx : x ∈ LevelCompact.universalNormSubmodule A V) :
    LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x ∈
      LevelCompact.universalNormSubmodule A U := by
  exact LevelCompact.relativeNorm_mem_universalNormSubmodule A U V h hx

theorem chosen_contains_universal (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) {x : openSubgroupInvariants A U.toOpenSubgroup}
    (hx : x ∈ LevelCompact.universalNormSubmodule A U) :
    x ∈ S.coefficients U := by
  exact S.universalNorm_le U hx

theorem chosen_norm_formula (S : LevelCompact.RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) (x : S.coefficients V) :
    (S.relativeNorm U V h x : openSubgroupInvariants A U.toOpenSubgroup) =
      LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x := by
  exact S.relativeNorm_coe U V h x

theorem chosen_norm_tower (S : LevelCompact.RestrictedLevelSystem A L)
    (U V W : OpenNormalSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) :
    (S.relativeNorm U V hVU).comp (S.relativeNorm V W hWV) =
      S.relativeNorm U W (hWV.trans hVU) := by
  exact S.relativeNorm_comp U V W hWV hVU

theorem chosen_norm_same_level (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    S.relativeNorm U U le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change LevelCompact.relativeNorm A U.toOpenSubgroup U.toOpenSubgroup le_rfl
      (x : openSubgroupInvariants A U.toOpenSubgroup) = x
  rw [LevelCompact.relativeNorm_refl]
  rfl

theorem chosen_norm_continuous (S : LevelCompact.RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    @Continuous (S.coefficients V) (S.coefficients U)
      (S.topology V) (S.topology U) (S.relativeNorm U V h) := by
  exact S.continuous_relativeNorm U V h

theorem chosen_compact (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @CompactSpace (S.coefficients U) (S.topology U) := by
  exact S.compact U

theorem chosen_hausdorff (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @T2Space (S.coefficients U) (S.topology U) := by
  exact S.t2 U

theorem chosen_additive_group (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @IsTopologicalAddGroup (S.coefficients U) (S.topology U) _ := by
  exact S.topologicalAddGroup U

noncomputable def chosen_compact_group (S : LevelCompact.RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) : CompHausAddCommGrp.{u} :=
  S.group U

noncomputable def chosen_norm_group_hom (S : LevelCompact.RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    S.group V ⟶ S.group U :=
  S.relativeNormHom U V h

theorem full_choice (U : OpenNormalSubgroup G) :
    (LevelCompact.fullRestrictedLevelSystem A L).subrepresentation U = ⊤ := by
  exact LevelCompact.fullRestrictedLevelSystem_subrepresentation A L U

theorem canonical_choice (U : OpenNormalSubgroup G) :
    (LevelCompact.universalNormRestrictedLevelSystem A L).coefficients U =
      LevelCompact.universalNormSubmodule A U := by
  change (LevelCompact.universalNormSubrepresentation A U).toSubmodule = _
  exact LevelCompact.universalNormSubrepresentation_toSubmodule A U

theorem canonical_le_full (U : OpenNormalSubgroup G) :
    (LevelCompact.universalNormRestrictedLevelSystem A L).coefficients U ≤
      (LevelCompact.fullRestrictedLevelSystem A L).coefficients U := by
  intro x hx
  exact (LevelCompact.fullRestrictedLevelSystem A L).universalNorm_le U
    (by simpa only [canonical_choice A L U] using hx)

local notation "G₂" => Multiplicative (ZMod 2)

local instance : TopologicalSpace G₂ := ⊥
local instance : DiscreteTopology G₂ := ⟨rfl⟩

def twoElementBottom : OpenNormalSubgroup G₂ where
  toOpenSubgroup := { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
  isNormal' := by
    change (⊥ : Subgroup G₂).Normal
    infer_instance

def twoElementTop : OpenNormalSubgroup G₂ where
  toOpenSubgroup := ⊤
  isNormal' := by
    change (⊤ : Subgroup G₂).Normal
    infer_instance

theorem twoElementBottom_lt_top : twoElementBottom < twoElementTop := by
  change (⊥ : Subgroup G₂) < ⊤
  exact bot_lt_top

noncomputable def finiteDiscreteLevelCompact (A : Rep.{0} (ZMod 2) G₂)
    [Finite A] : LevelCompact A where
  topology _ := ⊥
  compact U := by
    let _ : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    let _ : Finite (openSubgroupInvariants A U) :=
      Finite.of_injective (fun x : openSubgroupInvariants A U => (x : A))
        Subtype.val_injective
    infer_instance
  t2 U := by
    let _ : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    let _ : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    infer_instance
  topologicalAddGroup U := by
    let _ : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    let _ : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    infer_instance
  continuous_transport U V σ h := by
    let _ : TopologicalSpace (openSubgroupInvariants A U) := ⊥
    let _ : TopologicalSpace (openSubgroupInvariants A V) := ⊥
    let _ : DiscreteTopology (openSubgroupInvariants A U) := ⟨rfl⟩
    exact continuous_of_discreteTopology

theorem proper_level_norm_range {Rfinite : Type} [CommRing Rfinite]
    (A : Rep.{0} Rfinite G₂) (L : LevelCompact A)
    {x : openSubgroupInvariants A twoElementTop.toOpenSubgroup}
    (hx : x ∈ (LevelCompact.universalNormRestrictedLevelSystem A L).coefficients
      twoElementTop) :
    x ∈ LinearMap.range (LevelCompact.relativeNorm A
      twoElementTop.toOpenSubgroup twoElementBottom.toOpenSubgroup
      (le_of_lt twoElementBottom_lt_top)) := by
  have hx' : x ∈ LevelCompact.universalNormSubmodule A twoElementTop := by
    simpa only [canonical_choice A L twoElementTop] using hx
  exact universal_in_each_norm_range A twoElementTop twoElementBottom
    (le_of_lt twoElementBottom_lt_top) hx'

theorem finite_discrete_proper_norm_range (A : Rep.{0} (ZMod 2) G₂)
    [Finite A] {x : openSubgroupInvariants A twoElementTop.toOpenSubgroup}
    (hx : x ∈ (LevelCompact.universalNormRestrictedLevelSystem A
      (finiteDiscreteLevelCompact A)).coefficients twoElementTop) :
    x ∈ LinearMap.range (LevelCompact.relativeNorm A
      twoElementTop.toOpenSubgroup twoElementBottom.toOpenSubgroup
      (le_of_lt twoElementBottom_lt_top)) := by
  exact proper_level_norm_range A (finiteDiscreteLevelCompact A) hx

end RestrictedLevelNative
