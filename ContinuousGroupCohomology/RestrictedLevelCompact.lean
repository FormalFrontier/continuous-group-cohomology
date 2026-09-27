/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon (Source Maintainer)
-/
module

public import ContinuousGroupCohomology.LevelCompactNorm
public import ContinuousGroupCohomology.CompactAddCommGroup
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Restricted level-compact coefficient systems

This file provides the source-independent interface for choosing closed
subrepresentations inside the invariants of a level-compact representation.
The first canonical choice is the universal-norm submodule: the elements at
one open normal level that lie in the range of every deeper open-normal
relative norm. It is stable under the residual quotient action and relative
norms, hence defines a compact restricted coefficient system.

Restricted finite Tate stages and their connecting morphisms are deliberately
not constructed here.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- The elements of `A^U` lying in the range of the relative norm from every
deeper open normal level. -/
def universalNormSubmodule (A : Rep.{u} R G) (U : OpenNormalSubgroup G) :
    Submodule R (openSubgroupInvariants A U.toOpenSubgroup) :=
  ⨅ (V : OpenNormalSubgroup G), ⨅ (h : V ≤ U),
    LinearMap.range
      (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h)

theorem mem_universalNormSubmodule_iff (A : Rep.{u} R G)
    (U : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A U.toOpenSubgroup) :
    x ∈ universalNormSubmodule A U ↔
      ∀ (V : OpenNormalSubgroup G) (h : V ≤ U),
        x ∈ LinearMap.range
          (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) := by
  simp [universalNormSubmodule]

theorem universalNormSubmodule_le_range (A : Rep.{u} R G)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    universalNormSubmodule A U ≤
      LinearMap.range
        (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) :=
  iInf_le_of_le V (iInf_le_of_le h le_rfl)

/-- Relative norms carry universal norms at a deeper normal level to universal
norms at the target level. -/
theorem relativeNorm_mem_universalNormSubmodule
    (A : Rep.{u} R G) (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    {x : openSubgroupInvariants A V.toOpenSubgroup}
    (hx : x ∈ universalNormSubmodule A V) :
    relativeNorm A U.toOpenSubgroup V.toOpenSubgroup hVU x ∈
      universalNormSubmodule A U := by
  rw [mem_universalNormSubmodule_iff] at hx ⊢
  intro Z hZU
  let W : OpenNormalSubgroup G := V ⊓ Z
  have hWV : W ≤ V := inf_le_left
  have hWZ : W ≤ Z := inf_le_right
  obtain ⟨y, rfl⟩ := hx W hWV
  refine ⟨relativeNorm A Z.toOpenSubgroup W.toOpenSubgroup hWZ y, ?_⟩
  calc
    relativeNorm A U.toOpenSubgroup Z.toOpenSubgroup hZU
        (relativeNorm A Z.toOpenSubgroup W.toOpenSubgroup hWZ y) =
      relativeNorm A U.toOpenSubgroup W.toOpenSubgroup (hWZ.trans hZU) y := by
        simpa only [LinearMap.comp_apply] using congrArg (fun f => f y)
          (relativeNorm_comp A U.toOpenSubgroup Z.toOpenSubgroup
            W.toOpenSubgroup hWZ hZU)
    _ = relativeNorm A U.toOpenSubgroup V.toOpenSubgroup hVU
        (relativeNorm A V.toOpenSubgroup W.toOpenSubgroup hWV y) := by
      symm
      simpa only [LinearMap.comp_apply] using congrArg (fun f => f y)
        (relativeNorm_comp A U.toOpenSubgroup V.toOpenSubgroup
          W.toOpenSubgroup hWV hVU)

/-- The universal-norm submodule is stable under the residual quotient action. -/
theorem universalNormSubmodule_stable
    (A : Rep.{u} R G) (U : OpenNormalSubgroup G)
    (q : G ⧸ U.toSubgroup)
    {x : openSubgroupInvariants A U.toOpenSubgroup}
    (hx : x ∈ universalNormSubmodule A U) :
    (A.quotientToInvariants U.toSubgroup).ρ q x ∈
      universalNormSubmodule A U := by
  rw [mem_universalNormSubmodule_iff] at hx ⊢
  intro V h
  exact relativeNorm_range_quotientToInvariants_stable A U V h q (hx V h)

/-- Universal norms at `U`, as a subrepresentation of the residual
`G / U`-representation on `A^U`. -/
@[expose] def universalNormSubrepresentation (A : Rep.{u} R G)
    (U : OpenNormalSubgroup G) :
    Subrepresentation ((A.quotientToInvariants U.toSubgroup).ρ) where
  toSubmodule := universalNormSubmodule A U
  apply_mem_toSubmodule q _ hx := universalNormSubmodule_stable A U q hx

@[simp]
theorem universalNormSubrepresentation_toSubmodule
    (A : Rep.{u} R G) (U : OpenNormalSubgroup G) :
    (universalNormSubrepresentation A U).toSubmodule =
      universalNormSubmodule A U :=
  rfl

/-- Universal norms form a closed submodule for the level topology. -/
theorem isClosed_universalNormSubmodule (A : Rep.{u} R G) (L : LevelCompact A)
    (U : OpenNormalSubgroup G) :
    @IsClosed (openSubgroupInvariants A U.toOpenSubgroup)
      (L.topology U.toOpenSubgroup) (universalNormSubmodule A U : Set _) := by
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  let _ : T2Space (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.t2 U.toOpenSubgroup
  simp only [universalNormSubmodule, Submodule.coe_iInf]
  apply isClosed_iInter
  intro V
  apply isClosed_iInter
  intro h
  let _ : TopologicalSpace (openSubgroupInvariants A V.toOpenSubgroup) :=
    L.topology V.toOpenSubgroup
  let _ : CompactSpace (openSubgroupInvariants A V.toOpenSubgroup) :=
    L.compact V.toOpenSubgroup
  rw [LinearMap.coe_range]
  exact (isCompact_range
    (continuous_relativeNorm A L U.toOpenSubgroup V.toOpenSubgroup h)).isClosed

/-- A compatible choice of closed residual subrepresentation at every open
normal level, containing the universal norms and preserved by relative norms.

The topology on each chosen coefficient module is inherited from the supplied
`LevelCompact` topology; no topology on the ambient representation or scalar
ring is required. -/
structure RestrictedLevelSystem (A : Rep.{u} R G) (L : LevelCompact A) where
  /-- The chosen `G / U`-stable coefficient submodule at level `U`. -/
  subrepresentation : ∀ U : OpenNormalSubgroup G,
    Subrepresentation ((A.quotientToInvariants U.toSubgroup).ρ)
  /-- Every universal norm belongs to the chosen coefficient system. -/
  universalNorm_le : ∀ U,
    universalNormSubmodule A U ≤ (subrepresentation U).toSubmodule
  /-- Relative norms preserve the chosen coefficient system. -/
  relativeNorm_mem : ∀ (U V : OpenNormalSubgroup G) (h : V ≤ U)
    {x : openSubgroupInvariants A V.toOpenSubgroup},
    x ∈ subrepresentation V →
      relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x ∈
        subrepresentation U
  /-- Each chosen coefficient submodule is closed in its level topology. -/
  isClosed : ∀ U,
    @IsClosed (openSubgroupInvariants A U.toOpenSubgroup)
      (L.topology U.toOpenSubgroup) (subrepresentation U : Set _)

namespace RestrictedLevelSystem

variable {A : Rep.{u} R G} {L : LevelCompact A}

open CategoryTheory

/-- The coefficient module selected at an open normal level. -/
abbrev coefficients (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) :=
  (S.subrepresentation U).toSubmodule

/-- The topology inherited by a restricted coefficient module from the full
invariant module at the same level. -/
abbrev topology (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) :
    TopologicalSpace (S.coefficients U) :=
  (L.topology U.toOpenSubgroup).induced
    ((↑) : S.coefficients U → openSubgroupInvariants A U.toOpenSubgroup)

/-- A restricted coefficient module is Hausdorff in its inherited topology. -/
noncomputable abbrev t2 (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @T2Space (S.coefficients U) (S.topology U) := by
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  let _ : T2Space (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.t2 U.toOpenSubgroup
  exact inferInstance

/-- A restricted coefficient module is compact in its inherited topology. -/
noncomputable abbrev compact (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @CompactSpace (S.coefficients U) (S.topology U) := by
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  let _ : CompactSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.compact U.toOpenSubgroup
  exact isCompact_iff_compactSpace.mp (S.isClosed U).isCompact

/-- Addition and negation are continuous on a restricted coefficient module. -/
noncomputable abbrev topologicalAddGroup (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) :
    @IsTopologicalAddGroup (S.coefficients U) (S.topology U) _ := by
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  let _ : IsTopologicalAddGroup (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topologicalAddGroup U.toOpenSubgroup
  exact inferInstance

/-- The compact Hausdorff additive group carried by a restricted coefficient
module at one open normal level. Its carrier and inherited topology are exposed
so ordinary importing modules can construct continuous maps on the chosen
coefficient subtype. -/
@[expose] noncomputable def group (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) : CompHausAddCommGrp.{u} := by
  let _ : TopologicalSpace (S.coefficients U) := S.topology U
  let _ : T2Space (S.coefficients U) := S.t2 U
  let _ : CompactSpace (S.coefficients U) := S.compact U
  let _ : IsTopologicalAddGroup (S.coefficients U) := S.topologicalAddGroup U
  exact CompHausAddCommGrp.of (S.coefficients U)

/-- A relative norm restricted to the chosen coefficient modules. -/
@[expose] def relativeNorm (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    S.coefficients V →ₗ[R] S.coefficients U where
  toFun x := ⟨LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x,
    S.relativeNorm_mem U V h x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

@[simp]
theorem relativeNorm_coe (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) (x : S.coefficients V) :
    (S.relativeNorm U V h x : openSubgroupInvariants A U.toOpenSubgroup) =
      LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x :=
  rfl

/-- Restricted relative norms compose through a tower of open normal levels. -/
theorem relativeNorm_comp (S : RestrictedLevelSystem A L)
    (U V W : OpenNormalSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) :
    (S.relativeNorm U V hVU).comp (S.relativeNorm V W hWV) =
      S.relativeNorm U W (hWV.trans hVU) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change ((LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup hVU
      (LevelCompact.relativeNorm A V.toOpenSubgroup W.toOpenSubgroup hWV x) :
        openSubgroupInvariants A U.toOpenSubgroup) : A) =
    (LevelCompact.relativeNorm A U.toOpenSubgroup W.toOpenSubgroup
      (hWV.trans hVU) x : A)
  exact congrArg
    (fun f => ((f (x : openSubgroupInvariants A W.toOpenSubgroup) :
      openSubgroupInvariants A U.toOpenSubgroup) : A))
    (LevelCompact.relativeNorm_comp A U.toOpenSubgroup V.toOpenSubgroup
      W.toOpenSubgroup hWV hVU)

/-- Restricted relative norms are continuous for the inherited topologies. -/
theorem continuous_relativeNorm (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    @Continuous (S.coefficients V) (S.coefficients U)
      (S.topology V) (S.topology U) (S.relativeNorm U V h) := by
  let _ : TopologicalSpace (S.coefficients V) := S.topology V
  let _ : TopologicalSpace (openSubgroupInvariants A V.toOpenSubgroup) :=
    L.topology V.toOpenSubgroup
  let _ : TopologicalSpace (openSubgroupInvariants A U.toOpenSubgroup) :=
    L.topology U.toOpenSubgroup
  apply continuous_induced_rng.2
  exact (LevelCompact.continuous_relativeNorm A L U.toOpenSubgroup
    V.toOpenSubgroup h).comp continuous_subtype_val

/-- A restricted relative norm as a morphism of compact Hausdorff additive
groups. -/
def relativeNormHom (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    S.group V ⟶ S.group U := by
  apply ConcreteCategory.ofHom
  exact
    { toAddMonoidHom := (S.relativeNorm U V h).toAddMonoidHom
      continuous_toFun := S.continuous_relativeNorm U V h }

/-- The bundled relative norm evaluates as the existing restricted linear map.
This equation does not require exposing the morphism's implementation. -/
theorem relativeNormHom_apply (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) (x : S.coefficients V) :
    S.relativeNormHom U V h x = S.relativeNorm U V h x :=
  by rfl

end RestrictedLevelSystem

/-- The unrestricted system choosing the full invariant module at every open
normal level. -/
@[expose] def fullRestrictedLevelSystem (A : Rep.{u} R G) (L : LevelCompact A) :
    RestrictedLevelSystem A L where
  subrepresentation _ := ⊤
  universalNorm_le _ := le_top
  relativeNorm_mem := by
    intro U V h x hx
    trivial
  isClosed U := @isClosed_univ _ (L.topology U.toOpenSubgroup)

/-- The canonical restricted system consisting exactly of universal norms. -/
@[expose] def universalNormRestrictedLevelSystem (A : Rep.{u} R G) (L : LevelCompact A) :
    RestrictedLevelSystem A L where
  subrepresentation := universalNormSubrepresentation A
  universalNorm_le U := by
    rw [universalNormSubrepresentation_toSubmodule]
  relativeNorm_mem U V h _ hx :=
    relativeNorm_mem_universalNormSubmodule A U V h hx
  isClosed := isClosed_universalNormSubmodule A L

@[simp]
theorem fullRestrictedLevelSystem_subrepresentation
    (A : Rep.{u} R G) (L : LevelCompact A) (U : OpenNormalSubgroup G) :
    (fullRestrictedLevelSystem A L).subrepresentation U = ⊤ :=
  rfl

@[simp]
theorem universalNormRestrictedLevelSystem_subrepresentation
    (A : Rep.{u} R G) (L : LevelCompact A) (U : OpenNormalSubgroup G) :
    (universalNormRestrictedLevelSystem A L).subrepresentation U =
      universalNormSubrepresentation A U :=
  rfl

end ContinuousGroupCohomology.LevelCompact
