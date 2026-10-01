/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon (Source Maintainer)
-/
module

public import ContinuousGroupCohomology.RestrictedLevelCompact
public import ContinuousGroupCohomology.LevelCompactFunctoriality
public import ContinuousGroupCohomology.CompactExceptionalTateCoefficientMaps

/-!
# Functoriality of restricted level-compact coefficient systems

A morphism between chosen restricted systems is a level-compact representation
morphism preserving the selected subrepresentation at each open normal level.
Full-invariant and universal-norm systems give functors from all level-compact
representations. The latter needs no extra preservation hypothesis: a witness
in each relative-norm range transports along naturality of the relative norm.

The resulting maps on selected coefficients are linear and continuous for
their inherited level topologies, and commute with restricted relative norms.
They induce maps of the actual selected compact groups and natural transformations
of the native restricted norm diagrams. No topology on the ambient coefficient
module or scalar ring is required.
-/

public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

noncomputable section

namespace ContinuousGroupCohomology

universe u

variable (R G : Type u) [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- A level-compact representation with a chosen restricted coefficient system. -/
structure RestrictedLevelCompactRep where
  /-- The underlying level-compact representation. -/
  toLevelCompactRep : LevelCompactRep.{u, u, u} R G
  /-- The chosen closed residual subrepresentation at every open normal level. -/
  system : LevelCompact.RestrictedLevelSystem toLevelCompactRep.rep
    toLevelCompactRep.levelCompact

namespace RestrictedLevelCompactRep

variable {R G}

/-- The underlying representation. -/
abbrev rep (A : RestrictedLevelCompactRep R G) := A.toLevelCompactRep.rep

/-- The levelwise compact topology data. -/
abbrev levelCompact (A : RestrictedLevelCompactRep R G) :=
  A.toLevelCompactRep.levelCompact

/-- The full-invariant restricted system. -/
@[expose] def full (A : LevelCompactRep.{u, u, u} R G) :
    RestrictedLevelCompactRep R G where
  toLevelCompactRep := A
  system := LevelCompact.fullRestrictedLevelSystem A.rep A.levelCompact

/-- The canonical universal-norm restricted system. -/
@[expose] def universalNorm (A : LevelCompactRep.{u, u, u} R G) :
    RestrictedLevelCompactRep R G where
  toLevelCompactRep := A
  system := LevelCompact.universalNormRestrictedLevelSystem A.rep A.levelCompact

/-- A level-compact coefficient morphism preserving each chosen restricted
coefficient module. -/
@[ext]
structure Hom (A B : RestrictedLevelCompactRep R G) where
  /-- The underlying level-compact morphism. -/
  hom : A.toLevelCompactRep ⟶ B.toLevelCompactRep
  /-- Preservation of the selected subrepresentation at each level. -/
  map_mem : ∀ (U : OpenNormalSubgroup G)
    (x : openSubgroupInvariants A.rep U.toOpenSubgroup),
    x ∈ A.system.subrepresentation U →
      LevelCompactRep.mapInvariants hom U.toOpenSubgroup x ∈
        B.system.subrepresentation U

private lemma mapInvariants_id
    (A : RestrictedLevelCompactRep R G) (U : OpenNormalSubgroup G) :
    LevelCompactRep.mapInvariants
        (𝟙 A.toLevelCompactRep) U.toOpenSubgroup = LinearMap.id := by
  change ((Rep.invariantsFunctor R U.toOpenSubgroup).map
      ((Rep.resFunctor U.toOpenSubgroup.subtype).map
        (𝟙 A.rep))).hom = LinearMap.id
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

private lemma mapInvariants_comp
    {A B C : RestrictedLevelCompactRep R G}
    (f : A.toLevelCompactRep ⟶ B.toLevelCompactRep)
    (g : B.toLevelCompactRep ⟶ C.toLevelCompactRep)
    (U : OpenNormalSubgroup G) :
    LevelCompactRep.mapInvariants (f ≫ g) U.toOpenSubgroup =
      (LevelCompactRep.mapInvariants g U.toOpenSubgroup).comp
        (LevelCompactRep.mapInvariants f U.toOpenSubgroup) := by
  change ((Rep.invariantsFunctor R U.toOpenSubgroup).map
      ((Rep.resFunctor U.toOpenSubgroup.subtype).map
        (f.hom ≫ g.hom))).hom = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

instance : Category (RestrictedLevelCompactRep R G) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.toLevelCompactRep
      map_mem := by
        intro U x hx
        rw [mapInvariants_id A U]
        exact hx }
  comp {A B C} f g :=
    { hom := f.hom ≫ g.hom
      map_mem := by
        intro U x hx
        rw [mapInvariants_comp f.hom g.hom U]
        exact g.map_mem U _ (f.map_mem U x hx) }

/-- Forget the chosen restricted system, retaining the levelwise topology. -/
@[simps, expose]
def forget : RestrictedLevelCompactRep R G ⥤ LevelCompactRep R G where
  obj A := A.toLevelCompactRep
  map f := f.hom

instance : (forget (R := R) (G := G)).Faithful where
  map_injective {_ _} _ _ h := Hom.ext h

/-- The full-invariant restricted system is functorial on all level-compact
coefficient morphisms. -/
@[expose] def fullFunctor : LevelCompactRep.{u, u, u} R G ⥤
    RestrictedLevelCompactRep R G where
  obj A := full A
  map f :=
    { hom := f
      map_mem := by
        intro U x hx
        trivial }

/-- Universal norms are preserved because every deeper norm witness maps to
a witness in the corresponding target relative-norm range. -/
lemma mapInvariants_mem_universalNorm
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (U : OpenNormalSubgroup G)
    {x : openSubgroupInvariants A.rep U.toOpenSubgroup}
    (hx : x ∈ LevelCompact.universalNormSubmodule A.rep U) :
    LevelCompactRep.mapInvariants f U.toOpenSubgroup x ∈
      LevelCompact.universalNormSubmodule B.rep U := by
  rw [LevelCompact.mem_universalNormSubmodule_iff] at hx ⊢
  intro V hVU
  obtain ⟨y, rfl⟩ := hx V hVU
  refine ⟨LevelCompactRep.mapInvariants f V.toOpenSubgroup y, ?_⟩
  exact (LevelCompactRep.mapInvariants_relativeNorm f U.toOpenSubgroup
    V.toOpenSubgroup hVU y).symm

/-- The universal-norm restricted system is functorial on every level-compact
coefficient morphism, without an extra preservation assumption. -/
@[expose] def universalNormFunctor : LevelCompactRep.{u, u, u} R G ⥤
    RestrictedLevelCompactRep R G where
  obj A := universalNorm A
  map f :=
    { hom := f
      map_mem := by
        intro U x hx
        exact mapInvariants_mem_universalNorm f U hx }

variable {A B C : RestrictedLevelCompactRep R G}

/-- The map induced on selected coefficient modules at an open normal level. -/
@[expose] def coefficientMap (f : A ⟶ B) (U : OpenNormalSubgroup G) :
    A.system.coefficients U →ₗ[R] B.system.coefficients U where
  toFun x := ⟨LevelCompactRep.mapInvariants f.hom U.toOpenSubgroup x,
    f.map_mem U x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

@[simp]
lemma coefficientMap_coe (f : A ⟶ B) (U : OpenNormalSubgroup G)
    (x : A.system.coefficients U) :
    (coefficientMap f U x : openSubgroupInvariants B.rep U.toOpenSubgroup) =
      LevelCompactRep.mapInvariants f.hom U.toOpenSubgroup x :=
  rfl

/-- The map on coefficients is continuous for the inherited level topologies. -/
lemma continuous_coefficientMap (f : A ⟶ B) (U : OpenNormalSubgroup G) :
    @Continuous (A.system.coefficients U) (B.system.coefficients U)
      (A.system.topology U) (B.system.topology U)
      (coefficientMap f U) := by
  let _ : TopologicalSpace
      (openSubgroupInvariants A.rep U.toOpenSubgroup) :=
    A.levelCompact.topology U.toOpenSubgroup
  let _ : TopologicalSpace
      (openSubgroupInvariants B.rep U.toOpenSubgroup) :=
    B.levelCompact.topology U.toOpenSubgroup
  apply continuous_induced_rng.2
  exact (LevelCompactRep.continuous_mapInvariants f.hom U.toOpenSubgroup).comp
    continuous_subtype_val

@[simp]
lemma coefficientMap_id (A : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G) :
    coefficientMap (𝟙 A) U = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change LevelCompactRep.mapInvariants
    (𝟙 A.toLevelCompactRep) U.toOpenSubgroup x = x
  rw [mapInvariants_id]
  rfl

@[simp]
lemma coefficientMap_comp (f : A ⟶ B) (g : B ⟶ C)
    (U : OpenNormalSubgroup G) :
    coefficientMap (f ≫ g) U =
      (coefficientMap g U).comp (coefficientMap f U) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change LevelCompactRep.mapInvariants
      (f.hom ≫ g.hom) U.toOpenSubgroup x =
    coefficientMap g U (coefficientMap f U x)
  rw [mapInvariants_comp]
  rfl

/-- The restricted coefficient map commutes with relative norms. -/
lemma coefficientMap_relativeNorm (f : A ⟶ B)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U)
    (x : A.system.coefficients V) :
    coefficientMap f U (A.system.relativeNorm U V hVU x) =
      B.system.relativeNorm U V hVU (coefficientMap f V x) := by
  apply Subtype.ext
  exact LevelCompactRep.mapInvariants_relativeNorm f.hom U.toOpenSubgroup
    V.toOpenSubgroup hVU x

/-- Naturality of restricted relative norms as linear maps. -/
lemma coefficientMap_relativeNorm_linear (f : A ⟶ B)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    (B.system.relativeNorm U V hVU).comp (coefficientMap f V) =
      (coefficientMap f U).comp (A.system.relativeNorm U V hVU) := by
  apply LinearMap.ext
  intro x
  exact (coefficientMap_relativeNorm f U V hVU x).symm

/-- The continuous map of the actual selected compact coefficient groups. -/
@[expose] def groupMap (f : A ⟶ B) (U : OpenNormalSubgroup G) :
    A.system.group U ⟶ B.system.group U := by
  apply ConcreteCategory.ofHom
  exact { toAddMonoidHom := (coefficientMap f U).toAddMonoidHom
          continuous_toFun := continuous_coefficientMap f U }

/-- Evaluation of the compact-group morphism on a selected coefficient. -/
@[simp]
theorem groupMap_apply (f : A ⟶ B) (U : OpenNormalSubgroup G)
    (x : A.system.coefficients U) :
    groupMap f U x = coefficientMap f U x :=
  by rfl

@[simp]
theorem groupMap_id (A : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G) : groupMap (𝟙 A) U = 𝟙 (A.system.group U) := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  change coefficientMap (𝟙 A) U x = x
  rw [coefficientMap_id]
  rfl

@[simp]
theorem groupMap_comp (f : A ⟶ B) (g : B ⟶ C)
    (U : OpenNormalSubgroup G) :
    groupMap (f ≫ g) U = groupMap f U ≫ groupMap g U := by
  apply CompHausAddCommGrp.hom_ext
  apply ContinuousAddMonoidHom.ext
  intro x
  change coefficientMap (f ≫ g) U x =
    coefficientMap g U (coefficientMap f U x)
  rw [coefficientMap_comp]
  rfl

/-- The compact-group norm square, from the selected `V` group of `A` to
the selected `U` group of `B`. -/
theorem groupMap_relativeNorm (f : A ⟶ B)
    (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    A.system.relativeNormHom U V hVU ≫ groupMap f U =
      groupMap f V ≫ B.system.relativeNormHom U V hVU := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  change groupMap f U (A.system.relativeNormHom U V hVU x) =
    B.system.relativeNormHom U V hVU (groupMap f V x)
  let y : A.system.coefficients V := x
  have step1 := groupMap_apply f U (A.system.relativeNormHom U V hVU y)
  have step2 := congrArg (coefficientMap f U)
    (A.system.relativeNormHom_apply U V hVU y)
  have step3 := coefficientMap_relativeNorm f U V hVU y
  have step4 := congrArg (B.system.relativeNorm U V hVU) (groupMap_apply f V y)
  have step5 := (B.system.relativeNormHom_apply U V hVU (groupMap f V y)).symm
  exact step1.trans (step2.trans (step3.trans (step4.symm.trans step5)))

/-- The native diagram of selected compact coefficient groups and relative norms.
An arrow `V ⟶ U` represents `V ≤ U` and acts by the genuine relative norm. -/
@[expose] def restrictedNormDiagram (A : RestrictedLevelCompactRep R G) :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj U := A.system.group U
  map {V U} hVU := A.system.relativeNormHom U V (leOfHom hVU)
  map_id U := by
    apply CompHausAddCommGrp.hom_ext
    ext x
    let y : A.system.coefficients U := x
    change A.system.relativeNormHom U U le_rfl x = x
    refine (A.system.relativeNormHom_apply U U le_rfl y).trans ?_
    apply Subtype.ext
    change LevelCompact.relativeNorm A.rep U.toOpenSubgroup
      U.toOpenSubgroup le_rfl y = y
    rw [LevelCompact.relativeNorm_refl]
    rfl
  map_comp {W V U} hWV hVU := by
    apply CompHausAddCommGrp.hom_ext
    ext x
    let y : A.system.coefficients W := x
    change A.system.relativeNormHom U W (leOfHom (hWV ≫ hVU)) x =
      A.system.relativeNormHom U V (leOfHom hVU)
        (A.system.relativeNormHom V W (leOfHom hWV) x)
    have step1 := A.system.relativeNormHom_apply U V (leOfHom hVU)
      (A.system.relativeNormHom V W (leOfHom hWV) y)
    have step2 := congrArg (A.system.relativeNorm U V (leOfHom hVU))
      (A.system.relativeNormHom_apply V W (leOfHom hWV) y)
    have step3 := congrArg (fun norm => norm y)
      (A.system.relativeNorm_comp U V W (leOfHom hWV) (leOfHom hVU))
    have step4 := (A.system.relativeNormHom_apply U W (leOfHom (hWV ≫ hVU)) y).symm
    exact (step1.trans (step2.trans (step3.trans step4))).symm

@[simp]
theorem restrictedNormDiagram_obj (A : RestrictedLevelCompactRep R G)
    (U : OpenNormalSubgroup G) :
    (restrictedNormDiagram A).obj U = A.system.group U := rfl

@[simp]
theorem restrictedNormDiagram_map (A : RestrictedLevelCompactRep R G)
    {V U : OpenNormalSubgroup G} (hVU : V ⟶ U) :
    (restrictedNormDiagram A).map hVU =
      A.system.relativeNormHom U V (leOfHom hVU) := rfl

/-- Coefficient maps give natural transformations of the actual norm diagrams. -/
@[expose] def restrictedNormDiagramMap (f : A ⟶ B) :
    restrictedNormDiagram A ⟶ restrictedNormDiagram B where
  app U := groupMap f U
  naturality {V U} hVU := groupMap_relativeNorm f U V (leOfHom hVU)

@[simp]
theorem restrictedNormDiagramMap_app (f : A ⟶ B)
    (U : OpenNormalSubgroup G) :
    (restrictedNormDiagramMap f).app U = groupMap f U := rfl

/-- Functoriality of native compact restricted relative-norm diagrams on the
existing category of selected systems and preservation morphisms. -/
@[expose] def restrictedNormDiagramFunctor :
    RestrictedLevelCompactRep R G ⥤
      (OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u}) where
  obj A := restrictedNormDiagram A
  map f := restrictedNormDiagramMap f
  map_id A := by
    apply NatTrans.ext
    funext U
    exact groupMap_id A U
  map_comp f g := by
    apply NatTrans.ext
    funext U
    exact groupMap_comp f g U

@[simp]
theorem restrictedNormDiagramFunctor_obj (A : RestrictedLevelCompactRep R G) :
    restrictedNormDiagramFunctor.obj A = restrictedNormDiagram A := rfl

@[simp]
theorem restrictedNormDiagramFunctor_map_app (f : A ⟶ B)
    (U : OpenNormalSubgroup G) :
    (restrictedNormDiagramFunctor.map f).app U = groupMap f U := rfl

end RestrictedLevelCompactRep

end ContinuousGroupCohomology
