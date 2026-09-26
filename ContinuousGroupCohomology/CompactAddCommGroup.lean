/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact Hausdorff topological additive commutative groups

This file packages compact Hausdorff topological additive commutative groups
and continuous additive homomorphisms.  Unlike `ProfiniteAddGrp`, no total
disconnectedness hypothesis is imposed.

The closed-kernel and compact-range quotient constructions are included
explicitly.  They are the topological group operations needed to put honest
compact Hausdorff topologies on kernel/cokernel presentations without choosing
a topology on a coefficient ring.
-/

set_option warningAsError true

public section

open CategoryTheory

universe u

/-- The category of compact Hausdorff topological additive commutative groups. -/
@[pp_with_univ]
structure CompHausAddCommGrp where
  /-- The underlying compact Hausdorff space. -/
  toCompHaus : CompHaus.{u}
  /-- The additive commutative group structure. -/
  [addCommGroup : AddCommGroup toCompHaus]
  /-- Addition and negation are continuous. -/
  [isTopologicalAddGroup : IsTopologicalAddGroup toCompHaus]

instance : CoeSort CompHausAddCommGrp (Type u) where
  coe A := A.toCompHaus

attribute [instance] CompHausAddCommGrp.addCommGroup
  CompHausAddCommGrp.isTopologicalAddGroup

namespace CompHausAddCommGrp

/-- Bundle a compact Hausdorff topological additive commutative group. -/
abbrev of (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] :
    CompHausAddCommGrp.{u} where
  toCompHaus := CompHaus.of A
  addCommGroup := ‹_›
  isTopologicalAddGroup := ‹_›

@[simp]
lemma coe_of (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] :
    (of A : Type u) = A :=
  rfl

/-- Morphisms of compact Hausdorff topological additive commutative groups. -/
@[ext]
structure Hom (A B : CompHausAddCommGrp.{u}) where
  /-- The underlying continuous additive homomorphism. -/
  hom' : A →ₜ+ B

instance : Category CompHausAddCommGrp where
  Hom A B := Hom A B
  id A := ⟨ContinuousAddMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory CompHausAddCommGrp (fun A B ↦ A →ₜ+ B) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The continuous additive homomorphism underlying a morphism. -/
abbrev Hom.hom {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : A →ₜ+ B :=
  ConcreteCategory.hom (C := CompHausAddCommGrp) f

/-- Typecheck a continuous additive homomorphism as a categorical morphism. -/
abbrev ofHom {A B : Type u} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [CompactSpace B] [T2Space B] (f : A →ₜ+ B) : of A ⟶ of B :=
  ConcreteCategory.ofHom f

instance {A B : CompHausAddCommGrp.{u}} : CoeFun (A ⟶ B) (fun _ ↦ A → B) where
  coe f := f.hom

@[simp]
lemma hom_id {A : CompHausAddCommGrp.{u}} :
    (𝟙 A : A ⟶ A).hom = ContinuousAddMonoidHom.id A :=
  rfl

@[simp]
lemma hom_comp {A B C : CompHausAddCommGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CompHausAddCommGrp.{u}} {f g : A ⟶ B}
    (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- Forget a compact Hausdorff topological additive commutative group to its
underlying compact Hausdorff space. -/
instance : HasForget₂ CompHausAddCommGrp CompHaus where
  forget₂ :=
    { obj A := A.toCompHaus
      map f := CompHausLike.ofHom _ ⟨f, f.hom.continuous⟩ }

instance : (forget₂ CompHausAddCommGrp CompHaus).Faithful where
  map_injective {_ _} _ _ h := by
    apply hom_ext
    ext x
    exact CategoryTheory.congr_fun h x

/-- Forget to the underlying additive commutative group. -/
instance : HasForget₂ CompHausAddCommGrp AddCommGrpCat where
  forget₂ :=
    { obj A := AddCommGrpCat.of A
      map f := AddCommGrpCat.ofHom f.hom.toAddMonoidHom }

/-- A closed additive subgroup of a compact Hausdorff additive commutative
group is again a compact Hausdorff additive commutative group. -/
noncomputable abbrev ofClosedAddSubgroup (A : CompHausAddCommGrp.{u})
    (H : ClosedAddSubgroup A) : CompHausAddCommGrp.{u} := by
  let _ : CompactSpace H.toAddSubgroup :=
    isCompact_iff_compactSpace.mp H.isClosed'.isCompact
  exact of H.toAddSubgroup

/-- The quotient by a closed additive subgroup, with its quotient topology. -/
noncomputable abbrev quotient (A : CompHausAddCommGrp.{u})
    (H : ClosedAddSubgroup A) : CompHausAddCommGrp.{u} := by
  let _ : IsClosed (H.toAddSubgroup : Set A) := H.isClosed'
  exact of (A ⧸ H.toAddSubgroup)

/-- The kernel of a continuous additive homomorphism as a closed additive
subgroup. -/
@[expose] def kernelClosedAddSubgroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    ClosedAddSubgroup A where
  toAddSubgroup := f.hom.ker
  isClosed' := by
    change IsClosed (f ⁻¹' {0})
    exact IsClosed.preimage f.hom.continuous isClosed_singleton

/-- The compact Hausdorff group carried by the kernel of a continuous additive
homomorphism. -/
noncomputable abbrev kernelGroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    CompHausAddCommGrp.{u} :=
  ofClosedAddSubgroup A (kernelClosedAddSubgroup f)

/-- The range of a continuous homomorphism from a compact space is a closed
additive subgroup of the Hausdorff target. -/
@[expose] def rangeClosedAddSubgroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    ClosedAddSubgroup B where
  toAddSubgroup := f.hom.range
  isClosed' := by
    change IsClosed (Set.range f)
    exact (isCompact_range f.hom.continuous).isClosed

/-- The compact Hausdorff quotient of the target by the range of a continuous
additive homomorphism. -/
noncomputable abbrev quotientRange {A B : CompHausAddCommGrp.{u}}
    (f : A ⟶ B) : CompHausAddCommGrp.{u} :=
  quotient B (rangeClosedAddSubgroup f)

/-- The canonical inclusion of the compact Hausdorff kernel. -/
@[expose] noncomputable def kernelι {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    kernelGroup f ⟶ A := by
  apply ConcreteCategory.ofHom
  change f.hom.ker →ₜ+ A
  exact
    { toAddMonoidHom := f.hom.ker.subtype
      continuous_toFun := continuous_subtype_val }

/-- The canonical projection to the compact Hausdorff quotient by the range. -/
@[expose] noncomputable def quotientRangeπ {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) :
    B ⟶ quotientRange f :=
  ConcreteCategory.ofHom
    { toAddMonoidHom := QuotientAddGroup.mk' f.hom.range
      continuous_toFun := QuotientAddGroup.continuous_mk }

@[simp]
lemma kernelι_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B)
    (x : kernelGroup f) : kernelι f x = (x : A) :=
  rfl

@[simp]
lemma comp_kernelι_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B)
    (x : kernelGroup f) : f (kernelι f x) = 0 :=
  x.2

@[simp]
lemma quotientRangeπ_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : B) :
    quotientRangeπ f x = QuotientAddGroup.mk x :=
  rfl

@[simp]
lemma quotientRangeπ_comp_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : A) :
    quotientRangeπ f (f x) = 0 := by
  change QuotientAddGroup.mk' f.hom.range (f x) = 0
  rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
  exact ⟨x, rfl⟩

/-- A continuous commutative square induces a continuous map on closed
kernels. -/
@[expose] noncomputable def kernelMap {X Y X' Y' : CompHausAddCommGrp.{u}}
    (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x, g (p x) = q (f x)) : kernelGroup f ⟶ kernelGroup g := by
  have hker (x : kernelGroup f) : g (p x) = 0 := by
    have hx : f (x : X) = 0 := x.2
    rw [h x, hx, map_zero]
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom :=
        { toFun := fun x ↦ ⟨p x, hker x⟩
          map_zero' := by ext; simp
          map_add' := by intro x y; ext; simp }
      continuous_toFun := ?_ }
  exact (p.hom.continuous.comp continuous_subtype_val).subtype_mk _

/-- A continuous commutative square induces a continuous map on quotients by
the two compact ranges. -/
@[expose] noncomputable def quotientRangeMap {X Y X' Y' : CompHausAddCommGrp.{u}}
    (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x, g (p x) = q (f x)) : quotientRange f ⟶ quotientRange g := by
  let φ : Y →+ quotientRange g :=
    (QuotientAddGroup.mk' g.hom.range).comp q.hom.toAddMonoidHom
  have hφ : f.hom.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    change QuotientAddGroup.mk' g.hom.range (q (f x)) = 0
    rw [← h x, ← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact ⟨p x, rfl⟩
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom := QuotientAddGroup.lift f.hom.range φ hφ
      continuous_toFun := ?_ }
  apply continuous_coinduced_dom.2
  exact (quotientRangeπ g).hom.continuous.comp q.hom.continuous

@[simp]
lemma kernelMap_apply {X Y X' Y' : CompHausAddCommGrp.{u}}
    (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x, g (p x) = q (f x)) (x : kernelGroup f) :
    kernelMap p q f g h x =
      ⟨p x, by
        change g (p x) = 0
        have hx : f (x : X) = 0 := x.2
        rw [h x, hx, map_zero]⟩ :=
  rfl

@[simp]
lemma quotientRangeMap_mk {X Y X' Y' : CompHausAddCommGrp.{u}}
    (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x, g (p x) = q (f x)) (y : Y) :
    quotientRangeMap p q f g h (QuotientAddGroup.mk y) =
      QuotientAddGroup.mk (q y) :=
  rfl

end CompHausAddCommGrp
