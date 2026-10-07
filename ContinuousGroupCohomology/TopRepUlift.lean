/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.TopModuleCatUlift
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Universe lifts of topological representations

This file raises both the acting monoid and the carrier of a topological
representation through independently chosen `ULift` universes. It packages
the construction as a functor, identifies the lifted action with restriction
of the original action along the canonical lift equivalence, and shows that
joint continuity of the action is preserved and reflected.
-/

set_option warningAsError true

@[expose] public section

universe u v v' w w'

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Monoid G]

/-- The action carried by a topological representation is jointly continuous. -/
class JointlyContinuous [TopologicalSpace G] (X : TopRep.{w} k G) : Prop where
  continuous_action : Continuous fun p : G × X => X.ρ p.1 p.2

/-- Simultaneously raise the universes of the acting monoid and the carrier of
a topological representation. -/
def ulift (X : TopRep.{w} k G) :
    TopRep.{max w w'} k (ULift.{v'} G) :=
  let e : ULift.{w'} X ≃L[k] X := ContinuousLinearEquiv.ulift
  .of <| .ofMonoidHom
    { toFun := fun g => e.symm.toContinuousLinearMap.comp
          ((X.ρ g.down).comp e.toContinuousLinearMap)
      map_one' := by
        ext x
        simp [e]
      map_mul' := by
        intro g h
        ext x
        simp [e] }

@[simp]
lemma ulift_ρ_apply (X : TopRep.{w} k G) (g : ULift.{v'} G)
    (x : ULift.{w'} X) :
    ((X.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ g x) =
      ULift.up (X.ρ g.down x.down) :=
  rfl

/-- Raise a morphism of topological representations together with its source
and target carriers and the acting monoid. -/
def uliftMap {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) ⟶
      (Y.ulift : TopRep.{max w w'} k (ULift.{v'} G)) :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        (show ULift.{w'} Y ≃L[k] Y from
          ContinuousLinearEquiv.ulift).symm.toContinuousLinearMap.comp
          (f.hom.toContinuousLinearMap.comp
            (show ULift.{w'} X ≃L[k] X from
              ContinuousLinearEquiv.ulift).toContinuousLinearMap)
      isIntertwining' := fun g => by
        ext x
        change f.hom (X.ρ g.down x.down) = Y.ρ g.down (f.hom x.down)
        exact f.hom.isIntertwining g.down x.down }

@[simp]
lemma uliftMap_apply {X Y : TopRep.{w} k G} (f : X ⟶ Y)
    (x : ULift.{w'} X) :
    (uliftMap f :
      (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) ⟶
        (Y.ulift : TopRep.{max w w'} k (ULift.{v'} G))) x =
      ULift.up (f.hom x.down) :=
  rfl

/-- Simultaneously raise the acting monoid and coefficient carrier of every
object and morphism in `TopRep`. -/
@[simps obj map, pp_with_univ]
def uliftFunctor :
    TopRep.{w} k G ⥤ TopRep.{max w w'} k (ULift.{v'} G) where
  obj := ulift
  map := uliftMap
  map_id X := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    ext x
    rfl
  map_comp f g := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    ext x
    rfl

instance instAdditiveUliftFunctor : (uliftFunctor (k := k) (G := G) :
    TopRep.{w} k G ⥤ TopRep.{max w w'} k (ULift.{v'} G)).Additive where

/-- The original representation, restricted along the canonical map from the
lifted acting monoid, is equivalent to the lifted coefficient representation. -/
def uliftEquiv (X : TopRep.{w} k G) :
    (X.ρ.restrict MulEquiv.ulift.toMonoidHom).Equiv
      (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ :=
  ContRepresentation.Equiv.mk
    (show X ≃L[k] ULift.{w'} X from ContinuousLinearEquiv.ulift.symm) fun g => by
      ext x
      rfl

@[simp]
lemma uliftEquiv_apply (X : TopRep.{w} k G) (x : X) :
    (X.uliftEquiv :
      (X.ρ.restrict (MulEquiv.ulift : ULift.{v'} G ≃* G).toMonoidHom).Equiv
        (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ) x = ULift.up x :=
  rfl

@[simp]
lemma uliftEquiv_symm_apply (X : TopRep.{w} k G) (x : ULift.{w'} X) :
    (X.uliftEquiv :
      (X.ρ.restrict (MulEquiv.ulift : ULift.{v'} G ≃* G).toMonoidHom).Equiv
        (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ).symm x = x.down :=
  rfl

@[simp]
lemma uliftEquiv_naturality {X Y : TopRep.{w} k G} (f : X ⟶ Y) (x : X) :
    (uliftMap f :
      (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) ⟶
        (Y.ulift : TopRep.{max w w'} k (ULift.{v'} G)))
          ((X.uliftEquiv :
            (X.ρ.restrict (MulEquiv.ulift : ULift.{v'} G ≃* G).toMonoidHom).Equiv
              (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ) x) =
      (Y.uliftEquiv :
        (Y.ρ.restrict (MulEquiv.ulift : ULift.{v'} G ≃* G).toMonoidHom).Equiv
          (Y.ulift : TopRep.{max w w'} k (ULift.{v'} G)).ρ) (f.hom x) :=
  rfl

section JointlyContinuous

variable [TopologicalSpace G]

/-- Joint continuity of an action is preserved when both the acting monoid
and the coefficient carrier are raised to independent universes. -/
instance jointlyContinuousUlift (X : TopRep.{w} k G) [JointlyContinuous X] :
    JointlyContinuous (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) where
  continuous_action := by
    have hdown : Continuous
        (fun p : ULift.{v'} G × ULift.{w'} X => (p.1.down, p.2.down)) :=
      (Homeomorph.ulift.continuous.comp continuous_fst).prodMk
        (Homeomorph.ulift.continuous.comp continuous_snd)
    exact Homeomorph.ulift.symm.continuous.comp
      (JointlyContinuous.continuous_action.comp hdown)

/-- Joint continuity of an action is equivalent to joint continuity after
raising the acting monoid and coefficient carrier to independent universes. -/
theorem jointlyContinuous_ulift_iff (X : TopRep.{w} k G) :
    JointlyContinuous (X.ulift : TopRep.{max w w'} k (ULift.{v'} G)) ↔
      JointlyContinuous X := by
  constructor
  · intro h
    constructor
    have hup : Continuous (fun p : G × X => (ULift.up p.1, ULift.up p.2)) :=
      (Homeomorph.ulift.symm.continuous.comp continuous_fst).prodMk
        (Homeomorph.ulift.symm.continuous.comp continuous_snd)
    exact Homeomorph.ulift.continuous.comp (h.continuous_action.comp hup)
  · intro h
    let _ := h
    infer_instance

end JointlyContinuous

end TopRep

namespace TopRep

open scoped Topology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Joint continuity of a representation's action extends to its coinduced action
when the group is locally compact. -/
theorem jointlyContinuous_coind₁ [LocallyCompactSpace G]
    (X : TopRep.{w} k G) [JointlyContinuous X] : JointlyContinuous (coind₁ X) := by
  refine ⟨?_⟩
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hargs : Continuous (fun q : (G × C(G, X)) × G =>
      (q.1.2, q.1.1⁻¹ * q.2)) := by fun_prop
  have hresult : Continuous (fun q : (G × C(G, X)) × G =>
      X.ρ q.1.1 (q.1.2 (q.1.1⁻¹ * q.2))) :=
    JointlyContinuous.continuous_action.comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_eval.comp hargs))
  exact hresult

end TopRep

namespace TopRep

variable {k : Type u} [CommRing k] [TopologicalSpace k]
variable {G : Type v} [Monoid G]

instance instLinearUliftFunctor : (uliftFunctor (k := k) (G := G) :
    TopRep.{w} k G ⥤ TopRep.{max w w'} k (ULift.{v'} G)).Linear k where

end TopRep
