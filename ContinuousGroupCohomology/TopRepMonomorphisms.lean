/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Monomorphisms of topological representations

A morphism of topological representations is a monomorphism precisely when its
underlying function is injective. The concrete forgetful functor preserves finite
limits through the equivalence with actions on topological modules.

Only a ring with a supplied topology and a monoid are needed. The action operators
are individually continuous; no topology on the monoid or joint continuity of
its action is assumed.

## References

* Mathlib's continuous representations, by Edison Xie and Richard Hill, and
  topological modules, by Richard Hill and Andrew Yang.
* Mathlib's limits of actions, by Kim Morrison, and concrete-category
  monomorphism criteria, by Joël Riou and the Mathlib contributors.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Monoid G]

/-- The underlying-function functor on topological representations preserves
finite limits. -/
instance forget_preservesFiniteLimits :
    PreservesFiniteLimits (forget (TopRep.{w} k G)) := by
  change PreservesFiniteLimits
    (toActionTopModFunc ⋙ Action.forget (TopModuleCat.{w} k) G ⋙
      forget₂ (TopModuleCat.{w} k) TopCat.{w} ⋙ forget TopCat.{w})
  infer_instance

/-- A morphism of topological representations is a monomorphism if and only if
its underlying continuous intertwining map is injective. -/
theorem mono_iff_injective {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f.hom :=
  ConcreteCategory.mono_iff_injective_of_preservesPullback f

end TopRep
