/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Continuous cohomology as a functor in the coefficients

For a fixed topological group and degree, Mathlib's continuous-cohomology
maps for the identity group homomorphism form a functor on topological
representations. Its action on objects and morphisms is the existing
continuous cohomology and its coefficient map, respectively.

## References

* Mathlib's `ContinuousCohomology.map`, `map_id`, and `map_comp`.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous cohomology in a fixed degree and for a fixed acting group,
functorial in the topological coefficient representation. -/
noncomputable def coefficientFunctor (n : ℕ) :
    TopRep.{max v w} k G ⥤ TopModuleCat.{max v w} k where
  obj X := continuousCohomology n X
  map f := map (ContinuousMonoidHom.id G) f n
  map_id X := map_id X n
  map_comp f g := by
    have h := ContinuousCohomology.map_comp
      (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G) f g n
    convert h using 1
    all_goals rfl

@[simp] theorem coefficientFunctor_obj (n : ℕ) (X : TopRep.{max v w} k G) :
    (coefficientFunctor (k := k) (G := G) n).obj X = continuousCohomology n X := rfl

@[simp] theorem coefficientFunctor_map (n : ℕ) {X Y : TopRep.{max v w} k G}
    (f : X ⟶ Y) :
    (coefficientFunctor (k := k) (G := G) n).map f =
      map (ContinuousMonoidHom.id G) f n := rfl

end ContinuousCohomology
