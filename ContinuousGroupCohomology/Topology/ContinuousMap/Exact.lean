/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of coefficient postcomposition on continuous maps

For an arbitrary topological domain, the middle exactness of coefficient
postcomposition only needs a discrete middle coefficient space; surjectivity
only needs a discrete target coefficient space.

## References

* Mathlib's compact-open postcomposition and `postcomp_injective`.
-/

public section

namespace ContinuousMap

universe u v w z

variable {X : Type u} {A : Type v} {B : Type w} {D : Type z}
  [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace D]

/-- Postcomposition preserves middle exactness if the middle coefficient space
is discrete. No injectivity or discreteness of the source is required. -/
theorem postcomp_exact [Zero D] [DiscreteTopology B]
    (i : C(A, B)) (p : C(B, D)) (h : Function.Exact i p) :
    Function.Exact (ContinuousMap.comp i : C(X, A) → C(X, B))
      (ContinuousMap.comp p : C(X, B) → C(X, D)) := by
  classical
  intro F
  constructor
  · intro hF
    have hFx (x : X) : p (F x) = 0 := by
      have hx := congrArg (fun f : C(X, D) => f x) hF
      simpa using hx
    let lift : {b : B // p b = 0} → A := fun b =>
      Classical.choose ((h b.1).mp b.2)
    refine ⟨⟨fun x => lift ⟨F x, hFx x⟩,
      (continuous_of_discreteTopology : Continuous lift).comp
        (F.continuous.subtype_mk hFx)⟩, ?_⟩
    ext x
    exact Classical.choose_spec ((h (F x)).mp (hFx x))
  · rintro ⟨lift, rfl⟩
    ext x
    exact (h (i (lift x))).mpr ⟨lift x, rfl⟩

/-- Postcomposition by a continuous surjection onto a discrete space is
surjective. The domain of the coefficient map need not be discrete. -/
theorem postcomp_surjective [DiscreteTopology D]
    (p : C(B, D)) (h : Function.Surjective p) :
    Function.Surjective (ContinuousMap.comp p : C(X, B) → C(X, D)) := by
  classical
  intro F
  let select : D → B := fun d => Classical.choose (h d)
  refine ⟨⟨fun x => select (F x),
    (continuous_of_discreteTopology : Continuous select).comp F.continuous⟩, ?_⟩
  ext x
  exact Classical.choose_spec (h (F x))

end ContinuousMap
