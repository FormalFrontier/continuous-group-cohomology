/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Topology.ContinuousMap.Exact
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Exactness of continuous coinduction on discrete coefficient rows

The existing twisted coinduction functor maps a short exact row of discrete
coefficients to a row exact on underlying modules. Its map evaluates by
coefficient postcomposition.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3, Proposition (1.3.6)(i).
* Mathlib's continuous coinduction and compact-open postcomposition.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B D : TopRep.{max v w} k G}

/-- Evaluation identifies the existing functor map with coefficient
postcomposition, without changing the twisted coinduction construction. -/
theorem coind₁Functor_map_apply (f : A ⟶ B) (F : (coind₁Functor k G).obj A)
    (g : G) : ((coind₁Functor k G).map f).hom F g = f.hom (F g) := rfl

/-- The functor's underlying map is exactly compact-open postcomposition. -/
theorem coind₁Functor_map_eq_postcomp (f : A ⟶ B) :
    (((coind₁Functor k G).map f).hom : C(G, A) → C(G, B)) =
      ContinuousMap.comp (f.hom : C(A, B)) := by
  funext F
  ext g
  exact coind₁Functor_map_apply f F g

/-- The underlying-module maps of coinduction preserve a short exact row of
discrete coefficient representations. This is the underlying-map exactness
corresponding to Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
corrected second edition, Chapter I, §3, Proposition (1.3.6)(i). -/
theorem coind₁Functor_shortExact [DiscreteTopology B] [DiscreteTopology D]
    (i : A ⟶ B) (p : B ⟶ D)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    Function.Injective (((coind₁Functor k G).map i).hom) ∧
      Function.Exact (((coind₁Functor k G).map i).hom)
        (((coind₁Functor k G).map p).hom) ∧
      Function.Surjective (((coind₁Functor k G).map p).hom) := by
  rw [coind₁Functor_map_eq_postcomp i, coind₁Functor_map_eq_postcomp p]
  exact ⟨ContinuousMap.postcomp_injective _ hi,
    ContinuousMap.postcomp_exact _ _ hexact,
    ContinuousMap.postcomp_surjective _ hp⟩

end TopRep
