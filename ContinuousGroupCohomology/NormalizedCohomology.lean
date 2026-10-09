/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.ContinuousCohomologyUlift
import ContinuousGroupCohomology.ContinuousCohomologyFunctor

/-!
# Common-universe normalization for continuous cohomology

Mathlib's recursive homogeneous-cochain construction requires the acting
group and coefficient carrier to inhabit one small universe. This file uses
the canonical maximum of their two original universes to define an honestly
named normalized representation, cochain complex and continuous-cohomology
object. It also provides coefficient maps and their functor laws.

No comparison to the unnormalized recursive construction is asserted when
the original group and coefficient carrier inhabit different universes: that
construction is not exposed by the current mathlib API. The separate
same-universe comparison applies when those universes already agree.
-/

set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Raise both the acting group and coefficient carrier of a topological
representation into their canonical common maximum universe. -/
abbrev normalized (X : TopRep.{w} k G) :
    TopRep.{max v w} k (ULift.{max v w} G) :=
  TopRep.ulift.{u, v, max v w, w, max v w} X

/-- The functor raising a topological representation into the canonical
common maximum of its fixed group and coefficient universes. -/
abbrev normalizedFunctor :
    TopRep.{w} k G ⥤ TopRep.{max v w} k (ULift.{max v w} G) :=
  TopRep.uliftFunctor.{u, v, max v w, w, max v w}

/-- Raise a coefficient morphism into the canonical common maximum universe. -/
abbrev normalizedMap {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    normalized X ⟶ normalized Y :=
  normalizedFunctor.map f

/-- Homogeneous continuous cochains after canonical common-universe
normalization. -/
abbrev normalizedHomogeneousCochains (X : TopRep.{w} k G) :
    CochainComplex (TopModuleCat.{max v w} k) ℕ :=
  (normalized X).homogeneousCochains

/-- Continuous cohomology after canonical common-universe normalization. -/
noncomputable abbrev normalizedContinuousCohomology
    (X : TopRep.{w} k G) (n : ℕ) : TopModuleCat.{max v w} k :=
  continuousCohomology n (normalized X)

/-- The map on normalized continuous cohomology induced by a coefficient
morphism for a fixed acting group. -/
noncomputable def normalizedContinuousCohomologyMap
    {X Y : TopRep.{w} k G} (f : X ⟶ Y) (n : ℕ) :
    normalizedContinuousCohomology X n ⟶
      normalizedContinuousCohomology Y n :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id (ULift.{max v w} G)) (normalizedMap f) n

@[simp]
lemma normalizedContinuousCohomologyMap_id
    (X : TopRep.{w} k G) (n : ℕ) :
    normalizedContinuousCohomologyMap (𝟙 X) n = 𝟙 _ := by
  unfold normalizedContinuousCohomologyMap
  rw [show normalizedMap (𝟙 X) = 𝟙 (normalized X) by
    exact normalizedFunctor.map_id X]
  exact ContinuousCohomology.map_id (normalized X) n

@[reassoc]
lemma normalizedContinuousCohomologyMap_comp
    {X Y Z : TopRep.{w} k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    normalizedContinuousCohomologyMap (f ≫ g) n =
      normalizedContinuousCohomologyMap f n ≫
        normalizedContinuousCohomologyMap g n := by
  unfold normalizedContinuousCohomologyMap
  rw [show normalizedMap (f ≫ g) = normalizedMap f ≫ normalizedMap g by
    exact normalizedFunctor.map_comp f g]
  simpa only [ContinuousCohomology.coefficientFunctor,
    normalizedContinuousCohomology] using
    (ContinuousCohomology.coefficientFunctor
      (k := k) (G := ULift.{max v w} G) n).map_comp
        (normalizedMap f) (normalizedMap g)

end TopRep
