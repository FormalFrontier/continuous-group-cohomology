/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CohomologyExactSequence

/-!
# Evaluation of connecting isomorphisms

The linear map underlying the connecting isomorphism agrees pointwise with the
connecting map. The vanishing assumptions concern the two adjacent cohomology
modules after forgetting topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : TopRep.{max v w, u, v} k G}
variable [LocallyCompactSpace G] [DiscreteTopology B] [DiscreteTopology C]
variable [TopRep.JointlyContinuous B]
variable (i : A ⟶ B) (p : B ⟶ C)
variable (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
variable (hp : Function.Surjective p.hom) (n : ℕ)
variable (hBn : IsZero ((forget₂ (TopModuleCat k) (ModuleCat k)).obj
  (continuousCohomology.{u, v, w} n B)))
variable (hBnext : IsZero ((forget₂ (TopModuleCat k) (ModuleCat k)).obj
  (continuousCohomology.{u, v, w} (n + 1) B)))

example (x : (continuousCohomology.{u, v, w} n C).toModuleCat) :
    (connectingIso.{u, v, w} i p hi hexact hp n hBn hBnext).hom.hom x =
      (connecting.{u, v, w} i p hi hexact hp n).hom x := by
  simp

example (x : (continuousCohomology.{u, v, w} n C).toModuleCat) :
    (connectingIso.{u, v, w} i p hi hexact hp n hBn hBnext).hom.hom x =
      (connecting.{u, v, w} i p hi hexact hp n).hom x := by
  rw [connectingIso_hom_apply]

example (x : (continuousCohomology.{u, v, w} n C).toModuleCat) :
    (connectingIso.{u, v, w} i p hi hexact hp n hBn hBnext).hom.hom x =
      (connecting.{u, v, w} i p hi hexact hp n).hom x := by
  exact @connectingIso_hom_apply.{u, v, w} k _ _ G _ _ _ A B C _ _ _ _
    i p hi hexact hp n hBn hBnext x

end ContinuousCohomology
