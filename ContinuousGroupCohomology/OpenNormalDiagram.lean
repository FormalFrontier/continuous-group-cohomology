/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientTransitions

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuous cohomology over open-normal quotient stages

The order-dual index directs the coarser quotient stage toward its finer
refinements. The resulting diagram has a canonical inflation cocone in the
native category of topological modules; no colimit assertion is made.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The order dual of the open normal subgroups is filtered: intersections are
common refinements, and the whole group gives a nonempty stage. -/
theorem isFiltered_orderDual_openNormalSubgroup (G : Type v) [Group G]
    [TopologicalSpace G] : IsFiltered (OrderDual (OpenNormalSubgroup G)) := by
  refine { toIsFilteredOrEmpty := inferInstance, nonempty := ?_ }
  exact ⟨⟨(⊤ : OpenSubgroup G), by change (⊤ : Subgroup G).Normal; infer_instance⟩⟩

variable (X : TopRep.{max v w} k G) (n : ℕ)

/-- The native degree-`n` continuous-cohomology diagram: a morphism from `M` to
`N` means `N ≤ M`, and maps classes from `M`-invariants to `N`-invariants. -/
noncomputable def openNormalCohomologyDiagram :
    OrderDual (OpenNormalSubgroup G) ⥤ TopModuleCat.{max v w} k where
  obj M := continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X)
  map {M N} f :=
    map (quotientTransitionHom N M (leOfHom f))
      (quotientTransitionIncl X (leOfHom f)) n
  map_id M := by
    exact quotientTransition_map_id X M n
  map_comp f g := by
    exact quotientTransition_map_comp X (leOfHom g) (leOfHom f) n

/-- The canonical cocone whose legs inflate the classes of open-normal
quotients to continuous cohomology of the original representation. -/
noncomputable def openNormalInflationCocone : Cocone (openNormalCohomologyDiagram X n) where
  pt := continuousCohomology n X
  ι := {
    app M := map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) n
    naturality := by
      intro M N f
      exact (quotientTransition_map_inflate X (leOfHom f) n).symm
  }

@[simp] theorem openNormalCohomologyDiagram_obj (M : OpenNormalSubgroup G) :
    (openNormalCohomologyDiagram X n).obj M =
      continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X) := rfl

@[simp] theorem openNormalCohomologyDiagram_map
    {M N : OrderDual (OpenNormalSubgroup G)} (f : M ⟶ N) :
    (openNormalCohomologyDiagram X n).map f =
      map (quotientTransitionHom N M (leOfHom f))
        (quotientTransitionIncl X (leOfHom f)) n := rfl

@[simp] theorem openNormalInflationCocone_ι_app (M : OpenNormalSubgroup G) :
    (openNormalInflationCocone X n).ι.app M =
      map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) n := rfl

end ContinuousCohomology
