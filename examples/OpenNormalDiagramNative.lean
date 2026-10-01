/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.OpenNormalDiagram

/-! Ordinary-import tests at arbitrary degree and arbitrary open-normal stages. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) (n : ℕ)
variable {N M L : OpenNormalSubgroup G} (hNM : N ≤ M) (hML : M ≤ L)

private theorem refinement_direction
    (a : continuousCohomology n (TopRep.quotientInvariants M.toSubgroup X)) :
    ((ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM)).hom a =
      (ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom a := rfl

private theorem composition :
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ L N (hNM.trans hML)) =
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ L M hML) ≫
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
      (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM) := by
  exact (ContinuousCohomology.openNormalCohomologyDiagram X n).map_comp _ _

private theorem inflation_triangle :
    (ContinuousCohomology.openNormalCohomologyDiagram X n).map
        (@homOfLE (OrderDual (OpenNormalSubgroup G)) _ M N hNM) ≫
      (ContinuousCohomology.openNormalInflationCocone X n).ι.app N =
    (ContinuousCohomology.openNormalInflationCocone X n).ι.app M := by
  exact (ContinuousCohomology.openNormalInflationCocone X n).ι.naturality _

omit [IsTopologicalGroup G] in
private theorem filtered_index :
    IsFiltered (OrderDual (OpenNormalSubgroup G)) :=
  ContinuousCohomology.isFiltered_orderDual_openNormalSubgroup G

end CGCExamples.ContinuousCohomology
