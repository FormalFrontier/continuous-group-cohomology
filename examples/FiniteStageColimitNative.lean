/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageColimit

/-! Ordinary-import tests of the native colimit at arbitrary degree and target. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
  [TopRep.JointlyContinuous X] (n : ℕ)
variable (s : Cocone (ContinuousCohomology.openNormalCohomologyDiagram X n))

private noncomputable def descendant :
    (ContinuousCohomology.openNormalInflationCocone X n).pt ⟶ s.pt :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).desc s

private theorem descendant_factorization (M : OrderDual (OpenNormalSubgroup G)) :
    (ContinuousCohomology.openNormalInflationCocone X n).ι.app M ≫
      descendant X n s = s.ι.app M :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).fac s M

private theorem descendant_unique
    (f : (ContinuousCohomology.openNormalInflationCocone X n).pt ⟶ s.pt)
    (hf : ∀ M, (ContinuousCohomology.openNormalInflationCocone X n).ι.app M ≫
      f = s.ι.app M) :
    f = descendant X n s :=
  (ContinuousCohomology.openNormalInflationCoconeIsColimit X n).uniq s f hf

private noncomputable def zero_degree :
    IsColimit (ContinuousCohomology.openNormalInflationCocone X 0) :=
  ContinuousCohomology.openNormalInflationCoconeIsColimit X 0

end CGCExamples.ContinuousCohomology
