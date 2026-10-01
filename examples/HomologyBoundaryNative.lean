/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ContinuousGroupCohomology.Algebra.Category.ModuleCat.Topology.HomologyBoundary

set_option warningAsError true

open CategoryTheory

universe u v

namespace CGCExamples.TopModuleCat

private theorem equal_classes_have_difference_boundary
    {k : Type u} [Ring k] [TopologicalSpace k]
    (S : ShortComplex (TopModuleCat.{v} k)) (z₁ z₂ : S.cycles)
    (h : S.homologyπ.hom z₁ = S.homologyπ.hom z₂) :
    ∃ w : S.X₁, S.toCycles.hom w = z₁ - z₂ := by
  apply (TopModuleCat.shortComplex_homologyπ_eq_zero_iff S (z₁ - z₂)).mp
  simpa only [map_sub, sub_eq_zero] using h

end CGCExamples.TopModuleCat
