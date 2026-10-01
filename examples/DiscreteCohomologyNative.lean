/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.DiscreteCohomology

set_option autoImplicit false
set_option warningAsError true

/-!
# Ordinary-import clients for native continuous-cohomology discreteness

The degree and the coefficient representation are arbitrary; the client does
not assume joint continuity of the action or triviality of the module.
-/

@[expose] public section

universe u v w z

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

private theorem arbitrary_degree (n : ℕ) :
    DiscreteTopology (continuousCohomology n X) := by
  have : DiscreteTopology (continuousCohomology n X) :=
    ContinuousCohomology.discreteTopology_continuousCohomology X n
  exact inferInstance

private theorem arbitrary_function_is_continuous (n : ℕ)
    {Y : Type z} [TopologicalSpace Y] (f : continuousCohomology n X → Y) :
    Continuous f := by
  have : DiscreteTopology (continuousCohomology n X) := arbitrary_degree X n
  exact continuous_of_discreteTopology

end CGCExamples.ContinuousCohomology
