/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Torsion

/-!
# Public-import clients for continuous degree-one torsion

The integral representation is arbitrary: the client does not assume its
coefficients are torsion, finite, finitely generated, or acted on trivially.
-/

set_option autoImplicit false

public section

universe v w

namespace ContinuousTorsionNative

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} ℤ G) [DiscreteTopology X]
    [TopRep.JointlyContinuous X] [CompactSpace G]

/-- Specialization of the public API to integral representations. -/
theorem integralDegreeOne : IsAddTorsion (continuousCohomology 1 X) :=
  ContinuousCohomology.isAddTorsion_degreeOne X

/-- An open subgroup of the compact acting group may act nontrivially too. -/
theorem openSubgroupDegreeOne (H : OpenSubgroup G) :
    IsAddTorsion (continuousCohomology 1 (TopRep.res H.subtype X)) := by
  let _ : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact ContinuousCohomology.isAddTorsion_degreeOne (TopRep.res H.subtype X)

end ContinuousTorsionNative
