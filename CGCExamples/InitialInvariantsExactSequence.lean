/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.InitialInvariantsExactSequence
public import CGCExamples.CohomologyExactSequence

/-!
# Initial invariant arrows and the sign-action boundary

The trivial-action integer coefficient sequence has an invariant whose image
under multiplication by two remains nonzero. In contrast, for the integer sign
action and the mod-two quotient, an invariant quotient class has no invariant
lift and its existing algebraic degree-zero boundary is nonzero. These facts
are independent of the general unsplit exact-segment theorem and
zero-degree naturality bridge.
-/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology

namespace CGCExamples

local instance : TopologicalSpace TwoGroup := ⊥
local instance : DiscreteTopology TwoGroup := ⟨rfl⟩
local instance : IsTopologicalGroup TwoGroup := inferInstance
local instance : CompactSpace TwoGroup := inferInstance

/-- The multiplication-by-two injection in the trivial-action coefficient
sequence sends the invariant `1` to the nonzero invariant `2`. -/
theorem evenSequence_invariants_inclusion_nonzero :
    (evenSequenceInclusion.hom.mapInvariants
      (⟨1, by intro g; exact ContRepresentation.trivial_apply g 1⟩ :
        evenSequenceIntegers.ρ.invariants) : evenSequenceIntegers.ρ.invariants) ≠ 0 := by
  intro h
  have hval := congrArg Subtype.val h
  change (2 : ℤ) = 0 at hval
  omega

/-- The displayed invariant inclusion of the trivial-action sequence is nonzero. -/
theorem evenSequence_initialInvariants_inclusion_nonzero :
    ((initialInvariantsSequence evenSequenceInclusion evenSequenceProjection
      evenSequenceInclusion_injective evenSequence_exact
      evenSequenceProjection_surjective).map' 1 2).hom
        (⟨1, by intro g; exact ContRepresentation.trivial_apply g 1⟩ :
      evenSequenceIntegers.ρ.invariants) ≠ 0 := by
  rw [initialInvariantsSequence_inclusion_apply]
  exact evenSequence_invariants_inclusion_nonzero

/-- The unsplit initial-segment theorem supplies consecutive composites of
the actual coefficient and cohomology maps for the sign sequence. -/
theorem signedInitialInvariants_isComplex :
    (initialInvariantsSequence signedInclusion signedProjection
      signedInclusion_injective signedSequence_exact signedProjection_surjective).IsComplex :=
  (initialInvariantsSequence_exact signedInclusion signedProjection
    signedInclusion_injective signedSequence_exact signedProjection_surjective).toIsComplex

/-- The actual displayed invariant-to-degree-one arrow detects the nonzero
sign-quotient invariant using only the pre-existing connector. -/
theorem signedInitialInvariants_boundary_nonzero :
    ((initialInvariantsSequence signedInclusion signedProjection
      signedInclusion_injective signedSequence_exact signedProjection_surjective).map' 3 4).hom
        signedQuotientInvariantOne ≠ 0 := by
  rw [initialInvariantsSequence_boundary_apply]
  exact signedConnecting_one_ne_zero

/-- Nonzero quotient invariant, lack of an invariant integer lift, and a
nonzero degree-zero boundary, all established without the new exactness claim. -/
theorem signedInitialInvariants_obstruction :
    signedQuotientInvariantOne ≠ 0 ∧
      (¬∃ x : signedIntegers.ρ.invariants,
        signedProjection.hom.mapInvariants x = signedQuotientInvariantOne) ∧
      (connecting signedInclusion signedProjection signedInclusion_injective
        signedSequence_exact signedProjection_surjective 0).hom
          ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne) ≠ 0 := by
  refine ⟨signedQuotientInvariantOne_ne_zero, ?_, signedConnecting_one_ne_zero⟩
  exact signedQuotientInvariantOne_not_lifted

end CGCExamples
