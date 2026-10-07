/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ConnectingNaturality
public import CGCExamples.CohomologyExactSequence

/-!
# A nonidentity endomorphism of the sign coefficient sequence

Multiplication by three on the integer sign representations and the identity
on the mod-two quotient form a morphism of the short exact sequence
`ℤ --×2→ ℤ → ZMod 2`. Both coefficient squares commute, and the
degree-zero connecting class of the quotient invariant `1` is nonzero.
-/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology

namespace CGCExamples

/-- Multiplication by three on the integer sign representation. -/
def signedTriple : signedIntegers ⟶ signedIntegers :=
  (3 : ℤ) • 𝟙 signedIntegers

@[simp] theorem signedTriple_apply (x : ℤ) : signedTriple x = 3 * x := by
  rfl

/-- Scaling by three is not the identity on the integer coefficients. -/
theorem signedTriple_ne_id : signedTriple ≠ 𝟙 signedIntegers := by
  intro h
  have h' := congrArg (fun f : signedIntegers ⟶ signedIntegers => f (1 : ℤ)) h
  change (3 : ℤ) = 1 at h'
  omega

/-- Scaling by three commutes with multiplication by two. -/
theorem signedInclusion_signedTriple :
    signedInclusion ≫ signedTriple = signedTriple ≫ signedInclusion := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  change (3 : ℤ) • signedInclusion x = signedInclusion ((3 : ℤ) • x)
  rw [map_smul]

/-- Mod-two reduction is unchanged by multiplying by three. -/
theorem signedProjection_signedTriple :
    signedProjection ≫ 𝟙 signedQuotient = signedTriple ≫ signedProjection := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  change signedProjection x = signedProjection ((3 : ℤ) • x)
  rw [map_smul]
  simp only [zsmul_eq_mul, show ((3 : ℤ) : ZMod 2) = 1 by decide, one_mul]

/-- The coefficient map is nonidentity while the original degree-zero
connecting homomorphism detects the nonzero quotient invariant. -/
theorem signedTriple_nonidentity_nonzero_connector :
    signedTriple ≠ 𝟙 signedIntegers ∧
      (connecting signedInclusion signedProjection signedInclusion_injective
        signedSequence_exact signedProjection_surjective 0).hom
          ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne) ≠ 0 :=
  ⟨signedTriple_ne_id, signedConnecting_one_ne_zero⟩

/-- The nonidentity coefficient-sequence endomorphism acts naturally on the
algebraic connecting homomorphism in every degree. -/
theorem signedConnecting_triple_naturality (n : ℕ) :
    connecting signedInclusion signedProjection signedInclusion_injective
        signedSequence_exact signedProjection_surjective n ≫
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
        (map (ContinuousMonoidHom.id ℤˣ) signedTriple (n + 1)) =
    (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map
        (map (ContinuousMonoidHom.id ℤˣ) (𝟙 signedQuotient) n) ≫
      connecting signedInclusion signedProjection signedInclusion_injective
        signedSequence_exact signedProjection_surjective n := by
  exact connecting_naturality signedInclusion signedProjection signedInclusion
    signedProjection signedTriple signedTriple (𝟙 signedQuotient)
    signedInclusion_injective signedSequence_exact signedProjection_surjective
    signedInclusion_injective signedSequence_exact signedProjection_surjective
    signedInclusion_signedTriple signedProjection_signedTriple n

end CGCExamples
