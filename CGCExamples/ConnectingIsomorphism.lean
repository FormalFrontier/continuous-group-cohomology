/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CGCExamples.CohomologyExactSequence
public import CGCExamples.CoinducedAcyclic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Module.PUnit

/-!
# A coinduced coefficient row with a signed quotient

For the two-element group of integer units, constant integral functions embed
in the twisted coinduced representation. The difference of evaluations at its
two elements maps onto the integral sign representation. The middle cohomology
vanishes in degrees one and two, whereas the quotient has a nonzero class in
degree one. The resulting connector is nonzero by the existing long exact
sequence, independently of an isomorphism theorem.
The same row instantiates the general mono, epi and connecting-isomorphism
APIs, without using them to establish the preceding nonzero class.

Two split rows separately test the degree-zero boundaries. For
`Multiplicative (ZMod 2)`, positive coinduced vanishing does not make the
degree-zero connector injective; for `ℤˣ`, vanishing of signed invariants
does not make its degree-zero connector surjective.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3, the paragraph before Definition (1.3.5).
* Mathlib's twisted continuous coinduction and short-exact-complex boundary.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopRep ContinuousCohomology ContRepresentation

namespace CGCExamples

private instance : CompactSpace ℤˣ := inferInstance
private instance : DiscreteTopology ℤˣ := inferInstance

/-- The trivial integral representation of the group of integer units. -/
abbrev trivialUnitIntegers : TopRep ℤ ℤˣ :=
  TopRep.of (ContRepresentation.trivial ℤ ℤˣ ℤ)

private instance : DiscreteTopology trivialUnitIntegers := by
  change DiscreteTopology ℤ
  infer_instance

private instance : TopRep.JointlyContinuous trivialUnitIntegers where
  continuous_action := by
    change Continuous (fun p : ℤˣ × ℤ => p.2)
    exact continuous_snd

/-- The coinduced integral functions on the finite unit group are discrete. -/
instance signedCoinduced_discrete : DiscreteTopology (TopRep.coind₁ trivialUnitIntegers) := by
  change DiscreteTopology C(ℤˣ, ℤ)
  exact ContinuousMap.discreteTopology_of_compactSpace

/-- The twisted coinduced action is jointly continuous. -/
instance signedCoinduced_jointlyContinuous :
    TopRep.JointlyContinuous (TopRep.coind₁ trivialUnitIntegers) :=
  TopRep.jointlyContinuous_coind₁ trivialUnitIntegers

/-- Embed integers as constant functions in their twisted coinduction. -/
def signedCoinducedInclusion : trivialUnitIntegers ⟶ TopRep.coind₁ trivialUnitIntegers :=
  (TopRep.coind₁ι (k := ℤ) (G := ℤˣ)).app trivialUnitIntegers

@[simp]
theorem signedCoinducedInclusion_apply (x : ℤ) (t : ℤˣ) :
    signedCoinducedInclusion x t = x := rfl

/-- Subtract evaluation at the negative unit from evaluation at the positive
unit. Swapping the two evaluations intertwines the sign action. -/
def signedCoinducedProjection : TopRep.coind₁ trivialUnitIntegers ⟶ signedIntegers :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      ContinuousMap.evalCLM (R := ℤ) (M := ℤ) (1 : ℤˣ) -
        ContinuousMap.evalCLM (R := ℤ) (M := ℤ) (-1 : ℤˣ)
    isIntertwining' := by
      intro g
      apply ContinuousLinearMap.ext
      intro f
      obtain rfl | rfl := Int.units_eq_one_or g
      · simp
      · change f ((-1 : ℤˣ)⁻¹ * 1) - f ((-1 : ℤˣ)⁻¹ * -1) =
          (-1 : ℤˣ) • (f 1 - f (-1))
        simp [Units.smul_def]
  }

@[simp]
theorem signedCoinducedProjection_apply (f : TopRep.coind₁ trivialUnitIntegers) :
    signedCoinducedProjection f = f 1 - f (-1) := rfl

/-- Evaluation at the unit detects equality between constant functions. -/
theorem signedCoinducedInclusion_injective : Function.Injective signedCoinducedInclusion := by
  intro x y h
  have h₁ := congrArg (fun f : C(ℤˣ, ℤ) => f 1) h
  change x = y at h₁
  exact h₁

/-- The constant functions are exactly the functions taking equal values at
the positive and negative units. -/
theorem signedCoinducedSequence_exact :
    Function.Exact signedCoinducedInclusion signedCoinducedProjection := by
  intro f
  constructor
  · intro hf
    change f 1 - f (-1) = 0 at hf
    have heq : f 1 = f (-1) := sub_eq_zero.mp hf
    refine ⟨f 1, ?_⟩
    ext t
    obtain rfl | rfl := Int.units_eq_one_or t
    · change f 1 = f 1
      rfl
    · change f 1 = f (-1)
      exact heq
  · rintro ⟨x, rfl⟩
    change x - x = 0
    exact sub_self x

/-- Every signed integer is a difference of two values of a continuous
function on the discrete two-element group. -/
theorem signedCoinducedProjection_surjective :
    Function.Surjective signedCoinducedProjection := by
  intro x
  let coeff : ℤ := x
  let f : C(ℤˣ, ℤ) :=
    ⟨fun t => if t = 1 then coeff else 0, continuous_of_discreteTopology⟩
  refine ⟨f, ?_⟩
  change f 1 - f (-1) = coeff
  have h₁ : f 1 = coeff := by simp [f]
  have h₂ : f (-1) = (0 : ℤ) := by
    simp [f, show (-1 : ℤˣ) ≠ 1 by decide]
  calc
    f 1 - f (-1) = coeff - 0 := congrArg₂ (· - ·) h₁ h₂
    _ = coeff := sub_zero coeff

/-- Both positive-degree vanishing hypotheses hold for this specific middle
coefficient. -/
private theorem signedCoinduced_positive_eq_zero (m : ℕ)
    (x : continuousCohomology (m + 1) (TopRep.coind₁ trivialUnitIntegers)) : x = 0 :=
  coind₁_positive_eq_zero trivialUnitIntegers m x

private theorem signedCoinduced_isZero (m : ℕ) :
    IsZero ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj
      (continuousCohomology (m + 1) (TopRep.coind₁ trivialUnitIntegers))) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun x y => (signedCoinduced_positive_eq_zero m x).trans
    (signedCoinduced_positive_eq_zero m y).symm⟩

/-- The degree-one class supplied by the other signed coefficient row has a
nonzero image under this row's algebraic degree-one connector. -/
theorem signedCoinducedConnecting_one_ne_zero :
    (connecting signedCoinducedInclusion signedCoinducedProjection
      signedCoinducedInclusion_injective signedCoinducedSequence_exact
      signedCoinducedProjection_surjective 1).hom
        ((connecting signedInclusion signedProjection signedInclusion_injective
          signedSequence_exact signedProjection_surjective 0).hom
          ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne)) ≠ 0 := by
  let y := (connecting signedInclusion signedProjection signedInclusion_injective
    signedSequence_exact signedProjection_surjective 0).hom
      ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne)
  have hy : y ≠ 0 := signedConnecting_one_ne_zero
  intro hzero
  obtain ⟨x, hx⟩ := ((exact_map_connecting signedCoinducedInclusion
    signedCoinducedProjection signedCoinducedInclusion_injective
    signedCoinducedSequence_exact signedCoinducedProjection_surjective 1) y).mp hzero
  apply hy
  simpa [signedCoinduced_positive_eq_zero 0 x] using hx.symm

/-- Existing exactness and vanishing in degree two give surjectivity of the
same degree-one connector without using a connecting-isomorphism theorem. -/
theorem signedCoinducedConnecting_surjective :
    Function.Surjective (connecting signedCoinducedInclusion signedCoinducedProjection
      signedCoinducedInclusion_injective signedCoinducedSequence_exact
      signedCoinducedProjection_surjective 1).hom := by
  intro z
  apply ((exact_connecting_map signedCoinducedInclusion signedCoinducedProjection
    signedCoinducedInclusion_injective signedCoinducedSequence_exact
    signedCoinducedProjection_surjective 1) z).mp
  exact signedCoinduced_positive_eq_zero 1 _

private theorem signedCoinducedConnecting_mono :
    Mono (connecting signedCoinducedInclusion signedCoinducedProjection
      signedCoinducedInclusion_injective signedCoinducedSequence_exact
      signedCoinducedProjection_surjective 1) :=
  connecting_mono_of_isZero signedCoinducedInclusion signedCoinducedProjection
    signedCoinducedInclusion_injective signedCoinducedSequence_exact
    signedCoinducedProjection_surjective 1 (signedCoinduced_isZero 0)

private theorem signedCoinducedConnecting_epi :
    Epi (connecting signedCoinducedInclusion signedCoinducedProjection
      signedCoinducedInclusion_injective signedCoinducedSequence_exact
      signedCoinducedProjection_surjective 1) :=
  connecting_epi_of_isZero signedCoinducedInclusion signedCoinducedProjection
    signedCoinducedInclusion_injective signedCoinducedSequence_exact
    signedCoinducedProjection_surjective 1 (signedCoinduced_isZero 1)

private theorem signedCoinducedConnectingIso_hom_apply
    (y : continuousCohomology 1 signedIntegers) :
    (connectingIso signedCoinducedInclusion signedCoinducedProjection
      signedCoinducedInclusion_injective signedCoinducedSequence_exact
      signedCoinducedProjection_surjective 1 (signedCoinduced_isZero 0)
      (signedCoinduced_isZero 1)).hom.hom y =
        (connecting signedCoinducedInclusion signedCoinducedProjection
          signedCoinducedInclusion_injective signedCoinducedSequence_exact
          signedCoinducedProjection_surjective 1).hom y := by
  exact connectingIso_hom_apply _ _ _ _ _ _ _ _ y

private instance : TopologicalSpace TwoGroup := ⊥
private instance : DiscreteTopology TwoGroup := ⟨rfl⟩
private instance : IsTopologicalGroup TwoGroup := inferInstance
private instance : CompactSpace TwoGroup := inferInstance

private abbrev zeroTwoGroupCoefficients : TopRep ℤ TwoGroup :=
  TopRep.of (ContRepresentation.trivial ℤ TwoGroup PUnit)

private abbrev coinducedTwoGroupCoefficients : TopRep ℤ TwoGroup :=
  TopRep.coind₁ integerCoefficients

private instance : DiscreteTopology coinducedTwoGroupCoefficients := by
  change DiscreteTopology C(TwoGroup, ℤ)
  exact ContinuousMap.discreteTopology_of_compactSpace

private instance : TopRep.JointlyContinuous integerCoefficients where
  continuous_action := by
    change Continuous (fun p : TwoGroup × ℤ => p.2)
    exact continuous_snd

private instance : TopRep.JointlyContinuous coinducedTwoGroupCoefficients :=
  TopRep.jointlyContinuous_coind₁ integerCoefficients

private def zeroToCoinduced : zeroTwoGroupCoefficients ⟶ coinducedTwoGroupCoefficients := 0

private def coinducedIdentity : coinducedTwoGroupCoefficients ⟶ coinducedTwoGroupCoefficients :=
  𝟙 _

private theorem zeroToCoinduced_injective : Function.Injective zeroToCoinduced := by
  intro x y _
  exact Subsingleton.elim x y

private theorem zeroToCoinduced_exact :
    Function.Exact zeroToCoinduced coinducedIdentity := by
  intro f
  change f = 0 ↔ ∃ x : zeroTwoGroupCoefficients, zeroToCoinduced x = f
  constructor
  · intro hf
    refine ⟨0, ?_⟩
    simp [zeroToCoinduced, hf]
  · rintro ⟨x, rfl⟩
    change (0 : coinducedTwoGroupCoefficients) = 0
    rfl

private theorem coinducedIdentity_surjective : Function.Surjective coinducedIdentity := by
  intro f
  exact ⟨f, rfl⟩

/-- Over `Multiplicative (ZMod 2)`, a split row with coinduced middle
coefficient has vanishing degree-one middle cohomology but its degree-zero
connector is not injective. -/
private theorem twoGroup_connecting_zero_boundary :
    IsZero ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj
      (continuousCohomology 1 coinducedTwoGroupCoefficients)) ∧
    ¬ Mono (connecting zeroToCoinduced coinducedIdentity
      zeroToCoinduced_injective zeroToCoinduced_exact
      coinducedIdentity_surjective 0) := by
  constructor
  · rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun x y => (twoGroup_positive_eq_zero x).trans
      (twoGroup_positive_eq_zero y).symm⟩
  · intro hmono
    obtain ⟨y, hy⟩ := twoGroup_degree_zero_nonzero
    have hmap :
        (map (ContinuousMonoidHom.id TwoGroup) coinducedIdentity 0).hom y = y := by
      simp [coinducedIdentity, ContinuousCohomology.map_id]
    have hδ :
        (connecting zeroToCoinduced coinducedIdentity
          zeroToCoinduced_injective zeroToCoinduced_exact
          coinducedIdentity_surjective 0).hom y = 0 :=
      ((exact_map_connecting zeroToCoinduced coinducedIdentity
        zeroToCoinduced_injective zeroToCoinduced_exact
        coinducedIdentity_surjective 0) y).mpr ⟨y, hmap⟩
    have hinj := (ModuleCat.mono_iff_injective _).mp hmono
    apply hy
    exact hinj (hδ.trans (map_zero _).symm)

private abbrev zeroSignedCoefficients : TopRep ℤ ℤˣ :=
  TopRep.of (ContRepresentation.trivial ℤ ℤˣ PUnit)

private instance : DiscreteTopology zeroSignedCoefficients := by
  change DiscreteTopology PUnit
  infer_instance

private def signedIdentity : signedIntegers ⟶ signedIntegers := 𝟙 _

private def signedToZero : signedIntegers ⟶ zeroSignedCoefficients := 0

private theorem signedIdentity_injective : Function.Injective signedIdentity := by
  intro x y h
  exact h

private theorem signedToZero_surjective : Function.Surjective signedToZero := by
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

private theorem signedToZero_exact : Function.Exact signedIdentity signedToZero := by
  intro x
  constructor
  · intro _
    exact ⟨x, rfl⟩
  · intro _
    exact Subsingleton.elim _ _

private theorem zeroSigned_degree_zero_eq_zero
    (x : continuousCohomology 0 zeroSignedCoefficients) : x = 0 := by
  have hz : (zeroIso zeroSignedCoefficients).hom.hom x = 0 := Subsingleton.elim _ _
  have h := congrArg (fun y => (zeroIso zeroSignedCoefficients).inv.hom y) hz
  simpa only [Iso.hom_inv_id_apply, map_zero] using h

private theorem signed_degree_zero_eq_zero
    (x : continuousCohomology 0 signedIntegers) : x = 0 := by
  have hz := signedIntegers_invariant_eq_zero ((zeroIso signedIntegers).hom x)
  have h := congrArg (fun y => (zeroIso signedIntegers).inv.hom y) hz
  simpa only [Iso.hom_inv_id_apply, map_zero] using h

/-- Over `ℤˣ`, a split row with signed middle coefficients has vanishing
degree-zero middle-coefficient cohomology but its degree-zero connector is not surjective. -/
private theorem signed_connecting_zero_boundary :
    IsZero ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj
      (continuousCohomology 0 signedIntegers)) ∧
    ¬ Epi (connecting signedIdentity signedToZero signedIdentity_injective
      signedToZero_exact signedToZero_surjective 0) := by
  constructor
  · rw [ModuleCat.isZero_iff_subsingleton]
    exact ⟨fun x y => (signed_degree_zero_eq_zero x).trans
      (signed_degree_zero_eq_zero y).symm⟩
  · intro hepi
    let y := (connecting signedInclusion signedProjection signedInclusion_injective
      signedSequence_exact signedProjection_surjective 0).hom
        ((zeroIso signedQuotient).inv.hom signedQuotientInvariantOne)
    have hy : y ≠ 0 := signedConnecting_one_ne_zero
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective _).mp hepi y
    apply hy
    have hz := zeroSigned_degree_zero_eq_zero x
    simpa only [hz, map_zero] using hx.symm

end CGCExamples
