/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CoinducedInvariants
public import CGCExamples.CohomologyExactSequence

set_option warningAsError true

/-!
# Normal invariants with a moving coefficient

For the product of two groups of integer units, the second factor acts on the
integers by sign and the first survives the quotient. A function supported on
the identity coset has value `1`; its inverse image under the canonical
quotient-coinduction equivalence remains invariant but takes at the identity
a value moved by the normal subgroup. Thus the coefficient on the quotient
side is the whole integer module, not its fixed submodule. The full-group
boundary has the same feature.
-/

@[expose] public section

open CategoryTheory TopRep

namespace CGCExamples

/-- The normal second factor of the product of two sign groups. -/
def unitPairKernel : Subgroup (ℤˣ × ℤˣ) :=
  (⊥ : Subgroup ℤˣ).prod ⊤

/-- Membership in the second factor is characterized by a trivial first coordinate. -/
@[simp] theorem mem_unitPairKernel (g : ℤˣ × ℤˣ) :
    g ∈ unitPairKernel ↔ g.1 = 1 := by
  simp [unitPairKernel, Subgroup.mem_prod]

instance unitPairKernel_normal : unitPairKernel.Normal := inferInstance

/-- The sign representation restricted to the second factor. -/
def unitPairSignCoefficients : TopRep ℤ (ℤˣ × ℤˣ) :=
  TopRep.res (MonoidHom.snd ℤˣ ℤˣ) signedIntegers

/-- The coefficient module is the discrete, nonzero integer module. -/
instance unitPairSignCoefficients_discrete : DiscreteTopology unitPairSignCoefficients := by
  change DiscreteTopology ℤ
  infer_instance

/-- A finite discrete acting group acts jointly continuously on discrete coefficients. -/
instance unitPairSignCoefficients_jointlyContinuous :
    TopRep.JointlyContinuous unitPairSignCoefficients := by
  constructor
  apply continuous_prod_of_discrete_left.mpr
  intro g
  exact (unitPairSignCoefficients.ρ g).continuous

/-- The sign element of the normal second factor. -/
def unitPairSignFlip : ℤˣ × ℤˣ := (1, -1)

/-- The sign element belongs to the normal subgroup. -/
theorem unitPairSignFlip_mem : unitPairSignFlip ∈ unitPairKernel := by
  simp [unitPairSignFlip]

/-- The sign element moves the coefficient `1`, independently of coinduction. -/
theorem unitPairSignFlip_not_fixed :
    unitPairSignCoefficients.ρ unitPairSignFlip (1 : ℤ) ≠ (1 : ℤ) := by
  exact signedIntegers_negative_one_not_fixed

/-- No nonzero coefficient is fixed by the normal second factor. -/
theorem unitPairKernel_coefficients_fixed_eq_zero
    (x : (unitPairSignCoefficients.ρ.restrict unitPairKernel.subtype).invariants) :
    x = 0 := by
  let y : signedIntegers.ρ.invariants := ⟨x.1, by
    intro g
    have hg : (1, g) ∈ unitPairKernel := by simp
    exact x.2 ⟨(1, g), hg⟩⟩
  apply Subtype.ext
  change (x.1 : ℤ) = 0
  exact congrArg (fun z : signedIntegers.ρ.invariants => (z.1 : ℤ))
    (signedIntegers_invariant_eq_zero y)

/-- A sign element in the first factor survives the quotient. -/
theorem unitPairKernel_quotient_nontrivial :
    (QuotientGroup.mk' unitPairKernel ((-1 : ℤˣ), (1 : ℤˣ))) ≠ 1 := by
  intro heq
  have hmem : ((-1 : ℤˣ), (1 : ℤˣ)) ∈ unitPairKernel :=
    (QuotientGroup.eq_one_iff _).mp heq
  have hcontra : (-1 : ℤˣ) = 1 := mem_unitPairKernel _ |>.mp hmem
  exact (by decide : (-1 : ℤˣ) ≠ 1) hcontra

/-- The surviving quotient sign is its own inverse. -/
theorem unitPairKernel_quotient_sign_inv :
    (QuotientGroup.mk' unitPairKernel ((-1 : ℤˣ), (1 : ℤˣ)))⁻¹ =
      QuotientGroup.mk' unitPairKernel ((-1 : ℤˣ), (1 : ℤˣ)) := by
  rw [← map_inv]
  simp

/-- The integral quotient function supported on the identity coset. -/
noncomputable def unitPairCosetOne :
    TopRep.coind₁ (TopRep.of
      (ContRepresentation.trivial ℤ ((ℤˣ × ℤˣ) ⧸ unitPairKernel)
        unitPairSignCoefficients)) := by
  classical
  letI : DiscreteTopology ((ℤˣ × ℤˣ) ⧸ unitPairKernel) :=
    QuotientGroup.discreteTopology (isOpen_discrete (unitPairKernel : Set (ℤˣ × ℤˣ)))
  exact ⟨fun q => if q = 1 then (1 : ℤ) else 0, continuous_of_discreteTopology⟩

/-- The identity coset has coefficient `1`. -/
@[simp] theorem unitPairCosetOne_one : unitPairCosetOne 1 = (1 : ℤ) := by
  simp [unitPairCosetOne]
  rfl

/-- The nonidentity coset has coefficient zero. -/
theorem unitPairCosetOne_other :
    unitPairCosetOne (QuotientGroup.mk' unitPairKernel ((-1 : ℤˣ), (1 : ℤˣ))) = 0 := by
  simp [unitPairCosetOne]

/-- The surviving quotient sign swaps the supported and unsupported cosets. -/
theorem unitPairCosetOne_quotient_moved :
    ((TopRep.coind₁ (TopRep.of
      (ContRepresentation.trivial ℤ ((ℤˣ × ℤˣ) ⧸ unitPairKernel)
        unitPairSignCoefficients))).ρ
      (QuotientGroup.mk' unitPairKernel ((-1 : ℤˣ), (1 : ℤˣ)))
      unitPairCosetOne) 1 ≠ unitPairCosetOne 1 := by
  rw [ContRepresentation.coind₁_apply_apply]
  simp only [ContRepresentation.trivial_apply, mul_one]
  rw [unitPairKernel_quotient_sign_inv, unitPairCosetOne_other, unitPairCosetOne_one]
  change (0 : ℤ) ≠ 1
  norm_num

/-- The inverse image has value `1` at the identity of the original group. -/
theorem unitPairCosetOne_inverse_one :
    ((TopRep.quotientCoind₁Iso unitPairKernel unitPairSignCoefficients).inv
      unitPairCosetOne).1 (1 : ℤˣ × ℤˣ) = (1 : ℤ) := by
  rw [TopRep.quotientCoind₁Iso_inv_apply]
  simpa using unitPairCosetOne_one

/-- A quotient-invariant coinduced function need not take fixed values:
the independent sign calculation and the inverse evaluation identify one. -/
theorem unitPairInvariant_not_pointwise_fixed :
    unitPairSignCoefficients.ρ unitPairSignFlip
      (((TopRep.quotientCoind₁Iso unitPairKernel unitPairSignCoefficients).inv
        unitPairCosetOne).1 (1 : ℤˣ × ℤˣ)) ≠
      ((TopRep.quotientCoind₁Iso unitPairKernel unitPairSignCoefficients).inv
        unitPairCosetOne).1 (1 : ℤˣ × ℤˣ) := by
  rw [unitPairCosetOne_inverse_one]
  exact unitPairSignFlip_not_fixed

/-- Even the full-group invariant representation can have a value moved by
the coefficient action at the identity. -/
theorem unitPairTopInvariant_not_pointwise_fixed :
    ∃ f : TopRep.quotientInvariants (⊤ : Subgroup (ℤˣ × ℤˣ))
        (TopRep.coind₁ unitPairSignCoefficients),
      unitPairSignCoefficients.ρ unitPairSignFlip (f.1 (1 : ℤˣ × ℤˣ)) ≠
        f.1 (1 : ℤˣ × ℤˣ) := by
  let F : TopRep.coind₁ (TopRep.of
      (ContRepresentation.trivial ℤ ((ℤˣ × ℤˣ) ⧸ (⊤ : Subgroup (ℤˣ × ℤˣ)))
        unitPairSignCoefficients)) := ContinuousMap.const _ (1 : ℤ)
  have hF : F (QuotientGroup.mk' (⊤ : Subgroup (ℤˣ × ℤˣ))
      (1 : ℤˣ × ℤˣ)) = (1 : ℤ) := rfl
  refine ⟨(TopRep.quotientCoind₁Iso (⊤ : Subgroup (ℤˣ × ℤˣ))
    unitPairSignCoefficients).inv F, ?_⟩
  rw [TopRep.quotientCoind₁Iso_inv_apply]
  rw [hF]
  simp only [map_one, ContinuousLinearMap.one_def]
  exact unitPairSignFlip_not_fixed

end CGCExamples
