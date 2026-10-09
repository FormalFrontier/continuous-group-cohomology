/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ClosedTopologicalCoinvariants
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Instances.ZMod

/-!
# Closed topological reduction modulo `n`

For an additive topological commutative group `A`, this file defines
`TopologicalModN A n` to be the quotient of `A` by the topological closure of
the subgroup of `n`-fold multiples.  The input is not assumed separated.  In
particular, at `n = 0` this is the separation quotient by the closure of zero,
not unconditionally `A` itself.

The API supplies both the exact closed-kernel universal property and the more
convenient pointwise property for T1 targets.  It also supplies functoriality,
the compact Hausdorff comparison with algebraic `ModN`, a multiplicative
closed-power facade, and descent of actions by individually continuous
automorphisms.  No topology on the acting group and no joint-continuity claim
is introduced.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalModN

variable (A : Type uA) [AddCommGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A]

/-- The subgroup of `n`-fold multiples in an additive commutative group. -/
def multiples (n : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom n).range

/-- The topological closure of the subgroup of `n`-fold multiples. -/
def closedMultiples (n : ℕ) : AddSubgroup A :=
  (multiples A n).topologicalClosure

end TopologicalModN

/-- The quotient of `A` by the closure of its subgroup of `n`-fold multiples,
with mathlib's quotient topology. -/
abbrev TopologicalModN (A : Type uA) [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) :=
  A ⧸ TopologicalModN.closedMultiples A n

namespace TopologicalModN

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [IsTopologicalAddGroup C]

/-- The canonical continuous additive quotient homomorphism. -/
def mkQ (n : ℕ) : A →ₜ+ TopologicalModN A n where
  toAddMonoidHom := QuotientAddGroup.mk' (closedMultiples A n)
  continuous_toFun := QuotientAddGroup.continuous_mk

@[simp]
theorem mkQ_apply (n : ℕ) (a : A) :
    mkQ (A := A) n a = QuotientAddGroup.mk a := rfl

/-- Every multiple belongs to the closed subgroup of multiples. -/
theorem nsmul_mem_closedMultiples (n : ℕ) (a : A) :
    n • a ∈ closedMultiples A n :=
  AddSubgroup.le_topologicalClosure (multiples A n) ⟨a, rfl⟩

/-- The closed mod-`n` quotient is canonically a `ZMod n`-module, for every
natural `n`, including zero and one. -/
instance instModule (n : ℕ) : Module (ZMod n) (TopologicalModN A n) :=
  QuotientAddGroup.zmodModule (nsmul_mem_closedMultiples (A := A) n)

/-- Scalar multiplication by the discrete ring `ZMod n` is jointly
continuous. -/
instance instContinuousSMul (n : ℕ) :
    ContinuousSMul (ZMod n) (TopologicalModN A n) where
  continuous_smul := by
    rw [continuous_prod_of_discrete_left]
    intro z
    change Continuous fun x : TopologicalModN A n ↦ z • x
    rw [← ZMod.intCast_zmod_cast z]
    have hz : Continuous
        (fun x : TopologicalModN A n ↦ (ZMod.cast z : ℤ) • x) :=
      continuous_zsmul _
    simpa only [Int.cast_smul_eq_zsmul] using hz

/-- The quotient is T1 even when the input group is not. -/
instance instT1Space (n : ℕ) : T1Space (TopologicalModN A n) :=
  QuotientAddGroup.t1Space_iff.mpr
    (multiples A n).isClosed_topologicalClosure

/-- The quotient is Hausdorff even when the input group is not. -/
instance instT2Space (n : ℕ) : T2Space (TopologicalModN A n) := by
  infer_instance

/-- Pointwise formulation saying that a homomorphism kills all `n`-fold
multiples. -/
def KillsMultiples (n : ℕ) (f : A → B) : Prop :=
  ∀ a, n • f a = 0

omit [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] in
/-- Killing all pointwise multiples kills the algebraic multiple subgroup. -/
theorem multiples_le_ker (n : ℕ) (f : A →+ B)
    (hf : KillsMultiples n f) : multiples A n ≤ f.ker := by
  rintro x ⟨a, rfl⟩
  change f (n • a) = 0
  rw [map_nsmul, hf a]

/-- Raw universal property.  Without a separation condition on the target,
the exact hypothesis is containment of the closed multiple subgroup in the
kernel. -/
def liftOfClosed (n : ℕ) (f : A →ₜ+ B)
    (hf : closedMultiples A n ≤ f.ker) : TopologicalModN A n →ₜ+ B where
  toAddMonoidHom := QuotientAddGroup.lift (closedMultiples A n) f hf
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk
      (closedMultiples A n)).continuous_iff]
    exact f.continuous

omit [IsTopologicalAddGroup B] in
@[simp]
theorem liftOfClosed_mk (n : ℕ) (f : A →ₜ+ B)
    (hf : closedMultiples A n ≤ f.ker) (a : A) :
    liftOfClosed n f hf (mkQ n a) = f a := rfl

omit [IsTopologicalAddGroup B] in
/-- For a T1 target, pointwise killing of multiples implies the exact closed
kernel hypothesis. -/
theorem closedMultiples_le_ker [T1Space B] (n : ℕ) (f : A →ₜ+ B)
    (hf : KillsMultiples n f) : closedMultiples A n ≤ f.ker := by
  apply AddSubgroup.topologicalClosure_minimal
  · exact multiples_le_ker (A := A) (B := B) n f.toAddMonoidHom hf
  · exact isClosed_singleton.preimage f.continuous

/-- Universal property for continuous homomorphisms to T1 targets which kill
all `n`-fold multiples. -/
def lift [T1Space B] (n : ℕ) (f : A →ₜ+ B)
    (hf : KillsMultiples n f) : TopologicalModN A n →ₜ+ B :=
  liftOfClosed n f (closedMultiples_le_ker n f hf)

omit [IsTopologicalAddGroup B] in
@[simp]
theorem lift_mk [T1Space B] (n : ℕ) (f : A →ₜ+ B)
    (hf : KillsMultiples n f) (a : A) :
    lift n f hf (mkQ n a) = f a := rfl

omit [IsTopologicalAddGroup B] in
/-- Continuous additive homomorphisms out of the quotient are determined on
representatives. -/
theorem hom_ext (n : ℕ) {f g : TopologicalModN A n →ₜ+ B}
    (h : f.comp (mkQ n) = g.comp (mkQ n)) : f = g := by
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact DFunLike.congr_fun h a

/-- A continuous homomorphism sends the closed multiple subgroup into the
closed multiple subgroup. -/
theorem map_closedMultiples_le (n : ℕ) (f : A →ₜ+ B) :
    closedMultiples A n ≤ (closedMultiples B n).comap f := by
  apply AddSubgroup.topologicalClosure_minimal
  · rintro x ⟨a, rfl⟩
    simpa [nsmulAddMonoidHom] using
      (nsmul_mem_closedMultiples (A := B) n (f a))
  · change IsClosed (f ⁻¹' (closedMultiples B n : Set B))
    exact (multiples B n).isClosed_topologicalClosure.preimage
      f.continuous

/-- Functoriality of closed topological reduction modulo `n`. -/
def map (n : ℕ) (f : A →ₜ+ B) :
    TopologicalModN A n →ₜ+ TopologicalModN B n :=
  liftOfClosed n ((mkQ n).comp f) (by
    intro x hx
    exact (QuotientAddGroup.eq_zero_iff (f x)).mpr
      (map_closedMultiples_le n f hx))

@[simp]
theorem map_mk (n : ℕ) (f : A →ₜ+ B) (a : A) :
    map n f (mkQ n a) = mkQ n (f a) := rfl

/-- Reduction maps the identity homomorphism to the identity. -/
theorem map_id (n : ℕ) :
    map n (ContinuousAddMonoidHom.id A) =
      ContinuousAddMonoidHom.id (TopologicalModN A n) := by
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- Reduction respects composition. -/
theorem map_comp (n : ℕ) (f : A →ₜ+ B) (g : B →ₜ+ C) :
    map n (g.comp f) = (map n g).comp (map n f) := by
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- A continuous additive equivalence induces a continuous equivalence after
closed topological reduction. -/
def congr (n : ℕ) (e : A ≃ₜ+ B) :
    TopologicalModN A n ≃ₜ+ TopologicalModN B n := by
  let ef : A →ₜ+ B :=
    { toAddMonoidHom := e.toAddMonoidHom
      continuous_toFun := e.continuous }
  let einf : B →ₜ+ A :=
    { toAddMonoidHom := e.symm.toAddMonoidHom
      continuous_toFun := e.symm.continuous }
  exact
    { toFun := map n ef
      invFun := map n einf
      left_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        change map n einf (map n ef (mkQ n a)) = mkQ n a
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.symm_apply_apply a)
      right_inv := fun x ↦ by
        obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
        change map n ef (map n einf (mkQ n b)) = mkQ n b
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.apply_symm_apply b)
      map_add' := (map n ef).map_add
      continuous_toFun := (map n ef).continuous
      continuous_invFun := (map n einf).continuous }

@[simp]
theorem congr_mk (n : ℕ) (e : A ≃ₜ+ B) (a : A) :
    congr n e (mkQ n a) = mkQ n (e a) := by
  change map n
    ({ toAddMonoidHom := e.toAddMonoidHom
       continuous_toFun := e.continuous } : A →ₜ+ B) (mkQ n a) = _
  rw [map_mk]
  rfl

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
@[simp]
theorem multiples_zero : multiples A 0 = ⊥ := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro ha
    rw [AddSubgroup.mem_bot] at ha
    subst a
    exact ⟨0, by simp⟩

/-- At `n = 0`, the denominator is the closure of zero. -/
@[simp]
theorem closedMultiples_zero :
    closedMultiples A 0 = (⊥ : AddSubgroup A).topologicalClosure := by
  rw [closedMultiples, multiples_zero]

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
@[simp]
theorem multiples_one : multiples A 1 = ⊤ := by
  ext a
  simp [multiples]

@[simp]
theorem closedMultiples_one : closedMultiples A 1 = ⊤ := by
  apply le_antisymm le_top
  rw [← multiples_one (A := A)]
  exact AddSubgroup.le_topologicalClosure _

/-- Algebraic `ModN` carries the quotient topology induced by `ModN.mkQ`. -/
instance instTopologicalSpaceModN (n : ℕ) : TopologicalSpace (ModN A n) :=
  TopologicalSpace.coinduced (ModN.mkQ n) inferInstance

/-- The algebraic mod-`n` quotient map, bundled continuously for the quotient
topology on `ModN`. -/
def modNMk (n : ℕ) : A →ₜ+ ModN A n where
  toAddMonoidHom := ModN.mkQ n
  continuous_toFun := continuous_coinduced_rng

omit [IsTopologicalAddGroup A] in
@[simp]
theorem modNMk_apply (n : ℕ) (a : A) : modNMk n a = ModN.mkQ n a := rfl

/-- The algebraic quotient maps continuously to the closed quotient for every
topological additive commutative group.  It is generally a further quotient,
not an equivalence. -/
def algebraicToClosed (n : ℕ) : ModN A n →ₜ+ TopologicalModN A n := by
  let H := (LinearMap.range (LinearMap.lsmul ℤ A n)).toAddSubgroup
  have hH : H ≤ (mkQ n).ker := by
    rintro x ⟨a, rfl⟩
    change mkQ n ((LinearMap.lsmul ℤ A n) a) = 0
    apply (QuotientAddGroup.eq_zero_iff
      ((LinearMap.lsmul ℤ A n) a)).mpr
    simpa using (nsmul_mem_closedMultiples (A := A) n a)
  let hom : ModN A n →+ TopologicalModN A n :=
    QuotientAddGroup.lift H (mkQ (A := A) n).toAddMonoidHom hH
  exact
    { toAddMonoidHom := hom
      continuous_toFun := by
        change Continuous hom
        rw [continuous_iff_coinduced_le]
        unfold instTopologicalSpaceModN
        rw [coinduced_compose]
        rw [show (hom : ModN A n → TopologicalModN A n) ∘
            (ModN.mkQ n : A → ModN A n) =
            (mkQ n : A → TopologicalModN A n) by
          funext a
          rfl]
        exact continuous_iff_coinduced_le.mp (mkQ n).continuous }

@[simp]
theorem algebraicToClosed_mk (n : ℕ) (a : A) :
    algebraicToClosed n (modNMk n a) = mkQ n a := by
  unfold algebraicToClosed modNMk
  dsimp only
  rfl

section CompactHausdorff

variable [CompactSpace A] [T2Space A]

omit [T2Space A] in
/-- On a compact Hausdorff group, the subgroup of multiples is compact. -/
theorem multiples_isCompact (n : ℕ) :
    IsCompact (multiples A n : Set A) := by
  change IsCompact (Set.range fun a : A ↦ n • a)
  exact isCompact_range (continuous_nsmul n)

/-- On a compact Hausdorff group, the subgroup of multiples is closed. -/
theorem multiples_isClosed (n : ℕ) :
    IsClosed (multiples A n : Set A) :=
  (multiples_isCompact (A := A) n).isClosed

/-- On the compact Hausdorff boundary, taking the closure does not enlarge
the multiple subgroup. -/
theorem closedMultiples_eq (n : ℕ) :
    closedMultiples A n = multiples A n :=
  le_antisymm
    (AddSubgroup.topologicalClosure_minimal _ le_rfl
      (multiples_isClosed (A := A) n))
    (AddSubgroup.le_topologicalClosure _)

omit [TopologicalSpace A] [IsTopologicalAddGroup A]
    [CompactSpace A] [T2Space A] in
/-- The subgroup used by algebraic `ModN` is the subgroup of `n`-fold
multiples. -/
theorem multiples_eq_modNSubgroup (n : ℕ) :
    multiples A n =
      (LinearMap.range (LinearMap.lsmul ℤ A n)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp⟩

/-- For a compact Hausdorff group, the closed quotient is continuously
additively equivalent to mathlib's algebraic `ModN`, equipped with its quotient
topology. -/
def compactToModN (n : ℕ) : TopologicalModN A n →ₜ+ ModN A n :=
  liftOfClosed n (modNMk n) (by
    intro x hx
    apply (QuotientAddGroup.eq_zero_iff x).mpr
    rw [← multiples_eq_modNSubgroup (A := A) n,
      ← closedMultiples_eq (A := A) n]
    exact hx)

@[simp]
theorem compactToModN_mk (n : ℕ) (a : A) :
    compactToModN (A := A) n (mkQ n a) = modNMk n a :=
  liftOfClosed_mk n (modNMk n) _ a

/-- For a compact Hausdorff group, the closed quotient is continuously
additively equivalent to mathlib's algebraic `ModN`, equipped with its quotient
topology. -/
def compactModNEquiv (n : ℕ) : TopologicalModN A n ≃ₜ+ ModN A n := by
  let forward : TopologicalModN A n →ₜ+ ModN A n := compactToModN n
  let inverse : ModN A n →ₜ+ TopologicalModN A n :=
    algebraicToClosed n
  exact
    { toFun := forward
      invFun := inverse
      left_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        calc
          inverse (forward (mkQ n a)) = inverse (modNMk n a) :=
            congrArg inverse (compactToModN_mk n a)
          _ = mkQ n a := algebraicToClosed_mk n a
      right_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
        calc
          forward (inverse (modNMk n a)) = forward (mkQ n a) :=
            congrArg forward (algebraicToClosed_mk n a)
          _ = modNMk n a := compactToModN_mk n a
      map_add' := forward.map_add
      continuous_toFun := forward.continuous
      continuous_invFun := inverse.continuous }

@[simp]
theorem compactModNEquiv_mk (n : ℕ) (a : A) :
    compactModNEquiv (A := A) n (mkQ n a) = ModN.mkQ n a := by
  unfold compactModNEquiv
  dsimp only
  change compactToModN (A := A) n (mkQ n a) = _
  rw [compactToModN_mk]
  rfl

end CompactHausdorff

end TopologicalModN

namespace TopologicalPowerQuotient

/-- The subgroup of `n`-th powers. -/
def powers (A : Type uA) [CommGroup A] (n : ℕ) : Subgroup A :=
  (powMonoidHom n).range

/-- The topological closure of the subgroup of `n`-th powers. -/
def closedPowers (A : Type uA) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] (n : ℕ) : Subgroup A :=
  (powers A n).topologicalClosure

end TopologicalPowerQuotient

/-- Multiplicative facade for the quotient by the closure of `n`-th powers. -/
abbrev TopologicalPowerQuotient (A : Type uA) [CommGroup A]
    [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) :=
  A ⧸ TopologicalPowerQuotient.closedPowers A n

namespace TopologicalPowerQuotient

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [CommGroup A] [CommGroup B] [CommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C]

/-- The multiplicative facade is definitionally the quotient by the closed
power subgroup. -/
theorem presentation (n : ℕ) :
    TopologicalPowerQuotient A n = (A ⧸ closedPowers A n) := rfl

/-- The direct closed-power presentation agrees definitionally with the
multiplicative form of the additive closed-multiple quotient. -/
theorem multiplicativePresentation (n : ℕ) :
    TopologicalPowerQuotient A n =
      Multiplicative (TopologicalModN (Additive A) n) := rfl

/-- The closed-power quotient is T1 even when the input group is not. -/
instance instT1Space (n : ℕ) : T1Space (TopologicalPowerQuotient A n) :=
  QuotientGroup.t1Space_iff.mpr
    (powers A n).isClosed_topologicalClosure

/-- The closed-power quotient is Hausdorff even when the input group is not. -/
instance instT2Space (n : ℕ) : T2Space (TopologicalPowerQuotient A n) := by
  infer_instance

/-- The canonical continuous multiplicative quotient homomorphism. -/
def mkQ (n : ℕ) : A →ₜ* TopologicalPowerQuotient A n where
  toMonoidHom := QuotientGroup.mk' (closedPowers A n)
  continuous_toFun := QuotientGroup.continuous_mk

@[simp]
theorem mkQ_apply (n : ℕ) (a : A) :
    mkQ (A := A) n a = QuotientGroup.mk a := rfl

/-- Every `n`-th power belongs to the closed power subgroup. -/
theorem pow_mem_closedPowers (n : ℕ) (a : A) :
    a ^ n ∈ closedPowers A n :=
  Subgroup.le_topologicalClosure (powers A n) ⟨a, rfl⟩

/-- A continuous homomorphism sends the closed power subgroup into the closed
power subgroup. -/
theorem map_closedPowers_le (n : ℕ) (f : A →ₜ* B) :
    closedPowers A n ≤ (closedPowers B n).comap f := by
  apply Subgroup.topologicalClosure_minimal
  · rintro x ⟨a, rfl⟩
    simpa [powMonoidHom] using
      (pow_mem_closedPowers (A := B) n (f a))
  · change IsClosed (f ⁻¹' (closedPowers B n : Set B))
    exact (powers B n).isClosed_topologicalClosure.preimage
      f.continuous

/-- Functoriality of the multiplicative closed-power quotient. -/
def map (n : ℕ) (f : A →ₜ* B) :
    TopologicalPowerQuotient A n →ₜ* TopologicalPowerQuotient B n where
  toMonoidHom := QuotientGroup.lift (closedPowers A n) ((mkQ n).comp f) (by
    intro x hx
    exact (QuotientGroup.eq_one_iff (f x)).mpr
      (map_closedPowers_le n f hx))
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk
      (closedPowers A n)).continuous_iff]
    exact (mkQ n).continuous.comp f.continuous

@[simp]
theorem map_mk (n : ℕ) (f : A →ₜ* B) (a : A) :
    map n f (mkQ n a) = mkQ n (f a) := rfl

theorem map_id (n : ℕ) :
    map n (ContinuousMonoidHom.id A) =
      ContinuousMonoidHom.id (TopologicalPowerQuotient A n) := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem map_comp (n : ℕ) (f : A →ₜ* B) (g : B →ₜ* C) :
    map n (g.comp f) = (map n g).comp (map n f) := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- A continuous multiplicative equivalence induces an equivalence of closed
power quotients. -/
def congr (n : ℕ) (e : A ≃ₜ* B) :
    TopologicalPowerQuotient A n ≃ₜ* TopologicalPowerQuotient B n := by
  let ef : A →ₜ* B :=
    { toMonoidHom := e.toMonoidHom
      continuous_toFun := e.continuous }
  let einf : B →ₜ* A :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := e.symm.continuous }
  exact
    { toFun := map n ef
      invFun := map n einf
      left_inv := fun x ↦ by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        change map n einf (map n ef (mkQ n a)) = mkQ n a
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.symm_apply_apply a)
      right_inv := fun x ↦ by
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
        change map n ef (map n einf (mkQ n b)) = mkQ n b
        rw [map_mk, map_mk]
        exact congrArg (mkQ n) (e.apply_symm_apply b)
      map_mul' := (map n ef).map_mul
      continuous_toFun := (map n ef).continuous
      continuous_invFun := (map n einf).continuous }

@[simp]
theorem congr_mk (n : ℕ) (e : A ≃ₜ* B) (a : A) :
    congr n e (mkQ n a) = mkQ n (e a) := by
  change map n
    ({ toMonoidHom := e.toMonoidHom
       continuous_toFun := e.continuous } : A →ₜ* B) (mkQ n a) = _
  rw [map_mk]
  rfl

end TopologicalPowerQuotient

namespace PointwiseContinuousMulAction

variable {Q : Type uQ} {A : Type uA} {B : Type uB}
  [Group Q] [CommGroup A] [CommGroup B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B]

/-- Descend every individually continuous automorphism to the quotient by
closed `n`-th powers. -/
def topologicalPowerQuotient (rho : PointwiseContinuousMulAction Q A)
    (n : ℕ) : PointwiseContinuousMulAction Q (TopologicalPowerQuotient A n) where
  toMonoidHom :=
    { toFun := fun q ↦
        (TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q)).toMulEquiv
      map_one' := by
        apply MulEquiv.ext
        intro x
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        change TopologicalPowerQuotient.congr n
          (rho.continuousMulEquiv 1) (TopologicalPowerQuotient.mkQ n a) =
            TopologicalPowerQuotient.mkQ n a
        rw [TopologicalPowerQuotient.congr_mk]
        change TopologicalPowerQuotient.mkQ n (rho 1 a) =
          TopologicalPowerQuotient.mkQ n a
        rw [rho.map_one]
      map_mul' := fun q q' ↦ by
        apply MulEquiv.ext
        intro x
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
        change TopologicalPowerQuotient.congr n
          (rho.continuousMulEquiv (q * q'))
            (TopologicalPowerQuotient.mkQ n a) =
          TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q)
            (TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q')
              (TopologicalPowerQuotient.mkQ n a))
        rw [TopologicalPowerQuotient.congr_mk,
          TopologicalPowerQuotient.congr_mk,
          TopologicalPowerQuotient.congr_mk]
        change TopologicalPowerQuotient.mkQ n (rho (q * q') a) =
          TopologicalPowerQuotient.mkQ n (rho q (rho q' a))
        rw [rho.map_mul] }
  continuous_toFun := fun q ↦
    (TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q)).continuous

/-- Exact representative formula for the descended action. -/
@[simp]
theorem topologicalPowerQuotient_mk
    (rho : PointwiseContinuousMulAction Q A) (n : ℕ) (q : Q) (a : A) :
    rho.topologicalPowerQuotient n q (TopologicalPowerQuotient.mkQ n a) =
      TopologicalPowerQuotient.mkQ n (rho q a) := by
  change TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q)
    (TopologicalPowerQuotient.mkQ n a) = _
  rw [TopologicalPowerQuotient.congr_mk]
  change TopologicalPowerQuotient.mkQ n (rho q a) = _
  rfl

/-- An equivariant continuous homomorphism remains equivariant after passing
to closed power quotients. -/
theorem topologicalPowerQuotient_isEquivariant
    (rho : PointwiseContinuousMulAction Q A)
    (sigma : PointwiseContinuousMulAction Q B)
    (n : ℕ) (f : A →ₜ* B) (hf : rho.IsEquivariant sigma f) :
    (rho.topologicalPowerQuotient n).IsEquivariant
      (sigma.topologicalPowerQuotient n)
      (TopologicalPowerQuotient.map n f) := by
  intro q x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  change TopologicalPowerQuotient.map n f
      (TopologicalPowerQuotient.congr n (rho.continuousMulEquiv q)
        (TopologicalPowerQuotient.mkQ n a)) =
    TopologicalPowerQuotient.congr n (sigma.continuousMulEquiv q)
      (TopologicalPowerQuotient.map n f
        (TopologicalPowerQuotient.mkQ n a))
  rw [TopologicalPowerQuotient.congr_mk, TopologicalPowerQuotient.map_mk,
    TopologicalPowerQuotient.map_mk, TopologicalPowerQuotient.congr_mk]
  change TopologicalPowerQuotient.mkQ n (f (rho q a)) =
    TopologicalPowerQuotient.mkQ n (sigma q (f a))
  rw [hf q a]

end PointwiseContinuousMulAction

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Reduce the quotient-conjugation action before forming closed
coinvariants. -/
abbrev quotientConjActTopologicalAbelianizationModNAction
    (S : ContinuousGroupExtension N E Q) (n : ℕ) :=
  S.quotientConjActTopologicalAbelianizationAction.topologicalPowerQuotient n

/-- Closed coinvariants formed after closed topological reduction modulo `n`.
This definition deliberately does not identify the result with reduction
performed after coinvariants. -/
abbrev quotientConjActTopologicalAbelianizationModNCoinvariants
    (S : ContinuousGroupExtension N E Q) (n : ℕ) :=
  (S.quotientConjActTopologicalAbelianizationModNAction n).Coinvariants

namespace Equiv

variable {E' : Type uE'} [Group E'] [TopologicalSpace E']
  [IsTopologicalGroup E']
  {S : ContinuousGroupExtension N E Q}
  {S' : ContinuousGroupExtension N E' Q}

/-- Fixed-kernel/fixed-quotient extension equivalences preserve the
descended action after closed topological reduction. -/
theorem quotientConjActTopologicalAbelianizationModNAction
    (equiv : S.Equiv S') (n : ℕ) :
    S'.quotientConjActTopologicalAbelianizationModNAction n =
      S.quotientConjActTopologicalAbelianizationModNAction n := by
  change
    S'.quotientConjActTopologicalAbelianizationAction.topologicalPowerQuotient n =
      S.quotientConjActTopologicalAbelianizationAction.topologicalPowerQuotient n
  rw [equiv.quotientConjActTopologicalAbelianizationAction]

/-- Extension equivalences induce the identity-on-representatives continuous
equivalence between the reduced closed coinvariants. -/
def quotientConjActTopologicalAbelianizationModNCoinvariantsEquiv
    (equiv : S.Equiv S') (n : ℕ) :
    S.quotientConjActTopologicalAbelianizationModNCoinvariants n ≃ₜ*
      S'.quotientConjActTopologicalAbelianizationModNCoinvariants n :=
  PointwiseContinuousMulAction.congr
    (S.quotientConjActTopologicalAbelianizationModNAction n)
    (S'.quotientConjActTopologicalAbelianizationModNAction n)
    (ContinuousMulEquiv.refl (TopologicalPowerQuotient
      (TopologicalAbelianization N) n)) (by
        intro q a
        rw [equiv.quotientConjActTopologicalAbelianizationModNAction n]
        rfl)

end Equiv

end ContinuousGroupExtension
