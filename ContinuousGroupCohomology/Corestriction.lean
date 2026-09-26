/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.DegreeOne
public import Mathlib.GroupTheory.Complement
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Corestriction in continuous degree-one cohomology

This file constructs the continuous transfer formula attached to a finite right
transversal of an open finite-index subgroup.  It proves continuity in both the
group and cocycle parameters, the crossed-homomorphism identity, and
compatibility with principal cocycles.  Consequently, a chosen transversal
gives a continuous linear map on crossed-homomorphism quotients and, through
`ContinuousCohomology.degreeOneIso`, a morphism on continuous degree-one
cohomology.  The change-of-transversal formula shows that two such transfers
differ by a principal cocycle, giving a canonical degree-one corestriction map.

The canonical cohomology map is natural in coefficient morphisms, restriction
followed by corestriction is multiplication by the subgroup index, and
corestriction from the whole group is the identity under the canonical
restriction identification.  Corestriction composition and Mackey laws are not
asserted here.
-/

set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace TopRep

/-- Joint continuity is preserved when a representation is restricted to a subgroup. -/
instance jointlyContinuous_res (H : Subgroup G) (X : TopRep.{w} k G)
    [JointlyContinuous X] : JointlyContinuous (res H.subtype X) where
  continuous_action :=
    JointlyContinuous.continuous_action (X := X) |>.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end TopRep

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

/-- The `H`-factor in the unique decomposition `t * g = η(t,g) * (t ⋆ g)`.
Its representative calculation is used in composition of transversals. -/
@[expose]
def factor (t : ↥(T : Set G)) (g : G) : H := (T.2.equiv ((t : G) * g)).1

/-- The new transversal representative in `t * g = η(t,g) * (t ⋆ g)`.
Its representative calculation is used in composition of transversals. -/
@[expose]
def next (t : ↥(T : Set G)) (g : G) : ↥(T : Set G) :=
  (T.2.equiv ((t : G) * g)).2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma factor_mul_next (t : ↥(T : Set G)) (g : G) :
    (factor T t g : G) * (next T t g : G) = (t : G) * g :=
  T.2.equiv_fst_mul_equiv_snd _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma next_one (t : ↥(T : Set G)) : next T t 1 = t := by
  apply Subtype.ext
  simpa [next] using congrArg Subtype.val
    (T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma factor_one (t : ↥(T : Set G)) : factor T t 1 = 1 := by
  apply Subtype.ext
  simpa [factor] using T.2.coe_equiv_fst_eq_one_iff_mem H.one_mem |>.2 t.2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma equiv_mul (t : ↥(T : Set G)) (g g' : G) :
    T.2.equiv ((t : G) * (g * g')) =
      (factor T t g * factor T (next T t g) g', next T (next T t g) g') := by
  rw [← mul_assoc, ← factor_mul_next T t g, mul_assoc, T.2.equiv_mul_left]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma factor_mul (t : ↥(T : Set G)) (g g' : G) :
    factor T t (g * g') = factor T t g * factor T (next T t g) g' :=
  congrArg Prod.fst (equiv_mul T t g g')

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma next_mul (t : ↥(T : Set G)) (g g' : G) :
    next T t (g * g') = next T (next T t g) g' := by
  have h := equiv_mul T t g g'
  have hs := congrArg (fun p : H × ↥(T : Set G) => p.2) h
  exact hs

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma inv_mul_factor (t : ↥(T : Set G)) (g : G) :
    (t : G)⁻¹ * (factor T t g : G) = g * (next T t g : G)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  calc
    ((t : G)⁻¹ * (factor T t g : G)) * (next T t g : G) =
        (t : G)⁻¹ * ((factor T t g : G) * (next T t g : G)) := by
          rw [mul_assoc]
    _ = (t : G)⁻¹ * ((t : G) * g) := by rw [factor_mul_next]
    _ = g := by simp

/-- Right multiplication permutes the chosen right-transversal representatives. -/
@[expose]
def nextEquiv (g : G) : ↥(T : Set G) ≃ ↥(T : Set G) where
  toFun t := next T t g
  invFun t := next T t g⁻¹
  left_inv t := by
    change next T (next T t g) g⁻¹ = t
    rw [← next_mul, mul_inv_cancel, next_one]
  right_inv t := by
    change next T (next T t g⁻¹) g = t
    rw [← next_mul, inv_mul_cancel, next_one]

/-- Openness of the subgroup makes the transversal factor locally continuous. -/
lemma continuous_factor (H : OpenSubgroup G)
    (T : H.toSubgroup.RightTransversal) (t : ↥(T : Set G)) :
    Continuous (factor T t) := by
  apply continuous_induced_rng.2
  rw [continuous_iff_continuousAt]
  intro g
  let s : Set G :=
    {x | ((t : G) * g) * ((t : G) * x)⁻¹ ∈ H}
  have hs : IsOpen s := H.isOpen.preimage <|
    continuous_const.mul (continuous_const.mul continuous_id).inv
  have hg : g ∈ s := by simp [s]
  apply ((continuous_const.mul continuous_id).mul_const
    ((next T t g : G)⁻¹)).continuousAt.congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hg] with x hx
  have hnext : next T t x = next T t g := by
    apply T.2.equiv_snd_eq_iff_rightCosetEquivalence.2
    rw [RightCosetEquivalence, rightCoset_eq_iff H.toSubgroup]
    exact hx
  have hdecomp := factor_mul_next T t x
  rw [hnext] at hdecomp
  exact eq_mul_inv_of_mul_eq hdecomp

/-- The subgroup correction matching a representative in `T` with one in `S`. -/
def changeFactor (S : H.RightTransversal) (t : ↥(T : Set G)) : H :=
  (S.2.equiv (t : G)).1

/-- The representative in `S` of the same right coset as a representative in `T`. -/
def changeRep (S : H.RightTransversal) (t : ↥(T : Set G)) : ↥(S : Set G) :=
  (S.2.equiv (t : G)).2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma changeFactor_mul_changeRep (S : H.RightTransversal) (t : ↥(T : Set G)) :
    (changeFactor T S t : G) * (changeRep T S t : G) = (t : G) :=
  S.2.equiv_fst_mul_equiv_snd _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma changeRep_rightCoset (S : H.RightTransversal) (t : ↥(T : Set G)) :
    RightCosetEquivalence (H : Set G) (changeRep T S t : G) (t : G) := by
  rw [RightCosetEquivalence, rightCoset_eq_iff H]
  rw [← changeFactor_mul_changeRep T S t]
  simp only [mul_inv_cancel_right]
  exact (changeFactor T S t).2

/-- Matching representatives of two right transversals gives an equivalence. -/
@[expose]
def changeRepEquiv (S : H.RightTransversal) :
    ↥(T : Set G) ≃ ↥(S : Set G) where
  toFun := changeRep T S
  invFun := changeRep S T
  left_inv t := by
    change (T.2.equiv (changeRep T S t : G)).2 = t
    calc
      _ = (T.2.equiv (t : G)).2 :=
        T.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset T S t)
      _ = t := T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.2
  right_inv s := by
    change (S.2.equiv (changeRep S T s : G)).2 = s
    calc
      _ = (S.2.equiv (s : G)).2 :=
        S.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset S T s)
      _ = s := S.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem s.2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma changeRep_next (S : H.RightTransversal) (t : ↥(T : Set G)) (g : G) :
    changeRep T S (next T t g) = next S (changeRep T S t) g := by
  change (S.2.equiv (next T t g : G)).2 =
    (S.2.equiv ((changeRep T S t : G) * g)).2
  apply S.2.equiv_snd_eq_iff_rightCosetEquivalence.2
  rw [RightCosetEquivalence, rightCoset_eq_iff H]
  have hdecomp := factor_mul_next T t g
  rw [← changeFactor_mul_changeRep T S t] at hdecomp
  have heq :
      ((changeRep T S t : G) * g) * (next T t g : G)⁻¹ =
        (changeFactor T S t : G)⁻¹ * (factor T t g : G) := by
    apply (eq_inv_mul_iff_mul_eq).2
    calc
      (changeFactor T S t : G) *
          (((changeRep T S t : G) * g) * (next T t g : G)⁻¹) =
          (((changeFactor T S t : G) * (changeRep T S t : G)) * g) *
            (next T t g : G)⁻¹ := by simp only [mul_assoc]
      _ = (factor T t g : G) := (mul_inv_eq_iff_eq_mul).2 hdecomp.symm
  rw [heq]
  exact H.mul_mem (H.inv_mem (changeFactor T S t).2) (factor T t g).2

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma factor_change (S : H.RightTransversal) (t : ↥(T : Set G)) (g : G) :
    factor T t g =
      changeFactor T S t * factor S (changeRep T S t) g *
        (changeFactor T S (next T t g))⁻¹ := by
  apply Subtype.ext
  apply eq_mul_inv_of_mul_eq
  apply mul_right_cancel (b := (changeRep T S (next T t g) : G))
  calc
    ((factor T t g : G) * (changeFactor T S (next T t g) : G)) *
          (changeRep T S (next T t g) : G) =
        (factor T t g : G) * (next T t g : G) := by
      rw [mul_assoc, changeFactor_mul_changeRep]
    _ = (t : G) * g := factor_mul_next T t g
    _ = ((changeFactor T S t : G) * (changeRep T S t : G)) * g := by
      rw [changeFactor_mul_changeRep]
    _ = (changeFactor T S t : G) * ((changeRep T S t : G) * g) := by
      rw [mul_assoc]
    _ = (changeFactor T S t : G) *
          ((factor S (changeRep T S t) g : G) *
            (next S (changeRep T S t) g : G)) := by
      rw [factor_mul_next]
    _ = (changeFactor T S t : G) *
          ((factor S (changeRep T S t) g : G) *
            (changeRep T S (next T t g) : G)) := by
      rw [changeRep_next]
    _ = ((changeFactor T S t : G) *
          (factor S (changeRep T S t) g : G)) *
            (changeRep T S (next T t g) : G) := by
      rw [mul_assoc]

/-- The subgroup factor as a continuous map. -/
def factorC (H : OpenSubgroup G) (T : H.toSubgroup.RightTransversal)
    (t : ↥(T : Set G)) : C(G, H) :=
  ⟨factor T t, continuous_factor H T t⟩

variable (X : TopRep.{max v w} k G)

omit [IsTopologicalGroup G] in
lemma crossed_one (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    f.1 1 = 0 := by
  have h := f.2 1 1
  simpa using h

omit [IsTopologicalGroup G] in
lemma crossed_inv (f : continuousCrossedHom (TopRep.res H.subtype X)) (a : H) :
    f.1 a⁻¹ = -X.ρ ((a : G)⁻¹) (f.1 a) := by
  have h := f.2 a⁻¹ a
  rw [inv_mul_cancel, crossed_one X] at h
  change 0 = X.ρ ((a : G)⁻¹) (f.1 a) + f.1 a⁻¹ at h
  exact eq_neg_of_add_eq_zero_right h.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_mul_apply (a b : G) (x : X) :
    X.ρ a (X.ρ b x) = X.ρ (a * b) x := by
  calc
    _ = (X.ρ a * X.ρ b) x := (mul_apply_eq_comp _ _ _).symm
    _ = X.ρ (a * b) x := by rw [map_mul]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_inv_changeFactor (S : H.RightTransversal) (t : ↥(T : Set G)) (x : X) :
    X.ρ ((t : G)⁻¹) (X.ρ (changeFactor T S t : G) x) =
      X.ρ ((changeRep T S t : G)⁻¹) x := by
  rw [rho_mul_apply]
  congr 2
  rw [← changeFactor_mul_changeRep T S t]
  simp

noncomputable local instance transversalFintype (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal) :
    Fintype ↥(T : Set G) :=
  T.2.finite_right.fintype

/-- The coefficient measuring the change from `T` to `S`. -/
noncomputable def changeCoefficient (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) : X :=
  ∑ t : ↥(T : Set G),
    X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_inv_factor (T : H.RightTransversal) (t : ↥(T : Set G))
    (g : G) (x : X) :
    X.ρ ((t : G)⁻¹) (X.ρ (factor T t g : G) x) =
      X.ρ g (X.ρ ((next T t g : G)⁻¹) x) := by
  calc
    _ = (X.ρ ((t : G)⁻¹) * X.ρ (factor T t g : G)) x :=
      (mul_apply_eq_comp _ _ _).symm
    _ = X.ρ ((t : G)⁻¹ * (factor T t g : G)) x := by rw [map_mul]
    _ = X.ρ (g * (next T t g : G)⁻¹) x := by rw [inv_mul_factor]
    _ = (X.ρ g * X.ρ ((next T t g : G)⁻¹)) x := by rw [map_mul]
    _ = _ := mul_apply_eq_comp _ _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_factor_change (S : H.RightTransversal) (t : ↥(T : Set G))
    (g : G) (x : X) :
    X.ρ ((t : G)⁻¹)
        (X.ρ (changeFactor T S t * factor S (changeRep T S t) g : H)
          (X.ρ ((changeFactor T S (next T t g) : G)⁻¹) x)) =
      X.ρ g (X.ρ ((next T t g : G)⁻¹) x) := by
  calc
    _ = X.ρ ((t : G)⁻¹)
          (X.ρ ((changeFactor T S t * factor S (changeRep T S t) g *
            (changeFactor T S (next T t g))⁻¹ : H) : G) x) := by
      apply congrArg (X.ρ ((t : G)⁻¹))
      rw [rho_mul_apply]
      rfl
    _ = X.ρ ((t : G)⁻¹) (X.ρ (factor T t g : G) x) := by
      rw [factor_change T S t g]
    _ = _ := rho_inv_factor X T t g x

omit [IsTopologicalGroup G] in
lemma transfer_term_change (S : H.RightTransversal) (t : ↥(T : Set G))
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : G) :
    X.ρ ((t : G)⁻¹) (f.1 (factor T t g)) =
      X.ρ ((changeRep T S t : G)⁻¹)
          (f.1 (factor S (changeRep T S t) g)) +
        X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t)) -
          X.ρ g (X.ρ ((next T t g : G)⁻¹)
            (f.1 (changeFactor T S (next T t g)))) := by
  rw [factor_change T S t g, f.2, f.2, crossed_inv X]
  simp only [map_add, map_neg]
  change
    -X.ρ ((t : G)⁻¹)
          (X.ρ (changeFactor T S t * factor S (changeRep T S t) g : H)
            (X.ρ ((changeFactor T S (next T t g) : G)⁻¹)
              (f.1 (changeFactor T S (next T t g))))) +
        (X.ρ ((t : G)⁻¹)
            (X.ρ (changeFactor T S t : G)
              (f.1 (factor S (changeRep T S t) g))) +
          X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))) =
      X.ρ ((changeRep T S t : G)⁻¹)
          (f.1 (factor S (changeRep T S t) g)) +
        X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t)) -
          X.ρ g (X.ρ ((next T t g : G)⁻¹)
            (f.1 (changeFactor T S (next T t g))))
  rw [rho_inv_changeFactor (X := X) T S t]
  rw [rho_factor_change (X := X) T S t g]
  abel

/-- The contribution of one transversal representative to transfer. -/
def transferTerm (H : OpenSubgroup G) (T : H.toSubgroup.RightTransversal)
    (t : ↥(T : Set G)) :
    continuousCrossedHom (TopRep.res H.subtype X) →L[k] C(G, X) :=
  (ContinuousLinearMap.compLeftContinuous k G
      (X.ρ ((t : G)⁻¹))).comp <|
    (ContinuousMap.compCLM k X (factorC H T t)).comp <|
      Submodule.subtypeL (continuousCrossedHom (TopRep.res H.subtype X))

/-- The finite-coordinate transfer formula, before verifying the crossed identity. -/
noncomputable def transferRaw (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) :
    continuousCrossedHom (TopRep.res H.subtype X) →L[k] C(G, X) :=
  ∑ t, transferTerm X H T t

lemma transferRaw_apply (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : G) :
    transferRaw X H T f g =
      ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g)) := by
  classical
  simp only [transferRaw, sum_apply, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  rfl

lemma transferRaw_change (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : G) :
    transferRaw X H T f g =
      transferRaw X H S f g + changeCoefficient X H T S f -
        X.ρ g (changeCoefficient X H T S f) := by
  classical
  rw [transferRaw_apply, transferRaw_apply]
  have hfirst :
      (∑ t : ↥(T : Set G),
        X.ρ ((changeRep T S t : G)⁻¹)
          (f.1 (factor S (changeRep T S t) g))) =
        ∑ s : ↥(S : Set G), X.ρ ((s : G)⁻¹) (f.1 (factor S s g)) := by
    simpa [changeRepEquiv] using
      (Equiv.sum_comp (changeRepEquiv T S)
        (fun s : ↥(S : Set G) =>
          X.ρ ((s : G)⁻¹) (f.1 (factor S s g))))
  have hlast :
      (∑ t : ↥(T : Set G),
        X.ρ g (X.ρ ((next T t g : G)⁻¹)
          (f.1 (changeFactor T S (next T t g))))) =
        X.ρ g (∑ t : ↥(T : Set G),
          X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))) := by
    calc
      _ = X.ρ g (∑ t : ↥(T : Set G),
            X.ρ ((next T t g : G)⁻¹)
              (f.1 (changeFactor T S (next T t g)))) := by
          rw [map_sum]
      _ = _ := by
          apply congrArg (X.ρ g)
          simpa [nextEquiv] using
            (Equiv.sum_comp (nextEquiv T g)
              (fun t : ↥(T : Set G) =>
                X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))))
  calc
    (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g))) =
        ∑ t : ↥(T : Set G),
          (X.ρ ((changeRep T S t : G)⁻¹)
              (f.1 (factor S (changeRep T S t) g)) +
            X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t)) -
              X.ρ g (X.ρ ((next T t g : G)⁻¹)
                (f.1 (changeFactor T S (next T t g))))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact transfer_term_change (X := X) T S t f g
    _ = (∑ t : ↥(T : Set G),
            X.ρ ((changeRep T S t : G)⁻¹)
              (f.1 (factor S (changeRep T S t) g))) +
          (∑ t : ↥(T : Set G),
            X.ρ ((t : G)⁻¹) (f.1 (changeFactor T S t))) -
          (∑ t : ↥(T : Set G),
            X.ρ g (X.ρ ((next T t g : G)⁻¹)
              (f.1 (changeFactor T S (next T t g))))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [hfirst, hlast]
      rfl

lemma transferRaw_crossed (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g g' : G) :
    transferRaw X H T f (g * g') =
      X.ρ g (transferRaw X H T f g') + transferRaw X H T f g := by
  classical
  rw [transferRaw_apply, transferRaw_apply, transferRaw_apply]
  calc
    (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t (g * g')))) =
        ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)
          (X.ρ (factor T t g : G) (f.1 (factor T (next T t g) g')) +
            f.1 (factor T t g)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [factor_mul, f.2]
      rfl
    _ = (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)
            (X.ρ (factor T t g : G) (f.1 (factor T (next T t g) g')))) +
          ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g)) := by
      simp_rw [map_add]
      exact Finset.sum_add_distrib
    _ = X.ρ g (∑ t : ↥(T : Set G),
            X.ρ ((t : G)⁻¹) (f.1 (factor T t g'))) +
          ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g)) := by
      have hfirst :
          (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)
            (X.ρ (factor T t g : G) (f.1 (factor T (next T t g) g')))) =
            X.ρ g (∑ t : ↥(T : Set G),
              X.ρ ((t : G)⁻¹) (f.1 (factor T t g'))) := by
        calc
          _ = ∑ t : ↥(T : Set G), X.ρ g
                (X.ρ ((next T t g : G)⁻¹)
                  (f.1 (factor T (next T t g) g'))) := by
              apply Finset.sum_congr rfl
              intro t _
              exact rho_inv_factor X T t g _
          _ = X.ρ g (∑ t : ↥(T : Set G),
                X.ρ ((next T t g : G)⁻¹)
                  (f.1 (factor T (next T t g) g'))) := by
              rw [map_sum]
          _ = _ := by
              apply congrArg (X.ρ g)
              simpa [nextEquiv] using
                (Equiv.sum_comp (nextEquiv T g)
                  (fun t : ↥(T : Set G) =>
                    X.ρ ((t : G)⁻¹) (f.1 (factor T t g'))))
      exact congrArg (fun y => y +
        ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g))) hfirst

/-- Transfer on continuous crossed homomorphisms for a fixed right transversal. -/
noncomputable def transferCrossed (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) :
    continuousCrossedHom (TopRep.res H.subtype X) →L[k] continuousCrossedHom X :=
  (transferRaw X H T).codRestrict (continuousCrossedHom X) fun f g g' =>
    transferRaw_crossed X H T f g g'

lemma transferCrossed_apply (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : G) :
    (transferCrossed X H T f).1 g =
      ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (factor T t g)) :=
  transferRaw_apply X H T f g

lemma transferCrossed_natural {Y : TopRep.{max v w} k G} (q : X ⟶ Y)
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    crossedMap q (transferCrossed X H T f) =
      transferCrossed Y H T
        (crossedMap ((TopRep.resFunctor H.subtype).map q) f) := by
  ext g
  rw [crossedMap_apply, transferCrossed_apply, transferCrossed_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact TopRep.hom_comm_apply q ((t : G)⁻¹) _

lemma transferCrossed_change (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    transferCrossed X H T f =
      transferCrossed X H S f -
        principalToCrossed X (changeCoefficient X H T S f) := by
  ext g
  change transferRaw X H T f g =
    transferRaw X H S f g -
      (X.ρ g (changeCoefficient X H T S f) - changeCoefficient X H T S f)
  rw [transferRaw_change]
  abel

/-- The coefficient trace associated to the chosen transversal. -/
noncomputable def transferCoefficient (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) : X →L[k] X :=
  ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)

omit [IsTopologicalGroup G] in
lemma transferCoefficient_apply (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) (x : X) :
    transferCoefficient X H T x =
      ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) x := by
  classical
  simp [transferCoefficient]

lemma transferCrossed_principal (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X] (x : X) :
    transferCrossed X H T (principalToCrossed (TopRep.res H.subtype X) x) =
      principalToCrossed X (transferCoefficient X H T x) := by
  classical
  ext g
  rw [transferCrossed_apply]
  change (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)
      (X.ρ (factor T t g : G) x - x)) =
    X.ρ g (transferCoefficient X H T x) - transferCoefficient X H T x
  simp_rw [map_sub]
  rw [Finset.sum_sub_distrib, transferCoefficient_apply]
  have hfirst :
      (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹)
        (X.ρ (factor T t g : G) x)) =
        X.ρ g (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) x) := by
    calc
      _ = ∑ t : ↥(T : Set G),
            X.ρ g (X.ρ ((next T t g : G)⁻¹) x) := by
          apply Finset.sum_congr rfl
          intro t _
          exact rho_inv_factor X T t g x
      _ = X.ρ g (∑ t : ↥(T : Set G),
            X.ρ ((next T t g : G)⁻¹) x) := by
          rw [map_sum]
      _ = _ := by
          apply congrArg (X.ρ g)
          simpa [nextEquiv] using
            (Equiv.sum_comp (nextEquiv T g)
              (fun t : ↥(T : Set G) => X.ρ ((t : G)⁻¹) x))
  rw [hfirst]

/-- Transfer descends continuously through principal cocycles.
Its lift computes on representatives in the transitivity comparison. -/
@[expose]
noncomputable def transferQuotient (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom X ⧸ principalCocycles X) :=
  (principalCocycles (TopRep.res H.subtype X)).liftQL
    ((principalCocycles X).mkQL.comp (transferCrossed X H T)) <| by
      intro f hf
      rw [LinearMap.mem_ker]
      change (principalCocycles X).mkQL (transferCrossed X H T f) = 0
      change f ∈ LinearMap.range
        (principalToCrossed (TopRep.res H.subtype X)) at hf
      rcases hf with ⟨x, rfl⟩
      rw [transferCrossed_principal]
      exact (Submodule.Quotient.mk_eq_zero (principalCocycles X)).2
        ⟨transferCoefficient X H T x, rfl⟩

lemma transfer_mkQL_change (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    (principalCocycles X).mkQL (transferCrossed X H T f) =
      (principalCocycles X).mkQL (transferCrossed X H S f) := by
  rw [transferCrossed_change]
  rw [map_sub]
  have hp :
      (principalCocycles X).mkQL
          (principalToCrossed X (changeCoefficient X H T S f)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (principalCocycles X)).2
      ⟨changeCoefficient X H T S f, rfl⟩
  rw [hp, sub_zero]

/-- Transfer on the quotient is independent of the chosen right transversal. -/
lemma transferQuotient_eq (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    transferQuotient X H T = transferQuotient X H S := by
  apply ContinuousLinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro f
  change (principalCocycles X).mkQL (transferCrossed X H T f) =
    (principalCocycles X).mkQL (transferCrossed X H S f)
  exact transfer_mkQL_change X H T S f

lemma transferQuotient_natural {Y : TopRep.{max v w} k G} (q : X ⟶ Y)
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] [TopRep.JointlyContinuous Y] :
    (crossedQuotientMap q).comp (transferQuotient X H T) =
      (transferQuotient Y H T).comp
        (crossedQuotientMap ((TopRep.resFunctor H.subtype).map q)) := by
  apply ContinuousLinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  change (principalCocycles Y).mkQ (crossedMap q (transferCrossed X H T f)) =
    (principalCocycles Y).mkQ
      (transferCrossed Y H T
        (crossedMap ((TopRep.resFunctor H.subtype).map q) f))
  rw [transferCrossed_natural]

/-- The categorical form of coefficient naturality for fixed-transversal
transfer on crossed-homomorphism quotients. -/
@[reassoc]
lemma transferQuotient_natural_hom {Y : TopRep.{max v w} k G} (q : X ⟶ Y)
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] [TopRep.JointlyContinuous Y] :
    TopModuleCat.ofHom (transferQuotient X H T) ≫
        TopModuleCat.ofHom (crossedQuotientMap q) =
      TopModuleCat.ofHom
          (crossedQuotientMap ((TopRep.resFunctor H.subtype).map q)) ≫
        TopModuleCat.ofHom (transferQuotient Y H T) := by
  ext z
  exact DFunLike.congr_fun (transferQuotient_natural X q H T) z

/-- The degree-one corestriction morphism determined by a right transversal.
Its crossed-quotient formula is used by the composition and Mackey laws. -/
@[expose]
noncomputable def corestrictionOneWithTransversal
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] [LocallyCompactSpace H] :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶ continuousCohomology 1 X :=
  (degreeOneIso (TopRep.res H.subtype X)).inv ≫
    TopModuleCat.ofHom (transferQuotient X H T) ≫
      (degreeOneIso X).hom

/-- Degree-one corestriction is independent of the chosen right transversal. -/
lemma corestrictionOneWithTransversal_eq
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T S : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] [LocallyCompactSpace H] :
    corestrictionOneWithTransversal X H T =
      corestrictionOneWithTransversal X H S := by
  simp only [corestrictionOneWithTransversal]
  rw [transferQuotient_eq X H T S]

/-- Canonical degree-one corestriction for an open finite-index subgroup.
Its default-transversal formula is used by the Mackey comparison. -/
@[expose]
noncomputable def corestrictionOne
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] [LocallyCompactSpace H] :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶ continuousCohomology 1 X :=
  corestrictionOneWithTransversal X H default

/-- The canonical map may be computed using any chosen right transversal. -/
lemma corestrictionOne_eq_withTransversal
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (T : H.toSubgroup.RightTransversal) [TopRep.JointlyContinuous X]
    [LocallyCompactSpace G] [LocallyCompactSpace H] :
    corestrictionOne X H = corestrictionOneWithTransversal X H T :=
  corestrictionOneWithTransversal_eq X H default T

set_option backward.isDefEq.respectTransparency false in
/-- Canonical degree-one corestriction commutes with coefficient morphisms. -/
lemma corestrictionOne_natural {Y : TopRep.{max v w} k G} (q : X ⟶ Y)
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [TopRep.JointlyContinuous Y]
    [LocallyCompactSpace G] [LocallyCompactSpace H] :
    map (ContinuousMonoidHom.id (H : Subgroup G))
          ((TopRep.resFunctor H.subtype).map q) 1 ≫
        corestrictionOne Y H =
      corestrictionOne X H ≫ map (ContinuousMonoidHom.id G) q 1 := by
  simp only [corestrictionOne, corestrictionOneWithTransversal, degreeOneIso_inv]
  rw [homologyQuotientIso_natural_assoc,
    ← transferQuotient_natural_hom_assoc, degreeOneIso_natural]
  simp only [Category.assoc]

/-- Restriction of continuous crossed homomorphisms to an open subgroup.
Its value on subgroup elements is computed by evaluation in the ambient group. -/
@[expose]
def crossedRestrict (H : OpenSubgroup G) :
    continuousCrossedHom X →L[k]
      continuousCrossedHom (TopRep.res H.subtype X) :=
  ((ContinuousMap.compCLM k X
      ⟨H.subtype, continuous_subtype_val⟩).comp
        (Submodule.subtypeL (continuousCrossedHom X))).codRestrict
    (continuousCrossedHom (TopRep.res H.subtype X)) fun f g h => by
      change f.1 (((g * h : H) : G)) = X.ρ (g : G) (f.1 (h : G)) + f.1 (g : G)
      exact f.2 (g : G) (h : G)

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedRestrict_apply (H : OpenSubgroup G)
    (f : continuousCrossedHom X) (h : H) :
    (crossedRestrict X H f).1 h = f.1 (h : G) := rfl

omit [IsTopologicalGroup G] in
lemma crossedRestrict_principal (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] (x : X) :
    crossedRestrict X H (principalToCrossed X x) =
      principalToCrossed (TopRep.res H.subtype X) x := by
  ext h
  rfl

/-- Restriction descends to continuous crossed homomorphisms modulo principal
cocycles. Its application computes on quotient representatives. -/
@[expose]
def crossedQuotientRestrict (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom X ⧸ principalCocycles X) →L[k]
      (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) :=
  (principalCocycles X).liftQL
    ((principalCocycles (TopRep.res H.subtype X)).mkQL.comp
      (crossedRestrict X H)) <| by
      intro f hf
      rw [LinearMap.mem_ker]
      change (principalCocycles (TopRep.res H.subtype X)).mkQL
        (crossedRestrict X H f) = 0
      change f ∈ LinearMap.range (principalToCrossed X) at hf
      rcases hf with ⟨x, rfl⟩
      rw [crossedRestrict_principal]
      exact (Submodule.Quotient.mk_eq_zero
        (principalCocycles (TopRep.res H.subtype X))).2 ⟨x, rfl⟩

omit [IsTopologicalGroup G] in
@[simp]
lemma crossedQuotientRestrict_mk (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] (f : continuousCrossedHom X) :
    crossedQuotientRestrict X H ((principalCocycles X).mkQ f) =
      (principalCocycles (TopRep.res H.subtype X)).mkQ
        (crossedRestrict X H f) := rfl

/-- The continuous inclusion of an open subgroup. -/
def openSubgroupInclusion (H : OpenSubgroup G) : H →ₜ* G where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

/-- The identity coefficient map comparing restriction along the continuous
inclusion with the representation restricted along the underlying subgroup
inclusion. -/
def restrictionCoeffHom (H : OpenSubgroup G) :
    TopRep.res (openSubgroupInclusion H : H →* G) X ⟶
      TopRep.res H.subtype X :=
  TopRep.ofHom {
    __ := ContinuousLinearMap.id k X
    isIntertwining' := by intro h; rfl }

omit [IsTopologicalGroup G] in
lemma crossedRestrict_comp_mkQL (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (crossedRestrict X H) ≫
        TopModuleCat.ofHom
          (principalCocycles (TopRep.res H.subtype X)).mkQL =
      TopModuleCat.ofHom (principalCocycles X).mkQL ≫
        TopModuleCat.ofHom (crossedQuotientRestrict X H) := by
  ext f
  rfl

/-- An open subgroup inherits the ambient topological-group structure. -/
instance openSubgroupIsTopologicalGroup (H : OpenSubgroup G) :
    IsTopologicalGroup H := by
  change IsTopologicalGroup H.toSubgroup
  infer_instance

set_option maxHeartbeats 800000 in
lemma cocyclesOneCrossedIso_restrict (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] :
    cocyclesMap (openSubgroupInclusion H) (restrictionCoeffHom X H) 1 ≫
        (cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom =
      (cocyclesOneCrossedIso X).hom ≫
        TopModuleCat.ofHom (crossedRestrict X H) := by
  ext σ h
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom]
  change
    (((cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom
      (cocyclesMap (openSubgroupInclusion H) (restrictionCoeffHom X H) 1 σ)).1 h) =
      (((cocyclesOneCrossedIso X).hom σ).1 (h : G))
  rw [cocyclesOneCrossedIso_hom_apply, cocyclesOneCrossedIso_hom_apply]
  have hh := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (openSubgroupInclusion H) (restrictionCoeffHom X H)) 1) σ
  exact congrArg (fun τ => τ.1 1 h) hh

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homologyQuotientIso_restrict (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] :
    map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1 ≫
        (homologyQuotientIso (TopRep.res H.subtype X)).hom =
      (homologyQuotientIso X).hom ≫
        TopModuleCat.ofHom (crossedQuotientRestrict X H) := by
  apply (cancel_epi (π X 1)).1
  rw [← Category.assoc, π_map, Category.assoc,
    π_comp_homologyQuotientIso, ← Category.assoc,
    cocyclesOneCrossedIso_restrict, Category.assoc,
    crossedRestrict_comp_mkQL, ← Category.assoc,
    ← π_comp_homologyQuotientIso, Category.assoc]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The crossed-homomorphism restriction map agrees with mathlib's native
continuous-cohomology restriction in degree one. -/
lemma degreeOneIso_restrict (H : OpenSubgroup G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] :
    TopModuleCat.ofHom (crossedQuotientRestrict X H) ≫
        (degreeOneIso (TopRep.res H.subtype X)).hom =
      (degreeOneIso X).hom ≫
        map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1 := by
  apply (cancel_mono
    (homologyQuotientIso (TopRep.res H.subtype X)).hom).1
  rw [degreeOneIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [Category.assoc, homologyQuotientIso_restrict, ← Category.assoc,
    degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

omit [IsTopologicalGroup G] in
lemma transfer_restrict_term (H : OpenSubgroup G)
    (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom X) (t : ↥(T : Set G)) (g : G) :
    X.ρ ((t : G)⁻¹) (f.1 (factor T t g : G)) =
      f.1 g + X.ρ ((t : G)⁻¹) (f.1 (t : G)) -
        X.ρ g (X.ρ ((next T t g : G)⁻¹) (f.1 (next T t g : G))) := by
  have hfactor := f.2 (factor T t g : G) (next T t g : G)
  rw [factor_mul_next T t g, f.2 (t : G) g] at hfactor
  have h := congrArg (X.ρ ((t : G)⁻¹)) hfactor
  simp only [map_add] at h
  rw [rho_mul_apply] at h
  simp only [inv_mul_cancel, map_one] at h
  rw [rho_inv_factor] at h
  change f.1 g + X.ρ ((t : G)⁻¹) (f.1 (t : G)) =
    X.ρ g (X.ρ ((next T t g : G)⁻¹) (f.1 (next T t g : G))) +
      X.ρ ((t : G)⁻¹) (f.1 (factor T t g : G)) at h
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using h.symm

/-- The coefficient of the principal cocycle appearing when transfer is
applied to a restricted crossed homomorphism. -/
def restrictionTransferCoefficient (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom X) : X :=
  ∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (t : G))

lemma transferCrossed_restrict_apply (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    (f : continuousCrossedHom X) (g : G) :
    (transferCrossed X H T (crossedRestrict X H f)).1 g =
      H.toSubgroup.index • f.1 g + restrictionTransferCoefficient X H T f -
        X.ρ g (restrictionTransferCoefficient X H T f) := by
  classical
  rw [transferCrossed_apply]
  have hcard : Fintype.card ↥(T : Set G) = H.toSubgroup.index := by
    rw [← Nat.card_eq_fintype_card]
    exact T.2.card_right
  have hcard' : Finset.univ.card = H.toSubgroup.index := hcard
  have hlast :
      (∑ t : ↥(T : Set G),
        X.ρ g (X.ρ ((next T t g : G)⁻¹) (f.1 (next T t g : G)))) =
        X.ρ g (restrictionTransferCoefficient X H T f) := by
    calc
      _ = X.ρ g (∑ t : ↥(T : Set G),
          X.ρ ((next T t g : G)⁻¹) (f.1 (next T t g : G))) := by
            rw [map_sum]
      _ = X.ρ g (∑ t : ↥(T : Set G),
          X.ρ ((t : G)⁻¹) (f.1 (t : G))) := by
            apply congrArg (X.ρ g)
            simpa [nextEquiv] using
              (Equiv.sum_comp (nextEquiv T g)
                (fun t : ↥(T : Set G) => X.ρ ((t : G)⁻¹) (f.1 (t : G))))
      _ = _ := rfl
  calc
    (∑ t : ↥(T : Set G),
        X.ρ ((t : G)⁻¹) (f.1 (factor T t g : G))) =
      ∑ t : ↥(T : Set G),
        (f.1 g + X.ρ ((t : G)⁻¹) (f.1 (t : G)) -
          X.ρ g (X.ρ ((next T t g : G)⁻¹)
            (f.1 (next T t g : G)))) := by
              apply Finset.sum_congr rfl
              intro t _
              exact transfer_restrict_term X H T f t g
    _ = (∑ _t : ↥(T : Set G), f.1 g) +
          (∑ t : ↥(T : Set G), X.ρ ((t : G)⁻¹) (f.1 (t : G))) -
          (∑ t : ↥(T : Set G),
            X.ρ g (X.ρ ((next T t g : G)⁻¹)
              (f.1 (next T t g : G)))) := by
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_const, hcard', hlast]
      rfl

lemma transferCrossed_restrict (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] (f : continuousCrossedHom X) :
    transferCrossed X H T (crossedRestrict X H f) =
      H.toSubgroup.index • f -
        principalToCrossed X (restrictionTransferCoefficient X H T f) := by
  ext g
  rw [transferCrossed_restrict_apply]
  change
    H.toSubgroup.index • f.1 g + restrictionTransferCoefficient X H T f -
        X.ρ g (restrictionTransferCoefficient X H T f) =
      H.toSubgroup.index • f.1 g -
        (X.ρ g (restrictionTransferCoefficient X H T f) -
          restrictionTransferCoefficient X H T f)
  abel

lemma transferQuotient_comp_restrict (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    (transferQuotient X H T).comp (crossedQuotientRestrict X H) =
      H.toSubgroup.index • ContinuousLinearMap.id k
        (continuousCrossedHom X ⧸ principalCocycles X) := by
  apply ContinuousLinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  change
    (principalCocycles X).mkQ
        (transferCrossed X H T (crossedRestrict X H f)) =
      H.toSubgroup.index • (principalCocycles X).mkQ f
  rw [transferCrossed_restrict, map_sub, map_nsmul]
  have hp :
      (principalCocycles X).mkQ
          (principalToCrossed X (restrictionTransferCoefficient X H T f)) = 0 :=
    (Submodule.Quotient.mk_eq_zero (principalCocycles X)).2
      ⟨restrictionTransferCoefficient X H T f, rfl⟩
  rw [hp, sub_zero]

@[reassoc]
lemma transferQuotient_comp_restrict_hom (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (crossedQuotientRestrict X H) ≫
        TopModuleCat.ofHom (transferQuotient X H T) =
      H.toSubgroup.index • 𝟙 _ := by
  ext z
  exact DFunLike.congr_fun (transferQuotient_comp_restrict X H T) z

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction followed by degree-one corestriction is multiplication by the
subgroup index. -/
lemma restriction_corestrictionOne (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    [LocallyCompactSpace H] :
    map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1 ≫
        corestrictionOne X H =
      H.toSubgroup.index • 𝟙 (continuousCohomology 1 X) := by
  rw [corestrictionOne_eq_withTransversal X H T]
  simp only [corestrictionOneWithTransversal, degreeOneIso_inv]
  rw [homologyQuotientIso_restrict_assoc]
  rw [transferQuotient_comp_restrict_hom_assoc]
  rw [degreeOneIso, Iso.symm_hom, ← Category.assoc,
    Preadditive.comp_nsmul, Category.comp_id, Preadditive.nsmul_comp,
    Iso.hom_inv_id]

/-- The top open subgroup has finite index. -/
instance openSubgroupTopFiniteIndex :
    (⊤ : OpenSubgroup G).toSubgroup.FiniteIndex := by
  change (⊤ : Subgroup G).FiniteIndex
  infer_instance

/-- The top open subgroup of a locally compact group is locally compact. -/
instance openSubgroupTopLocallyCompact [LocallyCompactSpace G] :
    LocallyCompactSpace (⊤ : OpenSubgroup G) :=
  (⊤ : OpenSubgroup G).isOpen'.locallyCompactSpace

/-- Corestriction from the whole group is the identity after the canonical
restriction identification between `G` and its top open subgroup. -/
lemma corestrictionOne_top [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    map (openSubgroupInclusion (⊤ : OpenSubgroup G))
          (restrictionCoeffHom X (⊤ : OpenSubgroup G)) 1 ≫
        corestrictionOne X (⊤ : OpenSubgroup G) = 𝟙 _ := by
  rw [restriction_corestrictionOne X (⊤ : OpenSubgroup G) default]
  ext z
  simp

end CorestrictionTransversal

end

end ContinuousCohomology
