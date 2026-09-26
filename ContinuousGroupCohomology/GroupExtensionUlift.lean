/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Extension

/-!
# Universe lifts of topological group extensions

This file raises the three groups in a `GroupExtension` through independently
chosen `ULift` universes. It also shows that a short exact sequence in the
topological sense remains short exact after this universe change.
-/

set_option warningAsError true

@[expose] public section

universe uN uE uG vN vE vG

namespace ContinuousMulEquiv

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The canonical continuous multiplicative equivalence from a universe lift
of a group to the original group. -/
def ulift : ULift.{vG} G ≃ₜ* G :=
  ContinuousMulEquiv.mk' Homeomorph.ulift fun _ _ => rfl

@[simp]
lemma ulift_apply (x : ULift.{vG} G) : ulift x = x.down := rfl

@[simp]
lemma ulift_symm_apply (x : G) : ulift.symm x = ULift.up x := rfl

end ContinuousMulEquiv

namespace GroupExtension

variable {N : Type uN} {E : Type uE} {G : Type uG}
  [Group N] [Group E] [Group G]

/-- Raise all three groups in a group extension through independently chosen
universes. -/
def ulift (S : GroupExtension N E G) :
    GroupExtension (ULift.{vN} N) (ULift.{vE} E) (ULift.{vG} G) where
  inl := MulEquiv.ulift.symm.toMonoidHom.comp (S.inl.comp MulEquiv.ulift.toMonoidHom)
  rightHom := MulEquiv.ulift.symm.toMonoidHom.comp
    (S.rightHom.comp MulEquiv.ulift.toMonoidHom)
  inl_injective := MulEquiv.ulift.symm.injective.comp
    (S.inl_injective.comp MulEquiv.ulift.injective)
  range_inl_eq_ker_rightHom := by
    ext e
    constructor
    · rintro ⟨n, rfl⟩
      simp [MonoidHom.mem_ker]
    · intro he
      rw [MonoidHom.mem_ker] at he
      have he' : S.rightHom e.down = 1 := by
        exact ULift.up_injective he
      rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom,
        MonoidHom.mem_range] at he'
      obtain ⟨n, hn⟩ := he'
      exact ⟨ULift.up n, ULift.down_injective hn⟩
  rightHom_surjective g := by
    obtain ⟨e, he⟩ := S.rightHom_surjective g.down
    exact ⟨ULift.up e, ULift.down_injective he⟩

@[simp]
lemma ulift_inl_apply (S : GroupExtension N E G) (n : ULift.{vN} N) :
    S.ulift.inl n = ULift.up (S.inl n.down) := rfl

@[simp]
lemma ulift_rightHom_apply (S : GroupExtension N E G) (e : ULift.{vE} E) :
    S.ulift.rightHom e = ULift.up (S.rightHom e.down) := rfl

variable [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace G]

/-- A topological short exact sequence remains short exact after independently
raising the universes of all three groups. -/
theorem isSES_ulift (S : GroupExtension N E G)
    (hS : TopologicalGroup.IsSES S.inl S.rightHom) :
    TopologicalGroup.IsSES
      (S.ulift.{uN, uE, uG, vN, vE, vG}).inl
      (S.ulift.{uN, uE, uG, vN, vE, vG}).rightHom where
  isClosedEmbedding := by
    change Topology.IsClosedEmbedding (ULift.map S.inl)
    exact hS.isClosedEmbedding.uliftMap
  isOpenQuotientMap := by
    change IsOpenQuotientMap (ULift.map S.rightHom)
    convert Homeomorph.ulift.symm.isOpenQuotientMap.comp
      (hS.isOpenQuotientMap.comp Homeomorph.ulift.isOpenQuotientMap) using 1
    funext e
    rfl
  mulExact := fun e => by
    rw [← MonoidHom.mem_ker,
      ← (S.ulift.{uN, uE, uG, vN, vE, vG}).range_inl_eq_ker_rightHom,
      MonoidHom.mem_range]
    change (∃ n, (S.ulift.{uN, uE, uG, vN, vE, vG}).inl n = e) ↔
      ∃ n, (S.ulift.{uN, uE, uG, vN, vE, vG}).inl n = e
    rfl

end GroupExtension
