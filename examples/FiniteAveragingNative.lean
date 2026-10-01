/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteAveraging
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.Group.ContinuousInv

/-!
# Import-only clients for native finite-group averaging

These named clients use the public result on arbitrary representations, including
nontrivial actions, integral coefficients and an indiscrete finite group.
-/

set_option autoImplicit false

public section

universe u v w

namespace IncubatorTest.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]

private theorem genericPositiveDegree (X : TopRep.{max v w} k G) (n : ℕ)
    (a : continuousCohomology (n + 1) X) : Nat.card G • a = 0 :=
  ContinuousCohomology.finiteGroup_card_nsmul X n a

private theorem genericDegreeTwo (X : TopRep.{max v w} k G)
    (a : continuousCohomology 2 X) : Nat.card G • a = 0 := by
  simpa only [Nat.reduceAdd] using ContinuousCohomology.finiteGroup_card_nsmul X 1 a

private theorem integralArbitraryAction (X : TopRep.{max v w} ℤ G) (n : ℕ)
    (a : continuousCohomology (n + 1) X) : Nat.card G • a = 0 :=
  ContinuousCohomology.finiteGroup_card_nsmul X n a

private theorem trivialGroupSanity (X : TopRep.{w} ℤ PUnit.{1})
    (a : continuousCohomology 2 X) : Nat.card PUnit.{1} • a = 0 := by
  simpa only [Nat.reduceAdd] using ContinuousCohomology.finiteGroup_card_nsmul X 1 a

section Indiscrete

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊤

private theorem indiscreteTwoElementGroup (X : TopRep.{w} ℤ (Multiplicative (ZMod 2)))
    (a : continuousCohomology 2 X) : Nat.card (Multiplicative (ZMod 2)) • a = 0 := by
  simpa only [Nat.reduceAdd] using ContinuousCohomology.finiteGroup_card_nsmul X 1 a

end Indiscrete

end IncubatorTest.ContinuousCohomology
