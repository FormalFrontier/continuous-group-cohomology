/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Topology.Algebra.CompactGroup.DiscreteFactor
public import Mathlib.Topology.Instances.ZMod

/-!
# Ordinary-import clients for compact/discrete factorization

The examples use only production imports and do not introduce a Hausdorff,
profinite or algebraic codomain hypothesis into the general statements.
-/

private theorem generic_compact_map_space_client
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [DiscreteTopology Y] : DiscreteTopology C(X, Y) :=
  ContinuousMap.discreteTopology_of_compactSpace

private theorem empty_domain_client {Y : Type v} [TopologicalSpace Y]
    [DiscreteTopology Y] : DiscreteTopology C(Empty, Y) :=
  ContinuousMap.discreteTopology_of_compactSpace

private theorem generic_compact_group_client
    {G : Type u} {Y : Type v} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace Y]
    [DiscreteTopology Y] (f : C(G, Y)) :
    ∃ (N : OpenNormalSubgroup G) (fbar : C(G ⧸ N.toSubgroup, Y)),
      ∀ g : G, fbar (QuotientGroup.mk g) = f g :=
  f.exists_openNormalSubgroup_factor

private theorem finite_constant_nonhomomorphic_client :
    ∃ (N : OpenNormalSubgroup (Multiplicative (ZMod 2)))
      (fbar : C((Multiplicative (ZMod 2)) ⧸ N.toSubgroup, Multiplicative (ZMod 2))),
      ∀ g, fbar (QuotientGroup.mk g) = Multiplicative.ofAdd (1 : ZMod 2) := by
  let f : C(Multiplicative (ZMod 2), Multiplicative (ZMod 2)) :=
    ⟨fun _ => Multiplicative.ofAdd (1 : ZMod 2), continuous_const⟩
  exact f.exists_openNormalSubgroup_factor

private theorem finite_constant_not_group_hom :
    (Multiplicative.ofAdd (1 : ZMod 2)) ≠ (1 : Multiplicative (ZMod 2)) := by
  decide
