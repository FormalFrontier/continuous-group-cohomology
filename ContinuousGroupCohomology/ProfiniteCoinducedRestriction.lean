/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CoinducedRestriction
public import ContinuousGroupCohomology.Corestriction
public import ProfiniteGroups.ContinuousCosetRepresentative

/-!
# Twisted coinduction restricted to every closed subgroup

The chosen continuous coset representative from `ProfiniteGroups` supplies
the section required by `TopRep.coind₁RestrictionIso` for **any closed**
subgroup of a compact Hausdorff totally disconnected group. No normality,
openness, or countability of the subgroup is assumed. The coefficient on
`C(G ⧸ H, B)` has the pointwise restricted `H`-action; the entire continuous
function space is used, not a fixed-point or trivial-action space.

For discrete jointly continuous `B`, the resulting coinduced representation
is also discrete and jointly continuous. A chosen section is not a canonical
group splitting.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §3,
  Proposition 1.3.6(ii).
- `ProfiniteGroups.ContinuousCosetRepresentative` and Mathlib's twisted
  coinduction and compact-open topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public section

universe u v w

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (H : Subgroup G) [IsClosed (H : Set G)]

/-- The all-closed-subgroup specialization uses the continuous
representatives supplied by the profinite-group library. It realizes the
closed-subgroup restriction clause of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, Chapter I, §3,
Proposition 1.3.6(ii), for every closed subgroup of a compact Hausdorff
totally disconnected group, without a canonical choice of section. Discreteness
and joint continuity require separate coefficient hypotheses. -/
noncomputable def profiniteCoind₁RestrictionIso (B : TopRep.{w} k G) :
    res H.subtype (coind₁ B) ≅
      coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) := by
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact coind₁RestrictionIso H B H.continuousCosetRepresentative
    H.continuousCosetRepresentative_rightInverse

@[simp] theorem profiniteCoind₁RestrictionIso_hom_apply
    (B : TopRep.{w} k G) (f : C(G, B)) (h : H) (c : G ⧸ H) :
    ((profiniteCoind₁RestrictionIso H B).hom).hom f h c =
      f (h.val * (H.continuousCosetRepresentative c)⁻¹) := by
  have : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact coind₁RestrictionIso_hom_apply H B _ _ f h c

/-- The entire function-space coefficient is discrete for compact cosets and
discrete original coefficients. -/
instance profinitePointwiseContinuousMap_discrete
    (B : TopRep.{w} k G) [DiscreteTopology B] :
    DiscreteTopology (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) :=
  pointwiseContinuousMap_discrete (B := res H.subtype B)

omit [T2Space G] [TotallyDisconnectedSpace G] [IsClosed (H : Set G)] in
/-- Source-strength continuity of the pointwise restricted coefficient action. -/
theorem profinitePointwiseContinuousMap_jointlyContinuous
    (B : TopRep.{w} k G) [JointlyContinuous B] :
    JointlyContinuous (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) := by
  have : JointlyContinuous (res H.subtype B) := jointlyContinuous_res H B
  exact jointlyContinuous_pointwiseContinuousMap
    (Q := G ⧸ H) (H := H) (res H.subtype B)

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- Source-strength continuity of the twisted coinduction on the discrete
pointwise coefficients. -/
theorem profiniteCoind₁Restriction_jointlyContinuous
    (B : TopRep.{w} k G) [JointlyContinuous B] :
    JointlyContinuous
      (coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B))) := by
  have : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  have : JointlyContinuous (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) :=
    profinitePointwiseContinuousMap_jointlyContinuous H B
  exact jointlyContinuous_coind₁ _

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- The outer compact-open space is discrete as well. -/
theorem profiniteCoind₁Restriction_discrete
    (B : TopRep.{w} k G) [DiscreteTopology B] :
    DiscreteTopology
      (coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B))) := by
  have : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact (inferInstance : IsClosed (H : Set G)))
  exact ContinuousMap.discreteTopology_of_compactSpace

end TopRep
