/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Implementation: hive-request-a3c785c9e3c2568cbdb2e8592ff3c30ed2a0feee
  (8642a473-88cb-463a-beca-1c6e7fc1b695)
-/
module

public import ContinuousGroupCohomology.CompactTateNormLimitSequence

/-!
# Downstream full-system compact Tate norm sequence

These examples use only the public producer at arbitrary representations and
chosen level-compact topologies, including both exact middle terms, the
universal-norm kernel and the genuine topological quotient isomorphism.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace CGCExamples.CompactTateNormLimitSequenceNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)
variable (S : OpenNormalSubgroup G)

theorem exact_left_client : Function.Exact (LevelCompact.compactTateLimitInclusion A L)
    (LevelCompact.compactTateLimitNorm A L) :=
  LevelCompact.compactTateLimit_exact_left A L

theorem exact_right_client : Function.Exact (LevelCompact.compactTateLimitNorm A L)
    (LevelCompact.compactTateLimitProjection A L) :=
  LevelCompact.compactTateLimit_exact_right A L

theorem inclusion_injective_client :
    Function.Injective (LevelCompact.compactTateLimitInclusion A L) :=
  LevelCompact.compactTateLimitInclusion_injective A L

theorem projection_surjective_client :
    Function.Surjective (LevelCompact.compactTateLimitProjection A L) :=
  LevelCompact.compactTateLimitProjection_surjective A L

theorem norm_component_client : LevelCompact.compactTateLimitNorm A L =
    limit.π (LevelCompact.compactFiniteCoinvariantsDiagram A L) S ≫
      LevelCompact.normFromFiniteCoinvariants A L S :=
  LevelCompact.compactTateLimitNorm_π A L S

theorem projection_component_client : LevelCompact.compactTateLimitProjection A L ≫
      limit.π (LevelCompact.compactFiniteZeroDeflationDiagram A L) S =
    LevelCompact.finiteTateZeroπ A L S :=
  LevelCompact.compactTateLimitProjection_π A L S

theorem inclusion_component_client : LevelCompact.compactTateLimitInclusion A L ≫
      limit.π (LevelCompact.compactFiniteCoinvariantsDiagram A L) S =
    limit.π (LevelCompact.compactFiniteNegativeOneDeflationDiagram A L) S ≫
      LevelCompact.finiteTateNegOneι A L S :=
  LevelCompact.compactTateLimitInclusion_π A L S

theorem kernel_range_client (x : LevelCompact.group A L (⊤ : OpenSubgroup G)) :
    LevelCompact.compactTateLimitProjection A L x = 0 ↔
      x ∈ LevelCompact.compactUniversalNormSet A L :=
  LevelCompact.compactTateLimitProjection_eq_zero_iff A L x

theorem kernel_universal_norm_client
    (x : LevelCompact.group A L (⊤ : OpenSubgroup G)) :
    LevelCompact.compactTateLimitProjection A L x = 0 ↔
      x ∈ LevelCompact.universalNormSubmodule A
        (LevelCompact.fullOpenNormalSubgroup G) :=
  LevelCompact.compactTateLimitProjection_eq_zero_iff_universalNorm A L x

theorem range_universal_norm_client :
    Set.range (LevelCompact.compactTateLimitNorm A L) =
    {x : LevelCompact.group A L (⊤ : OpenSubgroup G) |
      x ∈ LevelCompact.universalNormSubmodule A
        (LevelCompact.fullOpenNormalSubgroup G)} :=
  LevelCompact.compactTateLimitNorm_range_eq_universalNormSubmodule A L

noncomputable def quotient_iso_client :
    CompHausAddCommGrp.quotient (LevelCompact.group A L (⊤ : OpenSubgroup G))
      (LevelCompact.compactUniversalNormClosedSubgroup A L) ≅
        LevelCompact.compactZeroTateLimit A L :=
  LevelCompact.compactTateUniversalNormQuotientIso A L

theorem quotient_compatibility_client
    (x : LevelCompact.group A L (⊤ : OpenSubgroup G)) :
    (LevelCompact.compactTateUniversalNormQuotientIso A L).hom
      (QuotientAddGroup.mk x) = LevelCompact.compactTateLimitProjection A L x :=
  LevelCompact.compactTateUniversalNormQuotientIso_mk A L x

theorem degree_zero_projection_surjective_client : Function.Surjective
    (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram A L) S) :=
  LevelCompact.compactZeroTateLimitπ_surjective A L S

end CGCExamples.CompactTateNormLimitSequenceNative
