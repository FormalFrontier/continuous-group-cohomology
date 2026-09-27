/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Implementation: hive-request-1d0844eac48c5857a2e1cc8b56121d7b8571e14b
  (a02c5d55-67a0-4421-a798-eebf69e9182a)
Destination transfer: hive-request-89268f99753a32543c537bc946e6f0fdc94c084c
  (6fb5a0a9-b048-4a08-ab62-90614094ecd7)
-/
module

public import ContinuousGroupCohomology.CompactTateNormNaturality

/-!
# Arbitrary-coefficient clients for compact Tate norm-row naturality

Every example has arbitrary level-compact coefficients and their existing
continuous coefficient maps. No property of a specially selected representation
or coefficient ring is used.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

namespace CGCExamples.CompactTateNormNaturalityNative

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable {A B C : LevelCompactRep.{u, u, u} R G}
variable (f : A ⟶ B) (g : B ⟶ C) (S : OpenNormalSubgroup G)

theorem coinvariant_stage :
    LevelCompactRep.compactFiniteCoinvariantsLimitFunctor.map f ≫
        limit.π (LevelCompact.compactFiniteCoinvariantsDiagram B.rep B.levelCompact) S =
      limit.π (LevelCompact.compactFiniteCoinvariantsDiagram A.rep A.levelCompact) S ≫
        LevelCompactRep.finiteCoinvariantsMap f S :=
  LevelCompactRep.compactFiniteCoinvariantsLimitFunctor_map_π f S

theorem inclusion_square :
    LevelCompactRep.compactNegativeOneTateLimitFunctor.map f ≫
        LevelCompact.compactTateLimitInclusion B.rep B.levelCompact =
      LevelCompact.compactTateLimitInclusion A.rep A.levelCompact ≫
        LevelCompactRep.compactFiniteCoinvariantsLimitFunctor.map f :=
  LevelCompactRep.compactTateLimitInclusion_naturality f

theorem norm_square :
    LevelCompactRep.compactFiniteCoinvariantsLimitFunctor.map f ≫
        LevelCompact.compactTateLimitNorm B.rep B.levelCompact =
      LevelCompact.compactTateLimitNorm A.rep A.levelCompact ≫
        LevelCompactRep.groupMap f (⊤ : OpenSubgroup G) :=
  LevelCompactRep.compactTateLimitNorm_naturality f

theorem projection_square :
    LevelCompactRep.groupMap f (⊤ : OpenSubgroup G) ≫
        LevelCompact.compactTateLimitProjection B.rep B.levelCompact =
      LevelCompact.compactTateLimitProjection A.rep A.levelCompact ≫
        LevelCompactRep.compactZeroTateLimitFunctor.map f :=
  LevelCompactRep.compactTateLimitProjection_naturality f

theorem quotient_representative
    (x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)) :
    LevelCompactRep.compactUniversalNormQuotientMap f (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (LevelCompactRep.groupMap f (⊤ : OpenSubgroup G) x) :=
  LevelCompactRep.compactUniversalNormQuotientMap_mk f x

theorem quotient_composition :
    LevelCompactRep.compactUniversalNormQuotientMap (f ≫ g) =
      LevelCompactRep.compactUniversalNormQuotientMap f ≫
        LevelCompactRep.compactUniversalNormQuotientMap g :=
  LevelCompactRep.compactUniversalNormQuotientMap_comp f g

theorem quotient_iso_component :
    (LevelCompactRep.compactTateUniversalNormQuotientNatIso.hom.app A) =
      (LevelCompact.compactTateUniversalNormQuotientIso A.rep A.levelCompact).hom :=
  LevelCompactRep.compactTateUniversalNormQuotientNatIso_hom_app A

theorem quotient_iso_representative
    (x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)) :
    (LevelCompactRep.compactTateUniversalNormQuotientNatIso.hom.app A)
        (QuotientAddGroup.mk x) =
      LevelCompact.compactTateLimitProjection A.rep A.levelCompact x :=
  LevelCompactRep.compactTateUniversalNormQuotientNatIso_hom_app_mk A x

end CGCExamples.CompactTateNormNaturalityNative
