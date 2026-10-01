/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Foundation mathematics and APIs: Beacon (six existing mathematical leaves)
-/
module

import ContinuousGroupCohomology.LevelCompactFunctoriality

/-!
# Native levelwise-compact representation client

The only topology parameters below are on the acting group and on individual
invariant levels. No topology on the coefficient ring or ambient representation
module is assumed. These examples use transport with its source-to-target
subgroup orientation, inclusion continuity, and faithful functorial coefficient
maps between independently specified compact levels.
-/

set_option warningAsError true
set_option autoImplicit false

open CategoryTheory ContinuousGroupCohomology

noncomputable section

universe uR uG uA

namespace LevelCompactNative

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {A : Rep.{uA} R G}

example (U V : OpenSubgroup G) (σ : G)
    (h : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (x : openSubgroupInvariants A U) :
    (openSubgroupInvariantsTransport A U V σ h x : A) = A.ρ σ x := by
  simp

example (U V : OpenSubgroup G) (h : V ≤ U)
    (x : openSubgroupInvariants A U) :
    (LevelCompact.inclusion A U V h x : A) = x := by
  simpa only using LevelCompact.inclusion_coe A U V h x

example (L : LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) :
    @Topology.IsClosedEmbedding
      (openSubgroupInvariants A U) (openSubgroupInvariants A V)
      (L.topology U) (L.topology V) (LevelCompact.inclusion A U V h) :=
  LevelCompact.inclusion_isClosedEmbedding A L U V h

example (U V W : OpenSubgroup G) (σ τ : G)
    (hUV : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (hVW : W.toSubgroup ≤ V.toSubgroup.map (MulAut.conj τ)) :
    (openSubgroupInvariantsTransport A V W τ hVW).comp
        (openSubgroupInvariantsTransport A U V σ hUV) =
      openSubgroupInvariantsTransport A U W (τ * σ)
        (openSubgroupInvariantsTransport_comp_le U V W σ τ hUV hVW) :=
  openSubgroupInvariantsTransport_comp A U V W σ τ hUV hVW

example (U V W : OpenSubgroup G) (σ τ : G)
    (hUV : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (hVW : W.toSubgroup ≤ V.toSubgroup.map (MulAut.conj τ))
    (x : openSubgroupInvariants A U) :
    ((openSubgroupInvariantsTransport A V W τ hVW).comp
        (openSubgroupInvariantsTransport A U V σ hUV) x : A) =
      A.ρ (τ * σ) x := by
  rw [openSubgroupInvariantsTransport_comp A U V W σ τ hUV hVW]
  exact openSubgroupInvariantsTransport_coe A U W (τ * σ)
    (openSubgroupInvariantsTransport_comp_le U V W σ τ hUV hVW) x

variable {X Y : LevelCompactRep.{uR, uG, uA} R G}

example : (LevelCompactRep.forget (R := R) (G := G)).Faithful :=
  inferInstance

example (f : X ⟶ Y) (U : OpenSubgroup G)
    (x : openSubgroupInvariants X.rep U) :
    (LevelCompactRep.mapInvariants f U x : Y.rep) = f.hom x := by
  simp

example (f : X ⟶ Y) (U : OpenSubgroup G) :
    @Continuous (openSubgroupInvariants X.rep U)
      (openSubgroupInvariants Y.rep U)
      (X.levelCompact.topology U) (Y.levelCompact.topology U)
      (LevelCompactRep.mapInvariants f U) :=
  LevelCompactRep.continuous_mapInvariants f U

example (f : X ⟶ Y) :
    (LevelCompactRep.forget (R := R) (G := G)).map f = f.hom := by
  exact LevelCompactRep.forget_map f

end LevelCompactNative
