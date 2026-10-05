/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
import Lake

open Lake DSL

package "continuous-group-cohomology" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "e37d88a26f3791ed5a93daa1f949af1021b8d103"

require finiteGroupTateCohomology from git
  "https://github.com/FormalFrontier/finite-group-tate-cohomology.git" @
    "fda003db3d06774f28b47232e8248852ffdbfc0d"

@[default_target]
lean_lib ContinuousGroupCohomology

-- Compile all forty-one native clients in both the named and default targets.
@[default_target]
lean_lib CGCExamples where
  roots := #[
    `examples.CompactFoundationNative,
    `examples.CompactExceptionalTateCoefficientMapsNative,
    `examples.CompactExceptionalTateLimitFunctorialityNative,
    `examples.CompactNegativeBarNative,
    `examples.CompactExceptionalTateNative,
    `examples.CompactFiniteTateNormSequenceNative,
    `examples.CompactTateNormLimitSequenceNative,
    `examples.CompactTateNormNaturalityNative,
    `examples.CompactUniversalNormLimitsNative,
    `examples.ContinuousTorsionNative,
    `examples.ExceptionalDeflationNative,
    `examples.ExceptionalTateDeflationTopologyNative,
    `examples.FiniteCoinvariantDeflationNative,
    `examples.FiniteCoinvariantsNative,
    `examples.FiniteDeflationTransitivityNative,
    `examples.FiniteNegativeNative,
    `examples.FiniteTateTopologyNative,
    `examples.LevelCompactNative,
    `examples.LevelCompactNormNative,
    `examples.NestedInvariantsNative,
    `examples.NativeCore,
    `examples.NonpositiveTateDiagramsNative,
    `examples.RestrictedLevelNative,
    `examples.RestrictedLevelCompactFunctorialityNative,
    `examples.CompactDiscreteFactorNative,
    `examples.QuotientInvariantsNative,
    `examples.CochainInjectivityNative,
    `examples.ResolutionImageNative,
    `examples.FiniteStageResolutionNative,
    `examples.FiniteStageCochainsNative,
    `examples.FiniteAveragingNative,
    `examples.CompactDiscreteTorsionNative,
    `examples.HomologyBoundaryNative,
    `examples.SeededCochainsNative,
    `examples.QuotientTransitionsNative,
    `examples.FiniteStageBoundaryNative,
    `examples.DiscreteCohomologyNative,
    `examples.OpenNormalDiagramNative,
    `examples.FiniteStageColimitNative,
    `ContinuousGroupCohomologyExamples.DiscreteHom,
    `CGCExamples.TopRepDiscrete,
  ]
