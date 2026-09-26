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

-- Compile all twelve native clients in both the named and default targets.
@[default_target]
lean_lib CGCExamples where
  roots := #[
    `examples.CompactFoundationNative,
    `examples.CompactNegativeBarNative,
    `examples.ContinuousTorsionNative,
    `examples.ExceptionalDeflationNative,
    `examples.FiniteCoinvariantsNative,
    `examples.FiniteDeflationTransitivityNative,
    `examples.FiniteNegativeNative,
    `examples.LevelCompactNative,
    `examples.LevelCompactNormNative,
    `examples.NestedInvariantsNative,
    `examples.NativeCore,
    `examples.RestrictedLevelNative,
  ]
