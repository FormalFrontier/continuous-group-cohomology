/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ResolutionImage
public import Mathlib.Data.Int.Order.Units
import examples.FiniteStageResolutionNative

/-!
# Resolution-image client entrypoint

The level-zero, level-one, level-three, refinement and non-liftability proofs
elaborate in `examples.FiniteStageResolutionNative`. This module retains its
public producer and Mathlib imports; import `ContinuousGroupCohomology.ResolutionImage`
for the production API. Seven current client proof environments, comprising
ten original environments, now elaborate together in the host. Importing this
forwarding root does not repeat the original isolated proof elaboration.
-/

set_option warningAsError true

@[expose] public section
