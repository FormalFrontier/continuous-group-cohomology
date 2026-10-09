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
reside in `examples.FiniteStageResolutionNative`. This entrypoint publicly
imports `ContinuousGroupCohomology.ResolutionImage`, imports the Mathlib sign
modules and imports the client module. Import the production module for the
image criterion over an open normal quotient. Right constancy alone does not
guarantee a lift without invariant values at the bottom level.
-/

set_option warningAsError true

@[expose] public section
