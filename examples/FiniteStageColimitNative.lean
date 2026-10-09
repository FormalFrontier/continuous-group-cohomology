/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageColimit
import examples.FiniteStageResolutionNative

/-!
# Colimit clients at arbitrary degree and target

The arbitrary-degree comparison and arbitrary-target cocone clients reside in
`examples.FiniteStageResolutionNative`. This entrypoint publicly imports
`ContinuousGroupCohomology.FiniteStageColimit` and imports that client module.
Import the production module for the finite-stage comparison and nonuniform
equality detection; the result does not choose one stage for every class.
-/

set_option autoImplicit false
set_option warningAsError true
