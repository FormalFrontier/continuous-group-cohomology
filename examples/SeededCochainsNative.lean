/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.SeededCochains
import examples.FiniteStageResolutionNative

/-!
# Ordinary-import client for seeded cochain descent

The cochain, its degree and the prescribed open normal subgroup are all arbitrary.
The descent client resides in `examples.FiniteStageResolutionNative`. This
entrypoint publicly imports `ContinuousGroupCohomology.SeededCochains` and
imports that client module. For compact `G` and discrete, jointly continuous
coefficients, the production result finds a suitable refinement below any
prescribed open-normal subgroup for each native homogeneous cochain.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
