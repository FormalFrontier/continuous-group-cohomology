/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageBoundary
import examples.FiniteStageResolutionNative

/-!
# Finite-stage boundary clients for eventual zero and equality

All representations and classes are arbitrary; in particular the degree-two
client does not assume that either cohomology group vanishes.

The eventual-zero and eventual-equality clients reside in
`examples.FiniteStageResolutionNative`. This entrypoint publicly imports
`ContinuousGroupCohomology.FiniteStageBoundary` and imports that client
module. The witnesses are found at a suitable open-normal refinement;
neither client assumes vanishing of a cohomology group.
-/

set_option autoImplicit false
set_option warningAsError true
