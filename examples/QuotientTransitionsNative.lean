/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientTransitions
import examples.FiniteStageResolutionNative

/-!
# Ordinary-import tests of native quotient-stage transitions

The stages, cochain, cohomology class and degree are arbitrary. No zero-class,
finite-coefficient, compactness or joint-continuity hypothesis is used.
The transition clients reside in `examples.FiniteStageResolutionNative`;
this entrypoint publicly imports `ContinuousGroupCohomology.QuotientTransitions`
and imports the client module. Import the production module for transition
maps and their composition and inflation laws. Refinement maps cochains and
classes contravariantly, from a coarser stage to a finer one.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
