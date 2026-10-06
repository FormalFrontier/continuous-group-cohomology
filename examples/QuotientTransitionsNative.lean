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
The transition proofs elaborate in `examples.FiniteStageResolutionNative`;
this root retains its public producer import. Seven current client proof
environments, comprising ten original ones, elaborate together in that host.
Importing this forwarding root does not repeat the original isolated proof
elaboration. Import `ContinuousGroupCohomology.QuotientTransitions` for the
production API.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
