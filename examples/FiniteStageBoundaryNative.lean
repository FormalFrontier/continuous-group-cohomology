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

This entrypoint retains its public producer import and forwards its proofs to
the finite-stage client host. Boundary, finite-stage boundary, colimit,
resolution/sign, quotient-invariants, resolution-image, cochain, seeded descent,
transition and diagram proofs elaborate together there: seven current
environments comprise ten originally isolated proof environments. Importing
this module does not repeat the former isolated boundary-proof elaboration.
-/

set_option autoImplicit false
set_option warningAsError true
