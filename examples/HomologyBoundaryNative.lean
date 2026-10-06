/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ContinuousGroupCohomology.Algebra.Category.ModuleCat.Topology.HomologyBoundary
import examples.FiniteStageResolutionNative

set_option warningAsError true

/-!
# Boundary clients for topological-module homology

This entrypoint retains its ordinary producer import and forwards the
equal-class boundary check to the finite-stage client host. The boundary,
finite-stage boundary, colimit, resolution/sign, quotient-invariants,
resolution-image, cochain, seeded descent, transition and diagram proofs
elaborate together there: seven current environments comprise ten originally
isolated proof environments. Importing this module does not repeat the former
isolated boundary-proof elaboration.
-/
