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

The equal-class boundary client for arbitrary cycles of a topological-module
short complex resides in `examples.FiniteStageResolutionNative`. This
entrypoint imports that module and the topological-module homology boundary
production module. A zero class supplies an actual boundary witness in the
algebraic range of `toCycles`, not merely its closure.
-/
