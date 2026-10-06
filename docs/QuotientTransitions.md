<!-- SPDX-License-Identifier: Apache-2.0 -->
# Native transitions between open-normal quotient stages

Import `ContinuousGroupCohomology.QuotientTransitions`.
For any topological group `G`, topological ring `k` (`[Ring k]`), native
`X : TopRep k G`, and `N ≤ M` open normal subgroups, the continuous
`quotientTransitionHom N M hNM` maps `G ⧸ N → G ⧸ M`, taking a representative
`g` to its class modulo `M`; it is surjective. The map
`quotientTransitionIncl X hNM` embeds `X^M` continuously and equivariantly
into `X^N` after restricting the `G ⧸ M`-action along this group map. The
invariants use their inherited submodule topologies; a merely continuous
representation needs no jointly continuous action.

The existing `ContinuousCohomology.cochainsMap` and `map` give **contravariant
refinement**: cochains and classes at the coarser `M` stage map to the finer
`N` stage. The `quotientTransition_cochainsMap_inflate` and
`quotientTransition_map_inflate` triangles identify inflation from `M` with
transition to `N` followed by inflation from `N`, including the equality of
the actual restricted coefficient inclusions. The corresponding `_id` and
`_comp` theorems prove identity and composition for cochains and for every
cohomology degree `n`; no class map is claimed injective. Independent universes
for the ring, group and representation are retained (`u`, `v`, `w`).

The ordinary-import generic client is
`examples.QuotientTransitionsNative`:
arbitrary nested `N ≤ M ≤ L`, degree, cochain and class exercise both triangles
and both composite transition laws. These private proofs elaborate in
`examples.FiniteStageResolutionNative`. The forwarding root retains its
original producer import but not its original isolated proof environment:
seven current client environments, comprising ten original ones, now elaborate
together in the host.

The original contributors and upstream results are credited in
[attribution](attribution.md).
