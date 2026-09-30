# Compact/discrete continuous maps and finite quotient factorization

Import `ContinuousGroupCohomology.Topology.ContinuousMap.CompactDiscrete` for
`ContinuousMap.discreteTopology_of_compactSpace`: if `X` is compact and `Y` is
discrete, the **existing compact-open topology** on `C(X, Y)` is discrete. No
Hausdorff, zero-dimensional, finiteness, nonemptiness, or algebraic hypothesis
on either space is needed. The theorem is deliberately not a global instance.
It uses the finite range of a continuous map on a compact domain and the
compact clopen fibres as compact-open subbasic constraints, including when
`X` or `Y` is empty.

Import `ContinuousGroupCohomology.Topology.Algebra.CompactGroup.DiscreteFactor` for
`ContinuousMap.exists_openNormalSubgroup_factor`. For any group `G` with a
compatible group topology and compact underlying space, discrete space `Y`,
and `f : C(G, Y)`, the theorem gives `N : OpenNormalSubgroup G` and
`fbar : C(G ⧸ N.toSubgroup, Y)` with
`∀ g, fbar (QuotientGroup.mk g) = f g`. Universes of `G` and `Y` are
independent. In particular, `G` need not be Hausdorff, profinite, or totally
disconnected, while `Y` and `f` need not be groups or homomorphisms. The
quotient is finite by `Subgroup.quotient_finite_of_isOpen` and discrete by
`QuotientGroup.discreteTopology`, both applicable to the returned `N`.

The second proof curries right translation into `C(G, Y)`; the preimage of
`{f}` is a clopen neighbourhood of the identity. Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` gives
an open normal subgroup inside it, so quotient-related group elements have
equal images. Continuous quotient elimination supplies `fbar`. This concerns
one ordinary map, not cochains, coefficients with actions, common quotients of
families, a colimit, or cohomology descent. Ordinary-import clients in
`examples/CompactDiscreteFactorNative.lean` cover both
generic results, the empty domain, and a finite constant map with nonidentity
value (hence not a group homomorphism).

See [attribution](attribution.md) for contributor lineage and rights scope.
