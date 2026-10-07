# Algebraic connecting homomorphisms

For a locally compact topological group `G`, a topologized ring `k`, and
`A ⟶ B ⟶ C` in `TopRep k G`, assume that the first arrow is injective, the
sequence is exact on underlying functions, and the second arrow is surjective.
Assume also that `B` and `C` are discrete and the action on `B` is jointly
continuous. No compactness, separation, continuous splitting, or vanishing of
cohomology is required.

The homogeneous cochain complex uses continuous maps and its homology is the
existing `continuousCohomology n` in topological modules. Forgetting topology
from the complex preserves homology because the forgetful functor from
topological modules to modules has both adjoints. In the abelian category
`ModuleCat k`, the degreewise short exact cochain sequence gives the canonical
connecting homomorphism of `HomologicalComplex.HomologySequence`.
`ContinuousCohomology.connecting` transports this homomorphism back across the
canonical homology comparison; its source and target are **underlying modules**
of the existing continuous cohomology objects. This does **not** assert that
the new connecting map is continuous for their quotient topologies.

For any `n : ℕ`, the following three successive terms are exact, by
Mathlib's short-exact-complex homology sequence and the homology comparison:

1. `Hⁿ(G,A) ⟶ Hⁿ(G,B) ⟶ Hⁿ(G,C)` (`exact_map_map`);
2. `Hⁿ(G,B) ⟶ Hⁿ(G,C) ⟶ Hⁿ⁺¹(G,A)` (`exact_map_connecting`);
3. `Hⁿ(G,C) ⟶ Hⁿ⁺¹(G,A) ⟶ Hⁿ⁺¹(G,B)` (`exact_connecting_map`).

`connecting_apply` computes the sign convention: if `z` is a cocycle
and `b` is any lift of `z` to the middle cochains, choose `a` in the left
cochains such that `i(a) = d(b)`; then `δ[z] = [a]`, without an added negative
sign. For a topologically split short exact sequence with jointly continuous
action on `A`, `connecting_zero_eq_split` identifies this algebraic degree-zero
connector with the existing continuous map
`TopologicallySplitShortExact.connectingMap` after the invariant-coefficient
comparison. This special comparison does not make the general connector
continuous.

The sign-action client uses `ℤˣ`, whose element `-1` changes the sign of both
integer terms in `ℤ --×2→ ℤ → ZMod 2`. Reduction modulo two has trivial
action. The integer invariants vanish but the quotient invariant `1` is
nonzero and has no invariant integer lift. These facts are independent of the
long exact sequence. Exactness at the quotient term implies that the
degree-zero connector sends the quotient invariant `1` to a nonzero
cohomology class. An independently proved parity obstruction also excludes
the expected boundary from the principal integer cocycles.

## References

- Neukirch, Schmidt, Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §3 and Exercise 1.
- Mathlib, `RepresentationTheory.Homological.ContCohomology`,
  `Algebra.Homology.HomologySequence`, and
  `Algebra.Category.ModuleCat.Topology.Homology`.
