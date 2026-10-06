# Attribution and mathematical sources

**Authors: Formal Frontier Agents.** Beacon developed the original low-degree,
transfer, compact additive-group and level-system mathematics. Formal Frontier
Agents contributed the other original proofs, native examples, documentation
and adaptations. The seven native finite-stage families (algebraic boundaries,
seeded cochains, quotient transitions, eventual boundary equality, cohomology
discreteness, open-normal diagrams and the colimit) have distinct original
contributors; adapting their imports, clients and documentation did not transfer
authorship of the proofs. The same distinction applies to the compact exceptional
Tate, norm and universal-norm modules. Original contributor, adaptation and
review roles are preserved in this repository's immutable Git history. This
summary distinguishes original proofs from later adaptations and editorial
changes.

Original Formal Frontier contributions are offered under the root
[Apache-2.0 license](../LICENSE). The collective author credit does not assert
copyright ownership. Retained or adapted third-party expression preserves its
own authentic notices and attribution. In particular,
[`TopModuleCatUlift.lean`](../ContinuousGroupCohomology/TopModuleCatUlift.lean)
retains **Nailin Guan's 2025 copyright and Apache-2.0 notice** for the
universe-lift construction adapted from
[mathlib's `ModuleCat/Ulift.lean`](https://github.com/leanprover-community/mathlib4/blob/e37d88a26f3791ed5a93daa1f949af1021b8d103/Mathlib/Algebra/Category/ModuleCat/Ulift.lean),
alongside the Formal Frontier/Beacon topological development credit. Other
original project files use `Authors: Formal Frontier Agents` with no invented
copyright holder. The [cochain-injectivity guide](CochainInjectivity.md)
identifies the mathlib continuous-cohomology functoriality source and its
contributors Edison Xie and Richard Hill.

## Formal foundations and related libraries

- [Lean 4](https://github.com/leanprover/lean4) and
  [mathlib at the pinned revision](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5)
  provide the categorical, group-cohomological and topological foundations,
  including [native continuous cohomology](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RepresentationTheory/Homological/ContCohomology/Basic.lean).
  Using these APIs does not make their upstream proof expression a project
  contribution.
- The [finite-group Tate dependency at its official pinned commit](https://github.com/FormalFrontier/finite-group-tate-cohomology/commit/d17f93bbc5b934f8b9f3cf077769a706a901608d)
  supplies finite Tate definitions and norm maps used here. Authorized access
  to this private dependency is required for building from the current pins.
- [`scripts/generate_api.py`](../scripts/generate_api.py) and
  [`scripts/test_generate_api.py`](../scripts/test_generate_api.py) adapt
  Apache-2.0 documentation-generator designs from Formal Frontier's
  profinite-groups and finite-group Tate libraries. The checked-in
   [API index](API.md) and [manifest](api-manifest.json) describe a historical
   graph, not all current modules. Their public display links use an exact
   [published source snapshot](https://github.com/FormalFrontier/continuous-group-cohomology/tree/be74358d7b1140e76ab6b2ad72f6aa068138e687);
   [reproduction notes](README.md) distinguish it from the original private
   extraction and state the raw-data/access limitations.

This library is original formalization drawing on the cited formal libraries;
no separate paper has been identified as the source of all its theorems. Its
mathematical statements, precise hypotheses, proof outlines and usage are
available through the [module guides](../README.md#what-is-available) and
linked Lean declarations rather than private catalog codes. Source-specific
correspondence and coverage decisions are separate from this library.

Authentic third-party notices remain in their files, and their licenses apply
to the respective retained or adapted expression. This attribution records
provenance without asserting copyright ownership or source formalization.
