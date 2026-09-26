# Continuous group cohomology: native core

A Lean library of low-degree continuous group cohomology, degree-one transfer,
topological quotients and actions, finite-group coinvariants and negative
deflation, and compact Hausdorff additive-group limit models. Import
`ContinuousGroupCohomology` for the complete public native core, or import a
`ContinuousGroupCohomology.*` leaf to limit dependencies. The checked
[`NativeCore` client](examples/NativeCore.lean) imports only the public root.

**Authors: Formal Frontier Agents.** Original project contributions are
offered under [Apache-2.0](LICENSE). Actual contributors, reused expression,
notices and outstanding rights checks are recorded in
[attribution](docs/attribution.md); a license label is not a whole-artifact
rights determination.

Browse the [native API reference](docs/API.md) for pinned displayed signatures,
Lean source anchors and clearly identified source docstrings or catalogue notes.
Its [reproduction guide](docs/README.md) and [machine-readable manifest](docs/api-manifest.json)
distinguish the frozen analyzed Lean inputs from this later documentation tree.

## What is available

| Area | Native modules | Mathematical boundary |
| --- | --- | --- |
| Continuous low-degree cohomology | `DegreeOne`, `LowDegreeExact`, `NormalizedCohomology`, `NestedInvariants` | Crossed cocycles modulo principal cocycles compute degree one with locally compact groups and jointly continuous actions; the degree-zero/one connecting sequence uses a continuous, not necessarily equivariant, splitting. |
| Transfer | `Corestriction`, `Composition`, `Mackey` | Open finite-index subgroup transfer and degree-one functoriality, composition and Mackey relations with the hypotheses in each declaration. |
| Finite constructions | `FiniteCoinvariants`, `FiniteNegativeDeflation` | Finite acting groups, orbit-difference relations, closed quotient under compact Hausdorff coefficients, and finite negative deflation via the pinned finite-group Tate library. This does not construct general nonpositive Tate cohomology for arbitrary topological groups. |
| Quotients and actions | `ClosedTopologicalCoinvariants`, `QuotientConjugationAction`, `TopologicalQuotientConjugationAction`, `TopologicalModN`, `ContinuousGroupExtension` | Closed versus algebraic coinvariants, quotient conjugation, continuous group extensions, and closed reduction modulo `n`; pointwise continuous actions do not imply jointly continuous actions. |
| Compact groups and limits | `CompactAddCommGroup`, `CompactAddCommGroupLimits`, `CompactFiniteHomology`, `CompactTopModuleLimits` | Compact Hausdorff additive groups, finite products, inverse limits and finite-stage homology constructions; cofiltered limit statements include empty indexing categories where stated. |
| Compact levels | `LevelCompact`, `LevelCompactFunctoriality`, `LevelCompactNorm`, `RestrictedLevelCompact` | Compact level systems, functoriality, relative norms and restricted systems with explicit finite-stage hypotheses. |
| Universe and representation interfaces | `TopModuleCatUlift`, `TopRepUlift`, `GroupExtensionUlift`, `HomogeneousCochainsUlift`, `ContinuousCohomologyUlift` | Universe transport and compatibility for the named continuous cohomology and extension constructions. |

The [`ContinuousGroupCohomology.lean`](ContinuousGroupCohomology.lean) root
publicly imports all 27 listed production leaves. All 27 and the eight clients
use Lean's native `module` system. A compact additive-group limit or finite-stage
homology *model* is not a construction of general completed continuous homology.
Finite quotients require their actual finite-index/finite-group hypotheses;
topological and compact results require the relevant continuity, compactness and
separation assumptions, not merely algebraic group structure. Consult theorem
statements and individual module documentation for precise universes and instances.

## Dependencies and builds

Use `elan` and Lake with `lean-toolchain`'s
`leanprover/lean4:v4.34.0-rc2`. `lakefile.lean` and `lake-manifest.json` fix
mathlib at `e37d88a26f3791ed5a93daa1f949af1021b8d103` and the **official
private** `finite-group-tate-cohomology` dependency at
`19c1d8ce0f11e9ce7af8ce5ae1e2479aa7cd0796` from
`https://github.com/FormalFrontier/finite-group-tate-cohomology.git`.
Authorized access to this private dependency and network access to the pinned
mathlib/transitive dependencies and their cache are required. No source-research
checkout is needed. Do not update the manifest when reproducing these pins.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build ContinuousGroupCohomology
lake --wfail build CGCExamples
lake --wfail build
```

Fetching the **matching mathlib cache must succeed before any build**; diagnose
a failed cache fetch rather than silently rebuilding mathlib from source.

### Build-time and memory baseline

In the 2026-09-26 native-core preparation with the pins above, after the matching
mathlib cache fetch and an initial single-leaf build, the root build took
**355.940 seconds** using Lake's normal scheduler. The subsequent eight-client
`CGCExamples` build took **7.794 seconds**, and the subsequent warm default build
took **2.499 seconds**. These are sequential workload observations, not three
independent clean builds. Toolchain installation, dependency checkout and cache
download time are excluded; any dependency compilation performed by a measured
build command is included. Later notice and documentation changes preserve the
measured Lean declarations, proofs, imports and build targets; these figures
reuse that preparation baseline rather than report a new benchmark.

The build environment had a shared **15 GiB** memory limit. Its lifetime cgroup
high-water reading was **14,701,797,376 bytes** after the root build and
**15,215,030,272 bytes** (about **14.2 GiB**) after the client build. These are
shared lifetime readings, **not per-command peak RSS** or a measured minimum
memory requirement. Plan additional headroom above that observed high-water
mark for other processes. CPU allocation and hardware were not recorded in this
baseline, so timings are indicative rather than portable guarantees; fresh setup
also depends on network access and available caches.

### Build targets and clients

`ContinuousGroupCohomology` compiles the public root and its 27 imports;
`CGCExamples` compiles precisely these eight native clients, also selected by
the default build:

- [`CompactFoundationNative`](examples/CompactFoundationNative.lean),
  [`FiniteCoinvariantsNative`](examples/FiniteCoinvariantsNative.lean),
  [`FiniteNegativeNative`](examples/FiniteNegativeNative.lean),
  [`LevelCompactNative`](examples/LevelCompactNative.lean);
- [`LevelCompactNormNative`](examples/LevelCompactNormNative.lean),
  [`NestedInvariantsNative`](examples/NestedInvariantsNative.lean),
  [`RestrictedLevelNative`](examples/RestrictedLevelNative.lean), and
  [`NativeCore`](examples/NativeCore.lean).

For an explicit fresh source elaboration of the aggregate-root client:

```sh
lake env lean examples/NativeCore.lean
```

The other seven client paths above can likewise be given to `lake env lean`.
Representative `#print axioms` commands in the client files report selected
proof dependencies. Release verification uses an applicable successful build and
a complete actual transitive-axiom audit of repository declarations, including
private declarations. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. The ordinary Lean build checks proofs; separate exhaustive stored-proof
rechecking is not a release prerequisite. Documentation, API claims, metadata,
rights and release history still need independent review. A successful build alone
is not a complete axiom or rights check.

## Scope and migration

This native core does **not** ship earlier scalar-extension experiments,
exceptional-degree deflation, finite Tate comparison diagrams, or the broader
nonpositive, compact/restricted Tate and topology layers. Earlier `design/`
notes and eight legacy clients are also excluded. Historical development is
retained in project history but not imported, installed or required by this
library. Migrate code importing an excluded module to the named retained API
where its mathematics matches; otherwise retain an earlier development
revision separately until the missing functionality is reviewed and added.
Removing a legacy import alone does not recreate a deferred theorem.

This is an explicitly scoped library, not an all-degree continuous cohomology
or general completed continuous homology formalization. No claim of source
coverage, first-release acceptance or publication follows from these files.
