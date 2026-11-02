# Article-step validation — 2026-11-02

**Main-theorem status: not yet verified.** Actual KdV/KdV2 spectral frequencies
and the physical Birkhoff flow identification remain open. The checked step
includes the article modules, the shared sequence divergence argument,
its existing Hilbert specialization and a transitive audit.

## Results

| Source | Checked content |
| --- | --- |
| `NLS/SequenceSpaces/NonnegativeEnergyDivergence.lean` and `NLS/SequenceSpaces/HilbertEnergyDivergence.lean` | General finite-energy divergence under coordinatewise approximation, reused by the prior Hilbert theorem with its statement preserved. |
| `NLS/Dynamics/ActionDependentWeightedPhaseFlow.lean` | Weighted coordinatewise-frequency continuity, action conservation, nonlinear group law, norm preservation, compact-time dependence and homeomorphic time slices. |
| `NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow.lean` | Source signed real sequence locus, zero-mode/reality preservation, actual coordinate-product actions, Hamiltonian phase signs, group and continuity results for a supplied action-frequency function. |
| `NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction.lean` | Exact `20(2nπ)` mass coefficient and the resulting compact-time phase obstruction, conditional on mass divergence, correction convergence and a nonzero limiting amplitude. |
| `NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities.lean` | Euler-Lagrange polynomials of the source doubled Hamiltonian densities; their gradients produce the literal PDE vector fields. Genuine smooth evaluation derivatives, exact constant-mean reductions, and period-one spatial balances of mean and quadratic mass. |
| `NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence.lean` | Exact endpoint/mass equivalence; divergence for every endpoint-regular approximation; signed finite truncations converging in norm; compact-time coordinate nonextension once the actual correction and phase identity are supplied. |
| `NLS/Dynamics/FixedTimePhaseObstruction.lean` | A relative phase tending to pi rules out a common fixed-time output limit, independently of convergence of the individual frequencies. |
| `NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion.lean` | Finite signed perturbations with an exact prescribed mass increment; endpoint regularity; norm convergence for every sigma<1/2. |
| `NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension.lean` | Fixed-time coordinate nonextension via two constructed approximating families, given the actual correction and endpoint phase identity. |
| The five imported classical Hill modules from `ConstantUpperSpectralBridge.lean` through `ClassicalBranchPrimitive.lean` | Actual IVP-to-Hill trace bridge, energy symmetry, entire joint discriminant and constructed local primitive/squared-primitive charts on continuous potentials. |
| `NLS/KdV/ClassicalFreePrimitive.lean` and `NLS/KdV/FreeFrequencyPsi.lean` | Actual free scalar trace/root/primitive, entire normalized numerator basis, omitted-mode and critical-point formulas, constructed isolating circles, exact periods and every positive free moment. |
| `NLS/KdV/FrequencyPrimitiveContinuation.lean` | Constructed analytic unit factorization at branch points, exact primitive/root endpoint limit, locally uniform quotient and positive-moment bounds, and local odd-moment cancellation. |
| `NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood.lean` | New common-neighborhood distant critical analyticity and simplicity at arbitrary complex sources, without a real-type assumption. |
| `NLS/KdV/ClassicalHighCriticalPoints.lean`, `ClassicalUniformCriticalBasis.lean`, `ClassicalCriticalTailAnalytic.lean` | Actual uniform high energy critical points, infinite entire numerator basis on one neighborhood, and Banach analytic/small ℓ² displacement tails. |
| `NLS/KdV/ClassicalSpectralEmbedding.lean`, `ClassicalContourCoverage.lean`, `NLS/ZakharovShabat/ContinuousPotentialL2Bound.lean` | Imported actual scalar trace/coefficient embedding and uniform continued-root contour coverage. |
| `NLS/ComplexAnalysis/JointSpectralDerivative.lean`, `ParametricDividedDifference.lean`, `AnalyticFinitePeriodNormalization.lean` | Full joint spectral-derivative analyticity; filled moving divided differences; constructed analytic finite period inversion. |
| `NLS/KdV/ClassicalCriticalPointBranch.lean`, `ClassicalCriticalNumerator.lean`, `ClassicalCriticalPeriods.lean`, `ClassicalFiniteNormalizedDifferentials.lean` | Actual analytic critical branches and entire numerator bases near zero; actual analytic period entries; exact finite normalization on one selected-mode neighborhood. |
| `NLS/KdV/ClassicalHillFlow.lean`, `ClassicalHillSpectrum.lean`, `ClassicalSourcePrimitive.lean` | Previously imported actual scalar IVP, Floquet characterization, free-normalized root and primitive continuation; now compiled directly by the frequency checker. |
| `NLS/SequenceSpaces/LocallyBoundedAnalyticSummation.lean` | Analytic ℓ¹ realization from local norm bounds, absolute summability and locally uniform convergence. |
| `NLS/KdV/FrequencySeriesBounds.lean` and `NLS/KdV/FrequencySeries.lean` | Exact quadratic-denominator kernel bounds; Hölder and bounded-kernel row estimates; analytic positive-index sums with locally uniform positive partial sums, given local spectral remainder bounds. |
| `NLS/KdV/FrequencyMoments.lean` | Literal weighted moments, Banach analyticity, odd and analytic-removal cancellations, norm estimate and binomial period expansions. |
| `NLS/KdV/FrequencyContourDecomposition.lean` | Exact cubic/fifth-power coefficients and finite-gap normalized exterior-period decompositions, using the proved finite-hole Cauchy theorem. |

All forty selected modules compile with pinned **Lean 4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using canonical **mathlib
v4.33.1** compiled imports at source base
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Options:
`-DautoImplicit=false -DwarningAsError=true`. The default heartbeat budget is retained.
No linters are disabled; no `sorry`, `admit` or new axioms are introduced.

Final output of `bash scripts/check-kdv-kdv2-frequencies.sh`:

```text
PASS NLS/ComplexAnalysis/JointSpectralDerivative
PASS NLS/ComplexAnalysis/ParametricDividedDifference
PASS NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
PASS NLS/ZakharovShabat/ContinuousPotentialL2Bound
PASS NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood
PASS NLS/KdV/ConstantUpperSpectralBridge
PASS NLS/KdV/ClassicalSpectralSymmetry
PASS NLS/KdV/ClassicalDiscriminant
PASS NLS/KdV/ClassicalLocalPrimitive
PASS NLS/KdV/ClassicalFreePrimitive
PASS NLS/KdV/ClassicalHillFlow
PASS NLS/KdV/ClassicalHillSpectrum
PASS NLS/KdV/ClassicalSourcePrimitive
PASS NLS/KdV/ClassicalSpectralEmbedding
PASS NLS/KdV/ClassicalContourCoverage
PASS NLS/KdV/ClassicalBranchPrimitive
PASS NLS/SequenceSpaces/LocallyBoundedAnalyticSummation
PASS NLS/KdV/FrequencySeriesBounds
PASS NLS/KdV/FrequencySeries
PASS NLS/SequenceSpaces/NonnegativeEnergyDivergence
PASS NLS/SequenceSpaces/HilbertEnergyDivergence
PASS NLS/Dynamics/ActionDependentWeightedPhaseFlow
PASS NLS/Dynamics/FixedTimePhaseObstruction
PASS NLS/KdV/FrequencyMoments
PASS NLS/KdV/FreeFrequencyPsi
PASS NLS/KdV/ClassicalCriticalPointBranch
PASS NLS/KdV/ClassicalHighCriticalPoints
PASS NLS/KdV/ClassicalUniformCriticalBasis
PASS NLS/KdV/ClassicalCriticalTailAnalytic
PASS NLS/KdV/ClassicalCriticalNumerator
PASS NLS/KdV/ClassicalCriticalPeriods
PASS NLS/KdV/ClassicalFiniteNormalizedDifferentials
PASS NLS/KdV/FrequencyPrimitiveContinuation
PASS NLS/KdV/FrequencyContourDecomposition
PASS NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow
PASS NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction
PASS NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion
PASS NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension
Axiom audit passed: 570 candidate declarations; 12091 declarations total.
```

`scripts/CheckKdVKdV2FrequencyCandidates.lean` checks every declaration from
the forty selected modules (including generated and private declarations)
and all imported `NLS` declarations. Their axioms are collected transitively.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The audit
rejects `sorryAx` and any other axiom. Its count does not replace the
dissertation's separate full-library validation record.

The original private three-module step also passed a transitive audit of
54 candidate declarations and 201 declarations total; it was rechecked in
this worktree before the smooth PDE module was added.

## Build isolation and reproduction

The actual branch and worktree are recorded in `PROGRESS.md`. Run:

```bash
bash scripts/check-kdv-kdv2-frequencies.sh
```

The checker explicitly selects the pinned executable, reads canonical
compiled imports, and writes these ordinary output files solely under this
worktree's `.lake/build/lib/lean/`:

```text
NLS/ComplexAnalysis/JointSpectralDerivative.olean
NLS/ComplexAnalysis/ParametricDividedDifference.olean
NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization.olean
NLS/ZakharovShabat/ContinuousPotentialL2Bound.olean
NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood.olean
NLS/KdV/ConstantUpperSpectralBridge.olean
NLS/KdV/ClassicalSpectralSymmetry.olean
NLS/KdV/ClassicalDiscriminant.olean
NLS/KdV/ClassicalLocalPrimitive.olean
NLS/KdV/ClassicalFreePrimitive.olean
NLS/KdV/ClassicalHillFlow.olean
NLS/KdV/ClassicalHillSpectrum.olean
NLS/KdV/ClassicalSourcePrimitive.olean
NLS/KdV/ClassicalSpectralEmbedding.olean
NLS/KdV/ClassicalContourCoverage.olean
NLS/KdV/ClassicalBranchPrimitive.olean
NLS/SequenceSpaces/LocallyBoundedAnalyticSummation.olean
NLS/KdV/FrequencySeriesBounds.olean
NLS/KdV/FrequencySeries.olean
NLS/SequenceSpaces/NonnegativeEnergyDivergence.olean
NLS/SequenceSpaces/HilbertEnergyDivergence.olean
NLS/Dynamics/ActionDependentWeightedPhaseFlow.olean
NLS/Dynamics/FixedTimePhaseObstruction.olean
NLS/KdV/FrequencyMoments.olean
NLS/KdV/FreeFrequencyPsi.olean
NLS/KdV/ClassicalCriticalPointBranch.olean
NLS/KdV/ClassicalHighCriticalPoints.olean
NLS/KdV/ClassicalUniformCriticalBasis.olean
NLS/KdV/ClassicalCriticalTailAnalytic.olean
NLS/KdV/ClassicalCriticalNumerator.olean
NLS/KdV/ClassicalCriticalPeriods.olean
NLS/KdV/ClassicalFiniteNormalizedDifferentials.olean
NLS/KdV/FrequencyPrimitiveContinuation.olean
NLS/KdV/FrequencyContourDecomposition.olean
NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow.olean
NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction.olean
NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities.olean
NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence.olean
NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion.olean
NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension.olean
```

The separate `.lake/article-imports` directory is an import overlay with
symlinks to read-only canonical imports and this worktree's own outputs.
Canonical dependencies are not copied, built or overwritten. The runner
does not invoke Lake against that overlay or change the global toolchain.
The reference checkout can be supplied with `DISS_LEAN_REFERENCE`; its
default is the agreed canonical checkout. The caller may also supply
`ELAN_HOME` and `MATHLIB_CACHE_DIR` explicitly.

Raw compiler logs stay in the private chat's `work/check/` directory.
Downloaded source PDFs, extracted text, renderings, object files and scratch
checks are not tracked. The pinned PDF hash is in `source.json`.

## Coverage limits

The generic flow results require a supplied action-frequency function;
coordinatewise continuity is an explicit assumption where needed. Actual
globally normalized rough spectral functions and their sharp estimates
remain to be proved. The actual continuous-potential discriminant and local
primitive charts have now been imported and extended; see
`PRIMITIVE_CONTINUATION.md`. The mass obstruction is now instantiated with signed finite truncations,
and mass divergence is proved from the exact endpoint condition. These
approximants have not yet been identified with physical smooth data through
an actual KdV Birkhoff map. The original mass-divergence adapter proves a compact-time obstruction;
the new separate fixed-time argument is recorded in
`FIXED_TIME_NONEXTENSION.md`. Both still require actual-equation spectral
and physical identifications.

The new PDE module proves physical differential algebra and smooth spatial
balances. It does not construct solutions, differentiate their time-dependent
integrals, establish spectral identities, or justify low-regularity products
of distributions. Main Theorems 1.2, 1.3, 1.9, 1.12 and the advertised further
results remain open. `SOURCE_MAP.md` and `PROGRESS.md` retain their domains,
topologies, endpoints, quantifier order and remaining requirements.

Aggregate imports and full combined validation are reserved for sequential
main integration after shared foundations are available. Expensive full
builds must hold `/tmp/diss-lean-article-build.lock`.


The import-overlay setup materializes private parent directories before
installing a new or replaced output link, so adding a shared sequence module
cannot write through a canonical-directory symlink. All selected output
files are ordinary files under the private build tree. The local checker
and all compiled proof modules remain separate from canonical build products.


The warning policy was corrected in the fixed-time milestone: the previous
`-E warning` flag did not enforce warnings as errors. The final ten-module
run uses Lean's actual `warningAsError=true` option and passes without
warnings. Previous passing logs contained no warnings, and their axiom
audits remain valid; no linter is disabled by this correction.


The frequency-contour milestone is detailed in `FREQUENCY_MOMENTS.md`.
It checks the actual contour algebra, not construction of spectral factors
or physical frequencies. Zeroth-period normalization and spectral analytic
properties remain explicit hypotheses to be discharged by their
construction. Neither finite sums nor the general contour norm estimate
replace the sharp spectral bounds needed for Theorems 1.2 and 1.9.
The subsequent summation milestone proves the infinite-series convergence
and analyticity implication from local remainder bounds; the actual
spectral estimates remain open. See `FREQUENCY_SERIES.md`.


The actual primitive-continuation milestone is detailed in
`PRIMITIVE_CONTINUATION.md`. It merges the shared action/discriminant branch
through `2135a680ab46ba7c476060e9a66db7d5753f8b29`, with ancestry retained.
All fifteen modules of that shared checker, the positive-index example,
and its 199-declaration transitive audit were rerun successfully in this
worktree after the public derivative-identity extraction. Those shared
modules use a separate private output directory; none is built into the
canonical checkout. Upstream shared coverage records are historical
snapshots; current consumed-source hashes are in this article's source.json.

The final frequency check compiles forty selected modules with both
strict options, and audits their private/generated declarations and all
imported NLS dependencies. It does not claim the article's full main
statements on rough potentials or a full dissertation-library build. Both
integration checkers were serialized with the shared build lock. No new
axioms, proof placeholders, disabled linters or increased heartbeats were
introduced by this milestone.


The free normalized differential milestone is detailed in
`FREE_FREQUENCY_PSI.md`. It imports the shared free-normalized source
continuation through `ecd0109` and proves the actual free numerator basis,
periods and positive moments. Both the 23-module frequency checker and
the updated shared integration checker are rerun on the current source.
The source canonical product identity and the normalized psi functions
away from zero remain open; no main theorem is marked verified.

Final free-basis validation: all 23 selected frequency modules pass with
`-DautoImplicit=false -DwarningAsError=true`. The full transitive frequency
audit passes for 404 selected declarations and 2002 declarations including
imported NLS dependencies. The updated shared checker passes all 20 shared
modules, its positive-index example and the 269-declaration transitive
shared-namespace audit. Both runs finish with exit code zero. The canonical
checkout remains clean on main; no full repository validation is claimed.


The actual critical-branch and finite-normalization milestone is detailed
in `FINITE_NORMALIZATION.md`. It retains the exact source `1/(2*pi)` period
factor and constructs analytic coefficients, rather than assuming a finite
matrix inverse or normalized functions. It adds no axioms, disabled linters
or raised heartbeat limits. No new shared branch merge is required: it
consumes the already imported scalar/root continuation modules directly.
The existing shared integration record remains historical for that merge;
this milestone's 33-module check includes all newly consumed dependencies.

Final finite-normalization validation: all 33 selected modules pass with
both strict options and default heartbeats. The complete transitive audit
passes for 497 selected-module declarations and 2148 declarations including
imported NLS dependencies. The only permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`. Source hashes match the checked files.
The canonical checkout remains clean on main. No full dissertation build
or article main-theorem completion is claimed.


The uniform critical-basis milestone is detailed in
`UNIFORM_CRITICAL_BASIS.md`. It imports the shared actual high-contour
foundation through `963d5bb`, preserving ancestry. Both the 40-module
frequency check and the updated shared integration checker are rerun on
the current source in private output trees. Upstream shared coverage
records remain historical snapshots. Current consumed-source hashes and
final audit counts are recorded in this article's `source.json`.

Final uniform critical-family frequency check: all 40 selected modules
pass with both strict options and default heartbeats. The transitive audit
passes for 570 selected declarations and 12091 declarations including
imported NLS dependencies. The larger dependency count reflects the reused
complete complex critical labeling theory. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted. No full dissertation
build or article main-theorem completion is claimed.

The shared integration recheck also passes: all 26 shared modules, the
positive-index example, and the transitive shared-namespace audit of 337
declarations. Both serialized validation processes finish with exit code
zero. The upstream shared snapshots remain historical; this records the
current integration, including the preserved public derivative lemma.
