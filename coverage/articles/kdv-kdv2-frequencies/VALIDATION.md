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
| `NLS/KdV/FrequencyMoments.lean` | Literal weighted moments, Banach analyticity, odd and analytic-removal cancellations, norm estimate and binomial period expansions. |
| `NLS/KdV/FrequencyContourDecomposition.lean` | Exact cubic/fifth-power coefficients and finite-gap normalized exterior-period decompositions, using the proved finite-hole Cauchy theorem. |

All twelve selected modules compile with pinned **Lean 4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using canonical **mathlib
v4.33.1** compiled imports at source base
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Options:
`-DautoImplicit=false -DwarningAsError=true`. The default heartbeat budget is retained.
No linters are disabled; no `sorry`, `admit` or new axioms are introduced.

Final output of `bash scripts/check-kdv-kdv2-frequencies.sh`:

```text
PASS NLS/SequenceSpaces/NonnegativeEnergyDivergence
PASS NLS/SequenceSpaces/HilbertEnergyDivergence
PASS NLS/Dynamics/ActionDependentWeightedPhaseFlow
PASS NLS/Dynamics/FixedTimePhaseObstruction
PASS NLS/KdV/FrequencyMoments
PASS NLS/KdV/FrequencyContourDecomposition
PASS NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow
PASS NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction
PASS NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion
PASS NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension
Axiom audit passed: 218 candidate declarations; 1593 declarations total.
```

`scripts/CheckKdVKdV2FrequencyCandidates.lean` checks every declaration from
the twelve selected modules (including generated and private declarations)
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
NLS/SequenceSpaces/NonnegativeEnergyDivergence.olean
NLS/SequenceSpaces/HilbertEnergyDivergence.olean
NLS/Dynamics/ActionDependentWeightedPhaseFlow.olean
NLS/Dynamics/FixedTimePhaseObstruction.olean
NLS/KdV/FrequencyMoments.olean
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
spectral functions and their continuity/analyticity estimates remain to be
proved. The mass obstruction is now instantiated with signed finite truncations,
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
replace the sharp spectral bounds and locally uniform infinite-series
convergence needed for Theorems 1.2 and 1.9.
