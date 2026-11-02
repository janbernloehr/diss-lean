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
| `NLS/ComplexAnalysis/RightHalfPlaneSquareRoot.lean`, `RationalCircleIntegrationByParts.lean` | Exact square-root sign in the positive frequency plane and closed-circle quotient integration by parts without an interior extension. |
| `NLS/KdV/FreeHighContourPeriods.lean`, `ClassicalUniformPeriodEntries.lean` | All fixed positive free contour periods, exact mapped energy path/Jacobian, and every analytic scalar period entry on one common neighborhood with full free identity. |
| `NLS/KdV/HighEnergyContourSeparation.lean`, `ClassicalPeriodIntegrationByParts.lean` | Actual uniform high energy separation and exact primitive tail formula; scalar 20/pi norm estimate retains a shifted-primitive bound. |
| `NLS/KdV/ActionHamiltonianMoments.lean`, `ClassicalContourMoments.lean`, `ClassicalHighContourMoments.lean` | Previously imported shared moment and actual contour-path dependencies, now compiled directly by the frequency checker. |
| `NLS/KdV/ClassicalDiscriminantUniformVariation.lean`, `FreeContourUniformLowerBound.lean`, `ClassicalUniformRootBounds.lean` | Uniform actual source derivatives, compact free-circle lower bound and one continued-root lower bound for all positive contours on a small potential ball. |
| `NLS/KdV/ClassicalUniformPrimitiveBounds.lean`, `ClassicalUniformCriticalLocalization.lean`, `ClassicalUniformPeriodBounds.lean` | Actual primitive error O(norm q), all-mode half-radius critical control, and an actual uniform reciprocal-square off-diagonal period tail bound. |
| `NLS/ComplexAnalysis/BanachTaylorBounds.lean`, `NLS/ZakharovShabat/ClassicalHorizontalStripBounds.lean` | Existing shared Banach Cauchy and actual IVP strip estimates, now directly recompiled as consumed dependencies. |
| `NLS/SequenceSpaces/ConvolutionDominatedMatrix.lean`, `ConvolutionMatrixAnalytic.lean`, `ReciprocalSquareKernel.lean` | Constructed bounded matrix actions, bounded linear matrix-symbol assembly, genuine operator-norm analyticity and a nonvanishing summable reciprocal-square majorant. |
| `NLS/KdV/ClassicalAllContourPeriods.lean`, `ClassicalAllContourPeriodBounds.lean`, `ClassicalPeriodOperator.lean`, `ClassicalPeriodInverse.lean` | One all-mode actual spectral family, full matrix bounds including the diagonal, the constructed analytic period operator and its analytic two-sided inverse of norm at most two near zero. |
| Six newly selected existing sequence modules | Multipliers, convolution, punctured reciprocal lattice, Holder products, operator basis equality and bounded-coordinate Banach analyticity; all directly recompiled before their consumers. |
| `NLS/SequenceSpaces/AnalyticReciprocalTail.lean`, `NLS/KdV/ClassicalNumeratorHilbert.lean` | Actual local reciprocal numerator tails, genuine l2 membership and a jointly Banach analytic entire numerator basis. |
| `NLS/KdV/ClassicalHilbertPeriod.lean`, `ClassicalNormalizedDifferentials.lean` | Actual Bochner period/row equality, absolutely convergent positive-index normalized entire functions, exact free slice and every normalization period on both frequency circles and mapped energy paths. |
| Four newly selected existing sequence/integral modules and the square-root identity | Local realizations, finite head/tail membership, bilinear Holder duality, Bochner circle interchange, and the general public principal-root square identity are directly recompiled. |
| Six new critical product/relabeling/convergence modules | Exact complete selected signed critical labeling, actual derivative product (15) on the full energy plane near zero, and the filled omitted-factor critical basis product. |
| Six newly selected existing product/labeling/analysis dependencies | Complex derivative product, complete central multiplicities and labels, finite l^p modifications, entire-limit removal and local square-root charts are directly recompiled. |
| `PositiveIndexWeight.lean`, `DiagonalIntertwining.lean`, `AnalyticOperatorInverse.lean` | Bounded reciprocal index symbol, actual operator/inverse intertwining, and a reusable constructed local analytic inverse near the identity. |
| `ClassicalWeightedPeriodOperator.lean`, `ClassicalWeightedPeriodInverse.lean`, `ClassicalWeightedNormalizedCoefficients.lean` | Actual one-weight matrix bounds and compatible inverses; genuine analytic l2 weighted coefficient errors, uniformly small before all positive indices, retaining every normalization period. |
| `RankOneDominatedMatrix.lean`, `MixedMajorantMatrix.lean`, `PositiveIndexPowerWeight.lean` | Actual Hilbert outer-product matrix bounds, analytic combined-majorant assembly, bounded reciprocal power symbols and the positive reciprocal Hilbert sequence. |
| `ClassicalTwoWeightedPeriodOperator.lean`, `ClassicalTwoWeightedPeriodInverse.lean`, `ClassicalTwoWeightedNormalizedCoefficients.lean` | Constructed actual twice-weighted matrix and compatible inverse; genuine analytic two-weight l2 coefficient errors and all-index smallness with exact n² scaling, retaining the actual normalized periods. |
| `ClassicalNormalizedResidues.lean` and the public one-weight energy kernel | Analytic actual l1 residue coefficients, fixed-energy reciprocal denominator bounds, absolute critical resolvent convergence and exact normalized entire-function identity; the one-weight estimate is reused as a public dependency. |
| Five new candidate geometry/row/zero-map modules | Full disc separation, positive quadratic resolvent bounds, actual analytic candidate roots, genuine analytic l2 resolvent rows and the actual jointly analytic l2 zero equation. |
| `CoordinateQuadraticDerivative.lean`, `ClassicalNormalizedRootBranches.lean` | Actual bounded identity derivative and a constructed analytic Hilbert displacement solving every retained infinite root equation on one source neighborhood for fixed n. |
| `ClassicalNormalizedZeroIdentity.lean`, `ClassicalNormalizedZeros.lean` | Literal normalized numerator zeros, including filled critical energies; distinct analytic energy zeros with exact free values and all original actual periods retained. |
| Four newly selected existing sequence/implicit-function modules | Two-majorant membership, translated reciprocal rows, actual coordinate Frechet derivatives and verified analytic Banach implicit roots are directly recompiled. |
| `ClassicalCandidateNumeratorUnits.lean`, `ClassicalNormalizedZeroFactorization.lean` | Nonzero filled critical basis factors and an exact normalized numerator/zero-equation factor identity throughout the candidate domain, retaining multiplicities. |
| `ClassicalNormalizedZeroDerivative.lean`, `ClassicalNormalizedSimpleZeros.lean` | Constructed invertibility of the actual operator-norm analytic partial map, proved diagonal structure and nonzero energy derivatives of all retained actual normalized zeros on one source neighborhood for fixed n. |
| `ClassicalCandidateRootProducts.lean` and two newly selected existing reflection/product modules | Genuine l2 signed free displacement and locally uniform entire signed product with its exact simple root set; this still includes zero/omitted placeholders and is not the Psi_n product identity. |
| `OddSquareDescent.lean`, `PairedEnergyProduct.lean`, `PairedEnergyZeros.lean`, `OmittedPairedEnergyProduct.lean` | Reusable exact paired/omitted positive energy products, whole-plane local uniform cutoff convergence, exact simple product zero sets and literal omitted prefactor. |
| `ClassicalCandidateEnergyProducts.lean`, `ClassicalNormalizedProductQuotient.lean` and three directly recompiled existing analytic dependencies | Actual selected Hill products, zero-displacement critical basis, constructed entire normalized quotient/factorization, nonzero selected-root quotient and exact free value one; all original periods retained. |
| `PositiveOddMultiplier.lean`, `PairedEnergyResolventExterior.lean`, `ClassicalNormalizedResolventExterior.lean` | Constructed actual odd Hilbert direction from two-weight inverse coefficients; exact paired energy resolvent, analytic leading scalar/free value and actual exterior asymptotic. |
| `ClassicalNormalizedProductAsymptotics.lean`, `ClassicalNormalizedProductConstant.lean` and four directly recompiled exterior/circle dependencies | Actual quotient limit and constancy, nonzero analytic scalar, complete simple actual Psi_n zero set and locally uniform actual products multiplied by that scalar, with constructed local families and every period retained. |

All 141 selected modules compile with pinned **Lean 4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using canonical **mathlib
v4.33.1** compiled imports at source base
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Options:
`-DautoImplicit=false -DwarningAsError=true`. The default heartbeat budget is retained.
No linters are disabled; no `sorry`, `admit` or new axioms are introduced.

Final output of `bash scripts/check-kdv-kdv2-frequencies.sh`:

```text
PASS NLS/ComplexAnalysis/BanachTaylorBounds
PASS NLS/SequenceSpaces/Convolution
PASS NLS/SequenceSpaces/Reflection
PASS NLS/SequenceSpaces/Multiplier
PASS NLS/SequenceSpaces/PositiveOddMultiplier
PASS NLS/ZakharovShabat/ClassicalHorizontalStripBounds
PASS NLS/SequenceSpaces/PositiveIndexWeight
PASS NLS/SequenceSpaces/PuncturedLattice
PASS NLS/SequenceSpaces/PositiveIndexPowerWeight
PASS NLS/SequenceSpaces/OperatorBasisExt
PASS NLS/SequenceSpaces/DiagonalIntertwining
PASS NLS/SequenceSpaces/BoundedCoordinateDifferentiable
PASS NLS/SequenceSpaces/CoordinateQuadraticDerivative
PASS NLS/SequenceSpaces/HolderEmbedding
PASS NLS/SequenceSpaces/BoundedCoordinateAnalytic
PASS NLS/ComplexAnalysis/JointSpectralDerivative
PASS NLS/ComplexAnalysis/AnalyticOperatorInverse
PASS NLS/SequenceSpaces/ConvolutionDominatedMatrix
PASS NLS/SequenceSpaces/LocallyBoundedRealization
PASS NLS/SequenceSpaces/TwoSequenceBound
PASS NLS/SequenceSpaces/FiniteHeadTailBound
PASS NLS/SequenceSpaces/AnalyticReciprocalTail
PASS NLS/SequenceSpaces/ConjugateDuality
PASS NLS/ComplexAnalysis/BilinearCircleIntegral
PASS NLS/SequenceSpaces/ConvolutionMatrixAnalytic
PASS NLS/SequenceSpaces/RankOneDominatedMatrix
PASS NLS/SequenceSpaces/MixedMajorantMatrix
PASS NLS/SequenceSpaces/ReciprocalSquareKernel
PASS NLS/ComplexAnalysis/ParametricDividedDifference
PASS NLS/ComplexAnalysis/AnalyticImplicitBanachRoot
PASS NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
PASS NLS/ComplexAnalysis/RightHalfPlaneSquareRoot
PASS NLS/ComplexAnalysis/EntireLimit
PASS NLS/ComplexAnalysis/LocalAnalyticSquareRoot
PASS NLS/ComplexAnalysis/SquareProductConvergence
PASS NLS/ComplexAnalysis/RemovableFactorConvergence
PASS NLS/ComplexAnalysis/RationalCircleIntegrationByParts
PASS NLS/ZakharovShabat/ContinuousPotentialL2Bound
PASS NLS/SequenceSpaces/FiniteModification
PASS NLS/ZakharovShabat/FreeDerivativeZeroCounts
PASS NLS/ZakharovShabat/CriticalPointLabeling
PASS NLS/ZakharovShabat/DiscriminantDerivativeProduct
PASS NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood
PASS NLS/ZakharovShabat/NearFreeCriticalRelabeling
PASS NLS/KdV/ConstantUpperSpectralBridge
PASS NLS/KdV/ClassicalSpectralSymmetry
PASS NLS/KdV/ClassicalDiscriminant
PASS NLS/KdV/ClassicalLocalPrimitive
PASS NLS/KdV/ClassicalDiscriminantUniformVariation
PASS NLS/KdV/ClassicalFreePrimitive
PASS NLS/KdV/ClassicalHillFlow
PASS NLS/KdV/ClassicalHillSpectrum
PASS NLS/KdV/ClassicalSourcePrimitive
PASS NLS/KdV/ClassicalSpectralEmbedding
PASS NLS/KdV/ClassicalContourCoverage
PASS NLS/KdV/ActionHamiltonianMoments
PASS NLS/KdV/ClassicalContourMoments
PASS NLS/KdV/ClassicalHighContourMoments
PASS NLS/ComplexAnalysis/AnalyticSquareDescent
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
PASS NLS/KdV/FreeHighContourPeriods
PASS NLS/KdV/FreeContourUniformLowerBound
PASS NLS/KdV/ClassicalUniformRootBounds
PASS NLS/KdV/ClassicalUniformPrimitiveBounds
PASS NLS/KdV/ClassicalCriticalPointBranch
PASS NLS/KdV/ClassicalHighCriticalPoints
PASS NLS/KdV/HighEnergyContourSeparation
PASS NLS/KdV/HighEnergyDiscSeparation
PASS NLS/KdV/PositiveEnergyResolventKernel
PASS NLS/KdV/ClassicalCriticalNumerator
PASS NLS/KdV/ClassicalUniformCriticalBasis
PASS NLS/KdV/ClassicalCriticalTailAnalytic
PASS NLS/KdV/ClassicalUniformCriticalLocalization
PASS NLS/KdV/ClassicalCriticalPeriods
PASS NLS/KdV/ClassicalFiniteNormalizedDifferentials
PASS NLS/KdV/ClassicalUniformPeriodEntries
PASS NLS/KdV/ClassicalPeriodIntegrationByParts
PASS NLS/KdV/ClassicalUniformPeriodBounds
PASS NLS/KdV/ClassicalAllContourPeriods
PASS NLS/KdV/ClassicalAllContourPeriodBounds
PASS NLS/KdV/ClassicalPeriodOperator
PASS NLS/KdV/ClassicalPeriodInverse
PASS NLS/KdV/ClassicalWeightedPeriodOperator
PASS NLS/KdV/ClassicalTwoWeightedPeriodOperator
PASS NLS/KdV/ClassicalWeightedPeriodInverse
PASS NLS/KdV/ClassicalTwoWeightedPeriodInverse
PASS NLS/KdV/ClassicalNumeratorHilbert
PASS NLS/KdV/ClassicalHilbertPeriod
PASS NLS/KdV/ClassicalNormalizedDifferentials
PASS NLS/KdV/ClassicalWeightedNormalizedCoefficients
PASS NLS/KdV/ClassicalTwoWeightedNormalizedCoefficients
PASS NLS/KdV/ClassicalNormalizedResidues
PASS NLS/KdV/ClassicalCandidateZeros
PASS NLS/SequenceSpaces/CompactPuncturedKernel
PASS NLS/KdV/ClassicalCandidateResolvents
PASS NLS/KdV/ClassicalNormalizedZeroMap
PASS NLS/KdV/ClassicalNormalizedRootBranches
PASS NLS/KdV/ClassicalNormalizedZeroIdentity
PASS NLS/KdV/ClassicalNormalizedZeros
PASS NLS/KdV/ClassicalSignedCriticalProduct
PASS NLS/KdV/ClassicalCandidateNumeratorUnits
PASS NLS/KdV/ClassicalNormalizedZeroFactorization
PASS NLS/KdV/ClassicalNormalizedZeroDerivative
PASS NLS/KdV/ClassicalNormalizedSimpleZeros
PASS NLS/ZakharovShabat/SourceGapInterpolationProduct
PASS NLS/KdV/ClassicalCandidateRootProducts
PASS NLS/ComplexAnalysis/CauchyFiniteHoles
PASS NLS/ComplexAnalysis/OddSquareDescent
PASS NLS/ZakharovShabat/PairedEnergyProduct
PASS NLS/ZakharovShabat/SourcePsiRootResolventExterior
PASS NLS/ZakharovShabat/PairedEnergyResolventExterior
PASS NLS/ZakharovShabat/SingleSpectralProductRatioExterior
PASS NLS/ZakharovShabat/PairedEnergyZeros
PASS NLS/ZakharovShabat/OmittedPairedEnergyProduct
PASS NLS/KdV/ClassicalCriticalEnergyProduct
PASS NLS/KdV/ClassicalCriticalBasisProduct
PASS NLS/KdV/ClassicalCandidateEnergyProducts
PASS NLS/ComplexAnalysis/FilledSimpleQuotient
PASS NLS/KdV/ClassicalNormalizedProductQuotient
PASS NLS/KdV/ClassicalNormalizedResolventExterior
PASS NLS/KdV/ClassicalNormalizedProductAsymptotics
PASS NLS/ComplexAnalysis/EntireCircleDecay
PASS NLS/ZakharovShabat/CentralCircleThresholds
PASS NLS/KdV/ClassicalNormalizedProductConstant
PASS NLS/KdV/FrequencyPrimitiveContinuation
PASS NLS/KdV/FrequencyContourDecomposition
PASS NLS/Articles/KdVKdV2Frequencies/SignedPhaseFlow
PASS NLS/Articles/KdVKdV2Frequencies/MassPhaseObstruction
PASS NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence
PASS NLS/Articles/KdVKdV2Frequencies/SignedMassInsertion
PASS NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension
Axiom audit passed: 1582 candidate declarations; 13743 declarations total.
```

`scripts/CheckKdVKdV2FrequencyCandidates.lean` checks every declaration from
the 141 selected modules (including generated and private declarations)
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


The infinite scalar period-entry milestone is detailed in `UNIFORM_PERIOD_ENTRIES.md`.
It consumes the already merged shared contour paths, retains their orientation
and exact energy Jacobian, and proves the actual uniform off-diagonal tail
formula. No new shared merge or canonical build mutation is required.

Final strict run: all 49 selected modules pass; the complete transitive audit
passes for 662 selected declarations and 12186 declarations including
all imported NLS dependencies. The only permitted axioms remain `propext`,
`Classical.choice` and `Quot.sound`. The source hashes cover all 49 selected
modules. The build and audit module selections agree exactly.

The optional `--prepare-only` switch only prepares private overlay links and
output directories for focused checks. The default command still performs
the full strict build and transitive audit. No warning exceptions, disabled
linters, additional axioms or raised heartbeat limits are introduced.
All main-theorem statuses remain open.


The actual uniform primitive milestone is detailed in `UNIFORM_PRIMITIVE_BOUNDS.md`.
It discharges the preceding scalar primitive-bound input, gives an actual
uniform reciprocal-square period tail, localizes every selected critical
frequency inside half the contour radius, and proves diagonal energy separation.

Final strict run: all 57 selected modules pass; the complete transitive audit
passes for 700 selected declarations and 12209 declarations including
all imported NLS dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. All 57 source hashes match the checked files,
and the checker, axiom audit and coverage selections agree exactly.

Both newly selected shared dependencies are compiled before their consumers
in the private import overlay. The full run uses strict options and default
heartbeats, without warning exceptions, disabled linters or additional axioms.
No new shared merge or canonical mutation is required. Full matrix operator
realization, infinite normalization and all main-theorem statuses remain open.


The actual analytic period-operator inverse milestone is detailed in
`ANALYTIC_PERIOD_INVERSE.md`. It constructs the full operator in the
Banach operator norm and its analytic two-sided inverse, retaining the
same selected spectral data on the final neighborhood.

Final strict run: all 70 selected modules pass; the complete transitive audit
passes for 869 selected declarations and 12291 declarations including
all imported NLS dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. All 70 source hashes match the checked files,
and the checker, axiom audit and coverage selections agree exactly.

The static module list is ordered by transitive NLS imports so that every
selected private output exists before any consumer is compiled. Strict
warnings, default heartbeats, private outputs and read-only canonical imports
are retained. No warnings are waived, linters disabled or axioms added.
Convergent normalized entire differentials, canonical products and all main
theorems remain open. No full dissertation build is claimed.


The actual infinite normalized entire-family milestone is detailed in
`INFINITE_NORMALIZED_DIFFERENTIALS.md`. It proves the actual Hilbert basis,
convergence, joint analyticity and every literal normalization period
near zero in the continuous-potential norm.

Final strict run: all 78 selected modules pass; the complete transitive audit
passes for 949 selected declarations and 12358 declarations including
all imported NLS dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted. All 78 source hashes match the checked files,
and the checker, axiom audit and coverage selections agree exactly.

The modified mapped-energy normalization is included in the final full run;
it also passes a focused strict recheck. Explicit composition arguments
keep the joint analytic pairing proof within the default heartbeat budget.
No heartbeat increases, warning exceptions, disabled linters or additional
axioms are introduced. Canonical products, global/rough compatibility and
all main-theorem statuses remain open. Canonical sources/builds are read only.


The exact selected critical-product milestone is detailed in
`CRITICAL_PRODUCTS.md`. Equation (15) holds for the actual selected
critical energies near the free continuous potential, with locally
uniform convergence on the entire complex energy plane. The omitted
nth factor gives the actual filled critical basis, including its own
critical energy. No normalized Psi_n zero/product identification is
claimed by this critical-basis result.

Final strict run: all 90 selected modules pass; the complete transitive
audit passes for 1067 selected declarations and 12429 declarations
including all imported NLS dependencies. The checker, audit and coverage
selections agree exactly, and all 90 checked source hashes match. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. Default
heartbeats, strict warnings and all linters remain enabled.

The canonical product (52) of the normalized Psi_n, global/rough
compatibility and every main-theorem inventory row remain open. Shared
canonical sources and compiled dependencies are read only; no shared
branch merge was needed for this milestone.


The actual one-weight normalized coefficient milestone is detailed in
`WEIGHTED_NORMALIZED_COEFFICIENTS.md`. The literal index-weighted inverse
column error is a genuine l2 vector with Banach analyticity and all-index
uniform smallness near zero. Both weighted and unweighted period maps and
inverses are constructed from the actual period matrix on one common
neighborhood, with exact compatibility via a bounded reciprocal diagonal.
The same R defines the normalized entire family and all its actual periods.

Final strict run: all 96 selected modules pass; the complete transitive
audit passes for 1118 selected declarations and 12480 declarations
including all imported NLS dependencies. All 96 checked source hashes
match, and the checker, audit and coverage selections agree exactly.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There
are no new axioms, placeholders, heartbeat increases, warning exceptions
or disabled linters. Shared canonical sources/builds remain read only.

A second index weight, actual normalized zeros/products, global/rough
compatibility and every article main theorem remain open. No main-theorem
inventory row is closed by the present coefficient estimate.


The two-weight normalized coefficient and critical resolvent milestone is
detailed in `TWO_WEIGHTED_NORMALIZED_COEFFICIENTS.md`. The actual squared-
index inverse-column error is a Banach analytic l2 vector, uniformly small
near zero with exact n² scaling. The bounded twice-weighted operator
retains the necessary outer-product far tail, and its actual inverse is
compatible with the R used by the normalized entire functions. Positive
residue coefficients are genuinely analytic in l1; fixed-energy critical
reciprocals are bounded, giving absolute critical resolvent convergence
and the exact entire-function identity off the critical energies.

Final strict run: all 103 selected modules pass; the complete transitive
audit passes for 1224 selected declarations and 12586 declarations
including all imported NLS dependencies. All 103 checked source hashes
match, and the checker, audit and coverage selections agree exactly.
The modified public one-weight energy kernel is directly recompiled.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There
are no new axioms, placeholders, heartbeat increases, warning exceptions
or disabled linters. Canonical sources and compiled dependencies remain
read only; the full validation is serialized by the shared build lock.

Actual normalized zeros, complete product identification (52), global/
rough compatibility and every main theorem remain open. These weighted
coefficient and resolvent results close no main-theorem inventory row.


The actual infinite normalized zero-family milestone is detailed in
`NORMALIZED_ZEROS.md`. For each fixed omitted n, a jointly analytic l2
zero equation has proved free partial derivative equal to the bounded
identity. The verified Banach implicit-function theorem constructs one
analytic l2 displacement solving every other positive index together.
The result is connected to zeros of the actual normalized entire
numerator, including at filled own critical energies, with distinct
analytic energy values and exact free energies. All original actual
normalization periods remain available on the common base neighborhood.

Final strict run: all 116 selected modules pass; the complete transitive
audit passes for 1332 selected declarations and 12712 declarations
including all imported NLS dependencies. All 116 checked source hashes
match, and the checker, audit and coverage selections agree exactly.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Default
heartbeats, strict warnings and all linters are retained. There are no
new axioms or placeholders. All canonical sources/builds remain read only.
The full validation is serialized by the shared build lock.

The zero subneighborhood may depend on n. Completeness, simplicity, real
gap placement, exact canonical product/prefactor (52), omitted-index
uniformity, the full rough/global domain and every main theorem remain
open. No main-theorem inventory row is closed by this local result.


The actual simple normalized zero and selected signed product milestone
is detailed in `SIMPLE_NORMALIZED_ZEROS.md`. A proved filled identity with
nonzero critical basis factors transports the actual nonzero diagonal
partial derivatives to nonzero energy derivatives of Psi_n. The partial
Hilbert map is operator-norm analytic and has a constructed inverse on
one smaller source neighborhood, before every retained index. The
analytic zero family, free values, distinctness and original periods are
retained for each fixed omitted n.

The signed selected roots also have genuine l2 free-lattice displacement.
The reused arbitrary-complex product theorem gives local uniform cutoff
convergence and precisely those simple product roots. This product still
contains zero and omitted-mode placeholders; no completeness or canonical
product identity for Psi_n is inferred from it.

Final strict run: all 123 selected modules pass; the complete transitive
audit passes for 1395 selected declarations and 13537 declarations
including all imported NLS dependencies. All 123 checked source hashes
match, and the checker, audit and coverage selections agree exactly.
The reflection and generic product dependencies are directly recompiled.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. There
are no new axioms, placeholders, heartbeat increases, disabled linters or
warning exceptions. Canonical sources/builds remain clean and read only.
The full validation is serialized by the shared build lock.

The source subneighborhood can depend on omitted n. Completeness for
Psi_n, its exact canonical product/prefactor, real gap placement, omitted-
index uniformity, full rough/global compatibility and all main theorems
remain open. No main-theorem inventory row is closed by this local result.


## Selected energy products and actual entire quotients

The current product/factorization milestone is detailed in
`NORMALIZED_ENERGY_PRODUCTS.md`. Literal positive energy cutoffs and the
omitted product with prefactor 2/(n*pi) converge locally uniformly on the
whole energy plane. The candidate product has precisely the selected
retained simple roots, including the filled omitted energy in the entire
convergence statement. Zero displacement recovers the actual critical
basis. The actual normalized Psi_n factors as this product times an
entire quotient, nonzero at selected roots and exactly one on the whole
free slice. Constructed local families retain every original period.

All 132 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1495
selected declarations and 13635 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound. All
132 source hashes and checker/audit/coverage selections agree. There are
no additional axioms, placeholders, heartbeat changes, disabled linters
or warning exceptions. The full run is serialized by the shared build
lock; compiled outputs are private and canonical sources/builds remain
read only.

An entire factorization does not prove the quotient constant or one at
nonzero potentials. Completeness for Psi_n, exact source (52), common
omitted-index uniformity, real gap/sharp root estimates (54), rough/global
compatibility and every main theorem remain open. No main inventory row
is closed by this milestone.


## Constant actual quotient and complete normalized zero set

The current milestone is detailed in `NORMALIZED_PRODUCT_CONSTANT.md`.
The actual normalized energy resolvent has a proved residue-sum leading
asymptotic, using an odd Hilbert direction constructed from the actual
two-weight inverse column. Free-normalized product ratios and entire
circle decay identify the entire quotient with the analytic leading
scalar. Simplicity at one retained actual root proves this scalar
nonzero. The selected retained roots are now the complete actual Psi_n
zero set, all simple, and literal products multiplied by the scalar
converge locally uniformly to Psi_n on the whole energy plane. The
constructed local families retain every original period and free value.

All 141 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1582
selected declarations and 13743 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound. All
141 source hashes and checker/audit/coverage selections agree. There are
no additional axioms, placeholders, heartbeat changes, disabled linters
or warning exceptions. The full run is serialized by the shared build
lock; all selected outputs are private and canonical sources/builds
remain read only.

The nonzero-potential value L_n=1 remains unproved. This milestone
therefore does not close exact source (52), its rough/global W domain
or the common omitted-index source neighborhood. Real gap/sharp root
estimates (54), physical frequency/flow identification and every article
main theorem remain open. No main inventory row is marked verified.
