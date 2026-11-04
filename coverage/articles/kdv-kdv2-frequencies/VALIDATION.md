# Article-step validation — 2026-11-04

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
| Selected proved whole-gap/annulus dependencies from convexity `4b8896c`, with local derivative additions preserved | Actual continuous-potential whole-gap analytic squares, source-strip normalization, branch matching and complete annulus source coverage; imported provenance and qualifications recorded separately. |
| `ClassicalHillWholeGapQuotients.lean`, `ClassicalHillOddDifferentialMoments.lean`, `ClassicalHillLowOddDifferentialMoments.lean` | Nonzero analytic filled quotients on complete high gaps, exact sheet/endpoints, actual differential radius independence, uniform high cancellation and finite-head source tubes yielding all-mode common-neighborhood odd cancellation. |
| `ClassicalNormalizedMoments.lean`, `ClassicalNormalizedOddMoments.lean`, extended `FrequencyMoments.lean` | Literal actual normalized moments, exact mapped energy contour and Jacobian, all-mode moment analyticity, exact original zeroth periods and every odd cancellation on one near-zero complex continuous-potential neighborhood. |
| Selected collapsed-gap dependencies from convexity `9d1741c` | Actual two-zero deflation including double roots, nonzero deflated units, and constructed analytic square roots on complete discs; local extensions preserved. |
| `ClassicalHillCollapsedDifferentialMoments.lean`, `ClassicalNormalizedCollapsedMoments.lean`, extended `FrequencyMoments.lean` | Every positive actual normalized moment vanishes at each high collapsed gap on one common local family, including the diagonal; retains all-mode analyticity, exact zeroth periods and odd cancellation. |
| `ClassicalCriticalResolvent.lean`, `CirclePowerIntegrationByParts.lean`, `ClassicalNormalizedMomentResolvent.lean` | Actual analytic Hilbert critical/squared resolvents; all-mode original contour avoidance; exact all-order 2*pi/(m+1) moment formula; absolute positive-index convergence outside the integral via a Bochner integral and Holder pairing. |
| Selected normalized endpoint-quotient sources from convexity `135b1fa`, extended `ClassicalCriticalTailAnalytic.lean`, and new `TwoZeroCriticalLocalization.lean`, `SquaredCoshCriticalDisc.lean`, `ClassicalCriticalGapLocalization.lean` | Arbitrarily small common high critical-frequency confinement at any continuous complex source; actual critical displacement at quadratic gap scale with arbitrarily small coefficient, analytic families, collapsed equality and diagonal critical-pole separation on gap circles. |
| Selected cut-root and contour-homotopy sources from convexity `135b1fa`, existing affine/nested circle dependencies, and five new weighted-period/Hilbert/moment modules | Actual all-order high-gap critical kernel bounds and quadratic basis-period bounds; constructed normalized second moments with quadratic diagonal and quartic off-diagonal gap-length bounds, retaining all original periods and cancellations on one local family. |
| `DiagonalBilinearPairing.lean`, `AnalyticTailSummation.lean`, `ClassicalTwoWeightedMomentBounds.lean`, `ClassicalFrequencyGapMajorant.lean`, `ClassicalNormalizedFrequencySeries.lean`, and the existing canonical gap identification | Actual weighted high second-moment bound and locally bounded l1 frequency-gap majorant; constructed normalized second-moment series is absolutely convergent, analytic and locally uniformly convergent near zero for every output index. Physical frequency identification and full rough/global scope remain open. |
| Selected actual Hminus1 trace/Miura/source-sheet dependencies from convexity `08db7a5`, `AnalyticSimpleCriticalBranch.lean`, `HillHminusOneCriticalPoints.lean`, `HillHminusOneCriticalNumerators.lean`, and `HillHminusOnePeriodEntries.lean` | Actual simple high critical energies at arbitrary complex rough sources; exact free labels; a common entire critical basis and all original contour/analytic period entries on one Hminus1-open neighborhood, with the full free identity matrix. Rough operator inversion and normalized moments remain open. |
| `HillHminusOneCriticalControl`, `HillHminusOneUniformPrimitiveBounds`, `HillHminusOnePeriodBounds`, `HillHminusOnePeriodInverse`, `HillHminusOneNumeratorHilbert`, `HillHminusOneHilbertPeriod`, `HillHminusOneNormalizedDifferentials`, `HillHminusOneNormalizedMoments` and shared elementary bounds | Actual rough uniform contour estimates; constructed bounded analytic period operator and two-sided inverse; normalized entire differentials and all-order moment analyticity with exact zeroth periods on one Hminus1-open neighborhood of zero. Full W and physical frequencies remain open. |
| `ClassicalRoughEmbedding`, `ClassicalRoughCriticalCompatibility`, `ClassicalRoughNormalizationCompatibility`, `HillHminusOneNormalizedOddMoments` and three generic uniqueness/congruence modules | Exact continuous interval/rough trace and normalized-family agreement, including all indices, filled centers and actual inverses; analytic propagation and true Fourier density give all odd normalized cancellation on one Hminus1-open ball. Full W and physical frequencies remain open. |
| `HillHminusOneTwoWeightedPeriodOperator`, `HillHminusOneTwoWeightedPeriodInverse`, `AnalyticTwoWeightedInverseColumns`, `HillHminusOneTwoWeightedNormalizedMoments`, `HillHminusOneSmallCriticalControl`, `HillHminusOneCriticalGapLocalization` and selected rough square/quotient sources | Actual weighted rough operator/inverse and analytic l2 errors, with all normalized/free/period/odd features retained on the same family; actual quadratic critical-gap localization, exact collapsed equality and any relative-gap coefficient locally in Hminus1. Sharp normalized moments, full W, lp remainders and physical frequencies remain open. |
| Eleven actual rough kernel/cut/second-moment modules detailed in `HMINUS_SECOND_MOMENTS.md` | Genuine direct Hilbert pole kernel, exact all-order normalized moment pairing and absolute coefficient series; same-pair cut roots and signed weighted deformation; filled collapsed cancellation; constructed sharp quadratic/quartic/twice-weighted actual rough second-moment bounds. Rough summable gap majorant and physical frequencies remain open. |
| `SquaredPairGapBound`, `HillHminusOneCanonicalFrequencyGaps`, `HillHminusOneFrequencyGapMajorant`, `HillHminusOneNormalizedFrequencySeries` and existing `UniformCanonicalPeriodicEndpoints` | Genuine rough locally bounded l1 gap majorant through the exact Miura energy shift; absolute/localuniform/analytic actual normalized second-moment series on one rough-open neighborhood before all output indices. Physical Hamiltonian identity (69), full W and all main theorems remain open. |
| Seven new real-preserving Miura/energy-descent modules and existing `ConjugateReflection`, `SourcePsiLemma12_11` | Actual physically real rough Miura charts at every real Hminus1 base potential; proved applicability of the common normalized NLS psi theorem; jointly analytic filled energy candidates with exact fixed-shift 2z factor identity. Hill energy normalization and all main theorems remain open. |
| Six new even-trace/root/contour/pullback modules and existing `SourceTheorem12_1` | Complete actual endpoint/multiplicity reflection, odd actual canonical root, exact signed contour transformation and constructed all-index positive Kronecker energy pullbacks near every real Hminus1 base potential. Global Hill energy-root/chart independence and physical frequencies remain open. |
| Seven actual energy-root/mapped-contour/chart-agreement modules and two existing real-band/domain dependencies | Actual jointly analytic Hill energy roots; positive mapped contours with winding one and exact normalization; root independence on the whole common energy domain at real inputs and equality of full joint complex germs. Entire-numerator identification and all main theorems remain open. |
| Four actual real-scaling/spectral-exclusion/root-compatibility modules | Nonreal spectral exclusion at every real rough potential; old continuation-domain inclusion; actual free normalization; root equality on full common domains near zero and agreement of full complex energy/source germs. Entire-numerator identification and all main theorems remain open. |
| Five complete critical-energy and genuine residue modules | All real rough Hill critical points are real and simple; actual complete positively indexed energy critical coordinates; exact signed residue transfer, genuine principal limits, analytic coefficient germs and central filling. Hilbert realization and main theorems remain open. |
| Nine actual critical-interpolation, residue Hilbert and entire representation modules | Derived exterior decay, exact Cauchy interpolation, genuine l2 residues and energy coefficients, absolute energy principal series and full filled entire canonical Hilbert representation at real rough chart inputs. Old weighted-family/contour identification and main theorems remain open. |

All 417 selected modules compile with pinned **Lean 4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, using canonical **mathlib
v4.33.1** compiled imports at source base
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Options:
`-DautoImplicit=false -DwarningAsError=true`. The default heartbeat budget is retained.
No linters are disabled; no `sorry`, `admit` or new axioms are introduced.

Validation output: the prior full strict rebuild of 415 unchanged modules,
followed by two strict incremental compilations and a fresh combined
transitive axiom audit of all 417 selected modules:

```text
# Prior full strict rebuild: 415 unchanged modules
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
PASS NLS/ComplexAnalysis/AffineLoopHomotopy
PASS NLS/ComplexAnalysis/ParametricDividedDifference
PASS NLS/ComplexAnalysis/AnalyticImplicitBanachRoot
PASS NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization
PASS NLS/ComplexAnalysis/PrescribedAnalyticSquareRoot
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
PASS NLS/ZakharovShabat/UniformSmallCriticalDisplacements
PASS NLS/ZakharovShabat/UniformCanonicalPeriodicEndpoints
PASS NLS/ZakharovShabat/SourceCriticalRootRatioContourHomotopy
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
PASS NLS/ComplexAnalysis/NestedCircleHomotopy
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
PASS NLS/KdV/ClassicalCoshStripControl
PASS NLS/KdV/ClassicalHillDiscAsymptotics
PASS NLS/KdV/ClassicalHillHighTracePhase
PASS NLS/KdV/ClassicalHillSmallDiscTrace
PASS NLS/KdV/ClassicalHillSmallGapCoverage
PASS NLS/ZakharovShabat/ClassicalSolutionInjectivity
PASS NLS/KdV/ClassicalHillGreen
PASS NLS/KdV/ClassicalHighGapPairs
PASS NLS/KdV/ClassicalHillReality
PASS NLS/KdV/ClassicalHillConjugation
PASS NLS/ComplexAnalysis/ContinuousSquareRootPath
PASS NLS/KdV/ClassicalHillPrimitiveSheets
PASS NLS/KdV/ClassicalHillPrimitiveReflection
PASS NLS/KdV/ClassicalHillBandNormalization
PASS NLS/KdV/ClassicalHillHighPrimitiveStrip
PASS NLS/KdV/ClassicalHillHighEndpointNormalization
PASS NLS/KdV/ClassicalHillSquaredPrimitiveMatching
PASS NLS/KdV/ClassicalHillWholeGapSquares
PASS NLS/KdV/ClassicalHillAnnulusCoverage
PASS NLS/KdV/ClassicalHillWholeGapQuotients
PASS NLS/KdV/ClassicalNormalizedMoments
PASS NLS/KdV/ClassicalHillOddDifferentialMoments
PASS NLS/KdV/ClassicalHillLowOddDifferentialMoments
PASS NLS/KdV/ClassicalNormalizedOddMoments
PASS NLS/ComplexAnalysis/TwoRootQuotientDiscBound
PASS NLS/ComplexAnalysis/TwoZeroDeflation
PASS NLS/KdV/ClassicalHillGapQuotients
PASS NLS/ComplexAnalysis/AnalyticDiscSquareRoot
PASS NLS/KdV/ClassicalHillCollapsedDifferentialMoments
PASS NLS/KdV/ClassicalNormalizedCollapsedMoments
PASS NLS/KdV/ClassicalCriticalResolvent
PASS NLS/ComplexAnalysis/CirclePowerIntegrationByParts
PASS NLS/KdV/ClassicalNormalizedMomentResolvent
PASS NLS/ComplexAnalysis/AnalyticLocalLipschitz
PASS NLS/KdV/ClassicalHillFreeSquareComparison
PASS NLS/ComplexAnalysis/NormalizedSquareRootBounds
PASS NLS/KdV/ClassicalHighGapFamilies
PASS NLS/KdV/ClassicalHillGapQuotientAsymptotics
PASS NLS/ComplexAnalysis/TwoZeroCriticalLocalization
PASS NLS/KdV/SquaredCoshCriticalDisc
PASS NLS/KdV/ClassicalCriticalGapLocalization
PASS NLS/KdV/ClassicalHillGapScaleBounds
PASS NLS/ComplexAnalysis/AnalyticTwoZeroRoot
PASS NLS/KdV/ClassicalHillGapCutRoots
PASS NLS/ComplexAnalysis/SquaredCircleHomotopy
PASS NLS/ComplexAnalysis/AnalyticCutContour
PASS NLS/KdV/ClassicalHillWeightedCutPeriods
PASS NLS/KdV/WeightedCutGapBounds
PASS NLS/KdV/ClassicalCriticalPrimitivePeriods
PASS NLS/SequenceSpaces/HilbertCoordinateRemainder
PASS NLS/KdV/ClassicalNormalizedGapMomentBounds
PASS NLS/SequenceSpaces/DiagonalBilinearPairing
PASS NLS/KdV/ClassicalTwoWeightedMomentBounds
PASS NLS/ZakharovShabat/CanonicalWeightedGapSummability
PASS NLS/KdV/ClassicalFrequencyGapMajorant
PASS NLS/SequenceSpaces/AnalyticTailSummation
PASS NLS/KdV/ClassicalNormalizedFrequencySeries
PASS NLS/FunctionalAnalysis/PeriodicIntegrationByParts
PASS NLS/MKdV/MiuraClassicalSolution
PASS NLS/SequenceSpaces/ConjugateReflection
PASS NLS/MKdV/SobolevMiuraPotential
PASS NLS/FunctionalAnalysis/LinearVolterraFlow
PASS NLS/MKdV/QuasiHillDiscriminant
PASS NLS/MKdV/MiuraBoundaryTransfer
PASS NLS/ZakharovShabat/ClassicalVolterraTrace
PASS NLS/MKdV/QuasiHillZSComparison
PASS NLS/MKdV/QuasiHillJointAnalytic
PASS NLS/ComplexAnalysis/SourceDiscriminantPrimitive
PASS NLS/ZakharovShabat/ContinuousPotentialSource
PASS NLS/ZakharovShabat/SourceCanonicalRootRealBand
PASS NLS/MKdV/QuasiHillSourcePrimitive
PASS NLS/DifferentialPolynomial/UngradedIntegrationByParts
PASS NLS/DifferentialPolynomial/PowerSeriesDerivation
PASS NLS/DifferentialPolynomial/DifferentialRiccati
PASS NLS/DifferentialPolynomial/RiccatiResolvent
PASS NLS/DifferentialPolynomial/LogarithmicDerivative
PASS NLS/DifferentialPolynomial/MiuraRiccati
PASS NLS/DifferentialPolynomial/ConstructedRiccatiResolvent
PASS NLS/DifferentialPolynomial/RiccatiResolventNaturality
PASS NLS/DifferentialPolynomial/MultiJet
PASS NLS/ZakharovShabat/SourcePsiLemma12_11
PASS NLS/ZakharovShabat/SobolevHierarchySymmetries
PASS NLS/MKdV/HierarchyRestriction
PASS NLS/DifferentialPolynomial/RiccatiResolventParity
PASS NLS/ZakharovShabat/NLSRiccatiResolvent
PASS NLS/MKdV/MiuraHierarchyHamiltonians
PASS NLS/DifferentialPolynomial/PolynomialVariation
PASS NLS/DifferentialPolynomial/AlgebraicPolynomialVariation
PASS NLS/DifferentialPolynomial/EulerLagrange
PASS NLS/DifferentialPolynomial/IndependentJetVariation
PASS NLS/DifferentialPolynomial/RiccatiResolventVariation
PASS NLS/ZakharovShabat/NLSRiccatiResolventVariation
PASS NLS/FunctionalAnalysis/UnitIntervalMean
PASS NLS/DifferentialPolynomial/SmoothVariation
PASS NLS/ZakharovShabat/ClassicalNLSHierarchyVariation
PASS NLS/DifferentialPolynomial/EulerScalar
PASS NLS/Fourier/PeriodicVariationalUniqueness
PASS NLS/ZakharovShabat/NLSRiccatiResolventGradient
PASS NLS/MKdV/HierarchyGradientRecurrence
PASS NLS/MKdV/MiuraHierarchyFlowRestriction
PASS NLS/DifferentialPolynomial/EulerOrderBounds
PASS NLS/ZakharovShabat/SobolevPolynomialL2
PASS NLS/Fourier/CircleUnitCoefficients
PASS NLS/ZakharovShabat/SobolevPolynomialVariation
PASS NLS/ZakharovShabat/SobolevSourceCotangent
PASS NLS/ZakharovShabat/SobolevSmoothFirstVariation
PASS NLS/MKdV/SobolevMiuraHillHamiltonian
PASS NLS/MKdV/MiuraHillRiccatiRemainder
PASS NLS/Fourier/CircleBilinearMean
PASS NLS/ZakharovShabat/SobolevPolynomialEndpointMean
PASS NLS/ZakharovShabat/SobolevScalarSmoothDensity
PASS NLS/MKdV/NativeMiuraHillHamiltonian
PASS NLS/MKdV/QuasiHillPhysicalEquation
PASS NLS/MKdV/QuasiHillPhysicalUniqueness
PASS NLS/MKdV/PhysicalHillDiscriminant
PASS NLS/MKdV/MiuraHillHamiltonianTrace
PASS NLS/MKdV/MiuraHillSpectralBridge
PASS NLS/KdV/HillNLSPrimitivePathComparison
PASS NLS/MKdV/MiuraHillPrimitiveComparison
PASS NLS/MKdV/QuasiHillPrimitiveComparison
PASS NLS/MKdV/SobolevQuasiHill
PASS NLS/MKdV/SobolevMiuraPrimitive
PASS NLS/KdV/FreeHill
PASS NLS/KdV/HillComplement
PASS NLS/KdV/HillReduction
PASS NLS/KdV/HillSobolev
PASS NLS/KdV/HillPhysical
PASS NLS/KdV/HillFirstOrderReduction
PASS NLS/KdV/HillAnalytic
PASS NLS/KdV/HillWeightedCoefficients
PASS NLS/KdV/HillBilinearSymmetry
PASS NLS/KdV/HillSpectralLipschitz
PASS NLS/FunctionalAnalysis/TwoDimensionalDeterminant
PASS NLS/KdV/HillRootSeparation
PASS NLS/SequenceSpaces/WeightedInsertion
PASS NLS/KdV/HillPeriodOnePotential
PASS NLS/KdV/HillL2SpectralCriterion
PASS NLS/KdV/HillClassicalIdentification
PASS NLS/FunctionalAnalysis/AbsoluteContinuityTranslation
PASS NLS/KdV/HillFullPeriod
PASS NLS/FunctionalAnalysis/LinearVolterraLinearity
PASS NLS/KdV/ClassicalHillMultipliers
PASS NLS/KdV/HillDiscriminantNecessity
PASS NLS/KdV/HillDiscriminantComparison
PASS NLS/ComplexAnalysis/EntireEvenSquareDescent
PASS NLS/KdV/HillL2EnergyDiscriminant
PASS NLS/MKdV/MiuraL2HillDiscriminant
PASS NLS/SequenceSpaces/PeriodOneMassResolvent
PASS NLS/SequenceSpaces/PeriodOneMiuraQuadratic
PASS NLS/ComplexAnalysis/SmallQuadraticInverse
PASS NLS/SequenceSpaces/PeriodOneMiuraCharts
PASS NLS/SequenceSpaces/PeriodOneMiuraRegularity
PASS NLS/SequenceSpaces/PeriodOneMiuraShift
PASS NLS/KdV/HillL2ConstantShift
PASS NLS/KdV/HillMiuraL2Discriminant
PASS NLS/SequenceSpaces/PeriodOneHminusOneDensity
PASS NLS/KdV/HillHminusOneDiscriminant
PASS NLS/ComplexAnalysis/ShiftedSquareRootBounds
PASS NLS/KdV/HillFreeEnergyShift
PASS NLS/KdV/HillHminusOneDiscAsymptotics
PASS NLS/KdV/HillWeightIndependence
PASS NLS/KdV/HillLocalization
PASS NLS/KdV/HillZeroCount
PASS NLS/ComplexAnalysis/ZeroCountHomotopy
PASS NLS/ComplexAnalysis/TwoZeroOrderComparison
PASS NLS/KdV/HillCharacteristicZeros
PASS NLS/KdV/HillRealSpectrum
PASS NLS/ComplexAnalysis/TracePrimitiveContinuation
PASS NLS/KdV/HillL2SourcePrimitive
PASS NLS/ComplexAnalysis/TracePrimitiveFunctoriality
PASS NLS/KdV/HillHminusOneSourcePrimitive
PASS NLS/KdV/HillHminusOneSmallGapCoverage
PASS NLS/KdV/HillHminusOneAnnulusCoverage
PASS NLS/ComplexAnalysis/AnalyticSimpleCriticalBranch
PASS NLS/KdV/HillHminusOneCriticalPoints
PASS NLS/KdV/HillHminusOneCriticalNumerators
PASS NLS/KdV/HillHminusOnePeriodEntries
PASS NLS/KdV/HillHminusOneCriticalControl
PASS NLS/KdV/HillHminusOneTraceControl
PASS NLS/ComplexAnalysis/LogarithmStripNormalization
PASS NLS/KdV/HillHminusOnePrimitiveStrip
PASS NLS/ComplexAnalysis/CoshStripBounds
PASS NLS/ZakharovShabat/SourceSection8SineEstimates
PASS NLS/ComplexAnalysis/CompactSliceBounds
PASS NLS/KdV/HillHminusOneUniformPrimitiveBounds
PASS NLS/ComplexAnalysis/CriticalBasisPeriodBounds
PASS NLS/KdV/HillHminusOnePeriodBounds
PASS NLS/KdV/HillHminusOnePeriodInverse
PASS NLS/KdV/HillHminusOneNumeratorHilbert
PASS NLS/KdV/HillHminusOneHilbertPeriod
PASS NLS/KdV/HillHminusOneNormalizedDifferentials
PASS NLS/KdV/HillHminusOneNormalizedMoments
PASS NLS/ComplexAnalysis/AnalyticImplicitUniqueness
PASS NLS/KdV/ClassicalRoughEmbedding
PASS NLS/KdV/ClassicalRoughCriticalCompatibility
PASS NLS/ComplexAnalysis/ParametricDividedDifferenceCongruence
PASS NLS/KdV/ClassicalRoughNormalizationCompatibility
PASS NLS/ComplexAnalysis/DenseLinearAnalyticUniqueness
PASS NLS/KdV/HillHminusOneNormalizedOddMoments
PASS NLS/KdV/HillHminusOneTwoWeightedPeriodOperator
PASS NLS/KdV/HillHminusOneTwoWeightedPeriodInverse
PASS NLS/KdV/HillHminusOneWholeGapSquares
PASS NLS/KdV/HillHminusOneFreeSquareComparison
PASS NLS/ComplexAnalysis/QuadraticClusterCount
PASS NLS/KdV/HillHminusOneHighGapPairs
PASS NLS/KdV/HillHminusOneGapQuotients
PASS NLS/KdV/HillHminusOneGapQuotientAsymptotics
PASS NLS/SequenceSpaces/AnalyticTwoWeightedInverseColumns
PASS NLS/KdV/HillHminusOneSmallCriticalControl
PASS NLS/KdV/HillHminusOneCriticalGapLocalization
PASS NLS/KdV/HillHminusOneTwoWeightedNormalizedMoments
PASS NLS/SequenceSpaces/QuadraticPoleKernel
PASS NLS/ComplexAnalysis/CriticalBasisPowerPeriods
PASS NLS/KdV/HillHminusOneMomentKernel
PASS NLS/KdV/HillHminusOneNormalizedMomentKernel
PASS NLS/ComplexAnalysis/CollapsedPowerPeriods
PASS NLS/KdV/HillHminusOneCriticalGapCutRoots
PASS NLS/KdV/HillHminusOneWeightedCutPeriods
PASS NLS/KdV/HillHminusOneGapPairUniqueness
PASS NLS/KdV/HillHminusOneCriticalPrimitivePeriods
PASS NLS/KdV/HillHminusOneNormalizedGapMomentBounds
PASS NLS/KdV/HillHminusOneTwoWeightedMomentBounds
PASS NLS/ComplexAnalysis/SquaredPairGapBound
PASS NLS/KdV/HillHminusOneCanonicalFrequencyGaps
PASS NLS/KdV/HillHminusOneFrequencyGapMajorant
PASS NLS/KdV/HillHminusOneNormalizedFrequencySeries
PASS NLS/ComplexAnalysis/EquivariantSmallQuadraticInverse
PASS NLS/SequenceSpaces/PeriodOneMiuraConjugation
PASS NLS/SequenceSpaces/PeriodOneRealMiuraCharts
PASS NLS/KdV/HillHminusOneRealMiuraCharts
PASS NLS/KdV/HillHminusOneRealMiuraSourcePsi
PASS NLS/ComplexAnalysis/ParametricOddSquareDescent
PASS NLS/KdV/HillHminusOneRealMiuraEnergyPsi
PASS NLS/ZakharovShabat/EvenDiscriminantPeriodicEndpoints
PASS NLS/ZakharovShabat/EvenDiscriminantCanonicalRoot
PASS NLS/ComplexAnalysis/NegatedCircleIntegral
PASS NLS/KdV/HillHminusOneMiuraRootSymmetry
PASS NLS/ZakharovShabat/SourceTheorem12_1
PASS NLS/ZakharovShabat/EvenPsiAntisymmetricPeriods
PASS NLS/KdV/HillHminusOneMiuraEnergyPeriods
PASS NLS/ZakharovShabat/EvenPositivePeriodCircle
PASS NLS/KdV/HillHminusOneMiuraEnergyRoot
PASS NLS/ComplexAnalysis/ShiftedSquaredCircle
PASS NLS/KdV/HillHminusOneMappedEnergyPeriods
PASS NLS/ComplexAnalysis/NonrealConnectedDomain
PASS NLS/ZakharovShabat/SourceHighShiftedRealBand
PASS NLS/KdV/HillHminusOneEnergyRootChartAgreement
PASS NLS/SequenceSpaces/PeriodOneRealScaling
PASS NLS/KdV/HillHminusOneRealSpectralExclusion
PASS NLS/KdV/HillHminusOneEnergyRootFreeAgreement
PASS NLS/KdV/HillHminusOneEnergyRootContinuationAgreement
PASS NLS/ComplexAnalysis/EvenSpectralDerivatives
PASS NLS/ZakharovShabat/EvenRealCanonicalCriticalPoints
PASS NLS/KdV/HillHminusOneRealCriticalEnergyGeometry
PASS NLS/ComplexAnalysis/SimpleZeroPrincipalCoefficient
PASS NLS/KdV/HillHminusOneMiuraCriticalResidues
PASS NLS/ZakharovShabat/SourcePsiCriticalQuotientExterior
PASS NLS/ZakharovShabat/SourcePsiCriticalInterpolation
PASS NLS/ComplexAnalysis/SimplePoleCircleResidue
PASS NLS/ZakharovShabat/SourcePsiCriticalResidueBounds
PASS NLS/KdV/HillHminusOneMiuraResidueHilbert
PASS NLS/ZakharovShabat/SourcePsiCriticalAbsoluteInterpolation
PASS NLS/KdV/HillHminusOneMiuraEnergyPrincipalSeries
PASS NLS/ComplexAnalysis/EntireCriticalHilbertBasis
PASS NLS/KdV/CanonicalMiuraNumeratorRepresentation
PASS NLS/ComplexAnalysis/SimpleRootGermUniqueness
PASS NLS/KdV/HillHminusOneCriticalChartIndependence
PASS NLS/KdV/HillHminusOneCriticalChartGerms
# Strict incremental compilation: two new modules
PASS NLS/KdV/FreeHillCriticalEnergies
PASS NLS/KdV/HillHminusOneCanonicalCriticalCompatibility
# Fresh combined audit: all 417 selected modules
Axiom audit passed: 4854 candidate declarations; 27013 declarations total.
```

`scripts/CheckKdVKdV2FrequencyCandidates.lean` checks every declaration from
the 417 selected modules (including generated and private declarations)
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


## Actual normalized odd moments on one all-mode neighborhood

The current milestone is detailed in `NORMALIZED_ODD_MOMENTS.md`.
The actual literal normalized moments have exact mapped energy contour
identities and Jacobians, all-mode analyticity and zeroth normalization.
Every odd moment vanishes on one common near-zero complex continuous-
potential neighborhood before all positive numerator/contour indices
and moment orders. The low contours, diagonal and collapsed gaps are
included. The proof constructs filled primitive/root quotients and uses
shared whole-gap squares/annulus coverage for the tail, then actual
compact free-source tubes and a finite intersection for the head.

Selected source imports are recorded in `SHARED_WHOLE_GAP_IMPORT.json`.
The local joint analytic derivative and exported squaredCosh derivative
are retained. The whole-gap square theorem is generalized to arbitrary
positive bounds, with its original unit-bound interface preserved.
The whole convexity branch and its L2-only outputs are not merged.

All 164 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1778
selected declarations and 13953 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound. All
164 source hashes and checker/audit/coverage selections agree. There are
no additional axioms, placeholders, heartbeat increases, disabled linters
or warning exceptions. The full run is serialized by the shared build
lock; all selected outputs are private and canonical sources/builds
remain read only.

This does not close the full W/rough-topology version of Lemma 3.1,
its even collapsed-moment clause, sharp moment/root estimates or the
exact nonzero-potential canonical leading scalar. Physical frequency/
Hamiltonian/Birkhoff flow identification and all main theorem rows
remain open. No main inventory row is marked verified.


## Positive normalized moments at actual collapsed high gaps

The current milestone is detailed in `NORMALIZED_COLLAPSED_MOMENTS.md`.
One actual normalized family retains all-mode analyticity, exact zeroth
periods and odd cancellation. On the same neighborhood, every positive
moment vanishes at each actual high collapsed gap, including diagonal
numerators. The actual squared-gap zero criterion forces the two roots
to coincide. Literal deflation constructs a nonzero analytic unit, its
disc square root supplies an analytic primitive extension, and a fixed
sign on the connected circle identifies the actual primitive. The
already constructed primitive/root quotient then fills the integrand.

`SHARED_COLLAPSED_GAP_IMPORT.json` records the selected proved sources
from convexity `9d1741c`; existing local extensions are preserved. The
whole branch and L2-only modules are not merged. No ZS RealType result
is applied to the Hill coefficient pair.

All 171 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1811
selected declarations and 13976 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound. All
171 source hashes and checker/audit/coverage selections agree. There are
no placeholders, new axioms, heartbeat increases, disabled linters or
warning exceptions. The full run uses the shared build lock and private
selected outputs; canonical sources/builds remain read only.

Finite low even collapsed contours, full W/rough-topology compatibility,
sharp normalized estimates, the exact nonzero-potential canonical scalar,
and physical frequency/Hamiltonian/action/Birkhoff flow identification
remain open. Every article main theorem remains unverified.


## Exact all-order normalized moment resolvent formulas

The current milestone is detailed in `NORMALIZED_MOMENT_RESOLVENT.md`.
The jointly analytic actual Hilbert critical resolvent is constructed
from the entire basis divided by Delta-prime. Its negative energy
derivative has the literal squared-denominator coordinates. Complete
selected critical labeling proves all original contours avoid every
critical point, including the finite head. Closed-circle power
integration by parts supplies the exact coefficient 2*pi/(m+1). A
genuine Hilbert Bochner contour integral and Holder summability prove
the absolutely convergent positive-index series outside the integral.
The actual normalized family retains all-mode moment analyticity,
exact zeroth normalization, odd cancellation and inverse norm at most
two on one local continuous-potential neighborhood.

All 174 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1858
selected declarations and 14023 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All selected source hashes, provenance hashes and build/audit/coverage
selections agree; selected outputs are private. No placeholders, new
axioms, heartbeat increases, disabled linters or warning exceptions
are introduced. Canonical sources and builds remain read only.

The new formula does not discard the diagonal critical summand. Sharp
normalized gap/root estimates, full W/rough-topology compatibility,
the exact nonzero-potential canonical scalar and physical frequency/
Hamiltonian/action/Birkhoff identification remain open. All main
theorem inventory rows remain unverified.


## Actual critical gap localization

The current milestone is detailed in `CRITICAL_GAP_LOCALIZATION.md`.
At every continuous complex source, one energy radius precedes all
tolerances, common neighborhoods/cutoffs and high indices. The actual
critical, midpoint and squared-gap families retain analyticity. The
critical displacement is at most eta times |squared gap|/k for any
prescribed eta>0 after choosing the common tail. It lies within one
quarter gap length of the actual midpoint and is separated from the
gap-length circle by at least half a gap length. Actual counted endpoint
geometry also proves the continuous-potential form of (37) with any
prescribed relative-gap tolerance on one common tail. At an actual collapsed
high gap it equals the midpoint. This follows from actual uniformly
small Hilbert critical tails, whole-disc normalized endpoint quotients,
proved stationarity of the primitive square and a Cauchy unit estimate.

The selected source record `SHARED_CRITICAL_GAP_IMPORT.json` preserves
local extensions and compatible older interfaces. Four new proved
continuous-potential dependencies are imported; the whole branch and
Miura/L2-only developments are not merged. No ZS RealType input is
imposed on the actual Hill coefficient pair.

All 183 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 1935
selected declarations and 14088 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and build/audit/coverage selections agree.
Selected outputs are private; canonical sources and builds remain read
only. No placeholders, new axioms, heartbeat increases, disabled linters
or warning exceptions are introduced.

The weighted lp remainder in Lemma 2.11(i), full rough/global W scope,
sharp normalized root/moment estimates, canonical scalar L_n=1 and
physical frequency/action/Birkhoff flow identification remain open.
No main theorem inventory row is marked verified.


## Actual normalized second moments at high-gap scale

The current milestone is detailed in `NORMALIZED_SECOND_GAP_BOUNDS.md`.
One constructed local complex continuous-potential normalized family has
quadratic diagonal and quartic off-diagonal second-moment gap-length
bounds on every high contour, uniformly before all numerator indices.
Every original zeroth period, all-mode analyticity and odd cancellation,
and every positive high collapsed-gap cancellation are retained.
The actual diagonal zeroth-period lower bound is constructed from
operator-norm continuity at the free identity. Actual cut-period
homotopies avoid critical poles; the exact Bochner resolvent formula
and zeroth normalization preserve the additional off-diagonal gap factor.

All 195 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 2095
selected declarations and 14239 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and checker/audit/coverage selections agree.
Selected outputs are private; canonical sources and builds remain read
only. No placeholders, new axioms, heartbeat increases, disabled linters
or warning exceptions are introduced.

`SHARED_CRITICAL_PERIOD_GAP_IMPORT.json` records five proved selected
cut-root/contour dependencies from convexity `135b1fa` and three retained
local extensions. Existing affine/nested circle dependencies are directly
recompiled. The whole branch and Miura/L2-only modules are not imported.
No ZS RealType wrapper is imposed on the Hill coefficient pair.

Full sharp index dependence, diagonal asymptotics, finite low even
collapsed contours, rough/global W compatibility, canonical scalar L_n=1
and physical frequency/action/Birkhoff identification remain open.
No main-theorem inventory row is marked verified.


## Analytic actual normalized second-moment series

The current milestone is detailed in `NORMALIZED_FREQUENCY_SERIES.md`.
One constructed local complex continuous-potential normalized family has
an absolutely convergent second-moment series for every output index,
with an analytic sum times the source coefficient -12 and locally
uniform ordinary positive partial sums. Original zeroth normalization,
all-mode moment analyticity and odd cancellation are retained. The proof
uses actual compatible twice-weighted inverse columns and an actual
locally bounded l1 frequency-scale squared-gap majorant, without assuming
unscaled energy-gap summability, continuous endpoint ordering, RealType
or a canonical scalar identity. The finite head is controlled locally.

All 201 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 2167
selected declarations and 14311 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and checker/audit/coverage selections agree.
Selected outputs are private; canonical sources and builds remain read
only. No placeholders, new axioms, heartbeat increases, disabled linters
or warning exceptions are introduced. The 195 previously selected sources
remain byte-identical. No new external branch sources are imported.

This is the local continuous-potential summation step toward source
Theorem 3.4, (73), PDF page 31. Physical identity (69), rough/global W
continuation, action descent, sharp two-index and diagonal asymptotics,
KdV2 series and main frequency/flow theorem obligations remain open.
No main-theorem inventory row is marked verified.


## Actual critical basis and period entries in Hminus1

The current milestone is detailed in `HMINUS_PERIOD_DATA.md`. At every
complex rough source, a proved local Miura chart constructs the actual
analytic/simple high critical energy family with unique shifted-disc
labels. Exact calculus retains its energy shift and proves unshifted
free values near zero. Finite implicit charts and high rough source
coverage give one Hminus1-open neighborhood before every critical,
numerator and original contour index. The actual critical basis is
entire jointly in energy and rough potential, has nonzero filled centers
and exact free slices. Every original scalar period entry is analytic
there, and its whole free matrix is the identity. No rough operator
inverse or normalized Psi_n is assumed or claimed in this result.

All 318 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 3895
selected declarations and 25200 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and checker/audit/coverage selections agree.
Selected outputs are private; canonical sources and builds remain read
only. No placeholders, new axioms, heartbeat increases, disabled linters
or warning exceptions are introduced. All 201 previously selected source
files remain byte-identical.

`SHARED_HMINUS_NORMALIZATION_IMPORT.json` records 113 new proved selected
sources from convexity `08db7a5`, with six compatible local files retained.
The new Euler-Lagrange source adds a direct proved integration-by-parts
import; its proof statements and bodies are unchanged. Two inherited
heartbeat overrides are removed and the unchanged proofs pass at the
default budget. Nine initially
inspected but unused new sources were removed. The full branch is not
merged. All four earlier selected-source provenance records remain valid.

Rough operator bounds/inversion, agreement with the continuous normalized
family, rough moments/summation and full W continuation remain open,
as do physical frequency/action/Birkhoff identification and the other
main theorem obligations. No main-theorem inventory row is verified.


## Actual normalized entire differentials and moments in Hminus1

The current milestone is detailed in `HMINUS_NORMALIZED_MOMENTS.md`.
Actual uniform critical and primitive bounds give summable bounds for
the literal period matrix. Its bounded operator and analytic two-sided
inverse are constructed on one rough-open neighborhood of zero.
Actual Hilbert numerator realization and vector-valued Bochner period
duality construct normalized entire differentials with every exact
original contour normalization and free slice. All literal moments
are analytic on one common Hminus1-open neighborhood before all indices
and orders, with the exact zeroth normalization.

All 334 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 4052
selected declarations and 25355 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and ordered checker/audit/PASS selections
agree. Selected outputs are private. The canonical main checkout remains
unchanged and clean. All 318 previously selected Lean source files remain
byte-identical, and the five earlier import records remain valid.

The three newly selected rough trace/primitive strip sources from
convexity `08db7a5` are unchanged, as recorded in
`SHARED_HMINUS_PRIMITIVE_IMPORT.json`. Existing ZS critical displacement
and cosine bound sources are directly selected for strict recompilation.
There is no whole-branch merge, placeholder, new axiom, heartbeat increase,
disabled linter or warning exception.

The earlier milestone paragraphs above describe their historical scope;
rough period inversion and local normalized moment construction are now
proved. Continuous-family compatibility, full W continuation, rough odd
and collapsed-even cancellation, sharp moment estimates and frequency
summation still remain open, as do physical frequency/action/Birkhoff
identifications and the other complete source main-theorem obligations.
No main-theorem inventory row is verified.

A final trailing-blank-line cleanup in `CompactSliceBounds.lean` was strictly
recompiled; its compiled object is byte-identical to the fully audited
object. The source hash was refreshed and all final checks passed.


## Exact continuous/rough agreement and all normalized rough odd moments

The current milestone is detailed in `HMINUS_NORMALIZED_ODD_MOMENTS.md`.
The actual continuous unit-interval Fourier realization is bounded linear
and dense in Hminus1, with exact physical trace, source-sheet and primitive
agreement and no endpoint matching assumption. One common continuous
neighborhood identifies every critical energy, filled numerator, matrix,
bounded operator, inverse, normalized entire numerator and moment.
Analytic uniqueness through the connected dense linear pullback gives
all odd normalized cancellation on one genuine rough-open ball, before
all positive indices and odd orders. Exact free values, all-order moment
analyticity, zeroth periods and actual rough contour data are retained.

All 341 selected modules pass strict Lean with default heartbeats and
warnings as errors. The complete transitive audit passes for 4102
selected declarations and 25405 declarations including imported NLS
dependencies, using only propext, Classical.choice and Quot.sound.
All source/provenance hashes and ordered checker/audit/PASS selections
agree. Selected outputs are private and fresh. The canonical main checkout
remains unchanged and clean. All 334 previously selected Lean source files
are byte-identical, and all six earlier provenance records remain valid.
There are seven new own proved modules, with no new external source import,
placeholder, new axiom, heartbeat increase, disabled linter or warning
exception. Earlier milestone paragraphs describe their historical scope;
continuous/rough compatibility and local rough odd cancellation are now
proved. Full W, even collapsed cancellation in the full required scope,
sharp rough moment bounds/summation, the exact canonical prefactor and
physical frequency/action/Birkhoff identifications remain open. No
main-theorem inventory row is verified.


## Actual rough weighted normalization and quadratic critical-gap localization

The current milestone is detailed in `HMINUS_WEIGHTED_CRITICAL_GAPS.md`.
The raw energy-kernel period bound and mixed majorant construct an actual
rough twice-weighted period operator and analytic inverse. Exact weighted
coordinate compatibility realizes genuine analytic l2 inverse column errors,
uniformly epsilon-small after n^2 scaling on a common neighborhood. The same
actual normalized family retains all operator/inverse/free/entry/period
assertions, joint entire numerator analyticity, all moment analyticities,
exact zeroth periods and every odd cancellation.

Actual selected critical energies obey quadratic displacement from actual
unordered gap midpoints, quarter-gap confinement, exact collapsed equality
and gap-circle pole separation on one local rough neighborhood/tail. The
radius precedes epsilon, and actual whole-gap analytic square, trace/primitive
matching and free-normalized filled endpoint quotient data are retained.
Any prescribed relative-gap coefficient gives the local Hminus1 form of
source (37). Full W and the lp remainder of Lemma2.11(i) remain open.

All 353 selected modules pass strict Lean with default heartbeats and
warnings as errors. The transitive axiom audit passes for 4235 selected
declarations and 25538 declarations including imported NLS dependencies,
using only propext, Classical.choice and Quot.sound. Ordered checker/audit/
PASS/coverage selections agree, source/provenance hashes match, and selected
outputs are private and fresh. Canonical main remains unchanged and clean.
All 341 previously selected Lean sources remain byte-identical. All six
earlier provenance records remain valid.

There are six new own proved sources and six unchanged selected dependencies
from convexity08db7a5, recorded in SHARED_HMINUS_GAP_QUOTIENT_IMPORT.json along
with the retained compatible local whole-gap extension. Two inspected unused
cut-root/scale sources were omitted. No full branch merge, placeholder, new
axiom, heartbeat increase, disabled linter or warning exception is introduced.
Sharp rough normalized moment estimates and frequency summation, even collapsed
cancellation in the full required scope, the exact canonical prefactor, full W
and physical frequency/action/Birkhoff identities remain open. No main-theorem
inventory row is verified.


## Actual rough sharp normalized second moments

The current milestone is detailed in `HMINUS_SECOND_MOMENTS.md`. Eleven
new proved modules construct the actual direct Hilbert moment kernel and
all-order normalized pairing/absolutely convergent coefficient expansion,
without dividing by the discriminant derivative or assuming an exhaustive
rough critical zero set. Same-pair actual cut roots, connected-circle sign,
weighted contour deformation and analytic filled collapsed power periods
give sharp actual rough high-gap second-moment bounds: quadratic diagonal,
quartic off-diagonal and twice-weighted additional k^-2 decay. Every positive
normalized moment vanishes at a collapsed high pair. The constructed family
retains all earlier weighted inverse, entire numerator, moment analytic,
exact zeroth-period and all odd-cancellation data.

All 364 selected modules pass with default heartbeats and warnings as errors.
The transitive permitted-axiom audit passes for 4406 selected declarations
and 25709 declarations including imported NLS dependencies. Ordered
checker/audit/PASS/coverage selections agree; all source hashes and seven
provenance records match; selected outputs are private and fresh. All 353
previously selected Lean sources remain byte-identical. Canonical main is
unchanged and clean. No placeholder, new axiom, heartbeat increase, disabled
linter or warning exception is introduced. No new shared branch import or
full branch merge occurs.

A genuine rough summable gap majorant, actual label/count matching through
the fixed Miura energy shift, the rough frequency series, physical identity
(69), full W, exact canonical product prefactor, action descent and actual
Birkhoff/PDE flows remain open. The finite-head collapsed-even obligation
in the full required scope is separate. All main inventory rows remain OPEN.


## Actual rough normalized frequency-series construction

The current milestone is detailed in `HMINUS_FREQUENCY_SERIES.md`. Four
new proved modules construct a genuine rough canonical l1 frequency-gap
majorant using the actual analytic Miura L2 source, the exact fixed energy
translation and actual counted canonical endpoint membership. Same-disc
unordered-pair uniqueness gives the estimate for every retained actual pair,
including collapsed ones. The actual twice-weighted second moments and
analytic finite head then give an absolutely convergent, locally uniformly
convergent and analytic correction candidate -12*sum k*Omega_nk^2 on one
Hminus1-open neighborhood before every output index. The same full weighted
normalized family and actual cut data remain available.

All 369 selected modules pass strict Lean with default heartbeats and
warnings as errors. The transitive permitted-axiom audit passes for
4453 selected declarations and 25753 imported NLS declarations.
Ordered checker/audit/PASS/coverage selections agree; all source hashes and
seven provenance records match; selected outputs are private and fresh.
All 364 previous selected Lean sources remain byte-identical. One existing
canonical endpoint cutoff dependency is now directly recompiled. No new
shared branch import/full merge, placeholder, axiom, heartbeat increase,
disabled linter or warning exception is introduced. Canonical main remains
unchanged and clean.

This is a local rough version of the actual series in Theorem3.4 (73),
PDF31. It is not the physical identity (69), Lemma3.2, PDF26-27. Full W,
physical Hamiltonian/Poisson/angle and normalized-differential identities,
action descent, sharp source weighted target spaces and asymptotics,
compact derivatives and actual Birkhoff/PDE flows remain open. All main
inventory rows remain OPEN.


## Real-preserving rough Miura charts and entire energy candidates

See `REAL_MIURA_ENERGY_PSI.md` for exact declarations and scope. Seven new
proved modules construct actual real-preserving complex Miura charts at
every physically real Hminus1 base potential. Physical realness proves
applicability of the existing verified common NLS normalized psi theorem.
One rough-open pullback precedes every index and retains actual spectral
isolation, analytic deleted-root branches and exact original raw frequency
periods. Antisymmetrization and a joint filled odd square descent produce
entire-energy candidates with the exact fixed-shift 2z factor identity,
including at the branch point. Hill energy normalization is not asserted.

All 378 selected modules pass strict Lean with default heartbeats and
warnings as errors. The permitted transitive axiom audit passes for
4517 selected declarations and 25796 imported NLS declarations.
Ordered checker/audit/PASS/coverage selections agree; all source hashes and
seven provenance records match; selected outputs are private and fresh.
All 369 previous selected Lean sources remain byte-identical. Two existing
conjugate-reflection/common NLS psi dependencies are directly recompiled.
No new shared branch import/full merge, placeholder, axiom, heartbeat
increase, disabled linter or warning exception is introduced. Canonical
main remains unchanged and clean.

These candidates require actual root parity/sign and contour matching,
Hill energy periods, lowest-cut analysis, overlap compatibility and
identification with the previous local rough normalized family. Global
coherent Hill normalized differentials, exact canonical leading scalar,
source root estimate(54), physical identity(69), action descent, weighted
target spaces/compact derivatives and actual Birkhoff/PDE identification
remain open. Every main inventory row remains OPEN.


## Actual root parity and normalized rough energy pullbacks

See `MIURA_ROOT_PULLBACK_PERIODS.md` for exact declarations and scope.
Six new proved modules derive complete actual spectrum/endpoint and
multiplicity reflection from the even Miura trace. Literal symmetric
standard-root products give oddness of the actual canonical root with
the exceptional central denominator retained. Actual original isolating
circles reflect to opposite indices; the same verified NLS psi family
has exact periods on every such circle. The literal signed change of
variable gives 2pi(delta_mn-delta_(-m),n). For positive indices it is
exactly the source Kronecker normalization. At every real rough base
potential one common complex rough-open set constructs actual analytic
energy candidates, nonempty all-index circles and the normalized
shifted-square pullback periods with the fixed shift and Jacobian 2z.

All 385 selected modules pass strict Lean with default heartbeats and
warnings as errors. The permitted transitive axiom audit passes for
4595 selected declarations and 26767 imported NLS declarations.
Ordered checker/audit/PASS/coverage selections agree; all source hashes and
seven provenance records match; selected outputs are private and fresh.
All 378 previous selected Lean sources remain byte-identical. The existing
`SourceTheorem12_1` is now directly recompiled. No new shared branch import,
full merge, placeholder, axiom, heartbeat increase, disabled linter or
warning exception is introduced. Canonical main remains unchanged and clean.

The proved integrals retain the actual NLS canonical root at the lifted
frequency. A global Hill energy-root function, chart/lift independence,
lowest-cut analysis, overlap compatibility and agreement with the earlier
local rough weighted normalized family remain separate obligations.
Canonical product leading scalar one, source root estimate(54), physical
identity(69), action descent, weighted target spaces/compact derivatives
and actual Birkhoff/PDE identification remain open. All main inventory
rows remain OPEN.


## Actual energy roots, mapped periods and root chart agreement

See `ENERGY_ROOT_CHART_AGREEMENT.md`. Seven new proved modules construct
a nonvanishing jointly analytic square root of the independent rough
Hill radicand from the actual canonical NLS product, with the exact fixed
Miura shift and an open joint domain. Positive original discs lie in the
right half-plane. Actual shifted-square smooth energy contours remain
in the root domain, have winding one and give exact raw 2pi Kronecker
periods of the constructed entire-energy candidates. Mapped endpoint
energies are actual characteristic zeros. One common complex rough-open
neighborhood at every real base potential precedes every index.

Actual canonical high endpoint pairs and the fixed-shift estimate put a
common high real energy in the same indexed band for two charts. The
verified actual real-band sign fixes their branch. Nonreal-domain
connectedness and analytic uniqueness prove root equality on the full
common energy domain at real inputs. The proved joint analytic domains
then give equality of full complex energy/rough-input germs. No root
agreement or sign choice is assumed as a hypothesis.

All 394 selected modules pass strict Lean with default heartbeats and
warnings as errors. The permitted transitive axiom audit passes for
4659 selected declarations and 26819 imported NLS declarations.
Exact ordered checker/audit/PASS/coverage selections, source hashes,
seven provenance records and private fresh outputs agree. All 385 earlier
selected Lean sources remain byte-identical. Two existing actual band-sign
and real-source domain dependencies are newly directly recompiled.
Checker/audit orders follow actual transitive selected imports. No new
shared branch import/full merge, placeholder, axiom, heartbeat increase,
disabled linter or warning exception is introduced. Canonical main remains
unchanged and clean.

Root chart agreement does not prove agreement or uniqueness of the entire
numerators, their canonical leading scalar, or identification with the
earlier rough weighted normalized family. Full coherent W, lowest-cut
primitive/moment identification, sharp source root54, physical frequency69,
action descent, weighted targets/asymptotics/compact derivatives and
actual Birkhoff/PDE flows remain open. All main inventory rows remain OPEN.


## Actual continued-root compatibility near zero

See `CONTINUATION_ROOT_AGREEMENT.md`. Four new proved modules exclude
nonreal periodic spectral zeros for every physically real Hminus1 input,
place every nonreal energy in the original free-normalized continuation
domain, fix the actual free root normalization from high-band signs, and
prove compatibility of the chart energy root with the old continued root.
One norm ball precedes all real inputs and all energies. Equality holds
on each full common energy domain, including real energies and closed-gap
inputs. The corresponding full complex energy/source germs also agree.

All 398 selected modules pass strict Lean with default heartbeats and
warnings as errors. The first combined import exposed a duplicate name
for the new free-root lemma. It was renamed to
`hillHminusContinuedRoot_base_sine`; its module and sole selected consumer
were rebuilt, then the final combined audit passed. The initial log
`work/check/continuation-root-agreement-final.log` retains that diagnostic;
`work/check/continuation-root-agreement-audit-final.log` records the final
two successful rebuilds and audit. The proof bodies and the earlier
394 selected sources are unchanged. The permitted transitive axiom audit passes for
4671 selected declarations and 26831 imported NLS declarations.
Exact ordered checker/audit/PASS/coverage selections, all source hashes,
seven provenance records and private fresh outputs agree. All 394 earlier
selected Lean sources remain byte-identical. No shared branch import,
placeholder, new axiom, heartbeat increase, disabled linter or warning
exception is introduced. Canonical main remains unchanged and clean.

Pointwise complex germ agreement is not a single uniform complex rough
neighborhood for all contours. Entire-numerator Hilbert realization and
identification with the earlier weighted normalized family, full coherent
W, physical frequency69, action descent, weighted target/asymptotic and
compact derivative claims and actual Birkhoff/PDE identification remain
open. All main inventory rows remain OPEN.


## Complete actual rough critical energies and principal coefficients

See `CRITICAL_ENERGY_RESIDUES.md`. Actual canonical critical reflection,
central cancellation and the shifted-square derivative identities give a
complete strictly ordered real sequence of simple critical energies at
every real-type rough chart input. Constructed actual charts imply that
every critical point of the independent Hill trace is real and simple at
every physically real Hminus1 potential, with no cutoff or open-gap exception.

The actual descended entire numerator has exact signed critical-residue
transfer with factor 2 beta. An analytic filled simple-zero quotient proves
the genuine punctured principal-coefficient limit. Fixed energy critical
coordinates and residue coefficients have full complex rough-input analytic
germs at real inputs. The central numerator is filled by its original
source derivative, and the central energy resolvent is jointly analytic.
One actual normalized NLS data set and one complex rough-open neighborhood
at every real base point precede all numerator and critical indices.

All 403 selected modules pass a full serialized strict rebuild and the
final combined transitive audit: 4720 selected declarations and 26880
imported NLS declarations. Only propext, Classical.choice and Quot.sound
occur. Exact ordered checker/audit/PASS/coverage selections, source hashes,
seven provenance records and private fresh outputs agree. All 398 earlier
selected Lean sources remain byte-identical. The combined import preflight
also passed. Canonical main remains unchanged and clean; no new shared
branch import, placeholder, axiom, heartbeat increase, disabled linter or
warning exception is introduced.

The complete critical coordinates and individual analytic residue germs
do not yet give a Hilbert residue sequence or a Mittag-Leffler numerator
representation. Those bounds, exterior remainder control, identification
with the earlier weighted normalized family, full coherent W, canonical
leading scalar one, sharp source(54), physical frequency(69), action descent,
weighted asymptotic/compact derivative claims and actual Birkhoff/PDE flows
remain open. No main theorem inventory row is closed.


## Full actual canonical numerator Hilbert representation

See `CANONICAL_NUMERATOR_REPRESENTATION.md`. Actual free-normalized product
ratios prove the critical quotient bound 8/|z| and vanishing Cauchy error.
Complete actual simple critical labels give exact Cauchy interpolation,
uniform symmetric limits and ordinary absolute sums. Actual small-circle
residue estimates yield 4/|j| tails and genuine signed l2 residues. The
bounded actual beta_j/(pi*j) multiplier gives the exact positive energy
coefficient vector a_j=A_j/(2pi*j), with no sequence membership assumed.

The shifted-square pullback and actual signed reflection give absolute
positive energy principal series. Actual quadratic critical energy growth
supplies an entire filled l2-valued critical basis. Its pairing with the
constructed coefficients equals the actual descended numerator at every
energy by analytic uniqueness, including all critical and central values.
One actual normalized NLS data set/common complex rough-open neighborhood
at every real base point precedes all indices and real inputs. The Hilbert
basis is spectrally entire for each fixed real-type input; joint Banach
analyticity of that basis or coefficient vector in the rough source is
not asserted.

All 412 selected modules pass the full serialized strict rebuild and final
combined transitive audit: 4837 selected declarations, 26997 imported
NLS declarations, only propext/Classical.choice/Quot.sound. Exact ordered
checker/audit/PASS/coverage selections, all source hashes, seven provenance
records and private fresh outputs agree. All 403 previous selected Lean
sources remain byte-identical. Combined import preflight passed. Canonical
main remains unchanged and clean. No new shared branch import, placeholder,
axiom, heartbeat increase, disabled linter or warning exception is introduced.

The canonical critical coordinates still need identification with the
earlier local rough critical labels, and actual contour normalization must
be transferred before applying the earlier period inverse. Agreement with
the weighted normalized family, full coherent W, canonical leading scalar
one, sharp source(54), physical frequency(69), action descent, weighted
asymptotic/compact derivative claims and actual Birkhoff/PDE flows remain
open. No main inventory row is closed.


## Intrinsic critical labels and compatible complex germs

See `CRITICAL_CHART_GERMS.md`. All 415 selected modules pass the serialized strict rebuild and combined transitive axiom audit: 4842 selected declarations, 27002 imported NLS declarations; permitted standard axioms only. All 412 previous selected Lean sources and seven provenance records remain unchanged. Actual critical labels agree at every real chart overlap; each positive label also has the same full complex germ. Neighborhoods may depend on the label. Old-family identification, contour normalization, physical frequency(69) and all main theorem rows remain open.


## Canonical and earlier period-data Hilbert compatibility

See `CANONICAL_CRITICAL_COMPATIBILITY.md`. Prior full strict rebuild of the unchanged 415 modules, strict incremental compilation of the two new modules in dependency order, then a fresh full combined transitive axiom audit of all 417 selected modules. Source bytes, exact selections, private fresh outputs and seven provenance records verified. No claim of a repeated full 417-module rebuild.

Audit: 4854 selected declarations; 27013 declarations including imported NLS dependencies. Only propext, Classical.choice and Quot.sound are permitted. Actual canonical free labels, real radial-path branch/germ continuation, filled scalar/Hilbert basis agreement and actual Miura numerator representation in the earlier period-data Hilbert class are proved. Original contour normalization, normalized-family identification, physical frequency(69) and all main theorem rows remain open.
