# Dissertation coverage audit

This is a focused map of the dissertation's introductory results to the
current public Lean API. It is not a completeness certificate for every
chapter or appendix. All paths below are relative to the repository root;
the introductory declarations are in `NLS.ZakharovShabat`.
The appendix audits below use `NLS.Fourier` and `NLS.ComplexAnalysis`.
Later milestone entries retain their historical validation counts and
then-current limitations. Current appendix comparisons are in
[Appendix D](coverage/APPENDIX_D.md), [Appendix E](coverage/APPENDIX_E.md),
[Appendix F](coverage/APPENDIX_F.md), [Appendix G](coverage/APPENDIX_G.md),
[Appendix H](coverage/APPENDIX_H.md), and [Appendix I](coverage/APPENDIX_I.md).
They supersede the historical appendix entries below. The focused Section 2 convergence and scalar-pairing audit is in
[`coverage/SECTION_2.md`](coverage/SECTION_2.md). The spectral overview link below and the final
dyadic-counterexample entry record the current status of Theorem 1.1.

The [reviewed numbered-heading index](coverage/NUMBERED_HEADINGS.md)
distinguishes actual statements, numbered remarks and reference-only labels.
Its counts describe source locations, not proved coverage.

| Source result | Public entry point | Scope |
| --- | --- | --- |
| Spectral overview p.17: real minimal-operator symmetry and closure | [Whole-line reality](NLS/ZakharovShabat/L2WholeLineReality.lean), [Symmetry and closure](NLS/ZakharovShabat/L2WholeLineSymmetry.lean), [audit](coverage/SPECTRAL_OVERVIEW.md) | Actual Hermitian pairing identity, inclusion in the Hilbert adjoint, closability, closed dense graph closure and compact test core. Self-adjointness, maximal-domain identification, spectrum and pure absolute continuity remain pending. |
| Spectral overview p.17: dense minimal whole-line operator | [Period L2 norm](NLS/ZakharovShabat/L2WholeLinePotentialPeriods.lean), [Local L2 estimates](NLS/ZakharovShabat/L2WholeLineLocalIntegrability.lean), [Test images](NLS/ZakharovShabat/L2WholeLineTestOperator.lean), [Dense Hilbert domain](NLS/ZakharovShabat/L2WholeLineTestDomain.lean), [Minimal physical operator](NLS/ZakharovShabat/L2WholeLineMinimalOperator.lean), [audit](coverage/SPECTRAL_OVERVIEW.md) | Actual complex-linear partial operator on Hermitian L2(R; C2), dense smooth compact domain and literal physical realization. Closure, self-adjointness, spectrum and pure absolute continuity remain pending. |
| Spectral overview p.17: full real-time propagation | [Fundamental matrix](NLS/ZakharovShabat/L2WholeLineFundamental.lean), [Bounded Floquet propagation](NLS/ZakharovShabat/L2WholeLineFloquetBound.lean), [Physical period equations](NLS/ZakharovShabat/L2WholeLineSolutionPeriods.lean), [Global physical equation](NLS/ZakharovShabat/L2WholeLineDifferentialEquation.lean), [audit](coverage/SPECTRAL_OVERVIEW.md) | Positive and negative periods, seam continuity, bounded unit-multiplier propagation and the original physical equation almost everywhere on the full real line. Whole-line operator spectrum and absolute continuity remain pending. |
| Spectral overview p.17: Floquet band prerequisite | [Unimodular quadratic](NLS/ZakharovShabat/FloquetQuadratic.lean), [Canonical band set](NLS/ZakharovShabat/SourceFloquetBandSet.lean), [Physical monodromy criterion](NLS/ZakharovShabat/L2FloquetBandCriterion.lean), [audit](coverage/SPECTRAL_OVERVIEW.md) | Exact complement-of-open-gaps criterion, with endpoints, for the discriminant and physical Hilbert monodromy. Whole-line operator spectrum and absolute continuity remain pending. |
| Introduction p.15: literal action smoothing | [Original action Fourier remainder](NLS/ZakharovShabat/SourceActionFourierRemainder.lean), [Weighted Hilbert products](NLS/SequenceSpaces/WeightedHilbertProduct.lean), [audit](coverage/SECTION_23.md) | The same original indexed actions minus squared Fourier coefficients have real analytic realizations in weighted ell1 of order 2m+1 for every positive integer Sobolev order m, with exact normalization and index reflection. |
| Theorem 0.3 and Corollary 18.2: explicit inverse neighborhoods | [Original frequency inverses](NLS/ZakharovShabat/SourceFrequencyOpenInverse.lean), [Analytic open inverses](NLS/ComplexAnalysis/AnalyticOpenInverse.lean), [audit](coverage/SECTION_18.md) | For the retained finite-p>2 frequency map, explicit open source and image neighborhoods with analytic inverse throughout, at zero and at every point of an open dense subset of its original domain. |
| Section 7: exact covering dimension | [Actual gap-count equality](NLS/ZakharovShabat/SourceHilbertExactCoveringDimension.lean), [Finite-torus dimension](NLS/FunctionalAnalysis/CircleProductCoveringDimension.lean), [audit](coverage/SECTION_7.md) | Standard numerical covering dimension equals the actual open-gap count, including infinity. The finite upper bound follows from fine periodic grid covers of multiplicity at most n+1; infinite dimension holds residually. |
| Section 7: infinite covering dimension | [Actual infinite-gap theorem](NLS/ZakharovShabat/SourceHilbertInfiniteCoveringDimension.lean), [Numerical cube lower bound](NLS/FunctionalAnalysis/CubeCoveringDimensionLower.lean), [audit](coverage/SECTION_7.md) | Every actual infinite-gap Hilbert isospectral set has no finite covering-dimension bound. The numerical cube premise is discharged using cubical Sperner, Lebesgue covering and shrinking lemmas. The subsequent periodic-grid proof establishes exact finite-torus dimension equality. |
| Section 7: standard covering-dimension foundations | [Covering dimension](NLS/FunctionalAnalysis/CoveringDimensionBasic.lean), [Actual isospectral reductions](NLS/ZakharovShabat/SourceHilbertCoveringDimensionReduction.lean), [audit](coverage/SECTION_7.md) | Finite-open-cover definition, closed-subspace monotonicity, dimension-zero obstruction and closed cubes of all finite sizes in actual infinite-gap Hilbert isospectral sets. The subsequent cubical covering theorem discharges the higher numerical cube bounds. |
| Section 7 overview, p.45: global squared-gap spectral uniqueness | [Global signed-gap injectivity and spectral uniqueness](NLS/ZakharovShabat/SymmetricSignedGapGlobalInjectivity.lean), [Finite-output properness](NLS/ZakharovShabat/SymmetricSignedGapFiniteProper.lean), [audit](coverage/SECTION_7.md) | Unconditional actual Hilbert signed-gap injectivity and equality of periodic spectra with algebraic multiplicities from equal squared gaps. Every finite-support signed-gap output has a unique symmetric Hilbert source. |
| Section 7 finite-gap trace and norm bounds | [Physical trace](NLS/ZakharovShabat/SourceFiniteGapPhysicalTrace.lean), [Pointwise and source bounds](NLS/ZakharovShabat/SourceFiniteGapPointwiseBound.lean), [audit](coverage/SECTION_7.md) | Actual finite-gap physical trace, uniform component bounds by total open-gap length, and Hilbert source norm squared at most twice its square. The subsequent global theorem proves properness over finite output spaces and global injectivity. |
| Section 7 signed-gap inverse: kernel vanishing and openness | [Actual kernel theorem](NLS/ZakharovShabat/SymmetricSignedGapKernelVanishing.lean), [Entire variation identity](NLS/ZakharovShabat/SymmetricSignedGapKernelVariation.lean), [audit](coverage/SECTION_7.md) | At every real symmetric Hilbert source the actual signed-gap derivative is bijective. The actual signed-gap map is globally open. The subsequent global theorem discharges finite-gap/global injectivity and proves squared-gap uniqueness. |
| Section 7 signed-gap inverse prerequisite: actual gradient matrix | [Actual transpose matrix](NLS/ZakharovShabat/SymmetricSignedGapGradientMatrix.lean), [Compact remainder](NLS/ZakharovShabat/SymmetricSignedGapMatrixCompact.lean), [audit](coverage/SECTION_7.md) | Exact cross-boundary matrix, collapsed diagonal two, and twice-identity-plus-compact on complex Hilbert directions. Transpose-kernel vanishing implies actual derivative bijectivity; the later interpolation step proves kernel vanishing; global injectivity is proved by the subsequent finite-output argument. |
| Section 7 signed-gap inverse prerequisite: local Dirichlet coordinates | [Dirichlet derivative](NLS/ZakharovShabat/SymmetricDirichletDerivative.lean), [Analytic local inverse](NLS/ZakharovShabat/SymmetricDirichletLocalInverse.lean), [audit](coverage/SECTION_7.md) | At every real symmetric Hilbert source the full Dirichlet derivative on symmetric complex directions is bijective, and the actual map has a two-sided analytic local inverse. No global Dirichlet inverse or signed-gap kernel vanishing asserted. |
| Section 7 overview, p.45: infinite-gap local topology | [Actual isospectral obstruction](NLS/ZakharovShabat/SourceHilbertInfiniteGapTopology.lean), [Infinite circle product](NLS/FunctionalAnalysis/InfiniteCircleProductLocalTopology.lean), [audit](coverage/SECTION_7.md) | Infinite-gap sets have no contractible neighborhoods or real normed atlas. A finite-dimensional Euclidean atlas exists exactly for finite-gap sources. A separate covering-dimension invariant remains unfinished. |
| Section 7 overview, p.45: infinitely many gaps generically | [Generic open gaps](NLS/ZakharovShabat/SourceGenericOpenGaps.lean), [Arbitrary small perturbations](NLS/ZakharovShabat/SourceGenericGapApproximation.lean), [audit](coverage/SECTION_7.md) | All gaps are open on a dense G-delta and residual set for every finite p>1. Finite-gap sources are dense but meagre. The separate infinite-dimensional topological invariant remains unfinished. |
| Section 7 signed-gap derivative: compactness and finite kernel | [Actual compact perturbation](NLS/ZakharovShabat/SymmetricSignedGapCompactDerivative.lean), [Kernel obstruction](NLS/ZakharovShabat/SymmetricSignedGapFredholm.lean), [audit](coverage/SECTION_7.md) | At every symmetric Hilbert source the derivative is 2 I plus compact and has finite-dimensional real kernel. Kernel vanishing is discharged by the later interpolation theorem; finite-gap injectivity is proved by the subsequent properness argument. |
| Section 7 squared-gap uniqueness: small Hilbert sources | [Local spectral uniqueness](NLS/ZakharovShabat/SourceSmallSquaredGapUniqueness.lean), [Local signed-gap inverse](NLS/ZakharovShabat/SymmetricSignedGapLocalInverse.lean), [audit](coverage/SECTION_7.md) | Unconditional equality of actual periodic spectra and algebraic multiplicities for two sources in one fixed small source ball with equal squared gaps. The later global theorem removes the small-source restriction. |
| Section 7 squared-gap uniqueness: explicit global reductions | [Finite-gap reduction](NLS/ZakharovShabat/SymmetricSignedGapFiniteFibers.lean), [Spectral reduction](NLS/ZakharovShabat/SourceSquaredGapUniquenessReduction.lean), [audit](coverage/SECTION_7.md) | Global openness and finite-gap injectivity in this reduction are discharged by the later theorems. Every Hilbert spectrum has a nonpositive signed-gap representative; the proved global signed-gap injectivity gives actual squared-gap spectral uniqueness. |
| Section 7 squared-gap uniqueness prerequisites: local signed-gap inverse | [Local inverse](NLS/ZakharovShabat/SymmetricSignedGapLocalInverse.lean), [Symmetric coordinates](NLS/ZakharovShabat/SymmetricSourceCoordinates.lean), [audit](coverage/SECTION_7.md) | Exact free derivative 2 I, analytic local inverse with derivative (1/2) I, and realization of all sufficiently small signed or nonnegative Hilbert gap sequences. Global injectivity is proved by the later finite-output argument. |
| Section 7 squared-gap uniqueness prerequisites: symmetric signed gaps | [Symmetric representatives](NLS/ZakharovShabat/SourceReflectionSymmetry.lean), [Actual signed gaps](NLS/ZakharovShabat/SourceSymmetricSignedGaps.lean), [audit](coverage/SECTION_7.md) | Reflection-fixed sources have opposite boundary endpoints; their analytic signed-gap sequence has the actual squared gaps. Every endpoint prescription has a unique symmetric Hilbert representative. Global Hilbert signed-gap injectivity is proved by the later finite-output argument. |
| Section 7 overview, p.45: finite-gap manifold dimension | [Actual manifold](NLS/ZakharovShabat/SourceHilbertFiniteGapManifold.lean), [Circle charts](NLS/FunctionalAnalysis/FiniteCircleProductManifold.lean), [audit](coverage/SECTION_7.md) | Hausdorff second-countable topological manifold with Euclidean model dimension equal to the number of actual open periodic gaps, including zero. |
| Section 7 overview, p.45: literal signed Dirichlet parametrization | [Signed parametrization](NLS/ZakharovShabat/SourceSignedDirichletParametrization.lean), [Actual signed sheets](NLS/ZakharovShabat/SourceDirichletRealSheetCoordinates.lean), [audit](coverage/SECTION_7.md) | Actual Hilbert eigenvalue/sign homeomorphism to the product of endpoint-glued signed gaps; every admissible literal prescription is realized uniquely, including infinitely many open gaps. |
| Section 7 overview, p.45: prescribed Hilbert Dirichlet terminals | [Sheet parametrization](NLS/ZakharovShabat/SourceDirichletSheetParametrization.lean), [Actual flow traversal](NLS/ZakharovShabat/SourceDirichletSpectralTraversal.lean), [audit](coverage/SECTION_7.md) | Every admissible full terminal prescription has one actual isospectral Hilbert realization; the actual terminal map is a homeomorphism onto the product of original algebraic sheets, without a finite-gap assumption. |
| Section 7 overview, p.45: signed Dirichlet uniqueness | [Uniqueness](NLS/ZakharovShabat/SourceSignedDirichletUniqueness.lean), [Actual signs](NLS/ZakharovShabat/SourceDirichletSignData.lean), [audit](coverage/SECTION_7.md) | Literal signed Dirichlet data injective on each actual periodic isospectral set for all finite p>1, without a finite-gap assumption; prescribed-data surjectivity and glued-circle topology remain open. |
| Section 7 overview, p.45: actual Hilbert isospectral tori | [Circle product](NLS/ZakharovShabat/SourceHilbertIsospectralTorus.lean), [Connectedness](NLS/ZakharovShabat/SourceHilbertIsospectralConnected.lean), [audit](coverage/SECTION_7.md) | Compact connected actual isospectral sets; homeomorphism to one circle per open periodic gap, including infinite products and the exact finite-gap factor count. |
| Propositions 6.1 and 6.3: corrected tails of fixed canonical sequences | [Displacement cutoffs](NLS/ZakharovShabat/SourcePeriodTwoCanonicalCutoffs.lean), [Weighted gaps](NLS/ZakharovShabat/SourceCanonicalWeightedGapTails.lean), [audit](coverage/SECTION_6.md) | Stronger full-cutoff and ceiling-half bounds in signed and positive ranges; locally small weighted gap tails and actual complete canonical gap regularity at finite p>1. |
| Page 35: complete canonical midpoint and gap sequences | [Canonical midpoint and gap](NLS/ZakharovShabat/SourcePeriodTwoCanonicalMidpointGap.lean), [audit](coverage/SECTION_6.md) | Actual central and distant pairs for arbitrary raw period-two input at finite p>1; ℓᵖ membership, corrected locally small tails, and eventual agreement with contour invariants. |
| Proposition 6.1, p.35: complete ordered period-two sequences | [Central completion](NLS/ZakharovShabat/SourcePeriodTwoCompleteLabels.lean), [ordering](NLS/ZakharovShabat/SourcePeriodTwoOrderedLabels.lean), [canonical labels](NLS/ZakharovShabat/SourcePeriodTwoCanonicalEndpoints.lean), [audit](coverage/SECTION_6.md) | Every raw period-two input at finite p>1; actual full spectrum and multiplicities, cutoff-independent canonical labels, ℓᵖ displacements and corrected locally uniform small tails. |
| Lemma 6.9, p.43: literal repeated-label positive sum | [Corrected sums](NLS/ZakharovShabat/SourceLemma6_9PositiveCorrected.lean), [literal counterexample](NLS/ZakharovShabat/SourceLemma6_9LiteralSum.lean), [audit](coverage/SECTION_6.md) | Same actual determinant data and corrected positive sums for finite p>1; actual roots refute the printed repeated-first-label budget locally uniformly at p=2. |
| Proposition 6.3, p.36: literal positive-index weighted gap sum | [Positive gap tail](NLS/ZakharovShabat/SourcePositiveGapTail.lean), [audit](coverage/SECTION_6.md) | Corrected intrinsic gap bound for n≥N at every source weight and finite p>1; actual positive gaps refute the printed locally uniform p=2 budget at unit weight, for intrinsic and counted-pair sums. |
| Proposition 6.1, p.35: literal positive-index sum | [Positive displacement tail](NLS/ZakharovShabat/SourcePositiveDisplacementTail.lean), [audit](coverage/SECTION_6.md) | Corrected original spectral bound for n≥N at finite p>1; actual positive roots refute the printed locally uniform p=2 budget. |
| Section 4, p.31: regularity loss before Lemma 4.3 | [Smooth constant reflection](NLS/ZakharovShabat/SourceReflectionRegularityLoss.lean), [audit](coverage/SECTION_4.md) | Both signs lose one derivative at every finite Banach exponent, with actual physical coefficients and completed distributions; scalar order-one membership holds exactly at infinity. |
| Appendix H, p.139: unreduced odd-Hamiltonian remainder | [Exact phase and counterexample](NLS/ZakharovShabat/SourceAppendixHRemainderPhase.lean), [audit](coverage/APPENDIX_H.md) | The unchanged H.1 remainder requires (-1)^(m+1); actual constant potential has H5=2 and integral(q4)=-2. The H.2 polynomial can absorb the phase. |
| Appendix A, p.123: printed witness at every positive period | [Explicit physical rescaling](NLS/Fourier/PrintedChirpPeriodTransport.lean), [audit](coverage/APPENDIX_A.md) | The same printed coefficients, uniform convergence with 2*pi*n/L frequencies, exact normalized interval Fourier integrals and original-space membership iff p>=2. |
| Appendix A, p.123: literal continuous witness in A.5 | [Exact displayed series](NLS/Fourier/PrintedChirpLiteralSeries.lean), [audit](coverage/APPENDIX_A.md) | Uniform convergence of ordinary cutoffs to a continuous period-two function; exact physical Fourier integrals, original-space membership iff p>=2 and the same L2 realization. |
| Appendix A, p.123: cancellation for the printed A.5 phase | [Uniform block estimates](NLS/Fourier/ChirpBlockCancellation.lean), [audit](coverage/APPENDIX_A.md) | Exact phase, every block prefix and every real physical point; squared norm at most N+12*pi*N*(1+log N). The later literal-series result proves weighted tails and uniform convergence. |
| Appendix A, p.123: printed A.5 series coefficients | [Exact threshold and L2 realization](NLS/Fourier/PrintedChirpCoefficients.lean), [audit](coverage/APPENDIX_A.md) | Literal phase, logarithmic denominator and positive-index cutoffs; lp membership iff p>=2 and actual physical L2 convergence. Its continuity is established by the later literal-series result. |
| Section 3 opening, p.23: analytic decomposition | [Physical analytic approximation](NLS/Fourier/SourceAnalyticApproximation.lean), [audit](coverage/SECTION_3.md) | Finite Fourier approximants with entire physical representatives, exact Fourier coefficients and distributions, and an arbitrarily small remainder in every original finite-exponent pair norm. |
| Section 3 opening, p.23: infinitesimal relative bound | [Original-norm bounds](NLS/ZakharovShabat/SourcePotentialRelativeBound.lean), [audit](coverage/SECTION_3.md) | Every positive relative coefficient, uniformly on bounded original potential sets, for all finite Banach exponents; both graph comparisons retain the complete original domain. |
| Appendix D, p.126: absolute convergence | [Exact convergence criterion](NLS/ComplexAnalysis/AbsoluteProductConvergence.lean), [audit](coverage/APPENDIX_D.md) | Ordered absolute convergence is equivalent to summability of perturbation norms and implies genuine complex convergence, including zero factors; ordinary convergence alone does not imply absolute convergence. |
| Appendix A, p.123: general distributional product | [Product criterion](NLS/Fourier/PeriodicDistributionConvolutionProduct.lean), [actual obstruction without growth](NLS/Fourier/PeriodicConvolutionGrowthObstruction.lean), [audit](coverage/APPENDIX_A.md) | Unique original products for convergent polynomially bounded convolutions, with separate unordered and symmetric criteria; finite-support convolutions of actual distributions show that growth cannot be omitted. |
| Theorem 23.4 proof, p.119: weighted tail corrections | [Actual-source counterexamples](NLS/ZakharovShabat/SourceSection28TailCounterexample.lean), [corrected tail](NLS/ZakharovShabat/SourceSection28TailEstimate.lean), [audit](coverage/SECTION_28.md) | The omitted cutoff boundary and missing 1+ factor fail independently at a real source in every retained domain. Corrected inclusive tails and their Fourier-tail budget are proved; final theorem constants are unchanged. |
| Section 25 opening, p.107: L2 localization obstruction | [Exact spectrum translation](NLS/ZakharovShabat/SourcePlaneWaveSpectrum.lean), [physical L2 obstruction](NLS/ZakharovShabat/SourceL2LocalizationObstruction.lean), [audit](coverage/SECTION_25.md) | Every positive physical L2 ball has a positive disc radius with no uniform spectral-tail cutoff; actual real sources of fixed norm supply the witnesses. |
| Section 23, pp.103-105: corrected Abel strip | [Original physical source](NLS/ZakharovShabat/SourceAbelStripCharacterization.lean), [physical Sobolev traces](NLS/Fourier/PhysicalSobolevStripTraces.lean), [audit](coverage/SECTION_23.md) | For s>=0 and a>0, original Abel membership iff the actual source has periodic holomorphic extensions to half-width a/pi with Sobolev norm traces. The printed narrower forward assertion is also proved. |
| Section 23, pp.103-105: Abel-strip characterization | [Original-source counterexample](NLS/ZakharovShabat/SourceAbelStripCounterexample.lean), [audit](coverage/SECTION_23.md) | A concrete original Hilbert source has holomorphic continuation and smooth L2 traces on the printed strip, but is outside the original Abel-weight image. The corrected-width equivalence uses Sobolev norm traces; the narrower forward implication is proved. |
| Section 23, pp.104-105: explicit weights and hierarchy | [Abel and Gevrey constructors](NLS/SequenceSpaces/ExponentialSpectralWeights.lean), [full hierarchy](NLS/SequenceSpaces/SpectralWeightHierarchy.lean), [audit](coverage/SECTION_23.md) | Exact M/M1 examples, original weighted estimates, vanishing full weight ratios and coefficient-preserving continuous inclusions. The corrected-strip characterization is proved in the subsequent follow-up. |
| Corollary 22.2(iii), pp.100-101: infinity-target extension | [Original family](NLS/ZakharovShabat/SourceSection22NonextensionAll.lean), [physical gauge proof](NLS/ZakharovShabat/SmoothSourceGaugeObstruction.lean), [audit](coverage/SECTION_22.md) | All-smooth physical nonextension at every original non-Hilbert source, for every target q>=1 including infinity, on forward and symmetric compact time intervals. |
| Lemma 21.2 proof, printed p.97: cube-shift constant | [Corrected primitive cube](NLS/ZakharovShabat/SourceSection21CubeShiftCorrection.lean), [audit](coverage/SECTION_21.md) | The constant is i*(pi*n)^3. The actual zero source refutes the printed expansion at every nonzero signed index; the corrected contour formula remains proved. |
| Section 20, printed pp.93 and95: infinity target and copied cube coefficient | [All frequency targets](NLS/ZakharovShabat/SourceSection20FrequencyTop.lean), [cube correction](NLS/ZakharovShabat/SourceSection20CubeConstantCorrection.lean), [audit](coverage/SECTION_20.md) | The same original complex domain supports l-infinity analyticity. An actual real finite-gap source refutes the p.93 constant coefficient; the original frequency identity remains proved. |
| Proposition 17.3 proof, printed pp.79–80: power constant and cutoff | [Full summed bound](NLS/ZakharovShabat/SourceActionPowerSum.lean), [enumeration cutoff](NLS/ZakharovShabat/Section17EnumerationCutoff.lean), [audit](coverage/SECTION_17.md) | Factor two and 2N+1 positions correct the printed estimates; actual original-source counterexamples and the retained 4 epsilon budget are proved. |
| Section 16 proof, printed p.76: uniform auxiliary estimates | [Full lp asymptotic](NLS/ZakharovShabat/SourceAuxiliaryUniformAsymptotics.lean), [physical gradient bound](NLS/ZakharovShabat/SourceAuxiliaryUniformGradient.lean), [audit](coverage/SECTION_16.md) | Banach analytic full lp error and simultaneous local bounds for all actual cotangents and physical conjugate gradients on unchanged original complex W, at every finite p>1. |
| Section 15, printed p.74: actual collapsed-limit counterexample | [Triangular source witnesses](NLS/ZakharovShabat/SourceTriangularCollapsedWitness.lean), [original phase limits](NLS/ZakharovShabat/SourceCollapsedOriginalEtaWitness.lean), [audit](coverage/SECTION_15.md), [erratum](SOURCE_ERRATA.md) | Every original neighborhood of zero contains a collapsed-gap witness in F_0. An actual open-gap sequence has both signed limits, exactly one zero. |
| Section 15, printed p.74: gap and eta discontinuity | [Original gap and eta phase](NLS/ZakharovShabat/SourceOriginalGapEtaDiscontinuity.lean), [audit](coverage/SECTION_15.md) | Both have continuity failures within the original open-gap domain, arbitrarily close to zero, for every finite p>1. |
| Lemma 11.1 proof, printed p.61: integrand strictness correction | [Interior zero](NLS/ZakharovShabat/SourceActionIntegrandCriticalZero.lean), [audit](coverage/SECTION_11.md), [erratum](SOURCE_ERRATA.md) | The literal integrand vanishes at the interior critical point with positive denominator; strict positivity of the action remains proved. |
| Section 10, printed p.55: individual endpoint discontinuity | [Domain discontinuity](NLS/ZakharovShabat/SourceAlmostRealLabelDiscontinuity.lean), [audit](coverage/SECTION_10.md) | Both central labels fail continuity within every source neighborhood of zero; the unchanged Lemma 10.2 domain retains all properties. |
| Section 8, printed p.49: complex label discontinuity | [Constant spectrum](NLS/ZakharovShabat/ConstantPeriodicSpectrum.lean), [original source](NLS/ZakharovShabat/SourceConstantPeriodicSpectrum.lean), [canonical pair](NLS/ZakharovShabat/SourceConstantCentralPair.lean), [discontinuity](NLS/ZakharovShabat/SourcePeriodicLabelDiscontinuity.lean), [audit](coverage/SECTION_8.md) | For every finite p>1, both actual central labels fail to be continuous at constant complex sources in every original-source neighborhood of zero. |
| Section 7 overview, printed p.46: two source corrections | [Closed-gap geometry](NLS/ZakharovShabat/PhysicalClosedGapGeometry.lean), [exact tangents](NLS/ZakharovShabat/PhysicalClosedGapTangents.lean), [psi normalization](NLS/ZakharovShabat/SourceSection7PsiNormalization.lean), [audit](coverage/SECTION_7.md) | The actual real collapsed-gap locus has codimension two. The literal fixed-denominator psi product diverges at the free source; mode-dependent normalization gives the exact finite value. |
| Sharper corrected Section 6 cutoffs | [Original spectral estimates](NLS/ZakharovShabat/SourceCeilingCutoffEstimates.lean), [original coefficient estimates](NLS/ZakharovShabat/SourceCoefficientCeilingCutoffs.lean), [audit](coverage/SECTION_6.md) | Propositions 6.1/6.3 and Lemmas 6.8/6.9 retain full-cutoff and ceiling-half corrected bounds in the original norms, with actual spectral/supremum data and one neighborhood for all later cutoffs. Printed false budgets remain refuted. |
| Exact native real one-smoothing | [`SourceBirkhoffNativeRealRemainders.lean`](NLS/ZakharovShabat/SourceBirkhoffNativeRealRemainders.lean), [`SourceSobolevNativeProjection.lean`](NLS/ZakharovShabat/SourceSobolevNativeProjection.lean) | Both stronger remainders have the original real codomains, component-sum norms, and literal forward/inverse coefficients. They are analytic and uniformly bounded on every native ball at every positive integer order. |
| One-smoothing for the retained Section 23 family | [`SourceSection23OneSmoothing.lean`](NLS/ZakharovShabat/SourceSection23OneSmoothing.lean) | Any retained Section 23 family acquires both exact real one-smoothing results without rechoosing its map, roots, atlas, domains, actions, or solution theory. One original family satisfies all orders simultaneously. |
| Canonical bounded forward and inverse one-smoothing | [`SourceBirkhoffInverseFourierSobolevBall.lean`](NLS/ZakharovShabat/SourceBirkhoffInverseFourierSobolevBall.lean), [`SourceBirkhoffInverseFourierAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffInverseFourierAnalytic.lean) | One constructed family has real analytic Fourier remainders gaining one derivative in both directions, uniformly bounded on all native real Sobolev balls for every integer m >= 1. The inverse uses the actual global Sobolev bijection and exact original Fourier normalization. |
| Canonical forward remainder and native source conversion | [`SourceBirkhoffFourierRemainder.lean`](NLS/ZakharovShabat/SourceBirkhoffFourierRemainder.lean), [`SourceSobolevNativeBridge.lean`](NLS/ZakharovShabat/SourceSobolevNativeBridge.lean) | The fixed h^(m+1) map has literal coordinates and a complex analytic germ at every real Hm point. A contractive conversion preserves raw coefficients and the real source condition, giving real analyticity on the whole native source space. |
| Bounded positive-integer Fourier one-smoothing | [`SourceBirkhoffFourierSobolevBall.lean`](NLS/ZakharovShabat/SourceBirkhoffFourierSobolevBall.lean) | The actual rectangular Birkhoff-minus-Fourier error has a common h^(m+1) bound on every real original Hm ball, integer m >= 1, for the same retained map as the local analytic result. |
| Complete uniform spectral Fourier errors | [`SourceEtaMidpointFourierSobolevBall.lean`](NLS/ZakharovShabat/SourceEtaMidpointFourierSobolevBall.lean), [`SourceEtaSineFourierSobolevBall.lean`](NLS/ZakharovShabat/SourceEtaSineFourierSobolevBall.lean) | The entire literal midpoint and terminal-sine errors are uniformly bounded in h^(s+1) on real Hs balls, including central indices and collapsed gaps, without smooth representatives. |
| Uniform spectral estimates on real Sobolev balls | [`SourceSpectralDisplacementSobolevBall.lean`](NLS/ZakharovShabat/SourceSpectralDisplacementSobolevBall.lean), [`SourceEtaMidpointFourierSobolevBallSmooth.lean`](NLS/ZakharovShabat/SourceEtaMidpointFourierSobolevBallSmooth.lean) | Common all-index displacement bounds, phase estimates and a literal midpoint Fourier H^(s+1) tail bound over every real Hs ball, integer s >= 1; matching smooth representatives remain explicit in the Fourier-tail conclusion. |
| Uniform complete critical-midpoint correction | [`SourceCriticalMidpointSobolevBall.lean`](NLS/ZakharovShabat/SourceCriticalMidpointSobolevBall.lean) | The actual correction is bounded in H^(2s) on every real Hs ball, including central and collapsed gaps, with explicit native-to-physical norm comparison. |
| Positive-integer Fourier one-smoothing | [`SourceBirkhoffHmFourierAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffHmFourierAnalytic.lean) | The actual rectangular Birkhoff-minus-Fourier coordinates have an analytic h^(m+1) realization near each real original Hm source, for every integer m >= 1, with one constructed map and root family. |
| Complete analytic midpoint Fourier error | [`SourceEtaMidpointFourierAnalytic.lean`](NLS/ZakharovShabat/SourceEtaMidpointFourierAnalytic.lean) | The literal midpoint error is analytic and locally bounded in h^(m+1), including the finite head and collapsed gaps, without smooth representatives. |
| Actual boundary phase Fourier tail | [`SobolevBoundaryPhaseFourierTail.lean`](NLS/ZakharovShabat/SobolevBoundaryPhaseFourierTail.lean), [`SourceBoundaryPhaseSmoothTail.lean`](NLS/ZakharovShabat/SourceBoundaryPhaseSmoothTail.lean) | The next phase offset has the signed original Fourier half-sum with an H^(s+1) tail on original Hs balls and at canonical source roots; smooth representatives remain explicit. |
| Weighted inverse-sine and phase-difference remainders | [`SobolevSinhFourierRemainder.lean`](NLS/SequenceSpaces/SobolevSinhFourierRemainder.lean), [`SobolevPhaseDifferenceRemainder.lean`](NLS/SequenceSpaces/SobolevPhaseDifferenceRemainder.lean) | Small inverse-index phase errors gain one Sobolev order at every Banach exponent, with explicit norm bounds. |
| Next Hamiltonian phase at actual separated roots | [`SobolevWKBBoundaryNextPhaseTail.lean`](NLS/ZakharovShabat/SobolevWKBBoundaryNextPhaseTail.lean) | The hyperbolic sine phase minus its normalized exact leading integrals has an H^(s+1) tail, uniformly for both boundary signs, bounded displacements, and every larger cutoff; smooth representatives remain explicit. |
| Nearby spectral phase comparison | [`SobolevNextPhaseDifference.lean`](NLS/ZakharovShabat/SobolevNextPhaseDifference.lean) | The nonlinear next-phase difference has an inverse-index Lipschitz bound on distant unit discs, uniformly on original Hs balls. |
| Complete analytic terminal-sine Fourier error | [`SourceEtaSineFourierAnalytic.lean`](NLS/ZakharovShabat/SourceEtaSineFourierAnalytic.lean) | The literal `sourceEtaSineFourierError` is analytic and locally bounded in h^(s+1) near every real original Hs source, integer s >= 1; all indices and collapsed gaps are included. |
| Complex omitted-product inverse normalization | [`SourceOmittedBoundaryDecay.lean`](NLS/ZakharovShabat/SourceOmittedBoundaryDecay.lean), [`SourceOmittedBoundaryInverseAnalytic.lean`](NLS/ZakharovShabat/SourceOmittedBoundaryInverseAnalytic.lean) | A connected source neighborhood preserves the real normalization sign. The entire inverse error is analytic in the order-one weighted supremum space for either boundary condition. |
| Analytic critical-phase tail on the original Hs source | [`SourceCriticalPhaseAnalyticTail.lean`](NLS/ZakharovShabat/SourceCriticalPhaseAnalyticTail.lean) | Near every real source, the actual next-phase offset at canonical critical points is analytic and bounded in H^(s+1) on a common tail for integer s >= 1. Central coordinates are zeroed; no smooth representative is assumed. |
| Spectral derivative and critical equation | [`SobolevWKBNextTraceDerivativeTail.lean`](NLS/ZakharovShabat/SobolevWKBNextTraceDerivativeTail.lean), [`SobolevWKBCriticalPhaseTail.lean`](NLS/ZakharovShabat/SobolevWKBCriticalPhaseTail.lean) | Fixed-radius Cauchy bounds retain the H^(s+1) error, then the actual critical equation controls the phase offset on original Sobolev balls. |
| Trace tails for bounded displacements | [`SobolevWKBNextTraceTail.lean`](NLS/ZakharovShabat/SobolevWKBNextTraceTail.lean) | The stronger `_of_bounded_displacement` theorem removes the inverse-index hypothesis, retains original Hs balls and all larger cutoffs, and permits fixed-radius spectral circles. Smooth representatives remain explicit. |
| Bounded frequency geometry and leading trace terms | [`WKBBoundedFrequencyCutoff.lean`](NLS/ZakharovShabat/WKBBoundedFrequencyCutoff.lean), [`SobolevWKBTraceLeadingTails.lean`](NLS/ZakharovShabat/SobolevWKBTraceLeadingTails.lean) | A common linear frequency lower bound and direct L2 sampling give the sharp tail under a supremum displacement bound alone. |
| Actual next-phase trace tail | [`SobolevWKBNextTraceTail.lean`](NLS/ZakharovShabat/SobolevWKBNextTraceTail.lean) | The actual discriminant minus 2*cos(i*sigma_(s+1)) has a uniform H^(s+1) tail on original Hs balls, with bounded inverse-index displacements and matching smooth representatives. |
| Uniform phase Taylor remainder | [`SobolevHamiltonianPhaseTaylor.lean`](NLS/ZakharovShabat/SobolevHamiltonianPhaseTaylor.lean), [`SobolevHamiltonianTraceTaylor.lean`](NLS/ZakharovShabat/SobolevHamiltonianTraceTaylor.lean) | The carrier and signed trace increments have order-(N+2) errors through the top density N=s. |
| Exact next-phase trace decomposition | [`NLSWKBNextTraceIdentity.lean`](NLS/ZakharovShabat/NLSWKBNextTraceIdentity.lean), [`SobolevWKBNextTraceCorrectionTail.lean`](NLS/ZakharovShabat/SobolevWKBNextTraceCorrectionTail.lean) | Corrected diagonal and small-factor leading terms give the exact trace error; the remaining scalar correction is an H^(N+1) tail. |
| Both corrected diagonal WKB tails | [`SobolevWKBBothCorrectedDiagonalTails.lean`](NLS/ZakharovShabat/SobolevWKBBothCorrectedDiagonalTails.lean) | Removing the explicit phase primitives gives common H^(N+1) tail bounds for both full diagonal remainders on original Hs balls, for 1 <= N <= s and every larger cutoff. |
| Next Hamiltonian phase increment | [`NLSHamiltonianPhaseIncrement.lean`](NLS/ZakharovShabat/NLSHamiltonianPhaseIncrement.lean), [`SobolevHamiltonianPhaseIncrement.lean`](NLS/ZakharovShabat/SobolevHamiltonianPhaseIncrement.lean) | The endpoint primitives equal the signed free carriers times the exact next phase increment, with a uniform order-(N+1) bound through N=s. |
| Diagonal response and oscillatory sampling | [`ClassicalDiagonalApproximation.lean`](NLS/ZakharovShabat/ClassicalDiagonalApproximation.lean), [`DiagonalOscillatorySampling.lean`](NLS/Fourier/DiagonalOscillatorySampling.lean) | Integration by parts gives an extra inverse power using the potential derivative L1 norm; the remaining boundary and nested integrals admit bounded l2 samples. |
| Analytic critical-midpoint correction | [`SourceCriticalMidpointSobolevAnalytic.lean`](NLS/ZakharovShabat/SourceCriticalMidpointSobolevAnalytic.lean), [`SourceCriticalMidpointHigherSobolev.lean`](NLS/ZakharovShabat/SourceCriticalMidpointHigherSobolev.lean) | The actual complete offset is locally analytic into every H^k with k <= 2s near real original Hs sources; positive s gives the required H^(s+1) correction. |
| Exact diagonal phase identities | [`NLSWKBTraceErrorDecomposition.lean`](NLS/ZakharovShabat/NLSWKBTraceErrorDecomposition.lean), [`NLSWKBLeadingDiagonalIdentity.lean`](NLS/ZakharovShabat/NLSWKBLeadingDiagonalIdentity.lean) | The actual trace error and leading forced diagonal primitive are identified exactly; the critical-phase estimate still remains. |
| Nested oscillatory sampling | [`NestedIntervalFourierSampling.lean`](NLS/Fourier/NestedIntervalFourierSampling.lean), [`WeightedCoordinateIntegral.lean`](NLS/SequenceSpaces/WeightedCoordinateIntegral.lean) | Bounded complex lattice displacements admit uniform nested l2 sampling using the inner L2 and outer L1 norms. |
| Complete boundary anti-discriminant Fourier error | [`SourceBoundaryAntiFourierAnalytic.lean`](NLS/ZakharovShabat/SourceBoundaryAntiFourierAnalytic.lean) | The actual signed Fourier error at canonical roots is analytic into H^(s+1), including the central block, on a common complex neighborhood of all real Hs sources for both boundary conditions. |
| Nonsmooth source extension | [`SourceBoundaryAntiSobolevTail.lean`](NLS/ZakharovShabat/SourceBoundaryAntiSobolevTail.lean), [`DenseWeightedCoordinateBound.lean`](NLS/SequenceSpaces/DenseWeightedCoordinateBound.lean) | The uniform weighted tail extends from finite Fourier potentials to every original Hs source by continuous coordinates and bounded coefficientwise limits. |
| Actual boundary Fourier identification | [`SobolevBoundaryAntiFourierTail.lean`](NLS/ZakharovShabat/SobolevBoundaryAntiFourierTail.lean) | Exact boundary phase elimination identifies both original signed Fourier terms, with a one-order smoother tail for matching smooth representatives. |
| Full off-diagonal WKB tails | [`SobolevWKBFirstOffDiagonalTail.lean`](NLS/ZakharovShabat/SobolevWKBFirstOffDiagonalTail.lean), [`SobolevWKBBothOffDiagonalTails.lean`](NLS/ZakharovShabat/SobolevWKBBothOffDiagonalTails.lean) | Both entire off-diagonal remainders have a common H^(N+1) tail bound for 1 <= N <= s on original Hs balls, retaining matching smooth representatives. |
| Next forcing density and actual response | [`SobolevWKBNextForcingL2.lean`](NLS/ZakharovShabat/SobolevWKBNextForcingL2.lean), [`SobolevWKBNextOscillatoryComparison.lean`](NLS/ZakharovShabat/SobolevWKBNextOscillatoryComparison.lean) | The next density has a uniform physical L2 bound. Retaining its free response and the actual leading response leaves an order-(N+2) vector error. |
| Sharp leading lower-response tail | [`ClassicalLowerKernelExpansion.lean`](NLS/ZakharovShabat/ClassicalLowerKernelExpansion.lean), [`SobolevWKBLeadingLowerFourierTail.lean`](NLS/ZakharovShabat/SobolevWKBLeadingLowerFourierTail.lean) | The actual leading lower response minus its free leading integral has an H^(N+1) tail through N=s, uniformly on original Hs balls and the physical period. |
| Next-order full WKB forcing | [`NLSRiccatiResidualNextOrder.lean`](NLS/ZakharovShabat/NLSRiccatiResidualNextOrder.lean), [`SobolevWKBNextForcingExpansion.lean`](NLS/ZakharovShabat/SobolevWKBNextForcingExpansion.lean) | The explicit next oscillatory density leaves an L1 forcing error of order N+2 for 1 <= N <= s. These estimates supply the full off-diagonal response bounds. |
| Arbitrary interval L2 sampling | [`MemLpBoundedLatticeFourier.lean`](NLS/Fourier/MemLpBoundedLatticeFourier.lean), [`PartialIntervalOscillatorySampling.lean`](NLS/Fourier/PartialIntervalOscillatorySampling.lean) | Actual bounded complex lattice samples have an L2 realization for nonsmooth interval densities, uniformly over partial intervals, including the free propagator. |
| First diagonal mass correction and exact forcing kernel | [`SobolevClassicalDiagonalExpansion.lean`](NLS/ZakharovShabat/SobolevClassicalDiagonalExpansion.lean), [`ClassicalScalarForcingLowerKernel.lean`](NLS/ZakharovShabat/ClassicalScalarForcingLowerKernel.lean) | Both actual diagonal entries have explicit first-order mass corrections and O(w^2) errors on original Hs balls. The actual lower scalar response equals its propagator integral; sharp sampled off-diagonal errors remain. |
| Both leading Fourier coefficients | [`SobolevWKBBothLeadingFourierTails.lean`](NLS/ZakharovShabat/SobolevWKBBothLeadingFourierTails.lean), [`SourceWKBBothLeadingFourierTails.lean`](NLS/ZakharovShabat/SourceWKBBothLeadingFourierTails.lean) | Both leading integrals have exact signed b_n and a_(-n) coefficients with one common H^(s+1) tail bound, including the actual boundary and critical sequences near real sources. |
| Actual anti-discriminant remainder decomposition | [`NLSWKBAntiErrorDecomposition.lean`](NLS/ZakharovShabat/NLSWKBAntiErrorDecomposition.lean), [`SobolevWKBDiagonalFourierTail.lean`](NLS/ZakharovShabat/SobolevWKBDiagonalFourierTail.lean) | The exact identity retains small initial-coordinate factors on the diagonal remainders; their contribution already has an H^(s+1) tail. The sampled off-diagonal remainders still require sharp estimates. |
| Exact reflected Hamiltonian phase | [`NLSHamiltonianReflection.lean`](NLS/ZakharovShabat/NLSHamiltonianReflection.lean), [`SobolevHamiltonianReflection.lean`](NLS/ZakharovShabat/SobolevHamiltonianReflection.lean), [`NLSWKBBoundaryPhaseElimination.lean`](NLS/ZakharovShabat/NLSWKBBoundaryPhaseElimination.lean) | Actual discriminant symmetry determines Hamiltonian parity. The Sobolev identity includes nonsmooth sources; exact endpoint algebra eliminates the phase from the separated and anti-discriminant models. |
| Nonlinear Riccati smoothing | [`SobolevRiccatiSmoothingRemainder.lean`](NLS/ZakharovShabat/SobolevRiccatiSmoothingRemainder.lean), [`SobolevRiccatiLeadingSampling.lean`](NLS/ZakharovShabat/SobolevRiccatiLeadingSampling.lean) | Removing the original leading Fourier derivative leaves an analytic H^(s-N+1) remainder, uniformly on original Hs balls, and an H1 sampling error under inverse-index displacement budgets. |
| Sharp leading WKB integral | [`SobolevWKBLeadingFourierTail.lean`](NLS/ZakharovShabat/SobolevWKBLeadingFourierTail.lean), [`SourceWKBLeadingFourierTails.lean`](NLS/ZakharovShabat/SourceWKBLeadingFourierTails.lean) | At N=s the explicit leading integral differs from i exp(i*pi*n) b_n by an H^(s+1) tail, including canonical boundary and critical sequences near real Hs sources. Smooth matching representatives remain explicit; this does not yet estimate the full WKB remainder. |
| Weighted Fourier sampling errors | [`BoundedLatticeFourierL2.lean`](NLS/Fourier/BoundedLatticeFourierL2.lean), [`BoundedLatticeFourierDifference.lean`](NLS/Fourier/BoundedLatticeFourierDifference.lean), [`WeightedLatticeFourierDifference.lean`](NLS/Fourier/WeightedLatticeFourierDifference.lean) | Actual samples have exponential L2 bounds for every bounded complex displacement. The removable divided difference transfers any weighted supremum displacement bound to a weighted L2 error bound. |
| Riccati sampling at canonical boundary and critical roots | [`SourceRiccatiBoundarySamplingError.lean`](NLS/ZakharovShabat/SourceRiccatiBoundarySamplingError.lean), [`SourceRiccatiCriticalSamplingError.lean`](NLS/ZakharovShabat/SourceRiccatiCriticalSamplingError.lean) | On complex Hs neighborhoods near real sources, s >= 1, the actual sampled density minus its original Fourier coefficients gains one weighted L2 derivative through N=s. Physical-density statements retain matching smooth periodic representatives. |
| Actual WKB characteristic and root estimates | [`SourceSobolevWKBCharacteristicModels.lean`](NLS/ZakharovShabat/SourceSobolevWKBCharacteristicModels.lean), [`SourceSobolevWKBBoundaryRoots.lean`](NLS/ZakharovShabat/SourceSobolevWKBBoundaryRoots.lean) | Original source functions have order-(N+1) model errors on Hs balls and strips. Both actual boundary root sequences satisfy local pointwise tail bounds; this does not assert weighted L2 remainders. |
| Fourier moment-series bound | [`UnitIntervalFourierMoments.lean`](NLS/Fourier/UnitIntervalFourierMoments.lean), [`BoundedLatticeMomentSeries.lean`](NLS/Fourier/BoundedLatticeMomentSeries.lean) | Unit-interval moments contract the actual Fourier L2 norm. Their bounded-displacement Taylor series converges in L2 with exponential norm bound; the actual integral identification and weighted error estimates are proved in the sampling modules above. |
| Both standard WKB columns | [`ClassicalSwapSymmetry.lean`](NLS/ZakharovShabat/ClassicalSwapSymmetry.lean), [`SobolevWKBFundamentalColumns.lean`](NLS/ZakharovShabat/SobolevWKBFundamentalColumns.lean) | Exact signed-swap covariance and initial-basis normalization give both actual columns order-(N+1) error, uniform on Hs balls and strips for s >= 1 and N <= s. Smooth periodic representatives remain explicit. |
| Both periodic endpoint samples | [`SourceRiccatiPeriodicSampling.lean`](NLS/ZakharovShabat/SourceRiccatiPeriodicSampling.lean) | Actual top-density samples at both canonical periodic endpoints are locally L2-bounded near every complex Hs source, including N=s and H0. No continuous ordering of endpoint labels is assumed. |
| Leading WKB Fourier term | [`SobolevWKBLeadingOscillatoryComparison.lean`](NLS/ZakharovShabat/SobolevWKBLeadingOscillatoryComparison.lean), [`SobolevWKBLatticeLeading.lean`](NLS/ZakharovShabat/SobolevWKBLatticeLeading.lean) | The actual oscillatory top-density term leaves a uniform order-(N+1) remainder for N <= s, s >= 1. Exact signed lattice coefficients; smooth periodic representatives remain explicit. |
| Actual spectral sampling | [`PerturbedLatticeFourierL2.lean`](NLS/Fourier/PerturbedLatticeFourierL2.lean), [`SourceRiccatiBoundarySampling.lean`](NLS/ZakharovShabat/SourceRiccatiBoundarySampling.lean), [`SourceRiccatiCriticalSampling.lean`](NLS/ZakharovShabat/SourceRiccatiCriticalSampling.lean) | Square-summable shifts preserve actual continuous-density Fourier samples. Canonical boundary and critical-point samples are locally L2-bounded near real Hs sources, including N=s and H0. |
| Nonsmooth discriminant asymptotics | [`SourceSobolevDiscriminantUniform.lean`](NLS/ZakharovShabat/SourceSobolevDiscriminantUniform.lean), [`SobolevDiscriminantDerivativeUniform.lean`](NLS/ZakharovShabat/SobolevDiscriminantDerivativeUniform.lean) | Actual canonical discriminant and the spectral derivative of its Hamiltonian approximation error have order-N strip bounds on all complex Hs balls, including nonsmooth sources. No extra source derivative. |
| Uniform Sobolev WKB strip estimates | [`SobolevWKBUniformComparison.lean`](NLS/ZakharovShabat/SobolevWKBUniformComparison.lean), [`SobolevWKBUniformEndpoint.lean`](NLS/ZakharovShabat/SobolevWKBUniformEndpoint.lean), [`SobolevDiscriminantUniformAsymptotics.lean`](NLS/ZakharovShabat/SobolevDiscriminantUniformAsymptotics.lean) | Actual solution, endpoint, and discriminant errors C/(2‖z‖)^N, uniform on original Hs balls and horizontal complex strips for N <= s, s >= 1. Smooth periodic representatives and exact source coefficients remain explicit. |
| Integral residual and leading coefficient | [`ClassicalIntegralResidualStability.lean`](NLS/ZakharovShabat/ClassicalIntegralResidualStability.lean), [`SobolevRiccatiResidualIntegralUniform.lean`](NLS/ZakharovShabat/SobolevRiccatiResidualIntegralUniform.lean), [`NLSRiccatiLeadingResidual.lean`](NLS/ZakharovShabat/NLSRiccatiLeadingResidual.lean) | The highest residual derivative is controlled in L2/L1; removing the exact leading Riccati density raises residual divisibility by one order. Sharp sampled Fourier estimates remain open. |
| Fixed smooth potential on complex strips | [`NLSHamiltonianDiscriminantStripAsymptotics.lean`](NLS/ZakharovShabat/NLSHamiltonianDiscriminantStripAsymptotics.lean) | All truncation orders for each smooth periodic complex potential; constants here may depend on the fixed potential. |
| Complex higher-order angular analyticity | [`SourceBirkhoffHmComplexSpectralTerminal.lean`](NLS/ZakharovShabat/SourceBirkhoffHmComplexSpectralTerminal.lean), [`SourceBirkhoffHmComplexSpectralTerminalAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffHmComplexSpectralTerminalAnalytic.lean), [`WeightedAnalyticRealization.lean`](NLS/SequenceSpaces/WeightedAnalyticRealization.lean) | Every integer m >= 1: actual signed errors are locally bounded and analytic in h^(m+1) on the original complex Hm source near every real point. Same original family, both signs and exact coefficients. |
| Analytic higher-order Fourier reduction | [`SourceBirkhoffHmComplexFourierErrorReduction.lean`](NLS/ZakharovShabat/SourceBirkhoffHmComplexFourierErrorReduction.lean) | Analytic h^(m+1) realizations of the two literal spectral errors imply an analytic realization of the actual Fourier remainder. The required realizations are now proved by the complete analytic midpoint and terminal-sine results above; the retained Section 23 family has full positive-integer one-smoothing. |
| Complex native weighted eta and spectral terms | [`SourceWeightedEtaComplexAnalytic.lean`](NLS/ZakharovShabat/SourceWeightedEtaComplexAnalytic.lean), [`SourceWeightedSpectralTermsComplex.lean`](NLS/ZakharovShabat/SourceWeightedSpectralTermsComplex.lean), [`SourceWeightedEtaRemainderAnalytic.lean`](NLS/ZakharovShabat/SourceWeightedEtaRemainderAnalytic.lean) | Actual eta and its remainder are analytic in every native spectral weight, locally near finite-p real sources with p>1. Both terminal spectral terms have bounded weighted realizations. |
| Complex normalization and phase decay | [`SourceBetaComplexSobolevDecay.lean`](NLS/ZakharovShabat/SourceBetaComplexSobolevDecay.lean), [`SourceNormalizedActionComplexSobolevDecay.lean`](NLS/ZakharovShabat/SourceNormalizedActionComplexSobolevDecay.lean), [`SourceNormalizationComplexPhaseSmoothing.lean`](NLS/ZakharovShabat/SourceNormalizationComplexPhaseSmoothing.lean) | Actual beta, normalized-action, and root errors have inverse-bracket decay on complex normalized first-order Sobolev neighborhoods. Exact normalization-and-phase multipliers gain one derivative on every Banach sequence scale. |
| Complex angular error analytic in h2 | [`SourceBirkhoffComplexSpectralTerminal.lean`](NLS/ZakharovShabat/SourceBirkhoffComplexSpectralTerminal.lean), [`SourceBirkhoffComplexSpectralTerminalAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffComplexSpectralTerminalAnalytic.lean) | Both actual signed Birkhoff-minus-terminal errors are locally bounded and analytic in h2, with exact unweighted coefficients and collapsed complex gaps. The normalized source weight is 1+\|2n\|. Full positive-integer Fourier one-smoothing is proved by the canonical real remainders above. |
| Higher-order angular smoothing | [`SourceHmGapBounds.lean`](NLS/ZakharovShabat/SourceHmGapBounds.lean), [`SourceGapWeightedEtaHmSequence.lean`](NLS/ZakharovShabat/SourceGapWeightedEtaHmSequence.lean), [`SourceBirkhoffHmSpectralTerminal.lean`](NLS/ZakharovShabat/SourceBirkhoffHmSpectralTerminal.lean) | For every integer m >= 1, the actual signed Birkhoff-minus-terminal error lies in h^(m+1), uniformly on physical Hm balls. Exact physical norm, same original family, both signs and collapsed gaps. |
| Higher-order Fourier-error reduction | [`SourceBirkhoffHmFourierErrorReduction.lean`](NLS/ZakharovShabat/SourceBirkhoffHmFourierErrorReduction.lean) | The two literal spectral errors in h^(m+1) imply the actual rectangular Fourier remainder belongs there. Their sharp bounds and stronger-target analyticity are supplied by the complete spectral-error results above. |
| Actual eta and angular h2 error | [`SourceGapWeightedEtaH1Sequence.lean`](NLS/ZakharovShabat/SourceGapWeightedEtaH1Sequence.lean), [`SourceBirkhoffH1EtaDifference.lean`](NLS/ZakharovShabat/SourceBirkhoffH1EtaDifference.lean), [`SourceBirkhoffSpectralTerminal.lean`](NLS/ZakharovShabat/SourceBirkhoffSpectralTerminal.lean) | Actual signed eta has gap norm and belongs to h1; both Birkhoff-minus-eta and Birkhoff-minus-literal-terminal belong to h2 uniformly on physical H1 balls. Same original family, collapsed gaps included. |
| Eta remainder and exact phase smoothing | [`SourceEtaRemainderLocalGapBound.lean`](NLS/ZakharovShabat/SourceEtaRemainderLocalGapBound.lean), [`SourceEtaRemainderH1Decay.lean`](NLS/ZakharovShabat/SourceEtaRemainderH1Decay.lean), [`SourceEtaRemainderPhaseSmoothing.lean`](NLS/ZakharovShabat/SourceEtaRemainderPhaseSmoothing.lean) | Local complex gap-factor bound, uniform inverse-bracket decay on physical H1 balls, real-valued remainder and collapsed-gap vanishing. Exact phase-error multipliers gain one derivative at every real order and Banach exponent. |
| Remaining Fourier-error reduction | [`SourceBirkhoffFourierErrorReduction.lean`](NLS/ZakharovShabat/SourceBirkhoffFourierErrorReduction.lean) | Exact decomposition into the proved angular error and two literal spectral errors. This reduction takes H2 membership of the spectral errors as a premise; the complete spectral-error results above now discharge it and prove full one-smoothing. |
| Uniform H1 normalization decay | [`SourceNormalizedActionH1Decay.lean`](NLS/ZakharovShabat/SourceNormalizedActionH1Decay.lean), [`SourceProfileActionUpperBound.lean`](NLS/ZakharovShabat/SourceProfileActionUpperBound.lean), [`SourceH1WeightedActionSequence.lean`](NLS/ZakharovShabat/SourceH1WeightedActionSequence.lean), [`SourceSobolevOpenGapDensity.lean`](NLS/ZakharovShabat/SourceSobolevOpenGapDensity.lean) | Actual normalized-action and root errors decay as (1+abs(n))^(-2), uniformly on physical H1 balls, including zero and collapsed gaps. H1 density extends the finite-gap ratio estimate directly. |
| Exact normalization and combined-phase multipliers | [`SourceNormalizedActionRootH1Multiplier.lean`](NLS/ZakharovShabat/SourceNormalizedActionRootH1Multiplier.lean), [`SourceBirkhoffH1NormalizationPhase.lean`](NLS/ZakharovShabat/SourceBirkhoffH1NormalizationPhase.lean), [`SobolevPowerMultiplier.lean`](NLS/SequenceSpaces/SobolevPowerMultiplier.lean) | Root and inverse-root errors gain two sequence derivatives; the original normalization times beta-phase error gains one, at every real sequence order and Banach exponent. The canonical real remainders above complete the coordinate smoothing and stronger-target analyticity at every positive integer order. |
| Sharp real gap-action and normalization bounds | [`SourceGapActionLowerBound.lean`](NLS/ZakharovShabat/SourceGapActionLowerBound.lean), [`SourceNormalizedActionLowerBound.lean`](NLS/ZakharovShabat/SourceNormalizedActionLowerBound.lean) | Actual gap squared <= 4 action, normalized action >= 1/4, normalized root >= 1, inverse norm <= 1, and root error bounded by half the normalized-action error. Every real source, finite p>1, including collapsed gaps. |
| Uniform index-scale separation and reciprocal-square decay | [`SourceDiscIndexSeparation.lean`](NLS/ZakharovShabat/SourceDiscIndexSeparation.lean), [`SourceSegmentIndexSeparation.lean`](NLS/ZakharovShabat/SourceSegmentIndexSeparation.lean), [`SourceSegmentCompactSeparation.lean`](NLS/ZakharovShabat/SourceSegmentCompactSeparation.lean), [`WeightedReciprocalSquareDecay.lean`](NLS/SequenceSpaces/WeightedReciprocalSquareDecay.lean) | All points on distinct actual gaps, locally and uniformly on physical H1 balls. Shared geometry preserves the existing midpoint API. Weighted l1 reciprocal-square sums have inverse-square-bracket decay; the resulting normalized-action upper decay is proved above. |
| One-smoothing ingredient: actual H1 beta decay | [`SourceAngularBetaH1Decay.lean`](NLS/ZakharovShabat/SourceAngularBetaH1Decay.lean), [`WeightedReciprocalDecay.lean`](NLS/SequenceSpaces/WeightedReciprocalDecay.lean), [`SourceAngularBetaCompactBound.lean`](NLS/ZakharovShabat/SourceAngularBetaCompactBound.lean), [`SourceAngularBetaH1BallBound.lean`](NLS/ZakharovShabat/SourceAngularBetaH1BallBound.lean) | Real interlacing and the actual weighted gaps give (1+\|n\|)*\|beta_n\| bounds, locally and uniformly on physical H1 balls, without a finite-gap hypothesis. |
| One-smoothing ingredient: signed phase multipliers | [`SourceBirkhoffH1PhaseDecay.lean`](NLS/ZakharovShabat/SourceBirkhoffH1PhaseDecay.lean), [`SourceBirkhoffH1BallPhase.lean`](NLS/ZakharovShabat/SourceBirkhoffH1BallPhase.lean) | Same original family; beta and exp(t*i*beta)-1 belong to every q>1, including infinity. Exact phase-error multiplication gains one derivative at every real sequence order and Banach exponent, uniformly on physical H1 balls. The canonical real remainders above now prove full Birkhoff-minus-Fourier smoothing and stronger-target analyticity at every positive integer order. |
| Literal Lemma 27.2, every m>=1 | [`SourceSection27SharpEndpoint.lean`](NLS/ZakharovShabat/SourceSection27SharpEndpoint.lean), [`SourceH1SharpEndpoint.lean`](NLS/ZakharovShabat/SourceH1SharpEndpoint.lean) | Exact original indexed-action constant at every order, without a smallness or representation premise. Includes H3<=S-M+S² and the same retained Section 27 family. |
| Actual finite-gap profile identity | [`SourceFiniteGapProfileIdentity.lean`](NLS/ZakharovShabat/SourceFiniteGapProfileIdentity.lean), [`SourcePrimitivePowerGlobalCubic.lean`](NLS/ZakharovShabat/SourcePrimitivePowerGlobalCubic.lean) | The filled quotient equals one plus the constructed positive correction. The profile identity includes selected endpoints. Density gives R_n>=(3/4)*I_n² on every real source at every finite p>1. |
| Exact exterior contour kernels | [`SourceWeightedPrimitiveBoundary.lean`](NLS/ZakharovShabat/SourceWeightedPrimitiveBoundary.lean), [`SourceFiniteGapQuotientCauchy.lean`](NLS/ZakharovShabat/SourceFiniteGapQuotientCauchy.lean), [`SourceExteriorQuotientContour.lean`](NLS/ZakharovShabat/SourceExteriorQuotientContour.lean), [`SourceExteriorRootDenominator.lean`](NLS/ZakharovShabat/SourceExteriorRootDenominator.lean), [`SourceExteriorKernelFiniteSum.lean`](NLS/ZakharovShabat/SourceExteriorKernelFiniteSum.lean), [`SourceExteriorContourKernel.lean`](NLS/ZakharovShabat/SourceExteriorContourKernel.lean) | Analytic weights, exact index cancellation, finite-hole representation, both real root signs, joint integrability, finite support, and the precise -2*pi*i normalization. |
| Analytic spectral quotient | [`SourceFilledGapQuotient.lean`](NLS/ZakharovShabat/SourceFilledGapQuotient.lean), [`SourceFilledGapQuotientInfinity.lean`](NLS/ZakharovShabat/SourceFilledGapQuotientInfinity.lean), [`StandardRootInfinity.lean`](NLS/ZakharovShabat/StandardRootInfinity.lean) | The selected gap is filled analytically; exact real profile and other-gap boundary jumps; actual finite-gap quotient tends to one at complex infinity. |
| Finite-hole Cauchy representation tools | [`CauchyFiniteHoles.lean`](NLS/ComplexAnalysis/CauchyFiniteHoles.lean), [`CauchyOuterLimit.lean`](NLS/ComplexAnalysis/CauchyOuterLimit.lean) | Exact value formula with subtracted inner contours and outer limit 2*pi*i. Their application to the actual finite-gap quotient is proved above. |
| Finite-gap reduction of the endpoint | [`SourceSharpCubicFiniteGapReduction.lean`](NLS/ZakharovShabat/SourceSharpCubicFiniteGapReduction.lean) | At every finite p>1, density reduces the sharp cubic inequality to actual finite-gap sources. The required finite-gap profile identities and the resulting unconditional H1 endpoint are now proved above. |
| Actual spectral gap separation | [`OrderedGapSeparation.lean`](NLS/ComplexAnalysis/OrderedGapSeparation.lean), [`SourceRealGapSeparation.lean`](NLS/ZakharovShabat/SourceRealGapSeparation.lean) | Neighboring original gaps give one positive exterior-distance bound, including collapsed exterior gaps; normalized kernels retain the original scale. |
| Actual angular density and majorant | [`SourceGapAngularDensity.lean`](NLS/ZakharovShabat/SourceGapAngularDensity.lean), [`SourceExteriorGapKernel.lean`](NLS/ZakharovShabat/SourceExteriorGapKernel.lean) | Positive densities integrate to half the actual actions. Action summability gives joint integrability, and uniform separation proves the actual kernel majorant integrable. |
| Explicit gap correction and H1 criterion | [`SourceExteriorGapCorrection.lean`](NLS/ZakharovShabat/SourceExteriorGapCorrection.lean), [`SourceH1ActualGapCriterion.lean`](NLS/ZakharovShabat/SourceH1ActualGapCriterion.lean) | Constructed nonnegative continuous correction. Actual profile identity implies the sharp cubic bound and printed endpoint; H1 callers supply no kernel, atlas or integrability data. The finite-gap identity and the unrestricted endpoint are proved above; an infinite-gap representation is not asserted. |
| Lemma 27.2, closed zero gap | [`SourceH1ZeroModeActionBound.lean`](NLS/ZakharovShabat/SourceH1ZeroModeActionBound.lean) | Actual weights give 2*M-I_0<=S; zero central action gives H3<=S-M+S^2/2. The literal endpoint holds for every real H1 source with collapsed zero gap, without a smallness restriction. |
| Lemma 27.2, one-moment criterion | [`SourceH1ZeroModeMomentCriterion.lean`](NLS/ZakharovShabat/SourceH1ZeroModeMomentCriterion.lean) | The single condition R_0>=(3/4)*I_0^2 implies H3<=S-M+S^2 and the printed bound, using the exact actual energy identity and nonnegative moments. |
| Sharp cubic profile and exterior kernels | [`SineCorrectedCubicIntegral.lean`](NLS/ComplexAnalysis/SineCorrectedCubicIntegral.lean), [`SineExteriorKernelCorrection.lean`](NLS/ComplexAnalysis/SineExteriorKernelCorrection.lean), [`SineIntegralKernelCorrection.lean`](NLS/ComplexAnalysis/SineIntegralKernelCorrection.lean) | Sharp sine-profile ratio, positive correction moments from both exterior sides, finite and integral mixtures, and an explicit integrable majorant proving continuity and Fubini applicability. |
| Exact conditional spectral endpoint | [`SourcePrimitivePowerSharpCubic.lean`](NLS/ZakharovShabat/SourcePrimitivePowerSharpCubic.lean), [`SourceH1ZeroModeKernelCriterion.lean`](NLS/ZakharovShabat/SourceH1ZeroModeKernelCriterion.lean) | Actual profile formula implies the sharp moment bound with original constants; zero-gap representation implies the literal endpoint using a constructed atlas. The finite-gap representation and unrestricted endpoint are now proved above; this conditional API remains available. |
| Analytic physical Hamiltonian fields | [`PhysicalHamiltonianAnalytic.lean`](NLS/ZakharovShabat/PhysicalHamiltonianAnalytic.lean) | Bounded complex linear cotangent-to-direction operation, exact Fourier realization, and analyticity of the literal native field. |
| Complete physical action trajectories | [`PhysicalActionFlow.lean`](NLS/ZakharovShabat/PhysicalActionFlow.lean), [`PhysicalActionFlowProperties.lean`](NLS/ZakharovShabat/PhysicalActionFlowProperties.lean) | All real times from every real physical L2 input, actual cross-gradient equation, uniqueness against arbitrary complex L2 solutions, preservation of all actions, the full discriminant and norm, stationary collapsed gaps. |
| Physical action flow groups | [`PhysicalActionFlowGroup.lean`](NLS/ZakharovShabat/PhysicalActionFlowGroup.lean), [`RealActionRotationProperties.lean`](NLS/SequenceSpaces/RealActionRotationProperties.lean) | Exact one-pair rotation, commuting flows, period 2*pi, joint continuity, fixed-time homeomorphisms and negative-time inverses; coordinate commutation and continuity include lp infinity. |
| Physical Birkhoff Fourier isometry | [`PhysicalBirkhoffFourier.lean`](NLS/ZakharovShabat/PhysicalBirkhoffFourier.lean) | Actual unit Fourier integrals, reflected first frequency, original normalization, full complex linear equivalence, and exact forward/inverse Hilbert norms. |
| Full physical derivative and inverse derivative | [`PhysicalBirkhoffLinearization.lean`](NLS/ZakharovShabat/PhysicalBirkhoffLinearization.lean) | Every original complex extension has the Fourier derivative at zero; the native real derivative is its restriction at every real input; the actual intrinsic inverse has the inverse Fourier derivative at zero. |
| Physical Poisson algebra and Hamiltonian directions | [`PhysicalPoissonAlgebra.lean`](NLS/ZakharovShabat/PhysicalPoissonAlgebra.lean), [`PhysicalHamiltonianDirection.lean`](NLS/ZakharovShabat/PhysicalHamiltonianDirection.lean) | Complex bilinear literal bivector; native cross-gradient direction, full differential evaluation, exact source comparison, and real-form preservation for real differentiable functionals. |
| Physical spectral and action commutation | [`PhysicalSpectralPoisson.lean`](NLS/ZakharovShabat/PhysicalSpectralPoisson.lean) | Actual monodromy discriminants commute on all complex L2 inputs; analytic indexed actions, full dI=x dx+y dy, and action commutation on the physical real form including closed gaps. |
| Physical action Hamiltonian fields | [`PhysicalActionHamiltonian.lean`](NLS/ZakharovShabat/PhysicalActionHamiltonian.lean) | One-pair velocity (-y,x), real tangency, full cotangent and native field zero at collapsed gaps; constructed complex extension with these velocities. No flow-existence assertion. |
| Physical L2 gradients and integral pairing | [`PhysicalL2BilinearPairing.lean`](NLS/ZakharovShabat/PhysicalL2BilinearPairing.lean), [`PhysicalCotangentGradient.lean`](NLS/ZakharovShabat/PhysicalCotangentGradient.lean) | Arbitrary L2 products are integrable; unconjugated physical pairing separates L2 pairs; every continuous complex cotangent has a unique gradient; exact literal integral/source bivector equality. |
| Physical canonical brackets | [`PhysicalPoissonBracket.lean`](NLS/ZakharovShabat/PhysicalPoissonBracket.lean), [`PhysicalBirkhoffCanonical.lean`](NLS/ZakharovShabat/PhysicalBirkhoffCanonical.lean) | Full differential pullback, actual Fourier integral checks, all three canonical coordinate brackets at every real Hilbert input including closed gaps; constructed canonical extension of the intrinsic map. Mixed bracket is minus delta_nm. |
| Intrinsic physical angular integrals | [`PhysicalAngularPaths.lean`](NLS/ZakharovShabat/PhysicalAngularPaths.lean), [`PhysicalDirichletPaths.lean`](NLS/ZakharovShabat/PhysicalDirichletPaths.lean), [`PhysicalAngularComparison.lean`](NLS/ZakharovShabat/PhysicalAngularComparison.lean) | Physical endpoints, actual monodromy radicand and terminal anti-discriminant, constructed C1 integrable paths, beta uniqueness and eta periods; no source-family fields in the specification. |
| Intrinsic physical angle values | [`PhysicalAngularValues.lean`](NLS/ZakharovShabat/PhysicalAngularValues.lean), [`PhysicalAngularReality.lean`](NLS/ZakharovShabat/PhysicalAngularReality.lean) | Actual selected beta and eta integrals, absolute convergence, real values, collapsed beta zeros, theta comparison modulo 2*pi, arbitrary eta-choice formulas. |
| Intrinsic physical Birkhoff map and inverse | [`PhysicalBirkhoffIntrinsic.lean`](NLS/ZakharovShabat/PhysicalBirkhoffIntrinsic.lean), [`PhysicalBirkhoffIntrinsicProperties.lean`](NLS/ZakharovShabat/PhysicalBirkhoffIntrinsicProperties.lean), `intrinsicPhysicalBirkhoffMap`, `intrinsicPhysicalBirkhoffHomeomorph` | Literal physical action-angle coordinates, full l2 membership, equality with every original family, global analytic inverse, both inverse identities, exact norms, zero source, complex extension. This identifies the inspected 2013 physical formulas; exact 2014 edition agreement remains open. |
| Intrinsic physical boundary labels | [`PhysicalBoundaryRoots.lean`](NLS/ZakharovShabat/PhysicalBoundaryRoots.lean), `existsUnique_physicalBoundaryRootData`, `physicalBoundaryRoots_eq_source` | Actual physical characteristic zeros, full analytic orders, lexicographic order, l2 displacements; both boundary conditions, normalized product and actual endpoint equations. |
| Intrinsic physical periodic endpoints | [`OrderedPairedL2Enumeration.lean`](NLS/SequenceSpaces/OrderedPairedL2Enumeration.lean), [`PhysicalPeriodicEndpoints.lean`](NLS/ZakharovShabat/PhysicalPeriodicEndpoints.lean), `PhysicalPeriodicEndpointData.unique` | Global multiplicities and l2 asymptotics determine both ordered sequences, including repeated roots and collapsed gaps. Exact source comparison proved. |
| Intrinsic physical canonical product | [`PhysicalCanonicalRoot.lean`](NLS/ZakharovShabat/PhysicalCanonicalRoot.lean), [`PhysicalSpectralCircles.lean`](NLS/ZakharovShabat/PhysicalSpectralCircles.lean) | Literal symmetric product convergence, exact free sign and square, nonsingular real isolating circles, actual action contours. |
| Independently specified physical psi-functions | [`PhysicalPsiComparison.lean`](NLS/ZakharovShabat/PhysicalPsiComparison.lean), [`PhysicalPsiFamily.lean`](NLS/ZakharovShabat/PhysicalPsiFamily.lean), `existsUnique_physicalPsiGapData`, `physicalPsiFunction_period` | Unique gap roots from placement and off-diagonal periods, entire numerator, exact diagonal normalization, real analyticity, complex extension, agreement with every original Section 14 family. Physical terminal-sheet angle comparison is proved above; precise 2014 version agreement remains open. |
| Original physical Hilbert equivalence | [`UnitIntervalL2Equiv.lean`](NLS/Fourier/UnitIntervalL2Equiv.lean), [`SourcePhysicalL2Equiv.lean`](NLS/ZakharovShabat/SourcePhysicalL2Equiv.lean), `sourcePhysicalL2Equiv`, `norm_sourcePhysicalL2` | The actual source map is onto and preserves the exact unit-interval L2 pair norm. Both inverse components are literal unit Fourier integrals; arbitrary L2 representatives, no endpoint matching. |
| Original physical real form | [`SourcePhysicalRealL2.lean`](NLS/ZakharovShabat/SourcePhysicalRealL2.lean), `sourcePhysicalL2_realType_iff`, `realSourcePhysicalL2Equiv` | A.e. physical conjugation is exactly Fourier conjugate reflection; real linear isometry equivalence of complete real spaces. |
| Physical action integrals | [`SourcePhysicalActions.lean`](NLS/ZakharovShabat/SourcePhysicalActions.lean), `physicalIndexedAction_eq_circuit`, `exists_physicalIndexedAction_circle` | Actual physical monodromy discriminant and derivative; fixed canonical free sign, nonnegative real actions, nonsingular circles and arbitrary admissible winding-one circuits. Spectral labels and canonical product are explicitly transported from the source construction. |
| Physical Hilbert action–angle inverse | [`SourcePhysicalActionAngle.lean`](NLS/ZakharovShabat/SourcePhysicalActionAngle.lean), `physicalRealActionAngleHomeomorph`, `physical_hasSum_actions` | Global analytic map and inverse in exact source and target Hilbert norms; both preserve the norm, with convergent mass trace and choice/family/exponent compatibility. |
| Physical complex extension | [`SourcePhysicalBirkhoffComplex.lean`](NLS/ZakharovShabat/SourcePhysicalBirkhoffComplex.lean), `physicalBirkhoffMap_analytic`, `physicalBirkhoffMap_real` | Full native Hilbert sequence map on an open physical L2 neighborhood of every real input, exact real restriction and complex indexed-action radii. |
| Constructed physical Hilbert package | [`SourceSection14PhysicalHilbert.lean`](NLS/ZakharovShabat/SourceSection14PhysicalHilbert.lean), `sourceSection14_physicalHilbert` | Original family, global real analytic homeomorphism, norm preservation, literal coordinates, and complex extension constructed together. Independent external-book primitive identification remains open. |
| Literal positive-root coordinates | [`SourceBirkhoffRealActionAngle.lean`](NLS/ZakharovShabat/SourceBirkhoffRealActionAngle.lean), `sourceRealActionAmplitude_eq_sqrt`, `real_rectangular_formula_of_eta` | Exact sqrt(2 I) cosine/sine formulas at every real gap; arbitrary admissible eta choices and arbitrary angle values at collapsed gaps. |
| Formula-defined full sequence map | [`SourceBirkhoffActionAngleMap.lean`](NLS/ZakharovShabat/SourceBirkhoffActionAngleMap.lean), `realActionAngleMap_eq`, `realActionAngleHomeomorph_analytic` | Real lp membership and analyticity for every finite p>1; family independence and exponent compatibility. Global analytic inverse for 1<p<=2, with inverse exponent compatibility. |
| Constructed Hilbert action–angle inverse | [`SourceSection14ActionAngle.lean`](NLS/ZakharovShabat/SourceSection14ActionAngle.lean), `sourceSection14_hilbert_actionAngle_inverse` | Actual family and global homeomorphism constructed together; literal formulas for every admissible eta choice. External 2014 map identification remains separate; see [the normalization audit](coverage/SECTION_14.md). |
| Native weighted real Jacobian | [`SourceBirkhoffWeightedRealJacobian.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedRealJacobian.lean), `originalWeightedRealMap_fderiv_bijective`, `originalWeightedRealJacobianEquiv_symm_complex` | Actual real derivative is a bounded equivalence at every weighted real source, every spectral weight and finite p>1; its inverse agrees with the complex inverse on real targets. |
| Real weighted local inverses | [`SourceBirkhoffWeightedRealLocalInverse.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedRealLocalInverse.lean), `exists_originalWeighted_real_localInverse`, `originalWeightedRealMap_isOpenEmbedding` | Both analytic inverse germs, strict inverse derivative, local real-form preservation of complex inverses, and an open embedding for every spectral weight. |
| Weighted inverse on the open image | [`SourceBirkhoffWeightedImageInverse.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedImageInverse.lean), `originalWeightedRealImageInverse_analytic`, `originalWeightedRealImageInverse_hasStrictFDerivAt` | Actual image homeomorphism; inverse analytic with the exact inverse Jacobian throughout the open image. Includes p>2 without assuming surjectivity. |
| Global Sobolev analytic inverse | [`SourceBirkhoffSobolevGlobalInverse.lean`](NLS/ZakharovShabat/SourceBirkhoffSobolevGlobalInverse.lean), `originalWeightedRealSobolevHomeomorph`, `originalWeightedRealSobolevEquiv_symm_analytic` | For 1<p<=2 and every real t>=0, the original native Sobolev bijection is a homeomorphism with both analytic directions and strict inverse derivative. Existing inverse identities and exponent compatibility are retained. |
| Constructed weighted real inverses | [`SourceSection14WeightedRealInverse.lean`](NLS/ZakharovShabat/SourceSection14WeightedRealInverse.lean), `sourceSection14_weighted_real_local_inverse`, `sourceSection14_sobolev_global_analytic_inverse` | One actual original family before all weights or Sobolev orders; real local inverses and global Sobolev analytic inverse in the onto range. |
| Weighted Jacobian bijectivity | [`SourceBirkhoffWeightedJacobianInvertible.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianInvertible.lean), `originalWeightedBirkhoffMap_fderiv_bijective` | Actual native complex derivative, every spectral weight and finite p>1, every weighted real source including closed gaps. |
| Actual weighted complex local inverse | [`SourceBirkhoffWeightedLocalInverse.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedLocalInverse.lean), `exists_originalWeighted_complex_localInverse`, `originalWeightedJacobianEquiv_symm_forget` | Both analytic inverse germs, strict inverse derivative, and compatibility of the bounded inverse Jacobian with forgetting the weight. Real-form preservation and the Sobolev global analytic inverse are proved above. |
| Weighted compact Fourier remainder | [`SourceBirkhoffWeightedJacobianCompact.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianCompact.lean), `isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real` | Full normalized weighted Jacobian differs compactly from the Fourier map at every weighted real source; proved by exact signed blocks and native weighted finite-gap density. |
| Actual weighted local inverse construction | [`SourceSection14WeightedLocalInverse.lean`](NLS/ZakharovShabat/SourceSection14WeightedLocalInverse.lean), `sourceSection14_weighted_complex_local_inverse` | One constructed family before choosing any weight or real source; no supplied inverse or compactness assumption. |
| Compact adapted derivatives | [`NormalizedWeightedClosingCompact.lean`](NLS/ZakharovShabat/NormalizedWeightedClosingCompact.lean), `exists_uniform_compact_normalizedWeightedClosingMap_derivative` | Every spectral weight, finite p>1, all complex sources, common neighborhood and all late cutoffs. Actual original adapted map follows at unit weight. |
| Actual inverse-chart compact remainder | [`SourceBirkhoffClosingInverseCompact.lean`](NLS/ZakharovShabat/SourceBirkhoffClosingInverseCompact.lean), `exists_uniform_complex_closing_inverse_compact` | Constructs analytic inverse charts at every real source with complex slice zeros and compact derivative remainder relative to the free Fourier map. |
| Exact finite-gap derivative blocks | [`SourceBirkhoffFiniteGapAdaptedDerivative.lean`](NLS/ZakharovShabat/SourceBirkhoffFiniteGapAdaptedDerivative.lean), `exists_uniform_finiteGap_adapted_derivative_blocks` | Actual chart, exact two-mode rows, compact Fourier remainder, and all four remainder entries uniformly tending to zero. The weighted transfer is proved above. |
| Weighted complex exponent compatibility | [`SourceBirkhoffWeightedComplexExponent.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedComplexExponent.lean), `weighted_complex_exponent`, `eventually_weighted_complex_exponent`, `weighted_complex_fderiv_exponent` | Entire complex intersections at finite 1<p<=q, every spectral weight, independent families, full sequence germs, and bounded derivative compatibility. Equal exponents give family independence. |
| Native weighted real analyticity | [`SourceBirkhoffWeightedRealAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedRealAnalytic.lean), `originalWeightedRealMap_analytic` | Full real power-series analyticity of the original weighted map on its entire native real source space, for every spectral weight and finite p>1. |
| Weighted Jacobian injectivity | [`SourceBirkhoffWeightedJacobianInjective.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianInjective.lean), `originalWeightedBirkhoffMap_fderiv_injective` | Trivial kernel at every weighted real source, including collapsed gaps. Weighted surjectivity and complex analytic local inverses are proved above. |
| Actual compatible weighted constructions | [`SourceSection14WeightedCompatibility.lean`](NLS/ZakharovShabat/SourceSection14WeightedCompatibility.lean), `sourceSection14_weighted_complex_compatible`, `sourceSection14_weighted_real_analytic` | Constructs the families and common domains for all weights, with full complex map/derivative compatibility, native real analyticity, and derivative injectivity. |
| Full weighted complex sequence map | [`SourceBirkhoffWeightedComplexAnalytic.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedComplexAnalytic.lean), `exists_originalWeightedBirkhoffMap_analytic` | Every spectral weight and finite p>1; common open complex domain containing all weighted real sources, full native weighted analyticity, exact raw coefficients, and original weighted real-map agreement. |
| Weighted Jacobian compatibility | [`SourceBirkhoffWeightedComplexDerivative.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedComplexDerivative.lean), `exists_originalWeightedBirkhoffMap_compatible_derivative` | Full bounded weighted derivative commutes with unweighted source and target inclusions. Bijectivity at weighted real sources is proved above. |
| Actual weighted analytic construction | [`SourceSection14WeightedComplex.lean`](NLS/ZakharovShabat/SourceSection14WeightedComplex.lean), `sourceSection14_weighted_complex_analytic` | One constructed Section 14 family supplies the full complex weighted maps and derivative compatibility for all weights. Weighted complex exponent compatibility, real and complex local inverses, and the Sobolev global analytic inverse are proved above. |
| Complex closing-coordinate bound | [`SourceBirkhoffComplexClosingBound.lean`](NLS/ZakharovShabat/SourceBirkhoffComplexClosingBound.lean), `exists_uniform_complex_closing_bound` | Actual complex Birkhoff tails bounded by two signed adapted coefficients; constructed inverse and real-form identity principle include closed gaps. |
| Weighted canonical coordinate identities | [`SourceBirkhoffWeightedCanonical.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedCanonical.lean), `originalWeightedBirkhoff_canonical`, `originalWeightedBirkhoff_mixed_fourier_canonical` | Actual full scalar coordinate derivatives on native weighted sources, every spectral weight and finite p>1, including closed gaps; all three physical brackets and the literal absolutely convergent mixed Fourier sum. |
| Actual weighted canonical construction | [`SourceSection14WeightedCanonical.lean`](NLS/ZakharovShabat/SourceSection14WeightedCanonical.lean), `sourceSection14_weighted_canonical`, `originalWeightedBirkhoff_analytic` | One constructed family for all weights; scalar complex analytic extensions share an open domain containing all weighted real sources. Full sequence analyticity and the bounded weighted Jacobian are proved by the entries above. |
| Exact Sobolev source regularity | [`SourceSobolevGapRegularity.lean`](NLS/ZakharovShabat/SourceSobolevGapRegularity.lean), `source_mem_sobolev_of_gap` | Every finite p>1 and real t>=0; actual weighted gaps imply the same exact original source weight, without finite-gap or prior positive-regularity hypotheses. |
| Source/gap/Birkhoff characterization | [`SourceBirkhoffSobolevRegularity.lean`](NLS/ZakharovShabat/SourceBirkhoffSobolevRegularity.lean), `sourceSection14_sobolev_characterization` | Exact equivalence at every nonnegative real Sobolev order, with native weighted source representatives. |
| Original Sobolev range | [`SourceBirkhoffSobolevRange.lean`](NLS/ZakharovShabat/SourceBirkhoffSobolevRange.lean), `originalWeightedRealMap_sobolev_range`, `sourceSection14_sobolev_open_dense` | Weighted range equals the continuous target inclusion's preimage of the unweighted range; open dense image for all finite p>1. |
| Original Sobolev bijection | [`SourceBirkhoffSobolevRange.lean`](NLS/ZakharovShabat/SourceBirkhoffSobolevRange.lean), `originalWeightedRealSobolevEquiv` | Onto for 1<p<=2, both inverse identities, exact agreement with the unweighted inverse, and inverse exponent compatibility. Continuity and analyticity of this actual weighted inverse are proved above. |
| Weighted real exponent compatibility | [`SourceBirkhoffWeightedExponent.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedExponent.lean), `sourceSection14_weighted_real_compatible` | Original maps commute with continuous coefficient-preserving inclusions, every finite 1<p<=q, every spectral weight, independent normalized families. |
| Actual center/gap estimate | [`SourceResonantCenterGapBound.lean`](NLS/ZakharovShabat/SourceResonantCenterGapBound.lean), `exists_uniform_sourceResonantCenter_gap_bound` | Both center coefficients bounded by twice the actual gap, uniformly nearby; counted collapsed gaps included. |
| Weighted adapted coordinates | [`SourceAdaptedGapWeightedMembership.lean`](NLS/ZakharovShabat/SourceAdaptedGapWeightedMembership.lean) | Every positive even gap weight is inherited by the adapted map; cutoff independent of the weight, with no weighted-source premise. |
| Forced Fourier-tail recurrence | [`SourceGapWeightedTail.lean`](NLS/ZakharovShabat/SourceGapWeightedTail.lean), `source_weighted_fourierTail_summable_of_gap_tail` | Actual nonzero gap forcing in every available spectral weight; exact geometric summability transfer below the algebraic rate. The exact Sobolev source converse is proved above. |
| Gap/coordinate weighted characterization | [`SourceBirkhoffGapNormEquivalence.lean`](NLS/ZakharovShabat/SourceBirkhoffGapNormEquivalence.lean), `weighted_gap_mem_iff_real_map_mem` | Locally uniform converse gap bounds and exact weighted membership equivalence for any positive weight. The source converse is separately proved for Sobolev weights. |
| Weighted complex gap topology | [`SourceWeightedGapSequence.lean`](NLS/ZakharovShabat/SourceWeightedGapSequence.lean) | Actual full lp sequence, locally uniform norm bound and small tails for all later cutoffs; arbitrary complex compatible weighted sources. |
| Original weighted Birkhoff continuity | [`SourceBirkhoffWeightedContinuity.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedContinuity.lean), `originalWeightedRealMap_continuous` | Stronger weighted source and target topologies, every Section 6 spectral weight and finite p>1. |
| Fractional Sobolev dense image | [`SourceBirkhoffSobolevDenseRange.lean`](NLS/ZakharovShabat/SourceBirkhoffSobolevDenseRange.lean), `originalWeightedRealMap_sobolev_denseRange` | Every real s>=0 and finite p>1; exact weights, actual finite-gap lifts, finite target attainment and density in the original weighted target norm. The open-image and surjectivity extensions are listed above. |
| Remark 14.2(iii), weighted membership | [`SourceBirkhoffWeightedMembership.lean`](NLS/ZakharovShabat/SourceBirkhoffWeightedMembership.lean), `sourceWeightedGap_mem`, `real_map_mem_weighted` | Every finite p>1 and every Section 6 spectral weight; full gap sequence and both original real rectangular coordinates. |
| Original weighted real spaces | [`SourceWeightedRealSpaces.lean`](NLS/ZakharovShabat/SourceWeightedRealSpaces.lean) | Closed conjugate-reflection source, complete real Banach space, norm-preserving coordinates, and exact raw input coefficients. |
| Original weighted Birkhoff map | [`SourceBirkhoffOriginalWeightedMap.lean`](NLS/ZakharovShabat/SourceBirkhoffOriginalWeightedMap.lean) | Original weighted source and target, exact raw output coefficients, injectivity and component-sum norm identity. |
| Fractional Sobolev specialization | [`SourceSection14WeightedMembership.lean`](NLS/ZakharovShabat/SourceSection14WeightedMembership.lean), `sourceSection14_weighted_real_injective` | One actual Section 14 construction for all weights; exact (1+abs(n))^s for every real s>=0. Weighted analyticity and analytic inverse properties are proved above; see [the Section 14 audit](coverage/SECTION_14.md). |
| Appendix C.1, bounded source operator | [`AppendixCSourceTransform.lean`](NLS/Fourier/AppendixCSourceTransform.lean), `sourceLemmaC1_bounded` | Unique continuous linear realization with all-input convergent rows and operator bound for every finite p>1. |
| Appendix C.1, all-exponent discrepancy | [`HilbertNotIsomorphismLp.lean`](NLS/Fourier/HilbertNotIsomorphismLp.lean), `sourceLemmaC1_not_bijective`, `sourceLemmaC1_no_linearEquiv` | Growing alternating blocks refute isomorphism for every finite p>1, including algebraic equivalences realizing the printed series. |
| Appendix C.2, uniform source operator | `sourceLemmaC2`, `sourceModifiedHilbert_hasSum` | One bound before both arbitrary complex displacement sequences, unique bounded operator, exact pi factor and omitted diagonal. See [the Appendix C audit](coverage/APPENDIX_C.md). |
| Appendix B.1 | [`AppendixBSourceInequalities.lean`](NLS/SequenceSpaces/AppendixBSourceInequalities.lean), `sourceLemmaB1` | Summability and both printed bounds; all nonnegative shifts and finite conjugate exponents. |
| Appendix B.2 | `Coeff.sourceLemmaB2` | Unique target sequence with convergent convolution rows and unit norm bound; all Banach Young triples, including infinity. |
| Appendix B.3, positive interpretation | `Coeff.sourceLemmaB3_positive`, `sourceLemmaB3_constant_sharp` | Finite positive exponents, including below one; every nested sum converges, exact bound one, and optimality for every admissible tuple. |
| Appendix B.3, zero qualification | [`MixedYoungZeroExponent.lean`](NLS/SequenceSpaces/MixedYoungZeroExponent.lean) | Printed zero auxiliary endpoints are undefined. Actual l1,l2,l2 inputs give divergent inner or middle sums with nonzero bases. See [the Appendix B audit](coverage/APPENDIX_B.md). |
| Appendix A.9, original interval functions | [`PeriodicIntervalFourierLebesgue.lean`](NLS/Fourier/PeriodicIntervalFourierLebesgue.lean), `ofL1_mem_fourierLebesgue_of_intervalSobolev`, `ofL1_mem_fourierLebesgue_of_intervalHalfSobolev` | Original normalized interval distributions; full strict source exponent ranges, no endpoint matching, ordinary L2 at s=0, and infinity via the q≥2 inclusion. |
| Appendix A.9, continuous injections | [`PeriodicIntrinsicSobolevEmbedding.lean`](NLS/Fourier/PeriodicIntrinsicSobolevEmbedding.lean), `originalFourierEmbedding`, `originalHalfFourierEmbedding` | Actual intrinsic interval classes to original FLq; complex continuous linear injections, exact smooth-test action, arbitrary-input recovery, and explicit physical norm bounds. |
| Subcritical original Sobolev identification | [`PeriodicIntrinsicSobolevEquivalence.lean`](NLS/Fourier/PeriodicIntrinsicSobolevEquivalence.lean), `originalSobolevEquiv` | Continuous linear equivalence for 0<s<1/2, both inverse identities, original physical representatives, and both norm bounds with the exact Section 2 weight. |
| Appendix A.7, original-distribution product | [`PeriodicFourierLebesgueProduct.lean`](NLS/Fourier/PeriodicFourierLebesgueProduct.lean), `youngProduct`, `norm_youngProductCLM` | Every positive period and every Banach Young triple, including infinity; unique convolution-defined original product, absolute convergence, sharp norm one, exponent independence, and actual continuous multiplication. |
| Original Wiener algebra | [`PeriodicWienerAlgebra.lean`](NLS/Fourier/PeriodicWienerAlgebra.lean), `wienerContinuousAlgHom` | Complete commutative normed complex algebra on original FL1, norm-one identity, injective algebra map into actual continuous functions. |
| Appendix A.8, corrected estimate | [`PeriodicSobolevEmbedding.lean`](NLS/Fourier/PeriodicSobolevEmbedding.lean), `sobolevToWiener`, `norm_sobolevProduct_le` | Every finite Banach exponent; exact original-distribution inclusion, continuous representative, inverse-weight Hölder constant C_p ≤ 2p with Section 2 norm. |
| Counterexample to printed (A.4) | [`SobolevProductCounterexample.lean`](NLS/Fourier/SobolevProductCounterexample.lean), `a8Original_constant_one_fails` | Actual finite polynomials on the original spaces; squared input norms 8 and 5, squared product norm 41. At period two the source proof's rescaled weight also agrees. |
| Appendix A Riemann–Lebesgue decay, first part of A.6 | [`PeriodicRiemannLebesgue.lean`](NLS/Fourier/PeriodicRiemannLebesgue.lean), `tendsto_fourierCoeff_cofinite`, `tendsto_truncate_ofIntervalL1` | Every positive physical period; two-sided coefficient decay and convergence in the original FL-infinity norm. Point evaluation has no interval L1 representative. |
| Appendix A L1 Fourier map into c0 | [`PeriodicL1Fourier.lean`](NLS/Fourier/PeriodicL1Fourier.lean), `circleL1Fourier`, `norm_circleL1Fourier`, `denseRange_circleL1Fourier` | Actual L1 quotient, complex continuous linear map, exact norm one, finite-polynomial coefficient recovery, injectivity, and dense range. Non-surjectivity and nonclosed range are proved below. |
| Appendix A.6, non-surjectivity | [`PeriodicL1NonSurjective.lean`](NLS/Fourier/PeriodicL1NonSurjective.lean), `circleL1Fourier_not_surjective`, `not_isClosed_range_circleL1Fourier`, `exists_vanishing_not_fourierCoeff` | Every positive physical period; actual L1-to-c0 map has proper dense nonclosed range. A cofinite-vanishing integer sequence is not the Fourier sequence of any integrable function. |
| Appendix A.6, original distribution counterexample | `PeriodicFourierLebesgue.exists_norm_convergent_not_ofCircleL1` | An original FL-infinity distribution has norm-convergent Fourier truncations and no physical L1 representative. |
| Rudin–Shapiro polynomial foundation | [`RudinShapiro.lean`](NLS/Fourier/RudinShapiro.lean), [`RudinShapiroCoefficients.lean`](NLS/Fourier/RudinShapiroCoefficients.lean) | Exact energy, uniform square-root bound, full finite coefficient support, coefficient norms, normalized Parseval, and exact finite p-norms. These provide the open-mapping contradiction in A.6. |
| Appendix A.3, non-measure distribution | [`NonMeasureFourierCounterexample.lean`](NLS/Fourier/NonMeasureFourierCounterexample.lean), `exists_fourierLebesgue_above_two_not_measure` | One original periodic distribution belongs to all FLp with p > 2, including infinity, and is not represented by any actual complex measure; every positive period. |
| Appendix A.5, continuous counterexample | [`ContinuousFourierCounterexample.lean`](NLS/Fourier/ContinuousFourierCounterexample.lean), `exists_continuous_not_fourierLebesgue_below_two` | One actual continuous function lies in no original FLp with 1 ≤ p < 2. An alternative block construction proves the source's existential statement. |
| Disjoint polynomial blocks | [`ShiftedRudinShapiro.lean`](NLS/Fourier/ShiftedRudinShapiro.lean) | Exact shifted support, disjointness, square-root uniform bound, and physical Fourier-polynomial recovery for the two sharpness examples. |
| Appendix A sharp interpolation prerequisites | [`FiniteInterpolationSharp.lean`](NLS/SequenceSpaces/FiniteInterpolationSharp.lean), [`DiscreteParseval.lean`](NLS/Fourier/DiscreteParseval.lean) | Exact geometric endpoint bound on arbitrary finite inputs; character orthogonality, discrete adjoint and Parseval identities, and exact sqrt(N) Hilbert norm factor. The full continuous embeddings are now proved below. |
| Appendix A.2 and A.4, full embeddings | [`PeriodicFourierLebesgueEmbeddings.lean`](NLS/Fourier/PeriodicFourierLebesgueEmbeddings.lean), `ofLp`, `lpRepresentative` | Actual Lᵖ → original FLᑫ and original FLᵖ → actual Lᑫ for conjugate 1 ≤ p ≤ 2, including both endpoints; continuous linear injections, constant-one bounds, exact 1/L action, unique representatives, and agreement with the earlier endpoint maps. |
| Appendix A Hausdorff–Young construction | [`FiniteMatrixInterpolation.lean`](NLS/SequenceSpaces/FiniteMatrixInterpolation.lean), [`DiscreteHausdorffYoung.lean`](NLS/Fourier/DiscreteHausdorffYoung.lean), [`CircleSampling.lean`](NLS/Fourier/CircleSampling.lean), [`PolynomialHausdorffYoung.lean`](NLS/Fourier/PolynomialHausdorffYoung.lean), [`CircleHausdorffYoungSynthesis.lean`](NLS/Fourier/CircleHausdorffYoungSynthesis.lean), [`CircleHausdorffYoungAnalysis.lean`](NLS/Fourier/CircleHausdorffYoungAnalysis.lean) | Exact finite matrix and DFT estimates, alias-free signed frequency grids, convergence of sample moments, density extension of synthesis, and full duality for analysis. |
| Appendix A integrable uniqueness | [`PeriodicL1Uniqueness.lean`](NLS/Fourier/PeriodicL1Uniqueness.lean), `Distribution.ofCircleL1_eq_iff`, `circleLp_fourierCoeff_injective`, `circleL1Fourier_injective` | Original distributions distinguish integrable functions modulo a.e. equality; Fourier coefficients determine all Banach Lᵖ classes. |
| Appendix A Fourier–Lebesgue Banach spaces and reflexivity | [`PeriodicFourierLebesgueSpace.lean`](NLS/Fourier/PeriodicFourierLebesgueSpace.lean), `coefficientsIsometry`, `bidual_surjective` | Actual original distributions, all positive periods and all real Sobolev orders; exact coefficient norm, completeness for 1 ≤ p ≤ infinity, reflexivity for 1 < p < infinity. |
| Appendix A Fourier-series convergence | [`PeriodicFourierLebesgueSeries.lean`](NLS/Fourier/PeriodicFourierLebesgueSeries.lean), `truncate_eq_ofContinuous`, `tendsto_truncate_action` | Actual continuous Fourier polynomials; finite-p norm convergence and all-p convergence against every original smooth test. At infinity, norm convergence iff weighted c0, with point-evaluation error exactly one. |
| Appendix A L2 identification and L1 endpoint | [`PeriodicFourierLebesgueEndpoints.lean`](NLS/Fourier/PeriodicFourierLebesgueEndpoints.lean), `l2Isometry`, `l2Isometry_apply_interval`, `l2Isometry_parseval_interval`, `norm_ofIntervalL1_le` | Actual physical-circle L2 quotient; exact 1/L integral and Parseval normalization; normalized L1-to-FL-infinity bound with constant one. |
| Appendix A absolute Fourier synthesis | `continuousRepresentativeCLM`, `existsUnique_continuousRepresentative`, `hasSum_continuousRepresentative` | Unique uniformly continuous representative of every FL1 distribution; absolute convergence, uniform convergence, exact physical frequencies, and sup norm at most the FL1 norm. |
| Appendix A pseudomeasures and full unweighted duality | [`PeriodicFourierLebesgueDuality.lean`](NLS/Fourier/PeriodicFourierLebesgueDuality.lean), `unweightedDualIsometry`, `pseudomeasureDualIsometry` | Entire continuous dual at finite source exponent, conjugate exponent including infinity; opposite Fourier indices and exact norm. |
| Appendix A complex Radon representation, (A.2) | [`PeriodicDistributionMeasure.lean`](NLS/Fourier/PeriodicDistributionMeasure.lean), `Distribution.order_zero_iff_measure`, `existsUnique_normalized_measure` | Every positive physical period; unique actual complex measure, exact 1/L action on original tests and all continuous functions, and converse for every complex Borel measure. |
| Appendix A finite variation, regularity, and uniqueness | [`ComplexMeasureContinuousIntegral.lean`](NLS/Fourier/ComplexMeasureContinuousIntegral.lean), `complexMeasure_variation_regular`, `complexMeasureContinuousIntegral_injective` | Finite total variation and regularity, standard Jordan integral independent of a positive-minus-negative representation, and measure uniqueness. |
| Appendix A measure normalization | `Distribution.ofComplexMeasure_dirac`, `ofComplexMeasure_zero_coefficient` | A mass Lz at x equals z times point evaluation; the zero Fourier coefficient is total mass divided by L. See [the Appendix A audit](coverage/APPENDIX_A.md). |
| Appendix A Fréchet space and density | [`SmoothPeriodicTestFrechet.lean`](NLS/Fourier/SmoothPeriodicTestFrechet.lean), `derivativeJetEquiv`, `denseRange_toContinuousCLM` | Complete, metrizable, Hausdorff, locally convex original test space; dense in C(T_L) at every positive physical period. |
| Appendix A order-zero extension and L1 action | [`PeriodicDistributionPhysicalOrderZero.lean`](NLS/Fourier/PeriodicDistributionPhysicalOrderZero.lean), `Distribution.order_zero_iff_physical_extension`, `ofL1_apply` | Unique continuous extension iff least order zero; exact 1/L integral and agreement with the actual L1 tempered distribution. The general complex Radon representation is established above. |
| Appendix A distributional derivative | [`SmoothPeriodicDistributionDerivative.lean`](NLS/Fourier/SmoothPeriodicDistributionDerivative.lean), `Distribution.derivative_coefficient`, `toTempered_derivative` | Original-dual derivative, exact signed i·2πn/L multiplier, order increase at most one, and equality with the physical tempered derivative. |
| Appendix A finite-order criterion (A.1) | [`SmoothPeriodicTestSpace.lean`](NLS/Fourier/SmoothPeriodicTestSpace.lean), `continuous_iff_finite_order` | Actual smooth periodic functions, all positive periods, exact sums of physical derivative sup norms; continuity iff one finite-order bound. |
| Theorem A.1(i) | [`PeriodicDistributionFourierGrowth.lean`](NLS/Fourier/PeriodicDistributionFourierGrowth.lean), `Distribution.coefficients_isBigO` | Literal least order, same polynomial degree, signed Fourier indices and exact physical period normalization. |
| Theorem A.1(ii) and actual realization | [`SmoothPeriodicDistribution.lean`](NLS/Fourier/SmoothPeriodicDistribution.lean), `Distribution.existsUnique_of_polynomial_isBigO`, `periodicTemperedEquiv` | Unique functional on all original smooth tests; polynomial synthesis includes degree zero and arbitrary zero mode; equivalence with actual periodic tempered distributions. See [the Appendix A audit](coverage/APPENDIX_A.md). |
| Formula (5.14) | [`SourceSection28Asymptotics.lean`](NLS/ZakharovShabat/SourceSection28Asymptotics.lean), `normalized_locally_uniform`, `normalized_uniform_H1_ball` | Original filled normalized actions, actual ℓ² realization, local complex uniformity and uniform bounds on every real physical H¹ ball via compact decoding. |
| Formula (5.15); final Lemma 28.1 bound; Proposition 28.2 | [`SourceSection28GapBounds.lean`](NLS/ZakharovShabat/SourceSection28GapBounds.lean), `SourceSection28Data.physical_H1_bounds` | Literal χ and indexed actions, exact factors 9/2048/4608, signed indices, inclusive cutoffs, closed complex gaps and a common connected L²-open domain. |
| Lemma 28.1 signed ratio | [`SourceSection28SignedIndex.lean`](NLS/ZakharovShabat/SourceSection28SignedIndex.lean), `section28_signed_ratio_zero` | Actual zero-source counterexample at n=−1, N=1 with the physical cutoff; does not refute the final 2048 bound. |
| Section 28 proof of Theorem 23.4 | [`SourceSection28Original.lean`](NLS/ZakharovShabat/SourceSection28Original.lean), `weighted_summable`, `weighted_continuous`, `weighted_bound` | Original weighted action sums converge continuously on the full weighted complex part of S; exact real 2²⁰ and complex 2²¹ bounds, connected weighted neighborhoods and the same original family. See [the Section 28 audit](coverage/SECTION_28.md). |
| Formula (5.13); Lemma 27.1 | [`SourceSection27Actions.lean`](NLS/ZakharovShabat/SourceSection27Actions.lean), [`SourceSection27Original.lean`](NLS/ZakharovShabat/SourceSection27Original.lean) | Original indexed actions, actual physical remainder integral, both component derivative energies, absolute convergence, and exact coefficients 1/2 and 1/3. |
| Lemma 27.2 | `sourceSection27_hamiltonian_estimate_literal`, `sourceSection27_endpoint` | Printed coefficient for every m>=1 and every real H^m input, with the original indexed actions. The former endpoint qualification is resolved. |
| Section 27 derivative estimate and original family | [`SourceSection27DerivativeBound.lean`](NLS/ZakharovShabat/SourceSection27DerivativeBound.lean), `exists_sourceSection27_derivative_bound`, `sourceSection27_original` | Literal pair factor 1/4, coefficient one on the highest action sum, unweighted final action factor, uniform constants, and unchanged U/T. See [the Section 27 audit](coverage/SECTION_27.md). |
| Formula (5.11), valid ranges | [`SourceSection26Interpolation.lean`](NLS/ZakharovShabat/SourceSection26Interpolation.lean), `sourceSection26_supremum_interpolate`, `sourceSection26_L2_interpolate` | Exact physical Hᵐ norm; supremum bound for i<m and L² bound for i≤m, with explicit constants. |
| Formula (5.11), printed supremum endpoint | [`SourceSection26SupremumCorrection.lean`](NLS/ZakharovShabat/SourceSection26SupremumCorrection.lean), `section26_supremum_no_uniform_constant` | Refuted at m=i=1 for every proposed constant by actual real H² sources with nonzero mass, bounded physical H¹ norm, and continuous first derivative; witnesses lie in every retained U∩T. |
| Proposition 26.1 | [`SourceSection26Actions.lean`](NLS/ZakharovShabat/SourceSection26Actions.lean), `sourceSection26_meanValue_complex`, `sourceSection26_exterior`, `sourceSection26_central` | Original real H¹ sources, exact norm and radius, actual gap points, signed indices, all m≥0, and the printed constants. |
| Lemma 26.2 | [`SourceSection26Sum.lean`](NLS/ZakharovShabat/SourceSection26Sum.lean), `sourceSection26_action_estimate_half_mass` | Original weighted action summability on Hᵐ; positive physical Hamiltonian sign, exact half-mass and full-mass remainders; literal printed sign proved at odd m. |
| Lemma 26.2 counterexample; p. 115 norm splitting | [`SourceSection26SignCorrection.lean`](NLS/ZakharovShabat/SourceSection26SignCorrection.lean), `section26_printedInequality_strict_counterexample`, `section26_printed_physicalNorm_split_counterexample` | Actual real H² source refutes the full signed inequality, with summability; a separate physical H¹ mode refutes the printed splitting coefficient. |
| Lemma 26.3; Section 26 original family | [`SourceSection26Original.lean`](NLS/ZakharovShabat/SourceSection26Original.lean), `exists_sourceSection26_remainder_bounds`, `sourceSection26_original` | One constant before all real sources controls both physical remainder and Hamiltonian; unchanged U and T. The (5.11) endpoint correction is recorded in [Section 26](coverage/SECTION_26.md). |
| Theorem 25.1; Lemma 25.4 | [`SourceSection25Localization.lean`](NLS/ZakharovShabat/SourceSection25Localization.lean), `sourceH1_uniform_localization`, `sourceH1_canonical_pair` | Original complex H¹ sources, exact physical norm and quadratic cutoff, signed endpoints, full-strip determinant roots and exact multiplicities. |
| Lemmas 25.2–25.3; (5.7) | [`SourceSection25Coefficients.lean`](NLS/ZakharovShabat/SourceSection25Coefficients.lean), `sourceM1_square_bound`, `sourceM1_coefficients_joint_analytic` | Exact operator and componentwise coefficient bounds, closed-strip and joint source analyticity, both diagonal representations of the actual inverse. |
| Proposition 25.5; (5.8) | [`SourceSection25Original.lean`](NLS/ZakharovShabat/SourceSection25Original.lean), `sourceSection25_original`, `SourceSection25Data.gap_bound` | Exact original tail and individual gap bounds; one open original subdomain chosen before all M₁ weights and potentials for the global 265π² estimate. See the [Section 25 audit](coverage/SECTION_25.md). |
| Theorem 24.1; (5.2)–(5.6) | [`SourceSection24Original.lean`](NLS/ZakharovShabat/SourceSection24Original.lean), `sourceSection24_original`, `SourceSection24Data.trace_printed_level` | Original contour-defined actions and retained primitive; absolute, analytic physical traces on the full complex H^(k−1) part of the unchanged original Section 19/20 domain, sharp odd Hᵐ traces, literal real gap integral and original mean-value comparison. See the [Section 24 audit](coverage/SECTION_24.md) for exact domains and the corrected zero-detection scope. |
| Section 24 asymptotic following (5.6) | [`SourceIndexedHigherActionAsymptotic.lean`](NLS/ZakharovShabat/SourceIndexedHigherActionAsymptotic.lean), `sourceIndexedHigherAction_asymptotic` | Actual mean-value samples with ℓᵖ displacement; original higher action equivalent to (nπ)^k Iₙ along both integer tails, all natural powers and real sources at every finite p>1, including collapsed gaps. |
| Section 24 zero-detection claim, p. 106 | [`SourceSection24ZeroDetectionCorrection.lean`](NLS/ZakharovShabat/SourceSection24ZeroDetectionCorrection.lean), `section24_levelTwo_zero_counterexample` | Refuted by an actual real finite-gap source with I₀=1, open central gap, and zero level-two action. Every retained original U contains a witness with any prescribed I₀>0. Odd real levels retain zero detection. |
| Theorem 0.1; Theorems 23.1–23.2; Remark 23.3 | [`SourceSection23Sobolev.lean`](NLS/ZakharovShabat/SourceSection23Sobolev.lean), `SourceSection17OriginalData.section23_sobolev_bounds` | One original map, every positive integer Sobolev order, common positive constants chosen before the potential, both Birkhoff bounds and both original indexed action bounds. |
| Theorem 23.4; Corollary 23.5 | [`SourceSection23Weighted.lean`](NLS/ZakharovShabat/SourceSection23Weighted.lean), `SourceSection20Data.section23_weighted_neighborhood`, `section23_realSobolev_neighborhood` | Same original family, every M₁ weight and every real order at least one; full real weighted locus inside one complex neighborhood decoding into the original domain, exact physical weights, original indexed actions and weighted target norms. |
| Introduction p.9: almost periodicity | [Original solutions](NLS/ZakharovShabat/SourceOriginalAlmostPeriodic.lean), [phase recurrence](NLS/Dynamics/PhaseAlmostPeriodic.lean), [audit](coverage/INTRODUCTION.md) | Proved in the full source norm and every nonnegative native Sobolev norm for 1<p<=2; the stronger representative recovers every original global ordinary/renormalized solution coefficientwise. |
| Introduction p.9: native Sobolev recurrence | [Original Sobolev solutions](NLS/ZakharovShabat/SourceSobolevAlmostPeriodic.lean), [weighted lift](NLS/ZakharovShabat/SourceSobolevPhaseFlow.lean) | Every nonnegative real order, exact original weight (1+|n|)^s, initial weighted source retained, and uniform recurrence in the actual stronger norm. |
| Introduction p.10: critical Sobolev inclusion | [Coefficient inclusion](NLS/SequenceSpaces/CriticalSobolevInclusion.lean), [original distributions](NLS/Fourier/PeriodicCriticalSobolevInclusion.lean), [audit](coverage/INTRODUCTION.md) | Continuous injective FL^p-to-H^(-1/2) inclusion for every finite p>2 and every positive period; all coefficients and the original distribution are unchanged. No infinity input assertion. |
| Introduction p.10: full-line dilation | [Physical PDE](NLS/ZakharovShabat/ScalarNLSScaling.lean), [homogeneous energy](NLS/Fourier/HomogeneousNLSScaling.lean), [audit](coverage/INTRODUCTION.md) | Actual NLS covariance and exact extended homogeneous Fourier-energy factor c^(2s+1); critical energy at s=-1/2 is invariant. The complete critical-space identification is listed next. |
| Introduction p.10: scalar Fourier differential | [Scalar differential](NLS/ZakharovShabat/ScalarNonlinearLinearization.lean), [audit](coverage/INTRODUCTION.md) | Global real analyticity and the full bounded differential at zero; its n-th coefficient is minus the actual physical Fourier coefficient at -n. |
| Introduction pp.10–11: global scalar nonlinear Fourier inverse | [Scalar inverse](NLS/ZakharovShabat/ScalarNonlinearInverse.lean), [audit](coverage/INTRODUCTION.md) | Explicit global real analytic inverse on all l2, both original L2 inverse identities, exact scalar norm and signed reflected inverse Fourier differential. |
| Introduction p.10: scalar nonlinear Parseval | [Scalar normalization](NLS/ZakharovShabat/ScalarNonlinearParseval.lean), [audit](coverage/INTRODUCTION.md) | The literal complex coefficient (x-i*y)/sqrt(2) has exactly the original scalar L2 norm, with a convergent sum of squared coefficients. The physical pair factor two is retained explicitly. |
| Introduction p.9: independence of action differentials | [Complex differentials](NLS/ZakharovShabat/SourceActionDifferentialIndependence.lean), [real differentials](NLS/ZakharovShabat/SourceRealActionDifferentialIndependence.lean), [audit](coverage/INTRODUCTION.md) | At every finite p>1, the actual action differentials indexed by open gaps are independent. A real action differential vanishes exactly at gap collapse, so the full real family is independent exactly when all gaps are open. |
| Introduction p.9: original spectral conservation and oscillators | [Spectral conservation](NLS/ZakharovShabat/SourceOriginalSpectralConservation.lean), [independent integrals](NLS/ZakharovShabat/SourceOriginalActionIntegrals.lean), [rectangular derivatives](NLS/Dynamics/RectangularHamiltonianOscillators.lean), [original oscillators](NLS/ZakharovShabat/SourceOriginalOscillators.lean), [audit](coverage/INTRODUCTION.md) | Every original global ordinary and renormalized solution for 1<p<=2 preserves its actions, actual periodic spectrum with multiplicities, discriminant, and frequencies. The action functions are linearly independent and in involution; the actual rectangular coordinates satisfy the oscillator equations. |
| Introduction p.10: original FLp distributions outside L2 | [Strictness](NLS/Fourier/PeriodicFourierLebesgueStrictness.lean), [audit](coverage/INTRODUCTION.md) | One actual nonmeasure distribution belongs to every FLp with p>2, including infinity, but not FL2=L2. The witness is simultaneous in p and exists at every positive period. |
| Introduction p.10: complete critical homogeneous space | [Distribution dilation](NLS/Fourier/LineTemperedNLSScaling.lean), [spectral measure](NLS/Fourier/CriticalFrequencyMeasure.lean), [complete model](NLS/Fourier/CriticalHomogeneousSobolev.lean), [Fourier characterization](NLS/Fourier/CriticalHomogeneousCharacterization.lean), [audit](coverage/INTRODUCTION.md) | Complete injective distributional realization with the exact homogeneous norm, converse finite-energy Fourier-density characterization, and physical dilation as a surjective linear isometry. |
| Introduction p.10: Galilean symmetry | [Physical PDE](NLS/ZakharovShabat/ScalarNLSGalilean.lean), [Fourier formula](NLS/Fourier/LineGalileanFourier.lean), [Schwartz operators](NLS/Fourier/LineAngularSchwartz.lean), [tempered distributions](NLS/Fourier/LineTemperedGalilean.lean), [Fourier-Lebesgue invariance](NLS/Fourier/LineFourierLebesgueGalilean.lean), [audit](coverage/INTRODUCTION.md) | Classical PDE covariance and invariance of the original distributional FLp spaces for every p>=1, including infinity, with exact Fourier representative norms. |
| Introduction, printed p. 12: mass nonextension | [`ActionMassNonextension.lean`](NLS/SequenceSpaces/ActionMassNonextension.lean), [`RealActionMassNonextension.lean`](NLS/SequenceSpaces/RealActionMassNonextension.lean) | No extension continuous at zero relative to the positive ell^q cone for any q>1, including infinity, in both real and complex action spaces. Local agreement with total action on summable positive sequences suffices. |
| Introduction, full Hamiltonian on weighted actions | [`SourceStandardActionHamiltonian.lean`](NLS/ZakharovShabat/SourceStandardActionHamiltonian.lean), [`SourceWeightedActionHamiltonianNorm.lean`](NLS/ZakharovShabat/SourceWeightedActionHamiltonianNorm.lean) | Complex and real analytic full energy in the exact standard ell^(2,1) topology, open domain containing the whole nonnegative cone, physical identity for every real H1 source, and coordinate derivative F_n + 4 mass + (2 pi n)^2. Coefficients are preserved through explicit norm bounds. |
| Theorem 0.2: analytic action Hamiltonian, sign, Hessian and local concavity | [`SourceHamiltonianActionConcavity.lean`](NLS/ZakharovShabat/SourceHamiltonianActionConcavity.lean), `exists_sourceHamiltonian_action_extension_with_concavity` | Actual source Hamiltonian on an open complex ℓ² domain containing all nonnegative summable actions; actual frequency gradient, Hessian −2 times Hilbert bilinear duality, quantitative local negativity. |
| Physical normalization of H* | [`SourceSobolevHamiltonianIdentification.lean`](NLS/ZakharovShabat/SourceSobolevHamiltonianIdentification.lean), `SourcePrimitivePowerAtlas.renormalizedHamiltonian_eq_sobolevPhysicalCorrection` | Identification with the H¹ energy correction on all real H¹ sources, beyond the finite-gap normalization. |
| Consequence after Theorem 0.2, printed p. 12: no C¹ extension for q > 2 | [`SourceHamiltonianOriginalNonextensionTop.lean`](NLS/ZakharovShabat/SourceHamiltonianOriginalNonextensionTop.lean), `SourceOriginalHamiltonianData.no_continuous_extension_all` | No continuous extension at zero relative to the nonnegative ell^q cone, hence no C1 extension, for every q > 2 including infinity. Any retained original Hamiltonian keeps its source recovery and physical H1 identity. |
| Theorem 0.3; Theorem 18.1: frequency extensions | [`SourceFrequencyOriginalHilbertTop.lean`](NLS/ZakharovShabat/SourceFrequencyOriginalHilbertTop.lean), `SourceOriginalHilbertFrequencyData.realizations_all` | The same original common frequency has complex and real analytic realizations in every target exponent r>1, including infinity, on its unchanged summable-action domain. Compatible higher-action extensions retain finite p>2 and the original locally uniform mixed remainder. |
| Local invertibility near zero; Corollary 18.2(i) | [`SourceFrequencyLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyLocalInverse.lean), `exists_sourceFrequency_localInverse` | Actual frequency derivative −2 times identity, both analytic local inverse identities, inverse derivative −1/2 times identity, and the Fredholm property throughout the action domain. |
| Remark after Theorem 0.3; Corollary 18.2(iv): generic local invertibility | [`SourceFrequencyGenericLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyGenericLocalInverse.lean), `exists_sourceFrequency_genericLocalInverse` | Open dense set of points with two-sided analytic local inverses on a connected action domain containing all real-source actions and all nonnegative summable actions. |
| Remark after Theorem 0.2: open dense positive Hamiltonian domain | `SourceOriginalHamiltonianData.positive_domain`, [`SourceOriginalActionDomains.lean`](NLS/ZakharovShabat/SourceOriginalActionDomains.lean) | The same retained Hamiltonian domain has a relatively open dense positive part. Its explicit real summable-action realization preserves all original values, sign and zero detection. |
| Remark after Theorem 0.3: open dense positive frequency domains | `SourceOriginalFrequencyData.positive_domain`, [`SourceOriginalActionDomains.lean`](NLS/ZakharovShabat/SourceOriginalActionDomains.lean) | Every retained original finite-exponent frequency keeps its unchanged domain, relatively open and dense in its positive action cone, and all its existing mixed remainder and inverse conclusions. |

The [introduction audit](coverage/INTRODUCTION.md) maps the three main
results and the method-of-proof outline, with exact domain and normalization
qualifications. The wider introductory background remains under review.

The named Section 23 estimates and exact physical norms are audited in
[`coverage/SECTION_23.md`](coverage/SECTION_23.md).
[`SourceSection23Original.lean`](NLS/ZakharovShabat/SourceSection23Original.lean)
retains one original family for all orders and weights, including the
original indexed actions throughout each complex weighted neighborhood.
The printed weight-growth bound has a formal M₁ counterexample and a
corrected geometric majorant. The opening fractional-smoothness claims
remain separately qualified.
The higher-action outline now has actual-source counterexamples to its
restricted index set and alternating sign; the original physical traces
and remaining assertions are audited in
[`coverage/SECTION_24.md`](coverage/SECTION_24.md).

The current original-domain angle audit is in
[`coverage/SECTION_13.md`](coverage/SECTION_13.md). The original Birkhoff
map and assertion-by-assertion Theorem 14.1 audit are in
[`coverage/SECTION_14.md`](coverage/SECTION_14.md). The original-domain
gap-weighted bounds, collapsed limits, and analytic sequences are audited in
[`coverage/SECTION_15.md`](coverage/SECTION_15.md). The original Jacobian,
Holder-conjugate gradient estimates, corrected reconstruction, and compact
normalization are audited in [`coverage/SECTION_16.md`](coverage/SECTION_16.md).
The original inverse, angle-flow, and isospectral assertions are audited in
[`coverage/SECTION_17.md`](coverage/SECTION_17.md).
The original action-frequency extensions, inverse assertions, Hamiltonian,
nonextension, and all four wellposedness cases of Theorems 18.1–18.5 are
audited in [`coverage/SECTION_18.md`](coverage/SECTION_18.md). The same
Hamiltonian retains the original frequency as its gradient and its physical
identity on every real H¹ source. Three printed normalization errors have
formal witnesses. The original abelian integral, admissible paths,
endpoint and side limits, physical Laurent series, and literal mixed gap
supremum are audited in [`coverage/SECTION_19.md`](coverage/SECTION_19.md).
These assertions hold for one canonical primitive on one common source
domain inside the original family. The original contour moments and
frequency assertions are audited in
[`coverage/SECTION_20.md`](coverage/SECTION_20.md). That package retains
the same primitive and original roots, proves the physical finite-gap
normalization, fixed mixed remainders, analytic sequence maps, and
compatibility with the original action frequency. The unrestricted
diagonal auxiliary-factor analyticity claim has a formal zero-source
counterexample. At real finite-gap sources the original angle flow
differentiates in H¹ throughout its pre-collapse interval. Physical
momentum has a unique Hilbert cotangent at every complex H¹ source and
generates the actual spatial-translation orbit. The original
angle–momentum bracket is 2πn on the full complex H¹ part of the
original Section 20 domain with the selected gap open. The proof starts
from the retained primitive's physical H₂ contour and H¹ finite-gap
density, then continues the real germs on the connected complex domain.

The original angle vector has a unique analytic H¹ lift throughout that
domain. Its full physical H¹ energy differential recovers the original
frequency with mass and dispersion restored. Dense H¹ inclusion and
connectedness of the nonzero locus of the analytic squared gap give the
full domain H¹_c ∩ (U \ Zₙ) for every n; U is chosen once before all
indices. No infinite intersection or further shrinking is needed. An L²
energy cotangent is not assumed at arbitrary H¹ sources; whenever one
represents the energy differential, the original bivector gives the same
value.

The original primitive-power moments and cubic Hamiltonian are audited
in [`coverage/SECTION_21.md`](coverage/SECTION_21.md). On one common
connected restriction retaining all real sources, the same Section 19
primitive satisfies every clause of Lemma 21.1. At exponent four, the
absolutely and locally uniformly convergent negative cubic series
recovers the original action Hamiltonian; its gradient is the retained
Section 20 frequency throughout the complex source domain. The full
source derivative has an absolutely convergent scalar series. The same
Hamiltonian retains its physical H¹ normalization, sign on its actual
action domain, Hessian, and local concavity. Three printed sign errors
have actual finite-gap or unit-mass source counterexamples.

The original coordinate phases and global physical solutions are audited
in [`coverage/SECTION_22.md`](coverage/SECTION_22.md). The same complex
source domain supports every compact-time coordinate trajectory, with
analytic dependence on the actual original coordinate image. For every
finite p > 1, actual original finite-gap sources refute both printed
phase velocities at every nonzero index. For p ≤ 2 the printed source
flows fail the original physical solution definition. The corrected
flows satisfy that definition, have analytic compact-time source
trajectories and analytic inverse time maps, and characterize all
continuous solutions through their coordinate laws. Corrected Remark
22.3 now holds at every finite exponent above one, and the actual image
condition is exactly when the inverse flow defines a compact-time
solution. Above two, the same family gives local analytic solutions
around every source and global analytic solutions on one invariant
neighborhood of zero. Both scalar-coordinate nonextension statements
and physical forward-time source nonextension use the original data.
Each scalar coordinate is jointly analytic in time and initial
coordinates. The named Section 22 assertions are thus integrated, with
the documented sign correction; Chapter 5's original-map audit is next.

## Canonical coordinate identities on weighted sources

Seven modules extend the actual scalar coordinate derivatives and physical
Poisson brackets to native weighted source spaces for every Section 6
spectral weight and finite p>1. Raw unit Fourier directions are preserved
by the original complex inclusion. Consequently all three canonical
relations, including the literal absolutely convergent mixed Fourier sum,
follow for the actual weighted coordinates even at collapsed gaps.

Scalar complex extensions share one open weighted domain containing the
entire real subspace. One actual Section 14 construction supplies the
canonical relations for all weights. Weighted sequence-valued analyticity,
a bounded weighted Jacobian, local inverses, and weighted inverse continuity
and analyticity remain separate work. See [the Section 14 audit](coverage/SECTION_14.md)
for exact statements and [the implementation status](STATUS.md) for validation.

## Nonextension proof and limits

The proof integrates the quantitative Hessian estimate along real radial
segments twice. Since H*(0) = 0 and its gradient vanishes at zero, this gives
`Re H*(I) ≤ -‖I‖₂²/2` on a small real Hilbert ball. A block of N+1 coordinates,
each equal to `c / sqrt(N+1)`, has ℓ² norm c and ℓ^q norm
`c (N+1)^(1/q-1/2)`. For finite q > 2 the latter tends to zero while the
Hamiltonian remains bounded above by `-c²/2`. Every block is nonnegative and
summable, so agreement with H* contradicts continuity at zero.

The formal statement allows an arbitrary ambient neighborhood U of zero
and requires agreement only for summable nonnegative actions lying in U.
Continuity and C¹ regularity are tested relative to the nonnegative cone.
No ℓ∞ endpoint is asserted in this milestone. Global analytic extension to
all of the nonnegative ℓ² cone, and global strict concavity, are not asserted.

## Accepted source corrections

The previously qualified m=1 case of Lemma 27.2 is now proved with its
printed coefficient in `sourceSection27_hamiltonian_estimate_literal`.
The earlier twice-remainder bound remains valid but is no longer needed as
a replacement. The scalar arithmetic diagnostic records a limitation of
the source proof alone. See [`SOURCE_ERRATA.md`](SOURCE_ERRATA.md) for this
resolved issue and the remaining discrepancies in printed statements or proofs.

## Relative density and limits

[`NonnegativeActionDensity.lean`](NLS/SequenceSpaces/NonnegativeActionDensity.lean)
proves a reusable closure identity: for finite q ≥ 1, every set V containing
all nonnegative summable actions has
`closure (V ∩ nonnegativeLocus q) = nonnegativeLocus q`.
Finite truncations preserve nonnegativity and converge in ℓ^q. Openness of V
then gives relative openness in the positive-cone subtype. This proves the
density assertions without requiring the entire positive cone to lie in V.
It makes no claim of density in the ambient complex space, no density claim
at q=∞, and no global extension or global strict-concavity claim.

## Numbered-statement inventory and spectral overview

[`coverage/statement-candidates.json`](coverage/statement-candidates.json)
indexes 156 distinct candidate numbered labels in the cached text extraction.
It records every matching occurrence, text page and line, and the extraction's
SHA256. Labels in proof references can also match: this is a navigation aid,
not a list of certified statements or completed proofs. It does not replace
an audit of unnumbered definitions, remarks and consequences.

Regenerate with `python3 scripts/source_inventory.py PATH_TO_DISS_TEXT
--output coverage/statement-candidates.json`; add `--check` to verify the
saved inventory without editing it. The source must be the same UTF-8 text
extraction to reproduce its hash and line positions.

[`coverage/SPECTRAL_OVERVIEW.md`](coverage/SPECTRAL_OVERVIEW.md) records the
detailed comparison. Theorem 1.1's unchanged printed source-norm height
and counting conclusions are proved for 1<=p<=4. Its all-exponent claim
is now refuted by actual balanced dyadic sources for every integer
P>=100000000, in the original source norm. Theorem 1.2 and Corollary 1.3 are proved for every finite
p>1, with the actual ordered endpoints, their multiplicities, and the
full locally uniform source bounds. Corollary 1.6's density of actual real
finite-gap sources is also verified. Theorem 1.5 is covered for every
finite p>1; Theorem 1.4 is covered at p=2, but its all-p original-norm
printed height is refuted by an actual Dirichlet spectral counterexample
at p=1024 (and every natural exponent at least 1024). No replacement
height is adopted.

## Appendix C.1 audit

The full-range boundedness assertion is proved by
[`HilbertBoundedness.lean`](NLS/Fourier/HilbertBoundedness.lean), including
the finite-input formula and, through `HilbertSeries.lean`, the convergent
series on every input. The printed isomorphism assertion is now refuted for
every finite p>1 by
[`HilbertNotIsomorphismLp.lean`](NLS/Fourier/HilbertNotIsomorphismLp.lean).
Alternating finite blocks have p-th norm power N+1 and uniformly bounded
transforms. The public results rule out a lower norm estimate, a bounded
linear left inverse, and bijectivity. `sourceLemmaC1_no_linearEquiv` excludes
even an algebraic linear equivalence satisfying the printed series.
The source-level bounded operator and its unique convergent formulas are
packaged in `sourceLemmaC1_bounded`. See
[the focused Appendix C audit](coverage/APPENDIX_C.md).

This is a proved source discrepancy, not a completed proof of the literal
statement. The correction and its precise scope are recorded in
[`SOURCE_ERRATA.md`](SOURCE_ERRATA.md). The argument makes no claim of a
nonzero kernel and leaves boundedness for all 1 < p < infinity intact.

## Appendix C.2 audit

Lemma C.2, printed page 126, is covered with its literal hypotheses by
[`ModifiedHilbertKernel.lean`](NLS/Fourier/ModifiedHilbertKernel.lean) and
[`ModifiedHilbert.lean`](NLS/Fourier/ModifiedHilbert.lean), in `NLS.Fourier`.
The displacement sequences s and r are arbitrary elements of ℓ∞. Their
nodes are sigma_n=pi*n+s_n and rho_k=pi*k+r_k. The hypothesis
`HilbertLatticeSeparated s r c` is precisely
`c^(-1)*|k-n| <= |rho_k-sigma_n|` for k != n, with c>0.

For every 1<p<infinity, `modifiedHilbert` is a continuous complex linear
operator on ℓp. `modifiedHilbert_source_apply` identifies it with
`pi * sum_{k != n} a_k/(rho_k-sigma_n)` on every input;
`summable_norm_modifiedHilbert_source_series` proves absolute convergence.
`norm_modifiedHilbert_le` gives the operator norm bound
`C_p+c*(norm(s)+norm(r))*norm(hilbertSquareCoeffs)`.
`exists_modifiedHilbert_uniform_bound` explicitly chooses the bound before
s and r, uniformly over prescribed upper bounds for their norms.
`sourceLemmaC2` combines that quantifier order with the unique continuous
linear operator and its actual convergent source series on every input.

No smallness, real-valuedness, or ordering of the two displacements is
required. The diagonal is omitted even when rho_n differs from sigma_n.
A common translation of any size recovers the ordinary Hilbert operator,
checking the exact pi normalization. The square-kernel correction also
extends to p=1 and p=infinity; no such endpoint claim is made for the full
operator. Only the valid boundedness part of C.1 is used.

## Appendix D.1–D.3 audit

The declarations in this section are in `NLS.ComplexAnalysis`.
[`SignedProductEstimates.lean`](NLS/ComplexAnalysis/SignedProductEstimates.lean)
uses A=sum(u), S=sum(norm(u)), B=sum(norm(u)^2), and P=prod(1+u).

| Source statement | Public theorem | Scope |
| --- | --- | --- |
| Lemma D.1, p. 126 | `norm_tprod_one_add_sub_one_le_signed_sum` | Exactly `norm(P-1) <= norm(A)*exp(S)+B*exp(S+S^2)`, for absolutely summable complex inputs with norm(u_i)<=1/2. |
| Remark D.2, p. 126 | `norm_tprod_one_add_sub_one_le_exp_sub_one_le` | Both printed inequalities `norm(P-1) <= exp(S)-1 <= S*exp(S)`; individual coefficients need not be small. |
| Remark D.3, p. 127, signed-sum interpretation | `norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` | Exactly `norm(P-1-A) <= norm(A)^2*exp(S)/2+B*exp(S+S^2)` with A the complex sum, including the half-unit boundary. |
| Literal reuse of D.1's A in D.3 | `printed_D3_absolute_linear_term_fails` | An admissible single negative coefficient refutes subtraction of the absolute sum. See `SOURCE_ERRATA.md`; the literal notation is not marked proved. |

The results apply to arbitrary index types and therefore to the printed
integer sequences. Infinite products are unconditional and are justified
by absolute summability. The proof keeps the stronger intermediate bound
`norm(P-exp(A)) <= B*exp(S+B)` before using B<=S^2. The logarithmic remainder
is bounded by B, and the exponential Taylor estimate retains the exact
factor 1/2. Finite cancelling-pair examples check that signed cancellation
is preserved. The D.4–D.9 audit below is scoped to the statements explicitly listed.

### Lemma D.4 and the displaced-root separation assertion

D.4, printed page 127, is now proved for every finite 1 <= p < infinity:

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal deleted product and joint analyticity | `tendsto_appendixDDeletedProduct`, `analyticOnNhd_appendixDDeletedProduct` | Exact source signs and normalization, including p=1. Uniform cutoff convergence on compact spectral sets over bounded displacement sets is supplied by `tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite`. |
| Roots listed with their multiplicities | `analyticOrderAt_appendixDDeletedProduct` | At every complex point, the order equals the cardinality of `displacedRootIndices a z` after erasing the omitted index. No injectivity hypothesis. |
| Simple roots and simple reciprocal poles for a simple sequence | `analyticOrderAt_appendixDDeletedProduct_of_injective`, `meromorphicOrderAt_inv_appendixDDeletedProduct_of_injective` | Every retained root has order one, and the reciprocal has meromorphic order minus one. |
| Meromorphic reciprocal and its printed product formula | `meromorphicAt_inv_appendixDDeletedProduct`, `tendsto_inv_appendixDDeletedProduct` | Meromorphic at every point; the literal negative reciprocal cutoffs converge away from retained roots. |
| Positive separation of simple sequences (preceding D.4) | `exists_uniform_displacedRoots_separation` | A positive lower bound for every distinct pair, for arbitrary injective finite-exponent displacements. No quarter-pi localization assumption. |

`DisplacedProductOrders.lean` uses properness to obtain finite root fibers
and isolating discs, then Rouche stability to pass finite cutoff orders to
the entire limit. `AppendixDProductMultiplicities.lean` also computes exact
meromorphic orders of full and deleted reciprocals, including higher-order
poles. The collision examples at p=1 check a double root, removal of one
occurrence, removal of an unrelated root, and the resulting pole orders.

### Lemma D.5: locally uniform exterior sine asymptotic

D.5, printed page 128, is now proved for every finite 1 <= p < infinity:

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal full product and joint analyticity | `tendsto_appendixDProduct`, `analyticOnNhd_appendixDProduct` | Exact negative product normalization, free value sin(z), including p=1. |
| Prescribed roots | `appendixDProduct_eq_zero_iff`, `analyticOrderAt_appendixDProduct` | Exactly the prescribed roots, counting repeated indices. |
| Source exterior Pi | `appendixDExterior_eq_compl_iUnion_ball` | Exactly the complement of the union of open quarter-pi discs, retaining their boundaries. |
| Uniform exterior error, locally uniform threshold | `exists_local_appendixDProduct_div_sin_bound` | For every a and epsilon > 0, there are eta > 0 and R > 0 that work for every b with norm(b-a) < eta and every exterior z with R <= norm(z). |
| Literal strict supremum inequality | `exists_local_appendixDProduct_div_sin_sup_lt` | The supremum of the quotient error over Pi and norm(z) > R is strictly below epsilon, with the same R for all b in the selected neighborhood. |

`LocallyUniformExteriorResolvent.lean` upgrades strong exterior decay at a
fixed input using the common operator bound. `AppendixDExteriorAsymptotic.lean`
then uses the exponential absolute-product estimate of D.2. The neighborhood
may depend on the tolerance, as in the source's explicit threshold formulation.
There is no injectivity or localization restriction on the displaced roots.
The strict supremum is proved via a uniform half-tolerance bound, rather
than inferred from individual strict inequalities at each spectral point.

Focused examples check the disc boundary, the zero-displacement quotient,
and both neighborhood and supremum estimates at p=1, as well as the
supremum estimate at p=3. D.5 does not settle the separate printed
spectral-height bound above p=2.

### Lemma D.6: relative products for arbitrary bounded reference roots

D.6, printed pages 128-129, is proved for every 1 < p < infinity.
Unlike the earlier free-lattice and spectral-midpoint special cases,
this result allows any bounded reference displacement and any bounded
numerator displacement with ell^p difference. The hypothesis is exactly
the pointwise lower bound on the distant open quarter-pi discs.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Reference separation | `AppendixDReferenceSeparated` | Every point of each disc with abs(n) >= N, every m != n, and the source constant c > 0. |
| Convergence of the omitted ratios | `sourceLemmaD6_multipliable` | Literal ratios for both bounded sequences; vanishing numerator factors are allowed. |
| Uniform ell^p disc error | `exists_appendixDRelativeProductSup_normBall` | A least majorant in ell^p, zero off the selected tail, norm <= C times the actual difference norm. Constants fixed before inputs and cutoffs. |
| Literal powered disc suprema | `sourceLemmaD6PowerSup`, `sourceLemmaD6` | Summability and both sum <= C times norm(difference)^p and the printed sum <= L times norm(difference). |
| Uniformity and the later cutoff N1 | `sourceLemmaD6` | Constants depend only on c, p and the two norm-ball radii; every K >= N is allowed. |

The signed reciprocal row plus a global quadratic product remainder
proves a stronger conclusion than the source's small-tail argument:
no additional cutoff smallness or simplicity of the reference sequence
is needed. Therefore every cutoff satisfying the printed sufficient
condition is covered. The linear-norm displayed right side is proved
literally by absorbing a bounded power of the difference norm into the
norm-ball constant; it is not silently replaced by a p-power right side.
Independent sampling establishes control of all disc suprema at once.

Focused examples use a nonzero constant bounded reference displacement,
check zero perturbations and a vanishing retained numerator, and instantiate
the two-sequence theorem at p=3 with constants preceding both cutoffs.
The following audit treats D.7; later statements still require their own source comparisons.

### Remark D.7: the signed quadratic product remainder

D.7, printed page 129, is proved for every 1 < p < infinity under the
arbitrary-reference hypotheses of D.6. The actual disc-supremum sequence
belongs to ell^(p/2), which is stronger than the printed sum-space result.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Signed linear term | `sourceRemarkD7Remainder`, `sourceRemarkD7Remainder_eq` | Exactly the omitted product minus one minus the sum of (sigma_m-rho_m)/(rho_m-z); no absolute value replaces the signed sum. |
| Literal supremum over each source disc | `sourceRemarkD7Sup`, `sourceRemarkD7_mem` | The norm supremum on the selected open quarter-pi discs is in ell^(p/2), extended by zero on the omitted finite head. |
| Printed ell^(p/2) + ell^(1+) assertion | `sourceRemarkD7` | A half-exponent sequence plus one CoeffOnePlus sequence; the latter can be zero. |
| Uniformity inherited from D.6 | `sourceRemarkD7_uniform` | One bound for both displacement norm balls, chosen before both sequences and cutoffs, valid for every K >= N. |
| Range 1 < p < 2 | `exists_squaredAbsoluteRows`, `exists_appendixDQuadraticSup` | Powered Young and a quasi-norm addition bound avoid imposing a Banach assumption on p/2. |

The global signed product remainder is bounded by exp(S)/2 times
(norm(A)^2+B), with A the complex sum, S the absolute sum, and B the
square sum. The proof compares finite products with exp(A), then passes
to the unconditional limit. This avoids the source proof's small-factor
step and handles vanishing numerator factors. The signed-row square and
the reciprocal-square convolution both lie in ell^(p/2), so no nonzero
ell^(1+) error is needed. The formula in D.7 explicitly subtracts the
signed sum and is unaffected by the D.3 notation correction.

The tail restriction is inherited from the D.6 separation hypothesis;
unseparated head discs may contain poles and are not included in this
claim. Every later cutoff, including a source-admissible small-tail
cutoff, is covered. Focused tests exercise p=3/2 and p=3, large cancelling
factors, zero perturbations, and uniform constants preceding all inputs.
The following audit treats D.8; later source statements remain to be audited.

### Lemma D.8: the two deleted sine-product asymptotics

D.8, printed page 129, is proved for every 1 < p < infinity, for arbitrary
ell^p displacements and all open quarter-pi source discs. There is no
restriction to a distant tail or to simple or small root displacements.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal left-side product and normalization | `tendsto_appendixDNormalizedDeletedProduct` | The positive symmetric product omitting n, divided by pi_n, converges to `jointDeletedSingleSpectralProduct n`; no factor of -2 or pi_n is dropped. |
| Multiplicative sine-product form | `appendixDDeletedProduct_eq_free_mul_relative`, `sourceLemmaD8` | Exact identity with the filled sine quotient and an actual ell^p relative-error sequence, for any independent disc samples. |
| Additive sine-product form | `appendixDDeletedProduct_sub_free_eq`, `sourceLemmaD8` | The same product is the filled quotient plus an actual ell^p additive-error sequence. |
| Uniformity over whole discs and displacements | `sourceLemmaD8_uniform` | Both literal norm-supremum sequences lie in ell^p, bounded by C times the input norm with C fixed on each norm ball. |
| Local uniformity in the displacement | `sourceLemmaD8_locally_uniform` | A common constant on the unit neighborhood of every input, for all independent samples. |
| The printed quotient and its removable center | `sourceLemmaD8_off_center`, `sourceLemmaD8_center` | Exactly sin(z)/(z-pi*n) away from the center, with value cos(pi*n) at the center. |

The finite-cutoff factorization proves the identity even at the free
center. The source's sine quotient is interpreted with its usual removable
extension there; the totalized quotient 0/0 would not have the correct
value. This is an explicit analytic convention, not a claimed equality
with Lean's raw division at zero. The entire deleted product is already
normalized by D.4. D.6 at the free reference lattice supplies the common
relative-error majorant on every disc, and the uniform sine-quotient bound
supplies the additive one. Actual suprema are constructed from these
majorants, rather than inferred from bounds on fixed sample sequences.

Focused checks include the value -1 at a negative odd free center, the
value 1 at zero, invariance under moving only the omitted root, a negative
omitted-index cutoff, p=3 norm-ball bounds, and p=3/2 local uniformity.
The following audits treat D.9 and E.1-E.3; later statements still require source-level comparison.

### Lemma D.9: the full sine-product asymptotic

D.9, printed page 130, is proved for every 1 < p < infinity and arbitrary
ell^p displacements. Every open quarter-pi source disc is included,
with arbitrary independent samples and with no simplicity or smallness condition.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal negative-product normalization | `appendixDProduct_eq_displacedBoundaryProduct`, `sourceLemmaD9_of_cutoff_limits` | The existing negative symmetric cutoff limit is exactly the entire boundary product; the sampled assertion also accepts any function specified by those limits. |
| Restoring the omitted factor | `appendixDProduct_sub_sin_eq_relative_error` | Exact identity `f(z)-sin(z) = -Q_n(z) * (a_n + (sigma_n-z) * error_n(z))`, including the filled center value. |
| Sampled full-product asymptotic | `sourceLemmaD9`, `sourceLemmaD9_mem` | An actual ell^p error for every independent disc sample sequence, including the free centers. |
| Disc-supremum control | `sourceLemmaD9Sup`, `sourceLemmaD9_uniform` | The literal norm suprema belong to ell^p with one bound on every displacement norm ball. |
| Local uniformity in sigma | `sourceLemmaD9_locally_uniform` | One constant on the unit neighborhood of each displacement, uniformly for all independent samples. |

The proof uses the existing entire-boundary disc majorants after identifying
the normalization, then constructs the literal suprema and the sampled error.
The independent restored-factor identity checks the source proof's sign.
Moving only the root at a free center gives minus cos(pi*n) times that
root displacement; focused examples check n=0 and n=-1. Other examples
exercise literal cutoff-defined functions and p=3 and p=3/2 uniform bounds.
No source correction is needed for D.9.

The following audit treats E.1's full interpolation formula, beyond the
earlier zero-sample uniqueness result.

### Lemma E.1: interpolation at arbitrary simple displaced roots

E.1, printed pages 130-131, is proved for every 1 <= p < infinity, with
an explicit correction of the product index m in Z to m != n. The source's
own residue calculation uses the latter. See SOURCE_ERRATA.md.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Entire numerator and literal supremum decay | `appendixESineCircleSup`, `norm_sineQuotient_le_appendixESineCircleSup`, `sourceLemmaE1` | The supremum is over the whole circle of radius N*pi+pi/2; its finiteness is derived, and its limit to zero is the actual hypothesis. |
| Arbitrary simple displaced sequence | `sourceLemmaE1` | Any injective roots pi*n+a_n with a in ell^p; complex roots and p=1 are included. |
| Literal cardinal product | `tendsto_appendixEInterpolationKernel` | The symmetric product of (sigma_m-z)/(sigma_m-sigma_n), omitting n, converges to the ratio of deleted products. |
| Correct residue coefficient | `deriv_appendixDProduct_at_root`, `appendixEInterpolationKernel_eq_deriv` | The full derivative at sigma_n is minus the deleted product divided by pi_n; the coefficient is exactly g(z)/(g'(sigma_n)*(z-sigma_n)). |
| Finite residue identity | `eventually_appendixE_interpolation_error` | All sufficiently large source circles contain precisely the symmetric root block and have the exact derived outer Cauchy error. |
| Vanishing error and convergence | `eventually_appendixE_outerCauchy_small`, `tendstoUniformlyOn_appendixEQuotientInterpolation` | No rate of source decay is assumed; quotient residue sums converge uniformly on bounded zero-free evaluation sets. |
| Full interpolation formula | `sourceLemmaE1`, `sourceLemmaE1_literal` | Symmetric sums converge to f(z) at every z off the root set; the literal version specifies both product and sum cutoffs in one theorem. |

The source contour argument determines symmetric convergence, which is
explicit here. No unconditional `HasSum` or absolute convergence is claimed.
The product index typo is not silently interpreted through division by
zero: `appendixE_all_index_cutoff_eq_zero` checks the obstruction formally.
`appendixEInterpolationKernel_root` gives the cardinal values one and zero.

Focused examples include p=1 and p=3, a negative omitted index, and a
nonreal single-root displacement. The end-to-end sinc example derives
the literal supremum-decay hypothesis and reconstructs the nonzero value
one at z=0 when the zero-index root is moved to i. E.2 and E.3 are audited below.

### Lemma E.2: the identity theorem for real subspaces

E.2, printed page 131, is proved for arbitrary continuous complexifications
on connected open domains that meet the included real space. The necessary
nonempty-real-slice interpretation of "neighborhood" is explicit. The
arbitrary-open-domain reading without that condition is refuted; see
SOURCE_ERRATA.md. Both uses in the dissertation start at real-type potentials.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| An arbitrary real space and its complexification | `RealComplexification` | A continuous real-linear equivalence from R times R to E, with the imaginary axis mapped to i times the included real axis; no isometry or projection-norm restriction. |
| Local uniqueness from the real slice | `DifferentiableOn.eventually_eq_zero_of_continuous_real_form` | Real and imaginary parts need only be continuous at zero, vanish there, and give the decomposition; no contractivity assumption. |
| Connected open domain | `sourceLemmaE2` | Vanishing on the nonempty real slice implies vanishing throughout the domain; no convexity assumption. |
| A neighborhood of a real point | `sourceLemmaE2_of_real_point` | An explicit included real point in the domain supplies the required nonemptiness. |
| Identity of two analytic maps | `sourceLemmaE2_eq` | Real-slice agreement gives agreement on the domain, also for complete complex Banach targets. |
| Necessity of the real-slice hypothesis | `sourceLemmaE2_realSlice_condition_needed` | Constant one on the ball of radius 1/2 about i satisfies real-slice vanishing vacuously but does not vanish on the domain. |
| The actual Fourier source real form | `sourceLemmaE2_realType` | Every finite Banach exponent, including p=1, and a connected open domain containing just one real-type source. |

The coordinate model encodes the usual unique decomposition x+i*y through
a topological real-linear isomorphism. Continuity replaces the older local
helper's contractive projections; the analytic identity theorem replaces
convexity in the global step. The source's Taylor-series proof is thus
replaced by a complex-line uniqueness argument with the same intended scope.

Focused checks use the complex plane with i removed and formally verify
that this domain is connected but not convex. They also check a translated
real base point, a paired complex target, the real-slice obstruction, and
the actual source spaces at p=1 and p=3.

### Lemma E.3: uniform Fourier-Lebesgue bounds for shifted exponentials

E.3, printed page 131, is proved for arbitrary complex frequencies with
|nu_n-n*pi| <= pi/4 outside a finite index block. Every q>1 is covered,
including infinity. No periodic endpoint matching is assumed: the
coefficients are the actual integrals on the unit interval.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Actual Fourier coefficients of exp(i*nu*x) | `exponentialFourierCoefficients_apply` | The coefficient-space element evaluates to the literal unit-interval Fourier integral. |
| Modulation and Fourier normalization | `intervalFourierCoefficient_exponential_modulation`, `intervalFourierCoefficient_exponential_lattice` | Integer modulation shifts the Fourier index; free pi-lattice modes recover the exact overlap integral. |
| Uniformity in the lattice index | `norm_exponential_residual_frequency_le`, `norm_exponentialFourierCoefficients_modulation` | Removing n/2 leaves norm at most 5*pi/4, including negative odd n; modulation preserves the full sequence norm. |
| Reciprocal decay in the printed proof | `norm_intervalFourierCoefficient_exponential_difference` | A common explicit constant bounds the literal difference coefficient by 1/(1+abs(n-2*m)) for every near-lattice index and every Fourier mode. |
| A common tail constant | `sourceLemmaE3_tail` | Positive constant depends only on q, before the sequence and cutoff. |
| Arbitrary finite head | `sourceLemmaE3` | All-index positive norm bound absorbs the unrestricted exceptional frequencies. |
| Literal O(1) conclusion | `sourceLemmaE3_bigO` | Boundedness as the absolute integer index tends to infinity, for every q>1 including infinity. |

Focused examples check q=3/2 and infinity, negative even and odd frequency
normalizations, a complex displacement exactly on the pi/4 boundary, and
a large exceptional imaginary frequency at index zero. No correction to
E.3 is needed. F.1-F.3 are audited below.

### Lemma F.1: critical-point bounds in terms of the periodic gap

F.1, printed pages 131-132, is proved with both printed constants. Its
first part covers every collapsed complex point in a single connected
almost-real domain, and its second part gives a common neighborhood for
all signed indices around each real source. No source correction is needed.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| One complex domain for every index | `exists_local_source_allCriticalGapQuotients_analytic`, `nonempty_sourceCriticalGapAnalyticDomain` | Uniform distant-index analyticity plus finitely many head neighborhoods; the connected domain contains all real sources. |
| Compatibility with earlier choices of W_p | `exists_sourceCriticalGapAnalyticDomain_within` | The domain can be chosen inside any prescribed open set containing the real locus. |
| Continuity without continuous endpoint labels | `SourceCriticalGapAnalyticDomain.continuousAt_gap_norm`, `.analyticAt_offset` | Gap magnitude is the square root of the norm of its analytic square; the exact squared-gap identity gives analytic critical offset. |
| F.1(i): constant 1/2 at a collapsed gap | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_i` | Every complex base point in the domain with zero selected gap; an open neighborhood remains inside that domain. |
| Stronger local collapsed-gap estimate | `SourceCriticalGapAnalyticDomain.exists_collapsedGap_bound` | Any positive constant times gap magnitude is valid on a sufficiently small neighborhood; no division by the gap. |
| Uniform tail control | `exists_local_sourceCriticalOffset_small_gap_tail` | A common cutoff and source neighborhood for any positive linear gap constant, at all positive and negative tail indices. |
| F.1(ii): constant 1 for all indices | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_ii` | One complex neighborhood around each real source, including every collapsed or noncollapsed finite-head gap. |
| Both statements on the same constructed domain | `sourceLemmaF1` | Every finite exponent strictly above one, an open connected domain containing the real locus, and the two source conclusions with literal canonical spectral coordinates. |

The proof uses the already proved exact squared-gap identity instead of
repeating the source's Rouche argument. The quotient is analytic even at
complex collapsed points of the constructed domain. Part (ii) uses real
interlacing to leave a strict margin at open head gaps; collapsed head gaps
use part (i), and a common small tail supplies the remaining indices.
Focused checks include p=3/2 and p=3, a negative index with no real-base-point
hypothesis, exact zero-source values, an actual nonzero real source, and
compatibility with an earlier prescribed domain. F.2 is audited below.

### Lemma F.2: analyticity of the actual endpoint-averaged integral

F.2, printed pages 132-134, is proved for the literal half-sum of two
improper endpoint integrals of Delta′/sqrt_c(Delta^2-4). One source
neighborhood supports every signed gap and every point on its assigned
isolating boundary. Complex collapsed points are included. The statement
is unchanged; two intermediate proof formulas need correction as recorded
in SOURCE_ERRATA.md.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Genuine nonsingular path integrals | `HasPolygonalIntegral`, `exists_hasPolygonalIntegral`, `polygonalIntegral_spec` | Finite sums of actual curve integrals along integrable straight segments; connectors exist on every open connected domain. |
| Genuine improper endpoint integration | `endpointPolygonalIntegral`, `tendsto_polygonalIntegral_endpoint` | Relative limit as the start approaches a singular endpoint through the domain; primitive boundary values give convergence. |
| Actual source differential and endpoint average | `sourceAbelianDifferential`, `sourceAbelianEndpointIntegral`, `sourceAbelianEndpointAverage` | Canonical discriminant derivative and canonical root; both actual periodic endpoints and the factor 1/2 appear in the definition. |
| Nonvacuous endpoint limits | `SourceFullAbelianUniformCauchyFamily.endpoint_mem_closure_rootDomain`, `.tendsto_endpointPolygonalIntegral` | Every endpoint, including a collapsed one, is approached through the cut complement; the limit filter is nontrivial. |
| Equality with the previously constructed primitive | `.endpointIntegral_eq`, `.endpointAverage_eq` | Either endpoint integral equals the full primitive normalized at that gap, hence so does their average. |
| Agreement with conventional admissible paths | `.endpointCurveIntegral_eq` | Every integrable C1 path whose interior avoids the cuts has the same value; no artificial endpoint value of the differential is used. |
| F.2 on each whole boundary circle | `.sourceLemmaF2` | One source ball, every gap and every boundary point, without a nonzero-gap hypothesis. |
| Full almost-real source statement | `sourceLemmaF2` | Connected open domain containing all real sources; every complex point has a common neighborhood supporting all boundary functions and their literal integral identification. |
| Exact free normalization | `sourceAbelianEndpointAverage_zero` | Value -i*nu+i*pi*n at every off-lattice evaluation point, including negative indices and collapsed free endpoints. |

The proof transfers joint analyticity through equality with the canonical
primitive and avoids the problematic dominated-convergence calculation.
The common-path coefficient check and the counterexample to the printed
real majorant are in `AppendixFProofAudit.lean`. Focused examples include
a nonconvex punctured domain, its improper endpoint integral, p=3/2 and
p=3, and nonzero free values. Corollary F.3 is audited below.

### Corollary F.3: analyticity between actual spectral endpoints

F.3, printed page 134, is proved unchanged. The integral is a second relative
endpoint limit of the actual improper polygonal integrals used in F.2.
For an initial endpoint in gap n and a terminal endpoint in gap m, its value
is i*pi*(n-m), including complex collapsed gaps and either endpoint choice.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Actual endpoint-to-endpoint integration | `sourceAbelianEndpointToEndpointIntegral`, `SourceFullAbelianUniformCauchyFamily.tendsto_endpointIntegral` | Iterated relative limits of finite sums of genuine curve integrals; terminal limit convergence is proved. |
| Exact endpoint normalization | `.endpointToEndpointIntegral_eq` | Value i*pi*(n-m) for all signed indices and either endpoint, with nontrivial endpoint filters. |
| Agreement with admissible paths | `.endpointToEndpointCurveIntegral_eq` | Every integrable C1 path with interior off the cuts agrees with the improper definition. |
| Arbitrary endpoint selections | `.endpointToEndpointIntegral_analytic` | Pointwise membership in each endpoint pair is enough; no continuity of the choices or nonzero-gap assumption. |
| Full source statement | `sourceCorollaryF3` | One connected open almost-real domain supports all gap pairs and all pointwise endpoint selections, including every complex base point. |
| Collapsed free normalization | `sourceAbelianEndpointToEndpointIntegral_zero` | Actual integral between pi*n and pi*m at zero equals i*pi*(n-m). |

Focused checks cover p=3/2 and p=3, opposite signs between gaps -3 and 2,
the vanishing same-gap integral, arbitrary predicates switching endpoint
choices, admissible C1 paths, and the common domain. The Appendix G audits
follow below; its existing implementation is not treated as automatic
coverage of every printed statement. The required unresolved p>2 spectral
height is unchanged.

### Lemma G.1: prerequisite stages

Current status: `sourceLemmaG1` now proves the estimate on the full physical
L2 domain in the Hermitian operator norm; see the final G.1 table below.
The following stages record how the earlier domain and norm gaps were closed.

The literal dependence on the potential's Hilbert L2 norm and on the
first Born term's L2 norm in time is now proved for the constructed
continuous-potential solutions. This replaces neither the full printed
L2 domain nor its matrix norm convention. Those requirements are supplied
by the subsequent stages below.

| Required ingredient | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Variable-forcing comparison | `le_forcing_add_exp_integral_mul` | Continuous scalar functions; integrating-factor proof retains terminal forcing and integral of coupling times forcing. |
| Exact L2 coefficient | `integral_mul_le_sqrt_sq_mul_sqrt_sq`, `le_forcing_add_L2_bound` | Actual square integrals give A*exp(A) on [0,T], T<=1; no supplied bound on the error. |
| Actual variable coupling | `classicalNormalizedRemainder_le_firstBorn_add_variable_integral` | Original signed Duhamel equations, with pointwise potential norm inside the integral rather than the potential supremum. |
| Actual first Born time dependence | `continuous_oscillatoryIntegral`, `continuous_classicalFirstBornVector`, `classicalNormalizedFirstBorn` | Continuity proved from the literal oscillatory integral, without differentiating the potential. |
| Hilbert L2 potential budget | `classicalPotentialL2Norm`, `sqrt_integral_potential_norm_sq_le` | Integral of the sum of both coordinate norm squares; controls every truncated pointwise-norm square integral. |
| Actual vector solution estimate | `classicalNormalizedRemainder_le_L2_firstBorn` | All continuous potentials, complex spectral parameters, initial vectors, and times in [0,1]; no nonzero-frequency or smoothness restriction. |
| Actual matrix estimate | `classicalNormalizedMatrixRemainder_le_L2_firstBorn` | Both columns of M-E and of the actual first Born matrix, explicitly using the elementwise maximum matrix norm. |
| Arbitrary L2 potentials | Completed in later stages below | L2-stable extension, original integral equation, and full estimate. |
| Matrix norm | Hermitian operator norm proved below | The convention is explicit in the related author preprint; the 2014 edition of [23] has not been checked directly. |

Checks include an actual nonzero triangular potential at zero frequency,
both-coordinate Hilbert norm sqrt(2), a variable potential (t,0) with
Hilbert L2 norm sqrt(1/3), free zero error for every complex frequency,
and a scalar exponential solution with time-dependent forcing. No source
erratum is asserted by this partial G.1 audit.

The related author preprint [Normal form theory for the NLS equation,
arXiv:0907.3938](https://arxiv.org/pdf/0907.3938), printed page 7,
explicitly uses the matrix operator norm induced by the Hermitian vector
norm. Its Lemma 2.1 (printed page 12) gives the variable-forcing estimate.
This supplies a concrete next target: use Euclidean vector/operator norms,
without multiplying the printed coefficient by a norm-equivalence constant.
The 2014 book [23] is a later publication, so its convention has not been
verified directly from that edition.

### Lemma G.1: Hermitian operator norm, continuous-potential stage

The genuine Hermitian operator-norm estimate is now proved, with the literal
Hilbert L2 coefficient A*exp(A). This closes the norm gap in the preceding
continuous-potential result. The arbitrary-L2 domain is supplied by the
subsequent extension and limit passage below.

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Genuine Hermitian vectors | `hermitianPair_norm`, `hermitianPair_norm_sq` | Euclidean norm on both complex coordinates, using WithLp 2. |
| No norm-conversion loss | `hermitianPair_norm_diagonal_le`, `norm_classicalHermitianDuhamelKernel_le` | Direct diagonal and off-diagonal bounds with coefficient one and the correct signed free exponential. |
| Exact off-diagonal operator norm | `norm_hermitianColumns_offDiagonal` | Maximum of the two scalar magnitudes. |
| Actual vector integral identity | `classicalHermitianRemainder_duhamel` | Transport of both original signed Duhamel equations, through a continuous linear equivalence used only for algebra and integration. |
| Actual vector Volterra bound | `classicalHermitianRemainder_le_firstBorn_add_integral` | Weighted Hermitian vector norm with the original pointwise potential coefficient. |
| Actual operator identification | `classicalHermitianRemainderOperator_eq_matrix`, `classicalHermitianFirstBornOperator_eq_matrix` | Operators are precisely M-E and the actual first Born matrix. |
| True induced operator norm | `classicalHermitianOperator_le_L2_firstBorn` | All initial vectors are bounded before taking the operator norm; exact A*exp(A) coefficient and actual first Born L2 time integral. |
| Exact first Born formula | `classicalNormalizedHermitianFirstBorn_eq` | The off-diagonal operator norm is the maximum of the oscillatory integral magnitudes. |
| Arbitrary L2 potentials | Proved in later stages below | Density, stability, the original equations, and passage of G.1 to the physical L2 space. |

The Hermitian convention is explicit on printed page 7 of the related
author preprint [arXiv:0907.3938](https://arxiv.org/pdf/0907.3938). The 2014
book [23] has not been read directly. Checks distinguish this operator norm
from the entrywise maximum, attain the signed kernel bounds in both
half-planes, and exercise zero time, arbitrary complex free frequency,
and a nonzero potential at zero frequency. No extra factor is accepted in
place of the printed coefficient.

### Lemma G.1: physical L2 stability and uniform extension

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Exact physical norm | `norm_continuousPotentialL2Class`, `dist_continuousPotentialL2Class` | Hilbert sum of both coordinate square integrals, with no normalization factor. |
| Full physical L2 density | `denseRange_continuousPotentialL2Class`, `exists_continuousPotential_L2_approximation` | Arbitrary a.e. L2 classes; no periodicity or endpoint condition. |
| Quantitative solution stability | `norm_classicalSolution_sub_le_L2`, `dist_classicalSolutionCurve_le_L2` | Actual classical solutions, uniformly in time and on L2-bounded potential sets. |
| Uniform extension exists | `cauchy_classicalSolutionCurve_L2`, `tendsto_classicalSolutionCurve_L2` | Convergence proved before relying on the limit; all physical L2 potentials and complex spectral parameters. |
| Approximation independence | `tendsto_solutionCurve_of_tendsto_L2` | Every approaching family, along any filter, has the same uniform limit. |
| Exact recovery and normalization | `l2SolutionCurve_of_continuous`, `l2SolutionCurve_zero`, `l2SolutionCurve_free`, `l2SolutionCurve_zero_initial` | Entire classical curves, arbitrary initial values, zero initial vector, signed free solution. |
| L2 growth bound | `norm_l2SolutionCurve_le` | Uniform curve norm bounded by ||v|| exp(||z||+||u||_2). |
| Original L2 equation and G.1 | Proved in later stages below | The original equations and the full Hermitian estimate are now proved. |

The uniform-limit construction is now supplemented by the actual integral
and a.e. differential equations in the next stage. Its defining convergence
alone was not counted as proof of those equations. Public checks include a discontinuous
step potential through `intervalL2OfFunction`, distinct approaching
sequences, both potential coordinates, and the free frequency signs.

### Lemma G.1: the original equation for arbitrary physical L2 potentials

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual scalar integral pairing | `intervalL2_integral_mul_eq_inner`, `continuous_intervalL2_integral_mul` | Ordinary representative-based integrals on [0,t]; joint continuity in L2 and uniform norms via an exact Hilbert inner-product identity. |
| Coefficient integrability | `intervalIntegrable_l2ODECoefficient` | Any physical L2 potential times any continuous vector curve. |
| Continuity of the original vector integral | `continuous_l2ODEIntegral` | Both signed coordinates; potential and curve vary together, for every fixed complex z and t in [0,1]. |
| Exact classical recovery | `classicalSolutionCurve_eq_l2ODEIntegral`, `l2ODEIntegral_of_continuous` | The actual previously constructed classical Volterra equation. |
| Original L2 Volterra equation | `l2SolutionCurve_eq_integral`, `l2SolutionCurve_eq_integral_ofFunction` | The constructed L2 limit solves the original equation at every time, for every complex z and initial vector. |
| Original differential equation | `ae_hasDerivAt_l2SolutionCurve` | Actual derivatives of the curve extension almost everywhere on the physical interval. |
| Physical spectral equation | `ae_physicalOperator_l2SolutionCurve`, `ae_physicalOperator_l2SolutionCurve_ofFunction` | L_phi y = z y with actual coordinate derivatives and any original L2 representative. |
| Full G.1 estimate | Proved in the final stage below | Actual L2 first Born operator, uniform convergence, and passage of the Hermitian bound with the literal coefficient. |

These results require neither pointwise convergence of L2 representatives
nor a continuous representative of the potential. Public checks directly
compute the signed coefficient integral for a discontinuous two-component
step and instantiate both the original integral and differential equations.
No claim of full dissertation completion follows from this milestone.

### Lemma G.1: full physical L2 domain and literal Hermitian estimate

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Uniform L2 primitive | `intervalL2PrimitiveCLM`, `norm_intervalL2_integral_mul_le` | Actual integrals of representatives; bounded complex-linear map to the uniform curve norm. |
| Actual oscillatory integrals | `l2OscillatoryCurve_apply`, `l2OscillatoryCurve_apply_ofFunction` | Exact original kernels with signed complex frequencies and arbitrary L2 inputs. |
| Actual first Born operator and matrix | `l2HermitianFirstBornOperatorCurve_apply`, `l2HermitianFirstBornOperatorCurve_eq_matrix`, `l2HermitianFirstBornOperatorCurve_ofFunction` | Signed off-diagonal entries are the original oscillatory integrals; independent of null-set changes. |
| Genuine Hermitian norm | `l2NormalizedHermitianFirstBorn_eq`, `l2NormalizedHermitianFirstBorn_ofFunction` | Exact maximum of the two scalar oscillatory integral magnitudes; no dimension factor. |
| Uniform first Born convergence | `continuous_l2HermitianFirstBornOperatorCurve`, `continuous_l2NormalizedHermitianFirstBorn` | Continuity from physical L2 potentials into operator and real curves with the uniform norm. |
| Actual square integral convergence | `continuous_curve_squareIntegral`, `integral_l2NormalizedHermitianFirstBorn_sq_of_continuous` | The literal time integral in G.1, with exact classical recovery. |
| Actual remainder M-E | `l2HermitianRemainderOperator_eq_matrix`, `tendsto_classicalNormalizedHermitianRemainder_L2` | Constructed L2 solution columns with the original integral and a.e. differential equations and identity initial matrix. |
| Printed estimate | `sourceLemmaG1`, `l2HermitianOperator_le_L2_firstBorn` | [0,1] × Complex × physical L2; exact weight exp(-|Im z|t), coefficient ||phi||_2 exp(||phi||_2), and actual first Born L2 time norm. |
| Exact classical recovery | `l2FundamentalMatrix_of_continuous`, `l2NormalizedHermitianRemainder_of_continuous`, `l2HermitianFirstBornOperatorCurve_of_continuous` | Existing actual matrices and operators are retained exactly. |

The source formula and domain were checked against printed page 135. A
noncontinuous two-component step is exercised with exact norm one, exact
terminal first Born norm one half, and the literal coefficient exp(1).
The full dissertation is still incomplete. Lemma G.2 requires a separate
comparison of its H1 norm convention, arbitrary time range, and precise
constants; the existing broader Sobolev bounds do not establish it verbatim.


### Lemma G.2: trace and derivative estimate; source norm comparison open

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Cauchy--Schwarz length factor | `integral_norm_le_sqrt_length_mul_L2` | Every t >= 0, arbitrary scalar L2 function; exact sqrt(t). |
| Integration by parts with L2 derivative | `norm_oscillatoryIntegral_weighted_le_L2` | Absolutely continuous functions; actual endpoint values and square integral of the derivative. |
| Actual Hermitian first Born operator | `intervalHermitianFirstBornOperator_weighted_le` | Any nonnegative time and any nonzero complex frequency; no matrix norm conversion factor. |
| Exact existing operator recovery | `intervalHermitianFirstBornOperator_of_continuous`, `intervalHermitianFirstBornOperator_eq_l2` | Equality with the classical operator and with the physical L2 operator of any original representative. |
| Numerical factor (2+sqrt(t))/(2\|z\|) | `intervalHermitianFirstBornOperator_weighted_le_of_trace_L2_bound` | Explicit common bound on both traces and coordinate derivative L2 norms; not an assumed Sobolev embedding. |
| Remainder consequence of G.1 | `l2HermitianRemainder_le_of_firstBorn_uniform`, `l2HermitianRemainder_le_of_firstBorn_uniform_unit` | Full physical L2; exact coefficient, with an optional sharper sqrt(t) factor. |
| Explicit size S | `classicalHermitianFirstBorn_le_traceL2Size`, `classicalHermitianRemainder_le_traceL2Size` | S is exactly max(sup norm(phi), norm(phi_-')_2, norm(phi_+')_2); constants (2+sqrt(t))/(2*abs(z)) and 3/(2*abs(z))(1+c_phi). |
| Physical H1 inputs | `classicalHermitianRemainder_sobolev_le_traceL2Size` | All physical period-two H1 Fourier pairs; regularity proved, no additional AC or derivative premises. |
| Printed interval H1 norm | **Unresolved** | Need its precise convention and a trace/derivative comparison on [0,t]. S is not declared equal to that norm. |

The source was checked at printed page 135. Printed page 103 explicitly
uses the periodic Fourier norm with weights (1+|2*pi*n|)^s; it does not
define the norm on arbitrary intervals [0,t]. A comparison with the combined
endpoint/derivative bound may be needed; a constant-one bound on each
component of S is not presumed. The related author preprint
[arXiv:0907.3938](https://arxiv.org/pdf/0907.3938), printed page 15, defines
the interval Sobolev space via distributional derivatives but does not settle
the required norm comparison in that definition. Its numbering differs from
the cited 2014 book, which has not been read directly. No source discrepancy
is asserted by this milestone. Existing coarse Fourier-norm estimates and
the explicit size S do not establish the literal printed H1 bound.


### Lemma G.2: integral H1 norm and the arbitrary-time interpretation

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Explicit scalar H1 energy | `intervalH1Norm`, `intervalH1Norm_sq` | Unnormalized integral of squared function and derivative magnitudes. |
| Existing energy compatibility | `NLS.Fourier.intervalH1Norm_eq_sqrt_energy` | Exactly the square root of the pre-existing physical squared energy on [0,t]. |
| Explicit Hilbert pair norm | `intervalPairH1Norm_eq_integral` | Exactly the square root of the sum of all four component integrals, with no norm-equivalence constant. |
| Combined trace estimate | `endpoint_variation_le_sample`, `endpoint_variation_le_integrals`, `endpoint_variation_le_three_H1` | Every t in [0,1], complex AC functions with L2 derivatives; no periodicity requirement. |
| Unit-interval Born bound | `intervalHermitianFirstBornOperator_weighted_le_unit_H1` | Actual Hermitian operator; coefficient 3/(2*abs(z)); original H1 functions. |
| Unit-interval remainder consequence | `l2HermitianRemainder_le_unit_H1` | Actual physical L2 solution; same coefficient and exact factor 1+norm(phi)_2 exp(norm(phi)_2). |
| Physical Fourier H1 inputs | `classicalHermitianRemainder_sobolev_le_unit_H1` | No extra AC/derivative premises; actual integral H1 norm retained. |
| Exact constant kernel | `oscillatoryIntegral_const`, `oscillatoryIntegral_neg_const`, `oscillatoryIntegral_const_quarter_period` | Original oscillatory integral and both frequency signs. |
| Arbitrary-time first inequality under the integral convention | `lemmaG2_firstBorn_integralNorm_counterexample`, `g2IntegralNormTestPotential_admissible` | Strict failure for smooth period-one phi=(1,0), t=1/4, z=2*pi; actual left side 1/(2*pi), right side 5/(16*pi). |
| Source's precise interval norm | **Still unresolved** | The counterexample concerns the explicit integral norm only. The unit-interval consequence is independently proved under that convention. |

The endpoint estimates are combined before integration: their variation sum
is at most 2 times the L1 function norm plus 2 times the L1 derivative norm.
Cauchy--Schwarz yields the needed constant three in H1. This avoids assuming
that individual point evaluations have norm at most one. The comparison with the source's
periodic Fourier convention on printed page 103 is proved in the next stage
below. The
arbitrary-time first inequality is not silently replaced or marked complete.


### Lemma G.2: unit-interval estimate in the exact periodic source norm

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Physical unit-period Parseval | `hasSum_sq_periodOneCoefficient`, `integral_sq_periodOneSobolevSynthesis` | Arbitrary L2 interval functions, then every original H1 Fourier input; no factor two. |
| Actual derivative energy | `integral_sq_deriv_periodOneSobolevSynthesis`, `intervalH1Norm_sq_periodOneSobolevSynthesis` | Actual classical derivative, with multiplier 2*pi*i*n at every signed frequency. |
| Original H1 source | `sourcePeriodicH1Potential_coefficients`, `periodic_sourcePeriodicH1Potential` | Both original sequences recovered, actual period-one representative; all complex H1 pairs. |
| Exact Chapter 5 norm | `sourcePeriodicH1_fourierNorm_sq` | Exactly the sum with weights (1+abs(2*pi*n))^2 and both component energies. |
| Constant-one comparison | `graphEnergy_le_sourcePiSobolev_one`, `intervalPairH1Norm_sourcePeriodic_le` | Integral H1 norm <= exact source norm, with no larger constant. |
| Physical/source L2 normalization | `norm_sourcePeriodicH1L2Class` | Original physical L2 norm equals the original source coefficient Hilbert norm. |
| Uniform Born estimate on [0,1] | `sourceLemmaG2_firstBorn_unit` | Actual Hermitian operator, coefficient 3/(2*abs(z)), exact periodic source norm. |
| Unit-interval G.2 remainder estimate | `sourceLemmaG2_remainder_unit` | Actual L2 fundamental solution; exact printed factors and Chapter 5 periodic norm. |
| Existing classical recovery | `sourcePeriodicH1Potential_eq_classical`, `sourcePeriodicH1L2Class_eq_classical`, `sourceLemmaG2_classical_remainder_unit` | Equality with the period-doubled classical curve and the same actual M-E estimate. |
| Arbitrary-time local-norm first inequality | **Still separate** | Not asserted by these unit-interval theorems. The qualified integral-norm counterexample remains valid. |

The periodic source norm is the one explicitly defined on printed page 103.
The comparison preserves its exact coefficient in G.2; equality is tested
on a constant 3-4 pair. The source space is identified through the existing
coefficient-preserving bijection `higherSobolevSourceOneEquiv`, rather than
restricted to a subset of Fourier inputs. The following milestone audits
G.3, with an explicit qualification of the singular epsilon endpoint.


### Lemma G.3: full matrices, exact source balls, and endpoint qualification

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual full matrix Fourier coefficients | `classicalHermitianRemainderFourierCoefficients_apply`, `classicalHermitianShiftedFreeFourierCoefficients_apply` | Bochner integrals of M-E_z and M-E_x; genuine Hermitian operator norm at each Fourier mode. |
| Original period-one H1 inputs | `sourceG3ClassicalCoefficients_potential`, `norm_sourceG3ClassicalCoefficients_le` | Actual source potential recovered on [0,1]; one uniform coefficient bound on each exact Chapter 5 source-norm ball. |
| Full-matrix physical H1 time norm | `sourceLemmaG3_H1` | Actual derivative and integrals; uniform O(1) under eventual bounded displacement from n*pi. |
| Near-free Fourier-Lebesgue decay | `sourceLemmaG3_fourier_decay` | Exact exponent, 0 < epsilon < 1, 1+epsilon <= q <= 2; one common cutoff for each ball and displacement tail. |
| Shifted-free comparison | `sourceLemmaG3_shiftedFree_decay` | Full M(nu_n)-E_(n*pi), with the stronger eventual O(1/abs(n)) displacement hypothesis. |
| q=2 endpoints | `sourceLemmaG3_l2_decay`, `sourceLemmaG3_shiftedFree_l2_decay` | Explicit inverse-index decay, with no epsilon parameter or singular quotient. |
| Printed epsilon=1 expression | **Qualified** | It is 0/0 at its only admissible q=2; no interpretation is assigned. See SOURCE_ERRATA.md. |

Both signed tails are covered, with unrestricted finite initial segments.
The fixed assembly factor four and coefficient-ball conversion factor two
are displayed in the bounds; neither changes the source's Big-O exponents.
A concrete off-diagonal Fourier mode checks that the sequence uses the
actual operator norm (four for entries three and four), rather than the
sum of entry norms. The source-ball domain is all complex H1 via the
existing bijective coefficient identification, not just real sources.

The full dissertation remains incomplete. The G.4 audit follows below;
G.2's arbitrary-time local norm, the remaining p>4 spectral height, and the
optional original m=1 sharpening retain their previously recorded status.


### Corollary G.4: full-matrix summability on exact source-norm balls

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Literal eventual pi/4 displacement | `sourceCorollaryG4` | One nonnegative lp majorant for the full matrix norms at all signed indices, uniform on each exact Chapter 5 source-norm ball. |
| Full shifted-free comparison | `sourceG4_shiftedFree_uniform_majorant` | Actual M(nu_n)-E_(n*pi), eventual O(1/abs(n)) displacement, arbitrary finite initial spectral values. |
| Uniform tails over spectral families | `sourceG4_remainder_tail_majorant`, `sourceG4_shiftedFree_tail_majorant` | The cutoff and summable majorant precede the spectral sequence and potential quantifiers; common displacement bound and initial cutoff. |
| Whole-sequence membership | `sourceG4_remainder_memlp`, `sourceG4_shiftedFree_memlp` | The actual full-matrix Fourier norms are in lp for every complex period-one H1 source. |
| Actual operator-valued membership | `sourceG4_remainder_operator_memlp`, `sourceG4_shiftedFree_operator_memlp` | The Fourier sequences themselves, with values in the Hermitian-operator coefficient space, form an lp sequence. |
| Complete exponent range | All preceding theorems | Finite real p>1, q>1+1/p, including q>2 and q=infinity; no threshold equality or excluded outer endpoints claimed. |

The source statement on printed page 137 fixes a spectral sequence before
asserting uniformity over potential balls. The whole-sequence majorant may
therefore depend on its finite initial values. The tail statements are
stronger uniform-family results, but do not impose a common bound on
unrestricted finite initial segments. This distinction is explicit in the
quantifier order. The generic near-free majorants allow any O(1) bound,
with the literal pi/4 hypothesis supplied by the source specialization.

Focused checks exercise q=3/2, q=2, q=infinity, a non-Hilbert outer p=3/2,
an arbitrary complex initial spectral value, an actual nonzero 1/abs(n)
displacement, and a common majorant chosen before the spectral family.
G.5's reference and endpoint audit is recorded below.
The dissertation remains incomplete; the previously recorded G.2 local-norm,
p>2 spectral-height, and optional original m=1 obligations remain open.


### Lemma G.5: literal-reference and infinity-endpoint audit

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual off-diagonal free gradients | `sourceG5_actual_i_free_upper`, `sourceG5_actual_i_free_lower` | Upper minus component and lower plus component, agreeing with the proof but opposing the printed statement. |
| Original source and both frequency hypotheses | `sourceG5_zero_admissible`, `sourceG5_printed_upper_lattice` | Zero period-one H1 potential, nu_n=n*pi, both printed references equal at every signed index. |
| Literal finite p=2 claim | `sourceG5PrintedUpperErrorCoefficients_diagonal`, `not_memlp_sourceG5PrintedUpperError_norms` | Actual scalar Fourier integral has modulus one at mode n; the norm sequence is not in l2. |
| Full-matrix implication and arbitrary finite exceptions | `not_memlp_sourceG5PrintedError_majorant`, `not_eventually_sourceG5PrintedError_majorant` | No l2 majorant of this component exists, even on any spectral tail. |
| Independent printed infinity endpoint | `sourceG5_triangular_coefficients`, `sourceG5_not_eventually_fourier_l1` | Original smooth period-one H1 source (1,0); a diagonal component fails Fourier l1 at every perturbed lattice index, independently of the off-diagonal reference correction. |

The source formula needs the two off-diagonal superscripts exchanged.
Even with this correction the printed outer p=infinity endpoint fails.
The corrected finite-p full-gradient estimate on exact source-norm balls
is now proved by the full assembly described below. This uses all eight
scalar components and the actual gradient-valued Fourier integrals.
See `SOURCE_ERRATA.md` for the literal formulas and proof discrepancy.
These findings do not change the unresolved G.2 local-norm and remaining
p>4 spectral-height obligations or the optional original m=1 sharpening.


### Corrected G.5: full-gradient summability on exact source-norm balls

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Full gradient and actual coefficients | `classicalHermitianGradientFourierCoefficients_apply` | Actual Bochner Fourier integral of i times the gradient error; induced norm from Hermitian potential directions to Hermitian matrix operators. |
| Corrected reference identification | `classicalHermitianGradientError_eq_correctedReference` | Exact matrix identity with the upper minus and lower plus component, for any complex source and both frequency arguments. |
| Exact signed lattice reference | `classicalHermitianCorrectedFreeGradientMatrix_lattice` | (-1)^n phase, signed +/-2n waves, and arbitrary potential directions; negative indices included. |
| First finite-p source assertion | `sourceLemmaG5_corrected` | Every finite p>=2, q=p/(p-1), eventual pi/4 displacement, one nonnegative lp majorant on each exact periodic source H1 ball. |
| Second finite-p source assertion | `sourceLemmaG5_shifted_corrected` | Exact lattice reference and eventual O(1/abs(n)) displacement, with the same source-domain and uniformity scope. |
| Generalized exponents | `sourceG5_gradient_uniform_majorant`, `sourceG5_shifted_gradient_uniform_majorant` | Every finite p>1 and q>1+1/p, including inner q=infinity; no outer p=infinity claim. |
| Whole-sequence membership | `sourceG5_gradient_memlp`, `sourceG5_shifted_gradient_memlp`, and the corresponding `norms_memlp` theorems | Actual gradient-valued Fourier sequences and their full operator Fourier norms belong to outer lp, including arbitrary finite initial spectral values. |
| Zero-source consistency | `classicalHermitianGradientError_zero`, `classicalHermitianGradientFourierCoefficients_zero` | Exact cancellation against the actual free reference, at every complex frequency and all q>1. |

A fixed factor eight assembles the scalar bounds in the full induced norm.
The source potential is reconstructed through the existing period-doubling
identification, and its classical coefficient norm is bounded by twice
the exact source norm. The majorant is chosen after fixing the spectral
sequence and before choosing a potential in the ball. No common bound on
arbitrary finite initial spectral values is silently imposed. Both G.5
assertions are proved with the explicit reference correction and finite
outer exponent restriction; the two printed failures remain documented.
G.6 is covered below. The dissertation remains incomplete, with the previously
recorded G.2 local-norm, remaining p>4 spectral-height, and optional original
m=1 obligations unchanged.


### Corollary G.6: exact source norms and the corrected wave reference

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Discriminant assertion | `sourceCorollaryG6_discriminant` | Unchanged assertion for every finite p>=2, conjugate q, eventual pi/4 displacement, exact H1 source ball and exact finite-q signed pair output norm. |
| Anti-discriminant assertion | `sourceCorollaryG6_antiDiscriminant_corrected` | Same exponent and norm scope, eventual O(1/abs(n)) displacement, reference wave subscripts corrected from -2*n*pi to -2*n. |
| Actual signed Fourier coefficients | `sourceG6DiscriminantCoefficients_fst`, `sourceG6DiscriminantCoefficients_snd`, and the anti-discriminant counterparts | Actual scalar Fourier integrals of i times the gradient or gradient remainder; the first physical index is -k and the second is k. |
| Exact equation (1.2) norm | `sourceG6DiscriminantCoefficients_norm_rpow`, `sourceG6AntiDiscriminantCoefficients_norm_rpow` | Combined coefficient energy for finite q, with the signed first-index reversal. |
| Uniform generalized bounds | `sourceG6_discriminant_sourceNorm_majorant`, `sourceG6_antiDiscriminant_sourceNorm_majorant` | Finite p>1 and finite q>1+1/p; one nonnegative summable majorant for all potentials in the exact source ball. |
| Coefficient-valued membership | `sourceG6_discriminant_source_memlp`, `sourceG6_antiDiscriminant_source_memlp` | The actual signed pair coefficient sequences belong to outer lp; arbitrary finite initial spectral values are included. |
| Vector Bochner integral interpretation | `classicalHermitianDiscriminantGradientCoefficients_apply`, `classicalHermitianAntiDiscriminantGradientCoefficients_apply`, `classicalHermitianAntiDiscriminantGradientCoefficients_lattice` | Separate Hermitian-vector coefficient representation and the actual corrected reference, including negative indices. |
| Printed-reference failure | `half_le_norm_sourceG6PrintedAntiErrorCoefficients`, `not_memlp_sourceG6PrintedAntiError_norms`, `not_eventually_sourceG6PrintedError_majorant` | At zero potential and exact lattice frequencies, the inner l2 norm is at least 1/2 for every nonzero n; no finite spectral head repairs outer l2 summability. |
| Failure in the exact source norm | `not_memlp_sourceG6Printed_pair_norms` | The same obstruction in the exact signed source pair norm, regardless of the second component. |

The majorant is chosen after fixing the spectral sequence and before the
potential. No uniform bound on arbitrary finite initial spectral values is
imposed. The source is the full complex period-one H1 domain, with no
smallness or reality restriction. The separate Hermitian-vector extension
allows inner q=infinity; no exact-source infinity output norm is claimed
here. The source's finite conjugate range is fully covered.

The printed second reference is refuted at p=2 under the source's own wave
definition; the first assertion remains unchanged. See `SOURCE_ERRATA.md`.
G.7's domain and printed wave indices are audited below.
The previously recorded G.2 local-norm, remaining p>4 spectral-height, and
optional original m=1 obligations remain open. Neither declaration counts
nor the source-label inventory certify completeness.


### Lemma G.7: actual spectral gradients and the corrected half-wave reference

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original complex H1 source | `sourceG7_periodic_representative` | Every original period-one Sobolev source supplies the required physical Sobolev representative; no separate compatibility assumption. |
| Both finite-p estimates | `sourceLemmaG7_corrected`, `sourceLemmaG7_corrected_with_coefficients` | Finite p>=2 and conjugate q; for each exponent one common open complex domain contains the entire real source locus. All signed indices and collapsed periodic gaps are retained. |
| Actual midpoint derivative | `sourceG7MidpointGradient_coefficients` | Exact signed coefficients of the Frechet derivative of the canonical periodic midpoint; first direction k and second direction -k. |
| Actual corrected Dirichlet gradient | `exists_sourceG7_dirichlet_coefficients`, `SourceG7DirichletCoefficients` | Actual Fourier integrals of the normalized squared eigenfunction gradient minus (wave(2*n),wave(-2*n))/2, on the same domain as the summability theorem. |
| Exact source norm | `norm_sourceG7SignedCoordinates`, `sourceG7DirichletGradientError_norm_rpow` | First-index reflection is an isometry; the norm power is the combined Fourier coefficient energy from equation (1.2). |
| Entire real H1 locus | `sourceLemmaG7_real_corrected` | Both estimates at every real H1 source, with no smallness assumption. |
| Correct free reference | `classicalDirichletNormalizedGradient_free_lattice`, `sourceG7_free_signed_coefficients`, `sourceG7DirichletGradientError_zero` | Exact factor one half, physical indices 2*n and -2*n, signed source index -n in both components, and exact cancellation of the actual free derivative. |
| Printed-reference failure | `quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients`, `not_eventually_sourceG7PrintedError_majorant` | Actual error norm at least 1/4 for every nonzero n at the zero H1 source; outer p=2 fails even after removing an arbitrary finite head. |
| Exact-norm obstruction | `not_memlp_sourceG7Printed_pair_norms` | Failure in the exact signed source pair norm, regardless of the second component. |

The exponent is finite, with q conjugate to p. The complex neighborhood
may depend on p, and the same neighborhood supports both estimates and
the actual corrected Fourier-integral representation. These are pointwise
H1 source estimates; no new uniform bound on all source balls in that
neighborhood is asserted. The midpoint assertion is unchanged, and the
Dirichlet reference is explicitly corrected from -2*n*pi to -2*n.
See `SOURCE_ERRATA.md` for the zero-source counterexample.

Appendix H's recurrence/homogeneity statement is covered below; its subsequent
integration-by-parts formulation is the next audit. The G.2 local-norm, remaining p>4 spectral-height,
and optional original m=1 obligations remain open. Neither source-label
inventories nor declaration counts certify completeness.


### Lemma H.1: the canonical weak density on the printed Sobolev source

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original H^(k-1) source | `weakSobolevRiccatiDensity`, `analyticAt_weakSobolevRiccatiDensity` | Every integer k=s+1>=1 and every complex period-one H^s pair; the next actual recurrence density belongs to H^-1 and depends analytically on the source. |
| Actual recurrence | `weakSobolevRiccatiDensity_apply`, `weakRiccatiNonlinear` | Weak derivative of the last L2 Riccati density plus actual double Fourier convolutions; all nonlinear factors retain at least H1 regularity. |
| Smooth identification | `weakSobolevRiccatiDensity_eq_classical_coefficients` | Exact Fourier integrals of the independently defined classical density u_(s+2), for every smooth periodic pair. |
| Full-source extension | `denseRange_sobolevSourceOfFinsupp`, `eq_of_continuous_of_smooth_sobolevSource`, `weakSobolevRiccatiDensity_unique` | Finite Fourier polynomials are dense in the complex H^s source; the weak density is the unique continuous extension of the actual smooth hierarchy. |
| Leading derivative and polynomial | `sourceLemmaH1`, `sourceLemmaH1_weak` | Coefficientwise and H^-1 equality: u_(k+1)=-b^(k)+q_k, with the exact multiplier 2*pi*i*j and actual lower-jet polynomial. |
| Every polynomial restriction | `sourceLemmaH1_polynomial` | Total weight k+1; after multiplication by the first field, equal field counts and total derivative count at most k-2; each remainder jet has order at most k-2. |
| Actual nonlinear Fourier integral | `sourceH1RemainderCoefficient_eq_integral`, `sourceH1RemainderL2_apply` | The remainder has the actual unit-period Fourier integrals of the continuous polynomial field, assembled in L2. |
| Distributional interpretation | `weakRiccatiDistribution_derivative`, `sourceLemmaH1_distribution`, `sourceH1RemainderDistribution_coefficient` | Faithful period-one tempered-distribution synthesis; the leading derivative is the actual distributional derivative and the remainder keeps its physical coefficients. |
| Low-order endpoints | `weakSobolevRiccatiDensity_zero_apply`, `weakSobolevRiccatiDensity_one_apply` | u2=-b' for H0 inputs; u3=-b''+a*b^2 for H1 inputs, using actual convolutions. |

The displayed kth derivative is weak at the printed H^(k-1) regularity.
The construction covers all k>=1; for k=1 the remainder polynomial is
zero, so its negative derivative-count bound is meaningful. No real-type,
smallness, or extra smoothness restriction is imposed. The polynomial is
canonical and independent of the input. The distributional realization
preserves the original period-one normalization, including negative modes.

H.2's full H^m statement is covered below. The G.2 local-norm, required p>2
spectral-height, and optional original m=1 obligations retain their status.
The source inventory and declaration count do not certify completeness.


### Corollary H.2: one polynomial and the physical integral on every real H^m source

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| One polynomial before all inputs | `sourceCorollaryH2` | For every m>=1, there exists a single polynomial giving the displayed integral for every real H^m source. |
| Jet order, homogeneity, field balance | `sourceH2Polynomial_properties` | Jets through m-1, total weight 2m+2, field charge zero; all for the same canonical chosen polynomial. |
| Highest physical derivative | `memLp_sobolevTopJetPhysical`, `periodOneCoefficient_sobolevTopJetPhysical` | Actual derivative of the penultimate H1 representative; square integrability and exact period-one coefficients on every H^m source. |
| Actual weak-derivative hierarchy | `hierarchySobolevJetL2_distribution_succ`, `hierarchySobolevJetL2_distribution_iterate` | Every available jet equals successive Mathlib tempered-distribution derivatives of the zeroth jet. |
| Exact physical square integral | `integral_sq_sobolevTopJetPhysical` | Unit-interval Parseval, including nonsmooth data, with no lost normalization factor. |
| Single real integral | `sourceCorollaryH2_integral` | Squared physical top derivative plus the continuous lower-jet polynomial, integrated over the original unit period. |
| Complex extension | `sobolevOddHamiltonian_eq_physical_integral` | Bilinear physical top-derivative integral plus the same polynomial, for every complex H^m pair. |
| Original smooth meaning | `sobolevTopJetPhysical_eq_classical`, `sobolevOddHamiltonian_unique_continuous` | Pointwise classical derivative agreement on smooth inputs; unique continuous Hamiltonian extension on complex H^m. |

The polynomial and Hamiltonian are the existing physical constructions;
no replacement by an action sum or an input-dependent polynomial occurs.
The lower jets of real inputs are pointwise conjugates by the existing
`hierarchySobolevJetContinuous_real` theorem. There is no source correction
for H.2. Appendix I's Schur-complement hypotheses are the next audit.
The G.2 local-norm, remaining p>4 spectral-height, and optional original
m=1 obligations remain open. Counts are not completeness certificates.


### Appendix I.1-I.2: the missing hypothesis and the original operator

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Identity terms and signs | `sourceSchur_apply`, `one_add_block` | S=Id+A-B*(Id+D)^(-1)*C; the identity shifts both diagonal blocks. |
| Corrected I.1 equivalence | `sourceLemmaI1_corrected` | Arbitrary complex Banach blocks, assuming Id+D has a bounded inverse; no finite-dimensional restriction. |
| Valid printed direction | `sourceLemmaI1_sufficient` | Invertibility of Id+D and S implies invertibility of Id+T. |
| Printed forward implication | `sourceLemmaI1_printed_false` | Refuted on C times C: Id+T is coordinate exchange while Id+D is zero. |
| I.2's lower inverse | `source_lower_isUnit_of_norm_lt_one` | The exact strict norm bound gives a bounded inverse by Neumann series. |
| I.2 determinant condition | `sourceCorollaryI2`, `sourceCorollaryI2_iff` | Finite-dimensional first block, arbitrary Banach second block; the printed sufficient condition and the equivalence under its norm bound. |
| Original Banach space | `source_operator_isUnit_iff`, `sourceLemmaI1_on_decomposition`, `sourceCorollaryI2_on_decomposition` | Any bounded direct-sum coordinate equivalence realizing T; conclusions concern Id+T on Z itself. |
| Strict-bound check | `sourceCorollaryI2_boundary_counterexample` | At norm(D)=1 a nonzero Schur determinant alone is insufficient; no refutation of the printed strict version. |

I.1's unrestricted statement is refuted, not proved by silently adding an
assumption. Its corrected form and the unchanged I.2 criterion are proved.
The polynomial and physical H.2 results above remain unchanged. Next is
I.3's full total-boundedness characterization, followed by I.4. The G.2
local-norm, remaining p>4 spectral-height, and optional original m=1
obligations remain open. Counts do not certify completeness.


### Lemma I.3: arbitrary sets, finite exponents, and weighted norms

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Full equivalence | `Coeff.sourceLemmaI3` | Every subset of l^p for 1<=p<infinity; pointwise coefficient bounds and one uniform N>=1 for each epsilon>0. |
| No hidden norm-bound hypothesis | `isBounded_of_pointwise_tail`, `totallyBounded_iff_pointwise_uniform_finite_tails` | The global norm bound is derived from the printed assumptions before applying finite-rank compactness. |
| Necessity uniformly over sets | `tendstoUniformlyOn_norm_tail_of_isCompact` | Decreasing continuous tail norms converge uniformly on compact sets by Dini; applies to the compact closure of any totally bounded set. |
| Exact symmetric cutoffs | `sourceI3Tail_apply`, `sourceI3Tail_eq_fourierTail` | Retains |n|<=N; complement equals the existing `fourierTail (N+1)`. Both signed boundary frequencies are tested. |
| Compactness and relative compactness | `Coeff.sourceLemmaI3_compact`, `Coeff.sourceLemmaI3_compactClosure` | Add closedness for compactness; the same printed criterion characterizes compact closure. |
| Original weighted source | `WeightedCoeff.sourceLemmaI3`, `WeightedCoeff.sourceLemmaI3_compact` | Every positive weight and every finite exponent; raw pointwise bounds and exact weighted tail norm, including all real Sobolev orders. |
| Full compact-operator output | `exists_sourceI3Tail_comp_norm_le`, `tendsto_sourceI3Tail_comp` | Arbitrary complex normed input space; entire output tails vanish in operator norm for compact operators, uniformly for all larger cutoffs. |
| Endpoint and hypothesis checks | `AppendixI3FullSetChecks` public examples | p=1, signed boundaries, weighted p=3, escaping unit vectors, and the compact constant-one singleton in l-infinity. |

The printed I.3 is proved unchanged. The operator consequence supplies the
initial tail estimate for I.4; it does not claim I.4's full real-analytic
or generic local-diffeomorphism conclusion. The relative-cone argument and Schur signs are covered below. G.2's local-norm, remaining p>4 spectral-height, and
optional original m=1 obligations remain open. Counts do not certify
completeness.


### Proposition I.4: relative-cone density and the Schur signs

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Boundary uniqueness | `eventuallyEq_of_nonnegative_agreement`, `eventuallyEq_of_nonnegative_restriction` | All finite Banach exponents; relative agreement on nonnegative sequences determines an ambient holomorphic germ, including at zero. |
| Relative density | `subset_closure_of_nonnegative_local_analytic_nonvanishing` | Local scalar criteria on the cone subtype; preconnected source domain, with no ambient-interior assumption. |
| Local compact Fredholm families | `open_dense_isUnit_of_nonnegative_analytic_compact_shift` | Local operator-valued extensions; compactness only at original cone parameters; one invertible point gives a relatively open dense invertible locus. |
| Intrinsic complexified derivative | `NonnegativeAnalyticAtlas.derivative_eq`, `derivative_hasLocalAnalyticExtensions` | Derivative independence and local analytic dependence follow from cone uniqueness and original-map agreement. |
| Actual local-inverse seed | `isUnit_fderiv_iff_localInverse`, `open_dense_localInversePoints_of_nonnegative_atlas` | One actual two-sided analytic local inverse implies a relatively open dense set of such points. |
| Original cone-map recovery | `open_dense_localInverse_of_nonnegative_atlas` | Both ambient extension inverse identities, inverse derivative, and the original map's left-inverse identity as a relative germ. |
| Atlas-independent locus | `NonnegativeAnalyticAtlas.localInversePoints_eq_of_atlas` | Changing local analytic extensions does not change which source points have local inverses. |
| Printed Schur signs | `sourceI4_printedSchur_false_positive`, `sourceI4_correctSchur_zero` | Finite-dimensional false positive for the displayed determinant; the corrected signs detect singularity. This does not refute I.4's conclusion. |

The source of these new theorems is the nonnegative cone in unweighted
l^p for every 1<=p<infinity. The openness and closure statements use its
relative topology, so the zero boundary and arbitrary zero coordinates
are included. The conclusion concerns inverses of local complex analytic
extensions, and agreement with the original cone map is proved. Only local
extensions are required; they need not be chosen as one global map.

Weighted complex and real transport, and the construction of the complex
atlas from real-analytic germs, are proved in the later entries below.
The G.2 local-norm, remaining p>4 spectral-height,
and optional original m=1 obligations retain their status. Source-label
inventories and declaration counts do not certify completeness.


### Proposition I.4: original weighted spaces at every real order

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original positive cone | `WeightedCoeff.mem_nonnegativeLocus_iff`, `nonnegativeHomeomorph` | Positivity of raw coefficients is equivalent to positivity after weighting; the full cone, including zero, is identified homeomorphically. |
| Local extension transport | `localAnalyticExtensions_transport`, `WeightedCoeff.HasLocalAnalyticExtensions.toCoeff` | Local germs are transported by compatible continuous parameter maps and ambient complex linear coordinates; no global extension assumption. |
| Weighted Fredholm density | `WeightedCoeff.open_dense_isUnit_of_nonnegative_analytic_compact_shift` | Every positive weight and finite Banach exponent; compactness only at original parameters, on the original operator space. |
| Intrinsic weighted derivative | `WeightedCoeff.NonnegativeAnalyticAtlas.derivative_eq`, `derivative_hasLocalAnalyticExtensions` | Original weighted derivatives are independent of local extension choices and locally analytic as operators. |
| One actual inverse as seed | `WeightedCoeff.open_dense_localInversePoints_of_nonnegative_atlas` | A relatively open dense local-inverse locus from one two-sided local inverse and compact derivative minus identity. |
| Original-space inverse identities | `WeightedCoeff.open_dense_localInverse_of_nonnegative_atlas` | The inverse maps the weighted space to itself; both extension identities, original cone-map recovery, and inverse derivative are proved. |
| Arbitrary real Sobolev order | `AppendixI4WeightedChecks` public examples | Instantiation at `Weight.sobolev s` for every real s, p=1 at zero, and arbitrary finite exponent; no nonnegative-order restriction. |
| Nonconstant boundary check | `AppendixI4WeightedChecks.rawCoordinateFamily` | The raw-coordinate scalar operator family is singular at zero and has an open dense invertible locus for every positive weight. |

All weighted statements use raw coefficients and the existing weighted norm.
No comparison constants, boundedness assumption on the weight, or compactness
hypothesis off the nonnegative cone have been added. The local inverses are
currently complex ambient inverses of the original weighted extensions.
Restriction to real sequence spaces is proved below for both unweighted
and weighted spaces. The real-analytic-to-complex-atlas representation
bridge is proved in the final I.4 entry below.
The previously recorded G.2, p>2 spectral-height, and optional original m=1
obligations remain open; counts do not certify completeness.


### Proposition I.4: actual real inverses and a real seed, unweighted

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Reality from original cone values | `eventually_realLocus_of_nonnegative_analytic`, `NonnegativeAnalyticAtlas.extension_eventually_real` | Local complex extensions preserve the full nearby real locus, derived from real values on the original cone, including at zero. The reality lemma also covers the infinite exponent. |
| Real derivative and inverse | `fderiv_entries_real_of_eventually_real`, `inverse_mapsTo_realLocus_of_real_entries` | Real matrix entries and preservation of the real locus by the inverse derivative; the latter uses finite p. |
| Preservation by nonlinear inverse | `eventually_mem_closedSubmodule_of_localInverse`, `exists_real_localInverse_of_nonnegative_atlas` | The actual complex inverse preserves nearby real targets; no extra inverse-reality assumption. |
| Actual real sequence maps | `realRestriction_localInverse`, `exists_realRestriction_localInverse_of_nonnegative_atlas` | Real analytic maps between `RealCoeff p` spaces, both inverse identities, center identity, and recovery of the original cone map. |
| Real inverse seed | `isUnit_fderiv_of_real_localLeftInverse`, `NonnegativeAnalyticAtlas.realLocalInversePoints_eq` | A differentiable real left inverse plus compact derivative minus identity yields an invertible complex derivative. The real and complex local-inverse loci coincide. |
| Real open dense conclusion | `sourcePropositionI4_real_unweighted`, `sourcePropositionI4_real_of_differentiable_seed` | Relatively open dense real analytic inverse locus on a relatively open preconnected cone domain at every finite Banach exponent. |
| Nonlinear boundary example | `AppendixI4RealChecks` | A quadratic coordinate perturbation at p=1 has an actual real analytic inverse at zero with both identities; generic examples check the real analytic and merely differentiable seed APIs. |

These results use local complex extension atlases to represent analyticity
at the cone boundary. The reality required to restrict those extensions and
their inverses is proved from the original cone values. The subsequent
entries transport the real conclusion, inverse locus, and seed to all
positive weights and construct the atlas from actual real-analytic germs.
The G.2 local-norm, remaining
p>4 spectral-height, and optional original m=1 obligations remain unchanged.


### Proposition I.4: real inverses in every positive weighted space

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original weighted real Banach space | `WeightedRealCoeff`, `WeightedRealCoeff.im_eq_zero`, `WeightedCoeff.mem_realSubmodule_iff` | Closed subspace with real raw coefficients and the original inherited weighted norm; complete at every Banach exponent. |
| Compatible real coordinates | `coordinateRealEquiv`, `val_coordinateReCLM`, `realRestriction_linear_conjugate` | Real inclusion and projection, recovery of real original values, and compatibility of real restriction with complex weighting. |
| Original compactness | `WeightedCoeff.NonnegativeAnalyticAtlas.toCoeff_derivative`, `toCoeff_compact` | Derivative conjugacy and compactness of derivative minus identity in normalized coordinates, from the original cone hypotheses only. |
| Actual real inverse locus | `WeightedCoeff.NonnegativeAnalyticAtlas.realLocalInversePoints_eq`, `realLocalInversePoints_eq_of_atlas` | Real and complex inverse loci coincide; the real locus is intrinsic to the original cone map. |
| Real weighted density | `WeightedCoeff.sourcePropositionI4_real_weighted` | One actual real local inverse implies a relatively open dense real inverse locus for all positive weights and finite Banach exponents. |
| Differentiable real starting inverse | `WeightedCoeff.sourcePropositionI4_real_weighted_of_differentiable_seed` | The initial real map need only be differentiable and a left inverse; the resulting inverse points have analytic two-sided real inverses. |
| Both real identities and original recovery | `WeightedCoeff.NonnegativeAnalyticAtlas.exists_real_localInverse` | Actual maps `WeightedRealCoeff w p -> WeightedRealCoeff w p`, with analyticity, center identity, both local inverse identities, and recovery of the original cone map. |
| Nonlinear check in arbitrary weights | `AppendixI4WeightedRealChecks` | A quadratic raw-coordinate perturbation has compact derivative minus identity, an inverse at the zero boundary, and an open dense real inverse locus for every positive weight. Both inverse identities are checked. |

The weight is only required to be strictly positive. All real Sobolev orders
are included, and no global upper or lower bound on the weight is assumed.
Only local complex extension atlases are used; compactness is assumed at
original cone points. The real transport obligation is now complete.
The following entry constructs those atlases from real-analytic germs and
closes this final representation obligation. The separate
G.2 local-norm, remaining p>4 spectral-height, and optional original m=1
obligations retain their status. Counts do not certify completeness.


### Proposition I.4: real-analytic germs and the original real derivative

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Complexify real coefficients | `Complexification.complexifyLinear`, `complexifyMultilinear`, `norm_complexifyMultilinear_apply_le`, `complexifyMultilinear_real` | Continuous complex multilinear extensions, agreement on real arguments, degree-n norm bound 2^n. |
| Extend real-analytic germs | `half_radius_le_complexifySeries`, `exists_complex_extension_of_analyticAt`, `exists_complex_extension_in_coordinates` | At least half the original radius; full real-neighborhood agreement at arbitrary real centers, also at p=infinity. |
| Identify the actual derivative | `complexifyRealMap_real`, `fderiv_eq_complexifyRealMap`, `realGermComplexExtension_fderiv` | Complex derivative equals complexification of the original real derivative. This is proved, not assumed. |
| Original real analyticity | `WeightedCoeff.NonnegativeRealAnalyticAtlas`, `toComplex`, `toComplex_restriction`, `toComplex_derivative` | Real analytic neighborhood extensions of the cone map yield the needed complex atlas and preserve full real germs. |
| Preserve the original inverse locus | `HasAnalyticInverse.congr`, `toComplex_realLocalInversePoints`, `complexifiedDerivative_eq`, `localInversePoints_eq_of_atlas` | The conclusion concerns the original real extensions, and the derivative and inverse locus are intrinsic. |
| Proposition I.4 | `WeightedCoeff.sourcePropositionI4_real_analytic` | Relatively open dense real inverse locus from one real local inverse, for all positive weights and finite Banach exponents; compactness only at cone points. |
| Original differentiable seed | `sourcePropositionI4_real_analytic_of_differentiable_seed` | A differentiable real left inverse suffices; analytic two-sided inverses result on the generic locus. |
| Both identities and source recovery | `NonnegativeRealAnalyticAtlas.exists_localInverse` | Actual real maps, both inverse identities on real neighborhoods, and recovery of the original cone map. |
| Nonlinear real-input checks | `AppendixI4RealAnalyticChecks` | A directly defined real quadratic map has compact complexified derivative minus identity, a real inverse at zero with both identities, and an open dense inverse locus for arbitrary positive weights. |

This completes I.4 with real-neighborhood extensions as the meaning of
real analyticity and local diffeomorphism at cone boundary points. No
ambient-interior, global complex-extension, or off-cone compactness
hypothesis is introduced. The source's path-connected domain is covered
by the weaker preconnected-domain hypothesis. All real Sobolev orders are
included. The density theorem keeps 1<=p<infinity; the separate extension
construction also permits p=infinity. The printed Schur sign error remains
recorded in `SOURCE_ERRATA.md`.

G.2's arbitrary-time local norm and the remaining p>4 spectral height remain
open; the original unrestricted m=1 sharpening remains optional and
unresolved. The dissertation is incomplete, and statement counts do not
certify completeness.


### Lemma G.2: arbitrary-length integral-norm bound and necessary scaling

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Length-dependent trace bound | `endpoint_variation_le_sample_interval`, `endpoint_variation_le_integrals_interval`, `endpoint_variation_le_length_H1` | Every T>0 and t in [0,T]; combined endpoints and variation bounded by 2*sqrt(1/T+T) times the integral H1 norm. |
| Actual all-time Born bound | `intervalHermitianFirstBornOperator_weighted_le_interval_H1`, `intervalHermitianFirstBornOperator_weighted_le_local_H1` | Original Hermitian operator, arbitrary nonzero complex frequency, all finite nonnegative times; local version uses T=t and handles zero separately. |
| Exact constant family | `g2IntegralNormTestPotential_norm_length`, `oscillatoryIntegral_const_half_phase`, `g2IntegralNormTestPotential_firstBorn_length` | Smooth period-one (1,0), every t>0, frequency pi/(2t), norm sqrt(t), actual Born norm 2t/pi. |
| Necessary length dependence | `lemmaG2_integralNorm_length_necessary`, `lemmaG2_integralNorm_no_uniform_numerator` | Any bound B(t)/(2|z|) in the integral norm requires B(t)>=2/sqrt(t); no fixed numerator suffices. |
| Sharp leading short-time coefficient | `intervalH1_length_factor_normalized`, `tendsto_intervalH1_length_factor_normalized` | Ratio of the sufficient numerator to the necessary lower bound equals sqrt(1+t^2) and tends to one from the right at zero. |
| Public checks | `AppendixG2LengthChecks` | Full interval theorem, arbitrary-length constant inputs, affine input on [0,4], zero time, exact values, the impossibility theorem, normalized limit, and the unit-length coefficient comparison. |

The integral H1 norm is exactly the previously defined integral energy,
with no length normalization. This entry supplies an explicit correction
candidate, not a proof of the printed coefficient under an unspecified
norm convention. The printed arbitrary-time G.2 interpretation remains
unresolved. The exact periodic-norm unit-interval theorem remains valid;
the remaining p>4 spectral height and optional original m=1 sharpening also
retain their status. None of these counts or examples certify completion
of the dissertation.


### Theorem 1.1 / Proposition 3.1: unchanged printed height through p=4

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Preserve the conjugate root | `norm_punctured_reciprocal_le_of_power_bound`, `norm_reciprocal_le_conjugate_root` | All finite conjugate pairs; retain the reciprocal-envelope coefficient 2*(2/(q-1))^(1/q). |
| Constant-eight free bound | `reciprocal_power_coefficient_le_four`, `freeL1Bound_le_height_eight` | Every 1<=p<=4, with the central inverse-height term retained. |
| Printed height and its edges | `mem_resolventSet_of_printed_height_up_to_four`, `abs_im_lt_printed_height_up_to_four` | Arbitrary complex potentials and norm balls; unchanged (1+8M)^p, both horizontal edges, strict spectral exclusion outside. |
| Exact source norm | `sourceSpectrum_abs_im_lt_printed_height_up_to_four` | Original period-one source with its component-sum norm, including p=4. |
| Full common-neighborhood counting | `exists_source_periodicCounting_printed_height_of_resolvent`, `exists_source_periodicCounting_printed_height_up_to_four` | One open convex neighborhood and every sufficiently large cutoff; central count 4N+2, disk counts two, parity, exhaustion, and analytic actual projections. |
| Distinguish criterion failure from spectral failure | `PrintedHeightFourChecks` | At p=3 and norm bound one the coarse test exceeds one, while the actual resolvent exists at 729i; p=4 checks include the negative edge and source central count. |
| Remaining limitation | `reciprocal_power_coefficient_four_fails_at_five` | Constant-four power-sum test fails at p=5; no spectral counterexample or all-exponent completion follows. |

This extends the required result beyond two without changing the printed
height or source norm. The full finite-exponent statement remains unresolved
above four. The all-exponent alternative height is not substituted for it.
The detailed source-scope audit is in `coverage/SPECTRAL_OVERVIEW.md`.
G.2's interval-norm interpretation and the optional original m=1 sharpening
retain their status. The dissertation remains incomplete.


### Theorem 1.2 and Corollary 1.3: full source periodic asymptotics

| Source requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Literal full eigenvalue displacement series | `sourcePeriodicEndpointEnergy_sum`, `sourceTheorem1_2` | Summability and one positive full-series bound on an open convex source neighborhood, every finite p>1. |
| Ordered actual eigenvalues with multiplicities | `sourceTheorem1_2_ordered_labels`, `PeriodicEndpointLabeling.exhaustive`, `CentralPeriodicLabeling.count_eq` | Both global lexicographic inequalities, all central repetitions, distant disk multiplicities, and exact original spectrum. |
| Choice-independent labels | `PeriodicEndpointLabeling.eq_canonicalPeriodicEndpoints` | Any admissible cutoff and complete ordered enumeration give the same endpoints. |
| Literal midpoint and gap membership | `sourceCorollary1_3_mem` and the displacement evaluation identities | Actual midpoint minus n*pi and unsquared gap in lp, without a smaller exponent range. |
| Joint local uniformity | `sourceCorollary1_3` | One source neighborhood and positive norm bound for both sequences; arbitrarily small tails at all larger cutoffs. |
| Public scope checks | `SourcePeriodicOverviewChecks` | General finite p, p=5, original multiplicities, literal series and sequences, coincident free roots. |

Both printed statements on p. 19 are covered unchanged. The neighborhoods
use the original finite-p source norm. No global constant over all
potentials or continuity of the sorted individual endpoints is claimed.
The construction does not depend on the unresolved printed height above
four. See `coverage/SPECTRAL_OVERVIEW.md` for the requirement-by-requirement
audit. The boundary-spectrum overview comparison is recorded below.
G.2's interval norm and the remaining height ranges are still open; the
dissertation is incomplete.


### Corollary 1.6: actual real finite-gap density

The source statement on p. 21 is covered by the existing
`exists_mem_sourceFiniteGapLocus_norm_sub_lt` and
`dense_sourceFiniteGapLocus` for every finite p>1. The underlying locus
uses finitely many nonzero actual canonical periodic gaps in the real
source space. Real spectral closing approximants converge in the original
finite-p pair norm, and the singleton-strip criterion proves their actual
finite-gap property. Existing public checks cover p=3 approximants and
density at p=2 and p=3/2. The detailed audit is recorded in
`coverage/SPECTRAL_OVERVIEW.md`. The unrestricted complex regularity
sentence is refuted below. Real-type spatial real analyticity is now
proved separately in `SourceFiniteGapAnalyticRealization.lean`, as recorded
in the latest entry below.


### Theorems 1.4 and 1.5: Hilbert box, all-p asymptotics, and a height counterexample

| Source requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Actual ordinary boundary spectra | `periodOneBoundaryPotential`, `BoundaryCondition.spectrum`, `sourceBoundarySpectrum_closed_discrete` | Same reflected source potential, two boundary restrictions, closed and discrete for every finite p>1. |
| One common neighborhood and cutoff | `exists_uniform_sourceBoundaryLabels` | Both canonical sequences and every larger cutoff, original source topology, full multiplicities and displacement norm bounds. |
| Reality of every eigenvalue | `sourceBoundarySpectrum_im_eq_zero` | Every real-type source, either condition, all central and distant points. |
| Exact printed height at p=2 | `norm_periodOneBoundaryPotential_two_le`, `sourceBoundarySpectrum_abs_im_lt_printed_height_two` | Original source norm and constant eight; spectrum strictly inside both horizontal edges. |
| Printed-box counts and exhaustion at p=2 | `sourceTheorem1_4_two` | Central count 2N+1, one simple root per high disk for either condition, no other roots, one neighborhood and all larger cutoffs. |
| Full Theorem 1.5 | `sourceTheorem1_5_mem`, `sourceTheorem1_5` | Both literal lp sequences and a common full-series bound for every finite p>1 and every complex source. |
| Canonical ordering and multiplicities | `monotone_canonicalPeriodOneBoundaryRoots`, `canonicalPeriodOneBoundaryRoots_multiplicity` | Global lexicographic order and all actual repetitions, independent of initial labels. |

Theorem 1.5 is covered unchanged. Every clause of Theorem 1.4 is covered
at p=2, but its all-p printed height is now refuted. The finite potential
`triangularNormalizedCoefficients P`, for every natural P>=1024, has source
norm at most 3/32 and an actual Dirichlet eigenvalue at i*2^P. The eigenvalue
escapes the printed box and every stated disk at every cutoff.
`sourceBoundaryPrintedHeight_counterexample` proves that assertion;
`not_sourceTheorem1_4_printed_exhaustion` negates the all-source exhaustion
statement at p=1024. No substitute spectrum, extended norm, or failed
sufficient estimate is used. See `SOURCE_ERRATA.md` and
`coverage/SPECTRAL_OVERVIEW.md`. No replacement height is adopted.
Theorem 1.1's periodic height above four remains unresolved, and the
dissertation remains incomplete.

Validation: the full project check passed (6592 build jobs), including all
public examples and the axiom audit of 27502 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Proposed boundary-height correction and necessary exponent dependence

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Retain the interval-extension loss | `norm_periodOneBoundaryPotential_le` | Reflected maximum pair norm bounded by E_p times the original source norm, all finite p>1. |
| Explicit sufficient source height | `mem_boundaryResolventSet_of_sourceBoundaryExplicitHeight`, `sourceBoundarySpectrum_abs_im_lt_explicit_height` | `(1+8*p*E_p*M)^p` on every original source norm ball; both ordinary boundary conditions, including the horizontal edges. |
| Corrected counts and exhaustion | `sourceTheorem1_4_proposed_height` | One open convex neighborhood containing the source and zero; every larger cutoff; original central count 2N+1, simple high roots and no other roots. |
| Necessary growth of any height coefficient | `sourceBoundaryCountingHeightCoefficient_necessary` | C_P>=P/96 for integer P>1, even with source-dependent cutoffs. |
| No fixed replacement for eight | `not_exists_uniform_sourceBoundaryCountingHeightCoefficient` | Negates all-source exhaustion for all integer exponents for every fixed nonnegative coefficient. |

The new sufficient height is recorded as a proved proposed correction,
not an adopted replacement for Theorem 1.4. The printed p=2 theorem and
all-p Theorem 1.5 remain unchanged. The periodic height above four is a
separate unresolved obligation. No optimality or whole-source completion
is certified.

Validation: the full project check passed (6594 build jobs), including all
public examples and the axiom audit of 27521 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Unnumbered finite-gap regularity: unrestricted complex reading refuted

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Actual triangular periodic inverse | `triangularResolvent_spectralPencil`, `spectralPencil_triangularResolvent` | Original one-derivative domain; any triangular coefficient potential; every finite Banach exponent; no smallness. |
| Full free spectrum | `periodicSpectrum_triangular`, `sourcePeriodicSpectrum_triangular` | Equality with the whole free lattice, including the original period-one source embedding. |
| Literal finite-gap property | `finite_canonicalPeriodicGap_triangular`, `roughTriangularSource_finite_gap` | Finite set of nonzero actual canonical indexed gaps for every finite p>1. |
| A rough source in the original space | `roughTriangularSource` | First coefficients 1/(1+|n|), second component zero; belongs to every finite lp with p>1. |
| Failure of smooth and analytic realizations | `roughTriangularCoefficients_no_smooth_representative`, `roughTriangularCoefficients_no_analytic_representative` | No periodic physical representative with the same Fourier coefficients has the claimed regularity. |
| Scope separation | `roughTriangularSource_not_realType`, `not_every_complex_finiteGap_source_smooth` | Refutes the unrestricted complex reading; preserves the existing real-type regularity and density results. |

The statement audited is the unnumbered sentence on printed p. 21, not
Corollary 1.6's real-type density theorem. Real-type spatial real
analyticity is now proved in the later analytic-realization entry. The
complex counterexample uses no proposed
replacement definition of finite gaps or of the periodic spectrum.
The dissertation remains incomplete.

Validation: the full project check passed (6596 build jobs), including all
public examples and the axiom audit of 27550 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Spatial translation: prerequisite for real-type finite-gap analyticity

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Translation in the original norms | `Coeff.spatialTranslation`, `WeightedCoeff.spatialTranslation`, `sourceSpatialTranslation`, `continuous_sourceSpatialTranslation` | Isometric equivalences, source group law, and joint continuity at every finite exponent. |
| Actual domain-to-base operator conjugacy | `domainInclusion_spatialTranslation`, `potentialMul_spatialTranslation`, `spectralPencil_spatialTranslation` | Original one-derivative domain and convolution, including p=1. |
| Full intrinsic spectral data | `mem_periodicRootSpace_spatialTranslation`, `periodicRootSpaceTopTranslationEquiv`, `periodicAlgebraicMultiplicity_spatialTranslation`, `periodicSpectrum_spatialTranslation` | All chain lengths, actual multiplicities, and the entire periodic spectral set. |
| Source normalization and indexing | `periodOnePotential_spatialTranslation`, `sourceCanonicalPeriodicEndpoints_spatialTranslation`, `sourceCanonicalPeriodicGap_spatialTranslation` | Original period-one coefficients and both complete canonical endpoint sequences; every finite p>1, with no index shift. |
| Real finite-gap translation orbit | `sourceSpatialTranslation_realType`, `sourceSpatialTranslation_closedGapTail`, `sourceSpatialTranslation_mem_sourceFiniteGapLocus` | Real type and exactly the same closed-gap cutoff survive every real displacement. |
| Physical spatial sign and scale | `Fourier.continuousSynthesis_spatialTranslation`, `Fourier.periodOneSynthesis_spatialTranslation`, `Fourier.periodOneCoefficient_translated_synthesis` | The action is f(x+t), in both periods, for arbitrary absolutely summable coefficients. |

The translation lemmas supply the fixed-gap-tail curve used in the
analytic-realization proof below. They do not assume or conclude
exponential coefficient decay. The complex counterexample and the other
unresolved source obligations are unchanged.

Validation: the full project check passed (6601 build jobs), including all
public examples and the axiom audit of 27610 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Unnumbered finite-gap regularity: real-type spatial analyticity proved

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Finite-dimensional analytic reconstruction | `exists_analyticAt_sourceFiniteGap_finiteReconstruction` | Local weighted lift factors through finitely many original Fourier coefficients; previous weighted-lift APIs retained. |
| Analytic target without analytic source assumption | `analyticAt_sourceTranslationFiniteTarget`, `sourceTranslationFiniteTarget_ofReal` | Entire complex-time finite target equals the exact weighted block of the real spatial translation. |
| Weighted lift of the same translated source | `exists_analyticAt_sourceFiniteGap_translationLift` | Analytic near time zero; decoding equals the actual original translation, using the unchanged canonical gap tail. |
| Bounded physical evaluation | `sourceOneDerivativeWeight_double`, `normalizedSobolevSourceL1`, `normalizedSobolevSourceEvaluation` | Exactly the original one-derivative weight after embedding; bounded l1 decoding and physical evaluation at every finite p. |
| Analyticity of the existing representative | `analyticOnNhd_sourceFiniteGapPhysicalPair` | Both original coefficient-preserving physical functions are real analytic on all of R, for every real-type finite-gap source at finite p>1. |
| Full qualified source assertion | `sourceFiniteGap_exists_analytic_representative` | Real analyticity, period one, and every original Fourier integral, without finite Fourier support or an extra regularity assumption. |

This completes the real-type reading of the regularity sentence on
printed p. 21. Its unrestricted complex reading remains refuted, while
Corollary 1.6's real-type density theorem remains proved. No claim about
p=infinity or a uniform analytic strip width is made. The unresolved
periodic-height range above four and G.2 norm interpretation remain;
the dissertation is incomplete.

Validation: the full project check passed (6605 build jobs), including all
public examples and the axiom audit of 27645 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.

### Lemma 3.2(ii) / Theorem 1.1 proof route: exponent dependence is necessary

[`FreeResolventHeightNecessity.lean`](NLS/ZakharovShabat/FreeResolventHeightNecessity.lean)
proves bounds for the actual free operator, using finite Fourier inputs.

| Public entry point | Scope |
| --- | --- |
| `tsum_scalarResolventToL1_triangularNormalized` | Exact output coefficient sum -2 at z=-i2^P for every positive integer exponent P. |
| `freeResolventToL1_dyadic_norm_lower`, `freeResolventToL1_dyadic_norm_upper` | P/48 <= actual pair-resolvent norm <= 2P+2^(-P), from lP to l1. |
| `freeResolventHeightCoefficient_necessary` | Any height coefficient C_P in the standard decay form must obey P <= 24 C_P+48. |
| `not_exists_uniform_freeResolventHeightCoefficient` | No fixed coefficient works for all finite integer exponents and nonreal parameters. |
| `freeResolvent_eight_height_bound_fails` | Actual constant-eight norm estimate fails for every integer P>240; checked at P=256. |
| `negativeDyadicHeight_mem_free_resolvent` | Every test point belongs to the actual free periodic resolvent set at every finite exponent. |

This establishes the necessary linear order of the exponent coefficient
in Lemma 3.2(ii)'s type of bound. It does not refute Theorem 1.1: its
unchanged printed periodic height remains proved through p=4 and required
but unresolved above four. The original source norm is unchanged, and no
source correction is adopted. The next periodic argument must use more
than a free-resolvent norm estimate with a fixed coefficient.

### Squared resolvent: component product and a conditional all-p printed height

[`ComponentProductResolvent.lean`](NLS/ZakharovShabat/ComponentProductResolvent.lean)
retains both off-diagonal component norms in the actual operator square.

| Public entry point | Scope |
| --- | --- |
| `norm_potentialFreeResolvent_sq_le_component_product` | Actual square norm bounded by B(z)^2 times the component-norm product, at every finite Banach exponent. |
| `squaredNeumannCondition_of_component_product` | Supplies the existing squared inverse with both inverse identities. |
| `mem_resolventSet_of_componentMean_height` | Both horizontal edges and the entire exterior for height (1+8p sqrt(ab))^p, where a,b are the component norms. |
| `periodicSpectrum_abs_im_lt_componentMean_height` | Every actual periodic spectral point lies strictly within that strip. |
| `source_mem_resolventSet_of_printed_height_component_product` | Unchanged printed source height at every finite p, assuming p sqrt(ab) <= original source norm. |
| `source_componentMean_condition_of_imbalance` | The norm condition p^2 b <= a implies that coupling hypothesis. |
| `analyticOnNhd_resolvent_componentProductRegion` | Actual resolvent analytic on an explicit open potential region containing every triangular potential for fixed z off the free lattice. |

Public examples check arbitrary finite exponents and p=256 with both
components nonzero. One example proves invertibility at z=i while the
previous Neumann condition fails; another checks the literal printed
height under the imbalance condition. The source norm remains the p-th
root of the two component p-energies. The unrestricted printed height
above p=4 is still required and unresolved, and the geometric-mean
supplement is not adopted as a replacement source statement.

### Theorem 1.1: exact balanced-source reduction of the remaining height claim

[`PeriodicDiagonalSimilarity.lean`](NLS/ZakharovShabat/PeriodicDiagonalSimilarity.lean)
and [`SourceBalancedHeightReduction.lean`](NLS/ZakharovShabat/SourceBalancedHeightReduction.lean)
transport actual spectral data while controlling the original source norm.

| Public entry point | Scope |
| --- | --- |
| `spectralPencil_diagonalSimilarity` | Exact conjugation of z-L on the original one-derivative domain, for any nonzero complex scalar. |
| `periodicRootSpaceTopDiagonalEquiv` | Full generalized root-space equivalence; finite root-chain transport is also proved. |
| `periodicAlgebraicMultiplicity_diagonalPotential`, `periodicSpectrum_diagonalPotential` | Actual multiplicities and entire periodic spectral set unchanged. |
| `exists_source_balanced_diagonalPotential` | For two nonzero components, both new norms equal sqrt(ab), the new p-energy norm is exactly 2^(1/p) sqrt(ab), and it does not exceed the original norm. |
| `source_printedHeight_iff_balanced` | At each finite exponent, the unrestricted literal height is equivalent to its equal-component-norm case. |
| `source_printedHeight_counterexample_balances` | Any putative violation retains its spectral parameter under balancing, with no increase in the source norm; no violation is asserted to exist. |
| `exists_source_periodicCounting_printed_height_of_balanced` | An explicit balanced-height hypothesis gives full counts, exhaustion, and actual analytic rectangular projections on one common open convex neighborhood, for all sufficiently large cutoffs. |

Public examples include p=5, rescaling component norms (1,4) to (2,2) and
checking the actual spectra and multiplicities, as well as arbitrary-exponent
interfaces and the full conditional counting conclusion. Equal norms do
not imply the source's real-type conjugation condition. The unrestricted
height above p=4 remains required and unresolved; the reduction is not a
proof of its explicit balanced-case hypothesis. No source correction is
adopted.

### Theorem 1.1: exact ordered-coupling criterion and normalization

[`OrderedTriangularMonodromy.lean`](NLS/ZakharovShabat/OrderedTriangularMonodromy.lean)
and [`OrderedTriangularNormalization.lean`](NLS/ZakharovShabat/OrderedTriangularNormalization.lean)
connect separated physical couplings to actual coefficient-space spectral points.

| Public entry point | Scope |
| --- | --- |
| `classicalSolution_eq_orderedTriangular` | Exact continuous-potential solution when the upper coupling acts before the lower coupling. |
| `classicalMonodromy_orderedTriangular`, `classicalDiscriminant_orderedTriangular` | Actual monodromy and trace expressed through two integrating-factor integrals A and B. |
| `source_mem_periodicSpectrum_orderedTriangular_iff` | Both Floquet signs characterize the actual spectrum at every finite p>=2; the original Hilbert source and its physical representative must agree. |
| `source_mem_periodicSpectrum_orderedPeriodicNormalization` | Scaling the upper coupling by -(exp(-i z)-1)^2/(A B) places z in the actual spectrum, assuming A B is nonzero. |
| `norm_orderedPeriodicNormalization`, `norm_scaleUpperSource_rpow` | Exact normalization magnitude and original source p-energy cost. |
| `exists_balanced_source_orderedPeriodicNormalization` | At nonreal z with nonzero components, a balanced realization retains z and has norm exactly 2^(1/p) sqrt(abs(kappa) a b). |

Public examples check the free trace, antiperiodic sign, normalized actual
spectral membership at p=5, and the arbitrary-exponent norm identities.
No quantitative small-norm profile or periodic-height counterexample is
claimed. Theorem 1.1's unrestricted printed height above p=4 remains
required and unresolved. No source correction is adopted.

### Theorem 1.1: concrete tent sources and reflected Fourier cancellation

[`ContinuousPeriodOneRealization.lean`](NLS/Fourier/ContinuousPeriodOneRealization.lean),
[`TentProfile.lean`](NLS/Fourier/TentProfile.lean),
[`OddTentProfile.lean`](NLS/Fourier/OddTentProfile.lean), and
[`OrderedTentSources.lean`](NLS/ZakharovShabat/OrderedTentSources.lean)
supply actual continuous profiles and quantitative estimates.

| Public entry point | Scope |
| --- | --- |
| `continuousPeriodOneCoefficients_apply`, `circlePullback_continuousPeriodOneCoefficients` | Every original Fourier integral and the actual almost-everywhere physical representative agree; no finite-support assumption. |
| `norm_sq_continuousPeriodOneCoefficients` | Exact unit-interval Parseval normalization. |
| `integral_tentProfile_mul_cexp`, `periodOneCoefficient_tentProfile` | Exact second-difference exponential transform. |
| `periodOneCoefficient_tentProfile_zero`, `norm_periodOneCoefficient_tentProfile_le_area` | Exact mean (b-a)^2/4 and the same coefficient bound at every frequency. |
| `norm_periodOneCoefficient_tentProfile_mul_frequency_le` | (2 pi abs(n))^2 times the coefficient norm is at most 4. |
| `normalized_orderedTentSource_mem_periodicSpectrum` | Explicit ordered tents realize every iH after normalization, at every finite p>=2; representative and interaction hypotheses are proved. |
| `exists_balanced_orderedTentSource` | At nonzero H, a balanced actual source retains iH with its exact original norm cost. |
| `periodOneCoefficient_oddTentProfile_zero` | An early tent minus its reflected tent has zero original Fourier mean. |
| `norm_periodOneCoefficient_oddTentProfile_le_low`, `norm_periodOneCoefficient_oddTentProfile_mul_frequency_le` | Low-frequency cancellation pi abs(n) b (b-a)^2 and quadratic high-frequency bound 8. |
| `integral_oddTentProfile_mul_exp_lower`, `integral_oddTentProfile_mul_exp_pos` | Quantitative weighted-interaction lower bound and strict positivity for an early nonempty signed pair. |

Public checks include concrete width 1/4 and p=5, as well as signed
profile estimates on [1/8,1/4]. The signed profiles have not yet been
summed over dyadic scales. No periodic-height violation is asserted;
Theorem 1.1 above p=4 remains required and unresolved.

### Theorem 1.1: dyadic interaction growth with bounded original coefficient norm

[`DyadicGeometricBounds.lean`](NLS/Fourier/DyadicGeometricBounds.lean),
[`NormalizedDyadicTent.lean`](NLS/Fourier/NormalizedDyadicTent.lean),
[`DyadicTentSum.lean`](NLS/Fourier/DyadicTentSum.lean), and
[`UniformQuadraticEnvelope.lean`](NLS/SequenceSpaces/UniformQuadraticEnvelope.lean)
prove the upper half of the proposed ordered multiscale construction.

| Public entry point | Scope |
| --- | --- |
| `sum_norm_le_of_dyadic_envelopes` | A bound of 80 for any finite set of scales satisfying the two envelopes; the proof splits at the frequency's dyadic bracket. |
| `periodOneCoefficient_dyadicTentSum`, `circlePullback_dyadicTentSumCoefficients` | The actual finite physical sum, every original Fourier integral, and the Hilbert representative agree. |
| `dyadicTentSum_eq_zero_near_ends` | The full upper profile vanishes on both endpoint intervals of width 2^(-J). |
| `norm_periodOneCoefficient_dyadicTentSum_le`, `norm_periodOneCoefficient_dyadicTentSum_tail` | Uniform coefficient bound 80 and quadratic tail abs(n)^2 abs(U_hat_J(n)) <= 16*4^J, without a scale-count factor. |
| `Coeff.norm_le_of_uniform_quadratic_envelope` | Original lp norm <= C (8N)^(1/p) for a zero-mean sequence bounded by C with quadratic tail C N^2, at every finite Banach exponent. |
| `norm_exponent_dyadicTentSumCoefficients_le` | Actual upper coefficient norm <= 80 (8*2^J)^(1/p), for every finite p>=2. |
| `norm_dyadicTentSumCoefficients_twice_exponent_le` | At J=2P and p=P, the original coefficient norm is at most 640 for every integer P>=3. |
| `integral_normalizedDyadicTent_ge_quarter` | Each sufficiently fine normalized scale contributes at least 1/4. |
| `integral_dyadicTentSum_pow_height` | The upper interaction at H=2^P is at least (P-2)/4 for every integer P>=3. |

Public checks cover negative frequencies, the zero mean and endpoint
support, a concrete scale contribution, and p=5 together with the full
integer-exponent family. The normalized lower coupling and final spectral
normalization estimate remain to be combined with these results.
Theorem 1.1 above p=4 is still required and unresolved; no periodic-height
counterexample or source correction is claimed.

### Theorem 1.1: actual counterexample to the all-exponent printed height

[`LowerDyadicTent.lean`](NLS/Fourier/LowerDyadicTent.lean),
[`OrderedDyadicSource.lean`](NLS/ZakharovShabat/OrderedDyadicSource.lean),
[`DyadicNormalizationBound.lean`](NLS/ZakharovShabat/DyadicNormalizationBound.lean), and
[`SourcePeriodicHeightCounterexample.lean`](NLS/ZakharovShabat/SourcePeriodicHeightCounterexample.lean)
complete the ordered multiscale construction in the original source norm.
This supersedes the historical unresolved-height entries above: the
all-exponent assertion is refuted, while the result through p=4 is proved.

| Public entry point | Scope |
| --- | --- |
| `integral_lowerDyadicTent`, `lowerDyadicTentCoefficients_zero` | Late tent has area one and original mean coefficient one. |
| `norm_lowerDyadicTentCoefficients_le_one`, `norm_lowerDyadicTentCoefficients_tail` | Every signed Fourier coefficient is bounded by one; its quadratic tail is bounded by 4^J. |
| `norm_exponent_lowerDyadicTentCoefficients_le` | Original lp norm <= 1+(8*2^J)^(1/p), for every finite p>=2. |
| `norm_lowerDyadicTentCoefficients_twice_exponent_le` | At J=2P and p=P>=3, the lower coefficient norm is at most nine. |
| `integral_lowerDyadicTent_exp_lower` | Lower interaction at H>=0 is at least exp(2H(1-2^(-J))). |
| `physicalBase_orderedDyadicSource`, `orderedDyadicCurve_support` | Original coefficients reconstruct the combined physical pair, with the upper coupling before the lower. |
| `normalized_orderedDyadicSource_mem_periodicSpectrum` | Normalization places i*2^P in the actual spectrum at every finite target p>=2 for each integer P>=3. |
| `exists_balanced_orderedDyadicSource` | Balanced source preserves that point with its exact original pair norm; no compatibility or nonzero-component hypotheses remain. |
| `norm_orderedDyadicNormalization_le` | Normalization magnitude <=12/(P-2) for integer P>=3. |
| `exists_balanced_dyadicSource_norm_le` | At exponent P, source norm <=2 sqrt(69120/(P-2)). |
| `exists_small_dyadicSource` | For integer P>=100000000, balanced source norm <=1/16 with actual spectral point i*2^P. |
| `sourcePeriodicPrintedHeight_counterexample` | The same source and point escape the printed-height box and all high disks at every cutoff N. |
| `not_sourceTheorem1_1_printed_exhaustion` | Explicit negation of all-source printed exhaustion at p=100000000. |

Public examples check the original mean and negative frequencies, the
concrete p=5 lower norm, physical reconstruction, actual spectral membership
at 32i, the normalization bound, the full counterexample family, and the
concrete negated assertion. No claim about the optimal threshold or every
individual exponent above four is made. Real-type reality and the printed
result through four remain valid. No replacement height is adopted.

Validation: the full project check passed (6624 build jobs), including all
public examples and the axiom audit of 27956 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Theorem 1.1: necessary coefficient growth and a proposed all-p height

[`SourcePeriodicHeightNecessity.lean`](NLS/ZakharovShabat/SourcePeriodicHeightNecessity.lean)
uses the actual balanced dyadic counterexample family.
[`SourcePeriodicExplicitHeight.lean`](NLS/ZakharovShabat/SourcePeriodicExplicitHeight.lean)
packages a separate sufficient correction in the original source norm.

| Public entry point | Scope |
| --- | --- |
| `exists_sourcePeriodicHeightCoefficient_counterexample` | At integer P>=3, every nonnegative C with 276480*C^2<P-2 has an actual balanced source whose spectral point exceeds (1+C*norm)^P. |
| `sourcePeriodicHeightCoefficient_necessary` | A universal original-source strip coefficient requires P-2<=276480*C^2. |
| `sourcePeriodicCountingHeightCoefficient_necessary` | The same necessary growth survives arbitrary source-dependent cutoffs and all high disks. |
| `not_exists_uniform_sourcePeriodicHeightCoefficient`, `not_exists_uniform_sourcePeriodicCountingHeightCoefficient` | No fixed nonnegative coefficient works at all integer exponents, for either strips or box/disk exhaustion. |
| `exists_source_periodicCounting_coefficient_height_of_resolvent` | General counting transfer for any nonnegative coefficient with an exterior resolvent estimate; the printed coefficient-eight API is preserved. |
| `mem_resolventSet_of_sourcePeriodicExplicitHeight` | Both closed exterior edges and the full exterior region for (1+8pM)^p, at all finite p>=1, in the original source norm. |
| `sourcePeriodicSpectrum_abs_im_lt_explicit_height` | Strict spectral strip bound for every source in the original norm ball. |
| `sourceTheorem1_1_proposed_height` | Common open convex source neighborhood, all larger cutoffs, full counting/parity data, central count 4N+2, spectral exhaustion, actual central projection, and analytic moving rectangular integrals. |

Public checks include the cutoff-dependent necessity, a concrete
coefficient-one failure at P=300000, exclusion of every uniform coefficient,
both signs of the corrected p=5 resolvent edge, and simultaneous central
count/parity data with analytic projections on one source neighborhood.
The printed height remains refuted at large integer exponents and proved
through p=4. No correction is adopted and no optimal growth rate is claimed.

Validation: the full project check passed (6626 build jobs), including all
public examples and the axiom audit of 27977 NLS declarations. Focused
builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with
156 labels. Counts do not certify completeness.

### Appendix G introduction: full-time fundamental-solution regularity to audit

Printed p. 135 recalls joint continuity of the original fundamental matrix
on `[0,infinity) x Complex x L2_c` and analyticity in frequency and potential
for every fixed time. The current `l2FundamentalMatrix` in
`L2HermitianOperatorBound.lean` is defined on `[0,1]`; its columns come
from `l2SolutionCurve` in `L2SolutionExtension.lean`. The integral equation,
a.e. differential equation, initial data, norm bounds, and recovery of
continuous inputs are proved. They do not by themselves establish the
full parameter-regularity and all-time statement. No matching public
entry point for that exact assertion was located during this audit.
It remains a concrete obligation, separate from G.2's interval-norm issue.
The plan is to establish regularity of the actual L2 solution and a
compatible extension of periodic inputs to all nonnegative times.

### Appendix G introduction: unit-interval L2 parameter regularity proved

The preceding all-time obligation is now reduced by a proved
unit-interval regularity result. The new modules
`ClassicalVolterraL2Bound.lean`, `L2ScalarVolterra.lean`,
`L2VolterraOperator.lean`, `L2VolterraInverse.lean`, and
`L2FundamentalAnalytic.lean` work with the original physical L2 norm and
actual integral equation. They impose no continuity assumption on the
potential. The existing coordinate integral formula is now public.

| Public entry point | Scope |
| --- | --- |
| `l2Volterra_apply`, `l2Volterra_of_continuous` | Exact original integral and classical-operator recovery. |
| `l2VolterraCoefficientMap`, `norm_l2Volterra_sub_le` | Bounded complex-linear parameter map and potential difference bound. |
| `isUnit_one_sub_l2Volterra` | Invertibility for every physical L2 potential and every complex frequency. |
| `l2SolutionOperator_eq_iff` | Unique actual integral-equation solution for arbitrary continuous forcing. |
| `norm_l2SolutionOperator_le` | Full forcing inverse norm at most exp(abs(z)+norm(u)). |
| `l2SolutionCurve_eq_l2SolutionOperator`, `l2SolutionCurve_unique_integral` | Identification and uniqueness for the existing initial-value solution. |
| `analyticOnNhd_l2SolutionOperator`, `analyticOnNhd_l2SolutionCurve_joint` | Joint parameter analyticity in the operator/uniform curve norm. |
| `analyticOnNhd_l2FundamentalMatrix_joint` | Fixed-time complex analyticity of the original matrix for every t in [0,1]. |
| `continuous_l2FundamentalMatrix_time_joint` | Joint time/frequency/potential continuity including both endpoints. |
| `det_l2FundamentalMatrix` | Determinant one for every original physical L2 input on [0,1]. |

The proof uses continuous approximation with a uniform L2 forcing bound,
then analytic inversion of the actual Volterra operator. It does not
replace the existing solution by an unrelated abstract construction.
Public checks include arbitrary forcing, both inverse identities,
initial-vector additivity, classical recovery, and matrix regularity.
The full `[0,infinity)` claim still requires periodic continuation and
identification with the original equation. The G.2 norm issue is separate.

Validation: the full project check passed (6631 build jobs), including all
public examples and the axiom audit of 28075 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Appendix G introduction: full-time physical L2 regularity proved

`L2PeriodicFundamental.lean`, `L2FundamentalInitialValue.lean`,
`L2PeriodicEquation.lean`, and `L2PeriodicUniqueness.lean` close the
full-time regularity obligation recorded above. The domain is all
nonnegative times and the original physical L2 space, with no continuity
assumption on the potential.

| Public entry point | Scope |
| --- | --- |
| `l2FundamentalMatrix_mul_column` | Matrix multiplication gives the existing initial-value solution for arbitrary initial columns. |
| `l2PeriodicFundamentalMatrix_on_period` | Exact M(s)*B^n formula on each whole closed period, including both joins. |
| `l2PeriodicFundamentalMatrix_unit`, `l2PeriodicFundamentalMatrix_nat` | Recovery on [0,1] and actual monodromy powers at all natural times. |
| `l2PeriodicFundamentalMatrix_zero`, `det_l2PeriodicFundamentalMatrix` | Identity initial value and determinant one for all nonnegative times. |
| `l2PeriodicFundamentalMatrix_add_nat` | Correct multiplication order in the monodromy relation for every natural time shift. |
| `continuous_l2PeriodicFundamentalMatrix_joint`, `analyticOnNhd_l2PeriodicFundamentalMatrix_joint` | Joint continuity through integer joins and fixed-time analyticity for all nonnegative times. |
| `l2PeriodicColumn_integral_on_period` | Actual signed Volterra equation on every closed period. |
| `ae_hasDerivAt_l2PeriodicColumn`, `ae_physicalOperator_l2PeriodicColumn` | Original differential and spectral equations almost everywhere on the full positive time domain. |
| `periodicL2Representative_ofFunction_periodic`, `ae_physicalOperator_l2PeriodicColumn_ofFunction` | Full-time agreement and spectral equation for any original period-one L2 representative. |
| `l2PeriodicColumn_unique` | Uniqueness among continuous columns with the same initial value and period-by-period integral equation. |
| `sourceFundamentalSolution_regularity` | The exact full-time continuity/analyticity assertion recalled on printed p. 135. |

Public checks include integer time 5, fractional time 5/2, a whole-period
shift, the free zero-frequency solution, first-period recovery, determinant
one, the actual integral equation on period three, arbitrary original
periodic representatives, and uniqueness. The construction uses periodic
coefficients after time one. The existing endpoint-clamped classical
construction is used only through its proved unit-interval recovery.

The independent G.2 interval-norm interpretation remains unresolved.
Next audit target: the trace-of-monodromy definition of the discriminant
on printed p. 45 for arbitrary rough Hilbert source potentials. The
existing `canonicalDiscriminant_eq_classical` requires a compatible
continuous representative; its removal is not supplied by the full-time
regularity theorem alone. The dissertation is incomplete.

Validation: the full project check passed (6635 build jobs), including all
public examples and the axiom audit of 28119 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Chapter 2, printed p. 45: the actual L2 monodromy trace for rough sources

`SourcePhysicalL2.lean`, `L2Discriminant.lean`, and
`L2DiscriminantCotangent.lean` extend the physical discriminant comparison
from continuous representatives to every original Hilbert source. The
source map reuses `physicalRestrictionL2CLM` and `periodOnePotential`.
The proof uses exact finite-source recovery, source density, and joint
continuity of the actual physical L2 trace.

| Public entry point | Scope |
| --- | --- |
| `sourcePhysicalL2_representative`, `sourcePhysicalL2_ofFinsupp` | Original Fourier representative on [0,1] and exact finite-curve recovery. |
| `analyticOnNhd_l2Discriminant_joint` | Joint frequency/potential analyticity of the actual L2 monodromy trace. |
| `canonicalDiscriminant_eq_l2_source` | Trace identity for every original Hilbert source, with no continuous-representative hypothesis. |
| `canonicalDiscriminant_eq_l2` | The same identity on the full even-supported Hilbert coefficient subspace. |
| `canonicalPeriodicProduct_eq_l2Discriminant` | Original normalized full spectral product equals actual trace squared minus four. |
| `l2Discriminant_sq_eq_four_iff` | Entire original periodic spectrum is exactly the physical characteristic zero set. |
| `l2Discriminant_parity_levels` | Trace levels two/minus two correspond to positive original even/odd algebraic multiplicity. |
| `l2Discriminant_zero` | Exact original free discriminant normalization. |
| `sourceDiscriminantCotangent_eq_l2`, `sourceDiscriminantCotangent_apply_eq_l2` | Complete source cotangent and every Hilbert variation agree with the physical L2 differential under the established source map. |
| `deriv_canonicalDiscriminant_eq_l2` | Equality of spectral derivatives. |

Public checks cover the literal monodromy trace, arbitrary even-supported
potentials, original representative recovery, source linearity, normalized
spectral product, spectrum equivalence, both parity sectors, arbitrary
Hilbert directions, spectral derivatives, and free/finite-source recovery.
These are exact identities, not only shared zero sets or proportionality.
The source normalization is retained throughout.

The rough-source physical anti-discriminant and separated-characteristic
comparisons remain the next transfer. Their current classical comparison
theorems require continuous representatives. A physical integral formula
for the full rough-potential gradient is also not supplied merely by the
cotangent chain-rule identity. The dissertation remains incomplete.

Validation: the full project check passed (6638 build jobs), including all
public examples and the axiom audit of 28144 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Physical L2 anti-discriminant and separated characteristics at rough sources

`L2SeparatedCharacteristics.lean`, `L2SourceCharacteristics.lean`, and
`L2CharacteristicCotangents.lean` remove the continuous-representative
hypotheses from the physical comparisons at the Hilbert exponent. They
reuse the established source-to-physical L2 map and prove exact identities
by finite-source density.

| Public entry point | Scope |
| --- | --- |
| `analyticOnNhd_l2SeparatedCharacteristic_joint`, `analyticOnNhd_l2AntiDiscriminant_joint` | Actual monodromy-entry formulas are jointly analytic on the entire physical L2 parameter space. |
| `l2SeparatedCharacteristic_eq_zero_iff` | Literal original endpoint condition for normalized initial data, with both boundary signs. |
| `l2SeparatedCharacteristic_zero`, `l2AntiDiscriminant_zero` | Exact sine and zero free normalizations. |
| `l2Discriminant_sq_sub_four` | Delta squared minus four equals delta squared minus four times the two separated characteristics for every physical L2 input. |
| `periodOneBoundaryCharacteristic_eq_l2`, `sourceAntiDiscriminantCandidate_eq_l2` | Exact original-source comparisons for every Hilbert source, without continuous-representative assumptions. |
| `l2SeparatedCharacteristic_source_eq_zero_iff`, `sourceBoundarySpectrum_iff_l2_endpoint` | Original restricted-operator spectrum equals the physical characteristic zero set and the actual L2 endpoint condition. |
| `analyticOrderAt_l2SeparatedCharacteristic_source` | Actual physical zero orders equal original algebraic multiplicities. |
| `l2SeparatedCharacteristic_source_eq_product` | Complete original boundary labelings give the normalized physical characteristic product. |
| `sourceBoundaryCharacteristicCotangent_eq_l2`, `sourceAntiDiscriminantCotangent_eq_l2` | Full continuous cotangent identities on the Hilbert source space. |
| `sourceBoundaryCharacteristicCotangent_apply_eq_l2`, `sourceAntiDiscriminantCotangent_apply_eq_l2` | Every Hilbert source direction is included. |
| `deriv_periodOneBoundaryCharacteristic_eq_l2`, `deriv_sourceAntiDiscriminantCandidate_eq_l2` | Exact spectral derivative comparisons. |

Public checks verify the Dirichlet and Neumann endpoint signs separately,
the off-diagonal anti-discriminant sum, original boundary spectra and
multiplicities, labeled normalized products, arbitrary Hilbert variations,
spectral differentiation, the determinant identity at a characteristic
zero, and both free normalizations.

The remaining physical-gradient transfer is an explicit integral formula
for the actual potential derivative at arbitrary rough L2 inputs and
directions. `ClassicalPotentialVariation.lean` proves the corresponding
variation result for continuous input. The cotangent identities above
alone do not supply that physical formula. The dissertation is incomplete.

Validation: the full project check passed (6641 build jobs), including all
public examples and the axiom audit of 28177 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 solution variation and linearized equation

`L2SolutionVariation.lean`, `L2PotentialVariation.lean`, and
`L2VariationEquation.lean` identify the actual solution derivative with
its physical linearized Volterra solution. They supply the rough-L2
variation prerequisite for the fundamental-matrix gradient formula in
the proof of Lemma G.5 (printed p. 137).

| Public entry point | Scope |
| --- | --- |
| `fderiv_l2SolutionCurve_joint_apply` | Joint frequency/potential derivative in the uniform curve norm, at every physical L2 input. |
| `l2VariationCurve_eq_integral`, `l2VariationCurve_zero`, `l2VariationCurve_unique` | Actual signed integral equation, zero initial value, and uniqueness among its continuous solutions. |
| `fderiv_l2SolutionCurve_potential`, `fderiv_l2SolutionCurve_potential_eval` | Arbitrary L2 potential directions and evaluation at every time, including the endpoint. |
| `l2PotentialVariation_eq_integral` | Explicit off-diagonal forcing with the original plus/minus signs. |
| `norm_l2VariationCurve_le` | Global bound, linear in the frequency and L2 perturbation norms. |
| `l2PotentialVariation_of_continuous` | Exact agreement with the existing classical potential variation. |
| `ae_hasDerivAt_l2VariationCurve`, `ae_hasDerivAt_l2PotentialVariation` | Actual linearized differential equation almost everywhere on the unit interval. |
| `l2VariationCurve_eq_integral_ofFunction`, `ae_hasDerivAt_l2VariationCurve_ofFunction` | Integral and differential equations for arbitrary original square-integrable representatives. |

Public examples verify the full derivative formula, potential directions,
endpoint and initial values, explicit signed forcing integrals,
uniqueness, the norm estimate, the a.e. equation, arbitrary physical
representatives, and classical recovery. The matrix kernel and the
resulting rough-L2 endpoint gradient integrals are not yet claimed.
The dissertation remains incomplete.

Validation: the full project check passed (6644 build jobs), including all
public examples and the axiom audit of 28197 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 variation kernel and endpoint gradient integrals

The matrix-kernel prerequisite for the gradient formula in the proof of
Lemma G.5 (printed p. 137) is now established at arbitrary physical L2
inputs. This is an exact formula, not an assumed gradient or a change
of the original Fourier normalization.

| Public entry point | Scope |
| --- | --- |
| `l2KernelPairing_apply` | Integrated adjugate forcing is the ordinary unconjugated integral of the original L2 representatives. |
| `continuous_l2KernelPairing`, `l2KernelPairing_sub`, `l2KernelPairing_smul` | Joint continuity and linearity in the adjugate column. |
| `continuous_l2VariationCurve`, `continuous_l2PotentialKernelCurve` | Joint continuity needed to pass both base potentials and directions through L2 approximation. |
| `l2PotentialKernelCurve_of_continuous` | Exact recovery of the existing classical variation through its determinant-one kernel. |
| `l2PotentialKernelCurve_eq_variation`, `fderiv_l2SolutionCurve_potential_eq_kernel` | Explicit kernel equals the actual derivative as a whole continuous curve on [0,1]. |
| `l2EndpointGradient`, `continuous_l2EndpointGradient` | Explicit physical adjugate gradient for any complex-linear endpoint functional at any unit-interval time. |
| `fderiv_l2Endpoint_eq_gradient_integral` | Actual L2 Fréchet derivative equals its unconjugated physical gradient integral. |
| `fderiv_sourceL2Endpoint_eq_gradient_integral`, `fderiv_sourceL2Endpoint_eq_physical_integral` | Every Hilbert source and direction, with the original physical Fourier representative and normalization. |

Public checks cover the entire-curve kernel identity, its two column
signs, literal integral pairing, general endpoint functional, an actual
monodromy-entry derivative, original Hilbert source directions,
classical recovery, and both free off-diagonal gradient signs.
Named trace, anti-trace, and separated-characteristic gradient integral
specializations remain to be connected to the existing source
cotangents. Counts do not certify completion of the dissertation.

Validation: the full project check passed (6648 build jobs), including all
public examples and the axiom audit of 28227 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Physical spectral-characteristic gradients on the full Hilbert source space

The generic endpoint integral now supplies the actual trace,
anti-discriminant, and both separated-characteristic gradients at rough
L2 inputs. Existing source cotangents are identified with these physical
integrals in every Hilbert direction.

| Public entry point | Scope |
| --- | --- |
| `intervalIntegrable_l2EndpointGradient_pairing` | Actual L2 endpoint pairings are integrable on every unit subinterval. |
| `fderiv_l2Endpoint_add_eq_gradient_integral` | Endpoint sums differentiate and combine inside the ordinary integral. |
| `l2DiscriminantGradient`, `l2AntiDiscriminantGradient`, `l2SeparatedGradient` | Explicit physical gradients constructed from the proven endpoint kernel. |
| `l2SeparatedCharacteristic_eq_endpoint` | Exact separated endpoint identity, including the original sine normalization and signs. |
| `fderiv_l2Discriminant_eq_gradient_integral`, `fderiv_l2AntiDiscriminant_eq_gradient_integral`, `fderiv_l2SeparatedCharacteristic_eq_gradient_integral` | Actual potential derivatives for all physical L2 bases and directions. |
| `continuous_l2DiscriminantGradient`, `continuous_l2AntiDiscriminantGradient`, `continuous_l2SeparatedGradient` | Continuity in the physical variable. |
| `sourceDiscriminantCotangent_eq_physical_gradient_integral`, `sourceAntiDiscriminantCotangent_eq_physical_gradient_integral`, `sourceBoundaryCharacteristicCotangent_eq_physical_gradient_integral` | Existing source cotangents equal ordinary integrals against the original Fourier-synthesized direction at every Hilbert source. |

Public checks include all six derivative/cotangent formulas,
integrability, the free trace and anti-trace gradients, and the exact
free gradient for both boundary signs. Pointwise comparison with the
classical gradient functions and the resulting connection to existing
corrected coefficient estimates remain the next step. The previously
proved estimates and documented reference/exponent corrections are
unchanged. The dissertation remains incomplete.

Validation: the full project check passed (6651 build jobs), including all
public examples and the axiom audit of 28245 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Classical comparison and actual L2 realization of G.6 coefficient estimates

The endpoint, trace, anti-trace, and separated gradient functions now
have pointwise classical comparisons on the physical unit interval.
The established G.6 signed coefficient vectors and their source-norm
estimates consequently apply to the actual physical L2 derivatives.

| Public entry point | Scope |
| --- | --- |
| `l2EndpointGradient_of_continuous`, `l2DiscriminantGradient_of_continuous`, `l2AntiDiscriminantGradient_of_continuous`, `l2SeparatedGradient_of_continuous` | Exact pointwise agreement on [0,1]. |
| `l2AntiDiscriminantGradientRemainder_of_continuous`, `l2AntiDiscriminantGradientRemainder_lattice` | Subtraction of the actual free L2 gradient and the corrected signed lattice waves. |
| `L2GradientFourierRealizes` | Actual Fourier integrals, factor i, first index -k and second index k. |
| `L2GradientFourierRealizes.unique`, `L2GradientFourierRealizes.norm_rpow` | Unique represented coefficient vector and the exact finite-q source energy. |
| `sourceG6DiscriminantCoefficients_realizes_l2`, `sourceG6AntiDiscriminantCoefficients_realizes_l2` | Existing coefficient vectors represent the actual L2 gradient and its free-reference error. |
| `sourceG6_l2DiscriminantGradient_majorant`, `sourceG6_l2AntiDiscriminantGradient_majorant` | One nonnegative outer-lp majorant on each exact H1 source ball, with the established spectral and exponent hypotheses. |
| `sourceG6_l2DiscriminantGradient_memlp`, `sourceG6_l2AntiDiscriminantGradient_memlp` | Realized whole coefficient sequences belong to outer lp; finite initial spectral values are retained. |

Public checks include the pointwise comparisons, actual free-gradient
subtraction, all signed lattice indices, both Fourier index conventions,
uniqueness, the q=2 energy, a p=q=2 uniform source-ball majorant, and
whole-sequence anti-discriminant summability. No new rough-L2-ball
asymptotic estimate or infinity endpoint is claimed. The existing
G.5–G.7 reference corrections and exponent restrictions remain unchanged.
Physical simple-root gradient normalization remains the next step.

Validation: the full project check passed (6654 build jobs), including all
public examples and the axiom audit of 28266 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 simple-root derivatives and Dirichlet normalization

The actual physical L2 separated characteristics now differentiate any
continuous local selection of a simple zero. The implicit-root quotient
uses the previously proved physical gradient integral for either boundary
sign, with no regularity assumption on the L2 potential or direction.

`L2SpectralVariation.lean` proves spectral differentiation of the entire
solution curve and the endpoint-dual integral identity for every L2
potential, before imposing a characteristic zero. Continuity and density
are used on this unrestricted identity; no density of smooth potentials
inside a root locus is assumed.

`L2DirichletNormalization.lean` proves that the dual curve at a Dirichlet
root is proportional to the forward eigenfunction. The spectral derivative
is -i times that factor times Q, where Q is twice the unconjugated integral
of the two eigenfunction components. Simplicity implies Q is nonzero.
`L2DirichletRootGradient.lean` then identifies the actual branch derivative
with the integral against (y2 squared / Q, y1 squared / Q). These expressions
agree with the classical ones on [0,1]; at zero potential Q=2 and the two
opposite exponential waves have exactly the factor one half.

Next is transfer of this normalized root differential to the original
Hilbert source coordinates and connection to the established corrected
G.7 coefficient estimates. No new asymptotic estimate on arbitrary rough
L2 balls is asserted. G.2's arbitrary-time interval norm remains unresolved;
neither proposed spectral-height correction is adopted. The optional
original m=1 sharpening remains under the accepted Lemma 27.2 correction.
The dissertation is incomplete.

Validation: the full project check passed (6658 build jobs), including all
public examples and the axiom audit of 28313 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `fderiv_l2SeparatedRoot_eq_gradient_quotient` | Both separated boundary signs; any continuous local simple-root branch in physical L2. |
| `hasDerivAt_l2SolutionCurve_spectral`, `deriv_l2Endpoint_eq_spectral_integral` | Actual spectral derivatives of the uniform solution curve and arbitrary linear endpoint functionals. |
| `l2DirichletDualCurve_of_root`, `l2SeparatedGradient_dirichlet_of_root` | Dual proportionality and reversed eigenfunction squares at a Dirichlet zero. |
| `deriv_l2DirichletCharacteristic_of_root`, `l2DirichletNormalization_ne_zero_of_simple` | Spectral derivative factorization; simplicity supplies the required nonzero denominator. |
| `fderiv_l2DirichletRoot_eq_normalized_integral` | Actual branch derivative paired with normalized eigenfunction squares, without complex conjugation. |
| `l2DirichletNormalization_of_continuous`, `l2DirichletNormalizedGradient_of_continuous` | Exact comparison with the established classical quantities. |
| `l2DirichletNormalization_free`, `l2DirichletNormalizedGradient_free` | Free normalization two and both opposite waves divided by two. |

Public checks cover both boundary signs, the unrestricted spectral integral,
the spectral factorization, simplicity implying nonzero normalization,
the expanded squared-eigenfunction derivative, classical comparison, and
the free normalization and waves, including their value at zero frequency.

### Original source Dirichlet differentials and actual L2 G.7 coefficients

The original canonical source Dirichlet differential now has its actual
physical L2 normalized squared-eigenfunction integral for arbitrary
Hilbert potentials and directions. `L2SourceDirichletGradient.lean`
retains the original period-one Fourier synthesis and proves compatibility
with every finite source exponent p>=2. One open complex neighborhood of
the entire real source locus supplies simplicity and nonzero normalization
at every signed index. No continuous representative or H1 assumption is
needed for this differential formula.

`L2SourceDirichletFourier.lean` identifies both unit-mode values of the
actual source cotangent with the normalized L2 Fourier integrals. Finite
directions are handled through their almost-everywhere physical
representatives; no continuity of the base potential is introduced.

`L2SourceG7Gradients.lean` identifies the existing signed G.7 Dirichlet
error vector with the actual normalized L2 gradient minus its actual free
reference. The signed coefficient convention has first index -k, second
index k, and no extra factor i. The represented vector is unique and its
finite-q norm power is exactly the combined coefficient energy. The free
reference has corrected waves at 2*n and -2*n, each divided by two.

Intersecting the physical-realization domain with the established G.7
summability domain gives one open complex domain for both results. On the
original H1 source, the realized whole sequence lies in outer lp with
finite p>=2 and conjugate exponent q, including all finite central indices.
Every real H1 source is covered without an extra smallness, simplicity,
or normalization premise. No new asymptotic estimate on rough L2 balls
or infinity endpoint is asserted.

Next is the actual physical L2 midpoint gradient and its contour formula,
connecting the other half of G.7 to the same construction. G.2's arbitrary-
time interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6661 build jobs), including all
public examples and the axiom audit of 28330 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `sourceBoundaryCharacteristicCotangent_exponent_l2_integral` | Both boundary signs, arbitrary Hilbert bases and directions, and finite source exponent inclusion. |
| `canonicalDirichletRoot_l2_normalized_integral_of_simple` | Actual normalized derivative at any differentiable simple complex canonical root. |
| `exists_global_source_dirichlet_l2_normalized_integral` | One complex neighborhood of the real locus, every signed index, and every Hilbert direction; normalization proved nonzero. |
| `exists_global_source_dirichlet_l2_fourier` | Both unit source directions have the actual normalized L2 Fourier coefficients without a continuous base representative. |
| `L2RootGradientFourierRealizes.unique`, `L2RootGradientFourierRealizes.norm_rpow` | Unique coefficient vector and exact finite-q energy. |
| `l2DirichletGradientRemainder_lattice` | Subtraction of the actual free half-waves with corrected signed indices. |
| `exists_global_sourceG7_l2_realization` | Existing G.7 Dirichlet error vector realizes the physical error at every included Hilbert source in one complex neighborhood. |
| `exists_global_sourceG7_l2_memlp`, `sourceG7_l2_memlp_real` | Whole-sequence H1 summability with physical realization on one complex domain, and the unconditional real-source corollary. |

Public checks include the Hilbert cotangent, arbitrary real Hilbert bases
and directions, complex-domain realization, the generic conjugate-exponent
real H1 result, signed lattice reference, uniqueness, and exact q=2 energy.

### Physical midpoint gradient contours and actual G.7 coefficients

The actual source midpoint differential now has a physical L2 gradient
contour. `L2GradientCurves.lean` places the endpoint and discriminant
gradients in the Banach space of continuous physical curves, proves
spectral continuity in the uniform norm, and constructs the unconjugated
pairing with any rough L2 direction as a continuous linear map.

`L2MidpointContour.lean` integrates the quotient-weighted discriminant
gradient in that uniform norm. Evaluation recovers its pointwise contour,
and the continuous pairing commutes with the contour to give the actual
directional discriminant integral. A radius-times-supremum estimate bounds
the entire physical gradient curve. Nonvanishing of the periodic
characteristic on the circle ensures integrability.

`L2SourceMidpointGradient.lean` identifies this physical integral with the
actual canonical source midpoint derivative on an isolating circle. The
original period-one realization, arbitrary Hilbert directions, and every
finite source exponent p>=2 are retained. Enclosing both indexed periodic
endpoints and avoiding the other cuts supplies denominator nonvanishing;
the two enclosed endpoints may coincide.

`L2SourceMidpointFourier.lean` constructs such circles for every signed
index on one common complex neighborhood of the real source locus. It
identifies the existing signed G.7 midpoint vector with the actual Fourier
coefficients of the physical contour gradient. On the original H1 source,
the whole realized sequence retains G.7's outer-lp summability with finite
p>=2 and conjugate q. The finite central block and collapsed gaps are
included without supplied circles or distinct-endpoint hypotheses.

Next is uniqueness of physical gradient representatives and independence
of the chosen isolating circle, followed by a choice-independent midpoint
gradient API. No new rough-L2-ball asymptotic estimate is asserted. G.2's
arbitrary-time interval norm remains unresolved; neither proposed spectral-
height correction is adopted. The optional original m=1 sharpening remains
under the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6665 build jobs), including all
public examples and the axiom audit of 28375 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `continuous_l2EndpointGradientCurve_spectral`, `continuous_l2DiscriminantGradientCurve_spectral` | Spectral continuity in the uniform norm of physical gradient curves. |
| `l2GradientPairing_apply`, `l2GradientPairing_discriminant` | Continuous unconjugated pairing with rough L2 directions; exact actual discriminant derivative. |
| `circleIntegrable_l2MidpointGradientIntegrand`, `l2MidpointGradient_apply` | Uniform curve contour and its literal pointwise values. |
| `l2MidpointGradient_pairing`, `norm_l2MidpointGradientCurve_le` | Justified pairing-contour interchange and the radius-times-supremum bound. |
| `exists_global_source_midpoint_l2_gradient_contour` | Actual source midpoint derivative from any admissible isolating circle, with finite exponent inclusion. |
| `exists_global_source_midpoint_isolating_circles`, `exists_global_source_midpoint_l2_gradient` | Constructed circles and physical gradient formulas for every signed index on a complex neighborhood. |
| `exists_global_sourceG7_l2_midpoint_realization`, `exists_global_sourceG7_l2_midpoint_memlp` | Exact signed G.7 coefficient vectors and whole-sequence H1 summability for the physical gradients. |

Public checks cover uniform continuity, the actual discriminant differential,
rough L2 pairing-contour interchange, the curve norm bound, arbitrary real
Hilbert source directions, the collapsed zero-potential case, and the generic
finite conjugate-exponent H1 summability result. Contour independence of the
pointwise physical representative is not yet asserted.

### Pointwise gradient uniqueness and contour-independent midpoint gradients

Physical midpoint gradients are now independent of the constructing
isolating circle. `IntervalContinuousUniqueness.lean` proves that equal
actual Fourier coefficients determine continuous functions on the entire
closed physical interval. The proof reconstructs their L2 classes and then
uses continuity to recover both endpoints; no endpoint-matching condition
is imposed.

`L2SourceGradientUniqueness.lean` proves pointwise uniqueness both from a
common signed Fourier vector and from the full Hilbert source cotangent.
`SourcePhysicalGradientRepresents` records the actual unconjugated source
integral, and every continuous curve representing the same cotangent is
equal. The selected representative agrees with any such constructed curve.
Its representation theorem requires existence; the total definition's
zero fallback outside that domain is not asserted to represent a cotangent.

`L2CanonicalMidpointGradient.lean` defines the physical midpoint curve from
the actual source derivative restricted to Hilbert directions. On a common
complex neighborhood of the entire real source locus, it represents that
full restriction at every signed index. Every admissible isolating circle
gives exactly the same curve, including endpoint values and collapsed gaps.
At real Hilbert sources the curve also agrees across all finite ambient
source exponents p>=2.

The signed G.7 midpoint vector now realizes this unique physical gradient
without contour parameters. The established whole-sequence H1 summability
persists on a common complex neighborhood, with finite p>=2 and conjugate q.
No new asymptotic estimate on rough L2 balls or infinity endpoint is claimed.

Next is physical-gradient realization below the Hilbert exponent, using
restriction to the original source spaces 1<p<=2 while retaining their
actual norms and established summability. G.2's arbitrary-time interval
norm remains unresolved; neither proposed spectral-height correction is
adopted. The optional original m=1 sharpening remains under the accepted
Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6668 build jobs), including all
public examples and the axiom audit of 28399 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `eqOn_Icc_of_intervalFourierCoefficient_eq` | Fourier uniqueness on any closed positive-length interval, with no endpoint-matching condition. |
| `L2RootGradientFourierRealizes.eqOn` | A common signed coefficient vector determines the physical gradient at every point of [0,1]. |
| `SourcePhysicalGradientRepresents.unique` | The full Hilbert source cotangent determines the entire continuous physical curve. |
| `sourcePhysicalGradientCurve_eq_of_represents` | Every constructed representative equals the selected curve. |
| `exists_global_source_midpoint_physical_gradient` | Canonical physical curve represents the actual source differential and is realized by a constructed contour at every index. |
| `exists_global_source_midpoint_contour_independent` | Every admissible isolating circle produces that same curve, including collapsed gaps. |
| `sourceMidpointPhysicalGradientCurve_exponent_of_real` | Equality with the Hilbert ambient-exponent construction at real sources. |
| `exists_global_sourceG7_canonical_midpoint_realization`, `exists_global_sourceG7_canonical_midpoint_memlp` | Actual signed Fourier identity and original H1 summability without contour parameters. |

Public checks include equality at both physical endpoints, uniqueness from
source cotangents and signed Fourier coefficients, admissible-circle
independence, equality of two represented contour curves, finite-exponent
compatibility, the collapsed zero-source case, and generic conjugate-
exponent H1 summability of the canonical gradient coefficients.

### Physical G.7 gradients in original source spaces below two

The actual canonical midpoint and Dirichlet differentials now have physical
integral formulas in every original source direction for 1<p<=2.
`L2GradientsBelowTwo.lean` differentiates the spectral-coordinate identities
under inclusion into the Hilbert source. It constructs open complex
neighborhoods containing the entire real source locus where these formulas
hold at every signed index. The midpoint uses the canonical Hilbert physical
gradient; the Dirichlet formula uses normalized squared eigenfunctions with
nonzero normalization proved on the same domain.

`L2GradientRestrictionFourier.lean` identifies the signed conjugate vectors
with the actual physical Fourier coefficients in the original source norm.
Both midpoint gradients and Dirichlet errors have this realization on
complex neighborhoods. The Dirichlet error subtracts the actual zero-source
gradient, with its exact half-wave normalization. The endpoint p=2 agrees
with the Hilbert construction.

`L2SourceG7BelowTwo.lean` transfers the established derivative estimates to
both physical G.7 coefficient sequences. For real H1 sources and every
1<p<=2, both sequences belong to outer lp in the exact conjugate pair norm,
including every signed index and the finite central block. The physical
formulas and coefficient realization hold on complex neighborhoods; this
step's summability theorem is for real H1 sources. It does not assert a new
complex-neighborhood summability estimate below two.

Next is physical realization of the G.6 anti-discriminant error in the
original source spaces below two. G.2's arbitrary-time interval norm remains
unresolved; neither proposed spectral-height correction is adopted. The
optional original m=1 sharpening remains under the accepted Lemma 27.2
correction. The dissertation is incomplete.

Validation: the full project check passed (6672 build jobs), including all
public examples and the axiom audit of 28422 NLS declarations. Focused
module builds and the standalone public probe passed, including the concrete
conjugate pair p=3/2, q=3 and the endpoint p=2. There are 21 existing warnings
and no new warnings. The source inventory check passed with 156 labels.
Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `CoeffPair.exponentInclusion_refl` | Identity exponent inclusion, including the Hilbert boundary case. |
| `fderiv_midpoint_below_two_of_hilbert_differentiable`, `fderiv_dirichlet_below_two_of_hilbert_differentiable` | Actual source derivatives restricted from the Hilbert source wherever its coordinate is differentiable. |
| `exists_global_source_midpoint_below_two_integral`, `exists_global_source_dirichlet_below_two_integral` | Physical integrals in every original direction on open complex neighborhoods, with nonzero Dirichlet normalization. |
| `signedGradient_realizes_below_two_of_integral` | An actual source integral determines its signed conjugate Fourier vector. |
| `fderiv_canonicalDirichletRoot_zero_eq_free_below_two` | Exact free half-wave differential for 1<p<=2. |
| `exists_global_sourceG7_midpoint_below_two_realization`, `exists_global_sourceG7_dirichlet_below_two_realization` | Both physical G.7 Fourier realizations on complex neighborhoods, with the actual free gradient subtracted for the Dirichlet error. |
| `sourceG7_below_two_memlp_real`, `sourceG7_below_two_physical_real` | Both whole coefficient sequences have outer-lp summability in the original conjugate norm at real H1 sources. |

Public checks cover the Hilbert boundary case, full original-direction
integrals on complex neighborhoods, subtraction of continuous physical
gradients, and both physical realizations and summability at the concrete
conjugate pair p=3/2, q=3. No infinity endpoint is asserted.

### Physical G.6 errors below two for complex sources

The actual anti-discriminant cotangent now has its physical integral in
every original source direction for 1<p<=2, at every complex potential and
spectral parameter. `L2AntiDiscriminantBelowTwo.lean` restricts the entire
Hilbert cotangent and constructs its error vector in G.6's signed Fourier
convention. The factor i and first-component index reversal preserve the
exact conjugate pair norm. Subtraction uses the actual zero-potential
gradient at the reference parameter.

`L2SourceG6BelowTwo.lean` proves outer-lp summability of this physical error
at both canonical Dirichlet and Neumann sequences for complex H1 sources.
Every signed index and the finite central block are retained. The Hilbert
estimate already applies to complex sources, so restricting it requires
neither a reality assumption nor root simplicity. On the original H1
source, uniqueness of the actual Fourier coefficients identifies the new
cotangent vector exactly with the established Sobolev G.6 vector.

The standalone public checks include arbitrary complex spectral and
reference parameters, exact coefficient energy, zero-source cancellation,
the Hilbert endpoint p=2, the concrete conjugate pair p=3/2 and q=3, and
both boundary conditions. This step supplies no infinity endpoint.

Next is extending the physical G.7 summability below two from real H1
sources to a common complex neighborhood of the real source locus. G.2's
arbitrary-time interval norm remains unresolved; neither proposed spectral-
height correction is adopted. The optional original m=1 sharpening remains
under the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6674 build jobs), including all
public examples and the axiom audit of 28435 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `sourceAntiDiscriminantCotangent_below_two_integral` | Entire physical integral in every original source direction for 1<p<=2. |
| `L2RootGradientFourierRealizes.mul_I` | Exact conversion to G.6's Fourier phase convention. |
| `sourceG6AntiDiscriminantCotangentCoefficients`, `norm_sourceG6AntiDiscriminantCotangentCoefficients` | Actual signed error vector, with its exact conjugate pair norm. |
| `sourceG6AntiDiscriminantCotangentCoefficients_realizes_below_two` | Physical remainder identity for any complex potential and spectral/reference parameters. |
| `memlp_source_antiDiscriminantCotangent_error_below_two_complex` | Original operator estimate at either boundary sequence for complex H1 sources. |
| `sourceG6_below_two_physical_complex` | Whole-sequence physical Fourier realization and outer-lp summability in the original source norm. |
| `sourceG6AntiDiscriminantCotangentCoefficients_eq_sobolev` | Exact equality with the established Sobolev physical G.6 coefficient vector. |

### Complex physical G.7 summability and the full finite source range

Physical G.7 summability below two now holds on a common open complex
neighborhood containing the entire real source locus, rather than only at
real H1 sources. `SourceHilbertGradientComplexSummability.lean` constructs
Hilbert neighborhoods before choosing the outer exponent. Every real outer
exponent greater than one works on those same domains, with the original
H1 source and the finite central block retained.

`L2SourceG7ComplexBelowTwo.lean` intersects the estimate domains with the
analytic coordinate domains, then restricts both actual derivatives to
the original source space for 1<p<=2. On one common complex neighborhood,
both signed conjugate coefficient sequences have outer-lp summability and
realize the canonical midpoint gradient and normalized Dirichlet gradient
error. Dirichlet normalization is nonzero at every signed index. The exact
free derivative and corrected half-wave reference are retained.

`SourceSobolevAllExponents.lean` supplies the original H1 input directly in
every coefficient exponent through its l1 embedding. The map preserves
both Fourier sequences and agrees with the established Hilbert inclusion.
`SourceLemmaG7AllFinite.lean` uses this map to give both corrected G.7
estimates for every finite p>1 on the original complex H1 source, with no
separate physical-compatibility premise. For each exponent, a single open
complex domain contains the real source locus and supports both estimates.

The public checks include a Hilbert domain common to all outer exponents,
the concrete conjugate pair p=3/2 and q=3, the collapsed zero source,
automatic physical H1 realization, and the full finite-exponent statement.
These remain pointwise H1 summability conclusions; no new uniform bound on
all H1 source balls or infinity endpoint is asserted.

Next is auditing the remaining Appendix G physical estimates and source
interfaces against the printed assumptions. G.2's arbitrary-time interval
norm remains unresolved; neither proposed spectral-height correction is
adopted. The optional original m=1 sharpening remains under the accepted
Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6678 build jobs), including all
public examples and the axiom audit of 28454 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `exists_global_hilbert_midpoint_outer_complex`, `exists_global_hilbert_dirichlet_outer_complex` | Complex Hilbert domains chosen before every outer exponent above one, for the actual derivatives and free-reference errors. |
| `exists_global_source_gradients_below_two_complex_memlp` | Both original source operator sequences summable on a common complex neighborhood for 1<p<=2. |
| `exists_global_sourceG7_below_two_physical_complex` | Both exact conjugate-norm sequences, physical Fourier realizations, and nonzero Dirichlet normalization on the same domain. |
| `sobolevSourceExponentInclusion`, `exponentInclusion_sobolevSourceExponentInclusion` | Continuous original H1 inclusion preserving both raw Fourier sequences across source exponents. |
| `sourceG7_below_two_periodic_representative` | Automatic physical H1 representative below two, without an added compatibility premise. |
| `sourceLemmaG7_all_finite_corrected` | Both corrected G.7 estimates for every finite p>1 on the original complex H1 source. |

### G.3 derivative proof correction and consolidated Appendix G audit

The intermediate derivative line in the proof of G.3 omits the remainder
hat. The rendered PDF on printed page 136 displays a uniform bound for the
time derivative of M. `ClassicalFundamentalDerivativeAudit.lean` proves
that at zero potential and time zero the actual fundamental derivative is
diag(-i*z,i*z), with Hermitian operator norm exactly abs(z). The displayed
uniform claim therefore fails even on real spectral parameters with
abs(z)>=1 and the singleton zero-potential source set.

`SourceG3DerivativeCorrection.lean` proves the required corrected bound for
the actual remainder M-E. After the printed exponential normalization,
the full Hermitian derivative is bounded uniformly at every nonzero
complex spectral parameter and every time in [0,1]. On the exact original
periodic H1 source ball of radius M, an explicit valid constant is
4*(8+pi)*(2*M)*exp(4*(2*M)). No spectral-strip restriction is required.
The stated G.3 remainder decay conclusions retain their existing proofs.

`coverage/APPENDIX_G.md` now consolidates the current source audit, including
the actual physical L2 fundamental solution, all seven numbered results,
original H1 source interfaces, corrected references, and exponent ranges.
It distinguishes source-level refutations from intermediate proof typos
and does not treat a corrected theorem as the unchanged printed statement.

Public checks cover the exact derivative norm at an arbitrary complex
parameter and at z=3, failure of the uniform printed estimate, the corrected
bound on the exact source ball, and vanishing of the free remainder's
derivative on the entire closed unit interval.

Next is auditing Appendix H's Hamiltonian formulas and weak-source
identifications against the printed assumptions. G.2's arbitrary-time
interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6680 build jobs), including all
public examples and the axiom audit of 28468 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `deriv_classicalHermitianFundamental_zeroPotential_at_zero` | Actual free diagonal generator at time zero. |
| `norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero` | Exact genuine Hermitian operator norm abs(z). |
| `sourceG3_printed_full_derivative_false` | Failure of the displayed uniform full-derivative bound even at the zero potential. |
| `classicalHermitianRemainder_derivative_weighted_sobolev_ball` | Corrected full-matrix derivative bound for every nonzero complex spectral parameter. |
| `sourceLemmaG3_weighted_remainder_derivative` | The same corrected estimate on the exact original periodic H1 source balls. |

See [`coverage/APPENDIX_G.md`](coverage/APPENDIX_G.md) for the current complete
comparison of Appendix G's numbered statements, distinct from a claim that
every printed assertion holds unchanged.

### Actual Riccati and Hamiltonian field rescaling

Appendix H's identity u_k(a,c*b)=c*u_k(c*a,b) is now proved for the actual
Riccati recurrence at every order and every complex scalar, including zero.
`NLSRiccatiRescaling.lean` uses recurrence uniqueness and then proves the
corresponding identity for the physical Hamiltonian integrals. No division
by the scalar or smoothness assumption is needed for the classical identity.

`SobolevRiccatiRescaling.lean` transfers the identity to every admissible
Sobolev density in H^(s-n) and to the next weak H^-1 density for an H^s
source. Continuity and dense smooth Fourier sources preserve the original
period-one coefficients. The result includes the H^0 endpoint and does
not impose extra regularity on the highest derivative.

`SobolevHamiltonianRescaling.lean` proves the Hamiltonian identity on the
original H^(k-1) domain and on the sharper H^m domain of H_(2m+1). It also
proves reciprocal field-rescaling invariance for nonzero scalars on both
domains. These are the existing physical Hamiltonians, with their exact
normalization and original smooth integral meaning.

`coverage/APPENDIX_H.md` records the current recurrence, normalization,
weak-source, polynomial, and physical-integral coverage for H.1 and H.2.
The public checks include scalar zero, the top available Sobolev density,
the weak H^-1 endpoint, mass on H^0, and reciprocal scaling of the odd
Hamiltonian on H^1 without imposing H^2 regularity.

Next is a systematic numbered-statement coverage audit beyond the existing
spectral overview, beginning with Sections 2–3. G.2's arbitrary-time
interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: focused module builds, the standalone public probe, and the full
project check passed (6,683 build jobs and all public examples). The axiom
audit passed for 28,476 NLS declarations with only the permitted classical
axioms. The build retains 21 existing warnings and introduces none. The
source inventory check passed for 156 candidate statement labels; this is
not a completeness certificate.

| Public entry point | Scope |
| --- | --- |
| `nlsRiccatiDensity_field_rescaling`, `classicalNLSHamiltonian_field_rescaling` | Actual classical recurrence and physical integral identities for every complex scalar and order. |
| `sobolevRiccatiDensity_field_rescaling` | Equality in the actual lower Sobolev space at every admissible order. |
| `weakSobolevRiccatiDensity_field_rescaling` | Equality in H^-1 at the next weak density, including H^0 sources. |
| `sobolevNLSHamiltonian_field_rescaling`, `sobolevOddHamiltonian_field_rescaling` | Original Hamiltonian regularity and the sharper odd H^m extension, with scalar zero included. |
| `sobolevNLSHamiltonian_reciprocal_rescaling`, `sobolevOddHamiltonian_reciprocal_rescaling` | Nonzero reciprocal rescaling preserves the actual Hamiltonians on both domains. |

See [`coverage/APPENDIX_H.md`](coverage/APPENDIX_H.md) for the current
comparison of the printed recurrence, proof identity, and H.1–H.2 conclusions.

## Section 2 infinity convergence correction

The rendered Section 2 paragraph on printed page 21 asserts Fourier-series
norm convergence without excluding p=infinity. `InfinityTruncation.lean`
now proves the exact correction for every positive weight: universal norm
convergence holds exactly at finite Banach exponents, while an individual
infinity input converges exactly when its weighted coefficients vanish
outside finite sets.

The coefficients 1/w(n) have weighted norm one and every finite Fourier
truncation has error exactly one. `SourceSectionTwoConvergence.lean`
realizes the Sobolev case as an actual period-two tempered distribution
for every real regularity, including negative orders. The same Fourier
sums converge distributionally while failing norm convergence. The
existing finite-exponent and distributional convergence results are retained.

`coverage/SECTION_2.md` records this focused source comparison and
`SOURCE_ERRATA.md` records the missing infinity qualification. The public
checks include p=1, general real regularity, every symmetric cutoff,
the zero-order constant coefficients, and infinity convergence for
finite-p inputs, which may have infinite support.

Next: the scalar bilinear pairing and dual-gradient claims on printed
page 22, followed by the numbered statements in Section 3. This focused
audit does not establish completeness. G.2's arbitrary-time interval norm
remains unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: both focused module builds and the standalone public probe
passed without warnings. The full project check passed all 6,685 build
jobs and public examples. The axiom audit passed for 28,499 NLS declarations
with only the permitted classical axioms. The full build retains 21 existing
warnings and introduces none. The source inventory check passed for 156
candidate statement labels; that count is not a completeness certificate.

## Section 2 physical bilinear pairing

Section 2's printed same-index scalar bilinear pairing is now formally
refuted by the smooth period-one wave exp(2*pi*i*x): its coefficient sum
is one and its actual physical integral against itself is zero. The
corrected pairing reverses one Fourier index. Abstract coefficient duality
remains unchanged; its physical interpretation uses that reflection.

`ArbitraryPeriodBilinearParseval.lean` proves the corrected physical
identity for all positive periods and square-integrable inputs with the
original 1/L factor. It also proves the unchanged sesquilinear formula.
`SobolevBilinearPairing.lean` supplies a bounded bilinear map on every real
Sobolev scale with absolute convergence and the sharp Hölder constant,
including both conjugate infinity endpoints.

`SobolevDistributionPairing.lean` identifies the pairing with normalized
actual distributional action. `SmoothPeriodicTestLift.lean` constructs
an exact Schwartz lift of every smooth period-two test, and
`SmoothPeriodicDistributionPairing.lean` gives the action identity for
all such tests and arbitrary periodic distributions of the stated regularity.
No extra smooth-test growth hypothesis is imposed. The source discrepancy
and the exact scope are recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_2.md`.

Next: arbitrary-positive-period distribution transport and the full
Section 2 dual-gradient representation, including exponent endpoints,
then the numbered Section 3 statements. The dissertation remains incomplete.
G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: the focused builds and standalone public probe passed without
new warnings. The full project check passed all 6,691 build jobs and public
examples. The axiom audit passed for 28,555 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 distributional pairing on every positive period

The corrected Section 2 scalar distributional pairing now holds on every
positive period. `DistributionDilation.lean` constructs continuous linear
rescaling of actual distributions with an exact inverse and the required
inverse Jacobian. Actual translation invariance rescales with the period.

`ArbitraryPeriodDistribution.lean` defines normalized Schwartz coefficient
tests whose periodizations are exactly (1/L) times the negative Fourier
waves. The zero-mode window is therefore normalized by 1/L. Each raw
weighted coefficient is recovered unchanged; every actual periodic
distribution of the stated coefficient regularity has a unique synthesized
representative. Continuous synthesis and distributional Fourier convergence
include the infinity endpoint and all real Sobolev orders. Period two
recovers the existing tests and distributions exactly.

`ArbitraryPeriodDistributionPairing.lean` proves the original smooth-test
action identity for every positive period and both conjugate endpoints.
It also proves existence and uniqueness of the smooth test's actual
normalized Fourier coefficients at every real order and Banach exponent.
The public checks include period three's exact 1/3 normalization, arbitrary
real regularity, p=1 and p=infinity, unique physical reconstruction, and
distributional convergence for the previous norm-convergence counterexample.

The period restriction in the previous scalar-pairing milestone is resolved.
Next: the full Section 2 dual-gradient representation and reflexivity,
with exponent endpoints audited explicitly, then numbered Section 3 results.
The dissertation remains incomplete. G.2's arbitrary-time interval norm
is unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: the focused builds and standalone public probe passed without
new warnings. The full project check passed all 6,694 build jobs and public
examples. The axiom audit passed for 28,624 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 full scalar duality and reflexivity

Section 2's scalar full-dual identification is now proved for every finite
Banach exponent, including p=1 with conjugate exponent infinity.
`FullDuality.lean` constructs the representative of an arbitrary bounded
complex functional, proves exact operator-norm equality, and bundles the
pairing as a linear isometry onto the entire continuous dual.

`SobolevFullDuality.lean` transports this result to every real Sobolev order
under the corrected physical bilinear pairing. Representation is unique,
the norm remains exact, and the coefficient at n is the original functional
applied to the raw mode -n. `SobolevScalarGradient.lean` gives a bounded linear
recovery operator, analytic scalar gradients on the original analytic domain,
and the complete Hessian identity. The p=1 endpoint is included throughout.

`Reflexivity.lean` proves surjectivity of the canonical evaluation map into
the continuous double dual for every positive weight and every 1<p<infinity.
The conjugate exponent is obtained automatically; the final theorem does
not require the caller to supply a second finite exponent. Together with
the existing intrinsic periodic-distribution identification, these scalar
coefficient results apply to the source's Fourier-Lebesgue spaces.

Next: finish the two-component gradient audit with the original signed
coefficients and the distinct infinity pair norm, and audit the unrestricted
infinity-source gradient claim before moving to numbered Section 3 results.
This milestone proves scalar duality and reflexivity; it does not claim
completion of the pair-gradient or endpoint audit. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,704 build jobs and public
examples. The axiom audit passed for 28,692 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 pair gradients and the infinity obstruction

Section 2's two-component gradient representation is now proved for all
finite source exponents and every real Sobolev order. The finite-conjugate
case retains the source q-sum norm; the p=1 case returns a gradient in the
separate frequencywise sum-norm infinity space. Both representations are
unique, bounded linear in the full functional, and analytic on the original
analytic domain. The conversion from signed pair coefficients to physical
scalar Fourier coefficients reflects the first component in both factors
and preserves the corrected physical pairing.

`SobolevPairCotangent.lean` supplies the complete component representation
and uniqueness. `SobolevPairGradient.lean` packages the two original target
norms, with bounds 2^(1/q) and 2 respectively. These are proved bounds, not
claims that the pair gradient is always isometric to the dual. Recovery of
prescribed endpoint components is exact; equal components have twice the
scalar norm, including the inverse-weight infinite-support example.

`InfinityDuality.lean` proves that full coefficient-dual representation is
surjective exactly when the source exponent is finite. A Hahn-Banach
functional vanishes on every finite sequence but is nonzero on one, so it
has no l1 representative. It is itself an everywhere-analytic functional
whose derivative has no coefficient gradient at any point.
`SobolevInfinityDuality.lean` transports the obstruction to every real
Sobolev order and the original weighted infinity pair norm.

The scalar duality statement on page 21 explicitly assumes finite p and
remains valid. The gradient paragraph on page 22 must retain that source
restriction: interpreting it for arbitrary infinity-source analytic
functionals is false, even with the corrected physical pairing. In
particular, the later automatic Poisson-regularity sentence cannot use
analyticity alone to supply a gradient for an infinity-domain functional.
The exact scope is recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_2.md`.

Next: audit the Section 2 Poisson bracket and its automatic regularity
claim against these full gradient APIs, then the numbered Section 3 results.
The dissertation remains incomplete. G.2's arbitrary-time interval norm
is unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,708 build jobs and public
examples. The axiom audit passed for 28,770 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 Sobolev Poisson pairing on common physical states

Section 2's Poisson pairing now covers every real Sobolev order and
conjugate gradient exponents, with the printed -iJ sign and matrix.
`SobolevBivector.lean` proves boundedness, absolute convergence, the signed
Fourier formula, and antisymmetry with explicit opposite-order transport.
The cross-component sum uses equal signed indices: reflecting the first
signed component converts it to the corrected physical scalar pairing,
which still uses opposite indices.

`ConjugateSobolevBracket.lean` applies this pairing to the full differentials
on reciprocal Sobolev domains when both source exponents are finite.
`SobolevCommonState.lean` constructs their closed Banach intersection, with
the maximum of the two original source norms. Every pair of representatives
with equal raw signed coefficients belongs to this intersection, and the
two representatives synthesize the same actual distribution pair on every
positive period.

`SobolevCommonBracket.lean` evaluates both functionals at that common state.
It proves the physical formula, automatic absolute convergence, analyticity
on the entire intersection of the analytic domains, and the left product
rule. The recovered gradients represent the complete ambient differentials
on every direction. The bracket bound is twice the product of the original
operator norms; no extra Hilbert regularity hypothesis is imposed.

`SobolevEndpointBivector.lean` retains the original l1 and frequencywise
sum-norm infinity pair spaces. Given represented gradients, its pairing is
bounded and absolutely convergent; analytic gradient fields give an analytic
bracket. This does not extend full-gradient existence to arbitrary analytic
functionals on an infinity source space, which the preceding milestone
refuted.

Next: formally compare this interface with the existing physical source
bracket and finish the remaining bracket algebra and domain audit, then
continue with numbered Section 3 results. Core bivector antisymmetry and a
left product rule do not by themselves establish the full bracket algebra
or Jacobi identity on these Sobolev domains. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither
proposed spectral-height correction is adopted. The optional original m=1
sharpening remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,713 build jobs and public
examples. The axiom audit passed for 28,868 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 bracket compatibility, domain exchange, and Hilbert Jacobi

The new full-gradient Sobolev bracket now agrees with the established
physical source bracket on their order-zero overlap.
`SobolevSourceCompatibility.lean` gives the signed-to-physical coordinate
equivalence, including exact first-component frequency reversal, and the
full differential mode formula at every real Sobolev order. Its comparison
allows any finite conjugate pair p,q and an ambient exponent r>=2 with
p<=r and q<=r. The two functionals are restricted from the same ambient
source space. Equality holds for actual brackets at every common physical
base point under differentiability of those ambient functionals.

`SobolevBracketSwap.lean` proves antisymmetry on the entire common Sobolev
domain for every real order and finite conjugate source pair. It explicitly
exchanges the two ambient domains, normalizes the double negative order
without changing signed coefficients, and exchanges the representatives of
the same state. The right product rule is also proved, complementing the
previous left product rule.

`SobolevZeroBracket.lean` defines a single-domain bracket from the full
Sobolev differentials at order zero and exponent two. It agrees both with
the common-state bracket and, through the coordinate equivalence, with the
existing physical bracket. This proves Jacobi for arbitrary functionals
analytic at the base point, analytic closure on their original domain,
antisymmetry, both product rules, left additivity under differentiability,
and scalar homogeneity (including scalar zero).

These results do not assert that arbitrary reciprocal Sobolev intersections
are closed under nested brackets. The Jacobi transfer is specifically on
the order-zero Hilbert domain; the common-domain antisymmetry and product
rules hold for every real order. The legacy ambient comparison at r=infinity
uses its existing maximum pair norm and finite-exponent restrictions; it
does not imply full coefficient-gradient representation on the original
infinity source norm. The previously proved infinity obstruction remains.

Next: audit the general weighted sesquilinear product and the normalized
periodic action of locally integrable functions in Section 2, then resume
the numbered Section 3 spectral statements. The dissertation
remains incomplete. G.2's arbitrary-time interval norm is unresolved;
neither proposed spectral-height correction is adopted. The optional
original m=1 sharpening remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,716 build jobs and public
examples. The axiom audit passed for 28,936 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 sesquilinear duality and physical pairings

Section 2's sesquilinear product is now proved on the full real Sobolev
scale and at both conjugate endpoints. `SobolevSesquilinearPairing.lean`
bundles physical conjugation as a conjugate-linear isometric involution:
it conjugates coefficients and reverses their Fourier indices. Composing
the corrected bilinear product with this involution gives precisely the
printed same-index sesquilinear sum. The sum converges absolutely, has a
constant-one norm bound, is jointly continuous, and is complex linear in
the first variable and conjugate linear in the second.

`SobolevPairSesquilinear.lean` adds the two signed components. The product
has a constant-one bound in the original finite pair norms, and in both
endpoint orientations using the separate frequencywise sum-norm infinity
space. All three pair products are jointly continuous and absolutely
convergent. Reflecting both first components recovers the physical scalar
Fourier convention without changing the product. The maximum product norm
is used only as an auxiliary continuity coordinate, not as the source
infinity norm.

`SobolevSesquilinearDuality.lean` identifies the entire scalar continuous
dual at every finite source exponent, including one, with a unique
opposite-order representative of exactly the operator norm. This Riesz
map is a conjugate-linear isometry; multiplying a functional by i multiplies
its representative by -i. Its coefficient at n is the conjugate of the
functional on the raw mode n. The infinity-source analytic counterexample
persists with this convention, so no unrestricted infinity Riesz or gradient
claim is introduced.

`SobolevSesquilinearDistributionPairing.lean` identifies the product with
actual periodic distributional action on a conjugated smooth test for every
positive period. Every smooth periodic test supplies its unique coefficient
representative automatically. The original normalized physical L2 integral
formula is also proved, retaining the factor 1/L. These statements keep the
sesquilinear same-index formula distinct from the corrected opposite-index
bilinear formula.

Next: prove the normalized periodic action for locally integrable periodic
functions, then resume the numbered Section 3 audit. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,720 build jobs and public
examples. The axiom audit passed for 29,013 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 normalized L1 periodic action

Section 2's normalized action is now proved for locally integrable data on
any positive period. `PeriodicL1Functional.lean` constructs the bounded
functional on continuous circle tests from interval-integrable input. Its
operator norm and every actual Fourier coefficient are bounded by the
normalized L1 norm. No square-integrability or boundedness hypothesis is
needed on the input.

`PeriodicL1Pairing.lean` applies that functional to the uniformly convergent
Fourier series of a smooth periodic test. The resulting opposite-index
coefficient sum equals the physical integral with exactly the factor 1/L.
The proof handles arbitrary positive periods directly.

`PeriodicL1Distribution.lean` realizes these bounded coefficients as an
actual periodic tempered distribution. Its normalized windowed action on
every smooth periodic test equals the same integral, and its Fourier
coefficients are exactly the normalized physical coefficients. The product
series converges absolutely. The distribution is unique among periodic
tempered distributions with these coefficients and depends only on the
almost-everywhere class on the fundamental interval. Conjugating the test
gives the corresponding sesquilinear action. Local integrability supplies
the interval hypothesis; the construction also works for the periodic
extension of arbitrary interval-integrable data.

This closes the pending normalized periodic smooth-test action obligation
on printed page 21. It does not assert an additional global real-line
integral formula for arbitrary Schwartz tests. The existing infinity norm
convergence, scalar pairing, and infinity duality qualifications remain.

Next: audit Section 3's numbered statements, starting with Proposition 3.1.
Its printed height must retain the existing qualification from Theorem 1.1;
neither proposed height correction is adopted. The dissertation remains
incomplete. G.2's arbitrary-time interval norm and the optional original
m=1 sharpening remain unresolved.

Validation: focused builds and the standalone public probe passed without
warnings, including a non-unit-period normalization check. The full project
check passed all 6,723 build jobs and public examples. The axiom audit passed
for 29,053 NLS declarations with only the permitted classical axioms. The
full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Proposition 3.1 on the full period-two source space

Proposition 3.1 (printed page 23) now has an explicit statement on the entire
period-two potential space with the original finite-exponent component-sum
norm. The earlier printed-height source theorem only covered embedded
period-one potentials. `PeriodTwoPrintedHeightCounting.lean` supplies the
full period-two neighborhood theorem, without an even-support restriction.

For 1<=p<=4, one open convex neighborhood containing the potential and zero
supports all sufficiently large cutoffs, the original norm-dependent
height, exact central and disk algebraic multiplicities, exhaustion, and
analytic moving rectangular projections. The original source norm occurs
in the height; the maximum norm is used only in the equivalent operator
coordinates. At every finite p, a separate theorem retains the established
height-N qualitative counting data on the original source space.

`Proposition3_1.lean` bundles the actual printed clauses: discreteness,
two eigenvalues per distant disk counted algebraically, the central count
4N+2, conditional parity and its central dimensions, exhaustion, and
real-type spectral reality. The conditional disk parity also implies the
actual pointwise unit-translation law of every finite-exponent eigenfunction.

The same module transfers the existing balanced dyadic counterexample to
the full period-two source space without changing its original norm. For
every integer P>=100000000, it gives a source of norm at most 1/16 and an
actual spectral point outside the printed box and high disks for every
cutoff. `not_proposition3_1_all_p` explicitly refutes the unrestricted
printed proposition at exponent 100000000. This is a source qualification,
not a replacement-height theorem; no proposed correction is adopted.

Next: audit Lemma 3.2, explicitly checking its operator norms in the source
pair norms, then continue through Section 3. The dissertation remains
incomplete. The earlier Section 2 endpoint and pairing corrections, G.2's
unresolved arbitrary-time interval norm, and the optional original m=1
sharpening remain as recorded.

Validation: focused builds and a standalone public probe passed without
warnings. The probe covers the p=4 endpoint, odd Fourier support, original
norms, central parity counts, all-finite-p qualitative counting, and the
concrete refutation. The full check passed all 6,725 build jobs and public
examples. The axiom audit passed for 29,081 NLS declarations with only the
permitted classical axioms. The build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Lemma 3.2 in the original pair norms

Lemma 3.2 (printed pages 23–24) is now checked in the original
component-sum pair norms. `SourceFreeResolvent.lean` transports the actual
free resolvent through the coefficient-preserving norm equivalences.
Clause (i) is compact in the original l1 space, and the same compactness
holds on every finite-exponent source space. Clause (iii)'s printed
8p/r estimate holds in the original p-to-one norms; the proof gives 4p/r.

The printed clause (ii) is false in these norms, already at p=2.
`SourceFreeResolventCounterexample.lean` uses lambda=i/10000 and a vector
with both zero-mode coefficients equal to one. The input norm is exactly
sqrt(2), the output norm is 20000, and the printed operator bound is 10800.
The output/input ratio exceeds that bound. The parameter is off the free
lattice with nonzero imaginary part, and the input is a finite, smooth
Fourier vector. `not_lemma3_2_ii_original_norms` explicitly refutes the
printed assertion in this domain.

`PairComponentHolder.lean` proves the exact two-component comparison
factor 2^(1-1/p), including p=1, and its attainment on equal components.
The original p-to-one free resolvent has a proved corrected height bound
with this factor multiplying the printed expression. A zero-mode lower
bound also proves that its pole term must account for this factor.
At p=1 the factor is one and the printed height bound remains valid.
The older maximum-product bound remains valid as stated in its own norm;
it does not certify the original component-sum operator estimate. The
corrected estimate is recorded separately, not silently substituted for
the false printed clause.

Next: audit Corollary 3.3 in the source norms and its dependence on the
maximum-product Neumann estimate, then continue Section 3. The failure
of the printed p-to-one bound alone does not refute the corollary's
resolvent region. The dissertation remains incomplete; the existing
spectral-height, Section 2, G.2, and optional m=1 qualifications remain.

Validation: focused builds and the standalone public probe passed without
warnings, covering compactness in the actual l1 norm, both endpoint and
finite-exponent factors, the pole lower bound, the concrete counterexample,
and the printed strip bound. The full check passed all 6,728 build jobs
and public examples. The axiom audit passed for 29,124 NLS declarations
with only the permitted classical axioms. The build retains 21 existing
warnings.
The source inventory check passed for 156 candidate labels; this count
is not a completeness certificate.

## Corollary 3.3 in the original source norms

Corollary 3.3 (printed page 24) is now proved for every finite Banach
exponent on the full period-two potential space in the original
component-sum norms. Its printed sufficient region remains valid:
`(4p/abs(Im(lambda))^(1/p)+1/abs(Im(lambda)))*norm(phi)<1`, with nonzero
imaginary part so both denominators are meaningful. This follows from
the valid maximum-product Neumann bound and the contractive conversion
of the original potential norm. It does not use the false original-norm
p-to-one estimate from Lemma 3.2(ii).

`SourceResolvent.lean` defines the actual operator, spectral pencil,
one-derivative inverse, base-space resolvent, and complete resolvent set
in the original norms. The source resolvent set equals the established
maximum-product resolvent set. Both inverse identities hold throughout
that set, the base-space inverse factors through the coefficient-preserving
domain inclusion, and the pencil is exactly lambda times inclusion minus
the source operator. The resolvent is compact and analytic on its full
natural set; its complement has the discrete subspace topology.
At zero potential it agrees with the original free resolvent at every
parameter off the free lattice, including real parameters.

`SourceCorollary3_3.lean` proves the numerical region is open and nonempty,
with one common height for every original-norm ball of potentials.
`sourceCorollary3_3` bundles the printed conclusion, actual resolvent-set
membership, both inverse identities, and discreteness. The p=1 endpoint
is included. No period-one support restriction is imposed.

Next: audit Lemma 3.4 in the original p-to-one pair norms, tracking the
component constants in the existing sandwich-resolvent estimate. The
dissertation remains incomplete, and all previously recorded source
qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The source inventory check passed for 156 candidate labels;
this count is not a completeness certificate. The full check passed all
6,730 build jobs and public examples. The axiom audit passed for 29,165
NLS declarations with only the permitted classical axioms. The build
retains 21 existing warnings; the new modules add none.

## Lemma 3.4 in the original pair norms

Lemma 3.4 (printed page 25) is now proved in the original component-sum
pair norms for every finite Banach exponent and every period-two
potential. `SourceDoubleResolvent.lean` constructs the actual map
R0 Phi R0 from the original p space to the original l1 space. Its
composition identity uses the original-norm free resolvent and potential
convolution, and both coefficient formulas are proved in the library's
raw scalar Fourier convention.

The explicit admissible constant is c_p=64p^2. The maximum-product
estimate has constant 32p^2; transporting its l1 output to the original
sum norm costs at most two, while the input and potential conversions
are contractive. The same comparison applies to the Fourier remainder.
The source only asks for a constant depending on p, so this verifies its
claim without asserting sharpness. The numerical discrepancy in
Lemma 3.2(ii) is not used or altered.

`SourceLemma3_4.lean` supplies `sourceLemma3_4`, with the positive constant
quantified before the potential, radius, spectral parameter, and strip
index. Membership in a permitted punctured strip proves that the free
inverse exists. The p=1 endpoint and both signs of the strip index are
included. The zero strip is controlled by the full potential remainder;
Lean's totalized division makes its frequency term zero.

The proof reuses `sourceFourierTail`, including its exact boundary cutoff,
norm monotonicity, and convergence to zero, and adds its contraction
bound. The explicit sandwich bound tends to zero, yielding uniform
smallness of the actual original-norm operator on all sufficiently high
punctured strips at every fixed admissible radius.

Next: Corollary 3.5 in the original source topology, with one neighborhood
and cutoff controlling the full stated complement of the central box
and high disks. The dissertation remains incomplete, and earlier source
qualifications remain in force.

Validation: the focused builds and standalone public probe passed without
warnings, including the original-norm composition, quantified constant,
p=1 endpoint, remainder boundary modes, and uniform smallness. The source
inventory check passed for 156 candidate labels; this is not a completeness
certificate. The full check passed all 6,732 build jobs and public
examples. The axiom audit passed for 29,183 NLS declarations with only
the permitted classical axioms. The build retains 21 existing warnings;
the new modules add none.

## Corollary 3.5 in the original source topology

Corollary 3.5 (printed page 26) is now proved on the entire period-two
source space for every finite Banach exponent, using the original
component-sum norm for both the potential topology and the resolvent's
base space. `SourceCorollary3_5.lean` gives one positive cutoff and one
open, convex, connected neighborhood containing the potential and zero.
Every potential in that neighborhood has its actual compact analytic
resolvent on the precise printed box-and-disk complement.

The geometry is unchanged: the central box has strict real-part bounds
and non-strict imaginary-part bounds; the removed high disks are open
quarter-pi disks with abs(n)>N. The proof preserves the vertical boundary
case abs(n)=N in the strip argument. The supporting height-and-strips
theorem includes equality at the horizontal height, so it also handles
horizontal contour points which lie inside the printed central box.

`sourceCorollary3_5_all_larger` proves the same conclusions for every
larger cutoff on the same neighborhood. The full source resolvent-set
inclusion is explicit, and the complement of that actual set lies in the
stated box-and-disk union. The construction pulls back the established
maximum-product neighborhood through the coefficient-preserving norm
equivalence, then uses the actual original-norm resolvent. No period-one
support restriction, p>1 restriction, or printed-height assumption is
introduced. Convexity also controls the entire line from zero to the
potential with one cutoff.

Next: equation (1.4), transporting the actual Cauchy-Riesz contour
projectors and their source analyticity to the original norms, followed
by the parity subspaces and Lemma 3.6. The dissertation remains incomplete;
all earlier source qualifications remain in force.

Validation: the focused build and standalone public probe passed without
warnings, covering the common neighborhood at all finite exponents,
the p=1 line segment, horizontal-boundary admissibility, and actual
inverse identities in the original domain. The source inventory check
passed for 156 candidate labels; this is not a completeness certificate.
The full check passed all 6,733 build jobs and public examples. The axiom
audit passed for 29,188 NLS declarations with only the permitted classical
axioms. The build retains 21 existing warnings; the new module adds none.

## Equation (1.4) in the original norms

Equation (1.4) (printed page 26) now has actual Cauchy-Riesz contour
projectors in the original component-sum norms. `SourceResolventContours.lean`
defines normalized, positively oriented circle integrals and four-edge
rectangle integrals of `sourceResolvent`. The central projector uses the
actual lower-left and upper-right corners of the height-N box.

For admissible contours, bounded linear conjugation commutes with these
operator-norm integrals. The resulting equalities identify them with the
established maximum-product contour operators. Integrability and evaluation
on vectors are proved in the original norm. The circle and central rectangle
operators are idempotent and compact, and their ranges are finite-dimensional.
The circle integral also has analytic dependence on the potential near every
source for which its circle lies in the full resolvent set.

`SourceEquation1_4.lean` proves the simultaneous statement. One positive
cutoff and one open, convex, connected original-norm neighborhood contain
the potential and zero. For every larger cutoff, the central rectangular
projector and every quarter-pi circle projector with abs(n)>N are analytic
on that same neighborhood. Every contour is in the actual source resolvent
set, and every corresponding actual integral is a compact finite-rank
projection. All finite Banach exponents, including p=1, and all period-two
potentials are covered without an even-support restriction.

The central boundary is established separately on all four edges, including
the horizontal edges inside the printed box. The integrals are defined as
integrals of the original resolvent, and their conjugation identities are
proved rather than used as replacement definitions. No quantitative claim
of isometry between the original norm and the maximum-product norm is made.

Next: the closed complementary parity subspaces and Lemma 3.6 in the original
norms, then the restricted projectors of equation (1.5). The dissertation
remains incomplete; earlier source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers the literal operator integrals, evaluation,
projection identities and finite rank, the common p=1 neighborhood, and
the full central-boundary package at every finite exponent. The source
inventory check passed for 156 candidate labels, not a completeness
certificate. The full check passed all 6,735 build jobs and public
examples. The axiom audit passed for 29,216 NLS declarations with only
the permitted classical axioms. The build retains 21 existing warnings;
the new modules add none.

## parity subspaces and Lemma 3.6 in the original norms

The closed even and odd subspaces immediately before Lemma 3.6 (printed
page 26) are now implemented in the original component-sum norms.
`SourceParity.lean` proves the exact printed coefficient conditions,
closedness, complementary bounded projections, and a topological direct
sum. The masks are contractive for every finite Banach exponent. Frequency
doubling gives a linear isometric equivalence from period-one coefficient
pairs onto the even subspace, with an explicit inverse reading index 2n.

`SourceLemma3_6.lean` proves that the actual Zakharov-Shabat operator,
with its original one-derivative domain, preserves both parities for
period-one potentials at every finite exponent, including p=1.
`sourceLemma3_6` supplies the even support automatically through the
canonical period-one embedding; a separate entry point accepts explicit
even support. The operator intertwines the domain and base parity masks.
The actual source resolvent and admissible circle integral commute with
the base parity projections.

An explicit odd potential sends an even domain vector to an output with
a nonzero odd coefficient. This verifies that the period-one assumption
cannot be dropped; it is not a correction to the source, whose proof
states this assumption explicitly. No claim identifies the infinity
endpoint's source pair norm with the maximum-product norm.

Next: equation (1.5), with actual continuous linear endomorphisms of each
parity subspace and analytic dependence on a neighborhood within the
period-one potential space. The dissertation remains incomplete; earlier
source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers both printed support conditions, negative
frequencies, the topological direct sum, finite-exponent contraction,
the isometry and inverse, domain invariance including p=1, nonconstant
mode coupling, necessity of period one, and commutation with the actual
resolvent and circle integral. The source inventory check passed for 156 candidate labels, not a
completeness certificate. The full check passed all 6,737 build jobs and
public examples. The axiom audit passed for 29,285 NLS declarations with
only the permitted classical axioms. The build retains 21 existing
warnings; the new modules add none.

## equation (1.5) in the original period-one topology

Equation (1.5) (printed page 26) now has actual bounded endomorphisms of
the original-norm parity subspaces. `SourceParityRestriction.lean` constructs
the central rectangular and circle projectors with each parity subspace
as both domain and codomain. For even-supported potentials and admissible
contours, their values agree exactly with the actual original-norm contour
integrals on those subspaces. They are idempotent and have finite-dimensional
range. The restricted range is exactly the part of the ambient range lying
in the selected parity subspace.

The construction uses bounded compression on the space of operators.
Commutation with parity proves that this compression equals restriction;
the rectangular commutation result covers all four edges. Analyticity of
compression transfers analytic dependence from the ambient projectors.

`SourceEquation1_5.lean` gives one positive cutoff and one open, convex,
connected neighborhood in the original period-one potential coordinates,
containing both the potential and zero. Simultaneously for both parities,
every larger central projector and every quarter-pi circle with abs(n)>N
is analytic on that neighborhood, agrees with the actual integral there,
and is a finite-rank projection on the parity subspace. The canonical
`periodOnePair` embedding supplies even support. Every finite Banach
exponent, including p=1, is covered.

No period-one assumption is dropped, and the neighborhood is open in the
period-one parameter space specified by the source. The fixed-norm-height
qualifications in Proposition 3.1 and Theorems 1.1 and 1.4 remain unchanged.

Next: the rank calculations following equation (1.5), then Lemma 3.7.
The dissertation remains incomplete; earlier source qualifications remain
in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe checks typed domains and codomains, equality with the
literal source resolvent integral, the exact restricted range, idempotence
and finite rank at p=1, and the common neighborhood for all finite exponents,
parities, and cutoffs. The source inventory check passed for 156 candidate
labels, not a completeness certificate. The full check passed all 6,739
build jobs and public examples. The axiom audit passed for 29,313 NLS
declarations with only the permitted classical axioms. The build retains
21 existing warnings; the new modules add none.

## original-norm ranks and periodic counts after equation (1.5)

The rank calculations and counting conclusions on printed page 27 now apply
to the actual original-norm contour projectors. The central rectangle has
rank 4N+2, and every distant quarter-pi circle has rank two. For period-one
potentials, the typed central restriction has rank 2N+2 in the parity of N
and 2N in the other parity. A distant circle has rank two in the parity of
its index and rank zero in the opposite parity, including negative indices.

`ConjugatedRanges.lean` gives linear range equivalences under continuous
linear conjugation, including intersections with transported subspaces.
`SourceContourRanks.lean` applies these to the actual source integrals and
typed parity restrictions. The norm conversion is not claimed to be an
isometry. Within the original norm, the typed restricted range is linearly
isometric to the corresponding ambient range intersection.

`SourcePeriodicCounting.lean` packages the numeric ranks together with the
established algebraic multiplicities of the coefficient operator, under
coefficient-preserving norm conversion. The disk counts are two with
algebraic multiplicity, and the central count is 4N+2. One positive cutoff
and one open, convex, connected original-norm neighborhood containing the
potential and zero support all larger cutoffs simultaneously. The actual
central and circle projectors are analytic there. A period-one version
also gives analytic typed restrictions and the same complete counting data.
All finite Banach exponents, including p=1, are covered.

Every vector in a distant contour range has the index's parity for an
even-supported potential. Eigenvectors in the actual original-norm domain
inherit that parity, and their continuous Fourier representatives satisfy
the corresponding unit-translation law. The full original-norm spectrum
is exhausted by the central cluster and unique high disks; its exterior
resolvent is analytic. Real-type potentials have real spectrum, without
an even-support restriction.

The central box here has height N, as in Corollary 3.5 and equations
(1.4–1.5). This does not resolve or adopt a correction to the separate
printed norm-dependent height in Proposition 3.1 and Theorems 1.1 and 1.4.
The positive cutoff and contour admissibility hypotheses are retained.

Next: Lemma 3.7, the analytic midpoint and squared-gap trace expressions
in the original source norms. The dissertation remains incomplete;
earlier source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers full ranks and algebraic counts on one neighborhood,
both central parity formulas, negative odd disk indices, the p=1 segment to
zero, analytic typed restrictions, physical antiperiodicity, spectral reality,
and exhaustive source-spectrum classification. The source inventory check
passed for 156 candidate labels, not a completeness certificate. The full
check passed all 6,742 build jobs and public examples. The axiom audit passed
for 29,407 NLS declarations with only the permitted classical axioms. The
build retains 21 existing warnings; the new modules add none.

## Lemma 3.7 in the original source norms

Lemma 3.7 (printed page 27) now uses traces of the actual original-norm
operator restriction. `SourceContourTrace.lean` lifts each contour-range
vector into the original one-derivative domain and proves that inclusion
recovers that same vector. Its intrinsic endomorphism acts by `sourceOperator`
on this lift. A proved range conjugation identifies its power traces with
the established coefficient-space traces; the source functions are defined
from the intrinsic traces themselves.

The midpoint is one half of the first trace, and the squared gap is twice
the second trace minus the square of the first. At rank two, the trace of
the centered square is exactly half the squared gap, as printed. These
identities hold for coincident eigenvalues and possible nontrivial Jordan
blocks. The functions agree with the midpoint and squared difference of
the algebraically counted enclosed pair. Free-potential values are pi*n
and zero, respectively.

`SourceContourReduction.lean` constructs analytic ambient transport, inverse
transport, and the operator on a fixed reference range, on an open neighborhood.
The concrete continuous linear range isomorphism is induced by that transport.
Its domain lift represents the transported vector exactly, and the transported
operator intertwines the actual original-domain operator. All power traces,
and both displayed rank-two formulas, agree in the intrinsic and fixed-range
representations.

`SourceLemma3_7.lean` supplies one positive cutoff and one open, convex,
connected original-norm neighborhood containing the potential and zero.
The midpoint and half-squared-gap functions are analytic there for every
high disk. The same neighborhood retains the actual counting data, the
trace formulas, and the enclosed eigenvalue pair with its algebraic
multiplicities. Every finite Banach exponent, including p=1, is covered.
The explicit period-one version uses the original period-one parameter
topology. The norm conversion is not claimed to be isometric.

Next: Section 4, beginning with the classical Dirichlet/Neumann domains
in equation (1.6) and their AKNS representation. The dissertation remains
incomplete; earlier source qualifications remain in force.

Validation: `./scripts/check.sh` passed: 6,745 build jobs, public examples, and the axiom audit of 29,480 NLS declarations. The build retains 21 existing warnings; the new modules and standalone public probe are warning-free. The source inventory check passed with 156 candidate labels (not a completeness certificate).

## Section 4 classical domains and AKNS conjugation

The beginning of Section 4 (printed pages 28–29) now has the original
classical AKNS domain and operator, with exact identifications of equation
(1.6), the component system (1.7), and the normalized coordinate matrix.
`AKNSCoordinates.lean` proves both matrix inverses, both boundary conditions,
and the derivative/potential intertwining for arbitrary complex coordinates.

`IntervalH1Linear.lean` supplies linear closure of the original interval H¹
class. `AKNSClassicalDomain.lean` proves equivalence of the original Sobolev
endpoint domains, actual derivative intertwining almost everywhere, and
equivalence of the physical eigenvalue equations. No regularity outside
[0,1] or endpoint periodicity is assumed.

`AKNSPhysicalNorms.lean` constructs `aknsL2Equiv` on the actual Lebesgue
component-sum L² space and proves exact preservation of the original H¹
norm. `AKNSIntervalOperator.lean` constructs the actual closed-interval AKNS
domain, characterizes membership by original H¹ functions and the printed
endpoint conditions, and identifies its norm with the physical H¹ norm.
The inclusion is injective and dense. Both inclusion and operator are
conjugated by the L² unitary and domain H¹ isometry. Their values are proved
to be the original function and actual AKNS differential expression almost
everywhere, for arbitrary L² potentials and either boundary condition.

The page 29 assertion phi = T(q,p) has a normalization error: the potential
map is (q+i*p,q-i*p) = sqrt(2) T(q,p), while T remains the normalized vector
matrix. This agrees with page 19. Lean proves the corrected relation and
counterexamples to the printed normalization, including the actual operator
on constant smooth data. The correction is confined to the potential map.

Next: the even/odd and signed-swap extensions and Lemma 4.1, auditing the
existing physical transfer against the original source spaces. The full
dissertation remains incomplete; all earlier qualifications remain in force.

Validation: `./scripts/check.sh` passed: 6,750 build jobs, public examples, and the axiom audit of 29,625 NLS declarations. The build retains 21 existing warnings; the five new modules and standalone public probe are warning-free. The source inventory check passed with 156 candidate labels (not a completeness certificate).

## reflection formulas and Lemma 4.1

The even/odd AKNS extensions on printed pages 28–29 are now connected
pointwise to the signed-swap ZS extensions. `AKNSReflection.lean` proves
both boundary cases, the inverse-coordinate formulas, and the common
potential extension (q even, p odd). It constructs actual periodic H¹
circle representatives with reconstruction on the whole closed period.
The extended functions solve the AKNS equation almost everywhere, and
original L² potentials have square-integrable reflected potentials.

`SourceLemma4_1.lean` proves both parts of Lemma 4.1 using actual periodic
H¹ representatives, exact closed-period reconstruction, and the reflected
physical operator equation. The potential is Dirichlet-reflected for both
boundary conditions; only the eigenfunction's reflection sign varies.
This physical implication does not need an extra potential integrability
assumption beyond its given almost-everywhere equation.

For original L² potentials, the file defines the exact normalized physical
Fourier coefficients in `CoeffPair 2` and the original weighted
`WeightedCoeffPair (Weight.sobolev 1) 2` domain. Their reconstruction and
coefficient identities are proved. The extended vector solves the actual
`sourceOperator` equation and is nonzero whenever the original interval
function is nonzero. Every original boundary eigenvalue lies in the actual
source spectrum. The spectrum is exactly the union of the two original
interval eigenvalue sets, establishing the paragraph following the lemma.
The exhaustion statement is a set identity; it adds no new multiplicity
formula. No maximum-norm conversion is claimed to be isometric.

Next: the Fourier representations (1.8)–(1.9) on page 30, followed by the
original-space extension/isomorphism assertions. The full dissertation
remains incomplete, and the earlier normalization correction is retained.

Validation: `./scripts/check.sh` passed: 6,752 build jobs, public examples, and the axiom audit of 29,664 NLS declarations. The build retains 21 existing warnings; both new modules and the standalone public probe are warning-free. The source inventory check passed with 156 candidate labels (not a completeness certificate).

## Fourier representations (1.8)–(1.9)

`SourceBoundaryFourier.lean` proves the printed series on page 30 in the
original component-sum coefficient norm and normalized physical period-two
L² norm. The source boundary modes are identified with the established
signed free modes and with the actual waves
(epsilon*exp(-i*pi*n*x), exp(i*pi*n*x)). Both boundary signs and the reversed
first-component frequency are explicit.

For arbitrary original L² interval data, the reflected function's normalized
Fourier coefficients equal the printed half-interval amplitudes. The
coefficient is exactly one half of the original sesquilinear component-sum
pairing with the physical boundary mode. The series converges in the
original `CoeffPair 2` norm. An actual linear isometric Fourier synthesis
transfers it to the physical component-sum L² space, and the sum is proved
to represent the actual signed reflection almost everywhere on [0,2].

The reflected coefficients have exactly the original interval L² norm:
normalizing the doubled period cancels the doubled reflection energy.
`sourceEquation1_8_1_9` supplies the printed H¹-input statement, with an
actual physical sum, its convergent half-pairing series, and its exact
energy. The stronger arbitrary-L²-input theorem is also public.

No endpoint condition is added to the page 30 input. Such a reflected
function may jump at the joins, so the asserted convergence is L², not
uniform or H¹ convergence. No correction to (1.8)–(1.9) is needed; the
page 29 AKNS potential-normalization correction is retained.

Next: the closed complementary Fourier–Lebesgue boundary subspaces after
(1.9), in the original norms, followed by Lemma 4.2. The dissertation
remains incomplete; earlier qualifications remain in force.

Validation: `./scripts/check.sh` passed: 6,753 build jobs, public examples,
and the axiom audit of all 29,752 NLS declarations. The build reports
21 existing warnings; the new module and standalone public examples are
warning-free. The source inventory check passed for 156 labels; this is
not a completeness certificate.

## Original boundary spaces and Lemma 4.2 (pages 30–31)

`SourceBoundarySpaces.lean` supplies both source boundary subspaces in
`WeightedCoeffPair` for finite exponents and in `WeightedCoeffPairInfty`
for the original signed coupled-supremum endpoint. At every real Sobolev
order both are closed, algebraically complementary, and topologically
complementary. Membership retains frequency reversal in scalar coordinates
and same-index signs in the source infinity coordinates.

`sourceWeightedBoundaryAmplitudeEquiv` and its infinity counterpart are
continuous linear equivalences, with exact original-norm factors 2^(1/p)
and 2 respectively. `SourceBoundarySeries.lean` supplies unit raw weighted
modes, their norm-convergent finite-p expansions, and actual tempered-
distribution expansions for all Banach exponents. The distributional modes
are identified by the ordinary physical wave integrals. Their sum is the
actual synthesis of the original coefficient pair, including at infinity.
Surjectivity of the amplitude equivalences identifies every boundary
element with such a series; infinity-norm convergence is not asserted.

`sourceClassicalBoundaryEquiv` establishes Lemma 4.2 using the original
physical H¹ classical domain and the original (1,2) weighted pair norm.
`sourceClassicalBoundaryEquiv_ofFunction` identifies the forward map with
the actual signed extension's coefficients, and
`sourceClassicalBoundaryEquiv_symm_apply` identifies the inverse with
physical restriction on the entire closed interval. No additional
normalization correction is needed for these assertions.

Public checks cover both boundary conditions, p=1, the original infinity
norm, negative and fractional Sobolev orders, negative frequencies, the
physical wave action, and both directions of the classical equivalence.

Validation: `./scripts/check.sh` passed: 6,756 build jobs, public examples,
and the axiom audit of all 29,809 NLS declarations. The build reports
21 existing warnings; both new modules and their standalone public
examples are warning-free. The source inventory check passed for 156
labels; this is not a completeness certificate.

## Lemma 4.3: original norms, rough limits, and arbitrary L² reflection

`SourceLemma4_3.lean` proves the two bounded analytic extensions for
1<p<infinity in the original period-one input norm and original period-two
boundary-space norm. The sufficient bound is `intervalExtensionBound`;
the exact amplitude factor 2^(1/p) cancels the input component comparison
factor 2^(1-1/p). The Hilbert case preserves the original norm exactly.
Finite physical Fourier integrals determine the continuous map uniquely.
Input truncations converge in norm, and their extensions converge both in
the boundary norm and as actual period-two distribution pairs.

`HalfIntervalL2Identification.lean` constructs the actual unit-interval
Fourier coefficients for arbitrary L² functions, identifies half-interval
integrals by bounded Hilbert functionals and Parseval, and proves that the
completed half-interval operator has exactly those integrals.
`SourceLemma4_3Physical.lean` identifies the original pair operator with
the actual signed-reflection coefficients for every original L² input.
Its physical synthesis equals the reflection a.e. on [0,2], without
continuity or boundary matching. The ordinary interval L² norm is retained.

`sourceLemma4_3_even_signed` and `sourceLemma4_3_odd_signed` prove the
corrected formulas in the source's signed coefficient convention.
The printed even formula is missing 1/2 and the odd kernel's factor 2i
must be i/pi. Constant-input counterexamples verify both discrepancies.
The theorem's boundedness and analyticity claims remain valid; the proof's
FL¹ input-norm notation does not replace the required FLᵖ estimate.

Public checks exercise both boundary signs, the all-finite-exponent
statement, a concrete exponent above two, exact Hilbert norms, rough
truncation/distribution limits, arbitrary L² integrals and reflection,
negative frequencies, signed finite formulas, and both counterexamples.

Validation: `./scripts/check.sh` passed: 6,759 build jobs, public examples,
and the axiom audit of all 29,884 NLS declarations. The build reports
21 existing warnings; the three new modules and standalone public
examples are warning-free. The source inventory check passed for 156
labels; this is not a completeness certificate.

## Lemma 4.4 audit: Lemma 4.4 and original restricted spectra

`SourceLemma4_4.lean` restricts the actual operator to each original
one-derivative boundary domain and proves its boundedness into the original
base space. Both restrictions use the same Dirichlet-reflected potential
from Lemma 4.3. The interval-input statement covers 1<p<infinity; the
restriction also works at p=1 for an already-reflected potential.

The free operator acts by pi times the mode index. The potential action
is the printed unconditionally convergent series in the original norm:
positive Dirichlet sign, negative Neumann sign, and output index k-n.
At p=2 the modes agree with those already identified with physical waves.
Removing the zero Sobolev weight is an isometry, and the base boundary
space is closed. The sufficient operator bound explicitly retains the
norm-comparison factor 2^(1/p).

`SourceBoundarySpectra.lean` defines the spectrum as the complement of
bijectivity of the actual restricted pencil, and proves that equivalent
base/domain norms preserve the full spectrum. The original periodic
spectrum is the union of the two restricted spectra. Both are closed,
discrete, and finite in bounded regions. For original interval input,
the canonical source labels exhaust exactly these restricted spectra.

Next: audit the original-norm Cauchy–Riesz restrictions and ranks in the
proof of Theorem 1.4. No new rank or algebraic-multiplicity formula is
claimed here. No correction to Lemma 4.4's signs or index shift is needed.
The separate all-exponent printed-height failure remains unresolved as
printed; the dissertation is not complete.

Validation: `./scripts/check.sh` passed: 6,761 build jobs, public examples,
and the axiom audit of all 29,941 NLS declarations. The build reports
21 existing warnings; both new modules and the standalone public examples
are warning-free. The source inventory check passed for 156 candidate
labels; this is not a completeness certificate.

## Theorem 1.4 proof audit: original boundary Riesz ranks and algebraic counts

`SourceBoundaryContours.lean` constructs the actual restrictions of the
original circle and four-edge rectangular Riesz integrals to each boundary
base space. On admissible contours these are finite-rank idempotents.
Their ranges are identified with the boundary part of the ambient range,
and continuous linear equivalences preserve their ranks under the change
from the original component-sum norm to the auxiliary maximum norm.

`SourceBoundaryRootSpaces.lean` proves the exact original-domain pencil
recursion for every finite Jordan chain. The full root space consists of
all finite chains, stabilizes, and is finite dimensional. Its dimension
defines the original restricted operator's algebraic multiplicity and
agrees with the existing coefficient multiplicity. This identifies whole
root spaces, not only eigenvectors or spectral sets.

`SourceBoundaryContourDomains.lean` shows that both projected ranges lie
in the original one-derivative boundary domain. Restricting the input to
that domain leaves the entire range unchanged. Thus the ranks also apply
to the displayed domain restrictions in the proof on page 32.

`SourceBoundaryCounting.lean` proves the rank/multiplicity formulas and
one common open convex connected original-input neighborhood containing
the given potential and zero. Both boundary signs and every larger cutoff
are covered. The projectors depend analytically on the original interval
input, central ranks and total algebraic counts are 2N+1, and high-disk
ranks and counts are one. Each high disk contains exactly one simple
boundary eigenvalue, and there is no spectrum outside the central box
and high disks. The central cutoff is positive.

This completes the original-norm Riesz counting argument of Theorem 1.4
with the established height-N boxes. It does not assert the separately
refuted all-exponent norm-dependent height printed in the theorem.
No replacement numerical height is silently adopted. The dissertation
remains incomplete. Next: Lemma 4.5, auditing the original restricted
operator trace formula for the analytic simple boundary eigenvalues.

Validation: `./scripts/check.sh` passed: 6,765 build jobs, public examples,
and the axiom audit of all 30,060 NLS declarations. The build reports
21 existing warnings; all four new modules and the standalone public
examples are warning-free. The source inventory check passed for 156
candidate labels; this is not a completeness certificate.

## Lemma 4.5 audit: Lemma 4.5 trace formula, including p=1

`SourceLemma4_5.lean` defines the intrinsic trace on the actual original
boundary contour range. Its bounded lift belongs to the original
one-derivative boundary domain and represents each spectral-range vector
itself. The intrinsic endomorphism acts by the original operator on that
lift. An isometry identifies this ambient boundary range with the typed
boundary-projector range from the preceding milestone. Continuous norm
conversion preserves the trace by conjugation of the finite restrictions.

The trace equals the enclosed eigenvalue whenever the original boundary
range has rank one. For 1<p<infinity, both trace-defined high-index branches
are analytic on one open convex connected original-input neighborhood
containing the input and zero. Their disks contain exactly those values,
with original algebraic multiplicity one. On admissible circles they agree
with the previously constructed period-one eigenvalue branches.

The PDF explicitly includes p=1 in Lemma 4.5. `SourceLemma4_5Endpoint.lean`
proves that endpoint using the classical Hilbert realization: an original
absolutely summable coefficient pair synthesizes a continuous period-one
physical potential, whose unit-interval L² coefficients are exactly the
bounded inclusion into p=2. Its completed reflection is the actual physical
Dirichlet reflection. The resulting spectrum equals the classical interval
eigenvalue set with the same boundary condition. Pulling back the Hilbert
trace branches proves analyticity in the original p=1 norm on a common
neighborhood, with exactly one classical eigenvalue in every high disk.
Multiplicity one is proved in this original Hilbert boundary realization.

The two theorems cover the printed finite-exponent range. No bounded
reflection into the period-two p=1 space, or trace on such a p=1 realization,
is asserted. No change to the analytic conclusion is needed; the endpoint
uses an explicit additional argument. Earlier source qualifications,
including the printed all-exponent height failure, remain unchanged.
Next: Section 5, the auxiliary physical boundary conditions (1.10), their
phase-twisted reflections, and Lemma 5.1. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6767 build jobs, the combined public examples, and the axiom audit of 30125 NLS declarations. The 21 existing warnings are unchanged; both new modules and their focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: Lemma 5.1 and physical auxiliary reflections

`SourceLemma5_1.lean` proves both parts of Lemma 5.1 using actual
periodic H¹ representatives. The auxiliary endpoint equations (1.10) are
f₋+i f₊=0 for D* and f₋−i f₊=0 for N*, at both endpoints. Their
extensions use the phase-twisted reflection (−i f₊, i f₋), with opposite
signs for the two problems. Both solve the physical differential equation
at the same Neumann-reflected potential on the full period.

The physical transfer does not add an L² hypothesis on the potential.
The constructed representatives reconstruct the entire reflected function
on [0,2] and retain the original values on [0,1], including the endpoints.
For L² potentials, the extension's weighted original-norm coefficients
solve the actual source operator equation. Both the potential coefficients
and the function coefficients are identified with their normalized physical
Fourier integrals. Nonzero original eigenfunctions remain nonzero and yield
spectral points of the original periodic source pencil.

The existing physical auxiliary H¹ domain and L² operator realize the
opening operator definition of Section 5; the new audit records the exact
entry points. The physical H¹-to-coefficient-domain identification is a
continuous equivalence, without asserting equality of those different norms.
No correction to (1.10), the reflected signs, or Lemma 5.1 is needed.
The following Fourier expansions (1.11)–(1.12), their normalizations and
auxiliary subspace decompositions are next. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6768 build jobs, the combined public examples, and the axiom audit of 30146 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: auxiliary Fourier expansions (1.11)–(1.12)

`SourceAuxiliaryBoundaryFourier.lean` proves the auxiliary Fourier
expansions in the original component-sum coefficient and physical L² norms.
The unnormalized modes are (ε exp(−iπnx), i exp(iπnx)), with ε=1 for D*
and ε=−1 for N*. The amplitude is exactly half the physical sesquilinear
pairing with that auxiliary mode. Both component coefficients equal the
normalized physical Fourier integrals of the actual reflected function.

For arbitrary original interval L² data, the series reconstructs the
auxiliary reflection almost everywhere on [0,2] and preserves the original
interval energy when the doubled period is normalized. Endpoint matching
is not assumed; uniform or H¹ convergence is not asserted for arbitrary
L² input. When the original data do satisfy the auxiliary H¹ endpoint
conditions, these coefficients agree exactly with the inclusion of the
Sobolev extension from Lemma 5.1.

The second line of printed (1.11) uses E_m^dir where E_m^d* is required.
A formal counterexample proves that its ordinary-mode series cannot sum
to the auxiliary reflection of the constant function (1,i). The corrected
auxiliary-mode series is proved. The component formula in the first line,
the factor 1/2, and equation (1.12) require no correction.

Next: the auxiliary Fourier subspaces, their complementary decomposition,
and the original-norm extension maps on page 34. The current Fourier-sum
result concerns L² data; the later finite-exponent and distributional
statements retain their separate scope. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6769 build jobs, the combined public examples, and the axiom audit of 30177 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: original auxiliary subspaces and mode decompositions

`SourceAuxiliarySpaces.lean` proves that the auxiliary D* and N* spaces
are closed topological complements at every real Sobolev order. Finite
exponents use the original component-sum norm; infinity uses the separate
signed coefficient space with the source's frequencywise-sum supremum norm.
Membership is the actual ±i reflection condition, with reversed first
frequency for raw coordinates and matching indices for signed coordinates.

The scalar amplitude maps are continuous linear equivalences onto these
spaces. Their explicit assemblies have norm factors 2^(1/p) for finite p
and 2 for the source infinity norm. The physical auxiliary H¹ domain is
continuously equivalent to the original one-derivative coefficient space;
the forward map is the actual reflected Fourier extension, and the inverse
is restriction at every point of the original closed interval.

`SourceAuxiliarySeries.lean` proves unique norm-convergent expansions for
finite exponents and actual periodic distributional expansions for all
Banach exponents, including infinity. The distributional sums are identified
with the actual original pair syntheses, and their modes act by the physical
exponential-wave integrals with the auxiliary phase. The infinity theorem
asserts a unique amplitude representation with its distributional sum; it
does not assert convergence in the infinity norm.

The page-34 decomposition repeats D* as both summands. A nonzero weighted
zero mode formally refutes self-complementarity, in both original norm
conventions. The corrected D* ⊕ N* decomposition is proved. The earlier
(1.11) correction remains separate. Next: the completed bounded auxiliary
extensions in the original spaces, their physical identification, and
operator invariance. Proposition 5.2's counting, reality and numerical-height
claims remain a separate audit. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6771 build jobs, the combined public examples, and the axiom audit of 30218 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: completed auxiliary extensions and actual spectra

`SourceAuxiliaryExtension.lean` constructs the completed page-34 auxiliary
reflection into the actual original zero-order weighted subspace for
1 < p < ∞. The auxiliary phase is an isometry of the original input norm,
so the ordinary interval-extension constant is a sufficient bound here too.
The map preserves the norm at p=2, agrees with the physical finite Fourier
integrals, is uniquely determined by those inputs, and is their norm limit.
Its actual paired periodic distribution has the same coefficients and phases.

`SourceAuxiliaryExtensionPhysical.lean` identifies this completion with
the physical auxiliary reflection for every original interval L² input.
Synthesis reconstructs the reflected function almost everywhere. On the
auxiliary H¹ domain it agrees with the actual Sobolev extension from Lemma 5.1.
No endpoint condition is needed for the L² identification.

`SourceAuxiliaryOperators.lean` proves invariance of the original auxiliary
domain under the actual operator. Both boundary signs use the same ordinary
Neumann-reflected potential. It constructs the restricted inclusion, operator,
and pencil z·inclusion − operator, and defines the resolvent set by actual
pencil bijectivity. Exact continuous conjugacy identifies that set and its
complement with the existing auxiliary realization. These restrictions also
cover p=1 when the potential already has the required reflection symmetry;
no bounded p=1 interval-extension map is asserted.

`SourceAuxiliarySpectra.lean` proves that the actual original spectrum is
closed, discrete, and finite in bounded regions. For physical L² potentials
it equals the classical auxiliary interval eigenvalue set, including when
the potential is supplied through the completed original interval map.
Proposition 5.2's uniform counts, original Riesz ranks, full Jordan
multiplicities, reality, and printed numerical height remain separate
assertions. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6775 build jobs, the combined public examples, and the axiom audit of 30286 NLS declarations. The 21 existing warnings are unchanged; all four new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: original auxiliary Jordan counts and reality

`SourceAuxiliaryRootSpaces.lean` identifies finite and full Jordan chains
of the actual original auxiliary pencil. The exact recursion uses the
original one-derivative domain and inclusion at every step. The full root
space is finite-dimensional and stabilizes at a finite level; its dimension
defines algebraic multiplicity and is positive exactly on the actual spectrum.
A continuous linear equivalence proves agreement with the existing auxiliary
coefficient realization, including every generalized eigenvector.

`SourceAuxiliaryCounting.lean` proves uniform counts in the original spaces.
One open convex connected neighborhood containing the original interval input
and zero supports both auxiliary signs and every sufficiently large cutoff.
Each high disk contains exactly one spectral value of algebraic multiplicity
one. The central cluster has total multiplicity 2N+1 for both signs, and these
regions exhaust the spectrum. The central box here has height N.

`SourceAuxiliaryReality.lean` proves Proposition 5.2(iv): the completed common
Neumann potential reflection preserves real type, and every eigenvalue of
either actual original auxiliary restriction is real for real-type input.
`SourceAuxiliaryPhysicalMultiplicity.lean` proves that at p=2 the original
full-chain multiplicities equal the independently defined physical auxiliary
Jordan multiplicities, also through the completed interval input map.

`SourceAuxiliaryHeightClusters.lean` identifies the central cluster of a
real-type potential at every nonnegative height, with its count and exhaustive
localization. In particular, a formal zero-input counterexample refutes the
proof's final 2N−1 auxiliary N count on page 35 in the literal printed box;
the count is 2N+1, as Proposition 5.2 itself states.

These results do not prove the printed norm-dependent height for general
complex input. The original restrictions of the actual Cauchy–Riesz contour
integrals, their domain lifts, ranks, and analytic dependence remain the next
proof audit. The bounded input completion and uniform source neighborhoods
require 1 < p < ∞; already-reflected root spaces and reality also include p=1.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6780 build jobs, the combined public examples, and the axiom audit of 30355 NLS declarations. The 21 existing warnings are unchanged; all five new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: actual auxiliary contour ranks and domain lifts

`AuxiliaryContourPhase.lean` proves exact conjugacy of the ambient resolvent
under the auxiliary phase, including its zero extension off the resolvent
set. It transports the actual normalized operator-valued circle and four-edge
rectangle integrals. For a Neumann-reflected potential, the auxiliary
complementary projections commute with both integrals.

`SourceAuxiliaryContours.lean` constructs the corresponding restrictions in
the original coefficient norm. On admissible contours their values are
exactly those of the actual ambient integrals. They are finite-rank
idempotents, and their ranges are isometric to the auxiliary parts of the
original ambient ranges. The completed common Neumann potential is a bounded
linear map of the original interval input, giving analytic circle families.

`SourceAuxiliaryContourDomains.lean` proves that each projected vector lifts
to the original one-derivative auxiliary domain. Restricting either integral's
input to that domain leaves its entire range unchanged.
`SourceAuxiliaryContourRanks.lean` identifies the actual ranks with sums of
full original auxiliary Jordan multiplicities, through the proved norm and
phase range equivalences.

`SourceAuxiliaryContourCounting.lean` combines admissible contours with the
original counts. One open convex connected neighborhood containing the
original input and zero supports both auxiliary signs, all sufficiently
large cutoffs, and analytic dependence of the actual restricted projections.
Central rank is 2N+1 and high-disk rank is one, including the displayed
restrictions to one-derivative inputs in the proof of Proposition 5.2.

The central rectangles here have height N. The source's printed norm-dependent
height for general complex input remains a separate audit; these contour
identities do not replace or repair it. Already-reflected potentials are
covered at every finite Banach exponent including p=1. The completed
interval-input neighborhood theorem requires 1 < p < ∞. The dissertation
remains incomplete.

Validation: `./scripts/check.sh` passed: 6785 build jobs, the combined public examples, and the axiom audit of 30451 NLS declarations. The 21 existing warnings are unchanged; all five new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.


## Section 5 audit: printed auxiliary height, valid Hilbert case and counterexample

`SourceAuxiliaryPotentialPhase.lean` upgrades the existing original-input
phase (iφ₋,−iφ₊) to an exact linear isometry at every finite Banach exponent.
Its inverse preserves finite Fourier input, with explicit component phases.
The actual completed auxiliary spectrum equals the ordinary boundary spectrum
at the rotated original input, retaining the precise source norm.

`SourceAuxiliaryPrintedHeight.lean` proves the unchanged printed height at
p=2 for both auxiliary conditions. One open convex connected neighborhood
containing the input and zero supports all larger cutoffs, central algebraic
count 2N+1 in the literal box of height (1+8‖ψ‖)², one simple eigenvalue in
each high disk, and exhaustive localization. Multiplicities remain the
dimensions of full original auxiliary Jordan root spaces. The earlier reality
and actual contour-rank results retain their separate proved scope.

`SourceAuxiliaryHeightCounterexample.lean` refutes the unrestricted printed
height assertion. For every natural exponent P≥1024, an explicit inverse-phase
rotation of the finite triangular input has original norm at most 3/32 and
an actual auxiliary D* eigenvalue i·2^P. That value lies outside the printed
height box and all quarter-pi high disks, for every cutoff N. The universal
exhaustion assertion is therefore formally false already at p=1024.

This is a height failure for complex input, distinct from the page-35
2N−1 count typo. No replacement numerical bound is adopted. The height-N counting theorem for 1<p<∞, original contour ranks, and
real-type prescribed-height results remain valid. The optimal validity range for the
printed formula is not claimed. Next: Section 6, starting with the original-
norm quantitative eigenvalue-displacement assertion of Proposition 6.1.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6788 build jobs, the combined public examples, and the axiom audit of 30472 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Proposition 6.1 audit: Proposition 6.1 in the original period-two norm

`SourcePeriodTwoDisplacement.lean` transports the actual periodic eigenvalue
pairs through the coefficient-preserving unit-weight isometry. Every Fourier
coefficient, the component-sum norm, and each symmetric tail cutoff remain
unchanged. Spectral membership is expressed as noninvertibility of the actual
original-domain pencil. The pairs retain their algebraic multiplicities.
One open convex neighborhood containing the input and zero supports the
corrected displacement power-sum estimate for every larger cutoff.

`SourcePeriodTwoAsymptotics.lean` proves the qualitative ℓᵖ conclusion for
finite p>1 with locally uniform small full signed power tails. The neighborhood
may depend on the tolerance. The selected entries are actual spectral pairs
at every sufficiently distant index; no spectral meaning is assigned to the
finitely many unspecified entries. Their values do not affect ℓᵖ membership.

`SourcePeriodTwoDisplacementCounterexample.lean` refutes the printed locally
uniform quantitative estimate already at p=2. Every open original-norm
neighborhood of zero and every proposed cutoff contain a potential with an
actual distant spectral value whose squared displacement exceeds the printed
budget. The final negation covers any labels that exhaust the high spectral
pairs and have the claimed summable bound. The underlying single-resonance
construction has quadratic displacement and a quartic printed budget.

The corrected bound includes an additive leading Fourier-tail term. Its
natural-number half-cutoff is floor(N/2), explicitly recorded in the audit.
The counterexample also defeats the smaller ceiling(N/2) printed budget;
rounding cannot account for the discrepancy. No sharp ceiling-cutoff version
of the corrected quantitative bound is claimed here.

Next: Corollary 6.2's four original boundary spectra, followed by the
midpoint/gap consequences and Proposition 6.3. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed: 6791 build jobs, the combined public examples, and the axiom audit of 30495 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Corollary 6.2 audit: Corollary 6.2 for arbitrary original period-two input

`PeriodTwoRestriction.lean` constructs bounded restriction from period-two
coefficients to unit-interval Fourier coefficients for every 1<p<∞. Even
frequencies are sampled directly; odd frequencies contribute through a
shifted Hilbert transform. The map is the identity on embedded period-one
input. `PeriodTwoRestrictionIntegrals.lean` proves exact physical integral
formulas for every finite input, including negative and odd frequencies.

`PeriodTwoRestrictionL2.lean` identifies the completed map with actual
restriction for arbitrary L² functions and proves almost-everywhere
reconstruction on the unit interval. `SourcePeriodTwoRestriction.lean`
lifts it to the original component-sum pair norm, proves its norm bound and
phase compatibility, and identifies restriction followed by completed
reflection with the literal physical reflection for arbitrary L² pairs.

`SourceCorollary6_2.lean` supplies all four complete canonical boundary
root sequences for arbitrary original period-two input. They exhaust the
actual ordinary and auxiliary restricted spectra, with repetitions equal
to full original Jordan multiplicities. Their displacement sequences belong
to ℓᵖ for every 1<p<∞. One open convex neighborhood containing the input
and zero bounds all four full displacement power sums, including central
indices. This proves the displayed period-two scope of Corollary 6.2 by
restriction; no correction of its input domain is needed.

Next: the midpoint/gap consequences and Proposition 6.3, preserving the
original norms and exact weighted assumptions. The dissertation remains
incomplete. Proposition 6.1's printed quantitative bound remains refuted;
the sharper ceiling-cutoff version of the corrected bound is unproved.

Validation: `./scripts/check.sh` passed: 6796 build jobs, the combined public examples, and the axiom audit of 30569 NLS declarations. The 21 existing warnings are unchanged; all five new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Section 6 audit: Midpoint/gap asymptotics and the Proposition 6.3 audit

`SourcePeriodTwoMidpointGap.lean` proves the midpoint and gap ℓᵖ
asymptotics for arbitrary original period-two input. The distant entries
are actual counted spectral pairs, retaining algebraic multiplicity.
Their contour-defined midpoint and squared gap have locally uniformly
small full signed power tails. The intrinsic full midpoint displacement is
in ℓᵖ; the full squared-gap p/2 powers are summable. Individual central
pairs are not newly labeled here, and no spectral meaning is assigned to
the finitely many unspecified entries of the selected root sequences.

`SourceWeightedGapAsymptotics.lean` proves the corrected Proposition 6.3
estimate on the exact original weighted component-sum norm. Forgetting
the weight preserves every raw Fourier coefficient and identifies spectral
membership with noninvertibility of the actual original source pencil.
One open convex neighborhood containing the input and zero controls all
larger cutoffs. The intrinsic squared gap, independent of root ordering,
is weighted at the source's resonant frequency 2n. The corrected budget
has an additive leading Fourier-tail term and becomes locally uniformly
small; the neighborhood may depend on the tolerance. All weighted gap
powers are summable, and every square-root choice of the intrinsic squared
gaps has the claimed weighted ℓᵖ regularity.

`SourceWeightedGapCounterexample.lean` refutes the printed locally uniform
quantitative gap estimate already for unit weight at p=2. In every open
neighborhood of zero and beyond every proposed uniform cutoff, an explicit
single-resonance input has actual roots nπ±t and squared gap 4t², while the
printed budget is at most 24C t⁴. The formal negation covers any choice of
actual counted root pairs. Both floor and ceiling half-cutoff conventions
fail. This does not refute the qualitative asymptotics or assert failure
for every individually chosen cutoff at a fixed input.

Next: the Section 6 Lyapunov–Schmidt decomposition, shifted source norms,
and Lemma 6.4. The corrected bounds use floor(N/2); sharper ceiling-cutoff
versions remain unproved. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6799 build jobs, the combined public examples, and the axiom audit of 30608 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Section 6 audit: The original P/Q splitting and Lemma 6.4

`SourceWeightedPencil.lean` includes the weighted derivative domain into the
original source domain without changing either raw Fourier component. Both
base and domain inclusions are injective and commute with domain inclusion.
The actual original spectral pencil is exactly the weighted free pencil minus
the weighted potential. The potential itself agrees with the difference
between the original operator at φ and at zero.

`SourcePQSplitting.lean` proves unique decomposition into the two resonant
amplitudes and a complementary remainder, for both base and derivative
weights. The original eigenvalue equation is equivalent to the actual P/Q
equations, including the form for a specified resonant part u and complementary
part v. These equivalences require no smallness or high-frequency assumption.
The complementary domain inverse solves the original free source equation
with right-hand side Q_n f, is unique on the complementary domain, and
annihilates both resonant modes even at λ=nπ.

`SourceLemma6_4.lean` identifies T_n with the actual potential part of the
original operator applied to that domain inverse. It proves the exact signed
shifted coefficient formula and the printed opposite-shift estimate for
every 1≤p<∞, uniformly in the weight, shift, strip index, and parameter in
the full closed strip. The printed Hilbert constant remains two. The endpoint
p=1 admits constant one in the same original pair norm. No extra assumption
w_0=1 is introduced; the public endpoint check includes a constant weight two.

Next: Lemma 6.5's squared-operator estimate and its locally uniform contraction
consequence, with the source tail, shift, and endpoint conventions audited.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6802 build jobs, the combined public examples, and the axiom audit of 30640 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Section 6 audit: Lemma 6.5 and compatible original-source inverses

`SourceLemma6_5.lean` identifies the conjugated square norm with the exact
operator norm induced by the source's n-shifted pair norm. The displayed
estimate holds for every 1≤p<∞, with tail |k|≥|n| including its boundary and
the factor 1/w_n. The constant depends only on p. No normalized-weight
assumption or restriction away from the free strip center is added.

The original unweighted operator `sourcePotentialInverse` is exactly
Φ A_λ⁻¹ Q_n on the original component-sum coefficient space. Unit weighting
preserves its squared operator norm exactly. One open convex neighborhood
containing the input and zero, and one positive cutoff, give both printed
half-contractions for every sufficiently large signed frequency and every
parameter in the entire closed strip.

`SourceComplementaryCorrection.lean` constructs the original-source inverse
of Id−T_n through (Id+T_n)(Id−T_n²)⁻¹. The even inverse is a convergent series
in the original operator norm. The correction has both inverse identities
and solves every right-hand-side equation uniquely. On weighted inputs it
agrees with the existing weighted correction. A locally uniform theorem
constructs both compatible bounded inverses on the same neighborhood and
all sufficiently distant closed strips. Only the square needs to be small.

Public checks cover the induced-norm characterization, exact operator
identity and norm transport, weighted inverse compatibility, tail-boundary
coefficients, and endpoint half-contraction and two-sided inversion. A
concrete p=1 check uses constant weight two, index −3, and λ=−3π.

Next: the source Q-equation solution and Lemma 6.6's two-dimensional
resonant determinant criterion, including actual domain reconstruction.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6804 build jobs, the combined public examples, and the axiom audit of 30668 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Section 6 audit: Original Q-solutions and Lemma 6.6

`SourceQEquation.lean` identifies the entire unit-weight derivative domain
with the original source derivative domain, preserving raw coefficients.
The complementary projection commutes with the source inclusions. The
weighted Q-equation is equivalent to the actual original projected equation.
For every original-domain input u, the constructed v belongs to the same
domain and Q_n, solves that equation, and is its unique complementary solution.
The displayed Φv=T̂_n T_n Φu identity uses the original-source potential,
complementary inverse, and correction. The two small-square hypotheses in
that identity agree by the preceding exact norm-transport theorem.

`SourceLemma6_6.lean` defines the actual two-mode resonant matrix and
reconstruction into the original derivative domain. Reconstruction is the
resonant lift plus the unique Q-solution and preserves both resonant amplitudes.
Its full original spectral-pencil residual is the synthesized matrix residual.
Consequently, precisely the matrix kernel reconstructs eigenvectors; nonzero
amplitudes give nonzero eigenvectors. Every original-domain eigenvector is
recovered from its own two resonant coefficients.

Lemma 6.6 now equates a zero determinant both with the actual original
periodic spectrum (noninvertibility of the source spectral pencil) and with
a nonzero vector in its full one-derivative domain. The locally uniform
formulation uses one positive cutoff and one open convex neighborhood
containing the input and zero. It covers all sufficiently large signed
frequencies, the entire closed strips, and every 1≤p<∞, including p=1.
No correction to the printed lemma is needed.

Public checks cover full-domain surjectivity, unique original Q-solutions,
the displayed potential formula, unchanged raw resonant amplitudes, full
residual and reconstruction identities, the spectrum and eigenvector criteria,
and the p=1 local uniform statement. At zero potential, the matrix criterion
recovers every free lattice center as a genuine eigenvalue, also at p=1.

Next: the resonant matrix coefficients and Lemma 6.7's diagonal and
real/imaginary-type symmetry identities. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6806 build jobs, the combined public examples, and the axiom audit of 30702 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Section 6 audit: Original resonant coefficients and Lemma 6.7

`SourceResonantCoefficients.lean` identifies every correction-matrix entry
with the actual original-source corrected potential evaluated on a resonant
domain vector. The library's physical order (minus, plus) is explicitly
reversed to the source's printed order (plus, minus). Thus the printed upper
and lower off-diagonals are b_n⁺ and b_n⁻ respectively. The determinant is
unchanged by this reversal and equals (λ−nπ−a_n)²−b_n⁺b_n⁻; its zero set is
the actual original periodic spectrum. Lemma 6.7(i), equality of the two
correction diagonals, holds for arbitrary complex potentials.

`SourceLemma6_7.lean` defines physical conjugation and component exchange
on the original potential, with Fourier-index reversal in both components.
The source condition φ*=εφ agrees with its weighted realization; sign one
also agrees with the existing original real-type predicate. For ε²=1, the
corrected Lemma 6.7(ii) proves a_n(conj λ)=conj(a_n(λ)) and
b_n⁺(conj λ)=ε conj(b_n⁻(λ)). The reality hypothesis applies to both
conclusions. Either sign gives a real diagonal on the real spectral axis.
One open convex neighborhood containing the input and zero and one positive
cutoff support both symmetry statements throughout all distant closed strips,
for every 1≤p<∞, including p=1.

`SourceLemma6_7Counterexample.lean` computes the actual original diagonal
for constant components (a,b) as ab/(2πn) at every nonzero free center where
the square is small. For the single fixed potential (1,i), this is nonreal.
Beyond every proposed cutoff there is a positive index where the source
half-contraction holds and diagonal reality fails. The formal negation of
the printed unconditional claim therefore rules out even an individual
potential-dependent cutoff, rather than only a locally uniform version.
The correction restores the reality assumption used in the source's proof;
it does not alter Lemma 6.7(i) or the signed off-diagonal statement.

Public checks cover actual operator entries, basis order, the scalar spectral
equation, arbitrary-complex diagonal equality, coefficient conjugation,
constant real- and imaginary-type inputs, both signs at p=1, the exact
constant-potential diagonal, and counterexamples beyond every cutoff.

Next: the parity expansions (1.14)–(1.15) and Lemma 6.8's analyticity and
coefficient-tail estimates. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6809 build jobs, the combined public examples, and the axiom audit of 30748 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Original-source audit: Original parity expansions and Lemma 6.8 analyticity

`SourceResonantParity.lean` transports every complementary-operator power
to the original source space. Its resonant input is the actual potential
applied to the original resonant derivative-domain vector. The even Neumann
vector has a convergent series in the original operator. Equations
(1.14)–(1.15) express the actual diagonal and off-diagonal remainders through
that vector. The leading terms are the second component at 2n and the first
component at −2n. The diagonal odd series and both strictly positive even
remainder series converge to the actual coefficients. The discarded parity
terms vanish without a contraction hypothesis.

`SourceResonantAnalytic.lean` defines total coefficient functions agreeing
with the original correction entries wherever the squared operator is small.
They are jointly analytic in the original potential and spectral parameter.
One open convex neighborhood containing the input and zero and one positive
cutoff give joint neighborhood analyticity on every distant closed strip,
with agreement with the actual source coefficients everywhere on those strips.
All results allow 1≤p<∞, including p=1. Analyticity is not asserted globally
for the total extensions outside the correction domain.

The same functions agree with the weighted analytic coefficients on the
common correction domain. A single weighted neighborhood and cutoff give
this agreement throughout every distant closed strip, rather than only at
free centers. Public checks connect the total functions to the actual scalar
spectral criterion, preserve both signed Fourier remainders under weight
inclusion, and exercise parity cancellation and endpoint convergence and
joint analyticity.

Next: transport Lemma 6.8's quantitative full-strip suprema and coefficient
tail estimates to these original functions, and audit its printed exponents
and norm factors. This milestone establishes the analytic assertion, not the
entire quantitative lemma. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6811 build jobs, the combined public examples, and the axiom audit of 30789 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Original-source audit: Lemma 6.8 quantitative original coefficient tails

`SourceResonantSup.lean` defines all three suprema using the actual original
coefficient functions on the entire closed, unbounded resonant strip. Weight
compatibility identifies their full images with those of the weighted
coefficients. Uniform majorants prove the images bounded, the suprema
nonnegative, and every pointwise coefficient norm bounded by its supremum.
These are genuine suprema, not replacement majorant sequences.

`SourceLemma6_8.lean` proves summability and explicit bounds for the full
signed p-power tails of the diagonal and both weighted off-diagonal
remainders. One open convex neighborhood containing the input and zero and
one cutoff N₀≥2 support both the bounded-image assertions and every tail
cutoff N≥N₀. The unweighted specialization provides a neighborhood directly
in the original period-two source space. Exact unit-weight identities retain
the original pair norm, component norms, and Fourier tail without constants.

The diagonal budget is C_p B^p(B^p/N^δ+T^p), where B is the original
unweighted pair norm, T its floor(N/2) tail norm, and δ=min(1,p−1).
The negative/positive remainder budgets are D_p B_±^p(W^(2p)/N^δ+T_w^(2p)),
with W the full weighted pair norm, B_± the corresponding component norm,
and T_w the weighted floor(N/2) tail norm. Both signs and both signed index
tails are included. Quantitative results require 1<p<∞; the preceding
analytic p=1 endpoint is not asserted for these bounds.

The printed page-41 off-diagonal display omits the left-hand p-powers and
uses the positive component in place of the full inner pair norm. This
milestone proves the form supported by the source's concluding proof,
with the explicit floor-half tail convention. It does not prove or formally
refute the literal display. The discrepancy and its remaining counterexample
audit are recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_6.md`.

Public checks exercise both component factors, exact original norms,
pointwise supremum domination, the original p=2 neighborhood, both signed
cutoff boundary indices, and floor(3/2)=1.

Next: formally audit the literal Lemma 6.8(ii) display, including its omitted
powers and positive-component norm factor. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6813 build jobs, the combined public examples, and the axiom audit of 30832 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Original-source audit: Lemma 6.8's omitted powers fail locally at zero

`CubicResonantPotential.lean` solves the correction equation explicitly for
a potential with first physical mode 2n of amplitude a and second mode zero
of amplitude b. The corrected vector has only three modes. The positive
coefficient at every nonzero free center is ab²/(2πn)². The coefficient
identity holds for arbitrary spectral weights and all finite 1≤p<∞.

`SourceCubicResonantPotential.lean` transports this calculation to the actual
original period-two potential and coefficient functions. At unit weight,
p=2, and a=b=t>0, its squared original norm is 2t² and its positive remainder
norm is t³/(2πn)². Its leading positive coefficient at 2n is zero.

`SourceLemma6_8Counterexample.lean` shows that every open neighborhood of
zero and every proposed common cutoff contain a witness exceeding the
printed positive-remainder budget. The correction is small and all distant
strip images are bounded, so the comparison uses actual coefficient values
and genuine full-strip suprema. Even enlarging the inner positive-component
norm to the full pair leaves a budget at most 16C t⁶, which cannot dominate
the cubic coefficient for sufficiently small t.

The complete unpowered signed-tail estimate is formally negated for every
tail-cutoff convention κ(N), including floor and ceiling half-cutoffs. Thus
changing only the inner norm cannot repair the absent left-hand powers.
The result concerns a locally uniform neighborhood and cutoff; it does not
claim that one fixed finite-support potential defeats every individual
potential-dependent cutoff. The valid p-power estimates remain unchanged.

Public checks cover the exact physical modes, the cubic identity at p=1,
the p=2 source norm, arbitrarily small witnesses, both half-cutoff roundings,
and failure even with the enlarged inner norm.

Next: independently audit the positive-component norm factor after restoring
the left-hand powers. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6816 build jobs, the combined public examples, and the axiom audit of 30884 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Original-source audit: Lemma 6.8's component factor fails independently

`ReverseCubicResonantPotential.lean` gives the complementary two-mode
calculation: first physical mode zero has amplitude a, and second mode −2n
has amplitude b. A three-mode vector solves the correction equation exactly.
The negative coefficient at a nonzero free center is a²b/(2πn)². These
coefficient identities hold for every finite 1≤p<∞ and every spectral weight.

`SourceReverseCubicPotential.lean` identifies the actual original source
remainder, component norms, distance from the fixed constant background
(1,0), and Fourier tails. At p=2 and a=1, b=t>0, the source distance from
that background is t. Every positive Fourier cutoff removes the constant
first component, leaving a squared tail norm at most t². The squared
negative remainder at the center is t²/(2πn)^4.

`SourceLemma6_8ComponentCounterexample.lean` restores the correct powers
on the left but retains the printed positive-component inner norm. This
budget is at most 2C t⁴, so it cannot control the quadratic squared remainder.
Every original open neighborhood of the same background and every common
cutoff contain a witness, with a small correction and bounded distant
strip images. The complete squared signed-tail estimate is formally
negated for every tail convention κ(N)≥1 when N≥2, including both floor
and ceiling half-cutoffs.

This is independent of the previously proved missing-power counterexample.
Restoring only the powers cannot repair the component factor; changing only
the inner norm cannot repair the missing powers. The valid p-power/full-pair
estimate remains available. Both refutations concern locally uniform
neighborhoods and cutoffs; neither asserts failure beyond every individual
cutoff for one fixed finite-support potential. No optimal norm replacement
or sharp constant is claimed.

Public checks verify the fixed background, physical mode signs, distinct
component amplitudes, the coefficient formula at p=1, arbitrarily close
original witnesses, and both half-cutoff versions of the correctly squared
sum negation.

Next: Lemma 6.9's determinant zeros and displacement estimates in the
original source realization. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6819 build jobs, the combined public examples, and the axiom audit of 30937 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 6.9 milestone in the original source space

`SourceResonantDeterminant.lean` forms the determinant from the actual original
analytic coefficients and identifies it with both basis orders of the source
matrix. Its zeros detect noninvertibility of the original period-two pencil.
The determinant is jointly analytic in potential and spectral parameter.
These pointwise assertions include p=1 on the correction domain.

The product supremum is the supremum of the actual product b⁺b⁻ over the
entire closed, unbounded strip. Its image is bounded and every pointwise
norm is bounded by this nonnegative supremum. One original open convex
neighborhood and cutoff give the numerical coefficient bounds, a small
correction, and the Cauchy derivative bound 1/8 on the refined disk.

`SourceLemma6_9.lean` gives two roots with repetition in each distant strip,
with no other scalar zeros or original spectral points there. Every scalar
analytic order equals the occurrence count in the two-element multiset;
the total count on the whole strip is exactly two. The coefficient-preserving
operator realization has the same algebraic multiplicities. Each root is
within 3π/32 of nπ, hence in the source's open π/4 disk, and the squared gap
is at most six times the full-strip product supremum.

For every finite p>1, `sourceLemma6_9` provides the joint analyticity, strip
control, counted pairs, and corrected displacement sums on one original
neighborhood and cutoff. Every larger signed-tail cutoff works. The budget
retains the additive leading Fourier tail and the explicit floor half-cutoff.
The labels are unique up to exchange, and arbitrary modewise choices give
identical displacement tails; no analytic individual labeling is asserted.

`SourceLemma6_9Counterexample.lean` formally refutes the printed Hilbert
pair-sum budget for any choices of these counted scalar roots, using the
previous actual-source spectral counterexample. This is a local uniform
failure near zero, not a claim about every individual cutoff at fixed input.

Public checks cover actual matrix/spectrum agreement at p=1, repeated roots
and free centers, both signs of the index, product and derivative bounds,
one neighborhood for all later cutoffs, label-independent sums, and the
printed sum negation.

Next: audit Chapter 2's Theorem 7.1 against the existing action-angle
construction, including its common neighborhood and Poisson-bracket scope.
Sharper ceiling-cutoff replacements remain unproved. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed: 6822 build jobs, the combined public examples, and the axiom audit of 30990 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Theorem 7.1 milestone: Theorem 7.1 on one original action-angle neighborhood

`SourceActionCommonNeighborhood.lean` proves that every scalar action is
complex and real analytic on one open neighborhood of the entire real
source locus. The argument evaluates the actual analytic rectangular
sequence map and its action-radius identity. It works for every finite
p>1, including 1<p<2, without an extra indexed action-domain condition.

`SourceRealThetaPhase.lean` fixes the real angle orientation by dividing
the signed eta coordinate by the canonical gap and including the beta
correction. Its unit phase defines an actual `Real.Angle`, a class modulo
2π. Canonical half-gap charts identify that class with their real theta
representative. Squaring the phase gives the existing complex analytic
phase modulo π.

`SourceThetaSpectralPhase.lean` proves that this oriented phase is the
exponential of the literal left-anchored spectral integral plus the beta
correction. The result includes periodic Dirichlet terminals. It retains
the actual/model integrability and admissible-path conditions; it does not
assert integrability for arbitrary paths.

`SourceTheorem7_1.lean` constructs `SourceTheorem7_1Data` for every finite
p>1. One original neighborhood supports all action extensions and every
open-gap angle's analytic phase and local representatives. The local
representatives are real on real input, stay in that same neighborhood,
and have the actual logarithmic angle differential. At a real base point,
the representative agrees with the real angle modulo 2π. The actions
retain their real nonnegative values and exact closed-gap zero criterion.

All three canonical relations use the actual regular source cotangents.
Their Fourier pairings converge absolutely throughout the full exponent
range. Only the angle gap must be open for the mixed bracket; both angle
gaps must be open for angle-angle commutation. Action-action commutation
also covers collapsed gaps. No canonical values or finite-source spectral
computations are assumptions of the constructed theorem.

Public checks exercise the common neighborhood at p=3/2, the doubled real
angle phase, local derivative agreement, precise bracket domains, literal
absolutely convergent Fourier formulas, and the opposite signs of the two
periodic endpoints when the corrections vanish.

Next: Section 8's Lemma 8.1, auditing the source discriminant products,
analytic extension, and uniform exterior asymptotics. The dissertation
remains incomplete.

Validation: `./scripts/check.sh` passed: 6826 build jobs, the combined public examples, and the axiom audit of 31030 NLS declarations. The 21 existing warnings are unchanged; all four new modules and both focused public probes compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.1 milestone: original discriminant products and exterior estimates

`SourceDiscriminantExtension.lean` identifies the source discriminant with
the physical L² monodromy trace. For p≥2 it extends along the original
Hilbert inclusion; for p≤2 it restricts the Hilbert function. Agreement on
finite Fourier sources determines it uniquely even among jointly continuous
functions on ℂ × `CoeffPair p`. The construction covers every finite p>1.

`SourceDiscriminantProductFormula.lean` supplies literal parity products
from actual counted roots, including the central roots in their correct
parity sectors. With prefactors -1 and 4 their locally uniform limits on
the whole spectral plane are Δ-2 and Δ+2. The full product uses the actual
canonical lexicographic endpoints and prefactor -4, with limit Δ²-4.
The printed -2 and 2 products also have literal limits: 2(Δ-2) and (Δ+2)/2.
They remain jointly analytic, but their shifted values are incompatible.

`SourceDiscriminantExterior.lean` gives one open convex neighborhood in the
original component-sum source norm, containing the base potential and zero,
and one positive spectral threshold for three estimates: the additive
trace error, additive derivative error, and derivative sine-quotient error.
The additive errors are normalized by exp(|Im λ|). All estimates hold on
the whole exterior of the open π/4 disks about πℤ. A companion cosine
quotient estimate retains an explicit positive relative denominator bound.

`SourceLemma8_1.lean` constructs the combined corrected theorem, including
joint analyticity, uniqueness, both Hilbert comparisons, the literal
products, and exact original spectral zeros and algebraic multiplicities.
The printed normalization and unrestricted cosine quotient are formally
refuted. The latter audit concerns the literal denominator-zero points;
it does not assert failure on every domain excluding those zeros.
The source PDF on printed p. 48 was visually checked. `SOURCE_ERRATA.md`
and `coverage/SECTION_8.md` record the precise corrections and scope.

Public checks cover p=3/2, physical Hilbert agreement, uniqueness from
Hilbert data, one neighborhood for simultaneous exterior estimates,
actual algebraic orders, all three finite-cutoff prefactors, and both
printed counterexamples. All four new modules and the focused public
probe compile without new warnings.

Next: Lemma 8.2, the continuity and strict interlacing of the actual
ordered periodic eigenvalues at real-type sources. The dissertation
remains incomplete.

Validation: `./scripts/check.sh` passed: 6830 build jobs, the combined public examples, and the axiom audit of 31061 NLS declarations. The 21 existing warnings are unchanged; all four new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.2 milestone: original endpoint continuity and real gaps

`SourcePeriodicEndpointContinuity.lean` recovers the actual left and right
endpoint displacement sequences from the midpoint displacement and half
the gap. Their existing sequence-norm continuity therefore gives continuity
of both endpoint sequences in ℓp at every real-type source. Perturbations
range over the whole complex source space. One open neighborhood controls
both endpoint errors simultaneously at every signed integer index.

`SourceLemma8_2.lean` constructs the original-source statement for every
finite p>1. Each actual canonical endpoint is continuous at real type,
real-valued there, and belongs to the original periodic spectrum. The
interlacing chain has a weak inequality within each gap and strict
inequalities between neighboring gaps. Distinct closed gaps are disjoint,
including central gaps and gaps of zero width.

The signed endpoint identity (2.5) uses integer powers and holds at both
endpoints for every positive and negative index. The following unnumbered
source assertions are also assembled: the signed discriminant inequality
on each closed gap, the full closed-gap union as the modulus-at-least-two
set, the open-gap interiors as the modulus-greater-than-two set, and the
endpoint set as the modulus-two set. Each superlevel point has a unique
gap index. At zero potential every gap is exactly its signed lattice
singleton; there are no false open gap interiors.

No simplicity or open-gap assumption is added. The result is continuity
at real-type base points under arbitrary complex perturbations, without
asserting global continuity of lexicographic labels at complex base points.
The precise scope is indexed in `coverage/SECTION_8.md`.

Public checks cover p=3/2, complex approximating sequences, a single
neighborhood for all indices, the negative-index level, uniqueness of the
gap index, and collapsed gaps at zero. Both new modules and the focused
public probe compile warning-free.

Next: Lemma 8.3, the locally uniform critical-root counts, exhaustion, and
reality of the discriminant derivative's roots. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed: 6832 build jobs, the combined public examples, and the axiom audit of 31092 NLS declarations. The 21 existing warnings are unchanged; both new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.3 milestone: original critical-root counts and reality

`SourceLemma8_3.lean` constructs the full critical-root counting statement
in the original source space for every finite p>1. At every complex base
point, one open convex neighborhood contains that point and zero, and one
positive cutoff works for all nearby potentials and every larger cutoff.

Each distant quarter-pi disk contains exactly one root of the actual
spectral derivative of the discriminant. That root is the canonical
critical coordinate, is simple, and is unique even in the closed disk.
The boundary is zero-free. The central disk of radius (K+1/2)π has exactly
2K+1 roots counted with multiplicity, and its boundary is also zero-free.
These regions exhaust all derivative zeros. At real-type potentials all
critical roots, including the central ones, are real.

The central labels are identified with the actual analytic-zero multiset.
Its cardinality, membership in the open disk, and each point's analytic
multiplicity are exposed explicitly; central simplicity is not assumed.
A uniform bound on the imaginary parts also proves that the central disk
and the earlier height-K box select exactly the same critical roots and
have the same count. The geometry and proof dependencies are recorded in
`coverage/SECTION_8.md`.

Public checks cover arbitrary complex sources at p=3/2, one original
norm ball for all larger cutoffs, negative distant indices, exact central
multiplicities, the central-box count, exhaustion, off-real nonvanishing
at real type, and the free central multiset. The new module and focused
public probe compile warning-free.

Next: Lemma 8.4, the locally uniform sampled ℓp asymptotics of the
discriminant and its spectral derivative. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed: 6833 build jobs, the combined public examples, and the axiom audit of 31113 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.4 milestone: actual sampled ℓp errors in the original space

`SourceLemma8_4.lean` constructs the actual sampled discriminant and
spectral-derivative errors as ℓp sequences in the original source space,
for every finite p>1. The two literal identities retain the free terms
2 cos λ and -2 sin λ at every signed integer index.

At every complex base point, one open convex source neighborhood contains
the base point and zero. One K≥0 bounds the value-error norm for every
nearby potential and every admissible sampling sequence; the derivative
error has the bound 4K/π. The result holds on the closed quarter-pi disks,
so includes the open disks stated in the source, central indices, negative
indices, and boundary samples. The choices of sample points may depend
arbitrarily on the potential.

For each nearby potential, an ℓp majorant is chosen before any samples
are chosen. It bounds the value error over every whole disk, and the
same majorant with factor 4/π bounds the derivative error. These are
locally uniform sequence-norm estimates, not only pointwise membership
for a fixed sampler. Both actual error sequences vanish identically at
zero potential. The precise quantifiers and Cauchy estimate are audited
in `coverage/SECTION_8.md`.

Public checks cover arbitrary complex bases at p=3/2, potential-dependent
samplers, a shared bound for different sources and samplers, the printed
open-disk ℓp membership, nonreal closed-disk boundary samples at all
signed indices, and both free error sequences. The new module and the
focused public probe compile warning-free.

Next: Lemma 8.5, the canonical critical-root asymptotics, derivative
product, real-type continuity, and the following interlacing and strict
extremum assertions. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6834 build jobs, the combined public examples, and the axiom audit of 31138 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.5 milestone: actual critical roots, product, continuity, and extrema

`SourceLemma8_5.lean` assembles the actual canonical critical-root
sequence in the original source space for every finite p>1. It is
lexicographically ordered, enumerates exactly all zeros of the actual
discriminant derivative, and retains every analytic multiplicity. Its
root displacement is the existing actual ℓp coefficient sequence.

One open convex neighborhood of each complex source contains that source
and zero, and gives a common bound on the complete displacement norm.
The literal symmetric products in equation (2.6), with prefactor two and
denominator one at index zero, converge locally uniformly on the entire
spectral plane to the derivative. This convergence is asserted for each
fixed source; the displacement norm bound is locally uniform in sources.

At real-type base points, individual critical coordinates are continuous
under arbitrary complex perturbations; the package also supplies their
analyticity and continuity of the full displacement sequence in ℓp.
Consequently one source neighborhood controls every critical-coordinate
error simultaneously. Each critical coordinate lies in its indexed real
gap. Every gap contains exactly one critical point and one strict real
local extremum, including collapsed gaps; all real local extrema are
canonical critical coordinates. The precise scope is recorded in
`coverage/SECTION_8.md`.

Public checks cover p=3/2, the exceptional zero-mode product factor, the
free product limit -2 at π/2, full sequence-norm convergence under complex
perturbations, one neighborhood for all signed coordinates, exact repeated
root multiplicities, exhaustion, and a collapsed negative-index gap.
The new module and focused public probe compile warning-free.

Next: Lemma 8.6, the locally uniform squared-gap improvement of the
critical-point midpoint offset at arbitrary complex sources. The
dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6835 build jobs, the combined public examples, and the axiom audit of 31170 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 8.6 milestone: original squared-gap offsets and corrected factorization

`SourceLemma8_6.lean` proves the squared-gap midpoint-offset estimate
in the original source space for every finite p>1. At each arbitrary
complex source, one open convex neighborhood contains that source and
zero, and one positive cutoff and one norm bound work throughout it.

The coefficient is the actual deleted-product derivative divided by
four times the offset coefficient on the tail, extended by zero at
central indices. It belongs to ℓp and has a uniformly bounded full norm.
The denominator has a uniform positive lower bound on that tail. The
actual critical-point midpoint offset equals the squared gap times this
coefficient. Complex collapsed gaps are included; the proof does not
divide by a gap. A pointwise quadratic norm bound and the vanishing of
the entire coefficient sequence at zero potential are also exposed.

The literal deleted products converge locally uniformly on the whole
spectral plane for each fixed source, including at removed and repeated
roots. Their normalization forces the midpoint factorization's prefactor
to be -4. A formal free-potential counterexample refutes the printed +4
at λ=π/2. The correction affects the displayed proof identity, while
Lemma 8.6's conclusion remains valid. See `SOURCE_ERRATA.md` and the
precise quantifiers in `coverage/SECTION_8.md`.

Public checks cover arbitrary complex bases at p=3/2, negative tail
indices, complex collapsed gaps, an explicit quadratic bound, the free
coefficient sequence, the zero-index product normalization, the value
at removed free double roots, and the printed-sign counterexample.
The new module and focused public probe compile warning-free.

Next: Lemma 9.1, the Dirichlet and Neumann characteristic products,
continuity at real type, and interlacing. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed: 6836 build jobs, the combined public examples, and the axiom audit of 31195 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 9.1 milestone: actual characteristic products, continuity, and interlacing

`SourceLemma9_1.lean` proves all three ordinary assertions for every
finite p>1. Both characteristics are jointly analytic in the spectral
parameter and original source. Their literal symmetric products use the
actual canonical roots, prefactor -1, and denominator one at index zero.
They converge locally uniformly on all of the spectral plane, with exact
boundary spectra and analytic orders equal to algebraic multiplicities.

At real-type sources, coordinates and full ℓp displacement sequences are
continuous under arbitrary complex perturbations. Both boundary roots
satisfy the literal interlacing chain, with strict separation from adjacent
periodic gaps. Collapsed gaps are included. The ordinary characteristics
agree exactly with the physical Hilbert formulas in both exponent-inclusion
directions, and finite Fourier agreement determines their continuous
extension uniquely.

`SourceLemma9_1Auxiliary.lean` proves the corresponding auxiliary statements
for the actual endpoint domains. One original open neighborhood controls
all indices of all four ordinary and auxiliary sequences simultaneously.
Phase conjugation preserves the original periodic gap indices.

`SourceAuxiliaryCharacteristicNormalization.lean` identifies the actual
auxiliary products with their classical and physical Hilbert monodromy
formulas. The printed D* and N* monodromy expressions on p. 53 exchange
the labels fixed by the endpoint domains on p. 33. The smooth constant
potential (1,0) distinguishes the two, both physically and in the actual
source products at every finite exponent. The auxiliary existence,
continuity, and interlacing assertions remain valid. The correction is
recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_9.md`.

Public checks cover p=3/2, literal free product normalization, full sequence
convergence under complex perturbations, one neighborhood for all four
sequences, negative indices and collapsed gaps, exact complex multiplicities,
physical Hilbert agreement, uniqueness, and the auxiliary label mismatch.
All three new modules and the focused public probe compile warning-free.

Next: Lemma 9.2, the analytic anti-discriminant extension, its identity
at Dirichlet roots, and locally uniform sampled ℓp estimates. The
dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6839 build jobs, the combined public examples, and the axiom audit of 31268 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 9.2 milestone: normalized anti-discriminant and full sampled ℓp bounds

`SourceLemma9_2.lean` proves the anti-discriminant assertions for every
finite p>1 in the original source space. The anti-discriminant is jointly
analytic in the spectral parameter and source; it agrees exactly with
the physical Hilbert monodromy off-diagonal sum in both exponent-inclusion
directions. Finite Fourier agreement determines the jointly continuous
extension uniquely.

The shifted-discriminant-square identity holds at every actual Dirichlet
zero, including multiple zeros. This strengthens the printed simple-root
statement: the global characteristic identity passes to all sources by
density before any root is selected.

Both actual Dirichlet sample sequences—the anti-discriminant values and
the spectral-derivative values—are constructed as elements of ℓp. One
original open neighborhood of each arbitrary complex base and one K≥0
bound both complete sequence norms. Central indices are included by a
uniform compact spectral-ball estimate; the assertion is not only a
distant-tail estimate. Both sequences vanish identically at zero potential.

On that same neighborhood, one ℓp majorant per source, chosen before any
spectral samples, bounds the value throughout every closed half-pi disk
and the derivative throughout every closed quarter-pi disk, with factor
4/π for the derivative. The exact quantifiers and the central-index
argument are recorded in `coverage/SECTION_9.md`.

Public checks cover arbitrary complex bases at p=3/2, arbitrary Dirichlet
zeros without simplicity, central and negative sample indices, both free
sequences, potential-dependent disk samplers, nonreal boundary samples,
physical normalization, both Hilbert inclusion directions, and extension
uniqueness. The new module and focused public probe compile warning-free.
The auxiliary label correction from Lemma 9.1 is retained; no additional
correction to Lemma 9.2 is needed.

Next: Lemma 10.1, common isolating neighborhoods and their global connected
domain near real-type sources, including an audit of its printed domain.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6840 build jobs, the combined public examples, and the axiom audit of 31294 NLS declarations. The 21 existing warnings are unchanged; the new module and focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 10.1 milestone: quantitative isolation and the corrected real-type domain

`SourceLemma10_1.lean` proves the common isolating-neighborhood theorem
on an open connected neighborhood of the entire real-type locus, for
every finite p>1 in the original source norm. Every point of that domain,
including complex points, has one open connected neighborhood carrying
one fixed family of positive-radius disks centered on the real line.
The full straight periodic gap and all actual Dirichlet, Neumann, and
critical coordinates lie in their assigned disk for every nearby source.
The disks equal the free quarter-pi disks outside one finite block.

The literal distance estimate (2.7) is included: one c≥1 bounds the
infimum distance between any two distinct disks above and below by
c and c⁻¹ times the absolute index difference. `SpectralSetDistance.lean`
identifies that distance as the greatest lower bound of all point-pair
distances. `SourceIsolatingDiscDistance.lean` proves the stronger pointwise
bounds, including central and mixed pairs. Halving the central margins
creates positive separation even if the original disjoint disks touch.
A uniform lattice-offset bound converts this margin to index-scale bounds.

The printed all-complex domain is false. In
`SourceIsolatingDomainCounterexample.lean`, the smooth constant source
(iπ,iπ) has four independent generalized eigenvectors at spectral value
zero: both raw Fourier blocks at +1 and -1 are square-zero. Its actual
algebraic multiplicity is therefore at least four. Any disjoint family
containing every indexed periodic pair would force multiplicity at most
two. Thus this source has no isolating family, even allowing arbitrary
set shapes. `not_sourceLemma10_1_all_complex` formally refutes the printed
domain at every finite p>1. Replacing FL_c^p by FL_r^p agrees with the
preceding paragraph, proof, and union construction on printed p. 54.
The correction and complete quantifiers are recorded in `SOURCE_ERRATA.md`
and `coverage/SECTION_10.md`.

Public checks cover p=3/2, the common global and local neighborhoods,
zero potential and collapsed gaps, all actual cluster coordinates,
central and negative-index set distances, real centers and the exact free
tail, tangent-disk shrinking, the greatest-lower-bound characterization,
and the four-dimensional obstruction to the printed domain. All four
new modules and the focused public probe compile warning-free.

Next: Lemma 10.2, analytic periodic power sums, midpoint and squared-gap
coordinates, and their locally uniform original sequence bounds on a
common almost-real domain. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6844 build jobs, the combined public examples, and the axiom audit of 31359 NLS declarations. The 21 existing warnings are unchanged; all four new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 10.2 milestone: analytic symmetric coordinates and full sequence bounds

`SourceLemma10_2.lean` proves all three clauses on one open connected
complex neighborhood of the entire real-type locus, for every finite
p>1 in the original source topology. The actual periodic power sums
for every natural power, midpoint, squared gap, and pair factor are
complex analytic; the pair factor is jointly analytic with the spectral
parameter. Its exact polynomial identity uses the actual endpoints and
holds at every complex source, including collapsed gaps.

`SourceSimpleSpectralDomain.lean` puts all ordinary Dirichlet and Neumann
coordinates and all critical coordinates on that same domain. Every
boundary root has actual operator algebraic multiplicity one; every
critical root has analytic order one as a zero of the discriminant's
derivative. Finite central neighborhoods and one common tail neighborhood
cover all indices. Taking the connected component containing the real
locus preserves connectedness after imposing the earlier isolation
constraints. Every point retains a connected local isolating neighborhood
inside the new domain, with the quantitative disk-distance bounds.

`SourceLemma10_2Sequences.lean` constructs the complete squared-gap
sequence in the literal space ℓ^(p/2), including p/2<1. Its quasi-norm
is exactly the square of the gap's ℓp norm, and the same identity holds
after removing any finite set of indices. For each base point and
positive tolerance, one original open neighborhood, cutoff and constant
control both complete midpoint and squared-gap sequences and all larger
truncation tails. The neighborhood may depend on the tolerance. Central
indices are included, and both complete sequences vanish at zero.

Public checks cover p=3/2 with literal target exponent 3/4, arbitrary
powers and signed indices, nonreal spectral parameters, actual operator
multiplicity and derivative zero order, common isolation and sequence
bounds, asymmetric truncations, exact factorization and free collapsed
gaps. The three new modules and focused public probe compile warning-free.
The corrected domain from Lemma 10.1 is retained; no additional correction
to Lemma 10.2 is needed. See `coverage/SECTION_10.md` for exact quantifiers.
The separate remark about discontinuity of ordered periodic labels is
not claimed as a new formal counterexample in this milestone.

Next: Lemma 10.3, the standard root's analytic domains, uniform bounds
between distinct isolating disks, and its normalized contour integrals.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 6847 build jobs, the combined public examples, and the axiom audit of 31400 NLS declarations. The 21 existing warnings are unchanged; all three new modules and the focused public probe compiled warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed.

## Lemma 10.3 milestone: standard roots and general contour normalization

`SourceLemma10_3.lean` proves the standard-root assertions for every
finite p>1 on exactly the same domain as Lemma 10.2. Spectral analyticity
holds off the actual closed gap at every complex source; joint analyticity
holds on the moving-gap complement over the common domain, and in
particular outside each fixed local isolating disk. One local neighborhood,
one disk family and the same c≥1 as the disk-distance estimate control
all distinct-index root norms, including central indices.

`PiecewiseC1Loop.lean` represents finite closed chains of actual C¹ paths.
Their derivatives need not match at corners, and the pieces need not be
individually closed. The contour integral is the sum of their actual path
integrals. Its winding integral is the conventional normalized integral
of the reciprocal pole; no desired root integral enters that definition.

`SourceStandardRootLogPrimitive.lean` constructs a single-valued
logarithmic correction whose derivative equals the inverse standard root
plus the midpoint pole. `SourceStandardRootPiecewiseContour.lean` telescopes
its primitive values across all pieces. The inverse-root integral is thus
the negative midpoint winding integral for every gap-avoiding piecewise
C¹ contour. Winding one gives the diagonal value -1; a primitive on a
distinct isolating disk gives zero off the diagonal. No circle-shape or
supplied homotopy hypothesis is required. Repeated traversals, reversed
orientation and collapsed gaps are included in the general winding formula.

The normalized root retains the literal principal-branch formula (2.9)
and extends as an entire linear function when the gap collapses. Existing
arbitrary-approach upper and lower gap-side limit theorems give the signs
in (2.12), including the midpoint and endpoints of complex gaps.

Public checks cover p=3/2, the unchanged common domain, literal branch
normalization, central/negative-index bounds, joint analyticity outside
open disks, both contour indices, clockwise winding, an actual two-turn
circle with period -2, a two-edge polygon with a corner, collapsed roots,
and complex one-sided limits. All four new modules and the focused public
probe compile warning-free. No new source correction is needed for
Lemma 10.3. Exact contour and domain conventions are recorded in
`coverage/SECTION_10.md`.

Next: Lemma 10.4, the gap-side endpoint integral estimate and its printed
index convention. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,851 build jobs, the full public example suite, and the axiom audit of 31,480 NLS declarations). The build retains 21 existing warnings; the four new modules and focused public probe are warning-free. The source inventory check verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.


## Lemma 10.4 milestone: actual side traces and a sharp endpoint bound

`SourceLemma10_4.lean` proves the gap-side endpoint integral estimate for
all original complex sources at every finite p>1, whenever the selected
actual gap is noncollapsed. The denominator is the side trace of w_n on
G_n, correcting the printed unbound m. One attained maximum of |f| on the
actual canonical segment controls every stopping point on both closed
sides. The theorem includes the literal real supremum over these values;
`sourceLemma10_4_sup` also writes the data maximum as its real supremum.

`SourceStandardRootGapSideEndpoint.lean` identifies the affine gap with
the actual canonical segment and its two endpoints. The trace is the
arbitrary-approach limit of the actual standard root on each side and is
continuous in the closed gap coordinate. The side integral is defined
from that trace and the actual affine Jacobian. Its integrand is genuinely
integrable at the branch points. Exact weighted substitution and both
one-endpoint and two-endpoint truncation limits connect the integral to
the improper interpretation in the source. Only continuity on the actual
gap is required; arbitrary complex gap directions are allowed.

Constant data give the exact normalized full-side values +ic and -ic.
Their supremum equals |c|, proving the factor one is sharp. The public
checks include actual noncollapsed real sources at p=3/2 and index -1,
endpoint integrability, midpoint stopping, both signs, both truncation
limits, a nonconstant test function, and the literal maximum/supremum.

`SourceLemma10_4IndexCorrection.lean` verifies the printed proof's index
mismatch. On a real gap G_n, the actual wrong-index kernel
(γ_n/2)/w_m(τ_n) is real for m≠n, hence cannot equal either claimed value
±i. Actual noncollapsed real gaps witness this failure at every finite
p>1 and every selected index. This refutes the printed substitution with
m≠n; it is not presented as a counterexample to every wrong-index
integral inequality. The corrected theorem uses n consistently.

All three new modules and the focused public checks compile warning-free.
The index correction and exact integral conventions are recorded in
`SOURCE_ERRATA.md` and `coverage/SECTION_10.md`.

Next: Lemma 10.5, convergence, analytic domains and nonvanishing of the
omitted standard-root product. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,854 build jobs, the full public example suite, and the axiom audit of 31,511 NLS declarations). The build retains 21 existing warnings; the three new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.


## Lemma 10.5 milestone: the actual omitted product and its analytic domains

`SourceLemma10_5.lean` proves convergence, analyticity and nonvanishing of
the literal omitted standard-root product for every finite p>1 and every
integer omitted index. `SourceLemma10_3Data.omittedProducts` keeps exactly
the supplied common domain. Each local package retains the original V,
disks D and distance constant c, including all Lemma 10.3 properties.
No new source-domain shrink is required.

The actual cutoffs are (1/π_n) times the product of w_m/π_m over
[-N,N] with n erased, with π_0=1. Their limits are the existing paired
products, not newly stipulated functions. `SourceStandardRootOmittedCommonDomain.lean`
proves joint analyticity and local uniform convergence on the full moving
complement of all unomitted gaps. It includes uniform convergence on
spectral and joint compact subsets, the printed complement of the CLOSED
isolating disks, and the stronger complement of the open disks. The
whole omitted disk, including its gap endpoints and any collapsed gap,
is an analytic, nonzero domain for the omitted product.

Absolute convergence is for the paired positive/negative blocks used in
the source proof. Their absolute tails vanish uniformly on a bounded
spectral region and a neighborhood of each original source, for arbitrary
finite subsets of the tail. Omitting an index changes only one pair.
`SourceStandardRootOmittedFreeNormalization.lean` proves that individual
free factor errors instead have a divergent harmonic tail at every
nonzero spectral point; this also occurs at i, which belongs to the
actual free omitted domain. Thus the pairing convention is substantive.

The free omitted product equals the filled sine quotient on all of ℂ.
At its omitted point it has value cos(nπ), of norm one, and it vanishes
at every unomitted free point. The public checks cover these signs and
zeros, the exact prefactor and early cutoffs for a negative index,
p=3/2, unchanged-domain transfer, both compact convergence statements,
closed-disk analyticity, omitted-gap nonvanishing, uniform absolute tails,
and paired versus individual convergence. All three new modules and the
focused public checks compile warning-free.

The proof's isolated a_k a_{-m} index typo is recorded in `SOURCE_ERRATA.md`;
the following regrouping uses a_k a_{-k}. The lemma's statement requires
no new correction. Exact domains and ordering are audited in
`coverage/SECTION_10.md`.

Next: Corollary 10.6, joint analyticity of the quotient product with
variable displaced roots. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,857 build jobs, the full public example suite, and the axiom audit of 31,565 NLS declarations). The build retains 21 existing warnings; the three new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.


## Corollary 10.6 milestone: the unconditional quotient and its joint analytic domains

`SourceCorollary10_6.lean` proves joint analyticity of the literal quotient
product for every finite p>1, every omitted integer index and every ℓᵖ
root-displacement sequence. `SourceLemma10_5Data.quotients` preserves the
supplied common domain W exactly. The local packages retain the original
V, isolating disks D and distance constant c from Lemma 10.5.

The source's displayed domain is the complement of the CLOSED unomitted
disks, times the full displacement space, times V. Both the analytic
quotient and the literal unordered product are analytic on that domain.
They are also jointly analytic on the open moving-gap domain and on the
whole selected disk. No distinctness, ordering, smallness or nonvanishing
condition is imposed on numerator roots.

`SourceSingleRootQuotientAbsolute.lean` proves absolute summability of
INDIVIDUAL quotient-factor deviations. The nonsummable free spectral
terms cancel between numerator and denominator; the remaining displacement,
midpoint and square-root corrections form an ℓ¹ sequence. The normalized
denominator factors tend to one, so division preserves the tail bound.
Thus this product converges unconditionally, without the pairing required
for the separate numerator and standard-root products. Its `HasProd` value
is exactly the previously constructed analytic quotient. The net of all
finite products with n erased converges to that same value.

`SourceSingleRootQuotientCommonDomain.lean` also proves local uniform
convergence of the literal symmetric cutoffs in all three variables,
uniform convergence on compact subsets of the triple domain, and
spectral analyticity for each fixed source and displacement sequence.
The normalization factors cancel at every finite cutoff, including
cutoffs which do not yet contain the omitted index.

`SourceSingleRootQuotientNormalization.lean` identifies the displacement
parameters with exactly the root sequences σ−σ⁰∈ℓᵖ. The free quotient is
one on its actual domain, including its selected collapsed gap. The
omitted displacement coordinate is irrelevant. An explicit finitely
supported example has the roots at −1 and 0 collide at i; the quotient
with −1 omitted is defined there and equals zero. This checks that
nonvanishing of the denominator has not become an incorrect nonvanishing
assertion for the quotient. Public checks also instantiate the complete
package and the collision example at p=3/2.

The printed Corollary 10.6 on p. 57 requires no new correction. Its exact
product, domain and quantifiers are audited in `coverage/SECTION_10.md`.

Next: equation (2.13) and Lemma 10.7, the canonical-root product and its
analytic domains. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,861 build jobs, the full public example suite, and the axiom audit of 31,626 NLS declarations). The build retains 21 existing warnings; the four new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.


## Lemma 10.7 milestone: the canonical root and its closed-gap boundary values

`SourceLemma10_7.lean` proves the canonical-root assertions of equation
(2.13), Lemma 10.7 and equation (2.14) for every finite p>1. The package
retains all Corollary 10.6 data on exactly the supplied common domain W.
Its local neighborhoods preserve the original V, isolating disks D and
distance constant c.

`SourceCanonicalRootCommonDomain.lean` proves joint analyticity on the
open complement of all moving periodic gaps, and on the printed complement
of the CLOSED isolating disks times V. The literal full symmetric cutoffs
converge locally uniformly in the spectral parameter and source, uniformly
on joint compact subsets and on spectral compact subsets at each source.
Equation (2.13) retains the exact 2i factor and π_0=1 normalization. The
canonical root factors through every omitted index, squares to the actual
source discriminant squared minus four off the gaps, and is nonzero there.

`SourceCanonicalRootBoundaryDomain.lean` puts the complete closed selected
gap in the omitted product's domain without shrinking W. The actual limits
from either open side exist, including at both endpoints. Their values
are continuous on the closed gap parameter interval, square to the
actual discriminant radicand, and are exact negatives. Both endpoint
values are zero; both interior values are nonzero for a noncollapsed gap.
These statements hold for complex sources in W, not only real sources.

`canonicalCollapsedDisk` proves analytic continuation on the original
selected disk when the gap collapses. `SourceCanonicalRootNormalization.lean`
shows that its center is a simple zero, with derivative -2i f_n(τ_n),
which is nonzero. This extension fixes the source; it does not assert a joint
extension through a gap that may reopen under source variation. At zero
source the root is the entire function -2i sin(λ), with value -2i at π/2
and derivative +2i at the negative free center -π.

The four real-source arrows in Figure 2.4 are also checked. The upper and
lower real-gap values have signs (+1)(-1)^n and (-1)(-1)^n; the adjacent
bands have imaginary signs (+i)(-1)^n on the left and (-i)(-1)^n on the
right. Negative integer indices are included. An actual open negative-index
gap witnesses the opposite real signs; no empty-hypothesis shortcut is
used for the sign and nonvanishing checks.

Public examples cover the full package at p=3/2, the unchanged domain,
literal finite prefactor and negative-index restoration, both compact
convergence statements, printed closed-disk domain, fixed-source collapsed
extension, simple-zero derivative, actual gap traces and endpoint limits,
discriminant-square identities and the figure's negative-index signs.
No new source correction is required. The exact domains and boundary
conventions are audited in `coverage/SECTION_10.md`.

Next: Lemma 10.8, the quotient-product asymptotic estimate with its sequence
exponents and local uniformity. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,865 build jobs, the full public example suite, and the axiom audit of 31,689 NLS declarations). The build retains 21 existing warnings; the four new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.


## Lemma 10.8 progress: estimates on every original disk

`SourceLemma10_8Estimates.lean` extends the quotient-product estimates to
every source in the unchanged Lemma 10.7 domain W and every original
isolating disk. The family V, D, c is chosen before the numerator roots
and target exponent. This is a substantial part of Lemma 10.8; the printed
local-uniformity wording for q<p remains under audit.

`SourceQuotientClosedDiscs.lean` proves that the original closed selected
disk avoids every other gap and is compact. Joint analyticity supplies a
common bound on any finite set of these disks near an arbitrary numerator
sequence and arbitrary complex source in W. The geometry package combines
this finite head with the original free tail, preserving every actual disk
and the original distance constant. Its auxiliary empty central disks are
used only to adapt the existing tail estimates, never as the actual disks.

`SourceQuotientDiscSupDecomposition.lean` defines the literal supremum of
the quotient error over D_n, proves it is finite and nonnegative, and gives
exact sequence decompositions with uniform norm bounds on bounded offset
families. For finite q>1 the two summands are in ℓq and ℓ(p/2), including
p/2<1. At q=1 there is one fixed ℓ(p/2) + ℓ(1+) pair: its ℓ(1+) summand
belongs to every finite exponent above one and is chosen before the
projection exponent. Zero summands supply the source's three-term notation.

`SourceQuotientOriginalTopology.lean` proves local uniformity in the
original ℓp root topology for every q≥p, including infinity. The same
joint neighborhood and bounds work for all these q. The free-numerator
consequence has q=p with no additional offset hypothesis, on every disk.
Its filled sine quotient includes the removable center and agrees with the
printed expression away from it. The actual unordered product equals the
analytic quotient on every selected disk.

Concrete checks include zero supremum at the free source, a numerator
collision giving error at least one at a negative free center inside a
central selected disk, p=3/2, the infinity target, a shared endpoint
remainder at exponents two and three, and actual non-real sources in W.
The focused examples and seven new modules compile without new warnings.

Remaining for Lemma 10.8: resolve the original-topology assertion when
q<p and the free-sine display's unspecialized q. The current bounds track
the ℓq offset norm explicitly; they do not prove that this norm is locally
bounded in ℓp when q<p. These are open source-audit items, not declared
counterexamples. Remark 10.9 and later statements remain ahead.

Validation: `./scripts/check.sh` passed (6,872 build jobs, the full public example suite, and the axiom audit of 31,764 NLS declarations). The build retains 21 existing warnings; the seven new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Lemma 10.8 audit result: original-topology uniformity fails

`SourceQuotientUniformityCounterexample.lean` resolves the first remaining
source-audit question: the printed original-topology local-uniformity
assertion is false in general. The formal counterexample has p=4, q=1,
zero source, and finitely supported numerator displacements. It does not
assert failure for every q<p.

`SourceQuotientBlockRoots.lean` perturbs roots 1 through L by one real
amplitude b. Outside this block, the actual analytic quotient at nπ is
exactly the finite product of 1−b/(π(n−m)). The proof uses the convergent
infinite product and the genuine omitted-root domain.
`SourceQuotientBlockLowerBound.lean` proves that for 2L<n≤3L and
0≤b≤π, each error is at least b/(6π). Thus every ℓ2 majorant B satisfies
||B||₂²≥L(b/(6π))².

Taking L=k⁴ and b=δ/(2k) fixes the input ℓ4 norm at δ/2, while forcing
||B||₂≥δk/(12π). Every input also belongs to ℓ1. Arbitrarily small
ℓ4 neighborhoods therefore have no common ℓ2 error bound. The three
printed summands ℓ1+ℓ2+ℓ(1+) would give such a bound by projecting the
last summand to ℓ2 and using contractive inclusion ℓ1→ℓ2, so even allowing
arbitrary decompositions and cancellation cannot restore uniformity.

The final theorem realizes this obstruction for the literal supremum on
a genuine Lemma 10.8 neighborhood with the actual original disks. A
separate positive theorem proves that each individual summable free-source
perturbation still has an ℓ2 supremum sequence. The failure concerns a
common local norm bound, not individual sequence membership.

The sufficient correction already proved is to bound ||σ−τ||q explicitly
when working with q<p. Original-topology uniformity for q≥p, including
infinity, remains proved without that extra bound. The free-sine display's
unspecialized q remains under audit; its unconditional q=p version is
proved. Remark 10.9 and later statements remain ahead.

Validation: `./scripts/check.sh` passed (6,875 build jobs, the full public example suite, and the axiom audit of 31,803 NLS declarations). The build retains 21 existing warnings; the three new modules and focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Lemma 10.8 progress: quadratic diagonal estimates for the Lemma 10.8 free-sine audit

Four modules identify and estimate the actual quadratic contribution to
the resonant diagonal. This advances the remaining free-sine exponent
audit; it does not yet prove improved midpoint summability or finish
Lemma 10.8.

`ResonantDiagonalQuadratic.lean` constructs the reflected product
b_j a_(−j) in ℓ(p/2), with norm at most ||a||p ||b||p even when p/2<1.
Its signed reciprocal sum is exactly the leading physical diagonal row,
with the resonant denominator omitted.
`ResonantDiagonalQuadraticSummability.lean` lifts independent spectral
samples to even Hilbert rows. It proves bounds for the literal supremum
on each free quarter-π disk in every finite r>1 with r≥p/2. For p>2
this includes r=p/2. A single ℓ(p/2)+ℓ(1+) pair works on bounded input
families, with all projections of the same endpoint summand controlled.

`ResonantDiagonalNonlinearRemainder.lean` splits the actual analytic
diagonal into that quadratic row and the explicit second-iterate
correction of the even source vector. The remainder bound first retains
the spectral square estimate and reciprocal row norm, then gives an
exponent-only quartic bound in the unweighted potential norm on the
contraction region.
`SourceResonantDiagonalQuadratic.lean` transports these formulas to the
original period-one source. The quadratic term is

    A2_n(z,φ) = ∑_(m≠n) φ₂,m φ₁,−m / (z+πn−2πm).

At z=nπ its Hilbert-transform factor is −1/(2π), including negative
indices. One open neighborhood of every original source and one cutoff
supply the actual diagonal expansion on every distant closed resonant
strip, with |A_n−A2_n|≤C_p ||φ||p⁴. The contraction hypotheses are
provided by the theorem, rather than assumed of the source family.

Remaining: control the nonlinear remainder in the required sequence
exponents and transfer the diagonal expansion to the actual periodic
midpoint. A coordinatewise quartic bound alone does not supply either
result. The free-sine consequence is still proved unconditionally at
q=p; its printed general q remains unresolved. The previous formal
p=4, q=1 counterexample to numerator local uniformity remains unchanged.

Validation: `./scripts/check.sh` passed (6,879 build jobs, the full public example suite, and the axiom audit of 31,856 NLS declarations). The build retains 21 existing warnings; the four new modules and six focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Lemma 10.8 progress: half-exponent midpoint-center comparison

Six modules close the midpoint-to-diagonal-center comparison needed for
the remaining Lemma 10.8 free-sine audit. On one original-source
neighborhood, the entire sequence τ_n−ζ_n belongs to ℓ(p/2) with a
common norm bound, for every finite p>1, including 1<p<2.

`ResonantMidpointTaylor.lean` proves second-derivative and Taylor bounds
from Cauchy estimates on nested disks. Averaging the two endpoint
expansions cancels the linear terms and leaves a squared-gap error.
`ResonantMidpointCenter.lean` subtracts the two determinant root equations
to bound the sum of the diagonal residuals. For a repeated root, the
vanishing determinant derivative gives the same estimate. Together,
these prove

    |τ_n−ζ_n| ≤ (8/π) sup_(z∈strip_n) |b_n⁺(z)b_n⁻(z)|.

`WeightedResonantMidpointCenter.lean` discharges the root and repeated-root
conditions using the actual periodic spectral pair and its algebraic
multiplicities. It identifies the midpoint with the intrinsic contour
trace. No reality, simple-root, or open-gap premise is needed.
`ResonantOffDiagonalMajorants.lean` constructs two actual ℓp majorants for
the full off-diagonal coefficients, retaining both the leading Fourier
coefficients and the double-row remainder. Their norms have a polynomial
bound on bounded source families.

`SourceResonantMidpointCenter.lean` transports all data to the original
period-one source and identifies the counted pair with the canonical
endpoint labels. `SourceMidpointCenterSummability.lean` multiplies the two
ℓp majorants using Hölder, retaining the quasi-normed exponent p/2 below
one. A fixed finite head completes the full sequence estimate. In that
head the named center retains its existing free fallback if no
refined-disc fixed point is available; its displacement is always at
most π/4.

For every r≥p/2, the actual midpoint displacement belongs to ℓr if and
only if the named diagonal-center displacement does. The remaining
free-sine question is therefore reduced to the nonlinear diagonal
remainder at the moving centers. Its pointwise quartic bound does not
yet give the required sequence estimate. Lemma 10.8 remains incomplete;
the unconditional q=p result and the separate p=4, q=1 local-uniformity
counterexample remain proved.

Validation: `./scripts/check.sh` passed (6,885 build jobs, the full public example suite, and the axiom audit of 31,911 NLS declarations). The build retains 21 existing warnings; the six new modules and six focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Lemma 10.8 audit result: refined free-sine consequence

Eight modules close the remaining Lemma 10.8 free-sine exponent audit.
The literal free-sine quotient error on every original isolating disk has
one locally uniformly bounded ℓ(p/2)+ℓ(1+) decomposition for every finite
p>1. This implies the printed consequence for every q≥1 by taking its
ℓq summand to be zero. The separate original-topology uniformity claim
for arbitrary numerators remains formally refuted at p=4, q=1.

`YoungConvolutionTranspose.lean` transposes the absolutely convergent
Banach-space convolution series through the conjugate pairing.
`UnweightedDoubleRowTesting.lean` tests the two remaining actual
resolvent symbols against arbitrary outer rows.
`ResonantDiagonalRemainderRows.lean` uses the auxiliary exponent 2p and
its conjugate to identify the exact transposed nonlinear diagonal
remainder. Young and Hölder retain two source-frequency reciprocal rows
instead of discarding their dependence on the index.

`ResonantDiagonalRemainderMajorants.lean` applies powered Young to both
rows. Each has an ℓp majorant; their product belongs to ℓ(p/2), including
the quasi-normed range p<2. The resulting majorant controls the actual
nonlinear remainder simultaneously over each full strip on the proved
contraction region. Its norm is quartic in the unweighted component norms.
`SourceDiagonalRemainderMajorants.lean` supplies the contractions on one
original-source neighborhood and cutoff, with a common majorant norm.

`SourceDiagonalCenterSummability.lean` combines the quadratic disk
estimate with this nonlinear bound at the moving diagonal centers.
A fixed finite head covers the named center's free fallback.
`SourcePeriodicMidpointRefined.lean` adds the previous midpoint-center
error. The full actual canonical midpoint displacement is locally
uniformly in every finite ℓr with r>1 and r≥p/2, on a single neighborhood
independent of r. Thus p>2 includes ℓ(p/2); p≤2 gives ℓ(1+), without
claiming ℓ1. One fixed mixed pair realizes these estimates.

`SourceFreeSineQuotientRefined.lean` inserts the actual free-minus-midpoint
offset into the existing full-disk quotient estimates. The theorem
`sourceLemma10_8_freeSine_refined` keeps the common almost-real source
domain and the original disk family, including every central disk and
the filled value at the removable free center. Its two summand maps are
chosen before every ℓ(1+) projection exponent, with uniform bounds on
one source neighborhood.

Lemma 10.8's audit is now resolved: bounded-offset estimates, the valid
original-topology range, the arbitrary-numerator uniformity counterexample,
and the unrestricted free-sine consequence are all accounted for. The
printed arbitrary-numerator uniformity assertion has not been proved;
it is false as stated. Next: Remark 10.9's sharpness expansion, then
Lemma 10.10 and the remaining Section 10 statements.

Validation: `./scripts/check.sh` passed (6,893 build jobs, the full public example suite, and the axiom audit of 31,950 NLS declarations). The build retains 21 existing warnings; the eight new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Exact Taylor expansion underlying Remark 10.9

Five modules prove the exact Taylor expansion underlying Remark 10.9.
For every finite p>1, the literal supremum over each original isolating
disk of

    | product_(m≠n) (τ_m−z)/w_m(z) − 1 − sum_(m≠n) γ_m²/[8(τ_m−z)²] |

is an ℓ(p/4) sequence, locally uniformly in the original source topology.
The estimate includes every central disk, repeated roots and collapsed
gaps. It does not round the exponent up to one or require a distant-index
cutoff. The disk family and common almost-real domain are retained.

`InverseSqrtProductTaylor.lean` proves the exact algebraic identity

    (sqrt(1−q))⁻¹ − 1 − q/2
      = (sqrt(1−q)−1)² (1/2 + (sqrt(1−q))⁻¹).

A uniform inverse-root bound controls the absolutely convergent infinite
product after its signed linear term, without a small-radicand hypothesis.
`SourceMidpointQuotientTaylorGeometry.lean` derives that inverse-root bound
from the original two-sided disk separation, identifies the unordered
product with the actual midpoint-numerator quotient, and records the
coefficient 1/8 and the moving midpoint denominator explicitly.

`SourceMidpointQuotientTaylorMajorant.lean` squares the actual reciprocal
squared-gap row using quasi-norm Hölder. `SourceRemark10_9Taylor.lean`
constructs the literal supremum coefficient and gives one common norm
bound near each source. The public theorem is
`sourceRemark10_9_exactTaylor`.

`SourceSquaredGapRowLowerBound.lean` shows that the row centered at m+1
is at least |γ_m|². Thus improved summability of the absolute row would
force the same improvement for the actual squared gaps. This gives a
necessary condition, not an example realizing a sharp exponent.

At this milestone, the printed replacement of the exact leading sum
by sum_(m≠n) γ_m²/(m−n)² was unresolved. The subsequent actual-source
counterexample recorded here refutes its asserted remainder class at
p=8. The corrected moving-denominator expansion remains valid. The full
p/2 optimality assertion was proved in the subsequent optimality
milestone; Lemma 10.10 and the remaining Section 10 statements remain.

Validation: `./scripts/check.sh` passed (6,898 build jobs, the full public example suite, and the axiom audit of 31,985 NLS declarations). The build retains 21 existing warnings; the five new modules and eight focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Remark 10.9 audit: actual-source counterexample to Remark 10.9's printed remainder

Four modules resolve the printed integer-kernel replacement in Remark
10.9. At p=8, every open neighborhood of zero in the original source
space contains a real potential and an original isolating-disk family
for which the literal printed remainder supremum is outside ℓ². Hence
it is outside the asserted ℓ(p/4)+ℓ(1+) class. This is a counterexample
using actual spectral data, not freely chosen abstract gaps.

`QuarterPowerWitness.lean` constructs the real ℓ⁸ sequence |n|^(-1/4),
zero at n=0, and proves that the squares of every nonzero real multiple
fail ℓ² membership. `SourceSquaredGapNonSummability.lean` scales this
sequence into the target of the already verified inverse Birkhoff chart,
restricted to an arbitrary prescribed open source neighborhood. The
chart preserves reality and the actual action-radius identity. The
bounded normalized-action roots and exact action-gap factorization then
force the actual squared gaps of the inverse source to lie outside ℓ².

`SourceRemark10_9LatticeTerm.lean` identifies the printed signed sum with
the nonnegative physical squared-gap row S for real sources. When the
midpoint displacement has norm at most one, the exact linear term L at
the free center nπ satisfies |L_n(nπ)| ≤ S_n/8. The printed row therefore
cannot be replaced by that Taylor term modulo an ℓ² error for the
constructed source.

`SourceRemark10_9Counterexample.lean` proves boundedness of each printed
supremum on every original disk before using it. If those suprema formed
an ℓ² sequence, combining them with the verified exact Taylor remainder
would give an ℓ² majorant for S on the tail. Finite-head completion and
the neighboring-row lower bound would put the squared gaps in ℓ², a
contradiction. The conditional obstruction works for every isolating
family containing the source; the final theorems construct such a family.

The public results are `sourceRemark10_9_printed_counterexample` and
`sourceRemark10_9_printed_decomposition_counterexample`. The latter
explicitly excludes a decomposition with one ℓ(8/4) summand and one
ℓ(1+) summand. The corrected moving-denominator expansion from the
previous milestone remains valid, including for these same sources and
disks. Seven public checks cover small nonzero real sources, both
remainder classes on the same data, the literal lattice sum, and bounded,
nonnegative suprema on all disks.

This p=8 obstruction at exponent two did not by itself prove full
optimality. The subsequent half-exponent optimality milestone recorded
here proves that assertion for every finite p>2 and every r<p/2, using
actual sources. The printed remainder formula remains refuted. The
next source statement is Lemma 10.10; the dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,902 build jobs, the complete public example suite, and the axiom audit of 32,016 NLS declarations). The build retains 21 existing warnings; the four new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Remark 10.9 audit: full half-exponent optimality in Remark 10.9

Six modules prove the full p/2 optimality assertion for actual source
potentials. For every finite p>2, every r<p/2, and every open neighborhood
U of zero in the original source space, there is a real ψ in U and one
constructed original isolating-disk family such that all three sequences

- the actual squared spectral gaps γ_n²;
- the signed lattice sum sum_(m≠n) γ_m²/(m−n)²;
- the literal supremum over D_n of |product_(m≠n)(τ_m−z)/w_m(z)−1|

belong to ℓ(p/2) and fail membership in ℓr. The same source and disk
family witness all three conclusions. The witness may depend on r;
this is optimality of the general exponent, not a claim that every
potential has exactly that regularity. The free source has zero quotient
supremum and remains an explicitly checked smooth special case.

`StrictSquaredExponentWitness.lean` proves the sharp squared-sequence
behavior of |n|^(-1/(2r)) and its nonzero real multiples.
`SourceSquaredGapSharpness.lean` lifts these real sequence witnesses
through the actual inverse Birkhoff chart inside any prescribed source
neighborhood. The action-radius and normalized-action identities force
the actual squared gaps to fail the stronger exponent.

`SourceMidpointTaylorLowerBound.lean` identifies the linear Taylor sum
at nπ with a convergent nonnegative real sum. A unit bound on the midpoint
displacement gives the neighboring lower estimate

    |γ_m|² ≤ 8(π+1)² |L_(m+1)((m+1)π)|.

`SourceMidpointQuotientSup.lean` proves boundedness and nonnegativity of
the literal quotient supremum and retains its ℓ(p/2) upper membership on
every original disk for p>2. `SourceMidpointQuotientSharpness.lean` shows
that stronger quotient-supremum summability would force stronger
squared-gap summability, by combining the lower estimate with the exact
ℓ(p/4) Taylor remainder and restoring the finite central head.

`SourceRemark10_9Optimality.lean` chooses an intermediate exponent q
between max(r,1,p/4) and p/2. This lets the argument cover every r<p/2,
including r≤1 and the finite-support exponent zero. The public theorem
is `sourceRemark10_9_halfExponent_optimal`. Nine public checks cover the
generic original-topology statement, p=3 and p=8 specializations, the
finite-support endpoint, a central neighboring gap, all-disk upper
membership, and the free-source exception.

Remark 10.9's audit is now resolved: its full general-exponent optimality
assertion is proved, its printed remainder display is formally refuted,
and the exact moving-denominator ℓ(p/4) expansion is the proved correction.
Next: Lemma 10.10, equation (2.15), and the remaining Section 10 statements.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,908 build jobs, the complete public example suite, and the axiom audit of 32,050 NLS declarations). The build retains 21 existing warnings; the six new modules and nine focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.10: common-domain critical offsets

Three modules complete Lemma 10.10 on the unchanged common almost-real
source domain for every finite p>1. At every source in that domain and
all signed indices, the actual critical root equals the midpoint plus
the squared gap times `sourceCriticalGapQuotient`. Each coordinate of
this coefficient is analytic, including across collapsed complex gaps.
A finite central block and the distant-root estimate give one local ℓp
norm bound and one bound for the literal sum of coefficient p-th powers.
The neighborhood and bound precede every nearby source and every index.

`SourceLemma10_8Estimates.criticalOffsets` retains the earlier domain and
Section 10 package. `sourceLemma10_10` constructs the common open connected
domain containing the entire real-type locus. The result includes central
indices and complex sources; it does not require division by a gap or a
reality assumption at the point being estimated.

Six public checks cover the retained domain, one simultaneous power-sum
bound and exact formula, a collapsed central complex gap with analytic
coefficient, indexed endpoint identification, p=3/2, and arbitrarily small
neighborhoods of real basepoints. The next source item is equation (2.15),
followed by admissible paths and Lemma 10.11. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed (6,911 build jobs, the complete public example suite, and the axiom audit of 32,074 NLS declarations). The build retains 21 existing warnings; the three new modules and six focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Equation (2.15): literal critical-root product

Three modules complete equation (2.15) and its following analytic-domain
assertions on the unchanged common source domain for every finite p>1.
The literal product of (critical_m−z)/w_m(z), over all signed indices,
equals i times the actual discriminant derivative divided by the canonical
root. Thus the source's -i normalization holds exactly. The individual
factor deviations from one are absolutely summable, and symmetric finite
products converge to the same normalized quotient.

The proof allows numerator factors to vanish. Both the actual quotient
and the literal product are jointly analytic on the full moving-gap
complement. They also retain the original fixed domain: the complement
of the union of closed isolating disks times the original neighborhood.
`SourceLemma10_10Data.criticalRootProduct` preserves W and the preceding
critical-offset conclusions. `sourceEquation2_15` constructs the common
open connected neighborhood of the entire real-type locus.

Seven public checks cover preservation of W, arbitrary complex source
points, symmetric cutoff convergence, a zero numerator factor, the free
product one and quotient -i, the original closed-disk domain, and p=3/2.
Next: admissible paths and Lemma 10.11. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,914 build jobs, the complete public example suite, and the axiom audit of 32,104 NLS declarations). The build retains 21 existing warnings; the three new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11(i): one extension through every collapsed gap

Three modules prove Lemma 10.11(i) for every finite p>1 on the unchanged
common source domain. One explicit product extends the critical-root
quotient analytically to the complex plane with only the noncollapsed
gap segments removed. Every collapsed factor is filled by one before
taking the product, and the individual factor errors remain absolutely
summable. Central and infinitely many collapsed gaps are included.

The continued function equals the actual quotient off all gaps and the
selected omitted analytic product throughout the omitted domain of any
collapsed index. The enlarged spectral domain is open at every complex
source in W. The preceding common domain, all previous conclusions and
the original isolating disks are retained by
`SourceEquation2_15Data.collapsedContinuation`; `sourceLemma10_11i`
constructs the common open connected neighborhood of the real-type locus.

At zero source, the extension is -i on the entire plane. In particular,
it fills the lattice points where the raw totalized quotient is 0/0=0.
Seven public checks cover that distinction, the infinitely collapsed
free case, a complex collapsed central gap, the exact extension domain,
actual product convergence, unchanged W and p=3/2.

Next: admissible paths and the endpoint-path and closed-contour vanishing
assertions of Lemma 10.11(ii). Part (ii) and the dissertation remain
incomplete.

Validation: `./scripts/check.sh` passed (6,917 build jobs, the complete public example suite, and the axiom audit of 32,137 NLS declarations). The build retains 21 existing warnings; the three new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11(ii): periods and closed contours on the original domain

Five modules prove vanishing of the critical-root quotient's original
circle periods throughout the unchanged connected common source domain,
for every finite p>1. A primitive then exists on every entire original
disk minus its selected gap. Every finite piecewise C¹ closed contour
there has zero integral, including contours with corners, repeated
traversals and self-intersections, at arbitrary complex sources in W.

The circle comparison uses the real centers and separation of the
original disk families. Other gaps lie on the same side of both selected
real diameters, while the selected gap stays inside both circles. Their
affine homotopy avoids every gap even when neither disk contains the other.
Thus one choice-independent indexed period is locally represented by
any original fixed circle and is analytic throughout W. An open zero
germ near one real base propagates across W by the identity theorem.

`SourceLemma10_11iData.zeroPeriods` retains W and the full part (i).
`sourceLemma10_11CirclePeriods` constructs the resulting common domain.
`SourceLemma10_11CircleData.originalDisk_primitive` keeps the entire
original disk; `.originalDisk_loopIntegral_zero` needs no prescribed
homotopy, winding number or real-source assumption. Eight public checks
cover circle independence, analytic periods, propagation from one real
base, retention of W, the central disk, general contours, smooth loops
and p=3/2.

Next: the endpoint-path assertion of Lemma 10.11(ii), including arbitrary
admissible paths and improper endpoint limits. That assertion and the
dissertation remain incomplete.

Validation: `./scripts/check.sh` passed (6,922 build jobs, the complete public example suite, and the axiom audit of 32,193 NLS declarations). The build retains 21 existing warnings; the five new modules and eight focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11: admissible endpoint paths and the full common-domain package

Five modules finish Lemma 10.11 on the unchanged common source domain
for every finite p>1. Every primitive of the actual critical-root
quotient on an original disk minus its gap has the same finite relative
limit at both endpoints, including non-real and collapsed gaps. The
full analytic continuation in part (i) and the closed-contour assertion
proved in the preceding step are retained.

Admissibility is defined literally as avoiding every periodic gap except
possibly at the path endpoints. Every admissible path that is C¹ in its
parameter interior has zero improper integral in its original disk.
The result also covers finite piecewise interior C¹ paths: corners are
allowed, and their interior vertices must avoid the gaps. Neither a
real-source condition, a half-plane restriction, a supplied homotopy,
nor full-path absolute integrability is assumed.

The improper integral is defined by actual truncated parameter integrals,
with its two cutoffs approaching the endpoints independently. The theorem
proves existence and value zero of that limit. For a piecewise path it
uses the limit of sums of truncated piece integrals. For absolutely
integrable C¹ paths the same result holds for the ordinary curve integral.
`SourceLemma10_11CircleData.admissibleEndpoints` upgrades the existing W;
`sourceLemma10_11` supplies the full public package on that domain.

Nine public checks cover retention of W and part (i), literal admissibility,
common boundary values at complex central endpoints, independent cutoffs,
cornered paths, ordinary curve integrals, and p=3/2. Two nonzero integral
checks verify the actual integral definitions: integrating one along
0→1 gives one, and along any cornered chain a→b gives b−a.

Next: Section 11, the action definition and its following assertions.
The dissertation remains incomplete; earlier source corrections and
counterexamples remain recorded in the coverage audit and errata.

Validation: `./scripts/check.sh` passed (6,927 build jobs, the complete public example suite, and the axiom audit of 32,249 NLS declarations). The build retains 21 existing warnings; the five new modules and nine focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 11 opening: simultaneous action contours

Four modules prove the contour setup at the start of Section 11 on the
unchanged common source domain, for every finite p>1. Around any complex
source in W, one open connected neighborhood supports all signed indices
simultaneously. Every circle and its fixed open annular neighborhood lie
inside the corresponding original isolating disk and avoid every moving
gap. The circles have winding number one around each point of their gap,
including collapsed gaps. Outside one finite cutoff they have free centers
and radius 3π/16 inside the original radius-π/4 disks.

The finite-head argument uses the open joint gap complement, a compact
sphere and continuity of the analytic midpoint. Connectedness prevents a
gap from crossing that sphere. No continuity of the ordered endpoint
labels at complex sources is assumed. Locally uniform tail estimates and
a finite intersection give the single common source neighborhood.

`SourceLemma10_11Data.actionContours` preserves W and all of Lemma 10.11.
`SourceSection11ContourData.contours` works with any supplied original
disk family; `.neighborhoods` supplies a family at every source in W.
`sourceSection11Contours` constructs the resulting public package. The
literal integrand λΔ′/canonicalRoot is jointly analytic on each entire
collar times the common source neighborhood, and every chosen fixed-circle
action is analytic there with the exact 1/π normalization.

Nine public checks cover unchanged W, the common all-index quantifiers,
original disks, avoidance of every gap, positive winding at the central
midpoint, both signed tails, the literal action formula, joint analyticity,
actual neighborhood existence and p=3/2.

Next: independence of arbitrary counterclockwise circuits and isolating
families in equation (2.16), followed by the full Lemma 11.1 on the retained
W. The fixed-circle results do not yet establish this global indexed action
or its gradient. See [the Section 11 audit](coverage/SECTION_11.md).
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,931 build jobs, the complete public example suite, and the axiom audit of 32,305 NLS declarations). The build retains 21 existing warnings; the four new modules and nine focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Equation (2.16): contour-independent indexed actions

Five modules define one indexed action on the unchanged common source
domain for every finite p>1. Its value is the literal 1/π integral of
λΔ′/canonicalRoot on every admissible counterclockwise finite piecewise C¹
circuit in every original isolating disk family. Circuits may have corners;
neither a supplied homotopy nor nesting of the compared disks is required.

The proof first subtracts a reciprocal pole with coefficient equal to the
circle period divided by 2πi. The remainder has a primitive on the entire
disk minus its selected gap. Every contour integral therefore equals the
circle period times its winding integral. Comparing original circles from
different real-centered disk families then gives a single choice-independent
`sourceIndexedAction`. The simultaneous inner circles from the preceding
step compute this same function on their common source neighborhood.

The indexed action is analytic on all of W and agrees with the existing
`sourceRealAction` on every real source. Hence it is real and nonnegative
there, and zero exactly when the corresponding gap is zero. It also agrees
with `sourceComplexAction` on a complex neighborhood of every real point
of W, and throughout any connected overlap containing a real point. No
containment of W in the earlier complex chart domain is assumed.

`SourceSection11ContourData.defineActions` preserves W and the full
preceding package. `sourceEquation2_16` supplies the public common-domain
statement, including the literal circuit formula, analyticity and the
bridges to existing actions. Eleven focused public checks cover arbitrary
winding, distinct isolating families, the central circuit formula, retained
W, simultaneous circles, nonzero real actions, complex germ and overlap
agreement, a nonzero repeated-winding integral, and p=3/2.

Next: the exact gradient formula (2.17) in Lemma 11.1 on the same W,
including the complex collapsed-gap consequence used in its proof.
The full lemma and dissertation remain incomplete. See the updated
[Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,936 build jobs, the complete public example suite, and the axiom audit of 32,351 NLS declarations). The build retains 21 existing warnings; the five new modules and eleven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 11.1 on the retained domain

Six modules complete Lemma 11.1 for every finite p>1 on the unchanged
common source domain W. The indexed actions retain equation (2.16) and
analyticity on W. Their actual complex Fréchet derivatives equal the
negative 1/π integral of the discriminant variation divided by the
canonical root, on every admissible counterclockwise finite piecewise C¹
circuit in every original open isolating neighborhood.

The proof differentiates the canonical-root square identity on the
retained joint domain, identifies the source derivative of Δ′/Q with the
spectral derivative of Δ_v/Q, and differentiates under a fixed circle.
Integration by parts gives the exact minus sign in equation (2.17).
An outer-circle winding formula then transfers the result to arbitrary
circuits with corners. No real-base restriction or supplied homotopy is
needed for the gradient theorem.

The same W also supports zero action at every collapsed complex gap,
including the central gap: Lemma 10.11's continued quotient is analytic
through the filled inner disk. On every real source, the actions are real
and nonnegative, vanish exactly when the literal canonical gap vanishes,
and are strictly positive when that gap is open.

`SourceEquation2_16Data.actionGradients` preserves W and all preceding
contour and action identifications. `sourceLemma11_1` supplies the complete
public package. Eleven focused checks cover domain retention, the joint
root derivative, the mixed derivative identity at complex sources, original
central circles, general-circuit gradients, complex collapsed gaps, the
real zero criterion and strict positivity, older-action agreement, a
nonzero integration-by-parts sign check, and p=3/2.

Next: the analytic zero sets Z_n and Theorem 11.2's normalized actions.
The dissertation remains incomplete. See the updated
[Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,942 build jobs, the complete public example suite, and the axiom audit of 32,375 NLS declarations). The build retains 21 existing warnings; the six new modules and eleven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 11: Theorem 11.2, normalized indexed actions

Four modules prove the analytic zero-locus assertion and the full statement
of Theorem 11.2 for every finite p>1. The original domain W₀ and all of
Lemma 11.1 are retained. One open neighborhood W⊆W₀ contains the entire
real-type source locus and supports all signed indices simultaneously.

The analytic normalized factor multiplies the literal canonical squared
gap to give the actual `sourceIndexedAction`, including at collapsed
complex gaps. Away from the gap zero set it is exactly I_n/γ_n². Both this
factor and its principal square root are complex and real analytic on W.
The roots never vanish, have positive real values on real sources, and
equal one at the zero source. The normalized factor equals 1/4 there.

At every complex point of W, one open neighborhood has a positive lower
bound for the real parts of all normalized factors. That same local
construction supplies actual ℓ^(p/2) and ℓ^(1+) summand functions for
both 4I_n/γ_n²−1 and ξ_n−1. The neighborhood and the summands are chosen
before the index and before every finite one-plus exponent q>1; their
respective quasi-norm and norm bounds are uniform on that neighborhood.

The key bridge builds all real-centered action charts on one source ball
using the simultaneous circles. This identifies every indexed action with
the previous complex-action construction on that common ball, allowing
its established analytic factors and estimates to be used for the actual
indexed actions. No infinite intersection of index-dependent domains is
used. Taking the union of qualifying open neighborhoods proves local
uniformity at arbitrary complex points, not only at real base points.

`sourceTheorem11_2` is the public existence theorem;
`SourceLemma11_1Data.normalizedActions` upgrades an existing original
domain. `sourceActionGapZeroLocus` is defined by the actual squared gap
on W₀, with an analytic defining function, relative closedness, and zero
indexed action there. On W, zero action is also equivalent to zero gap
for complex sources.

Next: audit the intermediate formulas (2.18)–(2.19), then Section 12.
The dissertation remains incomplete. See the
[Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,946 build jobs, the complete public example suite, and the axiom audit of 32,429 NLS declarations). The build retains 21 existing warnings; the four new modules and fifteen focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 11: equation (2.18), deleted product and recentered actions

Five modules prove equation (2.18), its literal deleted product χ_n,
and the following recentered action formula for every finite p>1.
`SourceLemma11_1Data.actionChi` retains the existing open source domain W
and the full preceding action theorem. `sourceEquation2_18` supplies the
open connected domain containing the entire real-type source locus.

The actual ℓᵖ critical displacement is analytic on W, allowing its
substitution into Corollary 10.6. Thus χ_n is jointly analytic on the
full moving complement of the other gaps, throughout every original
selected disk, and on the fixed complement of the other closed disks.
The latter uses U_m under the union over m≠n; the printed U_n is an index
typo, visually checked and recorded in `SOURCE_ERRATA.md`.

The literal quotient factorization has exactly the factor −i. Subtracting
the vanishing unweighted period gives the actual indexed action as
(i/π) times the integral of (critical_n−z)²χ_n/w_n on every admissible
finite piecewise C¹ winding-one circuit in the original cut disk.
Complex sources, central indices and collapsed gaps are included.
No original disk or source neighborhood is replaced.

Ten focused checks cover domain retention, sequence-valued analyticity,
both joint and original fixed domains, the selected disk, exact quotient
normalization, arbitrary central circuits, χ_0(0)=1 at the free collapsed
gap, the nonzero free quotient −i at z=i, and p=3/2.

Next: equation (2.19), its preceding weighted gap-integral formula for
complex sources, the collapsed limit and extension claims on every
original V_φ. These are not inferred from the smaller-domain Theorem 11.2.
Section 12 follows that audit. The dissertation remains incomplete.
See the [Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,951 build jobs, the complete public example suite, and the axiom audit of 32,456 NLS declarations). The build retains 21 existing warnings; the five new modules and ten focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 11: equation (2.19) and the original-domain extension

Six modules prove equation (2.19), its preceding weighted gap-integral
formula and the analytic collapsed-gap extension for every finite p>1.
`SourceEquation2_18Data.gapFormulas` retains the original open connected
source domain W and its entire preceding action package.

The actual indexed action equals the complex gap integral with the
literal inverse-square-root weight and factor 2/π. Away from zero gaps,
4I_n/γ_n² equals the stated integral with t_n=(critical_n−τ_n)/(γ_n/2).
Both weighted integrands are genuinely integrable at their endpoints.
The exact identity t_n=2γ_n B_n retains Lemma 10.10's actual ℓᵖ coefficient.

The proof establishes the regular cosine mean at real sources, including
collapsed gaps, and continues the identity throughout the original
connected complex domain. Analyticity of the midpoint and squared gap
suffices; no analytic choice of endpoint labels is assumed. A complex
change-of-variables theorem then yields the literal weighted formula.

`sourceNormalizedIndexedAction` equals the actual indexed quotient off
zero gaps and χ_n(τ_n)/4 at zero gaps. Local agreement with the existing
rationalized circle candidate proves analyticity on all of W. Thus
4I_n/γ_n² tends to χ_n(τ_n) along arbitrary complex approaches within W
with nonzero selected gap. The midpoint value is itself analytic on W.
The function agrees with the extension in Theorem 11.2 on that theorem's
smaller domain; at a collapsed gap its principal root squares to χ_n(τ_n).
At zero potential the filled normalized action is exactly 1/4 for all n.

`sourceEquation2_19` supplies the complete package. Eighteen focused
checks cover the unchanged domain, both integral identities and their
integrability, the critical coordinate, analytic extension and exact
factorization, complex collapsed limits, original circles, compatibility
with Theorem 11.2, midpoint analyticity, the collapsed root square, free
normalization, nonzero complex integral and shifted-moment constants,
and p=3/2 and p=4.

Next: audit the remaining p. 62 locally uniform χ_n and normalized-action
estimates on the full original domain, then Section 12. The smaller-domain
Theorem 11.2 estimates remain proved; they do not by themselves settle
those original-domain proof assertions. The dissertation remains
incomplete. See the [Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,957 build jobs, the complete public example suite, and the axiom audit of 32,536 NLS declarations). The build retains 21 existing warnings; the six new modules and eighteen focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 11: page 62 estimates on the original domain

Five modules prove the remaining p. 62 estimates on the entire original
source domain for every finite p>1. `SourceEquation2_19Data.originalEstimates`
keeps W and all previous integral and extension results.

The literal supremum of |χ_n−1| over the actual complex gap G_n is finite,
nonnegative, and bounds every gap point. At collapse it is exactly the
midpoint error; at the free source it vanishes for every signed index.
Near every complex point of W, this supremum and the actual deviation
4F_n−1 have fixed ℓ^(p/2)+ℓ^(1+) summand functions with uniform bounds.
One neighborhood and all four functions are chosen before any index or
finite one-plus exponent. F_n is the actual indexed quotient I_n/γ_n²
off zero gaps and the established analytic extension at zero gaps.

The proof substitutes the analytic critical-displacement map into the
existing joint quotient estimates. Lemma 10.10 gives the needed actual
half-exponent midpoint offset, so no stronger-topology assumption on an
arbitrary numerator is used. All original isolating families are allowed,
and the finite central block is included. The normalized-action cosine
identity now includes collapsed complex gaps; its quantitative error
bound transfers the literal gap supremum estimate to the actions.
The exact critical coordinate t_n=2γ_n B_n also has a locally uniformly
bounded ℓ^(p/2) coefficient, including the quasi-norm range p/2<1.

`sourceSection11OriginalEstimates` supplies the original open connected
W containing the entire real-type source locus and the complete package.
Seventeen focused checks cover domain retention, finite and collapsed
suprema, the complex cosine identity and error constants, original disk
families, the order of the uniformity quantifiers, the literal quotient,
free values, and p=3/2, p=2 and p=4. The p=3/2 check explicitly produces
the critical coordinate in ℓ^(3/4).

Next: Section 12, starting with the simultaneous psi-functions in (2.20)
and their normalized periods in (2.21). Positivity and the principal
square root remain on Theorem 11.2's established smaller domain. The
dissertation remains incomplete. See the [Section 11 audit](coverage/SECTION_11.md).

Validation: `./scripts/check.sh` passed (6,962 build jobs, the complete public example suite, and the axiom audit of 32,580 NLS declarations). The build retains 21 existing warnings; the five new modules and seventeen focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Section 12: Theorem 12.1 and original psi circuits

Four modules assemble the full statement of Theorem 12.1 for every
finite p>1. `SourceSection11OriginalEstimates.psiFunctions` constructs one
open, simply connected W inside the supplied original W₀, containing the
whole real-type source locus and supporting every deleted index n.
The complete preceding Section 11 package on W₀ is retained.

The entire functions use the literal symmetric product (2.20), with
prefactor −2/πₙ and π₀=1. Their roots are complex analytic, hence real
analytic, in the source. At every complex point of W, one neighborhood
and one positive bound work for all n in σₘⁿ=τₘ+γₘ²aₘⁿ, with actual
bounded ℓᵖ vectors aⁿ and aₙⁿ=0. At real sources every retained root lies
between the actual periodic endpoints; at zero potential σₘⁿ=mπ.

Equation (2.21) holds on every admissible original piecewise C¹ circuit,
with the exact factor 1/(2π). More generally, its period is δₘₙ times
the winding around the actual gap midpoint. The proof compares the
atlas's assigned circles with arbitrary original circles and then uses
the contour theorem for a disk cut along a compact segment. Collapsed
complex gaps and the finite central block are included.

Twenty focused checks cover retention of the original domain, the
literal product and zero-mode denominator, genuine root zeros,
entireness and joint analyticity, all-index uniformity, complex collapsed
roots, real endpoint bounds, arbitrary circuits and winding two,
nonzero free normalization, both signed free roots, and p=3/2 and p=4.

Next: audit the functional formulation (2.22)–(2.23) and Lemmas 12.2–12.3
against the original domain and circuits. The dissertation remains
incomplete. See the [Section 12 audit](coverage/SECTION_12.md).

Validation: `./scripts/check.sh` passed (6,966 build jobs, the complete
public example suite, and the axiom audit of 32,621 NLS declarations).
The build retains 21 existing warnings; the four new modules and twenty
focused checks are warning-free. The source inventory verified 156
candidate labels, and `git diff --check` passed. No admitted proofs,
additional axioms, or heartbeat overrides were introduced.

## Section 12: scalar psi equations and local contour domains

The scalar formulation of (2.22)–(2.23) now uses the actual original
piecewise C¹ circuits. `sourceGapFunctional` is (n−m) times the raw
canonical-root integral, with no 1/(2π) factor. Substituting the literal
entire product recovers the existing circle coordinate for every
arbitrary ℓᵖ displacement vector. Original circle families agree, and
an arbitrary original circuit computes that coordinate times its winding.
The simultaneous Theorem 12.1 family solves all these scalar equations.

The zero-contour argument now applies to a numerator analytic near the
filled original disk, with reality required only on the selected gap.
It covers both open and collapsed real gaps and every nonzero circuit
winding. In the collapsed case no reality condition on the numerator
is needed. The older entire-numerator APIs retain their signatures and
follow from these local proofs.

A verified counterexample makes the domain requirement precise. At the
free central gap {0}, f(z)=z/(z−1/2) is analytic on ℂ\{1/2}, which contains
the gap and the unit circle, and f vanishes on the gap. Nevertheless its
normalized standard-root contour is −1 and its normalized absolute value
is 1. The circle avoids all periodic gaps. Thus mere inclusion of the
gap and curve in an open analytic domain is insufficient for Lemma 12.3;
interior poles must be excluded from the contour deformation region.
See [the domain clarification](SOURCE_ERRATA.md).

This step proves the scalar formulation and the local disk version of
the zero-contour implication. It does not yet complete Lemmas 12.2–12.3
for contours adapted to arbitrary analytic gap neighborhoods, or the
complex open-gap maximum estimate. Those are next, followed by the full
ℓᵖ-valued mapping assertion in Lemma 12.4. The dissertation remains
incomplete. See the [Section 12 audit](coverage/SECTION_12.md).

Validation: `./scripts/check.sh` passed (6,971 build jobs, the complete
public example suite, and the axiom audit of 32,661 NLS declarations).
The build retains 21 existing warnings; the five new modules, the
refactored entire-numerator module, and seventeen focused checks are
warning-free. The source inventory verified 156 candidate labels, and
`git diff --check` passed. No admitted proofs, additional axioms, or
heartbeat overrides were introduced.

## Section 12: local gap contours and Lemmas 12.2–12.3

The local contour argument now works in arbitrary analytic neighborhoods
of a gap. The affine Joukowski map sends circles with radius r>1 to
ellipses avoiding the complex gap. Its normalized-root Jacobian is
−1/u. Cauchy's theorem on the image annulus and uniform convergence on
a compact parameter rectangle identify the actual contour period as
−2πi times the gap's cosine average. No enclosing midpoint disk inside
the numerator's domain is assumed.

`sourceLemma12_3_local` constructs a genuine piecewise C¹ contour inside
any supplied open analytic gap neighborhood, with actual winding one.
Noncollapsed gaps use ellipses; collapsed gaps use small circles. The
normalized absolute value is bounded by an attained maximum of |f| on
the actual source gap. If f is real on that gap, its normalized complex
period is −f(μ) for some point μ in the gap. Every finite p>1 and every
complex source are covered.

For original isolating disks,
`SourceCriticalRootPeriodCircle.standardRoot_local_circle_period` and
`.standardRoot_local_circuit_period` give the exact cosine formula,
including complex open and collapsed gaps and arbitrary circuit winding.
`.lemma12_3_circle` and `.lemma12_3_circuit` package both estimates, with
analyticity near the filled original disk as the explicit sufficient
condition. Finite piecewise C¹ circuits may have corners and intersections.

`SourceCriticalRootPeriodCircle.lemma12_2_local` proves the zero-functional
implication on a contour adapted to any analytic neighborhood of a real
source gap. It divides by the omitted root product only inside the
intersection with the original disk. The constructed contour avoids
all periodic gaps and has winding one. For m≠n, Aₘⁿf=0 implies an actual
zero of f in Gₘ, with reality required only on the gap. Both open and
collapsed gaps are included; no entire extension of f is used.

These are explicit admissibility versions of Lemmas 12.2–12.3. They do
not infer the estimates for an arbitrary loop merely contained in a
possibly punctured analytic domain. The previous pole counterexample
still has unit-circle period −1; the new construction supplies a small
admissible contour with period zero. A second rational example has poles
inside every enclosing midpoint disk but admits the local ellipse
mean-value theorem. See the [Section 12 audit](coverage/SECTION_12.md).

Next: Lemma 12.4's full original-domain ℓᵖ-valued mapping, analyticity and
bounds locally uniform in all deleted indices. The dissertation remains
incomplete.

Validation: `./scripts/check.sh` passed (6,981 build jobs, the complete
public example suite, and the axiom audit of 32,768 NLS declarations).
The build retains 21 existing warnings; the ten new modules and nineteen
focused public checks are warning-free. The source inventory verified
156 candidate labels, and diff checks passed. No admitted proofs,
additional axioms, or heartbeat overrides were introduced.

## Equations (2.24)–(2.26) and the literal equation-index supremum

The literal products (2.24)–(2.25) and the asymptotic (2.26) are now
proved on the original source domain and original isolating disks.
`sourcePsiZeta` uses the absolutely convergent double-omitted product.
The factorization of the actual contour integrand remains valid when
numerator roots coincide or the unused numerator root equals the
evaluation point. The older quotient representation retains its explicit
denominator-avoidance hypothesis.

For every finite p>1, every complex base source φ in W and every full
ℓᵖ input a₀, one open neighborhood and constants K,C work before choosing
the omitted index n. The weighted literal product splits exactly as
i/π plus a reciprocal-distance term bounded by K/|n−m| and a sequence
term. The actual disk suprema of the latter form an ℓᵖ sequence of norm
at most C, with zero at m=n. The entire finite head is included, and the
preceding source domain is unchanged.

Uniform coordinate replacement uses compact single-coordinate insertions
at the base input and contractive deletion of nearby perturbations.
The l^(p/2) quotient contribution embeds into ℓᵖ even for 1<p<2.
The unused root is fixed at the base midpoint in its original disk;
the remaining roots are unrestricted.

The stronger assertion in Lemma 12.4's proof is also certified:
`SourceLemma12_4Data.originalEquation_indexSup` constructs the literal
sequence sup_{n≠m}|Fₘⁿ(ψ,deleteₙ a)|. A common ℓᵖ majorant controls all
n at once, and this supremum sequence is locally bounded in the full
original parameter topology.

Eighteen focused checks exercise removable numerator-division points,
retained-root collisions, arbitrary double-omitted products, independence
of the unused root fill, exact asymptotic decomposition, actual disk
suprema and equation-index suprema, and exponents 3/2 and 4.
See the [Section 12 audit](coverage/SECTION_12.md).

Next: Lemma 12.5's actual Jacobian on the original real domain Ωᵖ,
including nonzero diagonals and the stated diagonal/off-diagonal
asymptotics. Existing restricted tail results do not by themselves
certify that full assertion. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,996 build jobs, the complete
public example suite, and the axiom audit of 32,893 NLS declarations).
The build retains 21 existing warnings. The seven new modules, extended
compact-slice helper, and eighteen focused public checks are warning-free.
The source inventory verified 156 candidate labels, and diff checks
passed. No admitted proofs, additional axioms, or heartbeat overrides
were introduced.

## Lemma 12.4 on the original source domain

`SourceSection11OriginalEstimates.lemma12_4` proves the sequence-valued
mapping assertion on the entire supplied original W, retaining the
preceding Section 11 data without shrinking that domain. For every finite
p>1, every complex source in W, every deleted index n and every arbitrary
deleted ℓᵖ root input, `sourcePsiOriginalEquation` is an actual deleted
ℓᵖ sequence whose coordinates equal (2.22) on every original circle.
The map is both complex analytic and real analytic in the source-first
parameter order printed in the dissertation.

The proof supplies one neighborhood and one norm bound before choosing n.
The literal p-power sum is strictly bounded by a positive constant on
that neighborhood, again uniformly in n. The omitted coordinate is zero,
so summing the extended sequence over all integers gives the printed
sum over m≠n. Reality on real source/root data and the exact winding
formula for original piecewise C¹ circuits are also proved. The family
from Theorem 12.1 solves this actual Banach-valued equation.

Arbitrary root inputs need not place all displaced roots inside the
isolating disks. The unused root is filled with the base source midpoint
in its original disk. These single-coordinate insertions lie in a compact
set in ℓᵖ. A finite subcover makes the quotient bound uniform in the
inserted index; original disk separation controls its denominator.
Lemma 12.3 then bounds every coordinate by the three displacement
magnitudes, which are actual ℓᵖ sequences. This includes the finite head,
complex gaps and collapse without any root-location restriction.

The total equation definition has a fallback outside the set where its
literal coordinate characterization has a witness. The witness is proved
at every point of W for every input; the fallback is never used there.
The public equation theorem gives exact coordinate agreement, rather
than assuming the choice has the desired formula.

Seventeen focused examples cover large imaginary root shifts with an
exact nonzero response, roots outside their disks, root collisions,
analyticity at those collisions, an explicitly nonreal source in any
open W containing zero, negative circuit winding, the same original W,
the Theorem 12.1 solution, and exponents 3/2 and 4.
See the [Section 12 audit](coverage/SECTION_12.md).

Next: audit the literal auxiliary products and the precise asymptotic
(2.24)–(2.26), then the Jacobian assertions of Lemma 12.5. Lemma 12.4 is
proved directly from the original-domain quotient bounds; this does not
by itself certify every intermediate asymptotic or later statement.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,989 build jobs, the complete
public example suite, and the axiom audit of 32,817 NLS declarations).
The build retains 21 existing warnings; the eight new modules and seventeen
focused public checks are warning-free. The source inventory verified
156 candidate labels, and diff checks passed. No admitted proofs,
additional axioms, or heartbeat overrides were introduced.

## Lemma 12.5 on the original real domain

`SourceLemma12_4Data.lemma12_5` proves Lemma 12.5 for the actual bounded
root derivative of the original equation, retaining the preceding source
domain W. `sourcePsiOriginalOmega` uses the full real source and full real
ℓᵖ root input, with every root in its assigned original disk before any
omitted index is chosen. This domain is open, including its infinite tail
placement condition.

Every matrix entry is real on real data, and every retained diagonal is
nonzero. The exact contour formulas use the literal double-omitted product.
The diagonal mean-value point belongs to the selected gap Gₘ, including
collapsed gaps. Analyticity is proved on a neighborhood of the closed
original disk, and root placement supplies every required separation.
The unused root fill does not change the actual derivative.

One neighborhood and constants K,C work for every omitted index n.
The diagonal is exactly 2+Rₘ+Sₘ, with |Rₘ|≤K/|n−m| and an actual ℓᵖ
sequence S of norm at most C; both errors vanish at the omitted coordinate.
A common ℓᵖ row majorant controls |m−r||Qₘᵣⁿ| for every n and column r.
The literal supremum over all off-diagonal columns and omitted equations
is itself an ℓᵖ sequence with the same local norm bound. All central rows
and columns are included, for every finite 1<p<∞.

Twenty focused public examples check the free matrix (diagonal 2 and
zero off-diagonal), negative and central indices, arbitrary unused-root
fills, deleted rows and columns, bounded differentiation without reality
or placement restrictions, original-domain openness and separation,
collapsed-gap evaluation, local uniformity, actual supremum sequences,
and exponents 3/2 and 4. A consequence verifies simultaneous vanishing
of every weighted off-diagonal row at infinity at a fixed point.
See the [Section 12 audit](coverage/SECTION_12.md).

Printed p. 66 names Gₙ in its final nonvanishing sentence; the required
interval is Gₘ. This index typo is recorded in [SOURCE_ERRATA.md](SOURCE_ERRATA.md).
No additional mathematical assumption is imposed.

Next: Lemma 12.6 for this actual original-domain Jacobian: an invertible
diagonal plus a compact remainder. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (7,004 build jobs, the complete
public example suite, and the axiom audit of 32,972 NLS declarations).
The build retains 21 existing warnings. The eight new modules and twenty
new public checks are warning-free. The source inventory verified 156
candidate labels; all 100 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

## Lemma 12.6 on the original real domain

`SourceLemma12_5Data.lemma12_6` proves that the actual bounded root
Jacobian is a diagonal continuous linear equivalence plus a compact
operator at every original Ωᵖ point, for every finite 1<p<∞ and every
omitted index. The preceding open connected source domain W and all
Lemma 12.5 data are retained.

For each fixed omitted index n, the diagonal entries tend to 2 as
|m| tends to infinity. Their nonvanishing on the finite head gives a
positive lower bound on all retained entries. The diagonal inverse
is explicit coordinatewise multiplication by the reciprocal entries;
both inverse identities hold on the complex deleted Banach space.

The canonical off-diagonal remainder has an actual ℓᵖ row majorant,
obtained from the reciprocal matrix bounds and conjugate-exponent
Hölder duality. Its finite output cutoffs have finite-dimensional range
and converge in operator norm. The cutoff error is bounded by the
ℓᵖ tail of that majorant. All central rows and columns are included.


Eighteen new public checks cover signed diagonal limits, the finite-head
lower bound, reciprocal inverse formulas, both inverse identities,
compactness, finite-rank ranges and norm convergence, cutoff behavior at
and away from the omitted index, the unchanged source domain, original
Ωᵖ points, and exponents 3/2 and 4.

Next: Lemma 12.7, injectivity of this actual original-domain Jacobian.
The dissertation remains incomplete. No new source correction is needed
for Lemma 12.6.

Validation: `./scripts/check.sh` passed (7,008 build jobs, the complete
public example suite, and the axiom audit of 33,006 NLS declarations).
The build retains 21 existing warnings. The four new modules and eighteen
new public checks are warning-free. The source inventory verified 156
candidate labels; all 115 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

## Lemma 12.7 on the original real domain

`SourceLemma12_6Data.lemma12_7` proves injectivity of the actual bounded
root Jacobian at every original Ωᵖ point, for every finite 1<p<∞ and
every omitted index. It retains the same open connected source domain W,
the preceding diagonal-plus-compact decomposition, and all earlier data.
Injectivity holds on the complex deleted Banach space.

Every actual matrix row sums to the bounded derivative applied to an
arbitrary direction, and every coordinate equals the contour integral of
its entire numerator variation. For real kernel directions, the original
contours supply a zero in each retained gap, including collapsed gaps.
The selected zeros have ℓᵖ displacements and are distinct. Together with
the original omitted root they define a simple entire interpolation
product. Interpolation forces the variation to vanish identically;
evaluation at the distinct original roots then recovers the zero direction.
Real matrix entries reduce a complex kernel vector to its real and
imaginary parts, proving the full complex result.

The source's outer-circle proof assertions are also certified: all large
half-integer-radius circles avoid the entire original disk family; the
literal root product has its exact sine normalization and tends uniformly
to one; and φ=(σₙ−z)φₙ/2 satisfies φ/sin(z)→0 uniformly. The exact
root-resolvent/product factorization is retained. No selected local chart
or replacement disk family is imposed.

Twenty-two new public checks cover matrix row sums, arbitrary complex
directions, collapsed gaps, kernel splitting, injectivity, unused root
fills, simple interpolation zeros, original disk avoidance, literal
product identities and decay, the retained source domain and preceding
decomposition, and exponents 3/2 and 4.

Next: Corollary 12.8, invertibility of the actual Jacobian using the
Fredholm alternative. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (7,013 build jobs, the complete
public example suite, and the axiom audit of 33,040 NLS declarations).
The build retains 21 existing warnings. The five new modules and twenty-two
new public checks are warning-free. The source inventory verified 156
candidate labels; all 117 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

## Corollary 12.8 on the original real domain

`SourceLemma12_7Data.corollary12_8` proves that the actual root Jacobian
is a continuous linear isomorphism at every original Ωᵖ point, for every
finite 1<p<∞ and every omitted index. The Fredholm alternative combines
the preceding diagonal-plus-compact decomposition with injectivity. Both
the complex and real deleted Banach spaces have continuous inverses.
The same open connected source domain W and all preceding data are retained.

`RealDeletedCoeff` is the closed subspace of real ℓᵖ sequences whose omitted
coordinate is zero. Complex inclusion and real-part projection connect it
to the complex deleted space. Real matrix entries imply that the complex
inverse preserves real inputs, giving the real linear equivalence.
Its underlying operator is exactly the real Fréchet derivative of
`sourcePsiOriginalRealEquation` at the original root input. At real-type
sources this equation agrees, under inclusion, with the original equation.

Twenty-three new public checks cover both inverse identities on both
spaces, the actual real derivative, compatibility of the two inverses,
unique real preimages, nonreal right-hand sides, omitted and negative
indices, unused root fills, fixed-point inverse norm bounds, the unchanged
source domain, and exponents 3/2 and 4. The norm bounds here are for a fixed
source and omitted index; uniform inverse bounds are a later obligation.
See the [Section 12 audit](coverage/SECTION_12.md).

Next: Proposition 12.9, the unique global real analytic solution map with
roots in the actual gaps. The dissertation remains incomplete. No new
source correction is needed for Corollary 12.8.

Validation: `./scripts/check.sh` passed (7,018 build jobs, the complete
public example suite, and the axiom audit of 33,111 NLS declarations).
The build retains 21 existing warnings. The five new modules and twenty-three
new public checks are warning-free. The source inventory verified 156
candidate labels; all 120 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

## Proposition 12.9 on the original real domain

`SourceCorollary12_8Data.proposition12_9` proves the unique global real
analytic solution map for the original psi equation, for every finite
1<p<∞ and every omitted index. Its values are actual real deleted ℓᵖ
vectors. Complex inclusion recovers the canonical gap-root map exactly.
The same open connected source domain W and all preceding data are retained.

The deleted placement domain is open and is exactly the projection of
original Ωᵖ under coordinate deletion. The solution graph lies in every
supplied original disk family over its real sources. Any real zero with
retained roots in those disks has its roots in the actual gaps, including
collapsed gaps, and equals the canonical solution. Uniqueness requires
no prior gap-placement assumption and holds across different disk families.

The earlier gap-solution construction supplies global existence,
continuation, and uniqueness. Exact original-circle coordinates now
transfer those results to the original equation and domain. The analytic
implicit theorem is also applied directly to the original complex
equation using Corollary 12.8's actual Jacobian. The real equation is
jointly analytic, and a local real branch through any placed zero stays
in the same original domain. Solutions converge in the full real ℓᵖ norm
along converging source sequences. At the free source the unique solution
has zero displacement.

Twenty-seven new public checks cover the actual equation and real codomain,
original-domain projection and graph lifting, uniqueness across disk
families, collapsed and free gaps, local real and complex analytic
branches, full sequence convergence, unchanged preceding data, and
exponents 3/2 and 4. See the [Section 12 audit](coverage/SECTION_12.md).

Next: Lemma 12.10, original-domain uniform inverse bounds and a common
complex extension for all omitted indices. The dissertation remains
incomplete. No new source correction is needed for Proposition 12.9.

Validation: the full build (7024 jobs), public example suite, and axiom
audit (33156 NLS declarations) pass. The six new modules and 27 new
checks are warning-free; the build reports 21 pre-existing warnings.
All 156 source inventory labels and 123 local Markdown links verify.

## Lemma 12.10, first proof steps: equations (2.28) and (2.29) on the original domain

The first operator-construction steps of Lemma 12.10 now hold on the
original isolating disks. Equation (2.28) uses the literal ratio
(nπ−mπ)/(σₙ−λ), with a uniform reciprocal-distance bound over every placed
complex root input and every point of the selected disk. At each fixed
row, one cutoff works in both index directions for all those inputs.

Actual original Jacobian entries converge to the literal Q* contour
entries. An eventual common operator bound makes these entries a bounded
operator, with coordinatewise convergence on every ℓᵖ input. Uniqueness
identifies one intrinsic Q*, independently of the original disk family
or circle. Its total definition's default branch is excluded throughout
the original placed-root domain at real-type sources. Roots may be
complex and need not lie in their spectral gaps for these results.

`sourceEquation2_29` retains Proposition 12.9 and its unchanged W. On every
original real Ωᵖ it proves the actual Q* diagonal is nonzero and equals
2 plus an ℓᵖ sequence, and its off-diagonal entries have one ℓᵖ row
majorant divided by index distance. Both sequence bounds are locally
bounded in the original parameters. The diagonal mean-value formula
uses an actual gap point and includes collapsed gaps. These estimates
make Q*−2I compact; bijectivity is reduced to a separate injectivity proof.

One joint root/source Lipschitz estimate controls every original full
Jacobian near a real-type source, with all omitted indices included.
Passing that estimate through coordinatewise limits proves operator-norm
continuity of Q* on the full original domain. On the smaller compact gap
product, Q* agrees with the prior bijective limit; the proved uniform
norm convergence and actual deleted inverse bounds transfer there.

Thirty new public checks cover complex root inputs, original circle and
family independence, the omitted diagonal convention, signed and central
indices, collapsed gaps, joint topology, compactness, the exact weighted
equation identity, and exponents 3/2 and 4. See the
[Section 12 audit](coverage/SECTION_12.md).

Lemma 12.10 remains incomplete. Next: full-domain operator-norm convergence,
Q* injectivity, and the original common complex extension. The printed
local-uniformity claim is also being audited. Gap-product norm convergence
and inverses are not asserted on the larger domain. No new source
correction is claimed in this milestone.

Validation: the full build passed (7033 jobs), the complete public example
suite passed, and the transitive axiom audit passed for 33238 NLS
declarations. The nine new modules and thirty new checks are warning-free;
the 21 existing warnings remain. The source inventory still verifies all
156 candidate labels, and all 134 checked local Markdown file links resolve.

## Lemma 12.10: full original-domain norm convergence and uniformity

The full original Jacobians now converge in operator norm to the intrinsic
Q* at every fixed real placed-root input, for every finite 1<p<∞ and as
the omitted index escapes in either direction. Roots need not lie in
their spectral gaps. The existing diagonal proof is generalized to
arbitrary real root inputs; its former gap-domain API remains available.
A single fixed ℓᵖ majorant controls all off-diagonal matrices and gives
uniform finite-block approximation. The off-diagonal norm limit even
allows complex placed-root inputs.

`sourceLemma12_10_normLimit` retains Proposition 12.9 and its unchanged
open connected W. Convergence on each original real Ωᵖ is locally
uniform in mathlib's sense: for each error tolerance and each base point,
one neighborhood and one index cutoff work for every input there.
Consequently convergence is uniform on every compact subset of Ωᵖ,
with both roots and sources allowed to vary.

A verified free-source counterexample resolves the stronger interpretation
of printed p. 69. For a real displacement δ at the omitted index n,
the adjacent diagonal of Qⁿ−Q* is exactly 2δ/π. Fixed small spikes can
move arbitrarily far out while staying in any given ball inside Ωᵖ.
Thus no fixed neighborhood of the free point supports uniform norm
convergence. This does not contradict the tolerance-dependent local
uniformity proved above. The counterexample includes existence of an
original isolating family and uses the actual original operators.
See [the source clarification](SOURCE_ERRATA.md).

Seventeen public checks cover unrestricted real diagonal inputs, complex
off-diagonal inputs, full-domain norm convergence, signed-index cutoffs,
strong convergence on every input vector, joint local and compact-set
uniformity, the actual free-spike identity and lower bound, failure on
all fixed neighborhoods, and exponents 3/2 and 4.

Lemma 12.10 remains incomplete: full original-domain Q* injectivity and
the common original complex extension are next. The printed source-only
Lipschitz bound remains under audit; the proved bound controls both roots
and source parameters.

Validation: the full build passed 7037 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33286 NLS
declarations. The four new modules, two generalized modules, and seventeen
new checks are warning-free; the 21 existing warnings remain. The source
inventory verifies all 156 candidate labels, and all 145 checked local
Markdown file links resolve.

## Lemma 12.10: original-domain invertibility and common complex inverse bounds

The intrinsic Q* is now bijective throughout the original real Ωᵖ for
every finite 1<p<∞. Its actual original contour action turns a real
kernel direction into a full product variation with a zero in every
spectral gap. Entire-function uniqueness, original-disk separation,
and reality of the matrix give complex injectivity; the Fredholm
alternative gives surjectivity. The input roots need only be real and
lie in the original disks.

The full original inverses converge in operator norm to (Q*)⁻¹ as the
omitted index escapes in either direction. One bound controls every
signed index at each base point, including the genuine deleted-space
inverse from Corollary 12.8.

Direct use of Lemma 12.4 gives one joint complex equation bound at all
deleted centers. Coordinate decay handles the tail and finitely many
local bounds handle the remaining indices. Cauchy's estimate gives a
common Lipschitz bound in both roots and sources. The Neumann estimate
then supplies actual two-sided inverses on one joint complex ball,
with radius and norm bound independent of the deleted index. This is
proved for both the full operators and the actual deleted Banach spaces.
An open neighborhood can also be kept inside the original source
neighborhoods and every original isolating disk.

`sourceLemma12_10_inverseBounds` packages the limit's bijectivity and
the common deleted-space complex inverse bounds, retaining Proposition
12.9 and the unchanged open connected W. Eighteen public checks cover
complex kernel directions, unique inhomogeneous solutions, signed-index
inverse limits, the actual Corollary 12.8 inverse, unrestricted complex
chart inputs, preservation of original domains, solution norm bounds,
and exponents 3/2 and 4.

Lemma 12.10 remains incomplete: the common analytic solution extension
must still be connected to the original isolating disks and global
domain requirements. The printed source-only Lipschitz estimate remains
under audit; the proved complex estimate controls both roots and sources.

Validation: the full build passed 7043 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33317 NLS
declarations. The six new modules and eighteen new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, and all 151 checked local Markdown file links resolve.

## Lemma 12.10: common original-domain extension

`sourceLemma12_10` completes the common complex extension for every finite
1<p<∞. One open simply connected W lies inside the unchanged Proposition
12.9 domain W₀ and contains the entire real-type source locus. All actual
original real solution maps extend analytically to this same W, and the
extensions solve the actual original equation. The package retains
Proposition 12.9 and Theorem 12.1 for exactly these domains and root maps.

For every supplied original disk family, compactness of the full gap
product gives a common placement margin. Uniform stability of the analytic
branches then places all retained roots, and the moving-midpoint fill,
in the same disks on one source ball independent of the omitted index.
The source neighborhood may shrink; the disks and comparison constant
are unchanged. Existing original isolating families also give the literal
local placement assertion on W∩V at every real-type source.

The printed p. 69 source-only Jacobian estimate is false when roots vary
independently. Arbitrarily small real placed-root perturbations change an
actual Jacobian at the fixed free source, making its proposed right-hand
side zero. This is proved for both full extensions and genuine deleted
blocks, with an existing original disk family. The previously proved
joint root/source estimate supplies the needed control. This correction
does not rule out source-only estimates along a prescribed solution graph.

Nineteen new public checks cover the common domain, actual real-solution
agreement and original equation, retained preceding data, uniform original
disk placement, the midpoint fill, constructed local families, both forms
of the counterexample, and exponents 3/2 and 4. An end-to-end example
states the full extension and local original-placement conclusion.

Next: Lemma 12.11, the remaining diagonal period normalization. The
dissertation remains incomplete; Lemma 12.10 is complete with the precise
uniformity clarification and estimate correction recorded in SOURCE_ERRATA.md.

Validation: the full build passed 7046 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33349 NLS
declarations. The three new modules and nineteen new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, and all 154 checked local Markdown file links resolve.

## Lemma 12.11: original diagonal normalization

`SourceLemma12_10Data.lemma12_11` proves the literal diagonal integral
2π for every complex source in the same common W, for every finite
1<p<∞ and every signed index. Both W₀ and W and all root maps are
unchanged. Every admissible original circle has this value; every
original piecewise C¹ circuit has 2π times its winding, hence 2π for
the source's positive cycles. Original period circles are constructed
at every source, including complex sources.

The proof follows the source's contour argument. The actual original
equation makes each retained period zero. Nested circles with disjoint
analytic collars are constructed inside any supplied original disk
family. Their exact free tail gives finite-hole geometry at all large
half-integer cutoffs. The outer contour therefore equals the omitted
original period, and the actual exterior limit fixes its value. This
argument does not use the retained Theorem 12.1 diagonal-period field.

The literal full standard-root quotient is an unconditional product,
including vanishing numerator factors. Filling the omitted coordinate
with the moving midpoint gives the printed pole formula. The product
tends uniformly to one on the outer circles, for arbitrary ℓᵖ numerator
roots and complex sources.

The two individual sine asymptotics on printed p. 70 need a minus sign.
With π₀=1, both underlying products have leading term −sin λ. Their
quotient still tends to one and the final integral is still +2π. The
corrected asymptotics are proved, and at the free source the error in
each printed positive-sine ratio is exactly two on every outer circle.
See SOURCE_ERRATA.md for the normalization convention and exact scope.

Twenty-six public checks cover original geometry, direct equation zeros,
large-circle equality, literal products and midpoint fill, numerator
zeros, orientation and winding, constructed circles, all collapsed free
gaps, unchanged preceding data, and exponents 3/2 and 4.

Next: Lemma 12.12's locally uniform squared-gap root offsets on this
same W. The dissertation remains incomplete.

Validation: the full build passed 7050 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33437 NLS
declarations. The four new modules and twenty-six new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, and all 158 checked local Markdown file links resolve.

## Lemma 12.12 on the original complex domain

`SourceLemma12_11Data.lemma12_12` proves the literal squared-gap root
factorization on exactly Lemma 12.10's W and root maps, retaining
Lemma 12.11's periods and the original W₀. For every finite 1<p<∞,
one positive bound for the summable p-power series works for all
omitted indices on a neighborhood of every complex source. The omitted
coordinate is filled with the moving midpoint and has zero offset;
collapsed complex gaps force the actual root to equal that midpoint.

The original construction witness is now retained in Lemma 12.10's
package. It supplies the common positive midpoint lower bound for the
same family. Its previously proved squared-gap estimate also supplies
norm compactness of the filled root vectors at each complex source.
Uniform branch continuity and a compact-parameter argument then transfer
the quotient estimates to every supplied original disk, including the
full quarter-π tail disks. This proof reuses that established estimate
for compactness; it does not assume compactness of arbitrary norm balls.

The literal identities (2.30), (2.31), and (2.33) hold on original
circles. Equation (2.32) has a complete ℓᵖ majorant locally throughout
W, uniformly in the omitted index. Existing simultaneous original
contours have a common positive boundary margin. Cauchy's estimate
bounds the divided differences on their entire filled disks. The actual
gap maximum gives both inequalities in (2.34), including their common
ℓᵖ bound. An O(1) branch estimate followed by the two substitutions
produces first-gap and squared-gap sequences, with exact factorizations
also at zero gaps. No further shrink of the common W occurs.

Twenty-eight public checks cover the unchanged domains and normalization,
complex-source compactness and uniform graph continuity, literal products,
original disk and contour estimates, signed indices, the first-order
expansion, both substitution stages, partial and total power sums,
collapsed complex and free gaps, and exponents 3/2 and 4.

Next: Section 13's admissible-path angle definitions and Theorem 13.1.
The dissertation remains incomplete.

Validation: the full build passed 7059 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33501 NLS
declarations. The nine new modules and twenty-eight new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, and all 167 checked local Markdown file links resolve.

## Section 13 original-domain path invariance

`sourceSection13OriginalDomain` retains exactly Lemma 12.12's W₀, W,
and psi root family. The earlier spectral results supply endpoint data
at every complex source. Actual original disk neighborhoods contain all
gaps and Dirichlet terminals simultaneously; no additional intersection
or replacement root atlas is used.

The original periods construct off-diagonal primitives and diagonal
model-remainder primitives on the full cut complement of every supplied
original disk. Their periodic endpoint values agree. Prescribed-sheet
primitives extend through cut interiors. At collapsed gaps, the actual
numerator cancels the selected root and gives a removable extension;
its normalized sheet data satisfy the same interface as open gaps.

For beta, any two integrable C¹ admissible paths with continuously
continued roots give the same integral when normalized at the actual
Dirichlet anti-discriminant. They may use different original disks, and
neither path must stay inside its terminal root chart. At periodic
terminals either sign gives zero, including collapsed gaps. For collapsed
beta gaps, integrability of every such C¹ path is also proved. For eta,
two admissible paths in any supplied original disk agree modulo 2π on
open gaps, with either sign permitted at a periodic terminal.

The general path comparisons explicitly require curve integrability;
the eta comparison requires it for both the actual and model integrands.
This step proves invariance of these integrals. It does not yet construct
every endpoint integral or identify the analytic angle functions on the
retained W. These remaining obligations are recorded in the Section 13
audit, before Theorem 13.1's estimates and series assertions.

Nineteen public checks cover the retained domain and family, actual
Dirichlet containment, full original-disk primitives, continued roots,
comparisons across disks, periodic terminals, collapsed complex and free
gaps, and exponents 3/2 and 4.

Next: construct and identify the endpoint integral values on this same W,
then audit Theorem 13.1 and Corollary 13.2. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 7066 build jobs, the complete
public example suite, and the transitive axiom audit of 33524 NLS
declarations. The seven new modules and nineteen new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 176 checked local Markdown file links resolve,
and `git diff --check` passes.

## Section 13 original-domain beta analyticity and estimate

`sourceTheorem13_1_original_beta` constructs the same W₀, W, and psi root
family retained by Lemma 12.12. Every off-diagonal beta has a unique
normalized primitive value at every complex source in W. Every integrable
C¹ admissible path in an original disk, with the actual Dirichlet terminal
normalization when nonzero, evaluates to that beta. Periodic terminals
and collapsed gaps are included.

Each beta is complex analytic throughout this unchanged W. Original
isolating disks supply local annuli around the periodic segment and
Dirichlet terminal. The proof uses stability of the whole segment and
analyticity of the terminal, without assuming analyticity of the ordered
periodic endpoints or dividing by the gap length.

The literal Theorem 13.1(i) estimate is now locally uniform in both
indices at every complex source:

`‖β_m^n‖ ≤ C (‖γ_m‖ + ‖μ_m − τ_m‖) / |n − m|`.

One neighborhood and positive constant work for all `m ≠ n`. The original
all-disk chi majorant controls each selected central chart uniformly in
the deleted index. Analyticity of the boundary displacement sequences
in their full sequence norm supplies the small Dirichlet tail at complex
sources. Fixed tail annuli then give a bound uniform in both indices;
a finite intersection handles the remaining selected gaps.

Twelve public checks cover value uniqueness, path evaluation, original
chart geometry, fixed tail annuli, sequence analyticity, the order of the
uniform quantifiers, periodic-terminal zeros, and exponents 3/2 and 4.

The analytic and estimate assertions for these beta values are proved.
Constructing integrable admissible paths at open singular endpoints is
still required for the complete literal integral construction. The eta
identification, beta-series assertions, theta assertions, and the full
same-domain Corollary 13.2 audit remain unfinished.

Next: construct the remaining endpoint paths and identify eta on this W,
then apply the beta estimate to the series. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 7072 build jobs, the complete
public example suite, and the transitive axiom audit of 33546 NLS
declarations. The six new modules and twelve new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 182 checked local Markdown file links resolve,
and `git diff --check` passes.

## Section 13 constructed endpoint integrals

`SourceLemma12_12Data.original_dirichlet_integral_path` constructs a
smooth path and continuously continued square root in every supplied
original disk containing its actual Dirichlet terminal. The root equals
the actual terminal anti-discriminant, including when it vanishes. The
same path realizes every off-diagonal beta numerator. No path or curve
integrability assumption is supplied by the caller.

The geometric construction uses a quadratic Bézier arc inside the
convex disk. Its interior stays strictly on one side of the selected
gap's line. Distances to both periodic endpoints have a common positive
lower bound proportional to `t(1-t)`. The construction also covers a
collapsed segment and a closed path with coincident endpoints.

For an open gap, the quadratic root gives an inverse-square-root bound
at each endpoint. The pulled-back actual angular one-forms and the eta
model are integrable under the weight `sqrt(t(1-t))`. The full root is
continued from the canonical interior root, with its global sign chosen
to match the prescribed terminal value. At zero endpoints, convergence
of the square proves convergence of the root. Collapsed-gap beta
integrability uses the original removable extension.

`beta_original_exists_improper_integral` identifies every beta with the
joint limit of ordinary parameter integrals as both truncation endpoints
approach independently. Thus the previously proved analytic beta and
uniform estimate now apply to constructed literal endpoint integrals.
At every open gap, the diagonal eta integral and its model also exist.
General path comparisons retain explicit integrability for other paths.

Twelve public checks cover collapsed closed paths, prescribed zero and
nonzero roots, independent endpoint truncations, one path for all beta
numerators, periodic-terminal zeros, open-gap eta/model integrability,
and exponents 3/2 and 4. The exponent-4 check constructs the original
domain, disks, paths, and integral values without any supplied witnesses.

Next: identify the eta integral class with the analytic eta charts on
the same W, then prove the remaining beta-series and theta assertions.
The full Corollary 13.2 audit and the dissertation remain incomplete.

Validation: `./scripts/check.sh` passes with 7,078 build jobs, the complete
public example suite, and the transitive axiom audit of 33,571 NLS
declarations. The six new modules and twelve new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 188 checked local Markdown file links resolve,
and `git diff --check` passes.

## Section 13 original-domain eta integrals and analyticity

`sourceTheorem13_1_original_eta` retains the same W₀, simply connected W,
and normalized psi family from Lemma 12.12. At every complex open gap,
`sourceAngularOriginalEta` is chosen from actual normalized endpoint
integrals. The fallback in its definition is never used on this domain.

Two original disks admit a shared transverse path in their open convex
intersection. Comparing each given path with this common path proves
that all normalized integrable eta values differ by an integer multiple
of 2π, even across different disks and at periodic terminals. No nesting
of the disks or nonzero terminal anti-discriminant is required.

The original annulus charts construct local analytic representatives
on the unchanged W. Every original-disk eta integral differs from these
representatives by an integer multiple of π. Consequently the phase
`exp(2i eta)` is a single nonzero complex analytic function throughout
the open-gap domain. The representatives and actual eta integrals are
real at real-type sources. The original off-diagonal beta values are
also proved real there, including collapsed gaps.

The chosen eta is a joint improper integral: both endpoint truncations
converge independently to its value. Actual and model integrability are
constructed for the chosen paths. General comparisons of other supplied
paths retain their C¹ and curve-integrability hypotheses.

Twelve public checks cover a noncircular convex intersection, common paths
in different disks, the stronger 2π period, literal integral phases,
real-type values, independent endpoint truncations, and periodic terminals
without a sign condition. Unconditional checks at exponents 4 and 3/2
construct the original domain and integral values or local representatives.

Next: prove locally uniform convergence and decay of the beta series on
this same W, then identify the literal theta sum and audit Corollary 13.2.
The remaining Section 13 assertions and the dissertation are incomplete.

Validation: `./scripts/check.sh` passes with 7,083 build jobs, the complete
public example suite, and the transitive axiom audit of 33,603 NLS
declarations. The five new modules, two extended construction modules,
and twelve new checks introduce no warnings; the 21 existing warnings
remain. The source inventory verifies all 156 candidate labels, all
193 checked local Markdown file links resolve, and `git diff --check` passes.

## Section 13 original series, theta, and canonical brackets

`sourceTheorem13_1_original` retains the same W₀, simply connected W,
and normalized psi family from Lemma 12.12. The literal beta correction
series converges absolutely at every source and locally uniformly on a
neighborhood common to every deleted index. Its sum is complex analytic
on W. Both the absolute sum and the correction tend to zero as the signed
index tends to either infinity. At real-type sources the correction is real.

`sourceAngularOriginalTheta` is exactly the constructed eta integral plus
this beta series. Changing the eta integral changes theta by an integer
multiple of 2π. Local analytic representatives agree with the literal sum
modulo π, are real at real-type sources, and have exactly the existing
phase differential. The complete angular interface is constructed with
W in all three domain slots, preserving the original root family.

`sourceCorollary13_2_original` supplies all three canonical identities for
every finite p>1. The action/action bracket needs no open-gap hypothesis;
the theta/theta bracket requires the two angle gaps to be open; the mixed
bracket requires only the angle gap. A collapsed action gap is allowed.

The action comparison is explicit: the original indexed action and the
earlier complex action have equal complex germs near every real source,
hence equal Fréchet derivatives. `originalActionCotangent` has the indexed
action's actual derivative as its underlying functional. The angle's
regular cotangent is likewise the derivative of a local representative of
the literal theta sum. Their square-summable coefficients give the actual,
absolutely convergent Fourier pairing with frequency reversal and sign -i,
including below exponent two.

Fourteen public checks cover the common-neighborhood quantifier order,
absolute convergence, decay in both directions, real values, integral-choice
periods, actual local differentials, all three brackets, collapsed action
gaps, and the literal Fourier sum. Unconditional checks at exponents 4 and
3/2 retain the original domain and verify the canonical mixed identity.

Remaining Section 13 work: extend the general path comparison from supplied
curve-integrable C¹ paths to arbitrary admissible C¹ paths whose endpoint
integrals are interpreted as improper limits. Constructed paths already
have absolute integrability and independent endpoint limits. No blanket
absolute-integrability assertion for arbitrary C¹ paths is made. After
that source-definition audit, proceed to Section 14. The dissertation is
not complete.

Validation: `./scripts/check.sh` passes: the full build completes 7,089
jobs, all public examples pass, and the transitive axiom audit checks 33,629
NLS declarations. The six new modules and fourteen new checks introduce no
warnings; the 21 existing warnings remain. The source inventory verifies
all 156 candidate labels, all 199 checked local Markdown file links resolve,
and `git diff --check` passes.

## Section 13 arbitrary-path improper integrals

The original angular integrals now exist along every admissible path
whose parameterization is C¹ on the open unit interval and whose root
continuation is continuous on the closed interval. Both endpoint cutoffs
vary independently. No absolute-integrability assumption or endpoint
C¹ assumption is required.

`beta_original_improper_limit` identifies the actual truncated beta
integrals with `sourceAngularBeta` on the retained Lemma 12.12 domain.
It includes collapsed gaps and regular terminals in the cut. At either
periodic terminal, `beta_original_periodic_terminal_improper_limit`
gives zero on either sheet. The value therefore agrees between different
original isolating disks.

`eta_original_admissible_improper_limit` proves existence at every open
gap and identifies every limit with `sourceAngularOriginalEta` modulo 2π.
The proof lifts the model's nonvanishing logarithmic coordinate along
the whole parameter interval, and evaluates the normalized remainder
by its primitive endpoint limits. It compares an arbitrary path with a
constructed integrable path in the same disk, then uses the established
cross-disk comparison. At a periodic terminal no root sign prescription
is needed. `eta_original_improperIntegral_spec` exposes both convergence
and the 2π class of the limit-defined integral.

Twelve public checks cover joint endpoint limits, beta equality and eta
periods across different disks, periodic terminals, the actual eta and
theta phases, reality, the same local analytic representative modulo π,
and agreement with ordinary curve integrals when they are integrable.
The statements apply to every finite p>1. The previous convergence,
analyticity, and canonical-bracket results consequently apply to this
arbitrary-path interpretation of the angle definitions.

The remaining Section 13 path obligation is discharged for the stated
interior C¹ class. No claim of absolute integrability for all such paths
is made. Next: audit Section 14's rectangular coordinates (3.1) against
these original actions and angles, then the five assertions of Theorem
14.1 and their proofs in Sections 15–17. The dissertation is not complete.

Validation: `./scripts/check.sh` passes: the full build completes 7,099
jobs, all public examples pass, and the transitive axiom audit checks 33,665
NLS declarations. The nine new modules, extended primitive-integral module,
and twelve new checks introduce no warnings; the 21 existing warnings
remain. The source inventory verifies all 156 candidate labels, all 209
checked local Markdown file links resolve, and `git diff --check` passes.

## Section 14 original Birkhoff map and real geometry

`sourceSection14_original` constructs the Birkhoff sequence map for every
finite p>1 using the same normalized root family retained from Lemma 12.12.
On an open complex neighborhood of the entire real locus, the full map is
complex analytic, its coordinates are the actual rectangular functions,
and their squared radius is twice `sourceIndexedAction`.

The exact signed phase is now proved: the gap-weighted coordinate equals
the canonical gap times exp(±i eta) for the literal original eta integral.
This fixes the sign not determined by equality of doubled phases.
`rectangular_formula` consequently proves equation (3.1), with cosine for
x and positive sine for y, using the original eta-plus-beta theta.
The analytic coordinates extend through complex collapsed gaps; at real
collapsed gaps both coordinates vanish.

The same map has all three canonical brackets on the real locus, with
regular cotangents whose underlying functionals are the actual complex
Fréchet derivatives. The mixed bracket is the absolutely convergent
Fourier pairing with frequency reversal and sign -i. This covers the
canonical assertion in the sense specified by Lemma 15.3, including p<2.
The real map is analytic and injective, has a two-sided analytic local
inverse at every source, and has open dense image. For 1<p≤2 it has a
global analytic inverse on the entire target.

Thirteen public checks cover the exact phase, original rectangular
formula, full sequence analyticity and evaluations, original action
radius, real closed-gap zeros, real restriction, canonical derivatives
and Fourier sum, real geometry, and real exponent compatibility.
Unconditional examples at p=4 and p=3/2 verify the construction and the
appropriate image and inverse conclusions.

Theorem 14.1(ii) is still incomplete: equality at real sources and equality
of complex germs do not establish equality on the entire intersection of
the complex exponent domains. That domain-compatibility proof is next,
followed by detailed source audits of Sections 15–17. Surjectivity for p>2
is not claimed; Remark 14.2(ii) leaves it open. The dissertation remains
incomplete. See [the Section 14 audit](coverage/SECTION_14.md).

Validation: `./scripts/check.sh` passes: the full build completes 7,105
jobs, all public examples pass, and the transitive axiom audit checks 33,689
NLS declarations. The six new modules and thirteen new checks introduce
no warnings; the 21 existing warnings remain. The source inventory
verifies all 156 candidate labels, all 220 checked local Markdown file
links resolve, and `git diff --check` passes.

## Section 14 full complex exponent compatibility

`sourceSection14` now constructs the original Birkhoff map on compatible
complex neighborhoods for every finite p>1. `SourceSection14Data.exponent`
proves equality on the entire complex intersection after coefficient
exponent inclusion. It applies to arbitrary complex sources, including
collapsed gaps, and to any two independently constructed packages.
Together with the inherited original-family results, this establishes
the five assertions of Theorem 14.1 for these constructed maps.

The domain is the union of every ball centered at a real source and
contained in the preceding map domain. It is open and still contains the
whole real locus. Given a point in two exponent domains, choose one ball
from each. The intersection of the first ball with the inclusion preimage
of the second is convex and contains the point's real-type projection.
The projection contracts distances from real centers and commutes with
exponent inclusion. Banach-valued analytic uniqueness propagates real
agreement across this convex overlap to the original complex point.

`eventually_map_exponent` identifies the whole sequence map on one germ
at every overlap point; `fderiv_exponent` identifies its full complex
Fréchet derivative after the input and output inclusions. Neither result
requires the source to be real. The construction preserves the original
root family, exact rectangular formula, indexed-action radius, canonical
brackets, real local inverses, and global inverse for 1<p≤2.

Twelve new public checks cover the domain geometry, full complex
intersection, sequence-valued germs and derivatives, independence of
families at a fixed exponent, and retained formulas and inverses.
Independent unconditional constructions at p=3/2 and p=4 agree on their
complex intersection; the p=3/2 construction retains both global inverse
identities on the entire real target.

Next: audit the detailed arguments and auxiliary assertions in Sections
15–17 against the original quantities. The identification in Remark
14.2(i) with the precise external Hilbert-space construction and the full
fractional Fourier–Lebesgue extension mentioned in Remark 14.2(iii) are
not separately certified by this milestone. Surjectivity for p>2 is not
claimed. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passes: the full build completes 7,108
jobs, all public examples pass, and the transitive axiom audit checks 33,710
NLS declarations. The three new modules and twelve new checks introduce
no warnings; the 21 existing warnings remain. The source inventory
verifies all 156 candidate labels, all 223 checked local Markdown file
links resolve, and `git diff --check` passes.

## Remark 14.2(iii) milestone: Remark 14.2(iii), original weighted membership and injectivity

For every finite 1<p<infinity, the original real Birkhoff map now takes every
weighted real source into the corresponding weighted real target. The result
holds for every Section 6 spectral weight, and one constructed Section 14
map works for all these weights. It is injective on each full weighted real
source space.

The proof completes the finite central set in the weighted spectral-gap
estimate, then uses the original action radius and normalized-action bound
to control both real coordinates by the actual gap lengths. Positive
weighting identifies the original closed real source with a complete real
lp space. Input and output coefficient identities show that this is the
same original map, with the exact weighted component-sum target norm.

The half-scale spectral weight w(k)=(1+|k|/2)^s gives w(2n)=(1+|n|)^s
exactly. Every real s>=0 is covered, including fractional orders; no
doubling constant or integer-order restriction is introduced. The five
new modules and 24 public checks include fractional p and s, negative and
zero frequencies, original coefficients, completeness, norm identities,
and unconditional constructions below and above p=2.
See [the updated Section 14 audit](coverage/SECTION_14.md).

Next: prove locally uniform bounds for the weighted complex coordinates
and their analyticity in the weighted topology. Weighted canonicality,
local inverse and open dense image, exponent compatibility, and the global
inverse for 1<p<=2 still need their full extension. This membership and
injectivity result does not complete Remark 14.2(iii). The external map
comparison, unrestricted Lemma 27.2 and G.2 norm qualifications remain;
the dissertation is incomplete.

Validation is recorded in [the current implementation status](STATUS.md).

## Remark 14.2(iii) topology milestone: weighted continuity and fractional Sobolev dense range

The original real Birkhoff map is now continuous in the stronger source
and target norms for every Section 6 spectral weight and every finite
1<p<infinity. A common weighted complex neighborhood controls the actual
gap sequence and all sufficiently distant tails. One coordinate bound
holds for all nearby real sources, so the same tail control proves
continuity of the full weighted real map.

For every nonnegative real Sobolev order s, the image is dense in the
original weighted target norm. Every finite target truncation has an
actual finite-gap preimage; the existing regularity bootstrap puts that
same source in the exact (1+|n|)^s space at the same exponent. Removing
and restoring the target weight preserves the finite coefficients, and
weighted truncation convergence proves density. This includes fractional
orders, zero regularity, and p>2 without asserting surjectivity there.

One constructed Section 14 package gives continuous injections for every
spectral weight and dense image for every Sobolev weight. Four new modules,
two updated modules, and 22 public checks cover the complex gap bounds,
uniform tails, exact weighted target coordinates, continuity, finite-gap
lifts, and approximation of arbitrary weighted targets.
See [the Section 14 audit](coverage/SECTION_14.md).

Next: prove weighted complex analyticity and the remaining extension in
Remark 14.2(iii). In particular, the weighted Dirichlet-minus-midpoint
estimate needed for the complex coordinate bound is still missing.
Weighted canonicality, exponent compatibility, open image and local
inverse, and the global inverse for 1<p<=2 remain. Dense image is proved
for Sobolev weights; no arbitrary-spectral-weight density claim is made.
The external map comparison, unrestricted Lemma 27.2 and G.2 norm
qualifications remain, and the dissertation is incomplete.

Validation is recorded in [the current implementation status](STATUS.md).

## Remark 14.2(iii) compatibility milestone: weighted real exponents and gap characterization

The original weighted real Birkhoff maps now commute with increasing the
exponent, for every finite 1<p<=q and every Section 6 spectral weight.
The maps can use independently constructed normalized families. Both
source and target inclusions preserve the raw coefficients and their
reality conditions, are continuous and injective, and compose exactly.
The real coefficient inclusion is contractive; the pair maps use their
actual source and target lp norms. An unconditional construction supplies
two compatible Section 14 packages for every such exponent pair.

A common positive lower bound for normalized actions also gives a
converse gap estimate near every real source: one constant bounds each
gap by the sum of the two absolute rectangular coordinates, uniformly
in the source and signed index. Together with the forward bound, this
proves that the actual gap sequence has any given positive weight in lp
if and only if both original real Birkhoff coordinates do. This result
allows arbitrary positive weights, including decreasing weights; it does
not assume that the original source already carries that weight.

Four new modules and 23 public checks cover fractional exponents across
two, negative and zero frequencies, exact compositions, source decoding,
independent map families, fractional Sobolev weights, and both directions
of the weighted gap characterization. The sequence-space inclusions also
cover the infinite Banach exponent; the Birkhoff statements retain finite
p>1. See [the Section 14 audit](coverage/SECTION_14.md).

Next: prove weighted complex analyticity and compatibility on complex
domains, weighted canonicality, open image and local inverses, and the
global inverse for 1<p<=2. The gap characterization concerns spectral
gaps and Birkhoff outputs; recovering weighted source regularity remains
a separate step. The complex estimate for the actual Dirichlet-minus-
periodic-midpoint displacement is also missing. The external map
comparison, unrestricted Lemma 27.2 and G.2 norm qualifications remain;
the dissertation is incomplete.

Validation is recorded in [the current implementation status](STATUS.md).

## Remark 14.2(iii) regularity milestone: Fourier-tail recurrence with nonzero spectral gaps

The actual off-diagonal coefficients at the moving diagonal center are
now bounded by twice the periodic gap, uniformly on a neighborhood of
each source and for every sufficiently distant index. Canonical counted
endpoints supply the roots; the proof includes collapsed gaps and does
not assume that the center lies between them. Forgetting a spectral
weight preserves the centers and transfers the same bound to any
available weighted realization.

Consequently, weighted gaps imply weighted membership of the actual
adapted closing coordinates for every positive even weight. The cutoff
is chosen before the weight, and no weighted regularity of the original
source is assumed. The previous gap/Birkhoff characterization gives the
same implication from weighted real Birkhoff outputs.

The Fourier-tail recurrence now retains a nonzero gap forcing term.
Writing v(N) for the p-power Fourier tail at physical cutoff 2N and G(N)
for the actual weighted gap power tail at source cutoff N, it proves
v(4N) <= C_p (2 C_p G(4N) + C ||psi||^p
(||psi||^(2p)/(4N)^alpha + v(N)^2)), where C_p=2^p and
alpha=min(1,p-1). Here C is the existing off-diagonal summation constant,
and psi is any weighted realization already carried by the source.
All norms are the actual component-sum norms.

A forced quadratic summability theorem then transfers the exact geometric
weight r^k from G(4^(k+1)M) to v(4^k M), provided r>0 and
r*4^(-alpha)<1. The proof absorbs the quadratic term after the tail becomes
small and retains the finite prefix. It does not replace the requested
weight with a slower geometric rate. Six modules and 16 public checks
cover these estimates, signed indices, collapsed gaps, fractional
exponents, and arbitrary real Sobolev orders for adapted coordinates.
See [the Section 14 audit](coverage/SECTION_14.md).

Next: identify geometric tail summability with exact Sobolev coefficient
membership and iterate the gain to recover weighted regularity of the
original source. Weighted complex analyticity and compatibility,
canonicality, open image, local inverses and global inversion for 1<p<=2
remain. The complex Dirichlet-minus-periodic-midpoint estimate is still
missing. The external map comparison, unrestricted Lemma 27.2 and G.2
norm qualifications remain; the dissertation is incomplete.

Validation is recorded in [the implementation status](STATUS.md).

## Remark 14.2(iii) milestone: exact Sobolev regularity and original weighted range

For every finite p>1 and every real t>=0, the original real source,
its actual periodic gaps, and both original Birkhoff coordinates have
exactly the same Sobolev regularity. The source converse assumes no
finite-gap property and no prior positive source regularity. Summability
of four-adic tails preserves the exact requested order; a finite sequence
of gains delta=t/K reaches t without requiring any greater gap weight.
Half-scale spectral weights retain the original (1+abs(n))^t convention.

The original weighted range is exactly the preimage of the unweighted
range under a continuous inclusion preserving every raw target coefficient.
It follows that the original Sobolev map has open dense image for every
finite p>1. For 1<p<=2 it is onto and therefore bijective on the native
weighted source and target spaces. One actual Section 14 construction
supplies these conclusions simultaneously at all nonnegative real orders.

The weighted bijection has both inverse identities. Its inverse agrees
with the original unweighted inverse on raw source coefficients and
commutes with increasing exponents within 1<p<=q<=2, including independent
normalized families. These are algebraic inverse statements; continuity
or analyticity of the inverse in the stronger weighted topology is not
inferred from bijectivity or from open image.

Seven new modules and 28 public checks cover exact tail summability,
original weighted representatives and inclusions, fractional and zero
orders, p=3/2 and p=4, large-order iteration, range equality, open image,
surjectivity, both inverse identities, and inverse exponent compatibility.
The sequence-space lemmas also retain their applicable p=1 and infinity
endpoints. See [the Section 14 audit](coverage/SECTION_14.md).

Next: weighted complex analyticity and compatibility, weighted canonicality,
analytic local inverses, and continuity and analyticity of the weighted
global inverse. The complex Dirichlet-minus-periodic-midpoint estimate is
still missing. No surjectivity for p>2 is asserted. The external map
comparison, unrestricted Lemma 27.2 and G.2 norm qualifications remain;
the dissertation is incomplete.

Validation is recorded in [the implementation status](STATUS.md).
