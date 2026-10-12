# Section 4: Dirichlet and Neumann spectra

This is a statement-by-statement audit against the original spaces and
physical expressions on printed pages 28 onward. Existing later results do
not by themselves certify this section or the full dissertation complete.

## Equations (1.6)–(1.7) and the AKNS coordinates (pages 28–29)

All coordinates and potentials may be complex. The original scalar H¹
condition is absolute continuity on [0,1] and square integrability of the
actual derivative. Domain vectors are actual closed-interval functions.
The physical L² and H¹ norms use the sum of the component energies.

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Normalized T and inverse | `aknsCoordinateEquiv`, `zsToAKNS_aknsToZS`, `aknsToZS_zsToAKNS` | Exact normalized vector coordinates, arbitrary complex pairs. |
| Both endpoint conditions in (1.6) | `aknsToZS_dirichlet_iff`, `aknsToZS_neumann_iff` | Equal ZS components iff second AKNS component vanishes; opposite iff first vanishes. |
| Original H¹ domain correspondence | `hasClassicalIntervalDomain_aknsToZS_iff`, `hasAKNSIntervalDomain_zsToAKNS_iff` | Both directions, both boundaries; no assumed periodicity or external regularity. |
| Actual closed-interval AKNS domain | `AKNSIntervalDomain`, `mem_aknsIntervalSubmodule_iff` | Membership is exactly representability by original H¹ data with the specified endpoints. |
| Physical L² unitary | `aknsL2Equiv` | Linear isometric equivalence of the original component-sum Lebesgue spaces, with a.e. pointwise realization. |
| Exact physical H¹ norm | `classicalIntervalNorm_aknsToZS`, `norm_aknsDomainOfFunction`, `aknsDomainEquiv` | Full value and derivative energies, including arbitrary original-domain representatives. |
| Original AKNS inclusion | `aknsInclusion`, `aknsInclusion_injective`, `aknsInclusion_denseRange`, `aknsInclusion_realization` | Injective dense inclusion giving the original function's actual L² class. |
| Original AKNS operator | `aknsIntervalOperator`, `aknsIntervalOperator_realization` | Bounded domain-to-L² map at arbitrary L² potentials; actual differential expression a.e. |
| Unitary conjugation | `aknsL2Equiv_inclusion`, `aknsL2Equiv_operator` | Exact identities for the actual inclusion and operator with their domain isometry. |
| Actual derivative intertwining | `deriv_aknsToZS`, `physicalOperator_aknsToZS` | Pointwise at differentiable points and a.e. on arbitrary original interval H¹ data. |
| Physical eigenvalue equations | `akns_eigenEquation_iff` | Equivalent a.e. equations under the domain correspondence, for both boundaries. |
| Component system (1.7) | `aknsAction_eigen_iff` | Exact signs and coefficients in both equations. |
| Correct potential transformation | `aknsPotential_eq_sqrt_two_smul`, `aknsAction_intertwining` | The potential map is (q+i*p,q-i*p), agreeing with printed page 19. |
| Page 29 normalization failure | `aknsAction_printed_normalization_false`, `physicalOperator_printed_akns_normalization_false` | Exact constant-data counterexamples to using normalized T on potentials as printed. |

These public entry points are in `NLS.ZakharovShabat`; Sobolev linear closure
is in `NLS.Fourier.HasIntervalH1Regularity.linearCombination`. The five new
modules are `IntervalH1Linear`, `AKNSCoordinates`, `AKNSClassicalDomain`,
`AKNSPhysicalNorms`, and `AKNSIntervalOperator`. The public examples cover
both boundary conditions, norm identities, domain membership, density,
actual inclusions/operator realizations, and the normalization counterexample.

The normalization discrepancy and its correction are recorded in
[SOURCE_ERRATA.md](../SOURCE_ERRATA.md). This audit concerns the classical
L² setting. It does not extend the interval regularity definition to all
Fourier–Lebesgue exponents; the source's later extension has 1<p<infinity.

## Reflection formulas and Lemma 4.1 (pages 28–29)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Even/odd eigenfunction extensions | `aknsIntervalExtension` | Dirichlet is even/odd; Neumann is odd/even. |
| Signed-swap coordinate formulas | `aknsToZS_intervalExtension`, `akns_intervalExtension_zsToAKNS` | Exact pointwise formulas for arbitrary original functions. |
| Common potential extension | `aknsPotential_intervalExtension`, `memLp_aknsPotentialExtension` | q even, p odd; actual Dirichlet potential extension in either boundary problem; arbitrary L² input. |
| Actual periodic H¹ AKNS representatives | `aknsCircleExtension`, `aknsCircleExtension_regular`, `aknsCircleExtension_reconstruct` | Circle functions recover the full closed-period piecewise extension, including both endpoints. |
| Extended AKNS equation | `akns_interval_equation_transfer` | Actual derivatives and a.e. equations for either original endpoint domain. |
| Both parts of Lemma 4.1 | `sourceLemma4_1` | Actual periodic H¹ circle representative, exact extension, and physical equation with the Dirichlet-reflected potential. |
| Original source potential | `sourceDirichletPotentialCoefficients`, `sourceDirichletPotentialCoefficients_coefficients`, `sourceDirichletPotentialCoefficients_reconstruct` | Exact normalized physical Fourier integrals in `CoeffPair 2`, with a.e. reconstruction. |
| Original weighted source domain | `sourceClassicalIntervalExtension`, `sourceClassicalIntervalExtension_coefficients` | Original component-sum weighted space, exact physical Fourier coefficients. |
| Actual source circle representative | `sourceClassicalCircleExtension`, `sourceClassicalCircleExtension_regular`, `sourceClassicalCircleExtension_reconstruct`, `sourceClassicalCircleExtension_restrict` | Periodic H¹ regularity, closed-period reconstruction, and exact original closed-interval values. |
| Actual original-norm operator equation | `source_classical_interval_equation_transfer` | The actual `sourceOperator` and `sourceDomainInclusion`, for arbitrary original L² potentials. |
| Nonzero source eigenvector | `sourceClassicalIntervalExtension_ne_zero`, `source_classical_interval_eigenvector_transfer` | Nonzero original interval functions remain nonzero in the actual source domain. |
| Boundary eigenvalues are periodic | `source_classical_interval_eigenvalue_mem_spectrum` | Membership in the complement of the actual original source resolvent set. |
| Exhaustion paragraph after the lemma | `source_periodicSpectrum_eq_classicalEigenvalues_union` | The source spectrum equals the union of the two original physical interval eigenvalue sets. |

The new entries are in `NLS.ZakharovShabat`, in `AKNSReflection.lean` and
`SourceLemma4_1.lean`. They reuse the proved physical reflection and
classical Fourier extension infrastructure while identifying the original
source spaces explicitly. No isometry of maximum and component-sum norms
is asserted. The physical equation transfer needs only its stated domain
and a.e. equation; Fourier and spectral conclusions require original L²
potentials. The spectrum-union theorem is a set identity, with no new
multiplicity assertion. The AKNS potential-normalization correction is
retained; the reflection signs and Lemma 4.1 need no further correction.

Public examples exercise both boundary conditions, endpoint reconstruction,
negative Fourier indices, the physical equation, nonzero original source
eigenvectors, and full spectral exhaustion.

## Fourier representations (1.8)–(1.9) (page 30)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original-norm reflected Fourier data | `sourceIntervalExtensionCoefficients` | Actual normalized physical integrals for arbitrary original L² data, with either boundary sign. |
| Both coefficient formulas | `sourceIntervalExtensionCoefficients_snd`, `sourceIntervalExtensionCoefficients_fst` | Printed half-interval amplitudes, first-frequency reversal, and boundary sign. |
| Assembly from scalar amplitudes | `sourceBoundaryAssembly`, `sourceIntervalExtensionCoefficients_eq_assembly` | Exact reconstruction of the original component-sum coefficient pair. |
| Original boundary modes | `sourceBoundaryMode`, `sourceBoundaryMode_eq` | The original-norm signed free modes. |
| Physical mode identification | `physicalBoundaryMode`, `sourceBoundaryMode_physical` | Actual waves (epsilon*exp(-i*pi*n*x), exp(i*pi*n*x)), as physical L² representatives. |
| Original coefficient series | `hasSum_sourceIntervalExtensionCoefficients` | Unconditional norm convergence in `CoeffPair 2`. |
| Original physical pair space and Fourier inverse | `SourceCirclePairL2`, `sourceCircleSynthesis` | Actual component-sum L² space on the period-two circle, with normalized Haar measure; linear isometric Fourier equivalence. |
| Physical L² convergence | `hasSum_intervalExtension_L2` | Convergence of the same boundary-mode series in the physical L² norm. |
| Actual reflected-function sum | `sourceCircleSynthesis_intervalExtension` | The physical representative of the sum equals the signed reflection a.e. on [0,2]. |
| Literal physical pairing | `intervalBoundaryPairing_eq_integral` | Integral of f times the componentwise conjugate boundary mode on [0,1]. |
| Printed half coefficient | `intervalAmplitude_eq_half_pairing` | Exactly one half of the physical pairing, at every integer index. |
| Full arbitrary-L² series | `sourceEquation1_8_1_9_L2` | The printed half-pairing series for either boundary condition, with no endpoint matching. |
| Exact original norm | `norm_sourceIntervalExtensionCoefficients` | Normalized doubled-period energy equals original interval energy. |
| Printed H¹-input package | `sourceEquation1_8_1_9` | Actual reflected L² sum, convergent half-pairing series, and exact physical energy for arbitrary original interval H¹ pairs. |

All entries are in `NLS.ZakharovShabat`, in `SourceBoundaryFourier.lean`.
The full page 30 H¹-input hypotheses are retained: no boundary-domain
condition is added. The result is strengthened to L² input where possible.
A reflected function may have jumps, so this milestone asserts neither
uniform nor H¹ convergence for arbitrary input. The separate periodic-H¹
extension results require the endpoint conditions stated in Lemma 4.1.
The physical period-two norm uses normalized Haar measure; the interval
energy uses ordinary Lebesgue measure. Their exact equality after signed
reflection is proved. No correction to the printed series is needed.

Public checks cover both boundary signs, negative indices, the full
H¹-input package, original and physical norm identities, literal pairing,
coefficient convergence, and reconstruction of both the basis and sum.

## Closed boundary spaces and Lemma 4.2 (pages 30–31)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original finite-exponent boundary spaces | `sourceWeightedBoundarySubspace` | Raw scalar Fourier coordinates with the original component-sum norm. |
| Original infinity boundary spaces | `sourceWeightedBoundarySubspaceInfty` | Signed source coefficients and the actual frequencywise sum supremum norm. |
| Closedness | `isClosed_sourceWeightedBoundarySubspace`, `isClosed_sourceWeightedBoundarySubspaceInfty` | Every real Sobolev order and Banach exponent, with the separate source endpoint norm. |
| Algebraic direct sum | `isCompl_sourceWeightedBoundarySubspaces`, `isCompl_sourceWeightedBoundarySubspacesInfty` | Zero intersection and sum equal to the full ambient space. |
| Topological direct sum | `isTopCompl_sourceWeightedBoundarySubspaces`, `isTopCompl_sourceWeightedBoundarySubspacesInfty` | Continuous complementary decomposition in the original topologies. |
| Exact coordinate conditions | `mem_sourceWeightedBoundarySubspace`, `mem_sourceWeightedBoundarySubspaceInfty` | Scalar frequency reversal versus signed same-index boundary sign. |
| Amplitude parametrizations | `sourceWeightedBoundaryAmplitudeEquiv`, `sourceWeightedBoundaryAmplitudeEquivInfty` | Continuous linear equivalences, hence unique amplitudes for every boundary element. |
| Exact amplitude norms | `norm_sourceWeightedBoundaryAmplitudeEquiv`, `norm_sourceWeightedBoundaryAmplitudeEquivInfty` | Factors 2^(1/p) for finite p and 2 for the actual source infinity norm. |
| Original-norm boundary series | `hasSum_sourceWeightedBoundaryModes` | Unconditional norm convergence for finite p. |
| Actual distributional boundary series | `hasSum_sourceBoundaryDistribution` | Every Banach exponent, including infinity, and every real Sobolev order. |
| Series sum identification | `sourceBoundaryDistribution_eq_sourcePair`, `sourceBoundaryDistribution_eq_sourcePairInfty` | Actual distributional synthesis of the original coefficient pair. |
| Mode identification | `sourceBoundaryDistribution_single`, `sourceBoundaryDistributionMode_physical` | Weighted raw single modes become the actual signed exponential waves under synthesis. |
| Lemma 4.2 | `sourceClassicalBoundaryEquiv` | Continuous linear equivalence of the original physical H¹ domain and original weighted (1,2) boundary space. |
| Forward extension | `sourceClassicalBoundaryEquiv_ofFunction` | Actual signed-extension Fourier coefficients of every classical input. |
| Inverse restriction | `sourceClassicalBoundaryEquiv_symm_apply` | Physical restriction at every point in the closed interval [0,1]. |

All entries are in `NLS.ZakharovShabat`, in `SourceBoundarySpaces.lean`
and `SourceBoundarySeries.lean`. The infinity assertions use the separate
`WeightedCoeffPairInfty` space, not the maximum norm on `CoeffPair ⊤`.
The finite-exponent original space is expressed in scalar Fourier
coordinates; the infinity space is expressed in signed source coordinates.
The conversion between these conventions is explicit. The series at
infinity is distributionally convergent; norm convergence is not claimed.
No correction to the source direct sum or Lemma 4.2 is needed.

Public checks include both boundary signs, the finite endpoint p=1, the
coupled infinity norm, negative/fractional regularity, negative indices,
actual physical wave integrals, and forward/inverse classical maps.

## Lemma 4.3 (page 31)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original-norm extension map | `sourceIntervalExtensionToBoundary` | Original period-one `CoeffPair p` to the original weighted order-zero boundary space, 1<p<infinity. |
| Exact amplitude norm | `norm_sourceIntervalExtensionToBoundary` | Output norm equals 2^(1/p) times amplitude norm. |
| Required FLᵖ bound | `norm_sourceIntervalExtensionToBoundary_le`, `sourceLemma4_3` | One positive constant `intervalExtensionBound` works for both boundary signs; component factors cancel. |
| Analyticity | `analyticAt_sourceIntervalExtensionToBoundary` | Complex analytic at every original input. |
| Physical finite-input coefficients | `sourceIntervalExtensionToBoundary_finite_integrals` | Both normalized Fourier integrals of the actual signed reflection. |
| Uniqueness of completion | `sourceIntervalExtensionToBoundary_unique` | The continuous map is determined by all finite physical inputs. |
| Norm limit of finite extensions | `tendsto_sourceIntervalExtension_truncate` | Actual original-norm convergence at every 1<p<infinity. |
| Actual distributional extension | `sourceIntervalExtensionDistributionCLM`, `tendsto_sourceIntervalExtensionDistribution_truncate` | Periodic tempered-distribution pairs and convergence of finite-input extensions. |
| Distributional coefficients and period | `sourceIntervalExtensionDistribution_coefficients`, `sourceIntervalExtensionDistribution_periodic` | Every raw coefficient and period two in both components. |
| Corrected even/odd formulas | `sourceIntervalAmplitudeCLM_even`, `sourceIntervalAmplitudeCLM_odd` | All original inputs; exact half and normalized shifted-Hilbert map. |
| Literal signed formulas | `sourceLemma4_3_even_signed`, `sourceLemma4_3_odd_signed` | Finite signed inputs: even factor 1/2, odd kernel i/pi, both boundary signs. |
| Printed-constant failures | `sourceLemma4_3_printed_even_counterexample`, `sourceLemma4_3_printed_odd_counterexample` | Actual constant interval inputs refute the printed even and odd constants. |
| Exact Hilbert norm | `norm_sourceIntervalExtensionToBoundary_two`, `norm_sourceIntervalExtensionL2` | Original component-sum norm is preserved. |
| Actual L² half-interval map | `halfIntervalCoeffs_two_ofFunction` | Arbitrary physical L² scalar input, no endpoint matching. |
| Actual L² pair coefficients | `sourceIntervalExtensionL2_ofFunction` | Completed operator equals actual signed-reflection Fourier coefficients. |
| Physical L² reconstruction | `sourceLemma4_3_L2_physical` | Its physical Fourier synthesis is the reflected function a.e. on [0,2]. |
| Original input normalization | `norm_sourceUnitIntervalL2Coefficients` | Unit-period coefficient norm equals ordinary physical interval L² norm. |

The main entries are in `NLS.ZakharovShabat`, in `SourceLemma4_3.lean`
and `SourceLemma4_3Physical.lean`. The scalar L² bridge is in
`NLS.Fourier.HalfIntervalL2Identification`. It uses Parseval and density
to identify a bounded Hilbert functional with each actual half coefficient.
No pointwise function is assumed for an arbitrary rough input. The general
map is a unique bounded completion with actual distributional synthesis;
for every physical L² input the actual reflection is identified as well.

The printed proof needs the normalization corrections recorded in
`SOURCE_ERRATA.md`: its even formula drops 1/2 and its odd kernel has 2i
instead of i/pi. Its reference to FL¹ input norm is not the FLᵖ estimate
needed for the theorem. The boundedness/analyticity statement is proved in
the required original FLᵖ norms. No extension to p=1 or p=infinity is claimed.
The separate all-exponent height problem in Theorem 1.4 remains unchanged.

Public checks include arbitrary L² representatives, negative frequencies,
exact Hilbert norms, a concrete exponent above two, all-p analytic bounds,
rough distributional limits, signed formulas, and both counterexamples.

## Lemma 4.4 and restricted spectra (page 32)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original base boundary space | `sourceBoundaryBaseSubspace`, `isClosed_sourceBoundaryBaseSubspace` | Closed subspace with the original component-sum norm. |
| Zero-weight identification | `sourceBoundaryZeroWeightEquiv`, `sourceBoundaryZeroWeightEquiv_mem` | Isometry retaining all raw coefficients and the boundary condition. |
| The common reflected potential | `sourceReflectedPotential`, `toMax_sourceReflectedPotential` | Actual completed Dirichlet extension from Lemma 4.3 for both restrictions. |
| Boundary invariance | `sourceLemma4_4` | Original interval input, 1<p<infinity. |
| Actual bounded restrictions | `sourceBoundaryOperator`, `norm_sourceBoundaryOperator_le` | Original one-derivative domain to original base; finite p including 1 for already-reflected potentials. |
| Free mode action | `sourceBoundaryDomainMode_free` | Eigenvalue pi*n for either boundary sign. |
| Potential mode action | `sourceBoundaryDomainMode_potential_series` | Original-norm HasSum, sign epsilon and output index k-n. |
| Physical Hilbert modes | `sourceBoundaryBaseMode_two`, `sourceBoundaryDomainMode_inclusion_two` | Agreement with the previously reconstructed physical waves. |
| Actual restricted pencil | `sourceBoundaryPencil_eq` | z times inclusion minus the actual restricted operator. |
| Full resolvent and spectrum | `sourceBoundaryResolventSet_eq`, `sourceBoundarySpectrum_eq` | Bijectivity is unchanged by the continuous base/domain equivalences. |
| Periodic spectral splitting | `sourcePeriodicSpectrum_eq_sourceBoundary_union` | Original periodic spectrum equals the union of the two restrictions. |
| Closedness and discreteness | `isClosed_sourceBoundarySpectrum`, `discreteTopology_sourceBoundarySpectrum`, `finite_sourceBoundarySpectrum_inter` | Each restriction has finitely many spectral points in bounded regions. |
| Interval-input spectrum | `sourceBoundarySpectrum_reflected`, `mem_sourceBoundarySpectrum_reflected_iff` | The canonical source labels exhaust the actual original-norm restriction. |

The main entries are in `NLS.ZakharovShabat.SourceLemma4_4` and
`NLS.ZakharovShabat.SourceBoundarySpectra`. The sufficient boundedness
constant is 2^(1/p)*(pi+Kp*norm(phi)), where Kp is the existing Sobolev
embedding constant and phi is the already-reflected potential. The
interval extension itself still requires 1<p<infinity. No endpoint
extension or original infinity-norm assertion is added.

The printed mode formulas need no correction. Public examples check both
signs explicitly, negative mode indices, a concrete exponent above two,
p=1 for already-reflected potentials, physical p=2 mode identification,
the actual pencil, spectral splitting, discreteness, and canonical labels.

## Theorem 1.4 proof: original Riesz restrictions and counts (page 32)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Boundary compression in original norms | `sourceBoundaryProjection`, `sourceBoundaryCompression` | Bounded maps in the original component-sum norms. |
| Actual circle and rectangle restrictions | `sourceBoundaryCircleProjection_apply`, `sourceBoundaryCentralProjection_apply` | Equal the original normalized integrals on boundary inputs. |
| Finite-rank idempotents | `sourceBoundaryCircleProjection_properties`, `sourceBoundaryCentralProjection_properties` | Admissible circle/rectangle boundaries. |
| Restricted range identification | `sourceBoundaryCompressionRangeEquiv` | Isometry to the boundary part of the ambient range; auxiliary norm transfer is only a continuous equivalence. |
| Original operator-domain recursion | `sourceBoundaryRootSpace_zero`, `sourceBoundaryRootSpace_succ` | Every finite Jordan chain uses the actual boundary inclusion and pencil. |
| Full root space | `mem_sourceBoundaryRootSpaceTop`, `finiteDimensional_sourceBoundaryRootSpaceTop`, `exists_sourceBoundaryRootSpace_eq_top` | All finite chains, finite dimension, and stabilization. |
| Original algebraic multiplicity | `sourceBoundaryAlgebraicMultiplicity`, `sourceBoundaryAlgebraicMultiplicity_eq` | Dimension of the full original root space, identified with coefficient multiplicity. |
| Domain-valued contour ranges | `sourceBoundaryCircleProjection_exists_domain`, `sourceBoundaryCentralProjection_exists_domain` | Every projected vector has an original one-derivative boundary-domain representative. |
| Printed domain restrictions | `range_sourceBoundaryCircleProjection_comp_inclusion`, `range_sourceBoundaryCentralProjection_comp_inclusion` | Restricting input to the original weighted domain retains the entire projected range. |
| Rank equals original multiplicity sum | `sourceBoundaryCircleProjection_rank_eq_sum`, `sourceBoundaryCentralProjection_rank_eq_sum` | Actual finite spectral sets, retaining Jordan multiplicities. |
| Common analytic neighborhood | `exists_uniform_sourceBoundaryCountingData` | Open, convex, connected, contains input and zero; both signs and every larger cutoff. |
| Central and disk ranks | `SourceBoundaryCountingData.central_rank`, `.disk_rank`, `.central_domain_rank`, `.disk_domain_rank` | 2N+1 and one, for base and displayed weighted-domain restrictions. |
| Central and disk counts | `SourceBoundaryCountingData.central_multiplicity`, `.disk_multiplicity` | Full original algebraic counts 2N+1 and one. |
| Unique simple high eigenvalue | `SourceBoundaryCountingData.disk_unique_simple` | Exactly one spectral point of original algebraic multiplicity one in each high disk. |
| Exhaustive localization | `SourceBoundaryCountingData.spectrum_subset` | No boundary spectrum outside the same central box and high disks. |

The four new modules are `SourceBoundaryRootSpaces`, `SourceBoundaryContours`,
`SourceBoundaryContourDomains`, and `SourceBoundaryCounting` in
`NLS.ZakharovShabat`. The interval-input theorem requires 1<p<infinity;
root chains and restrictions for already-reflected potentials also cover
p=1. The source infinity norm is not identified with a maximum norm.

The actual chain recursion establishes that transported dimensions are
multiplicities of the original operator. The projected range is contained
in its weighted domain, resolving the domain notation in the displayed
projectors. Counts include the zero potential in the common neighborhood.
The positive cutoff excludes the degenerate central rectangle.

This establishes the proof's counting argument using the existing
height-N central boxes. The independently refuted all-exponent printed
norm-dependent height remains refuted; no replacement bound is adopted.
Public examples cover arbitrary finite p>1, p=1 for reflected root spaces,
a concrete p>2, both boundary signs, negative high indices, domain-range
identification, Jordan recursion, algebraic sums, analytic neighborhoods,
finite-rank projections, simple eigenvalues, and exhaustive localization.

## Next source assertions

Audit Lemma 4.5 (page 33): identify the trace of the actual original
restricted operator on the rank-one Riesz range with the simple boundary
eigenvalue, and obtain analyticity in the original interval-input norm.
