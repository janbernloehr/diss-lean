# Appendix A: periodic distributions and Fourier Lebesgue spaces

## Ordered source comparison

The [ordered Appendix A comparison](APPENDIX_A_ASSERTIONS.md)
covers 32 groups on pp.121–124: 27 matched, four corrected and one
contextual. No partial or pending groups remain in this local ledger.

Original distributions, physical Lp quotients, positive periods and
the exact 1/L normalization are retained. The source assertions in
A.3, A.5 and A.6 keep their actual witnesses and quantifiers.

Direct corrections retain the weighted-c0 condition at infinity,
the physical chirp rescaling, the Holder product factor C_p <= 2p
and the original Section 2 weight. No new Lean proof or refutation
is added in this comparison.

The unchanged Lean snapshot reuses the successful full check recorded at commit cec78d328ace97d075ff5832a67c11eb4da30118: 8,582 build jobs, 7,692 public examples and an axiom audit of 44,706 NLS declarations, with 21 inherited warnings and zero new. All 104 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix B. The four Section 28 complex intermediate passages
and the [broader completion qualifications](COMPLETENESS.md)
remain qualified; the local counts do not certify the dissertation.

Earlier entries retain their original implementation and validation scope.

This audit covers the test-space foundations, finite-order criterion (A.1),
order-zero continuous extension, complex Radon representation (A.2), and L1
action on printed page 121, plus both parts of Theorem A.1 and the distributional
derivative on printed page 122. It also covers the original Fourier–Lebesgue
spaces, convergence and L2/L1 statements on page 122, and the absolute Fourier
synthesis and pseudomeasure-dual statements on page 123, plus both assertions
in Remark A.6, the actual L1-to-c0 Fourier map, and the full embeddings
of Lemmas A.2 and A.4 and the counterexamples A.3 and A.5 on page 123.
On page 124, A.7 and the embedding in A.8 are proved; the false constant-one
estimate (A.4) is replaced by a quantified bound and a polynomial counterexample.
A.9's full exponent ranges and the subcritical interval/periodic Sobolev
identification are now realized on the original distribution spaces.
The test space
contains the actual smooth complex-valued functions with the stated
positive physical period. It is not defined as a coefficient-sequence space.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Lemma A.9, full original-space membership | `ofL1_mem_fourierLebesgue_of_intervalSobolev`, `ofL1_mem_fourierLebesgue_of_intervalHalfSobolev` | 0≤s<1/2 and finite q>1/(s+1/2); separately s=1/2 and finite q>1. Original arbitrary interval input, no endpoint matching, and no fractional assumption at zero. |
| A.9 zero and infinity cases | `PeriodicFourierLebesgue.ofIntervalL2`, `norm_ofIntervalL2_le`, `l2OriginalEmbedding` | Ordinary interval L2 to every q≥2, including infinity; exact physical L^(-1/2) bound. This also supplies the infinity target for positive and half regularity. |
| A.9 continuous linear injections | `IntrinsicIntervalSobolev.originalFourierEmbedding`, `originalHalfFourierEmbedding`, `originalL2TargetEmbedding` | Injective maps on actual intrinsic interval classes, original smooth-test action and explicit physical norm bounds. |
| A.9 interval/periodic Sobolev identification | `IntrinsicIntervalSobolev.originalSobolevEquiv`, `originalSobolevEquiv_symm_represents` | Continuous linear equivalence for 0<s<1/2; both inverse identities, actual interval representatives, and bounds in both directions using the exact Section 2 weight. |
| Lemma A.7, original product | `PeriodicFourierLebesgue.youngProduct`, `youngProduct_unique`, `norm_youngProductCLM` | All positive periods and Banach Young triples; absolutely convergent coefficients, unique original distribution, sharp bilinear norm one. |
| Product compatibility | `youngProduct_eq_of_val_eq`, `tendsto_youngProduct_truncate`, `youngProduct_eq_ofContinuous` | Exponent independence; finite-input truncation limits even with infinity output; actual pointwise multiplication when one continuous factor is in FL1. |
| Original Wiener Banach algebra | `instWienerNormedCommRing`, `instWienerNormedAlgebra`, `wienerContinuousAlgHom` | Complete original FL1, norm-one unit, injective algebra map to C(T_L). |
| Lemma A.8, embedding | `sobolevToWiener`, `sobolevToWiener_val`, `sobolevToWiener_continuous_represents` | All finite Banach p; continuous linear injection preserving the original distribution and supplying an actual continuous representative. |
| Corrected (A.4) | `norm_sobolevProduct_le`, `norm_sobolevToWiener_le_two_mul` | Required inverse-weight Hölder constant C_p ≤ 2p; exact Section 2 weight (1+|n|), without silently rescaling it. |
| Printed (A.4) counterexample | `a8OriginalProduct_eq_ofContinuous`, `a8Original_constant_one_fails` | Finite physical polynomials, squared norms 8, 5 and 41. Works on all original positive-period spaces and on the proof's rescaled weight at period two. |
| Smooth periodic test space and its derivative-norm topology | `SmoothPeriodicTest`, `SmoothPeriodicTest.cNorm_apply` | Every positive period L; the seminorm at N is exactly the sum of the sup norms of physical derivatives of orders 0 through N. |
| Fréchet test space | `derivativeJetEquiv` and the completeness, metrizability, Hausdorff, and local convexity instances | A closed derivative-jet subspace of a countable product of Banach spaces, with the original topology. |
| Density in C(T_L) | `denseRange_toContinuousCLM` | Dense range on the actual physical circle, with the exact uniform norm `norm_toContinuousCLM`. |
| Least order zero iff unique continuous extension | `Distribution.order_zero_iff_physical_extension` | Unique complex continuous linear functional on C(AddCircle L, ℂ), for every positive L. |
| Original Fourier–Lebesgue spaces | `PeriodicFourierLebesgue`, `FourierLebesgueSpace`, `coefficientsIsometry` | Actual original-distribution subtype with exact weighted coefficient norm; all positive periods and all real Sobolev orders. |
| Completeness and reflexivity | `completeSpace`, Sobolev completeness instances, `bidual_surjective` | Complete for every Banach exponent; canonical double-dual map surjective for 1 < p < infinity. |
| Actual Fourier-series convergence | `truncate_eq_ofContinuous`, `tendsto_truncate`, `tendsto_truncate_action` | Continuous physical trigonometric polynomials; norm convergence for finite p and convergence on every original smooth test for all p. |
| Qualified infinity endpoint | `tendsto_truncate_top_iff`, `inverseWeightDistribution_one`, `norm_inverseWeightDistribution_sub_truncate` | Norm convergence iff weighted c0. At unit weight, point evaluation at zero has norm and every truncation error equal to one. |
| FL2 = L2 and Parseval | `l2Isometry`, `l2Isometry_represents`, `l2Isometry_parseval_interval` | Actual L2 quotient of the physical circle with normalized Haar measure; exact original action and 1/L interval square norm. |
| Normalized L1 bound | `ofIntervalL1`, `norm_ofIntervalL1_le` | Every interval-integrable function produces an original FL-infinity distribution with norm at most the exact normalized L1 norm. |
| Absolute and uniform Fourier synthesis | `continuousRepresentativeCLM`, `existsUnique_continuousRepresentative`, `hasSum_continuousRepresentative` | Unique uniformly continuous representative, absolute convergence in C(T_L), uniform convergence, physical frequencies 2πn/L, sup-norm bound one. |
| Pseudomeasures and duality | `unweightedDualIsometry`, `pseudomeasureDualIsometry` | Full continuous dual for finite p, including FL-infinity as the dual of FL1; opposite indices in the bilinear pairing and exact operator norm. |
| Riemann–Lebesgue decay, first part of A.6 | `tendsto_intervalFourierCoefficient_cofinite`, `tendsto_fourierCoeff_cofinite` | Every positive period; normalized interval and physical-circle coefficients vanish along the cofinite filter on integer frequencies. |
| L1 Fourier-series convergence in FL-infinity | `tendsto_truncate_ofIntervalL1`, `Distribution.evaluation_zero_not_ofL1` | Original FL-infinity norm convergence for interval L1 data; point evaluation at zero has no interval L1 representative. |
| Actual Fourier map L1 → c0 | `circleL1Fourier`, `norm_circleL1Fourier`, `denseRange_circleL1Fourier` | Complex continuous linear map from the actual L1 quotient, sharp operator norm one, injectivity, and dense range; non-surjectivity is proved below. |
| Non-surjectivity, second part of A.6 | `circleL1Fourier_not_surjective`, `not_isClosed_range_circleL1Fourier`, `exists_vanishing_not_fourierCoeff` | Actual L1 quotient to c0; every positive period; proper dense nonclosed range and a decaying sequence with no integrable preimage. |
| Original-space obstruction in A.6 | `PeriodicFourierLebesgue.exists_norm_convergent_not_ofCircleL1` | Norm-convergent Fourier truncations of an original FL-infinity distribution do not imply existence of an L1 representative. |
| Sharp finite interpolation prerequisites | `Coeff.norm_kernelPair_interpolate_sharp`, `sum_norm_sq_dft`, `norm_dft_piLp_two` | Geometric three-lines constant for arbitrary finite inputs; exact discrete Parseval and sqrt(N) Hilbert norm factor. Extended to the full A.2/A.4 embeddings below. |
| Lemma A.2, Lᵖ → FLᑫ | `PeriodicFourierLebesgue.ofLp`, `ofLp_injective`, `norm_ofLp_le` | Every conjugate pair with 1 ≤ p ≤ 2, including p=1, q=infinity; complex continuous linear injection of the actual Lᵖ quotient into original distributions, norm bound one and exact 1/L action. The source names the output exponent p. |
| Lemma A.4, FLᵖ → Lᑫ | `lpRepresentative`, `lpRepresentative_injective`, `norm_lpRepresentative_le` | Full inclusive range 1 ≤ p ≤ 2; unique actual Lᑫ representative, constant-one norm bound, original smooth-test action, and both endpoint identifications. |
| Lemma A.3, non-measure distribution | `exists_fourierLebesgue_above_two_not_measure` | One original distribution lies in every FLp with p > 2, including infinity, but is not represented by any actual complex measure on the physical circle. |
| Lemma A.5, continuous counterexample | `exists_continuous_not_fourierLebesgue_below_two` | One continuous physical-circle function lies outside every original FLp with 1 ≤ p < 2. Same witness for all exponents; alternative construction to the printed series. |
| Uniqueness of integrable representatives | `Distribution.ofCircleL1_eq_iff`, `ofCircleLp_injective`, `circleLp_fourierCoeff_injective` | Equality of original distributions iff a.e. equality for integrable functions; all Fourier coefficients determine every Banach Lᵖ equivalence class. |
| Complex Radon representation, (A.2) | `Distribution.existsUnique_normalized_measure`, `order_zero_iff_measure` | Unique actual complex measure on the physical circle, with 1/L times the standard complex integral; holds on all continuous functions and all original smooth tests. |
| Converse and identification with measures | `Distribution.ofComplexMeasure_order`, `complexMeasureOrderZeroEquiv` | Every complex Borel measure gives least order zero; both directions of the equivalence recover the original object. |
| Finiteness and Radon regularity | `complexMeasure_finite_variation`, `complexMeasure_variation_regular` | Every complex measure has finite total variation. Its variation on the compact metrizable physical circle is regular, hence inner regular. |
| Point-mass and total-mass normalization | `Distribution.ofComplexMeasure_dirac`, `ofComplexMeasure_zero_coefficient` | A mass Lz at x gives z times point evaluation; the zeroth coefficient is total mass divided by L. |
| L1 action following (A.2) | `Distribution.ofL1_apply`, `ofL1_order`, `ofL1_coefficient`, `toTempered_ofL1` | Only interval integrability is required; retains 1/L, original tests, all Fourier coefficients, and actual tempered realization. |
| Distributional derivative | `Distribution.derivative_apply`, `derivative_coefficient`, `derivative_order_le`, `toTempered_derivative` | Negative test derivative, exact signed multiplier i·2πn/L, order at most N+1, physical realization compatibility. |
| Continuity iff a finite-order estimate, (A.1) | `SmoothPeriodicTest.continuous_iff_finite_order` | Every complex-linear functional on the original test space; one N and one strictly positive constant before all tests. |
| Least distribution order | `Distribution.order`, `hasOrderAtMost_order`, `order_le` | The least admissible natural number, including order zero. |
| Theorem A.1(i) | `Distribution.coefficients_isBigO_of_order`, `coefficients_isBigO` | The prescribed order N gives the same polynomial degree N; the least-order version follows. The cofinite filter on integer frequencies expresses the two-sided asymptotic as absolute frequency tends to infinity. |
| Theorem A.1(ii) | `Distribution.existsUnique_of_polynomial_isBigO` | Every polynomially growing complex sequence yields exactly one continuous functional on all original smooth tests, at every positive period. |
| Full coefficient characterization | `Distribution.polynomial_growth_iff_existsUnique` | Polynomial growth iff unique realization on the original test space. |
| Actual tempered-distribution realization | `Distribution.periodicTemperedEquiv` | Both directions recover the original object and preserve every normalized Fourier coefficient. |
| Polynomial synthesis in the existing realization | `existsUnique_periodicDistribution_of_polynomial_bound`, `existsUnique_periodicDistribution_of_polynomial_isBigO` | Unique actual periodic tempered distribution, including arbitrary zero-mode values and degree-zero bounds. |
| Physical Fourier normalization | `mode_apply_physical`, `norm_derivative_mode_physical` | The test is exp(i·2πnx/L); the kth derivative sup norm is (2π|n|/L)^k. |
| Nonzero order-zero example | `Distribution.evaluation_order`, `evaluation_zero_coefficient` | Point evaluation has least order zero; evaluation at zero has every Fourier coefficient equal to one. |

The names beginning with `Distribution` above are in the namespace
`NLS.Fourier.SmoothPeriodicTest`; the other test-space results are in
`NLS.Fourier.SmoothPeriodicTest` unless otherwise indicated by their file.

## Original test topology and finite order

[`SmoothPeriodicTestSpace.lean`](../NLS/Fourier/SmoothPeriodicTestSpace.lean)
defines the original smooth periodic functions as a complex vector space.
Every physical derivative is a bounded continuous function on the real
line, using smoothness and periodicity. Its genuine sup norm enters the
finite sum defining the source's C^N norm.

The topology is generated by precisely those sums. A continuous functional
is bounded by finitely many generating seminorms; their monotonicity gives
a single derivative order N. Conversely, any such bound implies continuity.
Multiplication by a fixed Schwartz window is continuous for this topology,
with a proved finite Leibniz bound for every Schwartz seminorm.

[`SmoothPeriodicTestFrechet.lean`](../NLS/Fourier/SmoothPeriodicTestFrechet.lean)
identifies the same space with the closed set of compatible derivative jets
in a countable product of bounded-continuous-function Banach spaces. Uniform
convergence of each derivative preserves the derivative identities and period.
Conversely, each compatible jet comes from an original smooth periodic test.
The equivalence preserves the original seminorm topology. The resulting
completeness, metrizability, Hausdorff, and local convexity instances prove
the source's Fréchet assertion without assuming completeness of Schwartz space.

## Density, order-zero extension, and L1 action

[`PeriodicDistributionOrderZero.lean`](../NLS/Fourier/PeriodicDistributionOrderZero.lean)
first represents smooth periodic functions on the period-two circle. The
existing dense Schwartz periodization yields density of the original tests,
and the uniform norm is exactly the zeroth source seminorm. A finite
order-zero bound extends the functional continuously; density gives uniqueness.

[`PeriodicDistributionPhysicalOrderZero.lean`](../NLS/Fourier/PeriodicDistributionPhysicalOrderZero.lean)
transports these results isometrically to the actual circle of period L.
Evaluation at a real representative is the original test value, so no
rescaling remains in the physical extension statement. The L1 functional
acts by exactly (1/L) times the interval integral of the function times the
test. Its least order is zero, including the zero function. Its Fourier
coefficients and tempered realization agree with the existing interval-L1
construction without any boundedness or square-integrability hypothesis.

These results prove the continuous-extension criterion and L1 special case.
The general complex Radon-measure representation and converse are now proved
by the following construction.

## Complex measures and formula (A.2)

[`RealContinuousFunctionalDecomposition.lean`](../NLS/Fourier/RealContinuousFunctionalDecomposition.lean)
proves that every bounded real functional on continuous functions over a
nonempty compact space is the difference of two positive functionals. It
embeds a function and a scalar into the doubled compact space, controls the
functional by the uniform norm there, and uses a norm-preserving Hahn–Banach
extension. Its value at the constant-one function proves positivity. No
signed or complex Riesz representation is assumed in this step.

[`ComplexMeasureContinuousIntegral.lean`](../NLS/Fourier/ComplexMeasureContinuousIntegral.lean)
uses Mathlib's actual countably additive complex measures. Their integral is
the standard sum of four Bochner integrals against the positive and negative
Jordan components of the real and imaginary signed measures. The public
`complexMeasureContinuousIntegral_apply` gives this formula explicitly.
Changing a signed measure's positive-minus-negative representation does not
change the integral. Testing real continuous functions and using uniqueness
for regular positive measures recovers the entire complex measure.

The sum of the real and imaginary total variations bounds the complex total
variation and is finite. Thus every complex measure has finite variation.
On the compact metrizable physical circle this variation is regular, which
proves the required finite complex Radon property for every complex Borel
measure. No additional regularity hypothesis is passed to the representation
theorem on the circle.

[`ComplexMeasureRepresentation.lean`](../NLS/Fourier/ComplexMeasureRepresentation.lean)
applies Mathlib's positive real Riesz theorem to the proved positive
decomposition. It first represents arbitrary bounded real functionals by
signed measures. The real and imaginary restrictions of a complex functional
then provide an actual complex representing measure. Complex linearity
extends the equality from real tests to every continuous complex test.

[`PeriodicDistributionMeasure.lean`](../NLS/Fourier/PeriodicDistributionMeasure.lean)
scales that representation to the source's exact 1/L action. The unique
continuous extension of an order-zero distribution yields its unique measure;
conversely every complex measure produces an order-zero distribution. An
explicit equivalence packages both round trips. The integral of a constant
is that constant times the total mass. Consequently, the zeroth Fourier
coefficient is the total mass divided by L, and a complex mass Lz at a physical
point x acts as z times evaluation at x. Integration is on the physical circle,
so representatives at 0 and L denote the same point.

## Original Fourier–Lebesgue spaces and function endpoints

[`PeriodicFourierLebesgueSpace.lean`](../NLS/Fourier/PeriodicFourierLebesgueSpace.lean)
defines a subtype of the original smooth-test dual by membership of its
normalized Fourier coefficients in the weighted sequence space. Its norm is
induced by those coefficients, rather than by the ambient dual topology.
Surjectivity of coefficient extraction is proved using actual tempered
synthesis and its original-distribution inverse. The resulting linear isometry
establishes completeness and reflexivity, including negative and fractional
Sobolev orders. The Sobolev weight is exactly (1+|n|)^s, as explicitly defined
in Section 2 on printed page 22. At s=0 it equals the unit weight.

[`PeriodicFourierLebesgueSeries.lean`](../NLS/Fourier/PeriodicFourierLebesgueSeries.lean)
identifies transported coefficient cutoffs with integration against the actual
finite continuous trigonometric sum on the physical circle. Norm convergence
holds for finite p. At infinity it holds precisely when the weighted
coefficients vanish at infinity. Inverse-weight coefficients give a unit-norm
original distribution with truncation error one for every finite set. For the
unit weight this is exactly evaluation at zero, not an abstract sequence-only
counterexample. Thus the blanket norm-convergence sentence on page 122 is
false at infinity. Convergence against every original smooth test nevertheless
holds at all exponents, as does convergence in Mathlib's pointwise topology
on the actual tempered realization. No strong-dual convergence is inferred
from the pointwise statement.

[`PeriodicFourierLebesgueEndpoints.lean`](../NLS/Fourier/PeriodicFourierLebesgueEndpoints.lean)
identifies FL2 linearly and isometrically with the actual L2 quotient on
AddCircle L, using Haar measure of total mass one. The represented original
distribution acts by integration of the L2 representative times the smooth
test. Rewriting the Haar integral gives exactly 1/L times the integral over
[0,L], both for this action and for Parseval. The identification has both
round trips; it does not merely compare coefficient norms.

For arbitrary interval L1 data the same original action defines an element
of FL-infinity whose norm is bounded by L^{-1} times the integral of its
absolute value. For FL1, the Fourier series is absolutely summable in the
Banach space C(T_L), hence converges uniformly. Its sum has the exact original
coefficients, represents the entire original distribution, and is unique
among continuous functions. The map to continuous functions is complex linear
and continuous with norm at most one. Uniform continuity and the pointwise
series with frequencies 2πn/L are also explicit. These prove the endpoints
used by A.2 and A.4; the full intermediate-exponent embeddings are now
proved by the construction below.

[`PeriodicFourierLebesgueDuality.lean`](../NLS/Fourier/PeriodicFourierLebesgueDuality.lean)
transports the proved full sequence-space duality to these original spaces.
At finite source exponent p the entire continuous dual is linearly isometric
to FLq for its conjugate q, including q=infinity when p=1. One Fourier index
is reversed in the bilinear action. The exact norm is retained under both
coefficient transport and reflection. This gives the source's identification
of pseudomeasures with the full dual of the Wiener space.

## Riemann–Lebesgue decay and the L1 Fourier map

[`PeriodicRiemannLebesgue.lean`](../NLS/Fourier/PeriodicRiemannLebesgue.lean)
identifies the normalized interval coefficient with the real Fourier integral
of the function extended by zero, evaluated at frequency n/L and multiplied
by 1/L. Both positive and negative integer frequencies escape every compact
real set. Mathlib's real Riemann–Lebesgue theorem therefore gives cofinite
decay, with the exact normalization preserved. Rewriting the physical-circle
coefficient gives the same result for normalized Haar measure. The raw decay
statements also cover nonintegrable functions under Mathlib's convention for
Bochner integrals; the source application is to integrable functions.

The proved c0 criterion for original FL-infinity truncations then gives norm
convergence for every interval L1 function. Point evaluation has all
coefficients equal to one, so it cannot equal integration against an L1
function. This last obstruction concerns the larger FL-infinity space and
does not prove failure of surjectivity onto c0.

[`PeriodicL1Fourier.lean`](../NLS/Fourier/PeriodicL1Fourier.lean) constructs the
actual complex continuous linear map from the L1 quotient on the physical
circle to Mathlib's c0 space on the discrete integers. Almost-everywhere
invariance makes the map well defined on the quotient. The integral bound
proves operator norm at most one; the constant function attains one. Every
finite coefficient cutoff is the transform of a continuous physical
trigonometric polynomial. The defining c0 decay then proves dense range in
the uniform coefficient norm. The following construction proves non-surjectivity
and completes Remark A.6.

[`RudinShapiro.lean`](../NLS/Fourier/RudinShapiro.lean) constructs the classical
recursive polynomial pair on the physical circle. Its pointwise squared
energy is exactly 2^(n+1); each coefficient has norm one on the block
[0, 2^n) and is zero outside. The first polynomial therefore has uniform norm
at most sqrt(2^(n+1)) and normalized L2 square norm exactly 2^n.
[`RudinShapiroCoefficients.lean`](../NLS/Fourier/RudinShapiroCoefficients.lean)
packages the actual finite coefficients, proves their exact support and
p-norm (2^n)^(1/p), and recovers the polynomial by finite synthesis in every
Banach Lᑫ quotient, including infinity.

[`PeriodicL1NonSurjective.lean`](../NLS/Fourier/PeriodicL1NonSurjective.lean)
uses the actual L1 classes of these polynomials. Every transformed sequence
has c0 norm exactly one, whereas Parseval and the uniform bound force
2^n ≤ sqrt(2^(n+1)) times the L1 norm. If the Fourier map were onto, its
previously proved injectivity and the open mapping theorem would give a
bounded inverse with norm C. The estimates would then force 2^n ≤ 2C² for
every n, a contradiction. This makes the open-mapping argument mentioned
in A.6 explicit; it does not assume non-surjectivity or a counterexample.

Together with the established dense range, this proves that the image is
not closed. The existential counterexample is exported both as a c0 element
and as a raw integer sequence tending to zero along the cofinite filter,
with no integrable function having those Fourier coefficients. Transport
to the original FL-infinity space yields a distribution with vanishing
coefficients and no L1 representative. Its Fourier truncations nevertheless
converge in the original FL-infinity norm. Thus neither coefficient decay
nor that norm convergence is a converse to L1 representability.

## Sharpness counterexamples A.3 and A.5

[`ShiftedRudinShapiro.lean`](../NLS/Fourier/ShiftedRudinShapiro.lean) shifts
the polynomial P_(2j) by frequency 4^j. Its coefficients have norm one on
[4^j, 2*4^j) and vanish elsewhere. These blocks are pairwise disjoint, and
the uniform norm is at most sqrt(2)*2^j. Finite Fourier synthesis recovers
the actual continuous polynomial, and the original smooth modes realize
the corresponding physical-circle characters.

[`NonMeasureFourierCounterexample.lean`](../NLS/Fourier/NonMeasureFourierCounterexample.lean)
uses amplitudes (j+1)/2^j. The p-norm of block j is exactly
(j+1)*(2^(2/p-1))^j, so the blocks are summable in every finite exponent
p > 2. Their sum at p=3 synthesizes one original periodic distribution.
Coefficient evaluation shows that this same distribution lies in every
other finite FLp above two; exponent inclusion gives infinity as well.

For the non-measure assertion, the conjugate of the jth block polynomial
is an actual original smooth test, with uniform norm at most sqrt(2)*2^j.
Its pairing with the constructed distribution is exactly (j+1)*2^j.
A bounded extension to all continuous functions would therefore force
j+1 ≤ sqrt(2)*C for every j. This contradiction proves that its least order
is nonzero. Since every complex measure produces an order-zero original
distribution, no complex measure represents it. This proves all of A.3,
including its quantifier order and physical-circle interpretation.

[`ContinuousFourierCounterexample.lean`](../NLS/Fourier/ContinuousFourierCounterexample.lean)
uses amplitudes 1/((j+1)^2*2^j). The uniform norms are bounded by
sqrt(2)/(j+1)^2, giving an absolutely convergent series in C(T_L) and hence
a continuous sum. On each block its coefficients are exactly those of that
single term. Their p-norm is (2^(2/p-1))^j/(j+1)^2, which is unbounded
for every 1 ≤ p < 2. Any full ℓp coefficient sequence would bound all these
block norms, a contradiction. The conclusion is stated both for the actual
Fourier coefficients and for membership of the original distribution.
The witness is independent of p. This proves A.5 by an alternative
construction. The particular printed series, its uniform convergence and
its exact Fourier and physical L2 properties are also verified below.

The two Rudin-Shapiro constructions above apply to every positive physical
period and use the previously established normalized Fourier maps. Neither
assumes the desired counterexample, a failure of membership, or non-measure
representability. The literal printed series is treated separately below.

## Sharp finite interpolation prerequisites

[`FiniteInterpolationSharp.lean`](../NLS/SequenceSpaces/FiniteInterpolationSharp.lean)
retains the geometric endpoint constant B0^(1-t) B1^t in the existing finite
analytic-family argument. Independent complex scalings factor out of the
bilinear kernel pairing, so normalization extends the result from unit inputs
to arbitrary finite inputs, including zero inputs and zero endpoint bounds.

[`DiscreteParseval.lean`](../NLS/Fourier/DiscreteParseval.lean) proves exact
orthogonality for finite cyclic characters and the adjoint identity for the
negative-phase discrete Fourier transform. Applying that identity twice gives
Parseval with squared norm factor N, hence the Hilbert norm factor sqrt(N).
The L1 coefficient bound has constant one. All results include transform size
one. The following modules use these endpoints to prove the full embeddings.

## Full Hausdorff–Young embeddings, Lemmas A.2 and A.4

[`FiniteMatrixInterpolation.lean`](../NLS/SequenceSpaces/FiniteMatrixInterpolation.lean)
extends sharp bilinear interpolation to arbitrary finite input and output
index types, with their actual PiLp norms. Complex norming tests recover the
conjugate norm, and extension by zero preserves every finite exponent norm.
[`DiscreteHausdorffYoung.lean`](../NLS/Fourier/DiscreteHausdorffYoung.lean)
then proves the exact N^(1/q) bound for the unnormalized discrete transform.
The normalized qth moment has constant one.

[`CircleSampling.lean`](../NLS/Fourier/CircleSampling.lean) proves that equally
spaced averages on the physical circle converge to probability Haar integration
for every continuous function. The proof uses exact character averages,
uniform operator bounds, and density of Fourier polynomials.
[`PolynomialHausdorffYoung.lean`](../NLS/Fourier/PolynomialHausdorffYoung.lean)
embeds any finite set of signed frequencies into a sufficiently large cyclic
grid without aliasing. The negative-phase discrete transform is evaluated at
the reflected grid index to recover positive-phase synthesis. Passing sample
moments to the integral gives the constant-one polynomial estimate.

[`CircleHausdorffYoungSynthesis.lean`](../NLS/Fourier/CircleHausdorffYoungSynthesis.lean)
extends polynomial synthesis by density from ℓᵖ to the actual Lᑫ quotient,
for every conjugate pair with 1 ≤ p ≤ 2. The endpoint p=1, q=infinity has a
separate uniform estimate. Continuous coefficient functionals recover the
original coefficients after extension.
[`CircleHausdorffYoungAnalysis.lean`](../NLS/Fourier/CircleHausdorffYoungAnalysis.lean)
uses Hölder pairing with synthesis and the full ℓᵖ duality theorem to construct
Lᵖ → ℓᑫ. Reflection of the dual sequence supplies the negative Fourier sign.
Both maps are complex linear and continuous, with norm at most one.

[`PeriodicL1Uniqueness.lean`](../NLS/Fourier/PeriodicL1Uniqueness.lean) proves
that continuous tests separate integrable complex densities. For real densities,
uniqueness of regular positive and negative density measures gives a.e. zero;
real and imaginary parts give the complex result. Density of the original
smooth tests transfers it to the original distribution space. Thus equality
of represented distributions is exactly a.e. equality, including the L1 and
L-infinity endpoints. This also proves injectivity of the L1-to-c0 Fourier map.

[`PeriodicFourierLebesgueEmbeddings.lean`](../NLS/Fourier/PeriodicFourierLebesgueEmbeddings.lean)
packages the full source assertions on the original distribution subtypes.
`ofLp` is the continuous injection Lᵖ → FLᑫ, and `lpRepresentative` is the
continuous injection FLᵖ → Lᑫ. Both have constant-one bounds for normalized
Haar measure, and the action on every original smooth test is exactly 1/L
times the interval integral. The Lᑫ representative is unique. At p=2 these
maps agree with the previous L2 isometry and its inverse; at p=1 synthesis
is the L-infinity equivalence class of the earlier uniformly convergent
continuous Fourier series. No representation or coefficient-recovery premise
is required from the caller.

## Faithful realization and the period factors

[`SmoothPeriodicDistribution.lean`](../NLS/Fourier/SmoothPeriodicDistribution.lean)
defines a periodic distribution as a continuous complex-linear functional
on the original test space. Rescaled Schwartz periodization supplies every
original smooth test. The lift theorem recovers that test pointwise.

Transferring a functional to the period-two tempered realization keeps the
factor two in the action on periodized Schwartz tests. The normalized
coefficient test periodizes to one half of the negative Fourier mode, so
the two factors cancel exactly. Actual distributional dilation then gives
the stated physical period L. In the reverse direction, the normalized
window of period L defines the action on every smooth periodic test.

The two round-trip theorems recover both the original functional and the
actual periodic tempered distribution. Fourier uniqueness is consequently
uniqueness on the full original test space, with no realization hypothesis
left for the caller to supply.

## Polynomial growth and synthesis

[`PeriodicDistributionFourierGrowth.lean`](../NLS/Fourier/PeriodicDistributionFourierGrowth.lean)
defines the least order using the finite-order criterion. The exact norms
of the Fourier-test derivatives bound their C^N norm by a polynomial of
degree N. The resulting Fourier coefficient bound retains that same degree.
Converting a global bracket bound to the cofinite asymptotic discards only
the zero frequency and also works when N=0.

[`PolynomialPeriodicDistribution.lean`](../NLS/Fourier/PolynomialPeriodicDistribution.lean)
synthesizes a polynomially bounded raw sequence by placing it in the
weighted infinity coefficient space with weight (1+|n|)^(-N). The existing
actual distributional synthesis and uniqueness then apply. The asymptotic
version separately controls the arbitrary zero-mode value. The faithful
test-space bridge transfers this existence result to the original dual.

## Physical distributional derivative

[`SmoothPeriodicDistributionDerivative.lean`](../NLS/Fourier/SmoothPeriodicDistributionDerivative.lean)
constructs the continuous physical derivative on the original test space.
The derivative of a distribution is its negative transpose. Evaluation on
physical exponential modes gives the signed multiplier i·2πn/L, including
the zero frequency, and the finite-order estimate increases by at most one.
Differentiation commutes with the actual physical tempered realization;
the proof tracks both Schwartz and distribution dilation factors, including
negative dilation.

## Validation and remaining Appendix A work

The first four modules and 28 public checks cover finite order and Theorem A.1.
The next four modules add 30 public checks for the Fréchet instances, density,
unique physical-circle extension, normalized L1 action at periods one and
three, signed and zero derivative modes, order bounds for L1 functions and
point evaluation, negative dilation, and physical derivative realization.
Four further modules add 28 checks for the actual complex-measure
representation, finiteness, regularity, uniqueness, both identification round
trips, signed and imaginary point masses, periods one through three, zero
measure, constants and total mass, L1 realization, and actual tempered Fourier
coefficients. All twelve modules and their focused checks compile without
new warnings. Full validation is recorded in [STATUS.md](../STATUS.md).

Four new modules add 36 public checks for original-space completeness,
reflexivity, negative and fractional orders, actual finite polynomials,
finite-p and infinity convergence, the point-evaluation obstruction, both L2
round trips and physical normalization, the L1 bound, absolute and uniform
FL1 synthesis, and the entire pseudomeasure dual. These modules and their
focused checks compile without new warnings.

Four further modules add 28 checks for the geometric interpolation constant,
complex scalings, both interpolation endpoints, discrete orthogonality and
normalization, physical-period decay, the actual L1 quotient map, exact
operator norm one, signed finite cutoffs, and density in c0. They compile
without new warnings.

Eight further modules and 36 public checks cover the full Hausdorff–Young
embeddings, the fractional pair 4/3 and 4, size-one and size-sixteen transforms,
aliased and unaliased signed frequencies, physical period three, exact interval
action, both endpoint identifications, injectivity, and unique Lᑫ representatives.
All eight modules and the focused checks compile without new warnings.

Three further modules and 28 public checks cover the Rudin–Shapiro recurrence,
energy, support boundaries, signed frequency shifts, physical periods one and
three, finite fractional norms, the infinity synthesis endpoint, the exact c0
norm, the L1 growth bound, non-surjectivity, nonclosed dense range, and the
counterexamples as sequences and original distributions.

Three further modules and 28 checks cover A.3 and A.5, including signed
frequencies, all support boundaries, disjointness, uniform continuity,
physical periods one and three, the fractional exponents 4/3 and 5/2,
the exponent-two block norm, the infinity membership endpoint, exact
original-test pairing, positive order, and actual measure nonrepresentability.

Four further modules and 42 checks cover A.7, the Wiener algebra, the corrected
A.8 estimate and its finite-polynomial counterexample. The product is first
constructed through the exact original coefficient isometries. Uniqueness
holds among all original distributions. Mapping the uniformly convergent
Fourier series through continuous multiplication proves agreement with actual
pointwise products, which in turn proves the algebra laws.

[`PeriodicSobolevEmbedding.lean`](../NLS/Fourier/PeriodicSobolevEmbedding.lean)
transports the coefficient Hölder bound through the same isometries and proves
equality of the entire original functional. The constant is retained explicitly.
[`SobolevProductCounterexample.lean`](../NLS/Fourier/SobolevProductCounterexample.lean)
identifies both witnesses and their product with actual physical polynomials,
then computes the exact squared norms. See [SOURCE_ERRATA.md](../SOURCE_ERRATA.md).

Three further modules and 32 checks cover A.9 on the original spaces.
[`PeriodicIntervalFourierLebesgue.lean`](../NLS/Fourier/PeriodicIntervalFourierLebesgue.lean)
identifies the coefficient synthesis with integration against arbitrary interval
input. Its source-level membership theorems require only the printed L2 and
fractional regularity hypotheses, and include the strict exponent range at
zero and at half regularity. The zero-regularity result is stronger at q=2;
the ordinary L2 inclusion also supplies the infinity target.

[`PeriodicIntrinsicSobolevEmbedding.lean`](../NLS/Fourier/PeriodicIntrinsicSobolevEmbedding.lean)
transfers the established coefficient maps through the original coefficient
isometry. The equality of original distributions proves the exact 1/L action
on every smooth test. The domain is the actual a.e. interval quotient with
finite Slobodeckij difference energy. No periodic endpoint condition is imposed.
At s=0 the ordinary L2 API is used; the intrinsic graph energy at zero is not
silently identified with the usual L2 norm.

[`PeriodicIntrinsicSobolevEquivalence.lean`](../NLS/Fourier/PeriodicIntrinsicSobolevEquivalence.lean)
provides the continuous linear equivalence invoked in A.9's proof for
0<s<1/2. Both directions preserve the original function, and the inverse gives
an actual interval representative of every original FL^{s,2} distribution.
The exact weight (1+|n|)^s is retained. The analysis and synthesis constants
record the physical dilation from length L, so no isometric assertion about
the source's rescaled weight is substituted for this equivalence. At s=0,
the existing physical L2 isometry supplies the Hilbert identification.

This completes A.9's original-space integration. The separately recorded
corrections to the infinity Fourier-series assertion and (A.4) remain.

The blanket norm-convergence assertion on page 122 includes the infinity
endpoint. The obstruction already formalized for Section 2 applies there
as well; see [SOURCE_ERRATA.md](../SOURCE_ERRATA.md). Distributional
convergence is available at that endpoint and does not imply norm convergence.
The source's Lemma A.2 has L^(p') on its left side for 2≤p≤∞; the prime must
not be lost when reading extracted PDF text.

The [Section 14 edition comparison](SECTION_14.md) remains. The literal
all-order Lemma 27.2 is now proved in [Section 27](SECTION_27.md). This
appendix audit does not certify the whole dissertation complete.

## General convolution criterion before Lemma A.7

The unnumbered paragraph on printed p.123 requires each Fourier convolution
to converge and its values to have polynomial growth. The previously proved
Young products cover particular exponent pairs. The general criterion now
holds directly on the original smooth-test dual at every positive period.

[`PeriodicDistributionConvolutionProduct.lean`](../NLS/Fourier/PeriodicDistributionConvolutionProduct.lean)
defines a product by genuine coefficient convergence and proves existence
and uniqueness exactly when the resulting sequence has polynomial growth.
Uniqueness is equality on every original smooth periodic test. There are
separate statements for unordered `HasSum` convergence and symmetric integer
cutoffs. The latter does not require absolute convergence. Unordered
convergence implies the symmetric relation, and the existing original Young
products satisfy both. Point evaluation at zero cannot be multiplied by
itself under the unordered criterion: its convolution terms are all one.

[`SparseConvolutionGrowth.lean`](../NLS/Fourier/SparseConvolutionGrowth.lean)
shows why convergence alone is insufficient. The first input equals k at
k=4^j and zero elsewhere; the second equals one at k=j-4^j and zero elsewhere,
with j a natural number. Their growth has degree at most one and zero.
For fixed output m, any contributing labels i,j satisfy i,j≤|m|, so every
convolution has finite support. At nonnegative output m, the diagonal term
already has value 4^m and every term is nonnegative. The output therefore
violates every polynomial bound.

[`PeriodicConvolutionGrowthObstruction.lean`](../NLS/Fourier/PeriodicConvolutionGrowthObstruction.lean)
realizes these two inputs as actual continuous functionals on the original
test space at every positive physical period. Every actual coefficient
convolution converges, yet no original distribution has the output
coefficients. Neither unordered nor symmetric summation gives a product.
This confirms the necessity of the source's growth premise.

[`PeriodicSymmetricProductExample.lean`](../NLS/Fourier/PeriodicSymmetricProductExample.lean)
shows that the two convergence conditions differ for actual distributions.
The bounded coefficient sequence 1/k, with zero at k=0, defines an original
distribution at every positive period. Its symmetric sums cancel exactly.
Together with point evaluation at zero this gives a symmetric product equal
to the zero distribution. The positive-frequency harmonic subseries prevents
an unordered product for the same inputs.

Seven examples check a negative output at physical period three, a concrete
exponential lower bound, failure of the symmetric product, construction and
uniqueness when both conditions hold, and agreement with the original
Wiener product, plus actual symmetric cancellation and failure of unordered
convergence. All four modules and their focused examples compile without
new warnings. Full validation is recorded in [STATUS.md](../STATUS.md).
The particular printed A.5 series is verified in the follow-up sections
below, including uniform convergence and its exact coefficient threshold.
The alternative construction above also proves the existential statement.

## Literal coefficients in the proof of A.5

The series displayed on printed p.123 uses the coefficient

    a_n = exp(i*n*log(n))/(sqrt(n)*log(n)^2),  n>=2,

and zero at all other integer frequencies. The phase, denominator and
lower cutoff were checked in the original rendered page.

[`PrintedChirpCoefficients.lean`](../NLS/Fourier/PrintedChirpCoefficients.lean)
proves its exact magnitude and the sharp coefficient-space criterion:
for every Banach exponent p, this sequence is in lp if and only if p>=2,
including the infinity endpoint. Square summability follows by Cauchy
condensation, reducing the positive majorant to a constant multiple of
1/k^4. Below two, logarithmic growth is dominated by a sufficiently small
positive power, giving a divergent p-series lower bound.

`printedChirpL2` is an actual normalized period-two physical L2 function
with exactly these Fourier coefficients. Its literal partial sums over
2<=n<=N converge in the physical L2 norm. Three public examples check
the complex coefficient at n=2 and a negative mode, the fractional and
endpoint membership behavior, and the displayed partial sums with the
phase and denominator expanded.

This coefficient step is completed below by actual cancellation, weighted
tail estimates and uniform convergence of the literal series. The earlier
Rudin-Shapiro witness independently proves the existential statement.

## Cancellation for the literal printed A.5 phase

The next prerequisite concerns the actual oscillatory factors
exp(i*n*log(n))*exp(i*n*pi*x), uniformly for every real physical point x.
For every integer N>=1 and every prefix length 0<=M<=N, their sum over
N<=n<N+M has squared norm at most

    N + 12*pi*N*(1+log N).

The lower-cutoff case N>=2 needed by the printed series is included.
The estimate controls every prefix, not just complete dyadic blocks.

The proof squares the finite sum and groups off-diagonal terms by positive
lag h. In each correlation the linear physical phase becomes a constant.
Actual derivative and mean-value estimates for t*log(t) show that its
half-increments decrease and lie between h/(6*N) and 1/2. A reciprocal
exponential multiplier, exact summation by parts and telescoping total
variation bound each correlation prefix by 6*pi*N/h. The finite harmonic
sum then gives the logarithmic bound above. No unproved exponential-sum
estimate is assumed.

The following uniform-convergence result combines these bounds with the
printed amplitude, controls every ordinary positive-index cutoff, and
identifies the continuous representative with printedChirpL2. The
alternative witness establishes A.5's existential statement independently.

Public modules:

- [`OscillatorySumVariation.lean`](../NLS/Fourier/OscillatorySumVariation.lean)
- [`PhaseReciprocalMultiplier.lean`](../NLS/Fourier/PhaseReciprocalMultiplier.lean)
- [`AntitonePhaseCancellation.lean`](../NLS/Fourier/AntitonePhaseCancellation.lean)
- [`ChirpPhaseIncrements.lean`](../NLS/Fourier/ChirpPhaseIncrements.lean)
- [`ChirpCorrelationSums.lean`](../NLS/Fourier/ChirpCorrelationSums.lean)
- [`FiniteCorrelationIdentity.lean`](../NLS/Fourier/FiniteCorrelationIdentity.lean)
- [`ChirpBlockCancellation.lean`](../NLS/Fourier/ChirpBlockCancellation.lean)

## Uniform convergence of the literal printed series

The exact series displayed in the proof of A.5 now has a continuous
period-two realization. Its ordinary positive-index partial sums over
2<=n<=N converge uniformly for all real x to `printedChirpFunction`.
The public statement expands both exponential factors and the full
sqrt(n)*log(n)^2 denominator; it preserves the printed cutoff and phase.

The amplitude is positive and decreasing for n>=2. Abel summation
combines that fact with the actual block-prefix cancellation estimate.
For the block starting at 2^k, every weighted prefix has norm at most

    C/k^(3/2),
    C = sqrt(1+12*pi*(1+log 2))/(log 2)^2.

This majorant is summable. A complete-space argument first controls
dyadic cutoffs, then uses the prefix estimate inside each block to prove
convergence along every ordinary cutoff. Applied in C(R/2Z), this gives
uniform convergence and a continuous limit without assuming pointwise
convergence or replacing the printed coefficients.

Every actual Fourier coefficient and normalized interval Fourier integral
of the limit equals `printedChirpCoefficient`. Its physical L2 class is
exactly `printedChirpL2`. Membership in the original distribution-based
Fourier-Lebesgue space holds precisely for p>=2, including infinity.
Thus this particular printed witness, independent of p, supplies the
obstruction for all Banach exponents below two.

The literal displayed factors exp(i*n*pi*x) use physical period two.
The explicit transport below realizes the same witness at every positive
period with the required frequency change. Whole-dissertation completeness
and the separate source-edition and interval-norm qualifications remain
separate obligations.

Public modules:

- [`MonotoneWeightedSums.lean`](../NLS/Fourier/MonotoneWeightedSums.lean)
- [`PrintedChirpAmplitude.lean`](../NLS/Fourier/PrintedChirpAmplitude.lean)
- [`ChirpWeightedBlocks.lean`](../NLS/Fourier/ChirpWeightedBlocks.lean)
- [`DyadicPrefixConvergence.lean`](../NLS/Fourier/DyadicPrefixConvergence.lean)
- [`PrintedChirpPolynomials.lean`](../NLS/Fourier/PrintedChirpPolynomials.lean)
- [`PrintedChirpContinuous.lean`](../NLS/Fourier/PrintedChirpContinuous.lean)
- [`PrintedChirpLiteralSeries.lean`](../NLS/Fourier/PrintedChirpLiteralSeries.lean)

## The same printed witness at any positive physical period

[`PrintedChirpPeriodTransport.lean`](../NLS/Fourier/PrintedChirpPeriodTransport.lean)
transports the literal period-two witness to every positive physical
period L by the explicit coordinate change x -> 2*x/L. The pullback is
a continuous linear map between the two spaces of continuous functions.
It sends each signed Fourier character to the same signed integer mode
at period L.

The displayed coefficients are unchanged. Ordinary partial sums using
exp(2*pi*i*n*x/L) converge uniformly on the whole real line, and the
normalized period-L interval Fourier integrals recover every printed
coefficient exactly. Membership in the original distribution-based
Fourier-Lebesgue spaces is equivalent to p>=2, including infinity.
Thus the same explicit construction supplies one continuous witness
outside all Banach FLp spaces below two, at every positive period.

The period-two statement retains the literal factors printed in the
source. This transport states the physical frequency change explicitly.
Three examples check real-coordinate rescaling, the expanded series and
an actual Fourier integral at period three, and the all-exponent
original-space existential statement at an arbitrary positive period.
