# Appendix A: periodic distributions and Fourier Lebesgue spaces

This audit covers the test-space foundations, finite-order criterion (A.1),
order-zero continuous extension, complex Radon representation (A.2), and L1
action on printed page 121, plus both parts of Theorem A.1 and the distributional
derivative on printed page 122. The test space
contains the actual smooth complex-valued functions with the stated
positive physical period. It is not defined as a coefficient-sequence space.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Smooth periodic test space and its derivative-norm topology | `SmoothPeriodicTest`, `SmoothPeriodicTest.cNorm_apply` | Every positive period L; the seminorm at N is exactly the sum of the sup norms of physical derivatives of orders 0 through N. |
| Fréchet test space | `derivativeJetEquiv` and the completeness, metrizability, Hausdorff, and local convexity instances | A closed derivative-jet subspace of a countable product of Banach spaces, with the original topology. |
| Density in C(T_L) | `denseRange_toContinuousCLM` | Dense range on the actual physical circle, with the exact uniform norm `norm_toContinuousCLM`. |
| Least order zero iff unique continuous extension | `Distribution.order_zero_iff_physical_extension` | Unique complex continuous linear functional on C(AddCircle L, ℂ), for every positive L. |
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

The Fourier Lebesgue assertions and Lemmas A.2–A.9 still require their
Appendix A source audit and integration.

The blanket norm-convergence assertion on page 122 includes the infinity
endpoint. The obstruction already formalized for Section 2 applies there
as well; see [SOURCE_ERRATA.md](../SOURCE_ERRATA.md). Distributional
convergence is available at that endpoint and does not imply norm convergence.
The source's Lemma A.2 has L^(p') on its left side for 2≤p≤∞; the prime must
not be lost when reading extracted PDF text.

The [Section 14 qualifications](SECTION_14.md) and unrestricted printed
m=1 coefficient in [Section 27](SECTION_27.md) remain. The dissertation
is incomplete.
