# Section 2: current convergence and scalar pairing audit

This records the Fourier-convergence and scalar-pairing paragraphs on
printed pages 21–22, checked against the rendered source. It is a focused
part of the Section 2 audit; it does not certify the remaining full dual
representation, reflexivity, or gradient claims.

The source defines the scalar Fourier-Lebesgue space for every real
regularity and every exponent from one through infinity, then asserts that
its Fourier series converges in the same norm without excluding infinity.
That assertion needs an endpoint qualification.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Norm convergence for finite exponents | `NLS.Fourier.sourceSectionTwo_norm_convergence` | All real Sobolev orders, including negative orders, and every finite Banach exponent, including p=1. The net runs over all finite frequency sets. |
| Exact range of universal norm convergence | `NLS.WeightedCoeff.forall_tendsto_truncate_iff` | For every positive weight and Banach exponent, convergence for every input holds if and only if p is finite. |
| Correct individual infinity criterion | `NLS.WeightedCoeff.tendsto_truncate_top_iff` | At p=infinity, convergence is equivalent to the weighted coefficients tending to zero outside finite sets. This is the weighted c0 condition. |
| Exact counterexample error | `NLS.WeightedCoeff.norm_inverseWeightCoefficients_sub_truncate` | Coefficients 1/w(n) have norm one and error exactly one for every finite set, hence for every symmetric cutoff as well. |
| Actual periodic source | `NLS.Fourier.sourceSectionTwoInfinityDistribution_periodic`, `sourceSectionTwoInfinityDistribution_coefficient` | A genuine period-two tempered distribution with coefficients 1/(1+abs(n))^s, for every real s. Period two is one of the positive periods quantified over in the source. |
| Same sums, different convergence claims | `NLS.Fourier.sourceSectionTwo_infinity_counterexample` | The same unit-norm source and its finite sums fail norm convergence and converge distributionally. |
| Distributional convergence without the finite-exponent restriction | `NLS.Fourier.tendsto_sobolevDistributionSynthesis_truncate` | Every real Sobolev order and every Banach exponent, including infinity. |

These are statements about the original weighted coefficient norm and its
injective realization as actual periodic distributions. The counterexample
does not arise from changing the norm or from using a formal Fourier symbol
without a distributional realization. The weighting criterion also permits
infinite-support inputs at infinity when their weighted coefficients vanish.

The scalar claim is already false, so no choice of pair norm repairs it.
The separate source pair norm at infinity is the supremum of the sum of
component magnitudes; existing `PairDistributionInfty.lean` preserves that
norm and the reflected first signed coefficient. It must not be silently
replaced by the product maximum norm when auditing the rest of Section 2.

## Scalar bilinear pairing

The printed scalar sum uses the same index in both factors while claiming
to extend physical distributional action. In the coefficient convention
specified on page 21, the physical unconjugated pairing reverses one index.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Source counterexample | `NLS.Fourier.sourceSectionTwo_printed_bilinear_pairing_false` | A smooth period-one wave has printed same-index sum one and physical integral zero. Its actual Fourier coefficients are computed exactly. |
| Corrected physical bilinear formula | `NLS.Fourier.hasSum_bilinear_intervalFourierCoefficient` | Every positive period L and square-integrable inputs; reversed first index and the original 1/L normalization. |
| Original sesquilinear formula | `NLS.Fourier.hasSum_sesquilinear_intervalFourierCoefficient` | The same physical domain, with equal indices and complex conjugation. |
| Bounded scalar pairing | `NLS.WeightedCoeff.sobolevBilinearPairing`, `sobolevBilinearPairing_apply` | A complex bounded bilinear map on conjugate Sobolev coefficient spaces at every real order, using reversed second index. |
| Exact bound and absolute convergence | `NLS.WeightedCoeff.norm_sobolevBilinearPairing_le`, `summable_norm_sobolevBilinearPairing` | Constant one for every conjugate Banach pair, including either infinity endpoint. |
| Physical distributional action | `NLS.Fourier.periodicDistribution_sobolevBilinearPairing` | Any period-two tempered distribution with the stated coefficients, tested on Schwartz periodizations; the factor one half retains normalized periodic action. |
| Every smooth periodic test | `NLS.Fourier.periodization_smoothPeriodicTestLift`, `smoothPeriodicTestLift_sobolev_coefficients` | Every smooth period-two test has an exact Schwartz lift and actual Fourier coefficients in every real Sobolev class and Banach exponent. No additional growth hypothesis. |
| Full smooth-test action | `NLS.Fourier.periodicDistribution_sobolevBilinearPairing_smooth` | The corrected pairing equals the actual normalized windowed action on every smooth period-two test, for arbitrary periodic distributions of the stated regularity. |

The zero-mode Schwartz window has periodization one half; this fixes the
normalized action and prevents an accidental factor-two change. The lift
multiplies by two and reconstructs the original test exactly. Ordinary
abstract coefficient duality remains available; frequency reflection is
required when interpreting it as a physical unconjugated pairing.

The physical L2 integral formula covers every positive period. The general
distributional smooth-test bridge currently uses the repository's period-two
realization; arbitrary-positive-period distribution transport remains to
be verified. Next are that transport and the full dual-gradient assertion,
including its exponent endpoints, then the numbered Section 3 statements.
The candidate-label inventory and this focused map do not establish
completeness of those remaining claims.
