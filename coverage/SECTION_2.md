# Section 2: current convergence audit

This records the Fourier-convergence paragraph on printed page 21, checked
against the rendered source. It is a focused part of the Section 2 audit;
it does not certify the remaining duality, reflexivity, or gradient claims.

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

Next: audit the scalar bilinear pairing against the actual distributional
action on printed page 22, then its dual-gradient representation and the
numbered statements in Section 3. Neither the candidate-label inventory nor
this focused map establishes completeness of those remaining claims.
