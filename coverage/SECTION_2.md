# Section 2: convergence, duality, gradients, and Poisson pairing

This records the Fourier-Lebesgue-space statements on printed pages 21–22,
checked against the rendered source. The maps below identify proved scope
and endpoint corrections. The remaining bracket compatibility and algebra audit is open;
this file is not a completeness certificate for the dissertation.

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

## Arbitrary positive periods

The distributional bridge now covers every positive period as well as the
physical L2 integral formula. The transport acts on genuine tempered
distributions and Schwartz tests, retains the inverse Jacobian, and has
an exact inverse. No new source correction is introduced by this transport.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Actual period rescaling | `NLS.Fourier.distributionDilation_periodic`, `distributionDilation_inverse` | Translation-invariant distributions are rescaled with their original action; inverse rescaling recovers the same distribution. Physical period applications use positive scales. |
| Original coefficient normalization | `NLS.Fourier.periodCoefficientTest_periodization`, `periodCoefficientTest_zero_periodization` | The coefficient test periodizes to (1/L) times the negative Fourier wave. The zero-mode window periodizes to 1/L, including non-unit and non-integer periods. |
| Intrinsic Fourier identification | `NLS.Fourier.periodicDistribution_weighted_memlp_iff_existsUnique_arbitraryPeriod` | Every actual period-L distribution belongs to the weighted coefficient class exactly when it has a unique synthesized representative. All Banach exponents and all positive weights with tempered inverse; in particular every real Sobolev order. |
| Continuous physical synthesis | `NLS.Fourier.arbitraryPeriodDistributionSynthesisCLM`, `arbitraryPeriodDistributionSynthesis_coefficient` | A continuous linear map into actual distributions recovers every raw coefficient without a period-dependent factor. |
| Fourier convergence at every period | `NLS.Fourier.tendsto_arbitraryPeriodDistributionSynthesis_truncate` | Distributional convergence of the finite Fourier sums at all Banach exponents, including infinity. This does not assert infinity norm convergence. |
| Compatibility with the existing realization | `NLS.Fourier.periodCoefficientTest_two`, `arbitraryPeriodDistributionSynthesis_two` | Period two recovers the existing tests and synthesized distribution exactly. |
| Original smooth-test coefficient membership | `NLS.Fourier.existsUnique_smooth_arbitraryPeriod_coefficients` | Every smooth period-L test has its actual normalized Fourier coefficients in every real Sobolev class and every Banach exponent, without an additional growth hypothesis. |
| Corrected full smooth-test action | `NLS.Fourier.periodicDistribution_sobolevBilinearPairing_arbitraryPeriod` | Every positive period, real Sobolev order and conjugate Banach pair, including (1,infinity) and (infinity,1); the pairing equals the actual normalized distributional action. |

The earlier period-two smooth-test entry is the core theorem used by this
transport; its period restriction is no longer a limitation on the final
pairing API.

## Full scalar duality and reflexivity

The scalar dual-space assertion explicitly covers 1<=p<infinity. The
p=1 endpoint has conjugate exponent infinity and is included here. Physical
representation uses the corrected index reversal recorded above.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Entire scalar coefficient dual | `NLS.Coeff.dualityIsometry`, `dualPairing_fullCotangent` | All finite Banach source exponents, including p=1; every bounded complex functional has a conjugate coefficient representative. |
| Original operator norm | `NLS.Coeff.norm_fullCotangent`, `norm_dualPairing_eq` | Exact norm equality, including the (1,infinity) endpoint. |
| Full physical Sobolev dual | `NLS.WeightedCoeff.sobolevDualityIsometry`, `existsUnique_sobolevCotangent` | Every real Sobolev order and finite source exponent; a complex linear isometry onto the entire dual under the corrected physical pairing. |
| Frequency sign and original modes | `NLS.WeightedCoeff.sobolevCotangent_val` | The representative's coefficient at n equals the functional evaluated on the raw coefficient mode -n; no weight or normalization factor is lost. |
| Scalar gradient representation | `NLS.WeightedCoeff.fderiv_eq_sobolevBilinearPairing_gradient`, `norm_sobolevScalarGradient` | The complete differential is represented on every direction, and its operator norm equals the gradient norm. |
| Analytic scalar gradients | `NLS.WeightedCoeff.analyticOnNhd_sobolevScalarGradient`, `hessian_eq_sobolevBilinearPairing_gradient_derivative` | Analyticity on the original scalar domain and the full Hessian identity, including p=1 and arbitrary real regularity. |
| Reflexivity in the printed range | `NLS.WeightedCoeff.bidual_surjective` | Surjectivity of the canonical map into the continuous double dual, for every positive weight and every 1<p<infinity. The conjugate exponent is constructed automatically. |

The scalar coefficient norm is precisely the source Fourier-Lebesgue norm;
the earlier intrinsic distributional identification supplies unique actual
periodic representatives at every positive period. Reflexivity here is
proved through the canonical map, rather than an unrelated bijection with
the double dual. No endpoint reflexivity claim is made.

## Full pair gradients and the infinity-source obstruction

The finite-source gradient claim now preserves the original pair norms
and signed Fourier convention. The infinity-source extension fails even
for everywhere-analytic linear functionals, at every real Sobolev order.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Both full component representatives | `NLS.WeightedCoeffPair.sobolevCotangentComponentsCLM`, `sobolevCotangentComponents_unique` | All real Sobolev orders, finite source exponents, and conjugate exponents including infinity; uniqueness on the whole source pair space. |
| Finite conjugate pair gradient | `NLS.WeightedCoeffPair.existsUnique_sobolevFiniteGradient`, `analyticOnNhd_sobolevFiniteGradient` | Every finite conjugate pair; the original component q-sum norm, full representation and analytic dependence. |
| Original p=1 endpoint gradient | `NLS.WeightedCoeffPair.existsUnique_sobolevOneGradient`, `analyticOnNhd_sobolevOneGradient` | Every real order, with target `WeightedCoeffPairInfty` carrying the source frequencywise sum norm. |
| Bounds in the original pair norms | `NLS.WeightedCoeffPair.norm_sobolevFiniteGradientCLM_le`, `norm_sobolevOneGradientCLM_le` | Bounds 2^(1/q) and 2 times the original functional norm; no assertion of pair-dual isometry. |
| Signed-frequency fidelity | `NLS.WeightedCoeff.sobolevBilinearPairing_reflection`, `NLS.WeightedCoeffPair.sobolevOneGradient_represents_physical`, `sobolevFiniteGradient_represents_physical` | Reversing both first signed components gives the physical scalar convention and preserves the representation formula. |
| Actual endpoint norm regression | `NLS.WeightedCoeffPair.sobolevOneGradient_pairFunctional`, `norm_sobolevOneGradient_diagonal` | Arbitrary prescribed endpoint components are recovered exactly. Equal components have twice the scalar norm, including nondecaying inverse-weight coefficients. |
| Full-dual exponent range | `NLS.Coeff.dualPairing_surjective_iff` | Coefficient representation is onto the full continuous dual exactly for finite Banach source exponents. |
| Infinity counterexample | `NLS.Coeff.exists_singular_functional`, `exists_analytic_without_coefficient_gradient` | A bounded functional vanishes on every finite sequence but not on one; its analytic derivative has no l1 representative at any point. |
| Original weighted pair counterexample | `NLS.WeightedCoeffPairInfty.exists_analytic_sobolev_pair_without_gradient` | Every real order, the exact infinity pair norm, and the corrected physical pairing; an everywhere-analytic functional has no opposite-order l1 pair gradient at any point. |

The page-21 scalar duality statement explicitly assumes finite p and is
preserved. The page-22 gradient paragraph must carry that restriction if
it is read as a full-dual claim. At the infinity endpoint, coefficient
representability is an additional condition; analyticity does not imply it.
The same issue constrains the later automatic Poisson-regularity sentence
when one functional has infinity as its source exponent.

## Sobolev Poisson bracket on common physical states

The positive automatic-regularity statement is proved when both conjugate
source exponents are finite, for every real Sobolev order. The common-state
domain is the full intersection of the two original coefficient spaces,
with their original norms; it is not restricted to smooth or Hilbert inputs.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Physical matrix and sign | `NLS.Poisson.signedBivector_physical`, `signedJ_physical` | The printed -iJ formula; the first signed component is reflected to obtain physical scalar coefficients. |
| Absolutely convergent signed formula | `NLS.Poisson.summable_signed_cross`, `signedBivector_eq_tsum` | All real orders and conjugate gradient exponents, including either endpoint; cross-component products use equal signed indices. |
| Core antisymmetry | `NLS.Poisson.signedBivector_antisymm` | Swapped orders and exponents, with explicit coefficient-preserving transport from order -(-s) to s. |
| Complete intersection | `NLS.Poisson.SobolevCommonState`, `commonStateOfCoefficients`, `norm_commonState` | A closed Banach subspace; every equal-coefficient pair is admitted. At finite exponents its norm is the maximum of the two original source norms. |
| Actual shared physical state | `NLS.Poisson.commonState_distribution_eq` | Both representatives synthesize the same actual pair of periodic distributions, at every positive period. |
| Full ambient differentials | `NLS.Poisson.commonLeftGradient_represents`, `commonRightGradient_represents` | Each gradient represents the differential on every direction of its own complete ambient domain. |
| Automatic bracket regularity | `NLS.Poisson.commonSobolevBracket_summable`, `commonSobolevBracket_physical`, `commonSobolevBracket_eq_tsum` | Both conjugate source exponents finite, all real orders, and the same common base point; no additional Hilbert premise. |
| Original operator norm bound | `NLS.Poisson.norm_commonSobolevBracket_le` | Twice the product of the two original differential norms. |
| Analyticity on the intersection | `NLS.Poisson.analyticOnNhd_commonSobolevBracket` | The entire intersection of the functionals' analytic domains. |
| Product rule | `NLS.Poisson.commonSobolevBracket_mul_left` | Left Leibniz rule under differentiability of the two left-domain factors. |
| Represented endpoint gradients | `NLS.Poisson.oneInfinityBivector_summable`, `norm_oneInfinityBivector_le`, `analyticOnNhd_oneInfinityBivector` | Original l1 and frequencywise sum-norm infinity pair spaces; bounded, absolutely convergent pairing and analyticity for supplied analytic gradient fields. |

The same-index cross-component sum here is a consequence of the opposite
signs in the source pair basis. It does not restore the erroneous preceding
same-index scalar physical pairing. The physical formula explicitly uses
that scalar pairing with the necessary first-component reflections.

The endpoint result supplies a pairing for represented gradients, not a
full-dual representation theorem for infinity-source analytic functionals.
The common-state bracket with automatically recovered gradients requires
both source exponents to be finite. The auxiliary common-state type at
infinity uses a product maximum norm and is not claimed to carry the
source's distinct infinity pair norm; the endpoint API uses the separate
`WeightedCoeffPairInfty` type.

Next: prove compatibility with the existing physical `SourceBracket`
interface and finish the remaining bracket algebra/domain audit, then
continue with numbered Section 3. Core antisymmetry and the left product
rule are not a full Sobolev bracket Jacobi theorem. The candidate inventory
and these maps do not establish completeness of these obligations.
