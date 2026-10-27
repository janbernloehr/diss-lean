# Section 2: convergence, duality, gradients, and Poisson pairing

This records the Fourier-Lebesgue-space statements on printed pages 21–22,
checked against the rendered source. The maps below identify proved scope
and endpoint corrections. The bracket results below retain their explicit domain restrictions;
this file is not a completeness certificate for the dissertation.

The renewed comparison covers the definitions and assertions throughout
Section 2, including the signed pair basis, both pair norms, full finite-source
gradients, and the physical Poisson formula. Its twelve assertion groups and
31 reviewed module hashes are recorded as
`Section2SourceComparison-2026-10-27` in the
[source-comparison snapshot](source-review-index.json). The three source
corrections remain explicit: norm convergence at infinity, the scalar bilinear
Fourier index, and gradient representation at infinity. The final notation
conventions specialize the existing definitions to order zero and period one.

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

## Duality on the original distribution spaces

[`PeriodicSobolevDuality.lean`](../NLS/Fourier/PeriodicSobolevDuality.lean)
packages the full scalar duality directly on `FourierLebesgueSpace L s p`,
whose elements are continuous functionals on the original smooth periodic
tests. For every positive period, real order and finite source exponent,
`sobolevDualIsometry` identifies its entire continuous dual with
`FourierLebesgueSpace L (-s) q`, with exact operator-norm equality.
`existsUnique_sobolevRepresentative` states uniqueness among actual
periodic distributions and includes the p=1, q=infinity endpoint.

The absolutely convergent formula uses opposite Fourier indices.
`sobolevDualIsometry_ofSmooth` identifies evaluation on a smooth input
with the representative's original distributional action; the two-smooth-input
identity gives exactly `(1/L) * integral(g*f)`. Public examples also check
negative fractional order and the singular point-evaluation representative
at p=1. The source-infinity full-dual obstruction remains unchanged.

The underlying original-distribution carrier, coefficient isometry,
completeness, canonical double-dual surjectivity and physical Fourier
polynomial identification were rechecked in this comparison. Completeness
covers every Banach exponent; reflexivity retains 1<p<infinity. These
statements use the coefficient norm on actual distributions, rather than
assuming completeness in the distribution topology.

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

## Native physical Hilbert gradients

At p=2 the representation now also holds directly on the ordinary
unit-interval physical L2 pair space, with its original Hilbert norm.
[`PhysicalL2BilinearPairing.lean`](../NLS/ZakharovShabat/PhysicalL2BilinearPairing.lean)
proves integrability of arbitrary L2 products, the exact reflected Fourier
pairing, and separation of physical pairs by all L2 directions.
[`PhysicalCotangentGradient.lean`](../NLS/ZakharovShabat/PhysicalCotangentGradient.lean)
constructs the unique physical gradient of every continuous complex
cotangent and proves its integral representation on every direction.
The literal cross-gradient integral equals the source bivector, retaining
minus i and the frequency reversal of unconjugated physical duality.
[`PhysicalPoissonBracket.lean`](../NLS/ZakharovShabat/PhysicalPoissonBracket.lean)
then uses actual full complex differentials and proves the Fourier pullback
identity, antisymmetry, and the opposite-frequency coordinate check.
These results require neither continuous representatives nor endpoint
matching. They concern the Hilbert exponent and do not remove the infinity
obstruction above.

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

## Bracket compatibility and algebra

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Actual coordinate equivalence | `NLS.Poisson.zeroOrderPhysicalEquiv`, `zeroOrderPhysicalEquiv_inl_mode`, `zeroOrderPhysicalEquiv_inr_mode` | Order zero; first signed component reverses frequency, second component retains it. This is a continuous linear equivalence of the whole source spaces. |
| Complete differential mode formula | `NLS.Poisson.conjugateBivector_eq_tsum` | Every real order and finite conjugate source pair; the formula evaluates the complete functionals on the original signed mode directions. |
| Compatibility with existing cotangent pairing | `NLS.Poisson.conjugateBivector_zero_source_restrict` | Order zero, arbitrary finite conjugate p,q, and an ambient r>=2 with p,q<=r. Both full functionals come from that ambient space; no finite-support assumption. |
| Same ambient physical base point | `NLS.Poisson.zeroOrderSourceMap_common` | Every point of the common-state domain has equal physical images under the two original exponent inclusions. |
| Actual bracket agreement | `NLS.Poisson.commonSobolevBracket_zero_source` | The full common-state bracket equals the existing `sourceBracket` at that physical base point, under differentiability of the ambient functionals. |
| Exchange of source domains | `NLS.Poisson.negNegPairEquiv`, `swapCommonState` | All real orders; double-negative order normalization preserves every signed coefficient and swapping retains the same physical state. |
| Full common-domain antisymmetry | `NLS.Poisson.conjugateBivector_swap`, `commonSobolevBracket_swap` | All real orders and finite conjugate pairs, with the functionals, domains, and state explicitly exchanged. |
| Both common-domain product rules | `NLS.Poisson.commonSobolevBracket_mul_left`, `commonSobolevBracket_mul_right` | Differentiable factors in their respective full ambient domains. |
| Single-domain full-gradient bracket | `NLS.Poisson.zeroOrderBracket`, `zeroOrderBracket_source`, `commonSobolevBracket_zeroOrderBracket` | Order zero and exponent two; agrees with both the new common-state and established physical source brackets. |
| Analytic closure and Jacobi | `NLS.Poisson.analyticOnNhd_zeroOrderBracket`, `zeroOrderBracket_jacobi` | Analyticity on the original order-zero Hilbert domain; Jacobi for arbitrary functionals analytic at the base point. |
| Algebra on the Hilbert domain | `NLS.Poisson.zeroOrderBracket_antisymm`, `zeroOrderBracket_mul_left`, `zeroOrderBracket_mul_right`, `zeroOrderBracket_add_left`, `zeroOrderBracket_smul_left` | Antisymmetry, both product rules, differentiable left additivity, and scalar homogeneity including zero. |

The general comparison uses finite p,q. Its legacy ambient type at
r=infinity has the existing maximum pair norm; agreement of its finite
restrictions does not establish full gradient representation in the source's
distinct infinity pair norm. The original endpoint obstruction is unchanged.

The weighted `zeroOrderBracket_jacobi` theorem uses a single order-zero
Hilbert domain. The existing `sourceBracket_jacobi` also covers source
exponents p>=2; its infinity case uses the legacy maximum pair norm.
Neither result asserts closure of arbitrary nested brackets on reciprocal
Sobolev intersections with the source's norms.
The page-22 automatic-regularity assertion only supplies a pairing when the
two gradient domains are dual; the proved positive assertion and its endpoint
restriction are recorded above.

## Full weighted sesquilinear product

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Physical conjugation | `NLS.WeightedCoeff.sobolevConjugation`, `sobolevConjugation_apply` | A conjugate-linear isometric involution at every real order and Banach exponent, including infinity; coefficients conjugate and reverse index. |
| Printed scalar sesquilinear sum | `NLS.WeightedCoeff.sobolevSesquilinearPairing_apply`, `summable_norm_sobolevSesquilinearPairing` | Same-index product with conjugated second coefficient, absolutely convergent for every conjugate pair, including both endpoints. |
| Scalar bound and topology | `NLS.WeightedCoeff.norm_sobolevSesquilinearPairing_le`, `continuous_sobolevSesquilinearPairing`, `sobolevSesquilinearLeft`, `sobolevSesquilinearRight` | Constant-one bound and joint continuity; bundled bounded linear first-variable and conjugate-linear second-variable functionals. |
| Relation to the corrected physical product | `NLS.WeightedCoeff.sobolevSesquilinearPairing_conjugation`, `sobolevSesquilinearPairing_reflection` | Conjugating the second physical function recovers the opposite-index bilinear product; reflecting both factors preserves the product. |
| Original finite pair product | `NLS.WeightedCoeffPair.sobolevSesquilinearPairing_eq_tsum`, `norm_sobolevSesquilinearPairing_le_one`, `continuous_sobolevSesquilinearPairing` | Finite conjugate p,q, original component-sum norms, constant-one bound, absolute convergence, and joint continuity. |
| Original infinity-first endpoint | `NLS.WeightedCoeffPairInfty.sobolevSesquilinearPairing`, `norm_sobolevSesquilinearPairing_le`, `continuous_sobolevSesquilinearPairing` | Infinity against one, with the actual frequencywise sum infinity norm and constant-one bound; absolute convergence and joint continuity. |
| Original infinity-second endpoint | `NLS.WeightedCoeffPair.sobolevSesquilinearOneInfinity`, `norm_sobolevSesquilinearOneInfinity_le`, `continuous_sobolevSesquilinearOneInfinity` | One against infinity, with the actual infinity norm and constant-one bound; absolute convergence and joint continuity. |
| Signed pair physical fidelity | `NLS.WeightedCoeffPair.sobolevSesquilinearPairing_physical`, `sobolevSesquilinearOneInfinity_physical`, `NLS.WeightedCoeffPairInfty.sobolevSesquilinearPairing_physical` | Reflection of the first signed component in both factors gives the scalar physical convention, including the original endpoint types. |
| Entire scalar dual under this convention | `NLS.WeightedCoeff.sobolevSesquilinearRiesz`, `existsUnique_sobolevSesquilinearRepresentative`, `norm_sobolevSesquilinearRiesz` | Every real order and finite source exponent including one; a conjugate-linear isometry with unique representation on the full ambient space. |
| Exact Riesz phase and frequency | `NLS.WeightedCoeff.sobolevSesquilinearRiesz_smul`, `sobolevSesquilinearRiesz_val` | Scalars conjugate in the representative; its coefficient at n equals the conjugate of the functional on the original mode n. |
| Endpoint limitation retained | `NLS.WeightedCoeff.exists_analytic_sobolev_without_sesquilinearRepresentative` | At every real order there is an everywhere-analytic infinity-source functional whose derivative has no l1 representative in the sesquilinear convention. |
| Actual distributional meaning | `NLS.Fourier.periodicDistribution_sobolevSesquilinearPairing`, `existsUnique_sesquilinear_smooth_test` | Every positive period, real order, and conjugate pair including endpoints; action on a conjugated smooth periodic test with the original normalized window. Every such test supplies its unique coefficients. |
| Physical L2 normalization | `NLS.Fourier.sobolevSesquilinearPairing_eq_intervalIntegral` | The same coefficient pairing equals (1/L) times the integral of f times the conjugate of g for square-integrable physical inputs at every positive period. |

The product is complex linear in the first variable and conjugate linear
in the second. Its full Riesz representative is therefore conjugate linear
in the functional; it is not asserted to be a complex-analytic gradient
map. The bilinear gradient convention and its analytic theorems remain
unchanged. Auxiliary maximum products are used only for continuity; endpoint
bounds and formulas explicitly use the original infinity pair space.

## Locally integrable periodic action

The normalized action on page 21 now follows from interval integrability
alone. Local integrability supplies this hypothesis on every fundamental
interval. For periodic input this gives its periodic smooth-test action;
for arbitrary interval input the construction realizes its periodic extension.

| Requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Bounded action on continuous circle tests | `NLS.Fourier.periodicL1Functional`, `norm_periodicL1Functional_le` | Any L>0 and interval-integrable complex input; operator norm bounded by the normalized L1 norm. |
| Actual bounded coefficients | `periodicL1Coefficients`, `norm_periodicL1Coefficients_le` | The original normalized integral coefficients belong to the zero-order infinity space with the same bound. |
| Physical product series | `hasSum_periodicL1_pairing`, `tsum_periodicL1_pairing`, `summable_norm_periodicL1_pairing` | Every smooth periodic test; opposite indices, absolute convergence, and the exact 1/L integral. |
| Actual periodic distribution | `periodicL1Distribution_periodic`, `periodicL1Distribution_coefficient` | A genuine tempered distribution with the required period and actual coefficients. |
| Normalized smooth-test action | `periodicL1Distribution_smooth_action`, `locallyIntegrable_periodic_smooth_action` | Windowed periodic action equals the normalized physical integral, with no L2 or bounded-input premise. |
| Uniqueness and almost-everywhere invariance | `existsUnique_periodicL1Distribution`, `periodicL1Distribution_congr_ae` | Unique among actual periodic distributions with these coefficients; unchanged by almost-everywhere modifications on the fundamental interval. |
| Sesquilinear action | `periodicL1Distribution_sesquilinear_action` | The same normalized action with the smooth test conjugated. |

The proof applies the bounded integral functional to uniform Fourier
convergence of the smooth test and then uses the established distributional
coefficient identification. It proves the normalized periodic action stated
in Section 2; it does not add a global real-line integration theorem for
arbitrary Schwartz tests.

The numbered Section 3 audit now starts with Proposition 3.1 in
[SECTION_3.md](SECTION_3.md), retaining the printed-height qualification.
The candidate inventory and these maps are not a completeness certificate
for the dissertation.

## Native physical Hamiltonian directions

[`PhysicalPoissonAlgebra.lean`](../NLS/ZakharovShabat/PhysicalPoissonAlgebra.lean)
proves complex bilinearity of the literal cotangent bivector.
[`PhysicalHamiltonianDirection.lean`](../NLS/ZakharovShabat/PhysicalHamiltonianDirection.lean)
defines the native L2 direction by (-i grad_2, i grad_1), proves that every
cotangent evaluates on it to the literal integral bracket, and identifies
it with the exact Fourier realization of the source direction. A functional
that is complex differentiable and real on the physical real form has a
Hamiltonian field tangent to that real form. No regularity beyond the stated
differentiability is imposed; this does not prove a flow exists.
