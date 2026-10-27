# Section 4: Dirichlet and Neumann spectra

This is a statement-by-statement audit against the original spaces and
physical expressions on printed pages 28 onward. Existing later results do
not by themselves certify this section or the full dissertation complete.

## Complete Section 4 assertion inventory

The entire passage on printed pp.28–33 has been compared in 38 ordered
groups, with all six rendered pages inspected. The evidence record covers
definitions, statements, displayed formulas and substantive proof steps.
Intervening display fragments and transitions were reconciled with the
adjacent groups.

| Passage | Assessment retained by the inventory |
| --- | --- |
| Original domains and AKNS coordinates | Actual closed-interval H1 functions, dense physical L2 inclusion, both signed endpoint problems, and exact differential expressions. The printed potential normalization is refuted and corrected. |
| Reflections and Lemma 4.1 | Actual folded functions, required endpoint traces, periodic H1 representatives, physical equations and spectral inclusion/exhaustion. |
| Fourier expansions and boundary spaces | Normalized physical integrals and complete L2 sums; closed weighted complements with finite-p and distinct infinity norms. |
| Lemma 4.2 and scalar restrictions | Full original domains, literal sine/cosine series and normalized T formulas; continuous scalar restriction inverses with physical H1 norms. |
| Lemma 4.3 | Original native distributions, exact norms, full signed series, bounded analytic reflection for 1<p<infinity and corrected even/odd formulas on all rough inputs. Both printed coefficient constants remain refuted. |
| Lemma 4.4 and restricted spectra | Actual full-domain invariance, convergent signed potential action and bounded restrictions; the Sobolev embedding constant is retained. |
| Theorem 1.4 proof and labels | Actual analytic contour restrictions, domain-valued ranges, full Jordan multiplicities, common-neighborhood counts and complete ordered labels. Counts use height-N boxes. |
| Lemma 4.5 | Intrinsic rank-one trace and local analytic range transport; p=1 uses the same continuous physical potential in the Hilbert realization. |

The three local formula refutations are distinct from their proved
corrections. The FL1 wording in Lemma 4.3's proof does not replace its
FLp input norm. No bounded endpoint reflection or infinity-norm Fourier
convergence is asserted. The p=1 eigenvalue conclusion retains the
classical Hilbert realization and its multiplicity convention.

The previously refuted unrestricted height in Theorem 1.4 and missing
product constant in Appendix A.8 remain qualified. The latter still gives
the valid embedding and boundedness inference after retaining its constant.
The scalar restriction proof establishes the assertion cited to [54]
directly, without independently auditing the textbook. Earlier checkpoints
below retain their historical scopes; their pending-work wording does not
supersede this qualified inventory.

Section4AssertionInventorySourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records the 38 groups,
60 reviewed module hashes and 236 resolved declaration references.
This inventory covers Section 4 and does not certify the entire chapter
or dissertation. Its Lean sources match the full validation at `1e93351`;
this documentation update does not rerun Lean.

## Signed series and Lemma 4.3 on original distributions

The proof on printed p.31 now has direct interfaces on the original
periodic smooth-test distributions with the exact finite-p component-sum norm.

| Source assertion | Entry point | Exact scope |
| --- | --- | --- |
| Original signed coefficients and norm | [SourcePeriodOneSignedSeries.lean](../NLS/ZakharovShabat/SourcePeriodOneSignedSeries.lean), `sourceUnitPeriodSignedCoefficients`, `norm_sourceUnitPeriodSignedCoefficients` | Linear isometry equivalence; opposite signed directions and the exact sum of both coefficient energies. |
| Full signed expansion | `hasSum_sourceUnitPeriodSignedModes`, `sourceUnitPeriodSignedMode_physical` | Every native finite-p input, norm convergence of the entire integer-indexed series, and actual physical exponential modes. |
| Actual boundary space and analytic reflection | [SourceLemma43NativeExtension.lean](../NLS/ZakharovShabat/SourceLemma43NativeExtension.lean), `sourceNativeIntervalExtension`, `analyticAt_sourceNativeIntervalExtension` | Closed native period-two boundary space; bounded and analytic for 1<p<infinity. |
| Physical-mode agreement and uniqueness | `sourceNativeIntervalExtension_mode_integrals`, `sourceNativeIntervalExtension_unique` | Normalized physical integrals on every signed mode determine the entire continuous extension. |
| Full reflected expansion | `hasSum_sourceNativeIntervalExtension`, `sourceNativeIntervalExtension_tempered` | Convergence in the actual target norm and equality with the established tempered realization. |
| Corrected even formula | `sourceNativeIntervalExtension_even` | Half of the signed component sum for every rough input. |
| Corrected odd formula | `hasSum_sourceNativeIntervalExtension_odd` | Full series with kernel i/(pi*(2k-2n-1)), for every rough input. |
| Original Hilbert norm | `norm_sourceNativeIntervalExtension_two` | Exact preservation of the original norm at p=2. |

The missing even factor one half, the printed odd 2i normalization and
the FL^1 wording retain their earlier corrections or qualifications. The
full signed source expansion also holds at p=1; the bounded reflection
theorem requires 1<p<infinity. No endpoint reflection bound is claimed.
The auxiliary WithLp product at infinity is not the source's coupled norm.

Four examples check a negative signed mode, the Dirichlet and Neumann
constant amplitudes, the odd coefficient -i/pi, and exact Fourier energy
for arbitrary Hilbert inputs.

Section4SignedNativeSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records six focused groups.
The local series and extension proof bodies were compared; this does not
claim a fresh audit of every transitive Hilbert-transform theorem.
Section 4 and the dissertation-wide assertion inventory remain unfinished.

Validation passes: 8,446 build jobs, 7,510 public examples and a
transitive axiom audit of 43,246 NLS declarations. The 21 inherited
warnings are unchanged; the new modules and examples introduce none.

## Physical scalar restrictions in Lemma 4.2

The scalar restriction assertions on printed pp.30–31 now have explicit
continuous linear equivalences on actual functions, with physical H1 norms.

| Source object or assertion | Entry point | Exact scope |
| --- | --- | --- |
| Original H1 and zero-trace H1 | [SourceScalarIntervalH1.lean](../NLS/ZakharovShabat/SourceScalarIntervalH1.lean), `mem_sourceScalarIntervalSubmodule` | Actual functions on [0,1], with no periodicity condition; both zero traces only in the sine case. |
| Physical interval norm | `norm_sourceScalarH1OfFunction` | Square root of ordinary Lebesgue function plus actual derivative energy. |
| Amplitude restriction and product | [SourceLemma42ScalarRestriction.lean](../NLS/ZakharovShabat/SourceLemma42ScalarRestriction.lean) | Full even/odd weighted amplitude spaces, continuous inverses and exact closed-interval values. |
| Actual periodic sine/cosine spaces | [SourceLemma42PhysicalRestriction.lean](../NLS/ZakharovShabat/SourceLemma42PhysicalRestriction.lean), `mem_sourceCosinePeriodic_iff`, `mem_sourceSinePeriodic_iff` | Actual continuous periodic functions represented by the full signed series; every element has classical H1 regularity. |
| Physical periodic norm | `norm_sourceTrigPeriodicH1`, `sourceTrigPeriodic_norm_bounds` | Exact Lebesgue H1 norm on [0,2], with explicit bounds against the amplitude norm. |
| Printed scalar restrictions | `sourcePhysicalCosineRestriction`, `sourcePhysicalSineRestriction` and their `_apply` theorems | Continuous linear equivalences onto the full scalar interval spaces; action is literal restriction at every closed-interval point. |
| Product identity through T | `sourcePhysicalTrigClassicalEquiv`, `sourcePhysicalTrigClassicalEquiv_apply` | Entire original Dirichlet domain and exact normalized pointwise transform. |

This supplies the separate R_cos and R_sin maps absent from the preceding
Fourier milestone. It proves the asserted isomorphisms directly using the
established boundary restriction and Sobolev energy results; it does not
claim a separate review of textbook reference [54]. The physical norms
retain their period lengths. Neither the amplitude norm nor the product
maximum norm is asserted identical to the corresponding physical norm.

Four examples check a ramp with unequal endpoint values, its exclusion
from the sine target, its exact norm sqrt(4/3), and periodic sine extension
of every original zero-trace H1 function without extra smoothness.

Section4ScalarRestrictionSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups.
Section 4 and the dissertation-wide assertion inventory remain unfinished.

Validation passes: 8,444 build jobs, 7,506 public examples and a
transitive axiom audit of 43,202 NLS declarations. The 21 inherited
warnings are unchanged; the new modules and examples introduce none.

## Sine/cosine calculations in the proof of Lemma 4.2

[SourceLemma42FourierProof.lean](../NLS/ZakharovShabat/SourceLemma42FourierProof.lean)
exposes the literal Fourier calculations on printed pp.30–31.

| Source step | Entry point | Scope |
| --- | --- | --- |
| Actual trigonometric modes | `sourceCosineMode_apply`, `sourceSineMode_apply` | Exact cos(n*pi*x) and sin(n*pi*x), including negative indices. |
| Full convergent series | `hasSum_sourceCosineSynthesis`, `hasSum_sourceSineSynthesis` | Unconditional uniform-norm convergence for all finite p with one Fourier derivative. |
| Classical regularity and endpoints | `sourceTrigSynthesis_periodicH1`, `sourceSineSynthesis_endpoints` | Actual periodic H1 at p=2; both zero traces for odd sine amplitudes. |
| Continuous coordinate equivalence | `sourceBoundaryTrigEquiv`, `sourceBoundaryTrigSourceEquiv` | The entire even/odd amplitude product and original Dirichlet boundary space. |
| Literal T and inverse | `sourceBoundaryTrig_forward`, `sourceBoundaryTrig_inverse`, `sourceBoundaryCosineAmplitude_apply`, `sourceBoundarySineAmplitude_apply` | Forward amplitude (b-a)/sqrt(2), inverse amplitudes (f_n+f_-n)/sqrt(2) and (-f_n+f_-n)/sqrt(2), with pointwise physical identification. |
| Neumann analogue | `sourceBoundaryTrigNeumannSourceEquiv`, `sourceBoundaryTrig_neumann_forward` | Entire original Neumann space, with the exact swapped sine/cosine phases. |
| Full classical domains | `sourceBoundaryTrigClassicalEquiv`, `sourceBoundaryTrigNeumannClassicalEquiv` and their `_apply` theorems | Continuous equivalences onto both actual closed-interval H1 domains, preserving every physical value including endpoints. |

The last step composes with the previously proved physical restriction
maps. That milestone proved the product-domain conclusion; the subsequent
physical scalar restriction construction above supplies the separate
R_sin and R_cos equivalences. Reference [54] is not independently audited.
No finite-support input or extra endpoint periodicity is assumed. The product amplitude norm is not asserted to be isometric to
the original pair norm. The existing AKNS potential-normalization and
Lemma 4.3 coefficient corrections remain unchanged.

Four integration examples check a negative-frequency sine value, both
reflected coefficients of a complex single mode, representation of every
original classical-domain function for either boundary condition, and
uniform convergence of the inverse series at p=3.

Section4FourierProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups.
This does not certify every assertion in Section 4.

Validation passes: 8,441 build jobs, 7,502 public examples and a
transitive axiom audit of 43,038 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

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

## Smooth input can lose one derivative under reflection (page 31)

The unnumbered paragraph before Lemma 4.3 warns that a smooth period-one
potential can have a reflected extension outside the one-derivative
Fourier–Lebesgue space. The constant physical potential (0,1) proves this
for both reflection signs and every finite Banach exponent.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Smooth periodic input | `reflection_oneSided_source_regular`, `sourceReflectionConstantInput_physical` | The finite coefficient input is literally the smooth period-one constant (0,1). |
| Every input regularity order | `sourceReflectionConstantInput_has_all_orders` | Original component-sum weighted pair, every real order and Banach exponent. |
| Actual reflected Fourier integrals | `intervalExtension_oneSided_sobolev_one_iff` | The second component's order-one weighted coefficients lie in scalar ℓp exactly when p=infinity. |
| No finite-exponent pair representative | `intervalExtension_oneSided_no_oneDerivative_pair` | No original one-derivative pair has both actual normalized reflected Fourier coefficients. |
| Completed extension loses regularity | `sourceReflectionConstantInput_amplitude`, `sourceIntervalExtension_oneSided_not_oneDerivative` | The actual Lemma 4.3 map retains the physical coefficients and fails to preserve order one, for 1<p<infinity. |
| Original smooth-test distribution | `sourceReflectionConstantDistribution_coefficient`, `sourceReflectionConstantDistribution_sobolev_one_iff` | Exact normalized distributional coefficients; scalar order-one membership holds exactly at target exponent infinity. |

These entries are in
[SourceReflectionRegularityLoss.lean](../NLS/ZakharovShabat/SourceReflectionRegularityLoss.lean).
The proof uses the reflected constant's reciprocal odd Fourier tail.
One derivative leaves bounded coefficients that cannot belong to any
finite Banach exponent. The distributional conclusion uses the original
period-two smooth-test space and permits the source and target exponents
to differ. The infinity statement concerns scalar membership; it does
not identify different pair norms or extend the completed reflection map
to an endpoint exponent. No threshold for arbitrary fractional orders is
asserted.

Three public examples check both signs in the physical H¹ obstruction,
arbitrary input order with loss at p=4, and a single completed distribution
that separates finite target exponents from infinity. This confirms the
printed warning and adds no source correction.

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

## Lemma 4.5: original trace and the finite-exponent endpoint (page 33)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Actual boundary projector in the ambient source space | `sourceBoundaryAmbientCircleProjection` | Original normalized circle integral followed by the boundary projection. |
| Original operator-domain lift | `sourceBoundaryAmbientContourLift_mem`, `sourceBoundaryAmbientContourLift_inclusion`, `sourceBoundaryAmbientContourLift_range` | The lift belongs to the original weighted boundary domain and represents the spectral vector itself. |
| Typed range identification | `sourceBoundaryContourRangeEquiv` | Isometry between the typed boundary-projector range and the ambient boundary range used for trace. |
| Actual operator on the range | `sourceBoundaryContourRestriction_apply` | Intrinsic endomorphism acts by the original source operator on its domain lift. |
| Intrinsic trace formula | `sourceBoundaryContourTrace_eq_trace_restriction`, `sourceBoundaryContourTrace_eq` | The actual finite restriction has the coefficient-theory trace, by continuous conjugation. |
| Rank-one trace equals eigenvalue | `sourceBoundaryContourTrace_eq_of_rank_one` | Any admissible circle with rank one and an enclosed original eigenvalue. |
| Trace-defined high branches | `sourceBoundaryEigenvalue`, `sourceBoundaryEigenvalue_eq_periodOne` | Original trace agrees with the existing period-one branch on admissible high circles. |
| Analyticity in the original norm | `analyticAt_sourceBoundaryContourTrace`, `analyticAt_sourceBoundaryEigenvalue` | Complex analytic after the completed original interval extension, 1<p<infinity. |
| Common neighborhood and simple spectrum | `sourceLemma4_5`, `sourceBoundaryEigenvalue_spec` | Both signs, all high signed indices, singleton disks and original algebraic multiplicity one. |
| Continuous physical p=1 input | `sourceOnePhysicalPotential`, `continuous_sourceOnePhysicalPotential` | Absolute Fourier summability gives the actual period-one interval potential. |
| Coefficient-preserving Hilbert inclusion | `sourceOneToHilbert_coefficients` | The bounded inclusion gives exactly the physical unit-interval L² coefficients. |
| Actual physical reflected potential | `sourceOneToHilbert_reflected` | The completed Hilbert reflection equals the actual Dirichlet-reflected physical coefficients. |
| Classical endpoint spectrum | `sourceOneBoundarySpectrum_eq_classical` | Equality with the original interval differential equation and boundary conditions. |
| Printed p=1 analytic conclusion | `sourceLemma4_5_one` | Open convex connected neighborhood in the original p=1 norm; analytic trace branches, singleton classical eigenvalue disks, Hilbert-realization multiplicity one. |

The main entries are in `NLS.ZakharovShabat.SourceLemma4_5` and
`NLS.ZakharovShabat.SourceLemma4_5Endpoint`. The trace is independent of
any chosen basis or reference projection. The range equivalence preserves
the original norm; the separate equivalence to maximum-norm coefficients
is not asserted to be an isometry.

The strict-exponent theorem and the separate endpoint theorem cover the
printed range 1<=p<infinity. For p=1 the realization is explicitly the
classical Hilbert boundary problem for the same continuous potential.
No bounded interval-reflection map into the period-two p=1 space or trace
on that unavailable realization is inferred. The original-p=1 analytic
conclusion follows by bounded pullback, with physical spectrum equality
proved rather than assumed. No change to the printed trace normalization
or analytic conclusion is needed. The prior height qualifications remain.

Public checks include the actual operator and lift, both range realizations,
intrinsic trace, rank-one identification, all strict finite exponents,
a concrete exponent above two, negative high indices, coefficient and
physical-spectrum identification at p=1, and the full endpoint statement.

## Next source assertions

The physical auxiliary boundary conditions (1.10), phase-twisted
reflections, Lemma 5.1, and Fourier expansions (1.11)–(1.12) are recorded
in the [Section 5 audit](SECTION_5.md). Those constructions retain the
distinct Neumann-reflected potential and both auxiliary boundary signs.
