# Section 23: estimates for the original Birkhoff map

This audit concerns printed pp. 103–106. Theorems 23.1, 23.2, and 23.4,
Remark 23.3, and Corollary 23.5 now hold for one retained original
Sections 17–22 family. The exact norms and indexed actions are retained.
The opening Sobolev diffeomorphism assertion also follows from the
native weighted inverse results below. The cited one-smoothing property
is a separate assertion, and the higher-action outline has the source
corrections recorded in Section 24.

## One original map and exact norms

[`sourceSection23_original_estimates`](../NLS/ZakharovShabat/SourceSection23Original.lean)
chooses the original Birkhoff data D, moment atlas A, and source domain U
once, before any order, weight, or potential. `SourceSection23Data`
extends the same Section 20 package, so the original Section 22 physical
solution theory remains available. `SourceSection20Data.section23`
also adds the estimates to any already chosen original family.

[`SourceSection23Actions.lean`](../NLS/ZakharovShabat/SourceSection23Actions.lean)
identifies the original indexed actions with the complex contour actions
throughout the original complex Birkhoff domain. It proves the opening
Parseval identity for the component-sum Hilbert target norm.

Weighted source coordinates are normalized by dividing each Fourier
component by w(2n). `normalizedWeightedSource_physical_norm` proves both
absolute summability and the exact equality between the normalized
coordinate norm squared and the literal weighted Fourier energy of both
decoded components. For integer Sobolev order the weight is
⟨2nπ⟩ᵐ, where ⟨x⟩ = 1 + |x|. Both weighted target components are the
original Birkhoff components multiplied by that same weight.

`section23_sobolev_norm_sq` and `section23_weighted_norm_sq` identify the
target norm squared with twice the absolutely convergent weighted sum of
the original indexed actions. The integer identity holds at every lower
order k ≤ m, including k = 0. No maximum-product norm replaces the
component-sum norm in these statements.

## Sobolev geometry of the same original map

The later
[`SourceBirkhoffSobolevGlobalInverse.lean`](../NLS/ZakharovShabat/SourceBirkhoffSobolevGlobalInverse.lean)
applies to the already chosen D.complex. At p=2 and every real t>=0,
`originalWeightedRealSobolevHomeomorph` is the original map in its
native weighted source and target norms. Both it and its inverse are
real analytic on their entire spaces; the inverse's strict derivative
is the actual bounded inverse Jacobian. The result includes t=0 and
fractional orders, and does not choose a new Birkhoff family.

[`SourceBirkhoffWeightedCanonical.lean`](../NLS/ZakharovShabat/SourceBirkhoffWeightedCanonical.lean)
identifies the scalar extensions with that same map's raw coordinates
and proves all three canonical identities for their full weighted
derivatives. Together these results establish the opening canonical
bi-analytic Sobolev diffeomorphism assertion independently of the norm
estimates. The precise comparison with the published 2014 construction
is still qualified in [Section 14](SECTION_14.md).

## Named estimates

| Source assertion | Public entry point | Exact scope |
| --- | --- | --- |
| Theorem 23.1(i) | `SourceSection23SobolevBounds.birkhoff_upper` | Every integer m ≥ 1; highest source Sobolev norm plus (1 + H¹ norm)²ᵐ times the L² norm. |
| Theorem 23.1(ii) | `SourceSection23SobolevBounds.birkhoff_lower` | Highest target norm plus (1 + target h¹ norm)⁴ᵐ⁻³ times the target h⁰ norm. |
| Theorem 23.2(i) | `SourceSection23SobolevBounds.action_upper` | Literal indexed action sum with weight ⟨2nπ⟩²ᵐ; squared constant and lower-order exponent 4m. |
| Theorem 23.2(ii) | `SourceSection23SobolevBounds.action_lower` | Squared source norm bounded by the order-m action sum plus (1 + order-one action sum)⁴ᵐ⁻³ times the order-zero action sum. |
| Remark 23.3 | `SourceSection17OriginalData.section23_sobolev_bounds` | One positive pair cₘ,dₘ for all four inequalities, chosen before the potential. |
| Theorem 23.4 | `SourceSection20Data.section23_weighted_neighborhood` | Every M₁ weight; one complex weighted neighborhood containing the whole real weighted locus, the absolute indexed action bound, and original weighted target membership and norm bound. The same positive constant 2048 works for both bounds. |
| Corollary 23.5 | `SourceSection20Data.section23_realSobolev_neighborhood` | Every real r ≥ 1, including fractional orders; exact physical weight ⟨2nπ⟩²ʳ and powers 4r and 2r, with the same positive constant in both bounds. |

The integer results are in
[`SourceSection23Sobolev.lean`](../NLS/ZakharovShabat/SourceSection23Sobolev.lean).
They transfer the proved two-sided estimates to the original family and
its indexed actions, retaining every source and target norm.

The weighted and real-order results are in
[`SourceSection23Weighted.lean`](../NLS/ZakharovShabat/SourceSection23Weighted.lean).
Each neighborhood is the previously proved weighted action neighborhood
intersected with the continuous decoder's preimage of U. It is open in
the normalized weighted source space and still contains every real
weighted source. Every decoded complex source lies in U, so the indexed
action identification holds throughout the asserted neighborhood. The
original domain U itself is unchanged. For real r ≥ 1, the constant is
`realSobolevEstimateConstant r = 2048 * (1 + 17π)^r`.

## Corrected weight-growth sentence

After Theorem 23.4, printed p. 105 claims w(m) ≤ w(0)^|m|. The actual
M₁ weight w(n) = 1 + |n| refutes this at m = 1. In
[`SpectralWeightGrowth.lean`](../NLS/SequenceSpaces/SpectralWeightGrowth.lean),
`section23_printed_geometric_bound_counterexample` proves this failure
and `SpectralWeight.le_geometric` proves

    w(n) ≤ w(0) * w(1)^|n|.

The prefactor also handles n = 0 without imposing w(0) = 1. Thus the
conclusion of at most exponential growth remains valid. This correction
does not change Theorem 23.4 or Corollary 23.5. See
[source discrepancies](../SOURCE_ERRATA.md).

## Progress toward the separate one-smoothing assertion

[`SourceAngularBetaH1Decay.lean`](../NLS/ZakharovShabat/SourceAngularBetaH1Decay.lean)
proves locally uniform inverse-bracket decay for the actual angular
correction on every real H1 source. Real interlacing bounds the
Dirichlet-minus-midpoint term by half the periodic gap. The actual
weighted gap sequence, with its original even-frequency weight,
controls the reciprocal sum through
[`WeightedReciprocalDecay.lean`](../NLS/SequenceSpaces/WeightedReciprocalDecay.lean).
The zero mode and both signed tails are included.

[`SourceAngularBetaCompactBound.lean`](../NLS/ZakharovShabat/SourceAngularBetaCompactBound.lean)
uses a finite subcover and compactness of the normalized weighted decoder
to make the off-diagonal beta constant uniform on each physical H1 ball.
[`SourceAngularBetaH1BallBound.lean`](../NLS/ZakharovShabat/SourceAngularBetaH1BallBound.lean)
combines it with the proved global M1 gap estimate. The actual H1 gap
sequence and the full beta correction are consequently bounded uniformly
on every ball measured by `sourcePhysicalH1Coordinates`.

For any retained `SourceBirkhoffMapComplexData` family, the phase results in
[`SourceBirkhoffH1PhaseDecay.lean`](../NLS/ZakharovShabat/SourceBirkhoffH1PhaseDecay.lean)
and
[`SourceBirkhoffH1BallPhase.lean`](../NLS/ZakharovShabat/SourceBirkhoffH1BallPhase.lean)
prove, for all real sources of physical H1 norm at most R,

    (1+|n|)*|beta_n| <= K(R),
    (1+|n|)*|exp(t*i*beta_n)-1| <= |t|*K(R).

These hold for every signed index n and every real t, without a finite-gap
hypothesis. The correction and phase error are in every sequence exponent
q>1, including infinity. `beta_phase_multipliers_uniform_physical_H1_ball`
constructs multiplication by the exact phase error as a bounded
complex-linear map from h^r_p to h^(r+1)_p, with norm at most |t|*K(R),
for every real r and Banach p. These multiplier spaces use
`Weight.sobolev r`, namely (1+|n|)^r. The local version additionally
retains an open H1 neighborhood inside the original complex domain.

This supplies the beta-phase ingredient of the separate argument in
Kappeler, Schaad and Topalov's
[*Semi-linearity of the non-linear Fourier transform of the defocusing NLS equation*](https://arxiv.org/abs/1505.04455).
The proof uses the project's actual spectral quantities, without assuming
an external asymptotic theorem. The normalized-action decay is proved below. The remaining coordinate
asymptotics, the full Birkhoff-minus-Fourier derivative gain, and analyticity
into that stronger target are not established by the phase result.

## Normalization bounds and gap separation

[`SourceGapActionLowerBound.lean`](../NLS/ZakharovShabat/SourceGapActionLowerBound.lean)
proves the sharp inequality |gamma_n|² <= 4*|I_n| for the original canonical
quantities, at every real source and every finite p>1. Integration of the
actual positive finite-gap profile gives the inequality there; continuity
and finite-gap density give the full real statement. The final theorem
requires no supplied atlas or representation.

[`SourceNormalizedActionLowerBound.lean`](../NLS/ZakharovShabat/SourceNormalizedActionLowerBound.lean)
uses the exact action factorization on open gaps, then open-gap density,
to prove Re(rho_n) >= 1/4 including collapsed gaps. It identifies the actual
normalized root with sqrt(4*Re(rho_n)), proves Re(xi_n) >= 1 and
|xi_n^(-1)| <= 1, and bounds |xi_n-1| by |4*rho_n-1|/2.

[`SourceDiscIndexSeparation.lean`](../NLS/ZakharovShabat/SourceDiscIndexSeparation.lean)
extracts the common geometric argument used by the existing midpoint
estimate. [`SourceSegmentIndexSeparation.lean`](../NLS/ZakharovShabat/SourceSegmentIndexSeparation.lean)
applies it to every point of the actual periodic segments, on a complex
neighborhood of each real source. For distinct i and j, one constant gives

    |i-j| <= C*|w-z|,  z in gap_i, w in gap_j.

[`SourceSegmentCompactSeparation.lean`](../NLS/ZakharovShabat/SourceSegmentCompactSeparation.lean)
makes this constant uniform on compact real source sets and physical H1
balls. [`WeightedReciprocalSquareDecay.lean`](../NLS/SequenceSpaces/WeightedReciprocalSquareDecay.lean)
provides the complementary sum estimate: a two-derivative l1 majorant
controls the entire reciprocal-square sum at inverse-square-bracket rate.

## Uniform normalized-action and root decay

[`ReciprocalSquareDensityIntegral.lean`](../NLS/SequenceSpaces/ReciprocalSquareDensityIntegral.lean)
turns an l1 weighted density-mass majorant into joint integrability and an
inverse-square-bracket bound for the full index-angle integral.
[`SourceExteriorIndexDecay.lean`](../NLS/ZakharovShabat/SourceExteriorIndexDecay.lean)
uses the actual gap separation to dominate the exterior correction by
that integral. [`SourceH1WeightedActionSequence.lean`](../NLS/ZakharovShabat/SourceH1WeightedActionSequence.lean)
constructs the exact physical weighted action sequence, identifies its l1
norm with the literal sum, and bounds it uniformly on each physical H1 ball.

[`SineCorrectionActionUpperBound.lean`](../NLS/ComplexAnalysis/SineCorrectionActionUpperBound.lean)
and [`SourceProfileActionUpperBound.lean`](../NLS/ZakharovShabat/SourceProfileActionUpperBound.lean)
turn this correction bound into the finite-gap action-to-gap upper ratio.
The correction estimate itself includes infinitely many open gaps.
[`SourceSobolevOpenGapDensity.lean`](../NLS/ZakharovShabat/SourceSobolevOpenGapDensity.lean)
proves selected open gaps are dense in the H1 topology itself. Intersecting
this open dense set with the dense finite-gap locus allows division on the
approximants; continuity of the actual normalized action then includes
collapsed gaps without an infinite-gap profile identity.

The resulting public bounds in
[`SourceNormalizedActionH1Decay.lean`](../NLS/ZakharovShabat/SourceNormalizedActionH1Decay.lean)
are, for all real sources of physical H1 norm at most R and every signed n,

    (1+|n|)^2 * |4*rho_n-1| <= K(R),
    (1+|n|)^2 * |xi_n-1| <= K'(R).

[`SobolevPowerMultiplier.lean`](../NLS/SequenceSpaces/SobolevPowerMultiplier.lean)
converts a real power bound on a symbol into its exact bounded multiplier.
[`SourceNormalizedActionRootH1Multiplier.lean`](../NLS/ZakharovShabat/SourceNormalizedActionRootH1Multiplier.lean)
therefore supplies multiplication by xi_n-1 and xi_n^(-1)-1 from h^r_q to
h^(r+2)_q, uniformly on physical H1 balls. Every real r and Banach q,
including infinity, are covered. Inverting the actual positive root does
not increase its error from one; this comparison holds for every real
source at every finite source exponent greater than one.

For the same retained original Birkhoff family,
[`SourceBirkhoffH1NormalizationPhase.lean`](../NLS/ZakharovShabat/SourceBirkhoffH1NormalizationPhase.lean)
combines normalization and beta-phase decay. The exact multiplier with
symbol xi_n*exp(t*i*beta_n)-1 maps h^r_q to h^(r+1)_q with norm at most
(1+|t|)*C(R), for every real t, r and Banach q. The sequence weights are
(1+|n|)^r; the input ball is measured by the original physical H1 coordinates.
The eta factors are handled below. The spectral-coordinate error relative
to Fourier and stronger-target analyticity remain required for full one-smoothing.

## Actual eta and the spectral terminal

[`SourceGapWeightedEtaH1Sequence.lean`](../NLS/ZakharovShabat/SourceGapWeightedEtaH1Sequence.lean)
proves that each actual signed eta coordinate has norm equal to the real
gap, for every finite source exponent p>1, including collapsed gaps. The
actual H1 gap sequence gives an h1 eta sequence with its exact coefficients.
[`SourceBirkhoffH1EtaDifference.lean`](../NLS/ZakharovShabat/SourceBirkhoffH1EtaDifference.lean)
applies the normalization-phase multiplier and obtains an h2 difference
between the signed Birkhoff coordinate and eta, uniformly on physical H1
balls and for both signs of the same original family.

[`SourceEtaRemainderLocalGapBound.lean`](../NLS/ZakharovShabat/SourceEtaRemainderLocalGapBound.lean)
uses analytic evaluation at the moving Dirichlet terminal for the finite
central indices, and fixed tail annuli with the diagonal numerator bound
for the tail. One constant bounds all actual eta remainders by the
Dirichlet-to-midpoint displacement plus half the gap on a complex
neighborhood of each real source. In
[`SourceEtaRemainderH1Decay.lean`](../NLS/ZakharovShabat/SourceEtaRemainderH1Decay.lean),
real interlacing, compactness of the physical H1 decoder, and the actual
weighted gaps yield a uniform gap bound and inverse-bracket decay on
physical H1 balls.

[`SourceEtaRemainderPhaseSmoothing.lean`](../NLS/ZakharovShabat/SourceEtaRemainderPhaseSmoothing.lean)
proves real-valuedness of the remainder and vanishing at every real
collapsed gap, at all finite source exponents p>1. Its exact exponential
error multipliers gain one sequence derivative for every real sequence
order and Banach exponent, uniformly on physical H1 balls.

[`SourceBirkhoffSpectralTerminal.lean`](../NLS/ZakharovShabat/SourceBirkhoffSpectralTerminal.lean)
defines the literal terminal coordinate

    T_sign,n = -2 * (mu_n - tau_n + sign*i*sineNumerator_n)

and identifies it with eta times the inverse remainder phase. The actual
signed Birkhoff coordinate minus T_sign,n belongs to h2, with a uniform
bound for both signs on each physical H1 ball. This accounts for all
normalization and angular factors.

[`SourceBirkhoffFourierErrorReduction.lean`](../NLS/ZakharovShabat/SourceBirkhoffFourierErrorReduction.lean)
proves the exact rectangular Fourier-error decomposition in the project's
original signed Fourier convention. The remaining spectral quantities are

    A_n = mu_n - tau_n - (phi.fst(-n) + phi.snd(n))/2,
    B_n = sineNumerator_n - (i/2)*(phi.fst(-n) - phi.snd(n)).

If these two literal errors are represented in h2, the theorem constructs
an h2 pair equal coefficientwise to the original Birkhoff map minus its
Fourier linearization. This statement is conditional. Bounds for A and B
and stronger-target analyticity remain open, so full one-smoothing is
not asserted. The higher-order version is supplied below.

## Angular smoothing at every positive integer order

[`SourceHmGapBounds.lean`](../NLS/ZakharovShabat/SourceHmGapBounds.lean)
constructs the actual weighted gap sequence at every integer order and
proves a uniform norm bound on physical Hm balls for every m >= 1. The
proof uses the established global M1 estimate with the physical weight
(1+2*pi*|n|)^m. It also proves exact monotonicity of the physical pair
norms when lowering the integer order.

[`SourceGapWeightedEtaHmSequence.lean`](../NLS/ZakharovShabat/SourceGapWeightedEtaHmSequence.lean)
constructs both actual signed eta sequences in hm and bounds their norms
by the weighted gap norm. This includes collapsed gaps.
[`SourceBirkhoffHmSpectralTerminal.lean`](../NLS/ZakharovShabat/SourceBirkhoffHmSpectralTerminal.lean)
then applies the H1 multiplier estimates at order m, using the exact
physical norm comparison. For every integer m >= 1, both actual signed
Birkhoff coordinates minus their literal spectral terminals belong to
h^(m+1), with one bound on each physical Hm ball and the same original
family. The sequence-space weight is (1+|n|)^(m+1).

[`SourceBirkhoffHmFourierErrorReduction.lean`](../NLS/ZakharovShabat/SourceBirkhoffHmFourierErrorReduction.lean)
extends the exact Fourier comparison to every integer m >= 1. It constructs
the actual rectangular Birkhoff-minus-Fourier error in h^(m+1) when the
two literal spectral errors A and B above are represented there. Their
sharp estimates are still hypotheses of this reduction. Those estimates
and stronger-target analyticity remain needed for full one-smoothing.

## Complex angular smoothing and stronger-target analyticity

The complex argument now follows the same original Birkhoff family
through all normalization and angle factors. The normalized first-order
source decoder divides the nth coefficient by 1+|2n|. The final target
h2 uses weight (1+|n|)^2. These local complex estimates are distinct from
the uniform physical real Hm-ball bounds above.

[`SourceNormalizedRootComplexLower.lean`](../NLS/ZakharovShabat/SourceNormalizedRootComplexLower.lean)
gives one complex neighborhood where all normalized roots have norm at
least 1/2, hence inverse norm at most 2.
[`SourceEtaInverseNormalization.lean`](../NLS/ZakharovShabat/SourceEtaInverseNormalization.lean)
recovers the actual signed eta by exact inverse normalization.
[`SourceWeightedEtaComplexBound.lean`](../NLS/ZakharovShabat/SourceWeightedEtaComplexBound.lean)
and [`SourceWeightedEtaComplexAnalytic.lean`](../NLS/ZakharovShabat/SourceWeightedEtaComplexAnalytic.lean)
then preserve every native spectral weight locally and analytically for
finite source exponents p>1. The exact evaluation statements rule out
the fallback in the sequence realization on the specified neighborhood.

[`SourceWeightedTerminalComplexBound.lean`](../NLS/ZakharovShabat/SourceWeightedTerminalComplexBound.lean)
removes the eta-remainder phase and bounds the literal terminal.
[`SourceWeightedSpectralTermsComplex.lean`](../NLS/ZakharovShabat/SourceWeightedSpectralTermsComplex.lean)
reconstructs the midpoint displacement and sine numerator from its two
signs. [`SourceWeightedEtaRemainderComplex.lean`](../NLS/ZakharovShabat/SourceWeightedEtaRemainderComplex.lean)
and [`SourceWeightedEtaRemainderAnalytic.lean`](../NLS/ZakharovShabat/SourceWeightedEtaRemainderAnalytic.lean)
give the actual remainder's native weighted analyticity.

[`ComplexPhaseSmoothing.lean`](../NLS/SequenceSpaces/ComplexPhaseSmoothing.lean)
turns inverse-bracket decay of a complex symbol into a one-derivative
gain for its exact exponential error, at every real sequence order and
Banach exponent, including infinity. It is used by
[`SourceEtaRemainderComplexSmoothing.lean`](../NLS/ZakharovShabat/SourceEtaRemainderComplexSmoothing.lean)
and [`SourceBetaComplexPhaseSmoothing.lean`](../NLS/ZakharovShabat/SourceBetaComplexPhaseSmoothing.lean).
The beta bound comes from actual weighted spectral majorants in
[`SourceBetaComplexSobolevDecay.lean`](../NLS/ZakharovShabat/SourceBetaComplexSobolevDecay.lean).

[`SourceMidpointProductSobolevDecay.lean`](../NLS/ZakharovShabat/SourceMidpointProductSobolevDecay.lean),
[`SourceSquaredGapSobolevDecay.lean`](../NLS/ZakharovShabat/SourceSquaredGapSobolevDecay.lean),
and [`SourceCriticalOffsetSobolevMajorant.lean`](../NLS/ZakharovShabat/SourceCriticalOffsetSobolevMajorant.lean)
provide the weighted product and row estimates needed for
[`SourceCriticalFactorSobolevDecay.lean`](../NLS/ZakharovShabat/SourceCriticalFactorSobolevDecay.lean).
Exact common-circle agreement and the finite central block then give
actual normalized-action and principal-root decay in
[`SourceNormalizedActionComplexSobolevDecay.lean`](../NLS/ZakharovShabat/SourceNormalizedActionComplexSobolevDecay.lean).
[`SourceNormalizationComplexPhaseSmoothing.lean`](../NLS/ZakharovShabat/SourceNormalizationComplexPhaseSmoothing.lean)
combines the exact root and beta phase into a multiplier gaining one
derivative, including all complex collapsed gaps on that neighborhood.

[`SourceBirkhoffComplexSpectralTerminal.lean`](../NLS/ZakharovShabat/SourceBirkhoffComplexSpectralTerminal.lean)
assembles the h2 bound for both actual signed errors.
[`SourceBirkhoffComplexSpectralTerminalAnalytic.lean`](../NLS/ZakharovShabat/SourceBirkhoffComplexSpectralTerminalAnalytic.lean)
proves analyticity in that stronger norm and exposes an h2-valued map
whose every coefficient is the actual Birkhoff-minus-terminal error.
Both signs share the neighborhood and norm bound. This completes the
complex angular part at first source order. The following extension
covers all higher integer source orders; the sharp Fourier errors A and
B and full one-smoothing remain open.

## Complex angular analyticity at every higher integer order

[`SourceHigherSobolevFirstNormalizedCoordinates.lean`](../NLS/ZakharovShabat/SourceHigherSobolevFirstNormalizedCoordinates.lean)
constructs a continuous linear map from the original SobolevSource m,
for m >= 1, into normalized first-order coordinates. Its decoded
potential is exactly the original higher-order source, and it preserves
the real-type condition. The original domain weight is (1+|n|)^m;
normalized intermediate coordinates do not change the potential.

[`SourceBirkhoffHmComplexSpectralTerminal.lean`](../NLS/ZakharovShabat/SourceBirkhoffHmComplexSpectralTerminal.lean)
pulls back the complex root-and-phase multipliers through this map and
applies them to the actual native weighted eta sequence. Both signed
angular errors have a common local h^(m+1) bound on a complex neighborhood
of every real Hm source, including collapsed gaps.

[`WeightedAnalyticRealization.lean`](../NLS/SequenceSpaces/WeightedAnalyticRealization.lean)
provides a general actual weighted realization of scalar coefficients.
Analytic coefficients and locally bounded weighted realizations imply
analyticity in the weighted Banach target, including exponent infinity.
[`SourceBirkhoffHmComplexSpectralTerminalAnalytic.lean`](../NLS/ZakharovShabat/SourceBirkhoffHmComplexSpectralTerminalAnalytic.lean)
uses this theorem to prove that the actual signed angular-error map is
analytic into h^(m+1), with the original unweighted error at every index.

[`SourceBirkhoffHmComplexFourierErrorReduction.lean`](../NLS/ZakharovShabat/SourceBirkhoffHmComplexFourierErrorReduction.lean)
constructs an analytic pair in h^(m+1) realizing the actual rectangular
Birkhoff-minus-Fourier error whenever the literal errors A and B above
already have analytic h^(m+1) realizations. It retains both assumptions
and restricts to a common open neighborhood inside the original family's
domain. Their sharp estimates and analytic realizations remain necessary
for full one-smoothing; this conditional reduction does not prove them.

## WKB estimates uniform on Sobolev balls

The spectral part now has uniform finite-order WKB bounds. For integer
s >= 1, N <= s, a fixed original SobolevSource s norm ball, and a fixed
horizontal complex spectral strip, one constant controls the actual
solution error by C/(2|z|)^N for |z| >= 1. Smooth periodic representatives
must have the original source's exact Fourier coefficients. The constants
use no additional derivative; the WKB statements themselves still require
smooth representatives and do not yet extend to every nonsmooth source.

[`SobolevRiccatiUniformBounds.lean`](../NLS/ZakharovShabat/SobolevRiccatiUniformBounds.lean)
bounds every actual Fourier Riccati density through the highest L2 order,
including nonsmooth sources.
[`SobolevRiccatiPhysicalBounds.lean`](../NLS/ZakharovShabat/SobolevRiccatiPhysicalBounds.lean)
uses Parseval and continuous synthesis to identify physical L2 and
pointwise bounds for smooth periodic representatives.
[`SobolevRiccatiApproximationUniform.lean`](../NLS/ZakharovShabat/SobolevRiccatiApproximationUniform.lean)
and [`SobolevWKBCarrierUniform.lean`](../NLS/ZakharovShabat/SobolevWKBCarrierUniform.lean)
bound the finite correction, the carrier, and its reciprocal uniformly
on the original source ball.

[`NLSRiccatiResidualDegree.lean`](../NLS/ZakharovShabat/NLSRiccatiResidualDegree.lean)
gives a source-independent polynomial degree bound.
[`NLSRiccatiResidualIntegralCoefficient.lean`](../NLS/ZakharovShabat/NLSRiccatiResidualIntegralCoefficient.lean)
controls coefficients using pointwise lower densities and L1 derivatives.
[`PolynomialFunctionIntegralPower.lean`](../NLS/ComplexAnalysis/PolynomialFunctionIntegralPower.lean)
preserves the exact vanishing power under integration.
[`SobolevRiccatiResidualIntegralUniform.lean`](../NLS/ZakharovShabat/SobolevRiccatiResidualIntegralUniform.lean)
combines these with the top derivative's L2 bound. No supremum of that
top derivative is required.

[`ClassicalIntegralResidualStability.lean`](../NLS/ZakharovShabat/ClassicalIntegralResidualStability.lean)
controls the actual forced solution by the forcing's integral norm.
Forcing remains continuous; the scalar L2 version also states its MemLp
hypothesis explicitly.
[`SobolevWKBUniformComparison.lean`](../NLS/ZakharovShabat/SobolevWKBUniformComparison.lean)
then gives the actual initial-value solution error.
[`SobolevWKBUniformEndpoint.lean`](../NLS/ZakharovShabat/SobolevWKBUniformEndpoint.lean)
gives the monodromy's Hamiltonian approximate eigenvector, and
[`SobolevDiscriminantUniformAsymptotics.lean`](../NLS/ZakharovShabat/SobolevDiscriminantUniformAsymptotics.lean)
gives the same uniform order for the actual discriminant minus
2 cos(I*nlsHamiltonianPhase).

[`NLSRiccatiLeadingResidual.lean`](../NLS/ZakharovShabat/NLSRiccatiLeadingResidual.lean)
identifies the coefficient at the first possible nonzero order as minus
the next Riccati density, including N=0. Removing this term raises exact
polynomial divisibility to N+1. Bounds exploiting its sampled Fourier
cancellation are still needed for the two sharp spectral errors.

For each fixed smooth potential, all-order complex strip bounds are also
available in
[`ClassicalStripResidualStability.lean`](../NLS/ZakharovShabat/ClassicalStripResidualStability.lean),
[`NLSWKBCarrierStripBounds.lean`](../NLS/ZakharovShabat/NLSWKBCarrierStripBounds.lean),
[`NLSWKBStripComparison.lean`](../NLS/ZakharovShabat/NLSWKBStripComparison.lean), and
[`NLSHamiltonianDiscriminantStripAsymptotics.lean`](../NLS/ZakharovShabat/NLSHamiltonianDiscriminantStripAsymptotics.lean).
These include complex potentials without a real-type condition. Their
constants may depend on the fixed smooth potential.

## Leading Fourier terms and actual spectral sampling

[`NLSRiccatiResidualCorrection.lean`](../NLS/ZakharovShabat/NLSRiccatiResidualCorrection.lean)
and [`SobolevRiccatiResidualCorrectionUniform.lean`](../NLS/ZakharovShabat/SobolevRiccatiResidualCorrectionUniform.lean)
remove the exact top density from the residual. All higher residual
coefficients use only lower-density products. Consequently the correction
has order N+1 uniformly on the original Hs ball for N <= s.
[`SobolevWKBCarrierFreeUniform.lean`](../NLS/ZakharovShabat/SobolevWKBCarrierFreeUniform.lean)
gives the order-one free-carrier error, and
[`SobolevWKBLeadingForcing.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingForcing.lean)
identifies the actual leading scalar forcing with an L1 remainder of
order N+1. The top density is controlled in L2, without a supremum bound.

[`SobolevClassicalFreeUniform.lean`](../NLS/ZakharovShabat/SobolevClassicalFreeUniform.lean)
transfers the free-column estimate to the original Hs norm, preserving
the exact factor two from period doubling.
[`IntegralMajorantUnit.lean`](../NLS/ComplexAnalysis/IntegralMajorantUnit.lean),
[`ClassicalScalarForcingFreeComparison.lean`](../NLS/ZakharovShabat/ClassicalScalarForcingFreeComparison.lean),
and [`ClassicalLeadingForcedResidual.lean`](../NLS/ZakharovShabat/ClassicalLeadingForcedResidual.lean)
compare actual forced solutions with their free integral response.
[`SobolevWKBLeadingForcedComparison.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingForcedComparison.lean),
[`NLSWKBLeadingScalarIntegral.lean`](../NLS/ZakharovShabat/NLSWKBLeadingScalarIntegral.lean),
and [`SobolevWKBLeadingOscillatoryComparison.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingOscillatoryComparison.lean)
therefore give the explicit leading oscillatory integral in the actual
WKB solution error, with a uniform order-(N+1) remainder. These statements
still require smooth periodic representatives with exact original Fourier
coefficients, for s >= 1 and N <= s.

[`PiLatticeCoefficient.lean`](../NLS/Fourier/PiLatticeCoefficient.lean)
identifies the lattice integral with the exact unit-period coefficient,
including negative indices and index zero.
[`SobolevWKBLatticeLeading.lean`](../NLS/ZakharovShabat/SobolevWKBLatticeLeading.lean)
uses that identity at every nonzero signed index in the endpoint error.
[`PerturbedLatticeFourierL2.lean`](../NLS/Fourier/PerturbedLatticeFourierL2.lean)
proves a displacement-Lipschitz estimate for continuous-density Fourier
integrals and then realizes their perturbed samples as an L2 sequence.
The bound uses the original coefficient norm, density L1 norm, and the
actual complex displacement L2 norm.
[`SobolevRiccatiPerturbedLattice.lean`](../NLS/ZakharovShabat/SobolevRiccatiPerturbedLattice.lean)
applies this through the top Riccati order, including N=s and H0.
[`SourceRiccatiBoundarySampling.lean`](../NLS/ZakharovShabat/SourceRiccatiBoundarySampling.lean)
and [`SourceRiccatiCriticalSampling.lean`](../NLS/ZakharovShabat/SourceRiccatiCriticalSampling.lean)
instantiate the original canonical Dirichlet, Neumann, and critical
points. Their actual samples have a local L2 bound on a complex
neighborhood of every real original Hs source. No sharp Fourier spectral
error is inferred from this sampling bound alone.

## Discriminant estimates for nonsmooth original sources

[`SobolevFiniteBoundExtension.lean`](../NLS/ZakharovShabat/SobolevFiniteBoundExtension.lean)
transfers continuous scalar bounds from finite Fourier sources in a
slightly larger ball to the original Sobolev ball.
[`SobolevHamiltonianPhase.lean`](../NLS/ZakharovShabat/SobolevHamiltonianPhase.lean)
defines the phase from the actual Fourier NLS Hamiltonians and proves
its exact agreement with the physical phase on smooth sources.
[`SourceSobolevDiscriminantUniform.lean`](../NLS/ZakharovShabat/SourceSobolevDiscriminantUniform.lean)
then extends the Hamiltonian approximation bound to every complex Hs
source for s >= 1 and N <= s. The error is bounded by C/(2|z|)^N on
|z| >= 1 and each fixed horizontal strip. The constant is uniform on
the original source ball; no smoothness or real-type assumption remains.

[`SobolevDiscriminantDerivativeUniform.lean`](../NLS/ZakharovShabat/SobolevDiscriminantDerivativeUniform.lean)
proves spectral analyticity away from zero and a Cauchy bound for the
spectral derivative of this same error, of order C/|z|^N on |z| >= 2.
The source regularity is unchanged. This is a statement about the actual
canonical discriminant, not an extension of the full WKB vector.

The two-column results below supply the next input. The precise root
and product cancellations in the two literal Fourier errors remain open;
these estimates do not complete Fourier one-smoothing.

## Both standard fundamental columns and periodic endpoint samples

[`ClassicalSwapSymmetry.lean`](../NLS/ZakharovShabat/ClassicalSwapSymmetry.lean)
proves exact covariance of the actual solution under
(a,b,z) -> (-b,-a,-z), with swapped solution components. ODE uniqueness
fixes the signs for every initial vector and time.
[`SobolevWKBSecondColumn.lean`](../NLS/ZakharovShabat/SobolevWKBSecondColumn.lean)
then gives the second WKB vector's actual leading oscillatory integral
and uniform order-(N+1) remainder on original Hs balls and strips.

[`ClassicalBasisReconstruction.lean`](../NLS/ZakharovShabat/ClassicalBasisReconstruction.lean)
reconstructs the standard columns from initial vectors (1,p) and (q,1)
using the exact inverse determinant (1-pq)^(-1). It bounds that inverse
by two when |pq| <= 1/2 and propagates both vector errors.
[`SobolevWKBInitialBasis.lean`](../NLS/ZakharovShabat/SobolevWKBInitialBasis.lean)
chooses one frequency threshold for each original Hs ball so that
|p|,|q| <= 1/2. This includes the empty H0 truncation.
[`SobolevWKBFundamentalColumns.lean`](../NLS/ZakharovShabat/SobolevWKBFundamentalColumns.lean)
retains this exact normalization and both leading density integrals in
explicit models for the standard columns. Their errors have order N+1
uniformly in the original source ball, physical time, and horizontal
strip, for s >= 1 and N <= s. Smooth periodic physical representatives
must still match the original source's Fourier coefficients exactly.

[`SourceRiccatiPeriodicSampling.lean`](../NLS/ZakharovShabat/SourceRiccatiPeriodicSampling.lean)
first bounds both full canonical periodic displacement norms on one
complex source neighborhood. Its Sobolev pullback also controls the
original source norm. The actual top-density samples at both periodic
endpoint sequences consequently have L2 realizations with one common
local norm bound. This includes N=s and H0; no real-type assumption or
continuity of individual ordered endpoint labels is needed. Smooth
periodic representatives with exact source coefficients remain explicit.

The characteristic and root estimates below perform the next transfer.
The column and sampling bounds alone do not imply sharp Fourier errors
or full one-smoothing.

## Actual scalar spectral functions and canonical boundary roots

[`ClassicalCharacteristicColumnBounds.lean`](../NLS/ZakharovShabat/ClassicalCharacteristicColumnBounds.lean)
transfers both column errors to the trace, off-diagonal anti-discriminant,
and either source-normalized separated characteristic with factor two.
[`SobolevWKBCharacteristicModels.lean`](../NLS/ZakharovShabat/SobolevWKBCharacteristicModels.lean)
therefore gives one threshold and one uniform order-(N+1) error constant
for all these classical spectral functions on an original Hs ball and
horizontal strip, for s >= 1 and N <= s.
[`SobolevWKBEndpointFormulas.lean`](../NLS/ZakharovShabat/SobolevWKBEndpointFormulas.lean)
expands the endpoint models exactly. Both Hamiltonian phases, both
leading density integrals, and (1-pq)^(-1) remain explicit; no identity
between the two phases is assumed.

[`SourceSobolevClassicalCompatibility.lean`](../NLS/ZakharovShabat/SourceSobolevClassicalCompatibility.lean)
identifies the original canonical source functions with their classical
values for matching continuous periodic representatives. Every actual
canonical boundary root is a zero of the corresponding characteristic.
[`SourceSobolevWKBCharacteristicModels.lean`](../NLS/ZakharovShabat/SourceSobolevWKBCharacteristicModels.lean)
transfers the uniform WKB estimates to these original source functions.
[`SourceSobolevWKBBoundaryRoots.lean`](../NLS/ZakharovShabat/SourceSobolevWKBBoundaryRoots.lean)
uses actual tail localization to give one complex Sobolev neighborhood,
one cutoff, and one bound C/(1+|n|)^(N+1) at both Dirichlet and Neumann
root sequences. Both signed tails are included; the neighborhood may
be centered on a complex source. The WKB statements retain smooth
representatives and exact original coefficients.

The pointwise tail bound is not an h^(N+1) sequence bound: weighting it
only yields a bounded sequence. The sharp Fourier errors still require
square-summable remainder control and the actual phase, midpoint, and
product cancellations.

## Fourier moment series for bounded complex displacements

[`UnitIntervalFourierMoments.lean`](../NLS/Fourier/UnitIntervalFourierMoments.lean)
identifies the existing interval L2 realization with the original
period-one coefficients and proves its exact Parseval norm. The actual
coefficients of x^k f have norm at most the original coefficient norm,
uniformly in k, without requiring equal endpoint values.
[`BoundedLatticeMomentSeries.lean`](../NLS/Fourier/BoundedLatticeMomentSeries.lean)
realizes each Taylor moment as an L2 sequence for any bounded complex
displacement sequence delta. Its norm is bounded by
(2||delta||_infinity)^k/k! times the original coefficient norm.
The full series consequently converges in L2 with bound
exp(2||delta||_infinity) times that norm.

[`PerturbedLatticeMomentIntegral.lean`](../NLS/Fourier/PerturbedLatticeMomentIntegral.lean)
identifies the scalar Taylor series with the actual perturbed Fourier
integral using integrable factorial majorants.
[`BoundedLatticeFourierL2.lean`](../NLS/Fourier/BoundedLatticeFourierL2.lean)
then identifies the L2 sum with every actual sample, with norm at most
exp(2||delta||_infinity) times the original coefficient norm. The complex
displacement sequence need only be bounded, not square-summable.

[`BoundedLatticeDifferenceSeries.lean`](../NLS/Fourier/BoundedLatticeDifferenceSeries.lean)
constructs the removable divided-difference series, with norm at most
2 exp(2||delta||_infinity) times the original coefficient norm.
[`BoundedLatticeFourierDifference.lean`](../NLS/Fourier/BoundedLatticeFourierDifference.lean)
proves that the literal sampling difference equals delta times this
L2 sequence. At delta_n=0, its value is exactly -2i times the original
Fourier coefficient of x f. No division by delta is used.
[`WeightedLatticeFourierDifference.lean`](../NLS/Fourier/WeightedLatticeFourierDifference.lean)
transfers any weighted supremum bound on delta to the corresponding
weighted L2 bound on the actual error. Inverse-index displacements
therefore give one weighted derivative.

## Weighted Riccati sampling at actual boundary and critical roots

[`SobolevRiccatiWeightedSampling.lean`](../NLS/ZakharovShabat/SobolevRiccatiWeightedSampling.lean)
applies the weighted estimate uniformly to the actual original Riccati
hierarchy on Hs balls, through N=s and including the H0 hierarchy endpoint.
[`SourceBoundaryWeightedDisplacement.lean`](../NLS/ZakharovShabat/SourceBoundaryWeightedDisplacement.lean)
gives locally uniform inverse-bracket displacement bounds at every index
for either canonical boundary condition near each real original Hs source,
s >= 1. The neighborhoods include complex sources; the finite central block
uses continuity of the full displacement sequence.
[`SourceRiccatiBoundarySamplingError.lean`](../NLS/ZakharovShabat/SourceRiccatiBoundarySamplingError.lean)
therefore gives one weighted L2 derivative for the actual boundary-sampled
Riccati density minus its original Fourier coefficients.

[`ClassicalSobolevCriticalRootDisplacement.lean`](../NLS/ZakharovShabat/ClassicalSobolevCriticalRootDisplacement.lean)
uses a fixed-radius Cauchy estimate to control the actual discriminant
derivative error on physical H1 balls. The filled sine quotient then gives
inverse-index bounds for every critical root in the distant quarter-pi discs.
[`SourceCriticalSobolevDisplacement.lean`](../NLS/ZakharovShabat/SourceCriticalSobolevDisplacement.lean)
transfers this estimate to the actual canonical critical points through
exact physical compatibility and their critical equation.
[`SourceCriticalWeightedDisplacement.lean`](../NLS/ZakharovShabat/SourceCriticalWeightedDisplacement.lean)
includes the finite central block and both signed tails on one complex Hs
neighborhood near each real source.
[`SourceRiccatiCriticalSamplingError.lean`](../NLS/ZakharovShabat/SourceRiccatiCriticalSamplingError.lean)
then gives the same one-derivative weighted L2 gain at the actual critical
sequence. No smooth representative is required for displacement estimates.
The physical-density conclusions retain smooth periodic representatives
with exactly matching original coefficients, and include N=s without an
additional source derivative.

Three sampling examples check a constant pi displacement (allowed even
though it is not L2), the removable derivative -i for the constant density
at index zero, and vanishing error in an arbitrary weighted space at a
negative index. The two sharp Fourier spectral errors and full one-smoothing
still require weighted WKB remainders and the actual phase, midpoint, and
omitted-product cancellations.

## Exact Hamiltonian reflection and phase elimination

[`ClassicalSwapDiscriminant.lean`](../NLS/ZakharovShabat/ClassicalSwapDiscriminant.lean)
identifies the actual discriminant under signed potential swap and
spectral reflection. At free cosine zeros,
[`NLSHamiltonianReflectedPhaseEstimate.lean`](../NLS/ZakharovShabat/NLSHamiltonianReflectedPhaseEstimate.lean)
uses both discriminant asymptotics and a local sinh inverse estimate
to obtain arbitrary-order cancellation of their phase corrections.
[`NLSHamiltonianReflection.lean`](../NLS/ZakharovShabat/NLSHamiltonianReflection.lean)
recovers every Hamiltonian coefficient by analytic order, proving
H_(k+1)(-b,-a) = (-1)^k H_(k+1)(a,b).
[`NLSHamiltonianPhaseReflection.lean`](../NLS/ZakharovShabat/NLSHamiltonianPhaseReflection.lean)
then gives exact phase cancellation at all truncations and frequencies,
including the total definition at zero.

[`SobolevHamiltonianReflection.lean`](../NLS/ZakharovShabat/SobolevHamiltonianReflection.lean)
extends these identities to nonsmooth complex original Sobolev sources
by smooth density. Odd Hamiltonians retain their sharper Hm domains.
[`NLSWKBSinglePhaseModels.lean`](../NLS/ZakharovShabat/NLSWKBSinglePhaseModels.lean)
expresses the endpoint trace, anti-discriminant, and both separated models
using one phase and the actual leading integrals S and T. Write p and q
for the initial coordinates, eta for the boundary sign, d=1-pq, and
A=1+pq-eta(p+q). With d nonzero,
[`NLSWKBBoundaryPhaseElimination.lean`](../NLS/ZakharovShabat/NLSWKBBoundaryPhaseElimination.lean)
proves the exact identity
A d anti + (1-eta q)^2 S + (1-eta p)^2 T = -2i(p-q)d separated.
Also, the inverse of A has norm at most four when both initial
coordinates have norm at most one half. These are identities of the
actual explicit WKB models, with no assumed sharp solution remainder.

## Original Fourier coefficients in the leading WKB integrals

[`SobolevRiccatiSmoothingRemainder.lean`](../NLS/ZakharovShabat/SobolevRiccatiSmoothingRemainder.lean)
constructs the actual nonlinear Riccati remainder in H^(s-N+1) and proves
its coefficient formula rho_N(n)+(2*pi*i*n)^N b_n and analyticity.
[`SobolevRiccatiSmoothingUniform.lean`](../NLS/ZakharovShabat/SobolevRiccatiSmoothingUniform.lean)
bounds it uniformly on every original complex Hs ball.
[`SobolevRiccatiLeadingSampling.lean`](../NLS/ZakharovShabat/SobolevRiccatiLeadingSampling.lean)
combines it with weighted sampling to give an H1 error for the sampled
density plus its original leading Fourier derivative, for N <= s.
[`SourceRiccatiBoundaryLeadingSampling.lean`](../NLS/ZakharovShabat/SourceRiccatiBoundaryLeadingSampling.lean)
and [`SourceRiccatiCriticalLeadingSampling.lean`](../NLS/ZakharovShabat/SourceRiccatiCriticalLeadingSampling.lean)
apply this to the actual canonical sequences near real Hs sources.

[`WKBLeadingScalarMultipliers.lean`](../NLS/ZakharovShabat/WKBLeadingScalarMultipliers.lean)
controls the combined exponential and inverse-frequency multiplier by
the actual displacement, including zero powers.
[`WKBLeadingTailFourierError.lean`](../NLS/ZakharovShabat/WKBLeadingTailFourierError.lean)
then converts an Hs original coefficient and an H1 sampled-density error
into an H^(s+1) error for the literal leading expression.
[`WKBLeadingFrequencyCutoff.lean`](../NLS/ZakharovShabat/WKBLeadingFrequencyCutoff.lean)
provides a common cutoff on both signed tails from the displacement budgets.

[`SobolevWKBLeadingFourierTail.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingFourierTail.lean)
proves that at full order N=s, the actual explicit leading integral
minus i exp(i*pi*n) b_n is an H^(s+1) tail, uniformly on original Hs balls
and displacement budgets. The constructed sequence is zero on the
finite central block.
[`SourceWKBLeadingFourierTails.lean`](../NLS/ZakharovShabat/SourceWKBLeadingFourierTails.lean)
applies this to actual Dirichlet, Neumann, and critical points on complex
neighborhoods near real Hs sources, s >= 1. The physical integrals retain
matching smooth periodic representatives; the bounds require only the
original Hs norm, with no additional source derivative.

Eight public examples check physical momentum reflection, nonsmooth H0
mass invariance, the total zero-frequency phase, the H0 and first-order
zero remainders, the actual cubic convolution at a negative index,
the leading-integral sign at every lattice index, and zero-order
exponential displacement. These estimates do not yet give the sharp
full WKB remainder or the two literal Fourier spectral errors.

## Both leading coefficients and the diagonal error contribution

[`SobolevWKBBothLeadingFourierTails.lean`](../NLS/ZakharovShabat/SobolevWKBBothLeadingFourierTails.lean)
uses signed potential swap, frequency reflection, and the Sobolev
reflection isometry to prove both leading-integral tail estimates with
one cutoff and constant. The first leading coefficient is
 i exp(i*pi*n) b_n; the reflected coefficient is
-i exp(-i*pi*n) a_(-n).
[`SourceWKBBothLeadingFourierTails.lean`](../NLS/ZakharovShabat/SourceWKBBothLeadingFourierTails.lean)
applies the same result to the actual boundary and critical sequences
near real Hs sources, with no covariance assumption on canonical labels.

[`WKBBoundaryLeadingFactors.lean`](../NLS/ZakharovShabat/WKBBoundaryLeadingFactors.lean)
bounds the exact phase-elimination factors by six and their difference
from one by six times the sum of the initial-coordinate norms.
The separated-model coefficient has bound eight times that sum.
[`NLSWKBBoundaryLeadingCombination.lean`](../NLS/ZakharovShabat/NLSWKBBoundaryLeadingCombination.lean)
gives the exact anti-discriminant model as the two leading-integral
terms and the small separated-model contribution, with the phase eliminated.

[`NLSWKBAntiErrorDecomposition.lean`](../NLS/ZakharovShabat/NLSWKBAntiErrorDecomposition.lean)
defines the two actual WKB remainders E and F after subtracting the
explicit leading integrals. With initial coordinates p and q and
nonzero d=1-pq, it proves
 d (anti_actual - anti_model) = q E.fst + p F.snd - E.snd - F.fst.
Thus the diagonal terms carry additional small factors.
[`SobolevWKBInitialDecay.lean`](../NLS/ZakharovShabat/SobolevWKBInitialDecay.lean)
bounds both initial coordinates by one inverse-frequency factor,
uniformly on original Sobolev balls through N=s.
[`SobolevWKBDiagonalRemainder.lean`](../NLS/ZakharovShabat/SobolevWKBDiagonalRemainder.lean)
consequently gives order N+2 for q E.fst + p F.snd.

[`SobolevInversePowerBound.lean`](../NLS/SequenceSpaces/SobolevInversePowerBound.lean)
turns a bound C/(1+|n|)^(s+1) into an actual Hs sequence with norm at
most 2C, including the central index.
[`SobolevWKBDiagonalFourierTail.lean`](../NLS/ZakharovShabat/SobolevWKBDiagonalFourierTail.lean)
applies it to the literal diagonal contribution at N=s, giving a uniform
H^(s+1) tail on original Hs balls with the stated displacement budgets.
The central block is set to zero; multiplication by the uniformly bounded
inverse determinant is still to be included in the final assembly.

Three examples check the reflected sign and exact negative Fourier index,
unit leading factors at empty initial coordinates, and the inverse-square
sequence's H1 norm and coefficient at index -2. All physical comparisons
retain matching smooth periodic representatives. The remaining sharp
WKB estimate concerns E.snd + F.fst, rather than a stronger bound on
both full vector remainders. Critical-to-midpoint and omitted-product
cancellations are still required for the two literal spectral errors.

## Interval L2 sampling and the first diagonal correction

[`UnitIntervalMemLpMoments.lean`](../NLS/Fourier/UnitIntervalMemLpMoments.lean)
proves that physical moment multiplication contracts the actual Fourier
coefficient norm for arbitrary interval L2 data.
[`MemLpLatticeMomentSeries.lean`](../NLS/Fourier/MemLpLatticeMomentSeries.lean)
sums the resulting bounded-displacement Taylor series in the Hilbert
sequence space with constant exp(2||delta||_infinity).
[`PerturbedLatticeIntegrableMoments.lean`](../NLS/Fourier/PerturbedLatticeIntegrableMoments.lean)
identifies the scalar series with the actual sampled integral using only
integrability. Together these give
[`MemLpBoundedLatticeFourier.lean`](../NLS/Fourier/MemLpBoundedLatticeFourier.lean):
actual samples of any interval L2 density at pi*n+delta_n have an L2
realization with the same bound. No endpoint matching or continuity is
assumed, and a bounded displacement need not be square summable.

[`PartialIntervalFourierSampling.lean`](../NLS/Fourier/PartialIntervalFourierSampling.lean)
uses contraction under measurable cutoffs to give the same bound for
every partial interval [0,t].
[`PartialIntervalOscillatorySampling.lean`](../NLS/Fourier/PartialIntervalOscillatorySampling.lean)
includes the free propagator exp(i*(pi*n+delta_n)*t), with the uniform
constant exp(3||delta||_infinity) on the whole physical period.

[`SobolevClassicalDiagonalCarrier.lean`](../NLS/ZakharovShabat/SobolevClassicalDiagonalCarrier.lean)
shows that the actual diagonal fundamental entries differ from their
first WKB carriers by O(w^2), where w=(2*i*z)^(-1).
[`NLSWKBFirstCarrier.lean`](../NLS/ZakharovShabat/NLSWKBFirstCarrier.lean)
defines P(x)=integral_0^x a*b and proves the exact first-carrier identity
exp(-i*z*x)*exp(-w*P(x)). The primitive is continuous and invariant under
the signed potential swap, and its norm is bounded by the square of the
pointwise potential budget on the physical period.
[`SobolevWKBFirstCarrierExpansion.lean`](../NLS/ZakharovShabat/SobolevWKBFirstCarrierExpansion.lean)
linearizes both carriers with their exact signed mass corrections.
[`SobolevClassicalDiagonalExpansion.lean`](../NLS/ZakharovShabat/SobolevClassicalDiagonalExpansion.lean)
therefore proves the actual expansions
A1(x)=exp(-i*z*x)*(1-w*P(x))+O(w^2) and
B2(x)=exp(i*z*x)*(1+w*P(x))+O(w^2).
The constants are uniform on original complex Hs balls for s >= 1,
horizontal strips, and all physical x. Smooth periodic representatives
with exact original Fourier coefficients remain explicit hypotheses.

[`ClassicalScalarForcingLowerKernel.lean`](../NLS/ZakharovShabat/ClassicalScalarForcingLowerKernel.lean)
identifies the actual lower response to scalar forcing f with the
partial-interval integral of K22(t,x)*f(x), where
K22(t,x)=A1(x)*B2(t)-B1(x)*A2(t). This is an exact identity.
The first-order kernel estimate and its sharp sampled WKB consequence
are still to be assembled from the diagonal expansions and L2 sampling.

Five examples check the half-period cutoff, the real exponential signs
at the central sample for the constant imaginary shift delta_n=i, the
constant-potential mass primitive, the carrier at z=i for potentials 2
and 3, and K22(t,t)=1 for every potential. Critical-to-midpoint comparison
and omitted-product cancellations remain for the literal spectral errors.

## The leading lower response and the next WKB forcing

[`ClassicalLowerKernelExpansion.lean`](../NLS/ZakharovShabat/ClassicalLowerKernelExpansion.lean)
combines the actual diagonal expansions with the off-diagonal bounds to
prove K22(t,x)=exp(i*z*(t-x))*(1+w*(P(t)-P(x)))+O(w^2).
[`ClassicalLowerForcingExpansion.lean`](../NLS/ZakharovShabat/ClassicalLowerForcingExpansion.lean)
propagates this estimate for any continuous scalar density, retaining
the primitive-difference oscillatory correction exactly.

[`IntervalL2BoundedMultiplier.lean`](../NLS/Fourier/IntervalL2BoundedMultiplier.lean)
proves that a continuous physical multiplier bounded by K preserves
interval L2 data and multiplies the actual coefficient norm by at most K.
[`PartialIntervalMassCorrectionSampling.lean`](../NLS/Fourier/PartialIntervalMassCorrectionSampling.lean)
then gives an L2 sequence realization of the primitive-difference
correction with bound 2*K*exp(3*||delta||_infinity) times the original
coefficient norm, uniformly over every partial physical interval.

[`SobolevWKBLeadingLowerExpansion.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingLowerExpansion.lean)
identifies the actual lower response to the leading forcing as the free
leading integral plus (-i)*w^(N+1) times the mass-correction integral,
with an O(w^(N+2)) error. In
[`SobolevWKBMassCorrectionTail.lean`](../NLS/ZakharovShabat/SobolevWKBMassCorrectionTail.lean),
the correction is an H^(N+1) tail under the displacement budgets, with a
bound valid at every cutoff above the common threshold.
[`SobolevWKBLeadingLowerFourierTail.lean`](../NLS/ZakharovShabat/SobolevWKBLeadingLowerFourierTail.lean)
combines it with the inverse-power remainder to control the actual
leading lower response minus the free leading integral in H^(N+1).
The constants are uniform on original Hs balls through N=s and all
physical times. This estimates the leading forced response, not yet
the full off-diagonal WKB remainder.

[`NLSRiccatiResidualNextOrder.lean`](../NLS/ZakharovShabat/NLSRiccatiResidualNextOrder.lean)
isolates the coefficient c_N of w^(N+1) in the residual polynomial:
q_N(w)+rho_N*w^N-c_N*w^(N+1)=O(w^(N+2)). Its higher coefficients
need only lower undifferentiated Riccati densities.
[`SobolevRiccatiResidualNextOrder.lean`](../NLS/ZakharovShabat/SobolevRiccatiResidualNextOrder.lean)
proves continuity and uniform pointwise bounds for c_N and the improved
residual error on original Hs balls through N=s.

[`SobolevRiccatiApproximationFirstOrder.lean`](../NLS/ZakharovShabat/SobolevRiccatiApproximationFirstOrder.lean)
proves that every positive Riccati truncation equals -b*w+O(w^2).
[`SobolevWKBCarrierFirstOrder.lean`](../NLS/ZakharovShabat/SobolevWKBCarrierFirstOrder.lean)
therefore gives the same exp(-i*z*x)*(1-w*P(x))+O(w^2) expansion
for every positive carrier order. Finally,
[`SobolevWKBNextForcingExpansion.lean`](../NLS/ZakharovShabat/SobolevWKBNextForcingExpansion.lean)
proves that the full scalar forcing minus its leading forcing equals
w^(N+1)*i*(c_N+rho_N*P)*exp(-i*z*x), with an L1 error of order N+2.
No extra derivative of the source is required for 1 <= N <= s.

Four public examples check the actual free kernel's sign and time
direction, the central mass-correction sample 1/2 for P(x)=x and density
1, the correction 3 for constant potentials 2 and 3, and c_1=-a*b^2.
The uniform physical L2 bound for the next density, the full forced
response, both off-diagonal tails, and the anti-discriminant assembly
remain to be integrated. Critical-to-midpoint comparison and omitted-
product cancellations are still needed for the literal spectral errors.

## Both full off-diagonal WKB remainders

[`SobolevWKBNextForcingL2.lean`](../NLS/ZakharovShabat/SobolevWKBNextForcingL2.lean)
proves a uniform physical L2 bound for i*(c_N+rho_N*P), using the
bounded next residual coefficient and primitive together with the
original L2 bound for rho_N. No higher source derivative is needed.
[`ClassicalForcedKernelLinearity.lean`](../NLS/ZakharovShabat/ClassicalForcedKernelLinearity.lean)
records addition for the actual zero-initial forced solution and for
the scalar forcing embedding.

[`SobolevWKBNextScalarComparison.lean`](../NLS/ZakharovShabat/SobolevWKBNextScalarComparison.lean)
defines the explicit next forcing and free oscillatory term. Its actual
forced response differs from that free term by O(w^(N+2)), uniformly
on original Hs balls, strips, and the physical period.
[`SobolevWKBNextOscillatoryComparison.lean`](../NLS/ZakharovShabat/SobolevWKBNextOscillatoryComparison.lean)
propagates the full forcing expansion through the actual kernel. The
WKB vector minus its homogeneous solution, actual leading forced
response, and next free term has an order-(N+2) full vector bound.

[`SobolevWKBNextFreeTail.lean`](../NLS/ZakharovShabat/SobolevWKBNextFreeTail.lean)
combines the density's physical L2 estimate with partial-interval
oscillatory sampling and the inverse-frequency multiplier. The result
is an H^(N+1) tail for every cutoff above a common threshold.
[`SobolevWKBFirstOffDiagonalTail.lean`](../NLS/ZakharovShabat/SobolevWKBFirstOffDiagonalTail.lean)
then combines the leading lower-response tail, next free tail, and
order-(N+2) remainder to prove the full first-column off-diagonal
H^(N+1) bound for 1 <= N <= s.

[`SobolevWKBBothOffDiagonalTails.lean`](../NLS/ZakharovShabat/SobolevWKBBothOffDiagonalTails.lean)
proves the exact reflected-remainder identity and applies the first
estimate to (-b,-a), the spectral parameter -z, and displacement
-delta(-n). Weighted reflection gives the second off-diagonal tail with
the same cutoff and constant. No covariance of selected canonical root
labels is assumed. Smooth periodic representatives with matching
original coefficients remain explicit hypotheses throughout.

Three examples check the next density -18i for constant potentials
2 and 3, the next scalar forcing -9i/2 at z=i and x=0, and both exact
zero initial remainders. The two off-diagonal terms are now ready for
the anti-discriminant error identity. Extension to nonsmooth sources,
critical-to-midpoint comparison, and omitted-product cancellations
remain for the literal Fourier spectral errors.

## The complete analytic boundary anti-discriminant Fourier error

[`SobolevWKBAntiModelFourierTail.lean`](../NLS/ZakharovShabat/SobolevWKBAntiModelFourierTail.lean)
combines the exact determinant-weighted error identity with both full
off-diagonal tails and the diagonal contribution. It proves an H^(s+1)
tail for the actual anti-discriminant minus its WKB model, at every
cutoff above a common threshold and without a spectral-root equation.

[`SobolevWKBBoundaryFactorDecay.lean`](../NLS/ZakharovShabat/SobolevWKBBoundaryFactorDecay.lean)
controls both phase-elimination factors and the separated factor.
[`SobolevLeadingMultiplierTail.lean`](../NLS/SequenceSpaces/SobolevLeadingMultiplierTail.lean)
shows that an inverse-index deviation of a leading multiplier preserves
the one-order smoother Fourier error, including every larger cutoff.
[`SobolevWKBBoundaryLeadingTails.lean`](../NLS/ZakharovShabat/SobolevWKBBoundaryLeadingTails.lean)
applies this to both actual leading oscillatory integrals.
[`SobolevWKBBoundarySeparatedErrorTail.lean`](../NLS/ZakharovShabat/SobolevWKBBoundarySeparatedErrorTail.lean)
controls the separated model error after its small phase-elimination factor.

[`SobolevBoundaryAntiFourierTail.lean`](../NLS/ZakharovShabat/SobolevBoundaryAntiFourierTail.lean)
uses the actual separated-characteristic equation to obtain the literal
signed Fourier terms at either boundary condition.
[`SourceBoundaryAntiFourierTail.lean`](../NLS/ZakharovShabat/SourceBoundaryAntiFourierTail.lean)
transfers this estimate to the actual canonical source roots, locally
uniformly near every real original Hs source. These intermediate
physical comparisons retain matching smooth periodic representatives.

[`WeightedCoefficientLimit.lean`](../NLS/SequenceSpaces/WeightedCoefficientLimit.lean)
retains the weight and norm bound under bounded coefficientwise limits.
[`DenseWeightedCoordinateBound.lean`](../NLS/SequenceSpaces/DenseWeightedCoordinateBound.lean)
uses continuous raw coordinates to extend the bound from a dense subset
of an open source set.
[`SourceBoundaryAntiSobolevTail.lean`](../NLS/ZakharovShabat/SourceBoundaryAntiSobolevTail.lean)
then defines the literal source error and extends its H^(s+1) tail to
all Hs sources by finite Fourier approximation. No smooth representative
or additional source derivative remains in that theorem.

[`WeightedFiniteBlock.lean`](../NLS/SequenceSpaces/WeightedFiniteBlock.lean)
constructs finite raw-coordinate blocks in the actual weighted space.
[`WeightedTailCompletion.lean`](../NLS/SequenceSpaces/WeightedTailCompletion.lean)
adds the central frequencies to obtain a locally uniform full-sequence bound.
[`SourceBoundaryAntiFourierAnalytic.lean`](../NLS/ZakharovShabat/SourceBoundaryAntiFourierAnalytic.lean)
combines this bound with scalar canonical-root analyticity. For every
integer s >= 1, one open complex neighborhood of the entire real Hs
locus supports both boundary remainders as H^(s+1)-valued analytic maps,
with every raw coordinate equal to

    anti(z_n,ab) + i*exp(i*pi*n)*b_n - i*exp(-i*pi*n)*a_(-n).

Six examples check the distinct Dirichlet and Neumann leading factors,
a negative-mode estimate at an increased cutoff, both strict cutoff
endpoints of the finite head, a nonunit Sobolev weight at a negative
frequency, and the full remainder at the free potential.

This is the numerator estimate for the eta-sine Fourier error. The
omitted standard-root product remains in its denominator. The critical
phase and midpoint comparison also remain for the Dirichlet-midpoint
Fourier error; full Fourier one-smoothing is not asserted here.

## Critical-midpoint regularity and the diagonal phase identities

[`SobolevSquaredSymbol.lean`](../NLS/SequenceSpaces/SobolevSquaredSymbol.lean)
shows that the square of an order-s decaying symbol sends an unweighted
lp sequence into H^(2s), with its literal raw coefficients and an
explicit norm bound. This includes infinite lp exponent.
[`SourceCriticalMidpointHigherSobolev.lean`](../NLS/ZakharovShabat/SourceCriticalMidpointHigherSobolev.lean)
applies it to the actual Hs gap sequence and the bounded l2 quotient
in the exact critical-midpoint squared-gap identity. The resulting
bound includes every index, collapsed complex gaps, and s = 0.
[`SourceCriticalMidpointSobolevAnalytic.lean`](../NLS/ZakharovShabat/SourceCriticalMidpointSobolevAnalytic.lean)
realizes the actual offset as a locally bounded analytic map into H^k
for every k <= 2s on a complex neighborhood of each real Hs source.
For s >= 1, this proves the H^(s+1) critical-to-midpoint correction
without smooth representatives or additional source derivatives.

[`NLSWKBTraceErrorDecomposition.lean`](../NLS/ZakharovShabat/NLSWKBTraceErrorDecomposition.lean)
identifies the determinant-weighted actual trace error relative to both
the WKB model and the single Hamiltonian phase. Both diagonal errors
are retained; no cancellation is assumed.
[`ClassicalScalarForcingDiagonalIdentity.lean`](../NLS/ZakharovShabat/ClassicalScalarForcingDiagonalIdentity.lean)
uses integration by parts in the actual scalar forced ODE to isolate
the upper response. Its undivided identity also holds at z = 0.
[`NLSWKBLeadingDiagonalIdentity.lean`](../NLS/ZakharovShabat/NLSWKBLeadingDiagonalIdentity.lean)
specializes this identity to the original leading WKB forcing. With
w = (2iz)^(-1) and Riccati density r_N, the isolated diagonal primitive
contributes -w^(N+1)*exp(-izt)*integral(a*r_N) when z is nonzero.
Since r_0 = -b, its zeroth-order sign is positive in terms of integral(a*b).

[`WeightedCoordinateIntegral.lean`](../NLS/SequenceSpaces/WeightedCoordinateIntegral.lean)
constructs the integral of uniformly bounded weighted raw coordinates
by finite blocks and bounded coefficientwise limits. It needs no
strong measurability hypothesis on chosen full sequence realizations.
[`NestedIntervalFourierSampling.lean`](../NLS/Fourier/NestedIntervalFourierSampling.lean)
uses this construction to bound reverse partial-interval and nested
oscillatory samples at bounded complex lattice displacements. The
nested bound uses only the inner density's L2 norm and the continuous
outer density's L1 norm, with no derivative of either density.

Three examples verify squared weights at a negative frequency with
nonzero raw amplitude, the zero-source offset at every target order,
and the triangular nested integral's exact value 1/8 at half the period.

The critical-midpoint regularity is proved. The diagonal response still
needs its uniform remainder bound after removing the displayed phase
primitive, followed by the actual critical-phase estimate. The omitted
standard-root product cancellation remains separate. Full Fourier
one-smoothing is not claimed by these identities alone.

## Validation and remaining work

The original 24 public checks cover complex original-domain action identity,
Parseval, both weighted source components, common constants, integer
orders one and two, lower-order target norms, negative coordinate
indices, the full real locus in each complex neighborhood, and both
weighted estimates. Fractional order 3/2 checks the literal exponents
six and three; order one checks the endpoint domain. Further checks
retain both original physical solution theories, the unconditional
common-family constructor, and the weight-growth correction.
Eight further checks cover H1 beta and phase decay at zero and negative
indices, exponents 3/2 and infinity, a negative-order multiplier, one
original family valid for all real H1 sources, and phase/operator
constants chosen before every source in a physical H1 ball. Full
validation results are recorded in [implementation status](../STATUS.md).
Seven more checks cover the sharp gap-action bound, normalized action at
index zero, the reciprocal normalized root at a negative index, the
factor-two root-error bound, an l1 reciprocal-square sum, separation of
negative and positive gaps, and one separation constant on an entire
physical H1 ball.
Six new checks cover normalized decay at zero, root decay at a negative
index, the inverse-root multiplier on weighted l-infinity at negative
order, and H1 gap-opening perturbations preserving an open physical norm
constraint. They also check the combined signed factor and identify its
exponent-3/2 multiplier applied to an eta sequence with the original
Birkhoff weighted coordinate minus that sequence.

Six further checks cover eta norm at exponent three, negative-order
l-infinity phase multiplication, a common bound for both signed terminal
errors, both spectral errors at the zero source, collapsed-gap vanishing
at a negative index, and the conditional h2 Fourier reduction.

Four higher-order checks cover the exact physical H3-to-H1 norm inequality,
H2 eta at a negative index, the negative signed H3 terminal error in h4,
and the conditional H2 Fourier remainder in h3.

Ten complex checks cover normalized roots at exponent three, both native
eta constructions at a physical weight and negative indices, phase
multipliers at negative order with infinite or fractional exponents,
zero phase, root-error summability, a negative signed terminal error,
and differentiation in the actual h2 target.

Three higher complex checks cover polynomial coefficient realization in
weighted l-infinity at negative order, differentiation of the negative
signed H3 angular error into h4 at a negative index, and an analytic H2
Fourier remainder into h3 under the two literal spectral-error hypotheses.

Six WKB checks cover off-axis spectral values with negative real part,
constant complex potentials, the zeroth truncation and |z|=1 boundary,
the nonsmooth H0 density, the order-zero residual coefficient, and the
uniform H1 discriminant estimate at z=I.

Four column checks cover the second standard initial vector at empty
truncation, the reflected leading term's sign at zero spectral parameter,
the closed half-product determinant bound, and both normalized models
at time zero. Full validation is recorded in
[implementation status](../STATUS.md).

Three characteristic checks cover the exact free trace for arbitrary
complex frequency and the two mean-value signs at zero frequency, for
both separated boundary conditions. Full validation is recorded in
[implementation status](../STATUS.md).

The native Sobolev geometry is now covered by the independent inverse
and canonical results above. The discussion of the one-smoothing
property on p. 104 cites [39]. A full one-derivative gain for the
Birkhoff map minus its Fourier linearization is not proved by the
norm, normalization, and phase estimates alone and is not asserted here.

The outline's p. 105 trace now has two actual-source counterexamples:
the index sum must include all integers, and the alternating sign is
incorrect even with that index correction. The full original-domain
physical trace has positive factor 1/4ᵐ. See
[the Section 24 audit](SECTION_24.md) and
[`SourceSection23TraceCorrections.lean`](../NLS/ZakharovShabat/SourceSection23TraceCorrections.lean).
The precise two-sided asymptotic is proved there by
`sourceIndexedHigherAction_asymptotic`. The all-level zero-detection
claim is refuted by an actual open central gap with zero level-two
action, while `sourceIndexedHigherAction_even_eq_zero_iff` gives the
correct real odd-level converse. These distinctions are resolved;
they are not additional unproved requirements for the norm estimates.
