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
an external asymptotic theorem. The remaining coordinate and normalization
asymptotics, the full Birkhoff-minus-Fourier derivative gain, and analyticity
into that stronger target are not established by the phase result.

## Normalization bounds and separation for the next decay argument

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

The next obligation is to combine these results with the actual exterior
kernel and weighted actions to prove normalized-action/root upper decay.
The present lower bounds and separation estimates alone do not prove that
upper decay or the full Birkhoff-minus-Fourier smoothing assertion.

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

The native Sobolev geometry is now covered by the independent inverse
and canonical results above. The discussion of the one-smoothing
property on p. 104 cites [39]. A full one-derivative gain for the
Birkhoff map minus its Fourier linearization is not proved by the
norm estimates or the phase estimates alone and is not asserted here.

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
