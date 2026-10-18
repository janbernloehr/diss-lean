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

## Validation and remaining work

The 24 new public checks cover complex original-domain action identity,
Parseval, both weighted source components, common constants, integer
orders one and two, lower-order target norms, negative coordinate
indices, the full real locus in each complex neighborhood, and both
weighted estimates. Fractional order 3/2 checks the literal exponents
six and three; order one checks the endpoint domain. Further checks
retain both original physical solution theories, the unconditional
common-family constructor, and the weight-growth correction.
Full validation results are recorded in [implementation status](../STATUS.md).

The native Sobolev geometry is now covered by the independent inverse
and canonical results above. The discussion of the one-smoothing
property on p. 104 cites [39]. A full one-derivative gain for the
Birkhoff map minus its Fourier linearization is not proved by the
norm estimates alone and is not asserted here.

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
