# Section 28: original weighted actions and gap lengths

## Positive weighted small-ball estimate

The [small-ball estimate](../NLS/ZakharovShabat/SourceSection28SmallBall.lean)
now uses the same original weighted norm on the right-hand side:

    sum_n w(2n)^2 * |I_n| <= 2^20 * ||a||^2,  when 8*||a||^2 <= 1.

It applies to every M1 weight and every complex weighted source
decoding into the retained common domain. The full action series
is summable, including zero and the equality boundary.

This directly corrects the H1-only quadratic factor in the
near-zero intermediate display on p.119 to the weighted norm.
The final real 2^20 and complex 2^21 bounds retain their scope.

One positive theorem and two examples cover the source-shaped
bound with the additional factor (1+||a||)^4 and the inclusive
boundary budget 2^17. No new refutation is added.

The full check passed: 8,582 build jobs, 7,692 public examples and an axiom audit of 44,706 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The ordered Section 28 comparison continues. The
[broader completion qualifications](COMPLETENESS.md) remain.

This audit covers printed pp. 117–119: (5.14), (5.15), the valid final
estimate of Lemma 28.1, Proposition 28.2, and the proof of Theorem 23.4.
All actions are the original indexed contour actions. The physical H¹
norm retains the Fourier weight 1+|2nπ| and both components.

The literal signed ratio in Lemma 28.1 is false at the actual zero
potential. Its final constant 2048 and Proposition 28.2's constant 4608
are proved independently of that ratio. The earlier scalar boundary
counterexamples remain distinct from this spectral counterexample.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Compact H¹-to-L² inclusion used after (5.14) | `isCompactOperator_normalizedWeightedSource` | Exact decoding by 1/w(2n), every M₁ weight, every Banach coefficient exponent including infinity. |
| Formula (5.14), local uniformity | `SourceSection28Data.normalized_locally_uniform` | An actual ℓ² sequence equals 4 times the filled normalized indexed action minus one, uniformly on one neighborhood before all indices. Holds near every complex point of S. |
| Formula (5.14), bounded H¹ sets | `SourceSection28Data.normalized_uniform_H1_ball` | One ℓ² bound before all real sources in each exact physical H¹ ball. The more general API covers every real M₁ weighted ball. |
| Formula (5.15) | `SourceSection28Data.normalized_bound` | Exact factor nine for any nonnegative bound on χ over the closed gap; the filled version includes collapsed complex gaps. |
| Lemma 28.1, final bound | `SourceSection28Data.physical_H1_bounds` | Actual deleted product χ, constant 2048, signed indices, inclusive bracket cutoff and every point of the closed complex gap. |
| Lemma 28.1, signed ratio | `SourceEquation2_19Data.section28_signed_ratio_zero`, `section28_zero_physical_cutoff` | Refuted by the actual zero H¹ source at n=−1, N=1; its collapsed-gap midpoint has χ=1 and satisfies the printed cutoff. |
| Proposition 28.2 | `SourceSection28Data.physical_H1_bounds`, `chi_action_bound` | Original indexed action, constant 4608, exact physical norm and printed absolute-index threshold; the weighted-coordinate API also allows the inclusive bracket threshold. |
| Weighted sum in the proof of Theorem 23.4 | `SourceSection28Data.weighted_summable`, `weighted_continuous` | Absolute summability and continuity throughout the weighted complex part of S, for every M₁ weight. |
| Real bound in the proof of Theorem 23.4 | `section28_real_weighted_action_bound` | Printed 2²⁰ constant, actual original indexed actions, and the exact continuous weight extension at 16‖a‖². |
| Complex bound in the proof of Theorem 23.4 | `SourceSection28Data.weighted_bound` | Printed 2²¹ constant on a connected weighted-open neighborhood of the entire real weighted locus, decoding into S; zero is included. |
| One original family | `SourceSection28Data`, `sourceSection28_original` | Extends Section 27 with one connected L²-open S⊆T⊆U chosen before all weights; the original actions, Birkhoff map, and all previous estimates remain available. |

## Local uniformity and bounded physical H¹ sets

[`NormalizedWeightedSourceCompact.lean`](../NLS/ZakharovShabat/NormalizedWeightedSourceCompact.lean)
proves that the exact reciprocal symbol 1/w(2n) vanishes uniformly off
finite frequency sets. Its finite-rank approximations therefore make
the decoder compact. This holds even at the coefficient exponent infinity;
it does not assert norm convergence of arbitrary unweighted infinity
Fourier truncations.

[`SourceSection28Asymptotics.lean`](../NLS/ZakharovShabat/SourceSection28Asymptotics.lean)
uses the original Section 11 estimates. Their ℓ¹ part embeds into ℓ²,
and their one-plus part has its own ℓ² bound. A finite subcover then
gives one bound on every compact subset. The closure of a real weighted
ball's decoded image is compact and still real, so it lies in the original
domain. This supplies the uniform assertion for all real M₁ weighted balls,
including the physical H¹ balls stated in the source.

At an open gap, the filled value is exactly Iₙ/γₙ². At a collapsed gap,
the analytic filled value is used: Lean's totalized division 0/0 is not
substituted for that extension. Public checks retain the exact free value
4 times the filled normalized action = 1.

## Complex gap bounds and continuity

[`SourceSection28GapBounds.lean`](../NLS/ZakharovShabat/SourceSection28GapBounds.lean)
uses Lemma F.1 to choose a single connected neighborhood on which every
critical coordinate has norm at most two. The actual cosine integral
then gives the factor nine. The independently established complex χ
bound is converted to the literal deleted product with its unit phase
accounted for. Multiplying by the squared gap gives

    4|Iₙ| ≤ 9 · 2048(1+P²)|γₙ|²,

hence the exact action constant 4608. This division-free argument includes
collapsed gaps. The bound for physical H¹ sources is obtained by decoding
the exact physical coordinates, not by replacing the norm with an
equivalent one.

[`SourceSection28WeightedContinuity.lean`](../NLS/ZakharovShabat/SourceSection28WeightedContinuity.lean)
constructs locally bounded ℓ¹ realizations of the actual weighted action
coefficients at every admissible complex source. Their scalar coordinates
are analytic. The norm of that continuous ℓ¹ map is the literal convergent
weighted absolute sum. Thus continuity and summability hold on the entire
weighted part of S, beyond the smaller neighborhood used for the explicit
2²¹ estimate.

[`SourceSection28WeightedActions.lean`](../NLS/ZakharovShabat/SourceSection28WeightedActions.lean)
retains the exact 2²⁰ real and 2²¹ complex constants. The complex estimate's
neighborhood is chosen separately for each weight, is connected, contains
every real weighted source, and decodes into the common S. This distinguishes
the common L² domain from the weight-dependent estimate neighborhoods.

## Literal source corrections

[`SourceSection28SignedIndex.lean`](../NLS/ZakharovShabat/SourceSection28SignedIndex.lean)
proves that at the actual zero source, n=−1 and N=1, the printed ratio bound
has right-hand side −512/17 while |χ₋₁|=1. The physical H¹ norm is zero,
and the printed bracket cutoff holds. Every retained U and T contains
this witness. The proof's instruction to treat negative indices similarly
requires reflecting n; it does not make the literal signed formula true.

The separate positive-boundary arithmetic defects at n=N are recorded in
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md). Their corrected scalar constants
do not by themselves prove the spectral estimate. The formalization instead
retains the independently proved final spectral bounds. It also keeps the
factor four explicit when passing from 9·2048=18432 to the action constant
4608 in Proposition 28.2's proof.

## Validation and next work

Seven new modules and 31 public checks cover compact decoding, signed
frequencies, the physical zero-source counterexample, local and bounded-set
ℓ² estimates, filled and open-gap normalizations, exact numerical constants,
complex continuity, absolute convergence, connected domains, and retention
of the original family. Full validation is recorded in [STATUS.md](../STATUS.md).

The unrestricted printed m=1 coefficient is proved in [Section 27](SECTION_27.md).
The [Section 14 qualifications](SECTION_14.md) remain explicit. The remaining
source audit continues through the appendices; the dissertation is incomplete.

## The weighted tail display on p.119

The first display in the proof of Theorem 23.4 has two distinct defects:
its action sum includes |n|=N while its gap sum excludes those indices,
and its coefficient is 4608*P^2 instead of 4608*(1+P^2). The actual PDF
was checked, including the permitted cutoff N=0 for small nonzero inputs.

[SourceSection28TailCounterexample.lean](../NLS/ZakharovShabat/SourceSection28TailCounterexample.lean)
constructs a real H1 source with I_0=t and every other original indexed
action zero. Its exact physical H1 pair norm satisfies

    0 < P^2 <= 3*(t+t^2).

All noncentral gaps are closed. For t=1/1000000 and the original weight
w(m)=1+|m*pi|, the cutoff N=0 obeys 0<8*P^2<=1. The inclusive weighted
action sum is t, while the strictly exterior weighted gap sum is zero.
Thus no finite coefficient can repair the omitted cutoff boundary.

The same source also distinguishes the missing factor from that cutoff
error. The sharp actual gap-action inequality gives gamma_0^2<=4*t,
so even the inclusive weighted gap sum satisfies

    4608*P^2 * sum_{|n|>=0} w(2n)^2*|gamma_n|^2 < t.

Both failures occur in every retained Section 28 domain, because each
domain contains every real source. They concern the intermediate proof
display, not the final 2^20 and 2^21 estimates, which remain proved.

[SourceSection28TailEstimate.lean](../NLS/ZakharovShabat/SourceSection28TailEstimate.lean)
proves a corrected complex weighted tail on the same original domain.
Both sums use |n|>=N and the full factor 4608*(1+||a||^2) is retained.
The coefficient norm is the original weighted norm; for the pi-Sobolev
weight of order one it is exactly the physical H1 norm P.
The corrected estimate includes absolute summability and combines with
Proposition 25.5's actual Fourier-tail budget
6*||R_N a||^2 + 1152/(1+N)*||a||^6.

Four public examples check a prescribed small central action, failure
for every finite coefficient with the strict gap tail, the corrected
N=0 physical norm statement, and the N=2 Fourier-tail budget, which
retains both signed boundary indices.
