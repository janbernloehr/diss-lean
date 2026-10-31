# Appendix B source audit

## Ordered source comparison

The [ordered Appendix B comparison](APPENDIX_B_ASSERTIONS.md)
covers 12 groups on pp.124–125: eight matched, two corrected and two
contextual. No partial or pending groups remain in this local ledger.

B.1 retains both printed bounds. B.2 includes every Banach Young
triple and infinity endpoint, with absolute convergence and constant
one. B.3 retains finite positive exponents, including inputs below
one, and proves convergence of all three nested sum levels.

The outer sum in the proof is the gamma-th power of the stated
left side. Both directions of the intermediate exponent conditions
are now explicit. Zero auxiliary exponents and an unstated infinity
convention remain excluded. No new Lean proof or refutation is added
in this documentation step.

The unchanged Lean snapshot reuses the successful full check recorded at commit 862ad929f3588bf317eff9c659e8e63a1fef9549: 8,583 build jobs, 7,694 public examples and an axiom audit of 44,709 NLS declarations, with 21 inherited warnings and zero new. All 19 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix C. The four Section 28 complex intermediate passages
and the [broader completion qualifications](COMPLETENESS.md)
remain qualified; the local counts do not certify the dissertation.

Earlier entries retain their original implementation and validation scope.

## Positive proof-step estimates

The [Appendix B proof steps](../NLS/SequenceSpaces/AppendixBProofSteps.lean)
now make the intermediate exponent and outer power explicit.

Under (B.2), q >= beta holds exactly when gamma >= p1. The combined
mixed exponent condition is equivalent to the existence of an
intermediate exponent satisfying both powered Young relations.

The convergent outer sum is bounded by the gamma-th power of the
product of input norms. Its positive gamma-th root is the stated
left side of B.3. This directly corrects the proof normalization;
the final constant remains one.

Three positive theorems and two examples retain finite positive
exponents, including inputs below one and unequal nesting powers.
No new refutation is added.

The full check passed: 8,583 build jobs, 7,694 public examples and an axiom audit of 44,709 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The ordered Appendix B comparison continues. The
[broader completion qualifications](COMPLETENESS.md) remain.

The source is printed pages 124–125 of *Features of the Nonlinear Fourier
Transform for the dNLS Equation*. B.1 and B.2 are proved in their stated
ranges. B.3 is proved for finite positive exponents, including input exponents
below one. Its printed zero auxiliary endpoints need qualification: the
formula divides by those exponents and gives no definition there.

| Source assertion | Public theorem | Verified scope |
| --- | --- | --- |
| B.1, reciprocal series | `NLS.sourceLemmaB1` | Every nonnegative shift and every finite conjugate pair 1<p,q<infinity; summability and both printed bounds. |
| B.2, convolution inequality (B.1) | `NLS.Coeff.sourceLemmaB2` | Every Banach Young triple, including all infinity endpoints; a unique target sequence with the actual `HasSum` formula and bound one. |
| Absolute convergence in B.2 | `summable_norm_youngConvolution_terms` | Every output frequency, for all inputs in the stated spaces. |
| B.3, nested inequality | `NLS.Coeff.sourceLemmaB3_positive` | Explicit alpha>0 and beta>0, printed orderings and reciprocal identity; all three levels summable and exact bound one. All exponents are finite real numbers. |
| B.3, sharpness | `NLS.Coeff.sourceLemmaB3_constant_sharp` | Every admissible finite positive exponent tuple; unit modes force any uniform constant to be at least one. |
| Printed alpha=0 endpoint | `b3_zero_inner_terms_nonzero`, `b3_zero_inner_not_summable` | Actual inputs in l1,l2,l2; every inner product is nonzero, and its zeroth power yields a divergent row of ones. |
| Printed beta=0 endpoint | `b3_zero_middle_inner_summable`, `b3_zero_middle_inner_pos`, `b3_zero_middle_not_summable` | Actual inputs in l1,l2,l2; every inner sum exists and is positive, but the middle row at beta=0 consists of ones and diverges. |

## Source formulas and convergence

[`AppendixBSourceInequalities.lean`](../NLS/SequenceSpaces/AppendixBSourceInequalities.lean)
collects the source statements. For B.1 the sum over natural n of
1/(alpha+n+1)^q is exactly the printed sum over m>=1. Both estimates retain
the source constants, including (q+alpha)/(q-1)/(1+alpha)^q. The proof uses
[`ReciprocalSeries.lean`](../NLS/SequenceSpaces/ReciprocalSeries.lean).

For B.2 the `Coeff` spaces use the ordinary complex sequence norms and the
reciprocal condition `YoungRelation`. Exponents are extended nonnegative
reals with explicit Banach hypotheses. Each coefficient is the sum of
a(n-k)b(k). The target is unique by uniqueness of every convergent row.
[`YoungConvolution.lean`](../NLS/SequenceSpaces/YoungConvolution.lean) also
proves absolute convergence, the continuous bilinear construction, and its
sharp operator norm. No finite-support assumption is needed.

For B.3 the orderings alpha<=p2,p3 and 0<beta<=p1<=gamma ensure positivity
of every exponent. [`MixedYoungExponents.lean`](../NLS/SequenceSpaces/MixedYoungExponents.lean)
constructs the intermediate exponent in equations (B.2)–(B.3).
[`MixedYoung.lean`](../NLS/SequenceSpaces/MixedYoung.lean) applies powered
Young twice, verifies convergence before using the nested sums, and proves
the displayed bound. The input exponents may lie below one; only the
powered Young spaces must be Banach. Unit sequences attain equality.

## Zero auxiliary exponents

The printed hypotheses allow alpha=0 and beta=0, while the same display
contains 1/alpha, 1/beta, beta/alpha, gamma/beta and 1/gamma. The ordinary
real formula is undefined at those endpoints. The positive interpretation
must therefore be stated explicitly.

[`MixedYoungZeroExponent.lean`](../NLS/SequenceSpaces/MixedYoungZeroExponent.lean)
records a separate syntactic diagnostic, `TotalizedMixedYoungConditions`.
It copies the printed conditions using Lean's totalized real division.
The tuples (alpha,beta,gamma,p1,p2,p3)=(0,1,1,1,2,2) and (1,0,1,1,2,2)
satisfy that transcription. This does not give a mathematical meaning to
the source formula at zero.

The divergence witnesses use b(n)=c(n)=(1+|n|)^(-1). For alpha=0, take
a to be the unit sequence at zero and k=l=0; every inner term is nonzero.
For beta=0 and alpha=1, take a(n)=(1+|n|)^(-2); each inner sum is strictly
positive and finite, at every k,l. The relevant zeroth powers are all one,
so the inner or middle sum diverges. Neither witness relies on defining
0^0, nor on Lean assigning zero to a divergent totalized sum. These are
not counterexamples to the well-defined positive-exponent inequality.
See [the source qualification](../SOURCE_ERRATA.md).

## Scope and checks

B.2 includes infinity endpoints. B.3's current API uses finite real
exponents; it does not claim a separate infinity or limiting convention
for the printed nested powers. Such an extension would require a precise
supremum formulation and its own proof.

Twenty public examples exercise B.1's zero and positive shifts and both
bounds; B.2's l2*l2-to-l-infinity, l1/l-infinity endpoints, and fractional
Banach exponents; B.3 with unequal nesting exponents and with all exponents
one half; optimality of the constant; and both zero-exponent diagnostics,
including positivity and convergence of the inner rows.
