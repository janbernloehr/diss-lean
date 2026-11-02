# Actual normalized moment analyticity and all odd cancellations near zero

This step advances Lemma 2.6 (PDF page 15) and Lemma 3.1(i)–(iii)
(PDF pages 25–26). **No article main theorem is closed.** The actual
normalized entire numerators are the functions constructed from the
inverse R of the actual infinite Hill period operator. Their exact
source-normalized canonical prefactor at nonzero potentials remains a
separate obligation; it is not assumed by this moment argument.

## Literal moments and one common neighborhood

The new `classicalHillNormalizedMoment N R n k m q` is the literal
frequency pullback

    integral_C(k*pi,pi/4) (F(z^2,q)+i*k*pi)^m
      * Psi_n(z^2,q)/continuedRoot(z^2,q) * (2*z) dz.

`classicalHillNormalizedMoment_eq_curveIntegral` proves this is exactly
the one-form integral over the counterclockwise mapped energy contour,
including the Jacobian 2*z and with no extra normalization factor.

`exists_classicalHill_normalized_all_odd_moments` constructs N,U,R with
U open and containing zero in C([0,1], C) with the sup norm. Before
choosing **any** positive indices n,k or moment order, it proves:

- R is analytic on U and equals Id at the free potential.
- Every moment, including order zero, is analytic on U.
- `(2*pi)^(-1) * Omega_nk^(0) = delta_nk` for every n,k and q in U.
- `Omega_nk^(2*l+1) = 0` for every n,k, l>=0 and q in U.

There is no remaining finite-contour or omitted-n exception in this
local result. The odd cancellation includes n=k and collapsed gaps.
It does not assume the normalized numerator vanishes at a branch point.
These conclusions retain the same actual inverse and all original
normalization periods, rather than a newly postulated differential.

## Filled quotients and actual cancellation

The shared whole-gap square construction is reused from
`articles/kdv-convexity` at commit
`4b8896cdfc0e7fabc3b75df7db287ee472c532fe`. Its necessary continuous-
potential dependency set is imported; this is a selected source import,
not a merge of the whole other article branch or its coverage.
`SHARED_WHOLE_GAP_IMPORT.json` records paths, source hashes, local hashes
and qualifications. The existing local joint-analytic spectral derivative
and exported squaredCosh derivative lemma are preserved. The shared
whole-gap result is extended to arbitrary prescribed positive square
bounds, keeping its original unit-bound interface.

`exists_classicalHill_whole_gap_quotients` constructs one complex source
neighborhood and high cutoff at an arbitrary continuous potential.
Every whole high energy disc carries jointly analytic K,H with

    H != 0,  K = H^2*(Delta^2-4),
    K = F_k^2 and H = F_k/continuedRoot on the admissible source domain.

The actual complete straight complex two-root gap is strictly enclosed,
including a collapsed pair. At every branch zero, also multiple ones,
K=0 and H=(-1)^k/2. A single small neighborhood of the nonzero derivative
of squaredCosh at zero supplies all quotients. No nonzero Delta' or
simple-endpoint hypothesis is used. The continued root sheet is proved
to equal `2*(-1)^k*sinh(F_k)` exactly.

For the high contour family, shared annulus coverage justifies shrinking
the original frequency circle. The analytic extension of the odd
integrand is `K^l*H*P*(2*z)`, where P is any entire energy numerator.
Cauchy's theorem gives zero. The generic high theorem chooses its source
neighborhood and cutoff before k, the entire P and l.

For each fixed low contour, a local squared-cosh chart at the free
collapsed gap and compact source tubes provide the same cancellation
near zero. One tube controls the analytic filled chart on a closed
disc, one controls the actual primitive branch on its circle, and one
covers the closed annulus used for contour shrinking. A finite
intersection of these neighborhoods and the common high neighborhood
handles every positive k at once. This is then instantiated with each
actual entire Psi_n, before all output indices n.

The added `frequencyMoment_odd_eq_zero_of_continuations` requires only
circle agreement with analytic filled extensions. It does not prescribe
unfilled quotient values at the branch points themselves. No ZS RealType
hypothesis is applied to the Hill pair (-1,-q) at complex or real q.

## Lean map

| File / declaration | Proved content |
| --- | --- |
| `ClassicalHillWholeGapSquares.lean` / `exists_classicalHill_whole_gap_small_squares` | Shared actual whole-gap analytic squares, generalized to any prescribed positive bound with the original interface retained. |
| `ClassicalHillWholeGapQuotients.lean` / `exists_classicalHill_whole_gap_quotients` | Actual nonzero analytic filled quotients and exact sheet/endpoints on complete high-gap discs. |
| `ClassicalHillOddDifferentialMoments.lean` | Actual differential radius independence and all high odd cancellations for every entire numerator on a common complex neighborhood at any continuous source. |
| `ClassicalHillLowOddDifferentialMoments.lean` / `exists_classicalHill_all_odd_differential_moments` | Constructed fixed-contour free-source tubes and one common zero-source neighborhood for all positive contours, entire numerators and odd orders. |
| `ClassicalNormalizedMoments.lean` | Literal actual normalized moments, exact mapped energy contour identity, joint integrand and moment analyticity, exact zeroth-period normalization. |
| `ClassicalNormalizedOddMoments.lean` / `exists_classicalHill_normalized_all_odd_moments` | Actual all-mode normalized moment family with common-neighborhood analyticity, exact zeroth periods and every odd cancellation. |
| `FrequencyMoments.lean` / `frequencyMoment_odd_eq_zero_of_continuations` | Reusable filled-extension criterion that includes multiple/collapsed branch points. |

## Remaining source scope

The common neighborhood here is near zero in the continuous-potential
sup norm, not the full source W in its rough topology. Lemma 3.1(iv),
vanishing of every positive moment at arbitrary collapsed gaps, still
needs an actual even-moment argument. Sharp normalized moment estimates,
real gap/root bounds and the exact nonzero-potential leading scalar
normalization remain open. So do the physical Hamiltonian-frequency and
Birkhoff flow identifications, global/rough extension, weighted compact
derivatives and all main theorem rows. No source-wide Lemma 3.1 claim
is inferred from this local construction.
