# Rough weighted inverse columns and actual critical gap localization

This milestone constructs the actual rough twice-weighted period operator
and inverse, retains every normalized moment feature on the same source
neighborhood, and locates the actual critical energies at quadratic gap
scale. All neighborhoods below use the original unit-period Hminus1 norm.
The main-theorem inventory remains open.

## Actual twice-weighted operator and inverse

`HillHminusOneTwoWeightedPeriodOperator.lean` retains the sharper literal
period bound for distinct positive indices,

    |P_nk(q)| <= (20/pi)*A*n*k/|k²-n²|².

The formula comes from the actual primitive integration-by-parts identity,
source contour coverage and squared-energy critical separation. It is
valid for low indices as well as the high tail. The period normalization
is 1/(2*pi), with the exact energy Jacobian 2*z.

Conjugating the positive matrix by two index weights produces entries

    S_mn(q) = (w(m)²/w(n)²)*T_mn(q),
    w(m)=m for m>0, and w(m)=1 otherwise.

The already proved shared numerical kernel estimate retains a summable
near-diagonal convolution and a far Hilbert outer product. The mixed
majorant theorem constructs an actual bounded operator S, analytic in
the Banach operator norm and equal to the identity at zero. Its norm is
at most 26*((80/pi)*A+1) on the constructed neighborhood. No weighted
matrix action is assumed.

`HillHminusOneTwoWeightedPeriodInverse.lean` constructs an analytic
inverse Q of S on a common smaller rough-open neighborhood, with
Q(0)=Id and norm at most 2. The actual unweighted inverse R is retained,
with both inverse identities and its own norm bound at most 2. The
bounded reciprocal diagonal proves exact compatibility of every entry:

    w(m)²*(R(q)e_n)_m = w(n)²*(Q(q)e_n)_m.

## One actual normalized family with every retained feature

The reusable sequence-space module `AnalyticTwoWeightedInverseColumns.lean`
constructs the genuine l2 vector

    E_n(q) = n²*(Q(q)e_n-e_n).

Its coordinates are exactly w(m)²*((R(q)e_n)_m-(e_n)_m), not a formal
sequence for which membership is assumed. It is analytic, vanishes at
zero and satisfies

    ||E_n(q)|| <= n²*||Q(q)-Id||.

For any epsilon>0, one source neighborhood precedes every positive n
and gives ||E_n(q)|| <= epsilon*n².

`exists_hillHminus_twoWeighted_normalized_moments` constructs one common
rough-open neighborhood and T,R,S,Q. Its data record retains all four
operator analyticities/free values, both two-sided inverse identities,
both norm bounds, every literal matrix entry, exact weighted compatibility,
and the analytic l2 coefficient errors. The same R defines the actual
jointly entire normalized numerators, their exact free slices, all moment
analyticities, every original zeroth period and all odd cancellations.
The underlying actual critical/numerator/contour data are retained too.
There is no replacement of the normalized family when adding weights.

Odd cancellation is proved for any given actual analytic inverse using
the exact continuous/rough compatibility theorem and analytic uniqueness
through the dense linear pullback. It is then instantiated with the
weighted-compatible inverse. No bounded stronger-norm ball is assumed
dense in a rough ball.

## Actual rough critical energies at quadratic gap scale

Six unchanged selected shared sources from convexity `08db7a5` supply
actual rough whole-gap squares, complete two-root clusters and normalized
filled endpoint quotients. The pair is unordered and records the actual
radicand zeros and their analytic multiplicities on its energy disc.
No global analytic ordering of individual roots is assumed.

`HillHminusOneSmallCriticalControl.lean` proves arbitrarily small common
confinement of every selected physical critical frequency near its free
center. The proof keeps the fixed Miura energy translation and handles
the finite head by analytic continuity. Its source neighborhood precedes
all positive indices.

`exists_critical_gap_square_localization` chooses a radius r before a
tolerance epsilon. For every 0<epsilon<=1/16 it constructs one cutoff M
and rough-open neighborhood U of zero before all n>=M. It retains the
jointly analytic whole energy square K, its exact squared-cosh trace
identity, its agreement with the actual shifted primitive square wherever
source continuation is admissible, and the actual endpoint pair l,u.
The filled endpoint quotient is analytic on the whole disc, has the
literal factor identity at every energy, and obeys the free normalization

    |4*(n*pi)²*Q_endpoint + 1| <= epsilon.

These data refer to the actual critical energy critical_n(q), not the
source's Dirichlet eigenvalue notation. The proved conclusions are

    |critical_n(q)-(l+u)/2|
        <= (2*epsilon/(pi*r))*|l-u|²/n,
    |critical_n(q)-(l+u)/2| <= |l-u|/4.

At l=u, the critical energy equals that endpoint exactly. The entire
circle of radius |l-u| about the midpoint stays at least |l-u|/2 from
the critical pole. The proof uses the actual discriminant criticality,
the squared-cosh derivative and the shared two-zero localization theorem;
it never divides by the gap length.

`exists_relative_critical_gap_bound` gives any prescribed eta>0:

    |critical_n(q)-(l+u)/2| <= eta*|l-u|,

on one common local rough neighborhood and high tail. This is the
near-zero rough-topology form of source (37), PDF page 16. The stronger
quadratic estimate is an ingredient toward Lemma 2.11(i), PDF pages
18–19; its full source domain and lp remainder are not proved here.

## Source scope and remaining work

The weighted normalized-family result is a necessary ingredient for the
sharp normalized moments preceding the frequency series in Theorem 3.4,
PDF page 31. Analyticity, zeroth normalization and odd cancellation in
Lemma 3.1 are retained on the same local rough neighborhood.

The actual sharp rough normalized second-moment bounds and frequency
summation still require cut-resolvent period estimates and a summable
actual gap majorant. The retained K/endpoint quotient/critical data are
prepared for that step. Positive collapsed-even moments in the complete
required scope, the exact canonical product leading scalar, full W
continuation, physical Hamiltonian frequency identity (69), action
descent, weighted frequency asymptotics, compact derivatives and actual
Birkhoff/PDE flow identification remain open. No main theorem is marked
verified and no moment-frequency candidate is called a physical frequency.

## Integration and validation

`SHARED_HMINUS_GAP_QUOTIENT_IMPORT.json` records six unchanged new proved
sources from `08db7a5b181084e4436959d1e84b2596bd5d9338` and one compatible
local whole-gap extension retained unchanged. Two inspected cut-root/scale
sources were omitted from the current import because they are not needed
by this milestone. The full branch is not merged.

There are six new own proved modules and six selected shared sources.
All 341 previously selected Lean sources remain byte-identical; all six
earlier provenance records remain valid. `VALIDATION.md` and `source.json`
record the completed strict build and transitive axiom audit. The checks
use pinned Lean 4.33.1/mathlib v4.33.1, default heartbeats, warnings as errors
and private outputs. Only propext, Classical.choice and Quot.sound are
allowed; there are no placeholders, new axioms, heartbeat increases,
disabled linters or warning exceptions. Canonical main stays read only.
