# Actual critical basis and period entries in the Hminus1 topology

`exists_hillHminus_all_contour_period_data` constructs an actual critical
numerator basis and all of its original contour period entries on one
complex Hminus1-open neighborhood of zero. The domain is the library's
original unit-period `PeriodOneHminusOne`, with its Sobolev minus-one norm.
The neighborhood precedes every positive numerator and contour index.
This is a rough-potential construction, not a continuous-norm neighborhood
renamed as a rough one.

## Constructed critical energies

`HillHminusOneCriticalPoints.lean` uses the independently constructed
rough Hill discriminant and a proved local analytic Miura chart. In a
fixed chart with energy shift c, the exact trace identity is

    Delta_Hminus1(q, z²-c) = Delta_ZS(periodOne(diagonal(lift(q))), z).

The general complex ZS distant critical family supplies actual energies
mu_k(q)=zeta_k(q)²-c. Exact first and second derivative identities prove
Delta'(mu_k)=0 and Delta''(mu_k)!=0. One rough-open neighborhood and cutoff
precede all high k, at every complex Hminus1 source. The critical label
is unique on its shifted square disc. No real-type hypothesis on the
source is imposed.

At zero, a fixed energy translation is small in the high frequency
coordinate. Free criticality and the unique shifted-disc label give the
exact unshifted free value mu_k(0)=k²*pi². The auxiliary chart's energy
shift is retained throughout the proof; it is not silently discarded.
The energies here are critical energies lambda-dot_k, not Dirichlet mu_k
from the source's notation.

The reusable `AnalyticSimpleCriticalBranch.lean` constructs a local simple
critical branch for a jointly entire function with Banach parameters.
`HillHminusOneCriticalNumerators.lean` applies it to the finite head and
joins that head to the actual high family by a finite intersection. Thus
every positive selected critical energy is analytic and simple on one
common rough-open neighborhood, with its exact free value.

## Entire basis and original period entries

Filled analytic division constructs the literal critical basis

    B_n(lambda,q) = 2*n*pi*Delta'(lambda,q)/(lambda-mu_n(q)),

with the value at the moving critical center supplied by Delta''.
The numerator is jointly analytic on the whole energy plane times the
common rough neighborhood, and its filled critical value is nonzero.
Its entire free slice is the previously proved free normalized numerator.
The exact factor identity is proved at every energy, including centers.

`HillHminusOnePeriodEntries.lean` constructs source-sheet coverage of
every fixed original frequency circle C(k*pi,pi/4). The high tail uses
the actual rough annulus theorem. For each remaining circle, compactness
and the open source domain produce a neighborhood; a finite intersection
then gives one neighborhood before all indices.

The literal period entries are

    P_nk(q) = (2*pi)^(-1) integral B_n(z²,q)/root(z²,q) * 2*z dz.

Every entry is analytic on that same neighborhood, and the whole free
matrix is exactly the identity. The original source normalization has no
additional factor i, and the exact energy substitution has Jacobian 2*z.
`HillHminusAllContourPeriodData` packages the constructed critical,
numerator, source-cover and period assertions for the next operator step.

## Scope and remaining normalization work

The B_n are a critical basis. Their nonzero-potential periods have not
been inverted in the Hminus1 norm, so they are not yet the normalized
Psi_n. The all-mode construction is near zero. The arbitrary-source
assertion concerns the high simple critical family, not a global all-mode
normalization over the source's full W neighborhood.

This supplies actual rough ingredients for the differential/period
construction preceding Lemma 3.1 (PDF pages 26–27) and the rough analytic
frequency extension in Theorem 3.4 (page 31). Still required are rough
operator bounds and an analytic inverse, agreement with the constructed
continuous normalized family, rough normalized moments and summation,
and continuation over the full source domain. The physical frequency
identity (69), action descent, sharp estimates and Birkhoff/PDE flow
identification remain open. No main-theorem inventory row is verified.

## Selected-source integration and validation

`SHARED_HMINUS_NORMALIZATION_IMPORT.json` records 113 new proved sources
from convexity commit `08db7a5b181084e4436959d1e84b2596bd5d9338`, including
the actual physical Miura/L2 comparisons, analytic shifted Miura charts,
the jointly entire rough discriminant, source sheets and contour coverage.
Six compatible local files are retained. The import is a selected
dependency closure, not a full branch merge.

`EulerLagrange.lean` adds a direct import of the proved periodic
integration-by-parts module because the retained local Hamiltonian module
does not export that dependency. Its proof statements and bodies are
unchanged. Two source-local maxHeartbeats 800000 settings are removed
from the new Hill bilinear-symmetry and discriminant-necessity files;
both unchanged proofs pass at the default budget. These qualifications
and all source/local hashes are recorded.
Nine initially inspected but unused new sources were removed.

All 201 previously selected source files remain unchanged. The four
earlier provenance records also remain valid. Strict build counts and the
complete transitive axiom audit are recorded in `VALIDATION.md` and
`source.json` after the completed run. No heartbeat increase, linter
exception, placeholder or new axiom is used.
