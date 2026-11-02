# Actual critical energies at quadratic gap scale

This step supplies a localization needed to shrink the squared-resolvent
moment contours toward the actual gaps. It advances the continuous-
potential version of the critical-point estimates around (37) and
Lemma 2.11(i), PDF pages 16 and 18–19. **All article main theorems remain
open.** The full source rough/global W scope and the weighted lp remainder
in Lemma 2.11(i) are not proved by this step.

## Actual result and quantifiers

At any continuous complex source q, one radius r>0 is chosen before the
tolerance epsilon. For every 0<epsilon<=1/16, a common complex open
neighborhood V of q and a cutoff N are then chosen before every positive
index k>=N. The actual critical energy, midpoint and squared gap are
analytic on V, and throughout V,

    |lambda-dot_k - tau_k|
      <= (2*epsilon/(pi*r)) * |gamma_k^2|/k.

For the actual unordered complex endpoints l,u,

    |lambda-dot_k - (l+u)/2| <= |l-u|/4.

Consequently, on the gap-length circle centered at (l+u)/2, the distance
to the actual critical energy is at least |l-u|/2. This supplies the
diagonal critical-pole separation needed by the normalized moment
resolvent formula. The result does not assert that a complex critical
energy lies on the straight gap segment.

`exists_classicalHill_critical_gap_ratio_bound` gives the simpler
consequence: **for every eta>0**, a common neighborhood and tail cutoff
give `|lambda-dot_k-tau_k| <= eta*|gamma_k^2|/k` at all retained indices.
No quotient by a possibly zero gap is taken. At an actual collapsed high
gap, the critical energy equals the actual midpoint.

`exists_classicalHill_relative_critical_gap_bound` also proves the
continuous-potential counterpart of (37): for every eta>0, one complex
neighborhood and cutoff give `|lambda-dot_k-tau_k|<=eta*|l-u|` for all
retained actual pairs. The proof uses the actual counted endpoint
geometry `|l-u|<=2*pi^2*k` with the quadratic estimate above. It includes
zero gaps and does not assume a real ordering of the endpoints.

The Lean energy is `classicalHillHighCriticalPoint`, and the intrinsic
midpoint/squared gap are `classicalHillHighMidpoint` and
`classicalHillHighSquaredGap`. Above the original selected numerator
cutoff, `classicalHillUniformCriticalPoint` is this same high energy by
its definition. Here the source label is lambda-dot_k, not its Dirichlet
eigenvalue mu_k. No normalized numerator root sigma_k is identified by
this theorem.

## Constructed inputs and proof

The extended `ClassicalCriticalTailAnalytic.lean` proves arbitrarily small
uniform critical-frequency confinement near **any** continuous complex
source. The actual Hilbert displacement at the source has a small scalar
tail, and norm continuity of its analytic Hilbert realization controls
all nearby sources on one neighborhood. This makes the actual critical
energy lie in the small energy disc used below. The older fixed pi/8
bound alone would not imply this stronger confinement.

The selected proved shared quotient family gives

    K(lambda)=(lambda-l)*(lambda-u)*Q(lambda),
    |4*(pi*k)^2*Q(lambda)+1| <= epsilon

on the whole energy disc of radius R=pi*k*r. Endpoints and the actual
critical energy lie in the inner R/8 disc. A Banach Cauchy derivative
estimate controls the derivative of the normalized unit. Differentiating
the literal factorization at its actual stationary point gives

    2*h*Q + (h^2-(l-u)^2/4)*Q' = 0,
    h=lambda-dot_k-(l+u)/2.

The unit lower bound and coarse inner-disc localization absorb the
quadratic h term, yielding `|h|<=2*epsilon*|l-u|^2/R`. The reusable
`norm_critical_sub_midpoint_le_two_zero_gap` proves this for arbitrary
complex endpoints, including coincident endpoints.

Stationarity of K at the actual critical energy is also proved. The
actual relation `squaredCosh(K)=(-1)^k*Delta/2` and Delta'=0 imply K'=0
because squaredCosh' is nonzero there. `SquaredCoshCriticalDisc.lean`
proves its derivative has no zeros for |K|<pi^2, using the free sine zero
isolation and the exact derivative at zero. The quotient estimate itself
bounds K in that disc. No nonzero Delta' assumption is made at a branch
point, and no unproved inverse-chart range is assumed.

## Reuse and remaining scope

`SHARED_CRITICAL_GAP_IMPORT.json` records four selected proved sources
from convexity `135b1fa75525f1bf29841c56722aa528d49de7dc`:

- `AnalyticLocalLipschitz.lean`;
- `ClassicalHillFreeSquareComparison.lean`;
- `NormalizedSquareRootBounds.lean`;
- `ClassicalHillGapQuotientAsymptotics.lean`.

The local analytic derivative, exported squaredCosh derivative and
arbitrary-small whole-gap square extensions are preserved. Existing
compatible `ActionHamiltonianMoments` and `ClassicalHighGapFamilies`
interfaces are retained; unused newer additions are not imported. The
existing prescribed square-root and high-gap-family sources are directly
selected for strict recompilation. No full branch or Miura/L2-only
development is merged. No ZS RealType hypothesis is applied to Hill(-1,-q).

The actual normalized cubic-resolvent gap estimates can now use the
proved diagonal critical separation when shrinking contours. Sharp
normalized root/moment bounds, weighted lp critical remainders, low even
collapsed contours, full rough/global W compatibility, the canonical
scalar L_n=1, physical frequency/action identities and the main frequency
and flow theorems remain open. See `VALIDATION.md` and `source.json` for
the exact checked selection and complete transitive axiom audit.
