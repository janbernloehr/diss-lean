# Positive normalized moments vanish at actual collapsed high gaps

This step advances Lemma 3.1(iv), PDF pages 25–26. **Every article main
theorem remains open.** The normalized family is still local near zero
in C([0,1], C) with the sup norm. The new collapsed-gap assertion has
one high-contour cutoff; it does not yet cover the finite low head or
the full rough/global source W.

## Actual normalized result

`exists_classicalHill_normalized_moments_with_collapsed_tail` constructs
N,M,U,R, with U open and containing zero, before every positive output
index n and contour index k. It retains:

- R analytic on U and equal to Id at the free potential;
- analyticity of every literal normalized moment;
- exact zeroth normalization `(2*pi)^(-1)*Omega_nk^(0)=delta_nk`;
- vanishing of every odd moment for all positive n,k;
- for k>=M, if the **actual analytic squared Hill gap** is zero, every
  positive moment `Omega_nk^(m+1)` vanishes, for all n and m>=0.

The last assertion includes n=k. Neither a numerator zero at the branch
point nor an open-gap lower bound is assumed. The actual normalized
numerator is the same entire function defined by R, and every original
normalization period is retained.

The generic theorem
`exists_classicalHill_high_collapsed_differential_moments` works near
any continuous complex source. Its neighborhood and cutoff precede the
high contour k, any entire energy numerator P and every positive order.
The collapse criterion is `classicalHillHighSquaredGap a k = 0`, not
an assumed analytic continuation of the integrand.

## Construction through the collapsed point

The reused `ClassicalHillGapQuotients` constructs the actual two roots
l,u with their multiplicities and intrinsic squared gap. Their equality
follows from the squared-gap criterion. The actual shifted primitive
square K has the literal filled factorization

    K(lambda) = (lambda-l)^2 * Q(lambda),

where Q is analytic and nonzero on the complete energy disc. This
includes the collapsed point itself and is proved from the actual root
multiplicities. It is not an assumed model for an open gap.

The reused disc square-root theorem constructs an analytic g with g^2=Q.
Thus J(lambda)=(lambda-l)*g(lambda) is an actual analytic square root of K
on that disc. On a smaller frequency circle, J(z^2) and the actual F_k
have equal squares and are nonzero. Connectedness of the circle supplies
one fixed relative sign. It need not be selected analytically in the
potential.

A possibly different shared square/quotient chart supplies the already
proved analytic H=F_k/continuedRoot. Both charts are restricted to a
common smaller circle, using actual source-annulus coverage. The filled
extension of the positive-order integrand is then

    (signed J)^m * H * P.

It is analytic across the collapsed point. Pulling back with the exact
Jacobian 2*z and applying Cauchy's theorem gives zero, even for the
diagonal normalized differential. No nonzero discriminant derivative
is used at a double zero.

The new reusable criterion
`frequencyMoment_pos_eq_zero_of_continuations` requires only agreement
with filled analytic extensions on the contour. It does not assign
unfilled total-division values at the branch point.

## Verified source reuse

`SHARED_COLLAPSED_GAP_IMPORT.json` records the selected source dependency
import from `articles/kdv-convexity` at
`9d1741ce0f47d05e6bc63deaa43b5cdd043e7848`:

| Source | Role |
| --- | --- |
| `NLS/ComplexAnalysis/TwoZeroDeflation.lean` | Literal filled two-zero factorization, analyticity and nonzero deflated units, including double zeros. |
| `NLS/KdV/ClassicalHillGapQuotients.lean` | Actual common high-gap pair, square deflation, nonzero quotient and uniform quotient bound. |
| `NLS/ComplexAnalysis/AnalyticDiscSquareRoot.lean` | Constructed analytic square root of a nonvanishing analytic function on a disc, without a principal slit hypothesis. |

The existing local analytic spectral derivative, exported squaredCosh
derivative and arbitrary-small whole-gap bound are preserved. The
whole source branch and its L2-only modules are not merged. The existing
`ContinuousSquareRootPath` and `TwoRootQuotientDiscBound` are selected
for direct strict recompilation. All imported NLS dependencies are
included in the transitive audit.

The added actual proofs are
`ClassicalHillCollapsedDifferentialMoments.lean` and
`ClassicalNormalizedCollapsedMoments.lean`. No ZS RealType hypothesis is
applied to Hill(-1,-q), even for a real potential.

## Remaining source obligations

Positive even-moment cancellation at low collapsed contours, and the
full W/rough-topology version of Lemma 3.1, remain open. Sharp normalized
moment/root estimates, the exact nonzero-potential canonical scalar,
physical Hamiltonian-frequency/action/Birkhoff flow identification,
global extension and compact weighted derivatives also remain open.
No main theorem or source-wide Lemma 3.1 inventory row is closed by this
high-tail result.
