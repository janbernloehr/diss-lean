# Actual rough normalized second moments

This milestone proves the actual high-gap normalized second-moment bounds
near zero in the complex Hminus1 topology. Every article main theorem
remains OPEN. In particular, these estimates do not identify a physical
Hamiltonian frequency or prove the full source domain W.

## Constructed kernel and exact moment identity

`NLS/SequenceSpaces/QuadraticPoleKernel.lean` proves that quadratically
growing selected poles have an open pole complement. A finite head and
uniform reciprocal tail realize the literal coordinates

    W_j(lambda) = j/(lambda-mu_j)^2, j>0; W_j=0 otherwise

as a genuine analytic l2 vector. The realization agrees with every
coordinate; it is not a fallback at admissible energies. This generic
argument does not require an exhaustive spectral zero set.

`HillHminusOneMomentKernel.lean` applies it to the actual rough critical
energies. All original frequency circles avoid every selected pole, by
the proved diagonal and off-diagonal separation. The actual primitive
power times this Hilbert kernel has a genuine Bochner circle integral.
`CriticalBasisPowerPeriods.lean` gives scalar integration by parts using
the filled numerator factor identity and only contour nonvanishing of
the selected denominator.

`HillHminusOneNormalizedMomentKernel.lean` proves, for all n,k>0 and m>=0,

    Omega_nk^m = (2*pi)/(m+1) * pairing(R(q)e_n, K_km(q)),
    K_km(q) = integral F_k(z^2,q)^(m+1) * 2*z * W(z^2,q) dz.

The exact positive coefficient expansion is absolutely convergent.
Continuous coordinate maps commute with the Bochner integral; equality
of genuine l2 vectors and continuous bilinear duality justify the result.
No unproved exchange of an infinite scalar sum and an integral occurs.
The construction never divides by the discriminant derivative or assumes
that the currently selected rough critical points exhaust all its zeros.

`exists_hillHminus_weighted_moment_kernel_family` constructs this identity
on the same weighted family with all earlier operator, inverse, free,
entire numerator, moment analyticity, exact zeroth-period and odd-moment
data retained.

## Actual cut root, critical pole and collapsed periods

`HillHminusOneCriticalGapCutRoots.lean` constructs a root of the same
retained whole-disc square K and exact actual endpoint pair l,u used in
the quadratic critical localization. Its endpoint quotient is nonzero
by the proved free-normalized estimate. On the gap-sized disc off the
straight cut,

    |B(z)| <= 3*|l-u|/(pi*k).

The bound is independent of the auxiliary radius. The root, pair, filled
square, actual primitive-square matching, quadratic critical displacement,
quarter-gap pole localization and exact collapsed critical=endpoint are
retained together. The root extends analytically through a collapsed gap
and its value at the endpoint is proved to be zero by continuity.

`HillHminusOneWeightedCutPeriods.lean` fixes one sign on the connected
frequency circle and proves the exact weighted contour deformation to
an energy circle, with Jacobian 2*z. Critical weights may have poles
inside the contour. `HillHminusOneCriticalPrimitivePeriods.lean` constructs
one rough neighborhood and high cutoff before every critical index and
power. It keeps every squared critical denominator, including the diagonal.

`CollapsedPowerPeriods.lean` fills B(z)^(m+2)/(z-l)^2 with the analytic
divided slope at a collapsed gap. Its integral is zero. This also handles
power two: the ordinary total-division value at the center need not equal
the filled value. Equality on the contour is sufficient.

`HillHminusOneGapPairUniqueness.lean` identifies any two actual pairs on
the same disc as multisets, including multiplicities. Endpoint ordering
therefore does not affect the gap norm or any subsequent estimate.

## Sharp normalized second moments

`HillHminusOneNormalizedGapMomentBounds.lean` proves actual Hilbert
remainder estimates and uses exact zeroth normalization to control the
diagonal inverse coefficient. Write x_k=|l-u|^2/k^2 and let B>0 be the
uniform cut-bound constant. The actual second moments satisfy

    |Omega_kk^2| <= 96*pi^2*B^3*x_k,
    |Omega_nk^2| <= (1024/(3*pi)*B^4+64/(3*pi^2)*B^3)*x_k^2, n!=k.

Every positive-order normalized moment vanishes at a collapsed high pair,
for any coefficient operator R; the statement uses the actual kernel
identity and filled collapsed-period cancellation.

`HillHminusOneTwoWeightedMomentBounds.lean` moves the bounded reciprocal
square weight to the actual Hilbert kernel and proves

    |Omega_nk^2| <= 1376*pi^2*B^3*n^2*x_k/k^2.

`exists_hillHminus_weighted_second_gap_bounds` constructs all these bounds
on one rough-open neighborhood U and one high cutoff M, before q,n,k and
every actual unordered pair on the retained disc. It retains the complete
weighted normalized family on V with U contained in V, the actual cut data
on U, exact original periods and all moment analyticities and odd
cancellations. The two-sided analytic inverses and norm bounds are proved,
not assumptions supplied in place of construction. The cut constant in
this construction is 3/pi.

## Scope and next obligations

These are actual rough analogues of the high-gap moment estimates needed
for the source second-moment frequency series, around Lemma 3.1 and
Theorem 3.4, PDF pages 26–27 and 31. The identities retain the source
normalization 1/(2*pi), the actual shifted primitive, critical lambda-dot
energies and exact original contour. The critical energies are not
Dirichlet eigenvalues.

A summable actual rough gap majorant is still needed, with the correct
Miura energy shift and actual pair/counting identification. The continuous
potential norm budget cannot be used as a uniform bound on a rough ball.
After this, the existing analytic tail summation can construct the rough
moment-frequency series. Physical identity (69), full W continuation,
action descent, the exact canonical product prefactor, sharp root
asymptotics, weighted frequency/compact-derivative claims and actual
Birkhoff/PDE flow identification remain open. Collapsed positive moments
for the finite head in the full required scope also remain open.

## Validation

Eleven new proved modules are added. All 353 previously selected Lean
sources remain byte-identical and all seven shared import provenance
records remain valid. The focused checker and transitive audit select the
new sources in dependency order. `VALIDATION.md` and `source.json` record
the final strict build and audited declaration counts. Checks use pinned
Lean 4.33.1/mathlib v4.33.1, default heartbeats and warnings as errors, with
private outputs. Only propext, Classical.choice and Quot.sound are allowed.
Canonical main remains read only and unchanged. No main inventory row is
marked verified.
