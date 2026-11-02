# Exact all-order squared-resolvent formulas for actual normalized moments

This step supplies an actual contour formula for the estimates following
Lemma 3.2 and used in Lemma 3.3 (PDF pages 27–30). It is an alternative
proved representation, not an identification of a physical frequency or
a proof of the sharp estimates themselves. **Every article main theorem
remains open.** The constructed normalized family is still local near
zero in C([0,1], C) with the sup norm; full rough/global W compatibility
is not asserted.

## Exact formula and normalization

Write `a_j=(R(q)e_n)_j`, where R is the actual inverse period operator,
and let `mu_j` denote the selected **critical energy**, source lambda-dot_j
(not the source Dirichlet eigenvalue). For every m>=0 and positive n,k,
the proved formula is

    Omega_nk^m = (2*pi)/(m+1) * sum_{j>=1} j*a_j *
      integral_C(k*pi,pi/4) F_k(z^2)^(m+1) * (2*z)
        / (z^2-mu_j)^2 dz.

The positive-index sum is outside the integral and converges absolutely.
The frequency-to-energy Jacobian is exactly 2*z. There is no extra i in
the original source normalization `Omega_nk^0/(2*pi)=delta_nk`. In
particular, order two has coefficient 2*pi/3 and primitive power three.

`exists_classicalHill_normalized_resolvent_moments` constructs N,U,R
before every positive numerator/contour index and every moment order.
It retains R analytic, R(0)=Id, its norm bound two, analyticity of all
literal moments, exact zeroth periods and every all-mode odd cancellation,
together with this absolutely convergent formula. The stronger helper
`ClassicalAllContourPeriodData.normalizedMoment_resolvent_series` applies
to every existing D and R; it can therefore be used with the twice-
weighted inverse and the earlier canonical zero/product construction.
No new scalar normalization of the canonical product is assumed.

## Proof and the infinite series

`ClassicalCriticalResolvent.lean` constructs the actual Hilbert vector

    C(lambda,q) = numeratorHilbert(lambda,q)/(2*pi*Delta'(lambda,q)).

It is jointly analytic on the open set where Delta' is nonzero. The
existing filled basis identity proves its literal positive coordinates
`C_j=j/(lambda-mu_j)`; all nonpositive coordinates are zero. Completeness
of the selected signed critical labels, together with the already proved
diagonal and off-diagonal contour separation, proves Delta' is nonzero
on every original circle, including all low modes. No assertion that a
high asymptotic cutoff includes the finite head is used.

The negative energy derivative W=-C' is a genuine Hilbert vector with
coordinates `W_j=j/(lambda-mu_j)^2`. Continuous coordinate evaluations
commute with the Banach derivative, which proves this identity directly.
W is analytic in energy off the critical set. This construction needs
neither a separately assumed square-summability estimate nor additional
index weights on the inverse columns.

`CirclePowerIntegrationByParts.lean` proves closed-circle integration by
parts for F^m*F'*G, using only analyticity near the contour. The functions
may have singularities inside. Applied to the actual primitive and the
pairing of C with R(q)e_n, it produces the exact coefficient 2*pi/(m+1).

`ClassicalNormalizedMomentResolvent.lean` defines the Hilbert-valued
Bochner integral of `F_k^(m+1)*(2*z)` times W(z^2). Its continuous scalar
coordinate evaluations give the literal individual contour integrals.
Pairing this integral with the actual inverse column yields the moment.
Hilbert Holder summability then proves absolute convergence of the
positive-index sum outside the integral. Thus the series interchange is
justified by a proved Banach integral and continuous linear maps.

The general formula includes the critical pole associated with j=k.
It does not require the integrand to extend inside the contour, and it
does not discard the diagonal residue. The helper also requires no
unproved normalized numerator zero at a branch point.

## What remains

The formula prepares the cubic primitive/gap contour estimates needed
for sharp normalized moments and frequency remainders. It does not yet
supply the source Lemma 3.3 cubic-gap off-diagonal estimate or its precise
diagonal leading term. Those still require actual estimates on the
shrunk contours and the normalized root/residue coefficients.

Low even collapsed moments, full W/rough-topology compatibility, the
exact nonzero-potential canonical scalar L_n=1, physical Hamiltonian-
frequency/action identities, summable corrections, weighted asymptotics,
compact derivatives and actual Birkhoff/PDE flow identification remain
open. No main theorem inventory row is marked verified.

All three new sources are reusable shared-library proofs. See
`VALIDATION.md` and `source.json` for the current strict compilation and
complete transitive axiom audit.
