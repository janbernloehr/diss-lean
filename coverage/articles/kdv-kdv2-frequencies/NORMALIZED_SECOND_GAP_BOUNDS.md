# Actual normalized second moments at high-gap scale

`exists_classicalHill_normalized_second_gap_bounds` in
`NLS/KdV/ClassicalNormalizedGapMomentBounds.lean` constructs one actual
normalized family near the zero complex continuous potential. There are
positive cutoffs N,M, one open neighborhood U of zero, an analytic period
inverse R, and a positive constant B, chosen before every numerator index
n, high contour index k, and moment order. R is the identity at zero and
has operator norm at most two on U.

Let G_k(q) be the norm of the actual analytic squared-gap function and
write x_k = G_k(q)/k². For every q in U and k >= M, the literal original
normalized moments satisfy

* |Omega_kk^(2)| <= B x_k;
* |Omega_nk^(2)| <= B x_k² whenever n differs from k.

For actual unordered endpoints l,u, G_k = |l-u|². Thus the diagonal
bound is quadratic in the gap length and the off-diagonal bound is
quartic. Both include collapsed gaps. The same constructed family keeps
all-mode moment analyticity, the exact zeroth periods
Omega_nk^(0)/(2*pi) = delta_nk, every odd cancellation, and every positive
moment cancellation at an actual high collapsed gap.

## Proof and reusable dependencies

`ClassicalHillWeightedCutPeriods.lean` proves radius independence for
the actual weighted primitive powers with weights analytic on the
deformation annulus. It then matches them to cut-plane energy periods
with one fixed sign. The exact substitution is lambda=z², d lambda=2z dz;
there is no additional factor i in the source normalization.

`WeightedCutGapBounds.lean` moves the outer energy circle to the actual
gap-length circle. For the diagonal kernel, the excluded cut also
contains the critical point. The preceding quarter-gap localization
therefore supplies its denominator lower bound without crossing the
pole. Collapsed cases are treated by analytic removal or the already
proved actual moment cancellation.

`ClassicalCriticalPrimitivePeriods.lean` constructs all these geometric
and analytic inputs from the actual Hill data on one common family. For
the literal primitive kernel I_jk^p = integral F_k^p/(lambda-lambda-dot_j)²,
it proves diagonal estimates for every power p=m+2 and off-diagonal
estimates for every nonnegative power m. In endpoint notation gamma=|l-u|,
these bounds are

* |I_kk^(m+2)| <= 8*pi*C^(m+2)*gamma^(m+1)/k^(m+2);
* |I_jk^m| <= (32/pi³)*C^m*gamma^(m+1)/(k^m*|k²-j²|²), j != k.

It also proves the actual off-diagonal basis-period bound of quadratic
gap size. Every denominator uses the selected actual critical energy,
not the source's Dirichlet energy label.

`HilbertCoordinateRemainder.lean` proves the coordinate split for the
unconjugated Hilbert pairing. The punctured reciprocal lattice bounds
the actual Bochner period vector after removing its k-th coordinate.
The zeroth normalization forces the k-th inverse coefficient for n != k
to be small with that remainder. Applying the exact second-moment
resolvent formula then preserves the extra off-diagonal gap factor.
The needed lower bound on the diagonal zeroth period is constructed by
operator-norm continuity of the actual period operator at the identity.
It is not an added hypothesis of the final existence theorem.

One explicit choice is B = Bd+Bo, where
Bd = 96*pi²*C³ and Bo = 1024*C⁴/(3*pi)+64*C³/(3*pi²).
The coarse actual endpoint bound gamma <= 2*pi²*k absorbs x_k² into
the diagonal x_k bound. No canonical product scalar is set to one.

## Source scope and remaining obligations

This advances the estimates needed for source Lemma 3.3, following the
moment representation after Lemma 3.2 (PDF pages 27–30). It does not give
the full sharp n,k dependence or the diagonal leading coefficient in
that lemma. The construction is on a local complex continuous-potential
neighborhood; the full rough/global W domain and its topologies are
still open. The finite low even collapsed contours, sharp normalized
root displacement (54), canonical scalar L_n=1, physical frequency
identity (69), Hamiltonian/action/Birkhoff identifications and the main
frequency and flow theorems still require proofs. Every main-theorem
inventory row remains unverified.

`SHARED_CRITICAL_PERIOD_GAP_IMPORT.json` records five selected proved
cut-root/contour sources from convexity commit
`135b1fa75525f1bf29841c56722aa528d49de7dc`, with source and local hashes.
Three existing local extensions are retained. Existing affine/nested
circle homotopy dependencies are now directly selected and recompiled.
The whole branch and its Miura/L2-only modules are not imported. No ZS
RealType wrapper is applied to the Hill coefficient pair (-1,-q).

Validation counts, strict options and the transitive axiom audit are
recorded in `VALIDATION.md` and `source.json` after the completed run.
