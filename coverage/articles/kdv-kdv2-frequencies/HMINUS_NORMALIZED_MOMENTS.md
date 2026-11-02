# Actual normalized Hill differentials and moments in Hminus1

`exists_hillHminus_analytic_normalized_moments` constructs one complex
`PeriodOneHminusOne`-open neighborhood of zero before every positive
numerator index, positive contour index and nonnegative moment order.
The topology is the original unit-period Sobolev minus-one norm.
Every normalized numerator is jointly analytic in energy and rough
potential on the whole energy plane times this neighborhood. Every
literal moment is analytic there, and all zeroth periods have the exact
source normalization. No inverse or normalized numerator is supplied
as a hypothesis of the existence theorem.

## Constructed uniform estimates

`HillHminusOneCriticalControl.lean` proves, on one common neighborhood,

    |sqrt(critical_n(q)) - pi*n| < pi/8.

The proof combines the actual ZS critical displacement with the fixed
Miura energy translation, then intersects finitely many neighborhoods
for the low indices. The chart shift is retained. These are critical
energies, not the source's Dirichlet eigenvalues.

The selected shared rough trace approximation and primitive strip
results come from convexity commit `08db7a5`. The actual trace is uniformly
close to the free cosine on high frequency discs, and its continued
primitive has the correct imaginary strip. The elementary shared lemma
`norm_le_two_norm_cosh_add_abs_im` converts these facts into a uniform
high-contour norm bound. Compact source tubes handle the finite head.
Thus `exists_uniform_primitive_bound` proves a common positive constant A
with

    |F(z²,q) + i*k*pi| <= A,  z in C(k*pi,pi/4),

for every positive k. `CompactSliceBounds.lean` contains the reusable
compact-parameter argument. No heartbeat or linter exception is used.

Exact rational circle integration by parts rewrites the actual critical
basis periods as

    P_nk(q) = n * integral (F(z²,q)+shift)*2*z/(z²-critical_n(q))² dz.

The shared `CriticalBasisPeriodBounds.lean` proves that identity and the
circle norm bound. Actual rough critical separation then gives

    |P_kk| <= (80/pi)*A,
    |P_nk| <= ((5/pi)*A)/|k-n|²,  n != k.

The formula uses the original frequency circles and the exact Jacobian
2*z. There is no extra factor i in the source normalization.

## Actual infinite operator and inverse

`HillHminusOnePeriodInverse.lean` extends the positive period matrix by
the identity on nonpositive integer coordinates and zero mixed entries.
The summable reciprocal-square convolution majorant constructs a bounded
operator T on the actual coefficient Hilbert space. Scalar entry
analyticity and the common majorant prove operator-norm analyticity.
Equality on every single-coordinate vector proves T(0)=Id.

The proved generic analytic operator inversion theorem constructs a
smaller rough-open neighborhood and an analytic R satisfying

    T(q) R(q) = R(q) T(q) = Id,  R(0)=Id,  ||R(q)|| <= 2.

`exists_hillHminus_analytic_period_inverse` retains all actual critical,
entire numerator, contour coverage and period data on that neighborhood.

## Actual normalized entire numerators and moments

Quadratic growth of the selected critical energies and their exact
filled factor identity give locally uniform reciprocal-index tails for
the critical numerator coordinates. `HillHminusOneNumeratorHilbert.lean`
constructs their genuine Hilbert-valued entire realization B(lambda,q).

`HillHminusOneHilbertPeriod.lean` defines the actual vector-valued Bochner
contour integral. Continuous bilinear duality commutes with this integral;
equality on the whole coefficient basis identifies the resulting
functional with the actual row of T on every coefficient vector.

The normalized numerator is defined by the continuous bilinear pairing

    Psi_n(lambda,q) = pairing(R(q)e_n, B(lambda,q)).

The defining series converges absolutely, including its positive-index
form. Joint analyticity and the exact entire free slice are proved.
The literal periods satisfy, for every positive n,k,

    (2*pi)^(-1) integral Psi_n(z²,q)/root(z²,q) * 2*z dz = delta_nk.

The equivalent mapped energy-contour statement is also proved. The
nonpositive rows of T and support of every positive inverse column are
proved explicitly.

`HillHminusOneNormalizedMoments.lean` defines the literal moment

    Omega_nk^m(q) = integral (F(z²,q)+i*k*pi)^m
                           * Psi_n(z²,q)/root(z²,q) * 2*z dz.

Every integrand is jointly analytic wherever the actual source sheet is
defined. Parametric circle integration proves analyticity of every
moment on the same rough-open neighborhood, before n,k,m. The mapped
energy-contour equality and the zeroth normalization
`Omega_nk^0/(2*pi)=delta_nk` retain the exact constants.

## Source correspondence and remaining obligations

This is an actual local rough-topology differential/moment construction
toward the material preceding Lemma 3.1 and its analyticity/zeroth-period
clauses (PDF pages 26–27), and the rough frequency extension in Theorem
3.4 (page 31). It does not establish their complete source domains.

Still open are agreement with the previously constructed continuous
normalized family, the source's canonical product normalization including
its exact nonzero-potential leading scalar, rough odd and collapsed-even
moment cancellation, sharp rough moment bounds and summation, and
continuation over the full source neighborhood W. Physical Hamiltonian
frequency identity (69), action descent, weighted frequency asymptotics,
compact derivatives and Birkhoff/PDE flow identification remain open.
All main-theorem inventory rows remain unverified.

## Provenance and validation

`SHARED_HMINUS_PRIMITIVE_IMPORT.json` records the three unchanged selected
shared sources: rough trace control, logarithm strip normalization and
rough primitive strip. Existing critical-displacement and cosine-bound
sources are additionally selected for direct strict checking. No full
branch is merged. The 318 previously selected Lean files remain unchanged,
and all five earlier import records remain valid.

`VALIDATION.md` and `source.json` record the completed strict build and
transitive axiom audit. Builds use private outputs and a read-only
canonical dependency overlay, with pinned Lean 4.33.1/mathlib v4.33.1,
default heartbeats and warnings as errors. Only propext, Classical.choice
and Quot.sound are permitted; no placeholders or new axioms are used.
