# Constructed infinite normalized entire differentials near zero

The actual infinite normalized entire family is now constructed near the
free continuous potential. Its positive-index coefficient sums converge
absolutely, the numerators are jointly analytic in energy and potential,
and every actual contour period equals the Kronecker delta. The exact
free entire functions are retained. **Canonical products, global/rough
compatibility and all article main theorems remain open.**

The potential space is `C([0,1],ℂ)` with its sup Banach norm. One open
complex neighborhood V contains zero and precedes every positive family
index n, contour index k and energy lambda.

## The entire numerator basis as an actual Hilbert map

`ClassicalNumeratorHilbert.lean` defines integer-indexed coordinates equal
to the already constructed entire B_n on positive indices and zero on
nonpositive indices. The selected critical frequencies satisfy half-radius
localization; consequently the actual critical energies obey

```text
|mu_n(q)| >= (pi²/4)*n².
```

On each bounded energy neighborhood, the literal factor identity
`(lambda-mu_n)*B_n=2*n*pi*Delta'_q(lambda)` gives a locally uniform
`|B_n|<=C/n` tail. The apparent quotient centers remain filled by the
existing joint divided difference; finitely many low modes use their
proved analyticity. No numerator bound is supplied as an assumption.

`AnalyticReciprocalTail.lean` proves the reusable sequence theorem:
analytic coordinates and locally uniform reciprocal tails give the genuine
ℓ² realization and its Banach analyticity. The proof bounds a finite head
and the actual punctured reciprocal ℓ² tail. It proves membership before
identifying the total constructor, so the zero fallback cannot occur.

Applied to the actual basis, this yields a jointly analytic map
`B(lambda,q)` into complex ℓ² on the full `ℂ × V`, with every coordinate
proved equal to its specified entire numerator. In particular, this is a
norm-valued analytic statement, not merely coordinate analyticity.
The general principal-root square identity is made public in the existing
`RightHalfPlaneSquareRoot.lean` dependency.

## Convergent normalized entire functions

`ClassicalNormalizedDifferentials.lean` defines

```text
Psi_n(lambda,q) = dualPairing(R(q)e_n, B(lambda,q)),
               = sum_(m>=1) (R(q)e_n)_m * B_m(lambda,q).
```

Here R is the constructed analytic inverse of the actual infinite period
operator, of norm at most two on V. The pairing is complex bilinear,
without conjugation. Hilbert Hölder duality proves absolute convergence
of the literal positive-index scalar sum. Joint Banach analyticity of the
two factors proves joint analyticity of Psi_n on `ℂ × V`; each fixed-q
energy function is explicitly proved entire.

The inverse columns have zero nonpositive coordinates, proved using the
actual period matrix's complementary identity block and the inverse
identity. This auxiliary block is not identified with physical signed
Birkhoff coordinates. The whole free slice is exact:
`Psi_n(lambda,0)=classicalHillFreePsi n lambda` for every complex lambda.

## Every literal contour period

`ClassicalHilbertPeriod.lean` proves integrability of the actual ℓ²-valued
contour vector

```text
integral on C(k*pi,pi/4)
  ((2*z)/root(z²,q)) * B(z²,q) dz.
```

The scalar period of a coefficient combination is a bounded linear
functional obtained by pairing with this Bochner integral. The proved
continuous-linear-map integral identity transports the pairing through
the integral. Its values on every unit Fourier coefficient agree with
the corresponding actual period-matrix row, including the zero mixed
entries. Equality on the complete basis therefore identifies the two
bounded functionals on every ℓ² vector.

Applying that identity to `R(q)e_n` and using `T(q)R(q)=Id` gives, for all
positive n,k and every q in the identical V,

```text
(1/(2*pi))*integral on C(k*pi,pi/4)
  Psi_n(z²,q)/root(z²,q)*(2*z) dz = delta_nk.
```

`normalizedNumerator_energy_period` also proves the literal holomorphic
one-form integral over the actual mapped energy path equals delta_nk.
It retains the positive orientation, exact `2*z` Jacobian and source
`1/(2*pi)` factor, with no additional factor i.

`exists_classicalHill_infinite_normalized_differentials` chooses N,V and
the actual inverse map before all positive indices. It proves joint
analyticity, the free entire slice and every normalization period, and
retains the identical `ClassicalAllContourPeriodData` on V. The separate
series and entire-slice theorems apply to this same selected data.

## Scope, validation and next obligations

This proves the local continuous-potential infinite normalization step
underlying equation (53), on the constructed fixed squared-frequency
contours. It does not prove the source canonical zero/product formula
(52), global spectral-cycle compatibility, uniqueness among unrestricted
entire functions, or the source's full rough-potential version.

The focused checker and complete transitive axiom auditor select the same
78 modules, including all four new proof modules and four newly selected
existing dependencies. The modified square-root dependency is directly
recompiled. Pinned Lean 4.33.1/mathlib v4.33.1, strict warnings, default
heartbeats and the three-standard-axiom restriction are unchanged. Final
counts and checked source hashes are in `VALIDATION.md` and `source.json`.

Canonical zero/product identification and global/rough compatibility are
the next spectral obligations. Sharp frequency moments, physical
Hamiltonian-frequency identities, action descent, weighted asymptotics,
compact derivatives and actual Birkhoff/PDE flow identification remain
essential. No main-theorem status is changed by this local construction.
