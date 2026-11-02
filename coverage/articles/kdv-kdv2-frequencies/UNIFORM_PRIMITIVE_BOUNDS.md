# Actual uniform primitive errors and period-tail bounds

The primitive-bound hypothesis in the preceding scalar estimate is now
discharged for the actual continued Hill primitive. One small complex
potential ball supports every positive fixed contour, with a uniform root
lower bound, source derivative bound and primitive error `O(norm q)`.
The actual off-diagonal period tail has a uniform reciprocal-square bound.
Every selected critical frequency can also be localized inside half the
contour radius. **The full bounded period operator, its inverse and all
article main theorems remain open.**

The potential space remains `C([0,1],ℂ)` with its sup Banach norm.
No rough Fourier-Lebesgue extension or physical frequency identification
is inferred from these estimates.

## Actual discriminant and root estimates

`ClassicalDiscriminantUniformVariation.lean` reuses the existing actual
IVP growth bound in `ClassicalHorizontalStripBounds.lean` and the Banach
Cauchy estimate in `BanachTaylorBounds.lean`. Since the constant-upper
potential obeys `norm((-1,-q))<=1+norm q`, for `|Im z|<=H` and `norm q<1`,

```text
norm(d_q Delta_q(z²)) <= 4*exp(H+3),
|Delta_q(z²)-Delta_0(z²)| <= 4*exp(H+3)*norm q,
|radicand(z²,q)-radicand(z²,0)| <= 16*exp(H+3)²*norm q.
```

These bounds are independent of Re z and the contour index. Source
differentiation uses the continuous-potential norm. No new ODE or spectral
foundation is introduced.

`FreeContourUniformLowerBound.lean` proves
`|sin(z-k*pi)|=|sin z|`. Zero isolation gives a positive minimum on the
compact circle `C(0,pi/4)`. This works on all positive translated circles
and, using the exact free root, gives a positive radicand lower bound a.

`ClassicalUniformRootBounds.lean` chooses

```text
L = 16*exp(pi/4+3)²,
R = min(1,a/(2*L)),
b = sqrt(a/2).
```

For `norm q<R`, the actual radicand norm is at least a/2 on every positive
contour. The proof checks the whole straight source segment from zero to
q, so every `(z²,q)` lies in the actual continuation domain and its
continued root norm is at least b>0. There is no cutoff or avoidance input.

## Uniform actual primitive errors

`ClassicalUniformPrimitiveBounds.lean` restricts the joint primitive
differential to the source direction, obtaining the exact identity
`d_q F=root^(-1)*d_q Delta`. The root lower bound and convex mean-value
inequality give one C>0 such that, on the same ball and all positive circles,

```text
norm(d_q F(z²,q)) <= C,
|F(z²,q)-F_free(z²)| <= C*norm q,
|F(z²,q)+i*k*pi| <= pi/4+C*norm q.
```

The exact free slice and positive-half-plane square-root sign give
`F_free(z²)=-i*z`. These are estimates for the constructed logarithmic
continuation, with no additive period choice or assumed primitive bound.

## Actual period tail and all-mode critical control

`ClassicalUniformPeriodBounds.lean` constructs N, M>=N, one open complex V
containing zero and one K>0 before n,k,q. All scalar entries remain analytic
on V, the complete free matrix is the identity, and for every distinct
n,k>M and every q in V,

```text
|P_nk(q)| <= K/|k-n|².
```

The scalar primitive-bound input is discharged by the preceding actual
estimate. The proved algebraic inequality
`n*k/|k²-n²|² <= 1/(4*|k-n|²)` permits
`K=(5/pi)*(pi/4+C*R)`. This is a uniform entry estimate, not yet an operator
realization or an estimate tending to zero with norm q.

`ClassicalUniformCriticalLocalization.lean` combines a finite head of
continuous free critical charts with the actual small Banach analytic
displacement tail. On one neighborhood, for every positive n,

```text
|sqrt(mu_n(q))-n*pi| < pi/8.
```

The selected mu_n retain analyticity, simplicity, the actual critical
equation and exact free values. The high principal root is identified
with the actual frequency critical root via its positive real part.
Only finitely many head neighborhoods are intersected.

The added `highEnergyContour_diagonal_separation` proves, for z on
`C(n*pi,pi/4)` and w in `closedB(n*pi,pi/8)`,
`|z²-w²| >= (pi²/8)*n`. This is the denominator geometry needed to treat
the diagonal, alongside the existing off-diagonal energy separation.

## Validation and remaining obligations

The checker and complete transitive axiom auditor select the same 57
modules: six new proofs, two newly selected existing dependencies, and
the preceding 49 modules. The tail-formula theorem also retains its
constructed numerator factor identity on the identical neighborhood.
Pinned Lean 4.33.1/mathlib v4.33.1, strict warnings, default heartbeats and
the three-standard-axiom restriction are unchanged. Final counts and all
checked source hashes are in `VALIDATION.md` and `source.json`.

Newer shared real spectral developments were inspected; no new merge was
needed here. Imported shared ancestry remains through `963d5bb`. Canonical
sources and build outputs remain read only.

Next, assemble the diagonal and finite-head estimates into the full bounded
matrix realization and prove its operator-norm analyticity/continuity at
the free identity. Only then can the infinite inverse and convergent entire
normalized family be constructed. Canonical products, global/rough
compatibility, sharp moment sums, physical frequency/action identities,
weighted asymptotics, compact derivatives and actual Birkhoff/PDE flow
remain essential open work. No main-theorem status is changed.

The subsequent [analytic period inverse milestone](ANALYTIC_PERIOD_INVERSE.md)
constructs the full bounded operator, proves operator-norm analyticity and
constructs its analytic two-sided inverse near zero. The convergent entire
normalized family, canonical products and actual main theorems remain open.
