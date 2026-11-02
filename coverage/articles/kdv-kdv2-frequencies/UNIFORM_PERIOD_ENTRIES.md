# Actual infinite period entries and uniform tail formulas

One open complex neighborhood of the free continuous potential now supports
the entire scalar period matrix. All entries are analytic there, and the
whole matrix is the identity at zero. On one uniform off-diagonal tail,
the entries have a proved primitive integration-by-parts formula and an
actual quadratic energy separation estimate. **Bounded operator realization,
infinite normalization and the article main theorems remain open.**

The potential space is `C([0,1],ℂ)` with its sup Banach norm. These results
do not assert extensions to the source's rough Fourier-Lebesgue scales.
The critical energies below are zeros of the actual Hill discriminant
derivative; they are not Hamiltonian frequencies.

## Contours and exact free normalization

`NLS/ComplexAnalysis/RightHalfPlaneSquareRoot.lean` proves that the principal
square root of z² is z when Re z>0. It fixes the sign when pulling the free
root and differential back to the positive frequency plane.

`NLS/KdV/FreeHighContourPeriods.lean` uses the actual fixed circles
`C(k*pi,pi/4)` for every positive k. They avoid all free sine zeros, their
squares lie in the energy slit plane, and the continued free root is
`-2*i*sin(z)` there. The exact free numerator pullback is

```text
(psi_n(z²)/root_free(z²))*(2*z)
  = -i/(z-n*pi) + i/(z+n*pi).
```

The negative pole is outside every selected positive closed disc. The
positive pole is inside precisely when n=k. The actual contour integral
is therefore `2*pi*delta_nk`, with positive orientation and no additional
factor i. Every index is covered; the result assumes no isolating-contour
hypothesis from the caller.

## One neighborhood for every matrix entry

`NLS/KdV/ClassicalUniformPeriodEntries.lean` defines, for a single cutoff N,

```text
P_nk(q) = (1/(2*pi))*integral B_n(lambda,q)/root(lambda,q) d(lambda).
```

For k<=N it uses the previously constructed free isolating energy circle.
For k>N it uses the squared image of `C(k*pi,pi/4)`, with the exact Jacobian
`d(lambda)=2*z*dz`. The latter formula is also proved equal to the
holomorphic one-form integral over the actual mapped energy path, reusing
the shared `ClassicalHighContourMoments` path and generic holomorphic
pullback theorem. No new contour convention is introduced.

Only finitely many compact-contour neighborhoods are intersected for the
head. The existing uniform high-contour coverage supplies the entire tail.
The common numerator neighborhood is then intersected with that finite
head neighborhood. `exists_analytic_classicalHill_uniform_period_entries`
chooses N and one open V containing zero before both positive indices n,k.
It proves every scalar entry analytic on V, `P_nk(0)=delta_nk`, and retains
the actual filled numerator factor identity on that same V.

Separate entry analyticity is not asserted to imply operator-norm
analyticity. Neither a bounded infinite matrix nor its inverse has been
constructed by this theorem.

## Actual energy separation and integration by parts

`NLS/KdV/HighEnergyContourSeparation.lean` proves, for n!=k,

```text
z on C(k*pi,pi/4), w in closedB(n*pi,pi/4)
  ==> |z²-w²| >= (pi²/4)*|k²-n²| > 0.
```

The proof factors the energy difference and bounds the frequency difference
and sum using the distinct positive integer centers. The actual selected
critical root lies in the required disc on a constructed common potential
neighborhood at every complex continuous potential. Thus the separation
applies to the actual high critical energies, with both indices quantified
after the cutoff and neighborhood.

`NLS/ComplexAnalysis/RationalCircleIntegrationByParts.lean` proves

```text
integral F'/G = integral F*G'/G²
```

from analyticity near the circle and nonvanishing of G on it. Its proof
integrates the derivative of F/G around the closed circle. It requires no
analytic extension across the enclosed disc.

`NLS/KdV/ClassicalPeriodIntegrationByParts.lean` combines that theorem with
the actual primitive derivative and the filled numerator identity. With
`mu_n=classicalHillUniformCriticalPoint N n q`, it proves the exact formula

```text
P_nk(q) = n * integral on C(k*pi,pi/4)
  (F(z²,q)+i*k*pi)*(2*z)/(z²-mu_n(q))² dz.
```

`exists_classicalHill_uniform_period_tail_formula` supplies one common V,
all-entry analyticity and free identity, and a single tail cutoff M>=N.
For every distinct n,k>M and every q in V, both the actual energy
separation and this formula hold. Its contour, factor and denominator
conditions are discharged using the constructed spectral data.

For a nonnegative contour bound `|F(z²,q)+shift|<=A`,
`norm_classicalHillUniformHighPeriod_le` further proves

```text
|P_nk(q)| <= (20/pi)*n*k*A/|k²-n²|².
```

The constant includes the actual circle length and the Jacobian estimate.
This scalar estimate explicitly retains the primitive-bound hypothesis;
uniform control of A, and especially of the error relative to the free
primitive, remains to be proved.

## Validation and next obligations

The focused checker now selects 49 modules, including all six new proof
modules and the three already imported shared moment/path modules. Its
selection exactly matches the axiom auditor's module list. The checker
uses pinned Lean 4.33.1/mathlib v4.33.1, `autoImplicit=false`,
`warningAsError=true`, and default heartbeats. See `VALIDATION.md` and
`source.json` for the completed run and its transitive audit counts.

The optional `--prepare-only` switch prepares the existing private import
overlay and output directories for focused checks. The default command
still compiles every selected module and runs the full transitive audit.
Canonical sources, canonical build outputs and branch selection remain
unchanged. No new shared branch merge is needed for this milestone.

The next analytic obligation is uniform primitive-error and critical-shift
control strong enough to realize P-Id as a small bounded operator, including
the diagonal and head/tail interactions. The inverse must then produce
convergent entire numerators with all infinitely many periods normalized.
The source's canonical products, global/rough gap and sheet compatibility,
sharp physical frequency moments, action descent, weighted asymptotics,
compact derivatives and actual Birkhoff/PDE flow identification remain
essential. Equations (52)-(53) are not yet proved in full at nonzero
potentials, and no main-theorem status is changed.

The subsequent [uniform primitive milestone](UNIFORM_PRIMITIVE_BOUNDS.md)
discharges the actual uniform primitive bound and proves its error relative
to the free primitive is O(norm q). It also establishes a uniform
reciprocal-square bound for the actual off-diagonal period tail and
all-mode critical localization. Full operator realization and inversion
remain open.
