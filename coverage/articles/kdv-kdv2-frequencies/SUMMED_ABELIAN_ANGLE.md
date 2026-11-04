# Actual infinite Abelian angle variation

The local raw Abelian angle now has a proved complex source derivative.
For every real period-one L2 potential q and positive selected index n
with open n-th gap, the construction gives actual analytic functions
A and epsilon on a complex L2 neighborhood, with nearby-real matching

```text
A(p) = epsilon_n(p) - pi + sum_(k>=1) regular_correction_(n,k)(p),
D A(q)[X_b] = -psi_n(q,b)/2,                 b in C.
```

Here epsilon is an actual sheeted Dirichlet terminal-angle chart, and the
series is the absolutely convergent actual physical regular correction
sum, not an assumed sequence model. A is real on nearby real potentials.
The selected n-th gap must be open; every other gap may be open or closed.
Terminal bandedges and every filled Dirichlet spectral diagonal, including
zero energy, are retained. These are local angle lifts; the canonical
Birkhoff angle orientation and global angle identification are not claimed.

## Per-gap derivatives

`fderiv_hillRegularAbelianCorrection_open_extension` proves the actual
open-gap correction derivative for every differentiable complex extension
agreeing with the physical correction near real potentials:

```text
D C_(n,k)[X_b] = psi_n(mu_k) K_k(b)
                  - delta_(k,n) I U_k(mu_k) K_k(b).
```

`fderiv_hillRegularAbelianCorrection_closed_extension_eq_zero` proves zero
derivative at every closed gap, including the omitted own index. Its
analytic model factors through the actual moving signed Dirichlet sheet;
both the sheet and its Gardner derivative vanish at a collapsed gap.
No angle coordinate or division by that sheet is used there.

`hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed` proves the
normalized numerator vanishes at each closed other-gap Dirichlet energy.
Thus `fderiv_hillRegularAbelianCorrection_extension` supplies one formula
for all positive k whenever the selected n-th gap is open.

## Differentiation of the actual infinite series

The imported shared construction supplies a finite analytic head and a
high analytic tail on one common complex source neighborhood, with a
summable C/k^2 bound and simultaneous nearby-real physical matching.
It includes actual complex Dirichlet/root/quadratic-ODE construction and
closed-gap analytic extensions.

`tendsto_fderiv_sum_of_summable_uniform_bound` proves operator-norm
convergence of partial source derivative sums to the actual sum derivative.
It uses the uniform holomorphic-limit theorem on a smaller ball, after the
actual scalar series converges uniformly on a larger source ball. A separate
evaluated version handles every fixed source direction. No summability of
derivatives is assumed.

`exists_hillSummedRegularAbelianCorrection_gardner_variation` combines
this analytic derivative limit with the per-gap formulas and the previously
proved actual filled Dirichlet interpolation limit. Its exact result is

```text
D summed_regular_correction_n[X_b]
  = -psi_n(b)/2 - I U_n(mu_n) K_n(b).
```

Adding the already proved actual terminal-angle derivative cancels the
own-gap term. `exists_hillDirichletAbelianAngle_gardner_variation` gives
the displayed local raw angle formula with actual terminal/sheet matching,
source analyticity and reality. It does not formally differentiate an
uncontrolled pointwise series or rely on finite-gap value identities.

## Validation and provenance

Prior strict validation of all 884 unchanged selected sources; strict dependency-order compilation of 75 byte-identical shared analytic correction dependencies; strict compilation of one byte-identical canonical holomorphic-limit helper and five new proof modules; then a fresh combined transitive axiom audit of all 965 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, all source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 965-module rebuild is claimed.

Fresh combined audit: 8939 selected declarations and 31478 imported NLS
declarations. Only propext, Classical.choice and Quot.sound occur
transitively. Lean 4.33.1, mathlib v4.33.1, warnings as errors and default
200000 heartbeats; no sorry, new axioms or linter/heartbeat exceptions.

`SHARED_ANALYTIC_CORRECTION_IMPORT.json` records 75 unchanged imports
from estimates snapshot 82f5fd2f6d0bab28b0137a8ec3b59534d950c1e9 and 13
retained local interfaces. All fourteen shared records and five canonical
reuse records have their exact source and local hashes checked. The new
`CANONICAL_NORMAL_DERIVATIVE_REUSE.json` records the unchanged generic
holomorphic-limit helper. The thirteen old shared records and four old
canonical records, and all 884 prior selected source files, remain unchanged.

## Remaining main-theorem obligations

The raw local Abelian angle still needs identification and orientation
relative to the article's canonical Birkhoff angle. Consequently the
physical canonical angle/discriminant identity and Hamiltonian frequency
identities (69)/(84) are not yet proved. The partial-sum interpolation result
is used with a justified analytic source derivative limit; absolute
summability of its spectral kernel series is not asserted separately.

Full rough W and chart compatibility, exact leading scalar and sharp
root/moment bounds, weighted remainders and compact derivatives,
action/Birkhoff realization and PDE identification remain open.
All eleven main inventory rows remain OPEN. This milestone is progress
on their necessary physical source-variation dependencies.
