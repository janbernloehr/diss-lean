# Exact actual cubic frequency contours

## Genuine analytic filling

For a real period-one L2 spectral source, write F for the actual real-cut
primitive and R=2*sinh(F) for its actual root. The unfilled cubic kernel
is F(E)^3*P(E)/R(E), with an entire numerator P.

At every point of the lowest cut the actual F^2 is already analytically
filled. The exact identity F/R=1/(4*deriv squaredCosh(F^2)) and the
nonzero squared-cosh derivative on the positive real axis construct an
actual analytic local cubic chart. This includes the lowest branch point.

At a nonselected collapsed positive gap, the actual normalized numerator
psi_n vanishes at its intrinsic label a. The actual primitive is already
proved analytic through that gap. The actual canonical root factors as
(a-E)*U(E), with U a nonzero analytic deflated root. Thus psi_n/R is
filled by the negative divided difference of psi_n/U at a. Multiplying by
the actual analytic F^3 gives a genuine local cubic chart.

The canonical `DenseAnalyticExtension` helper glues these charts from the
fixed dense set of nonreal energies. It is byte-identical to main c5bcf634,
already transitively imported/audited at the baseline, and now explicitly
selected and strictly compiled with its canonical hashes recorded.

ONE resulting filled kernel is analytic on the actual filled-square
domain with the SELECTED own gap removed. The own gap is retained even
when closed: its normalized numerator need not vanish and the unshifted
primitive there is -i*n*pi. Literal total-division values at other closed
points are not claimed analytic; the extension supplies the proper values.

## Actual contours at every sufficiently large radius

The filled kernel agrees with the actual kernel on the actual real cut
domain and hence at every nonreal energy. Each centered positive-radius
circle has only two real crossings. Codiscrete congruence therefore proves
that actual and filled kernels have identical circle integrals and circle
integrability, without requiring matching values at those crossings.

Actual finite-gap sources supply a common exterior inside this filled
domain. Cauchy's theorem on closed annuli now proves genuine integrability
and exact independence of the actual cubic outer periods at EVERY
sufficiently large radius. This analytic result needs neither physical
smoothness nor zero mean.

## Actual KdV velocity coefficient and coordinate derivative

For real smooth period-one mean-zero physical Q, the previously verified
actual cubic contour LIMIT is the actual finite-gap Dirichlet velocity
sum V_n(Q,N), with every open gap and the selected index included in N.
Exact contour independence identifies that limit with every large contour:

```text
V_n(Q,N) = (4/(i*pi))*integral F(E)^3*psi_n(E)/R(E) dE.
```

All integrals are genuine counterclockwise positive-radius centered
circle integrals. The factor and the positive physical Fourier time
convention are preserved. Combining this exact identity with the actual
finite-gap KdV scalar coordinate variation gives

```text
D Z_n[actual KdV field]
  = ((4/(i*pi))*integral F^3*psi_n/R) * (i*z_n).
```

This applies to every differentiable nearby-real matching scalar
coordinate germ, including when its selected gap is closed. One radius
is chosen before the germ. Existing verified results provide actual
analytic matching germs. A zero coordinate jet at a closed gap does not
identify its Hamiltonian frequency.

No finite-gap-only Hamiltonian VALUE identity was differentiated as an
open L2 germ; the exact coefficient follows from actual analytic filling,
Cauchy contour independence and the independently verified physical limit.

## Validation

Prior strict evidence for all 1079 unchanged selected baseline sources; strict dependency-order compilation of six additions (one unchanged canonical dense-extension helper and five new proof modules); then a fresh combined transitive axiom audit of all 1085 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1114 frozen source/checker/provenance hashes, all 26 unchanged provenance records plus one new verified canonical dense-extension record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1085-module rebuild is claimed.

Fresh audit: 9798 selected and 32228 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, additional
axioms, heartbeat overrides or linter exceptions. All 1079 baseline
selected sources and all 26 prior provenance records are unchanged.

## Remaining main obligations

For (69), deform the actual cubic contour through finitely many intrinsic
gap circles, prove the required actual gap-moment cancellations and
identify the actual Hamiltonian frequency, retaining the own closed pole.
The local charts and global filled kernel proved here supply the analytic
input to that deformation.

The quintic coefficient and translation/mass renormalization for (84),
full canonical brackets, Fourier zero jet, full native Banach analytic
map and inverse, rough W compatibility and normalization, sharp estimates,
frequency action descent and actual PDE flow realization remain open.
All eleven main rows remain OPEN. Current dependencies are listed in
`source.json`; prior milestone dependency snapshots are retained separately
as historical evidence.
