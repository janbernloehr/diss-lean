# Actual cubic velocity contour limit

## Full-circle analytic inputs

The actual real-cut primitive F and root R=2*sinh(F) obey
F(conj E)=-conj(F(E)) and R(conj E)=-conj(R(E)) off the real axis.
The scalar Dirichlet characteristic D obeys D(conj E)=conj(D(E))
for every real continuous physical potential, at every energy, by actual
scalar IVP conjugation. The actual selected normalized numerator psi_n
already obeys conjugate reflection.

A reusable theorem proves genuine circle integrability from continuity
along only the closed upper arc and conjugate reflection off the real
axis. The two real crossings may have different sheet limits; the proof
uses agreement on the open lower arc, so finitely many boundary values
do not affect integrability. It assumes no continuation through interior
spectral cuts.

The actual root comparison proves R nonzero everywhere on every
sufficiently large selected circle, including both real crossings. The
actual F^3*psi_n/R integrand is therefore continuous along the closed
upper arc and genuinely integrable on the full circle. The polynomial
Dirichlet integrand is continuous on the circle by actual D nonvanishing.

## Quantitative actual contour comparison

For real smooth period-one mean-zero sources, the proved actual local
kernel expansion gives

```text
r * |F(E)^3*D(E)/R(E) + E/2 + Q(0)/4| <= A,
```

on the whole energy circle of radius r^2. Independently the actual
normalized numerator satisfies |psi_n(E)/D(E)|<=B/r^2 there. Exact division
by the zero-free actual D gives

```text
r^3 * |F(E)^3*psi_n(E)/R(E)
          - (-E/2-Q(0)/4)*psi_n(E)/D(E)| <= A*B.
```

The energy circle has length 2*pi*r^2, so the genuine contour integrals
satisfy

```text
r * |integral F^3*psi_n/R
        - integral (-E/2-Q(0)/4)*psi_n/D| <= 2*pi*A*B.
```

Their difference tends to zero as the selected frequency radii tend to
infinity. Constants may depend on the source and selected index. No
finite-gap assumption or source-uniform Sobolev ball estimate is claimed
for this comparison.

## Actual finite-gap KdV velocity

If all actual gaps above N are closed and N>=n, the already verified exact
Dirichlet contour identity yields

```text
(4/(i*pi))*integral F(E)^3*psi_n(E)/R(E)
    --> kdvDirichletVelocitySum(Q,q,n,N).
```

This is the actual finite spectral velocity coefficient in the proved
physical KdV scalar coordinate derivative. The literal source factor is
verified algebraically from -2*(Q(0)+2E)=8*(-E/2-Q(0)/4).
The selected own index remains included even when its physical gap is
closed. A vanishing coordinate jet does not determine that mode's
Hamiltonian frequency.

## Validation and remaining main obligations

Prior strict evidence for all 1074 unchanged selected baseline sources; strict dependency-order compilation of five new proof modules; then a fresh combined transitive axiom audit of all 1079 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1107 frozen source/checker/provenance hashes, all 26 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1079-module rebuild is claimed.

Fresh audit: 9760 selected and 32197 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warnings as errors, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, new axioms,
heartbeat overrides or linter exceptions. All 1074 baseline selected
sources and all 26 existing provenance records are unchanged.

This record proves a contour LIMIT. Exact exterior contour independence,
finite-hole deformation to actual gap moments and actual Hamiltonian
frequency identification in (69) remain to be proved. In the finite-hole
argument, retain the selected index even if closed: its normalized
numerator need not vanish and its unshifted primitive is nonzero there.
Do not differentiate a finite-gap-only Hamiltonian VALUE identity as an
open L2 germ.

The quintic local coefficient and mass/translation renormalization for
(84), full canonical brackets, Fourier zero jet, full native Banach map
and inverse, rough W compatibility, sharp estimates, action descent and
actual PDE flow existence remain open. All eleven main rows remain OPEN.
