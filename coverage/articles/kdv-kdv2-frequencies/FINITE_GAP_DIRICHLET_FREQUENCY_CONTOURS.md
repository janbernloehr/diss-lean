# Actual finite-gap Dirichlet frequency contours

## Precise finite-gap scope

An actual real period-one Hill potential has finitely many open positive
gaps. For each selected n>=1 a proved cutoff N>=n contains them all.
Including n is essential even if its own gap is closed: psi_n(mu_n) need
not vanish there. The other closed gaps have zero numerator values.

Let D be the actual Dirichlet characteristic, mu_k its actual complete
simple positive-labelled root sequence and psi_n the actual globally
normalized numerator. These are the previously verified physical maps.

## Exact actual partial fractions and moments

The proved complete positive-index interpolation reduces to a finite sum:

```text
psi_n(w)/D(w) = sum_(1 <= k <= N) [psi_n(mu_k)/D'(mu_k)]/(w-mu_k),
                                                       D(w) != 0.
S_l = sum_(1 <= k <= N) mu_k^l * psi_n(mu_k)/D'(mu_k).
```

The filled interpolation equality also holds at every complex energy,
including the actual roots and their zero-energy case. No Dirichlet
canonical product or fixed normalized leading scalar is postulated.

Cauchy's formula pairs every analytic test function f with these actual
residues on an enclosing circle with actual zero-free characteristic:

```text
(1/(2*pi*i)) integral f(w)*psi_n(w)/D(w) dw
  = sum_(1 <= k <= N) f(mu_k)*psi_n(mu_k)/D'(mu_k).
```

Actual complete-spectrum circle selection proves that all sufficiently
large selected energy circles are zero-free and enclose the required
finite roots. This gives the exact polynomial moments S_l on the same
circle sequence. Their values are independent of the valid finite-gap
cutoff, provided it contains the selected n.

## Both actual physical PDE velocity polynomials

For the previously proved actual KdV/KdV2 coefficient profiles, the finite
Dirichlet velocity sums are exactly

```text
Vsum1 = -2*Q(0)*S0 - 4*S1
Vsum2 = (2*Q_xx(0)-6*Q(0)^2)*S0 - 8*Q(0)*S1 - 16*S2.
```

They also equal the actual Dirichlet contour coefficients obtained from

```text
f1(w) = -2*(Q(0)+2*w)
f2(w) = -2*(-Q_xx(0)+3*Q(0)^2+4*w*Q(0)+8*w^2).
```

For every real smooth period-one source Q, every positive n, and EVERY
differentiable complex extension C matching the actual coordinate z_n
nearby on the real physical source, both literal PDE derivatives satisfy

```text
D C[actual_PDE_j] = Vsum_j*(i*z_n),                    j=1,2.
```

Consequently they equal the displayed genuine Dirichlet contour
coefficients times i*z_n on every sufficiently large selected circle.
No own-gap opening or source mean-zero hypothesis is imposed.
The closed-own coordinate derivative is zero, but the retained own
residue is not discarded and no frequency is inferred from that zero.

## Uniform actual Laurent remainders

The exact finite principal-part expansion gives genuine constants
R,C2,C3>0, depending on the actual source and finite cutoff, such that
for ||w||>=R with D(w)!=0,

```text
||w||^3 * |psi_n(w)/D(w) - S0/w - S1/w^2| <= C2
||w||^4 * |psi_n(w)/D(w) - S0/w - S1/w^2 - S2/w^3| <= C3.
```

The coefficients and bounds are derived from the actual residues.
The proof uses the exact simple-pole geometric remainders and the lower
bound |w-mu_k|>=|w|/2 on a common exterior. No local diagonal-resolvent
expansion or unproved normalized leading constant is supplied.

## Validation and main obligations still open

Prior strict evidence for all 1060 unchanged selected baseline sources; strict dependency-order compilation of four new modules; then a fresh combined transitive axiom audit of all 1064 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1091 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1064-module rebuild is claimed.

Fresh audit: 9678 selected and 32123 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, new axioms,
heartbeat overrides or linter exceptions. All existing selected sources
and all provenance records are unchanged.

The Dirichlet polynomial contours still need comparison with the source's
actual F^3*psi_n/R and F^5*psi_n/R contours. A local diagonal-resolvent
D/R expansion is a remaining necessary dependency of the proposed route;
it is not proved by the Laurent estimates above. Actual Hamiltonian
frequency identities (69)/(84), closed-frequency identification, full
canonicality, Fourier zero jet, full native Banach map and inverse,
rough W compatibility, sharp estimates, action descent and PDE flow
existence remain open. Do not differentiate a finite-gap-only Hamiltonian
VALUE identity as an open L2 germ. All eleven main inventory rows remain
OPEN; this is progress toward their actual frequency identification.
