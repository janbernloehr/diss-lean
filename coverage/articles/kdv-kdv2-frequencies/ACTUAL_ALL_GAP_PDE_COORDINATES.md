# Actual KdV and KdV2 coordinate derivatives at every gap

## Actual maps and source domain

Let q be the actual Fourier coefficient sequence of a real smooth
period-one physical potential Q. No mean-zero hypothesis is imposed.
For each n>=1, z_n is the previously constructed actual scalar
amplitude-weighted Abelian coordinate. Its norm squared is the actual
action, and it has a genuine complex-L2-analytic scalar matching germ at
EVERY real source, including a closed own gap.

K1_k and K2_k are the exact actual Dirichlet velocity profiles already
proved in `ACTUAL_ABELIAN_PDE_MOTION.md`. V1 and V2 are the actual Fourier
velocities reconstructing the literal physical KdV and KdV2 right-hand
sides. The positive physical Fourier time convention is retained.

## Closed own gaps

The actual gap-division-free terminal factor has a genuine analytic germ

```text
T = r_D(mu_n)/U_n(mu_n) - (mu_n - tau_n).
```

At a closed own gap its value is zero. Both the actual moving signed-sheet
derivative and the actual Dirichlet energy derivative in either PDE field
are zero: use actual r_D(mu_n)=0 and Delta(mu_n)*Delta_E(mu_n)=0 in the
proved velocity pair. The actual midpoint derivative is zero by universal
trace stationarity. Therefore D T[V]=0, including its nonzero deflated-root
coefficient. No terminal angle or gap division is needed.

The actual coordinate germ factors as T times an analytic prefactor.
The product rule proves D z_n[V1]=D z_n[V2]=0 at a closed own gap. This is
a derivative proof; it does not infer it merely from z_n(q)=0.

## Open own gaps and universal physical matching jets

The actual phase is exp(i*A_n), so its derivative is i times the phase
times D A_n[V]. The previous normally convergent correction-series result
computes D A_n[V] as the limit of the actual Dirichlet partial sums.
The genuine analytic square root of the actual local contour action is
stationary: literal contour differentiation and actual all-energy trace
stationarity give the zero action derivative.

Combining phase and amplitude proves, for EVERY differentiable complex
extension C agreeing with the actual coordinate on a nearby-real physical
neighborhood, and BOTH actual PDE fields,

```text
lim_(M -> infinity) [sum_(1 <= k <= M) psi_n(mu_k)*Kj_k] * (i*z_n)
  = D C[Vj],                 j=1,2.
```

This statement has NO own-gap opening hypothesis. At closed own gaps the
sequence is identically zero by its physical z_n factor and the actual
derivative is zero by the terminal-factor proof. Actual even-jet
uniqueness transfers the law to every physical matching extension.

`exists_hillDirichletAbelianCoordinate_both_pde_extension` constructs ONE
genuine scalar complex-L2-analytic coordinate germ with BOTH PDE derivative
limits and ONE physical matching neighborhood, with arbitrary closed gaps.
This is a scalar statement, not full weighted Banach-map analyticity.

## Exact finite-gap reduction

Every closed gap k has a zero coordinate-velocity summand. If k differs
from n, the actual normalized numerator vanishes at its Dirichlet energy.
If k=n, the physical coordinate itself vanishes.

If all gaps above N are closed, the coordinate partial sums eventually
equal their finite sum through N. Uniqueness of the already proved limit
therefore gives the exact actual PDE derivative

```text
D C[Vj] = [sum_(1 <= k <= N) psi_n(mu_k)*Kj_k] * (i*z_n),   j=1,2.
```

This covers open and closed own gaps and every matching differentiable
extension. The finite-sum identity follows from actual spectral zeros and
proved analytic derivatives. It does not assume Hamiltonian frequency
values or a polynomial-growth high-energy interpolation formula.

## Validation and remaining main obligations

Prior strict evidence for all 1054 unchanged selected baseline sources; strict dependency-order compilation of six new modules; then a fresh combined transitive axiom audit of all 1060 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1087 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1060-module rebuild is claimed.

Fresh audit: 9613 selected and 32058 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, additional
axioms, heartbeat overrides or linter exceptions. All existing selected
sources and all provenance records remain unchanged.

Evaluate the actual finite Dirichlet spectral sums and identify them with
the Hamiltonian frequency identities (69)/(84). Full canonical brackets,
Fourier differential at zero, full native Banach-map analyticity and
inverse, rough W compatibility, sharp estimates, action descent and actual
PDE flow existence remain open. Do not differentiate a finite-gap-only
Hamiltonian VALUE identity as an open L2 germ. All eleven main theorem
inventory rows remain OPEN. This milestone is progress toward them.
