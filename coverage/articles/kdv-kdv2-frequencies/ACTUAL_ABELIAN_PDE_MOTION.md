# Actual physical Abelian angle derivatives for KdV and KdV2

## Domain and actual velocities

For a real smooth period-one potential Q, let q be its actual physical
Fourier coefficient sequence, mu_k the actual labelled Dirichlet energy,
D the actual Dirichlet characteristic and U_k the actual normalized
nonzero deflated root. The actual PDE Fourier velocities reconstruct the
printed physical PDE right-hand sides. No source mean-zero assumption.

```text
K1_k = -2 (Q(0) + 2 mu_k) / D'(mu_k)
K2_k = -2 (-Q_xx(0) + 3 Q(0)^2 + 4 mu_k Q(0) + 8 mu_k^2) / D'(mu_k)
D mu_k[V_j] = r_D(mu_k) K_jk
D moving_r_D(mu_k)[V_j] = Delta(mu_k) Delta_E(mu_k) K_jk
```

These are actual source derivatives, proved at every positive index,
including closed gaps. The shared `HillDirichletVelocityData` merely
packages these actual facts, parity and universal trace stationarity.
Both physical PDE fields instantiate it without supplied spectral models.

## Terminal angles and individual actual integrals

When gap k is open, both trigonometric coordinate variations and the actual
deflated energy identity prove, for every differentiable physical matching
terminal angle epsilon_k,

```text
D epsilon_k[V] = i U_k(mu_k) K_k.
```

This includes terminal bandedges. It does not divide by the vanishing sine
there. Arbitrary other gaps may be closed. A single genuine analytic
Dirichlet Abelian integral germ B_nk works for every such velocity datum:

```text
D B_nk[V] = psi_n(mu_k) K_k.
D correction_nk[V] = psi_n(mu_k) K_k - delta_kn i U_n(mu_n) K_n.
```

The open-gap formula transfers to every differentiable physical matching
extension by uniqueness of its jet on even tangents. At a closed gap a
genuine analytic quadratic correction chart has zero derivative: its actual
signed sheet is zero and its moving derivative is zero since
Delta(mu_k) Delta_E(mu_k)=0. Thus no angle chart is required there.
For own n open, the displayed correction formula holds at EVERY k, using
actual numerator vanishing at closed k different from n.

## Infinite derivative and one common physical angle germ

The actual common analytic correction tail has a summable uniform bound.
The proved operator-norm derivative convergence justifies taking limits
of its differentiated finite sums. No interpolation formula for a growing
polynomial velocity coefficient is assumed.

For ONE genuine complex-L2-analytic raw Abelian angle germ
A_n=epsilon_n-pi+S_n with actual nearby-real physical matching and real
values, the own terminal contribution cancels the single subtraction:

```text
lim_(M -> infinity) sum_(1 <= k <= M) psi_n(mu_k) K_k = D A_n[V].
```

`exists_hillDirichletAbelianAngle_both_pde_variation` chooses ONE such germ
and proves this convergence simultaneously for the actual KdV and KdV2
velocities with their exact K1/K2 profiles. Only the own selected gap n
must be open; every other gap can be closed. This is ordinary partial-sum
convergence, not a separate claim of absolute summability of the displayed
spectral series.

## Validation

Prior strict evidence for all 1043 unchanged selected baseline sources; strict dependency-order compilation of eleven new modules; then a fresh combined transitive axiom audit of all 1054 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1081 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1054-module rebuild is claimed.

Fresh audit: 9590 selected and 32035 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, additional
axioms, heartbeat overrides or linter exceptions. No existing selected
source or provenance record changed.

## Remaining main obligations

The actual convergent Dirichlet spectral sums still need evaluation and
identification with the physical Hamiltonian frequencies (69)/(84).
The raw-angle sign remains as already proved: canonical theta=-A.
Full canonical brackets, Fourier differential at zero, full native Banach
map analyticity and inverse, rough W compatibility, sharp estimates,
action descent and actual PDE flow existence remain open. A finite-gap
Hamiltonian value identity must not be differentiated as an open L2 germ.
All eleven main theorem inventory rows remain OPEN; this is validated
progress toward them, not completion of a main theorem.
