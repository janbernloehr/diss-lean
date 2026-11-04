# Actual Abelian coordinates and native weighted continuity

## Physical scalar coordinates at every real source

`hillDirichletAbelianCoordinate` is the literal amplitude-weighted
physical phase `sqrt(I_n) P_n`, where `I_n` is the actual Hill action and
`P_n` is the previously constructed branch-independent Abelian phase.
The source uses complex coordinates with `abs(z_n)^2=I_n`. The imported
shared prefactor normalizes `sqrt(2 I_n)` for real Cartesian coordinates;
`hillAbelianAmplitudePrefactor` divides that prefactor by `sqrt(2)`.

The actual all-gap factorization is

```text
z_n = K_n [r_D(mu_n)/U_n(mu_n) - (mu_n-tau_n)] exp(i S_n).
```

Here `K_n` is the analytic positive action-gap prefactor in complex
normalization, `r_D` is the actual signed Dirichlet sheet, `U_n` the
nonvanishing deflated root, `mu_n` the actual Dirichlet label, `tau_n`
the actual gap midpoint, and `S_n` the actual infinite regular correction
sum. No division by the gap length or by the vanishing sheet appears.
The factorization is proved also when the selected gap is closed.

`exists_hillDirichletAbelianTerminalFactor_analytic_extension` builds a
genuine complex L2 analytic extension of the bracketed terminal factor,
with one nearby-real physical matching germ. Its Gardner trace-direction
derivative vanishes at a closed selected gap for every complex energy.
`exists_hillDirichletAbelianCoordinate_analytic_extension` combines this
with the genuine analytic action prefactor and summed regular correction.
Thus every scalar coordinate has an actual analytic local extension at
every real source, with no own-gap opening assumption. Scalar continuity
on the entire real period-one L2 space is proved. Every differentiable
matching extension has the same zero Gardner derivative at a closed gap.

`norm_sq_hillDirichletAbelianCoordinate` proves the exact actual action
identity, and `hillDirichletAbelianCoordinate_eq_zero_iff` identifies its
zero set precisely with the closed selected gap.

## Actual signed weighted map

For every source `SpectralWeight w`, `hillPhysicalAbelianMap w` maps the
actual real weighted L2 potential space to `WeightedCoeff` with target
weight

```text
w(2 n) (1+abs(n))^(1/2).
```

The doubled index is the existing unit-period to even period-two Fourier
convention. The map has zero mode, conjugate negative coefficients and
`z_n*z_-n=I_n`. Membership follows from the proved physical weighted
action series, using `(1+n) <= 2n` for positive n. These are literal
physical coordinates, not a target model supplied as a hypothesis.
The map is defined on all real weighted sources; a later bijection theorem
must use the correct mean-zero leaf.

`continuous_hillPhysicalAbelianMap` proves continuity in the full native
weighted norm even at arbitrary closed gaps. The proof first controls the
locally uniform tails of the actual squared amplitudes by `1/pi` times
the actual weighted action tails. This proves continuity of the total
positive amplitude sum. The exact signed Parseval identity gives

```text
norm(z)^2 = 2 sum_(n>=0) weighted_abs(z_n)^2,   z_0=0.
```

`Coeff.continuousAt_of_coordinatewise_of_norm_sq` then upgrades scalar
continuity and squared-norm continuity to full Hilbert norm continuity,
using the exact finite Fourier Pythagoras identity and locally small tails.
Coordinatewise continuity alone is not used as a substitute for this step.

## Reuse and validation

Eleven sources are imported byte-identically from the fixed estimates
commit `ba58180a96d3fa19baf3f732e7116dbbede8e81a`; thirteen existing local
variants are retained unchanged. `SHARED_ACTION_PREFACTOR_IMPORT.json`
records all 24 entries. The unchanged canonical uniform-tail criterion
is selected, strictly compiled and recorded in
`CANONICAL_COORDINATE_CONTINUITY_REUSE.json`. The prior nineteen provenance
records and all 970 baseline selected sources remain unchanged.

Prior strict evidence for all 970 unchanged selected baseline sources; strict dependency-order compilation of eleven byte-identical shared action-prefactor sources, one byte-identical canonical continuity criterion and six new proof modules; then a fresh combined transitive axiom audit of all 988 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1011 frozen source/checker/provenance hashes, 21 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 988-module rebuild is claimed.

Fresh combined audit: 9180 selected declarations and 31737 imported
NLS declarations; allowed axioms only `propext`, `Classical.choice`,
`Quot.sound`. Lean4.33.1/mathlib4.33.1, warnings as errors and default
200000 heartbeats. No sorry, added axioms or resource/linter exceptions.

## Remaining main-theorem obligations

This advances the physical coordinate foundation of Theorem 1.1. Scalar
complex analyticity and real weighted norm continuity do not yet prove
full Banach-valued complex analyticity. Actual canonical brackets and
source angle orientation, action-gradient identification of contour
tangents, exact Fourier differential at zero, global inverse, negative
regularity and full rough W/chart compatibility remain open. The actual
Hamiltonian frequency identities (69)/(84), sharp estimates, action
descent and physical PDE realization are still required. The previous
physical positive-exponent time correction is retained unchanged.
All eleven main inventory rows remain OPEN; the goal is incomplete.
