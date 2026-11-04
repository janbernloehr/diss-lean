# Actual Dirichlet and signed-sheet motion for KdV and KdV2

## Physical state boundary terms

The actual scalar sine state s has s(0)=0, s_x(0)=1 and s(1)=0 at a
Dirichlet energy E. Write beta=s_x(1), chi=c_x(1), with c the actual cosine
state. Both the square state and mixed state obey the verified third-order
kernel system. Its genuine Lenard concomitant gives

```text
integral s^2 L_E(P) = -2 P(0) (beta^2-1),
integral c s L_E(P) = -2 P(0) chi beta.
```

The boundary terms are retained. The proof holds for every smooth complex
period-one potential, every complex Dirichlet energy and every evaluated
differential polynomial P. No gap-opening assumption is used.

## Actual branch normalization

The previously proved actual rough branch gradient and physical Fourier
realization identify the branch derivative with the first integral divided
by its actual scalar state mass M. The actual Wronskian and trace give

```text
beta r_D = beta^2-1,
M = D_char'(E) beta.
```

The nonzero actual slope and characteristic derivative therefore yield

```text
D mu[X_(L_E(P))] = r_D(mu) K,
K = -2 P(0)/D_char'(mu).
```

This is proved for every analytic actual Dirichlet branch at a real smooth
period-one source. No branch velocity is supplied as a hypothesis.

## Moving signed sheet, including terminal band edges

The actual slope potential derivative is the verified physical combination
of square and mixed scalar forcing integrals. The boundary terms above
reduce it to `D beta[X_(L_E(P))]=-2 P(0) chi`.

The trace is stationary in the same actual direction. The full moving
spectral-parameter chain rule gives the source and energy terms of r_D.
The actual Wronskian energy identity

```text
2 D_char' chi + (2 beta_E-Delta_E) r_D = Delta Delta_E
```

then yields

```text
D r_D(mu)[X_(L_E(P))] = Delta(mu) Delta_E(mu) K.
```

There is no division by r_D. The proof therefore includes terminal band
edges, where differentiating r_D squared alone would not determine the
sheet derivative. Other gaps and the selected gap may also be closed.

## Both actual printed PDE fields

The article adapter uses the proved exact seeds

```text
P1(E)=q+2E,
P2(E)=-q_xx+3q^2+4Eq+8E^2.
```

Their Lenard expressions are the literal printed KdV and KdV2 fields,
whose Fourier realization was already proved. Thus their respective actual
coefficients in both motion formulas are

```text
K1 = -2(q(0)+2mu)/D_char'(mu),
K2 = -2(-q_xx(0)+3q(0)^2+4mu q(0)+8mu^2)/D_char'(mu).
```

Source mean zero is not required. Physical coefficient reality at the base
is explicit; real physical Q supplies it by the already proved
`isRealHillPotential_hillContinuousCoefficients` theorem. Every analytic
actual branch with a nearby complex characteristic-root germ is covered.

All five former private DirichletLenardTest proofs are now promoted or
subsumed. Reusable state, branch and sheet results live in `NLS/KdV`;
the specific PDE adapters live in `NLS/Articles/KdVKdV2Frequencies`.

## Validation and remaining obligations

Prior strict evidence for all 1030 unchanged selected baseline sources; strict dependency-order compilation of four new proof modules; then a fresh combined transitive axiom audit of all 1034 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1061 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1034-module rebuild is claimed.

Fresh audit: 9483 selected and 31928 imported NLS declarations. Only
`propext`, `Classical.choice`, `Quot.sound`; Lean4.33.1/mathlib4.33.1,
warnings as errors, default200000heartbeats. No sorry, added axioms,
heartbeat overrides or linter exceptions.

The actual terminal endpoint velocities are proved. Stationarity of the
full normalized source differentials in the PDE directions, the summed
Abelian phase velocities and actual Hamiltonian frequencies (69)/(84)
remain required. Full canonicality, the Fourier differential at zero,
full native Banach coordinate analyticity/inverse, rough W compatibility,
sharp estimates, action descent and physical PDE flow realization remain
open. The finite-gap Hamiltonian value identity is not differentiated as
an open L2 matching germ. All eleven main theorem rows remain OPEN.
