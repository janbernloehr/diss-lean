# Actual smooth KdV and KdV2 spectral/action stationarity

## Reusable scalar trace-kernel identity

`ClassicalHillLenardIdentity` defines the literal polynomial expression

```text
L_E(a) = -a''' + 4(q-E)a' + 2q'a.
```

The actual scalar fundamental solutions give a trace kernel G, its spatial
derivative H and its velocity quadratic form J. Their already verified
ordinary derivatives satisfy

```text
G'=H,  H'=2J+2(q-E)G,  J'=(q-E)H.
```

For any evaluated periodic differential polynomial a, the actual function

```text
U = -a''G + a'H - 2aJ + 2a(q-E)G
```

has ordinary derivative `G L_E(a)`. Every endpoint agrees, by actual
periodicity of q and its jets and the proved fundamental-state kernel
endpoint identities. The fundamental theorem of calculus therefore gives
`integral_0^1 G L_E(a)=0`. No isospectral hypothesis or formal integration
rule is substituted for this physical integral proof.

## Actual physical Fourier directions

`HillPolynomialDirections` realizes evaluated differential polynomials
with the actual bounded unit-interval Fourier analysis and canonical even
insertion. It proves physical L2 reconstruction almost everywhere, exact
mean coefficient and conjugate Fourier reality when the evaluated function
is real. Its actual L2 trace derivative is the literal kernel integral.
Consequently actual Lenard directions annihilate that trace.

## Both printed PDE fields

The article adapter computes the exact seeds

```text
a_1(E) = q + 2E,
a_2(E) = -q'' + 3q^2 + 4Eq + 8E^2.
```

Their Lenard expressions are precisely the printed fields

```text
L_E(a_1) = -q''' + 6qq',
L_E(a_2) = q''''' - 10qq''' - 20q'q'' + 30q^2q'.
```

Although the seeds depend on E, the actual Fourier fields do not. Every
complex-energy Hill trace therefore has zero full source differential
along either actual PDE velocity. This holds for every smooth complex
period-one source. The velocities reconstruct the literal physical fields,
have zero Fourier mean, and are real at real physical sources.

For real sources, the proved universal actual contour action derivative
then gives

```text
D I_n[KdV(q)] = D I_n[KdV2(q)] = 0,  every n>=1.
```

Every differentiable nearby-real physical action extension is covered.
The selected gap and any other gaps may be closed. The source itself may
have nonzero mean: no extra source mean-zero hypothesis is imposed.

The former private smooth KdV trace prototype is subsumed by the reusable
Lenard identity, actual Fourier trace derivative and article adapter. It
is no longer an unproved dependency of this step.

## Validation

All 1027 prior selected sources and all 25 provenance records are unchanged.
New reusable results are in `NLS/KdV`; source-specific KdV/KdV2 identities
are in `NLS/Articles/KdVKdV2Frequencies`.

Prior strict evidence for all 1027 unchanged selected baseline sources; strict dependency-order compilation of three new proof modules; then a fresh combined transitive axiom audit of all 1030 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1057 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1030-module rebuild is claimed.

Fresh audit: 9454 selected and 31899 imported NLS declarations. Only
`propext`, `Classical.choice`, `Quot.sound`; Lean4.33.1/mathlib4.33.1,
warnings as errors, default200000heartbeats. No sorry, added axioms,
heartbeat overrides or linter exceptions.

## Remaining main obligations

These are physical source-vector and first-variation identities. They do
not assert a solution flow, its global existence, the actual coordinate
phase velocities, or Hamiltonian frequency formulas (69)/(84). Those
formulas, full canonicality, the Fourier differential at zero, full native
Banach coordinate analyticity and inverse, rough W/chart compatibility,
sharp estimates and action descent remain required. The finite-gap quartic
Hamiltonian value identity is not differentiated as an open L2 source germ.
All eleven main theorem rows remain OPEN.
