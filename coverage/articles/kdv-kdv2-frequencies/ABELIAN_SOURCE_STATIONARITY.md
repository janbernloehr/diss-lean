# Actual gap data and Abelian source stationarity

Actual logarithmic contour moments, gap midpoints and full squared gap
lengths have zero source derivative along every constructed complex Gardner
direction. These results include closed gaps. The actual Cauchy-deflated
unit and its nonzero local root are stationary throughout their filled
intrinsic disc, including the original gap endpoints.

At an open gap, the physical half-length has a stationary analytic local
extension. Every differentiable extension agreeing with it on nearby real
period-one L2 potentials has the same zero Gardner derivative. No analytic
half-length at a closed gap is asserted.

## Actual normalized primitives and terminals

`exists_hillDeflatedNormalizedDifferential_stationary_analytic_gap_chart`
constructs a genuine jointly analytic normalized deflated differential on
an open chart covering the entire closed gap. It is stationary in the
source and agrees with the actual physical normalized differential at
nearby real potentials, including filled endpoint values.

`exists_hillAbelianCosinePrimitive_stationary_joint_analytic_open_gap_chart`
constructs the actual normalized cosine primitive on a convex angle chart
containing the full segment from -pi to pi. It is jointly analytic, anchored
exactly to zero at pi, and agrees with the physical primitive for nearby
real potentials. Its source derivative vanishes along every actual complex
Gardner direction. Its angle derivative is exactly the actual physical
cosine differential.

`exists_hillDirichletAbelianIntegral_stationary_source_decomposition`
constructs genuine analytic integral and sheeted terminal-phase branches
B and epsilon, with nearby-real physical and Dirichlet-label agreement.
At the base, for each complex Gardner direction X_b,

```text
D B[X_b] = hillAbelianCosineDifferential(e) * D epsilon[X_b].
```

This is the exact remaining terminal contribution after proving that the
entire actual source contribution vanishes. It is valid also when the
Dirichlet terminal is at a bandedge; no division by its vanishing sine or
sheet root is used. It does not yet evaluate D epsilon[X_b].

## Proof chain

- `IntegralSourceStationarity`: actual compact contour/interval derivative
  rules prove stationarity of literal Cauchy transforms and affine-segment
  primitives.
- `StationarySquareRoot`: differentiate an actual local square identity
  at a nonzero differentiable root.
- `HillGardnerGapMoments`: actual mixed spectral radicand derivative,
  logarithmic contour moments and symmetric gap data are stationary.
- `HillGardnerDeflatedRoot`: actual quadratic gap polynomial and Cauchy
  density, filled unit/root, and open-gap half-length variations vanish.
- `HillGardnerFilledDifferential`: retain actual nearby-real canonical
  numerator agreement while constructing the stationary filled quotient.
- `ParametricCosineStationarity`: stationary moving midpoint/half-length
  and filled numerator give stationary literal normalized primitive;
  a moving terminal then contributes only the actual spectral chain rule.
- `HillGardnerAbelianPrimitive`: instantiate these results with actual
  normalized spectral data and actual sheeted Dirichlet terminal charts.

## Shared reuse and validation

Prior strict validation of all 828 unchanged selected sources; strict dependency-order validation of 27 shared sources (26 byte-identical imports and one compatibility import reusing an already proved local spectral-derivative theorem); strict final compilation of seven new proof modules; then a fresh combined transitive axiom audit of all 862 selected modules. Twelve compatible local variants retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 862-module rebuild is claimed.

The new shared closure comes from fixed estimates snapshot
`e36a0443e127c72527458d1970ad66ecbef091f2`. Its split
`JointSpectralDerivativeAnalytic` helper initially redeclared a theorem
already proved in the retained local `JointSpectralDerivative`. The split
file now preserves its imports and reuses that proved declaration; its
source/local hashes and exact adaptation are recorded. The first six shared
dependencies passed before this diagnosis; the compatibility import and
remaining twenty dependencies then passed strict checks. Both original
logs and their successful evidence sequence are retained privately.

Fresh audit: 8254 selected declarations and 30841 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors and default 200000 heartbeats;
no sorry, added axioms, heartbeat increases or linter exceptions.

## Remaining article scope

Terminal-phase variation, including a filled treatment at terminal bandedges,
closed-gap and infinite-tail angle variation, entire Dirichlet interpolation
and the canonical angle orientation remain open. Thus the final angle/
discriminant identity and physical Hamiltonian frequency identities (69)/(84)
are not proved here. Full rough W and cross-chart compatibility, the exact
leading scalar and sharp root/moment bounds, weighted remainders and compact
derivatives, action/Birkhoff realization and PDE identification still remain.
All main theorem inventory rows remain OPEN. The finite-gap energy value
identity alone cannot justify arbitrary Hamiltonian source differentiation.
