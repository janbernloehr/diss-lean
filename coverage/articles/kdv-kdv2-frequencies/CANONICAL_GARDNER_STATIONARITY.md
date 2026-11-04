# Canonical normalized differential source stationarity

At every real period-one L2 Hill base, positive index and complex energy,
every differentiable source extension of the genuine canonical normalized
differential has zero derivative along every constructed complex Gardner
direction, provided it agrees with that differential at nearby real
period-one potentials. This is
`fderiv_hillAbelianSelectedGlobalPsi_extension_gardnerDirection_eq_zero`.

The existence result
`exists_hillAbelianSelectedGlobalPsi_stationary_joint_analytic_extension`
constructs such a jointly analytic extension. It strengthens the previous
base-agreement result to exact agreement at every nearby real potential.
The same branch supplies physical agreement and zero derivative.

## Proof and exact scope

`HillNormalizedGardnerStationarity` now exposes the actual tail-control
certificates used to construct its stationary branch. Its original
existence theorem remains available with the same statement.
`HillCanonicalGardnerStationarity` uses these certificates to match every
actual mixed period to the corresponding physical period nearby. Its own
period stays nonzero by actual analyticity. The verified entire normalized
Hilbert numerator uniqueness theorem identifies the literal quotient with
the genuine canonical global normalized differential at each such potential.

`RealLineDerivativeUniqueness` proves that nearby agreement on a real affine
line determines the complex source derivative in its direction, using the
complex line chain rule and uniqueness of the real derivative. No analytic
identity principle or complex-germ equality is assumed.

`HillRealSourceJetUniqueness` applies this to actual continuous affine
curves in the physical real period-one L2 potential space. Conjugate Fourier
reflection decomposes every even complex direction into two real directions.
Complex linearity identifies derivatives on the whole period-one subspace.
Every actual Gardner direction lies in that subspace, so an arbitrary
differentiable extension inherits the constructed branch's zero derivative.

Only differentiability at the base and actual nearby physical agreement
are required for extension independence. The result does not assert
extension independence on odd Fourier directions. It does not assert
vanishing derivatives in arbitrary source directions.

Eight missing shared nearby root/contour/period-matching and normalized
uniqueness sources are reused byte-identically from estimates snapshot
`e36a0443e127c72527458d1970ad66ecbef091f2`. Twelve compatible local variants
are retained unchanged; `SHARED_NEARBY_NORMALIZATION_IMPORT.json` records
all source/local hashes.

## Validation

Prior strict validation of 817 selected sources, of which 816 are unchanged; strict dependency-order compilation of eight byte-identical shared nearby-matching sources; strict final compilation of the extended stationary-branch module and three new proof modules; then a fresh combined transitive axiom audit of all 828 selected modules. Twelve compatible local variants are retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 828-module rebuild is claimed.

Fresh audit: 8090 selected declarations; 30674 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors, default 200000 heartbeats;
no sorry, added axioms or linter exceptions.

## Remaining source obligations

This finishes canonical normalized numerator stationarity needed in the
Abelian-angle/discriminant calculation used before Lemma 3.2 (69), PDF26.
Actual spectral endpoint and terminal-angle variation, the canonical angle
orientation and entire Dirichlet interpolation still need to be connected.
Physical Hamiltonian frequency identities (69)/(84), full rough W and
cross-chart compatibility, exact leading scalar and sharp bounds, weighted
remainders and compact derivatives, action/Birkhoff realization and PDE
identification remain open. Every main theorem inventory row remains OPEN.
The existing finite-gap energy value identity cannot by itself justify
arbitrary physical Hamiltonian source differentiation.
