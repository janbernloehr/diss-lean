# Actual normalized differential Gardner stationarity

At every real period-one L2 Hill potential and every positive index n,
`exists_hillBaseNormalizedComplexPsi_stationary_analytic_branch` constructs
an actual analytic numerator-coordinate branch from the genuine selected
global normalized roots. Its normalized differential is jointly analytic at
every complex energy and the base source, agrees exactly with the genuine
global normalized differential at that base, and satisfies the actual
infinite mixed normalization equations on a source neighborhood.

Both the coefficient branch and its normalized differential have zero
source Frechet derivative along every actual complex Fourier Gardner
direction `hillL2DiscriminantGardnerDirection` constructed previously.
This is a proved stationary analytic local germ, not a supplied abstract
normalization model.

## Proof chain

- `HillGardnerLocalRootVariation`: differentiate the actual radicand and
  local square identity to prove stationarity of every nonzero local root.
- `ParametricCircleStationarity`: compactness and joint analyticity justify
  differentiating the literal contour integral.
- `HillAbelianGardnerPeriods`: actual contour-root, integrand, and period
  source stationarity, including free-reference contours at another source.
- `HillMixedGardnerVariation`: identify actual Hilbert derivatives through
  scalar coordinates for the finite intrinsic head and controlled infinite
  free tail; project to the actual supported normalization equation.
- `ImplicitRootStationarity`: differentiate the actual implicit zero
  equation; injectivity of the root derivative forces zero root variation.
- `HillNormalizedGardnerStationarity`: retain that injectivity while
  constructing the analytic branch from genuine normalized roots; prove
  zero numerator variation and differentiate the own-period quotient.

The verified shared bijective period chart and genuine global normalized
roots are reused from `articles/kdv-estimates` at `e36a0443e127c72527458d1970ad66ecbef091f2`.
Exactly 239 missing dependencies are imported unchanged; twelve compatible
local variants remain unchanged. Full provenance and both source/local
hashes appear in `SHARED_NORMALIZED_DIFFERENTIAL_IMPORT.json`.

## Validation

Prior strict validation of 572 unchanged selected sources; strict default-limit dependency-order compilation of 239 byte-identical shared normalization dependencies; strict compilation of six new stationarity modules; then a fresh combined transitive axiom audit of all 817 selected modules. Twelve compatible local shared variants are retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 817-module rebuild is claimed.

Fresh audit: 8045 selected declarations and 30623 imported NLS
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur
transitively. Lean 4.33.1, mathlib v4.33.1, warnings as errors and the default
200000 heartbeat limit; no sorry, new axioms or linter exceptions.

## Scope toward the article

This supplies actual normalization-variation input toward the
angle/discriminant identity used in the proof of Lemma 3.2 (69), PDF page26.
Abelian-angle variation and its orientation, entire Dirichlet interpolation,
and differentiation of a genuine open-source physical Hamiltonian identity
remain necessary. The finite-gap quartic value identity alone cannot be
differentiated in arbitrary source directions. Global cross-chart normalized
family compatibility, full rough W, exact leading scalar, sharp bounds,
physical frequency/action identities, and the main theorem conclusions
remain open. Every main statement inventory row is still OPEN.
