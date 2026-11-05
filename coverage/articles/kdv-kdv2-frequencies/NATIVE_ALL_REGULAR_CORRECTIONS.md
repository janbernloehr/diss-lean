# Native physical regular corrections for every positive gap

The declaration `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_all_regular_corrections` constructs one complex period-one L2 ball, one positive bound and a native output Hilbert-valued analytic family indexed by every positive gap. These choices precede all complex sources, real physical sources, gap indices and output indices. Every positive component at every real source in that same ball equals the actual `hillRegularAbelianCorrection`. All nonpositive complex output components vanish. First gaps, own modes, collapsed gaps and nonzero means are included. There is no high-gap cutoff or output-dependent neighborhood.

The family is the positive projection of the existing literal native terminal, evaluated at the existing logarithmic-moment Dirichlet root and literal complex terminal square root. The proofs establish the moving terminal and its sheet; no new physical correction is defined in place of the existing one.

## Proof components

- `UnitSpectralWeightNorm`: the unit-weight coefficient map preserves norm, allowing an actual real source metric neighborhood to give the required coefficient-norm ball.
- `HillLocalDirichletChart`: fixed-gap compact boundary stability gives the actual Dirichlet characteristic zero count one, a unique simple root and source analyticity of the existing literal logarithmic-moment root.
- `HillAllDirichletCharts`: a finite head plus a uniform tail gives one complex source ball before every positive Dirichlet root and localized periodic pair.
- `HillAllDirichletTerminals`: on one source ball all literal moving roots and terminal square roots are analytic; their distances and norms are bounded by k/16 and k/8 respectively, and the exact terminal square identity holds.
- `HillAllNativeRegularTerminal`: every native filled quadratic solution with full norm C/k yields a native analytic moving terminal with full norm C/8, on one source ball before every positive gap.
- `HillLocalRegularTerminalData`: at each fixed gap, actual physical symmetric data, moving Dirichlet energy and deflated root match the literal complex data on a sufficiently small energy ball. This avoids assuming a radius-k physical root chart for low gaps.
- `HillAllRegularTerminalData`: the physical data packet holds on one real coefficient-norm ball before all positive gaps, by the finite-head and uniform-tail argument.
- `HillRegularTerminalPhysicalComparison`: coordinate evaluation of the actual native quadratic equation and the proved physical cosine comparison identify every positive output terminal with the actual regular correction, including the own mode.
- `AllRegularCorrections`: applies these constructions to the previously proved all-gap physical normalized numerator and filled solutions, yielding the actual all-gap native correction family. Its coarse full norm bound is 9*pi*C/4.

## Scope and remaining obligations

This completes moving Dirichlet evaluation and physical regular correction identification for the finite head as well as the uniform tail. It provides a uniformly bounded analytic family; it does not establish decay or summability over the gap index. The C/k solution bound times a coarse terminal factor of order k only gives a constant bound.

Next are genuine complex spectral/divisor/amplitude sequence estimates and phase control, followed by actual physical Abelian coordinates in weighted half-shift Hilbert norm. Possible routes require proving unscaled terminal ell2 bounds for an absolute Bochner sum, or scaled terminal ell2 bounds plus reciprocal off-diagonal estimates for a native bounded phase sequence. Neither route is asserted here. Real pointwise sequence bounds do not supply the missing complex estimates.

The full s >= -1 scale, arbitrary-base and global neighborhoods, canonicality and global Birkhoff inverse, Hamiltonian action frequencies, rough-W/sharp/infinite-gap results and PDE-flow conclusions remain essential. All eleven main theorem inventory rows remain OPEN.

## Validation

Prior strict evidence for all 1188 unchanged selected baseline sources; strict dependency-order compilation of nine new proof modules; then a fresh combined transitive axiom audit of all 1197 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1229 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1197-module rebuild is claimed.

Fresh audit: 10713 selected and 32844 imported NLS declarations. Nine new proof modules, 14 explicit theorems including private helpers and 1 definition. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
