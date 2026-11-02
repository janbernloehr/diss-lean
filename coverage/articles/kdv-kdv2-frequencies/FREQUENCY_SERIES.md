# Infinite frequency-series dependencies

The fixed-mode summation steps used in source Theorems 3.4 (p. 31) and
4.3 (pp. 42–43) are proved with explicit spectral-estimate inputs.
**No actual article main theorem is verified by this milestone.**

## Theorems and exact scope

`NLS/SequenceSpaces/LocallyBoundedAnalyticSummation.lean` proves
`NLS.Coeff.analytic_tsum_of_local_one_bounds`. On any open subset of a
complex normed parameter space, analytic scalar summands with locally
bounded actual ℓ¹ norms have an absolutely convergent analytic sum.
The symmetric finite partial sums converge locally uniformly. A common
pointwise summable majorant is not assumed: the existing Banach analytic
realization theorem constructs the analytic ℓ¹ map, and the existing Dini
argument gives the local uniform convergence.

`NLS/KdV/FrequencySeriesBounds.lean` proves:

- `quadratic_frequency_kernel_le`: for positive integer n,k with k≠n,
  both n²/|n²−k²| and nk/|n²−k²| are at most n/|n−k|.
- `hilbert_frequency_kernel_le`: n²k²/|n²−k²| is at most n²(1+n²).
  This explicit fixed-n constant makes the implicit ℓ¹ bound in the
  source's Hilbert-space argument precise; no uniform-in-n asymptotic
  claim follows from this coarse constant.
- `exists_one_coefficients_of_reciprocal_bound`: an ℓᵖ remainder,
  1<p<∞, with reciprocal-distance factor and separately bounded diagonal
  gives an actual ℓ¹ row and an explicit Hölder norm bound. It uses the
  dissertation's punctured reciprocal lattice and norm-preserving reindexing.
- `analytic_tsum_of_local_reciprocal_bounds` and
  `analytic_tsum_of_local_bounded_kernel_bounds`: local bounds for the
  remainder sequences yield absolute summability, analyticity and local
  uniform convergence. The remainder sequences need not themselves be
  continuous or analytically chosen.

`NLS/KdV/FrequencySeries.lean` proves the positive-index versions:

- `tsum_eq_positive_of_nonpositive_zero` and `sum_symmetric_eq_positive`
  rigorously identify the integer zero extension with the positive Hill
  index series and its positive partial sums, also at truncation N=0.
- `analytic_positive_series_of_quadratic_bounds` applies the two exact
  quadratic-denominator estimates to locally bounded ℓᵖ remainders,
  1<p<∞, keeping the diagonal independent.
- `analytic_positive_series_of_hilbert_bounds` applies the polynomial
  kernel bound to locally bounded ℓ¹ remainders.

Both conclusions are absolute summability, Banach analyticity of the
positive-index scalar sum, and locally uniform convergence of the positive
partial sums. Indices are the literal positive integers, rather than an
arbitrary enumeration that would lose the denominator geometry.

## Source correspondence and remaining obligations

For Theorem 3.4 the summands are k Ω²_nk; the off-diagonal estimate uses
n²/(n²−k²) times an ℓ¹ remainder. The existing exponent inclusion ℓ¹→ℓ²
permits the reciprocal theorem to be applied. For Theorem 4.3 the Hilbert
case uses n²k²/|n²−k²| times an ℓ¹ remainder. The non-Hilbert quadratic
sum and the quartic sum use nk/(n²−k²) and Hölder. Remainders of exponent
p/4 can be included into a finite exponent above one; deriving these
remainders and their local bounds from the actual spectral functions
remains open. The exact frequency multipliers remain −12 for KdV and
−160π², +80 for KdV2, as in the proved finite-gap contour formulas.

The new results discharge the summation implication, not its spectral
hypotheses. Construction and normalization of actual Hill moments, their
sharp locally uniform remainder estimates, finite-gap/physical frequency
identification, action descent, and output-sequence asymptotics and compact
derivatives remain necessary for Theorems 1.2 and 1.9.

## Shared developments and validation

The locally inspected Hill line reaches `1806362e18c4924a0e58e902455a42d8dc8c90d3`.
The action line reaches `2135a680ab46ba7c476060e9a66db7d5753f8b29`, which constructs
the actual continuous-potential Hill discriminant and local primitive
charts. These new commits were inspected, not imported by this milestone;
rough-potential spectral identification, global gap normalization and
normalized psi functions are not supplied by those local charts alone.
No competing Hill or action-Hamiltonian construction was added.

All fifteen selected modules compile with pinned Lean 4.33.1/mathlib
v4.33.1, `-DautoImplicit=false -DwarningAsError=true`, and default heartbeats.
The transitive axiom audit passes for 244 selected declarations and 1658
declarations including imported NLS dependencies, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Reproduce with
`bash scripts/check-kdv-kdv2-frequencies.sh`.
