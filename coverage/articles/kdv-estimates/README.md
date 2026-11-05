# KdV estimates: main theorem coverage

The named main Theorems 1–3 of Jan-Cornelius Molnar, *On Two-Sided Estimates
for the Nonlinear Fourier Transform of KdV*, are proved locally. The exact
source is the explicitly versioned arXiv:1502.04550v1 PDF, SHA-256
`b275b8c6770a650f614acd0788611044c6b0ee8da4506857294dc3ae617666dd`.
The served PDF displays September 4, 2018 despite the 2015 submission date;
no identification with a different historical download or journal version is
assumed. See `source-map.json` for source pages, conventions and proof history.

| Source statement | Lean declaration in `NLS.Articles.KdVEstimates` |
| --- | --- |
| Theorem 1, both Sobolev estimates | `theorem1` |
| Theorem 2, both action estimates | `theorem2` |
| Theorem 3, weighted target membership and both estimates with one constant | `theorem3` (membership also in the typed restriction) |

All three are in `NLS/Articles/KdVEstimates/MainBirkhoffEstimates.lean`.
The constants precede the potential quantifier, with the same dependence as
in the source. Theorem 1 and Theorem 2 apply to every integer `m ≥ 1` and
every real, mean-zero period-one potential in the indicated Sobolev space.
Theorem 3 applies to every `0 ≤ r ≤ 1/2`, every normalized, symmetric,
monotone, submultiplicative weight `v`, and `w = ⟨k⟩^r v`.
`SpectralWeight.realExtension` is the source's piecewise linear extension.

## The fixed map and its norms

`hillOriginalBirkhoffMap` uses the original full physical spectral
construction, with raw pairs `(Re Z_n, -Im Z_n)`. Its normalized complex
sequence is `sqrt(2πn) * (x_n - i*y_n)`. Physical coordinate equality is
proved in `hillOriginalBirkhoffMap_coordinates`; every weighted and Sobolev
restriction keeps these exact raw pairs of this one map.
The original actions, physical Dirichlet sheets, and full regular phase
are retained. Canonicality alone is not used as a uniqueness criterion for
identifying a Birkhoff map.

`hillOriginalBirkhoffHomeomorph`, its actual two-sided inverse, and real
Banach analyticity of both directions are proved for the original real
mean-zero L² source and the explicit real Hilbert target. The original
source norm and topology are preserved. The canonical Gardner matrix is
proved by actual analytic physical coordinate germs at every source,
including all low and collapsed gaps.

The source norm squared is
`Σ_{k∈ℤ} (1+|2πk|)^(2m) |u_hat(k)|²`; the coefficient-preserving lower
Sobolev source is `hillRealNativeIntegerLower`.
The target norms squared are exactly
`Σ_{n≥1} (2πn)^(2m+1) (x_n²+y_n²)` and
`Σ_{n≥1} (2πn) w(2n)² (x_n²+y_n²)`.
`HillBirkhoffSobolevSpace` and `HillBirkhoffWeightedSpace` encode actual
weighted square-summable real pairs with these complete Hilbert topologies.
Lean's natural index `k` represents physical positive index `n=k+1`.

`hillOriginalBirkhoffAction` is `(x_n²+y_n²)/2` and equals the physical gap
integral at every positive index. The original Arnold contour integral is
identified with that integral by `sourceArnoldAction_eq_gapIntegral`.
The integer action masses are proved summable; target membership gives the
weighted action summability. No estimate is obtained by assigning a total
sum to a divergent sequence.

## Validation and limits

The validation record covers 1,486 focused source modules: an unchanged
strictly validated 1,475-module base and 11 new isolated strict compilations.
The base provenance is a full 583-module focused run plus 892 isolated
additions. The complete current aggregate import and expanded transitive
axiom audit are checked separately. The only allowed axioms are
`propext`, `Classical.choice`, and `Quot.sound`.
The three final declarations also pass explicit integrated theorem and
axiom checks. No fresh complete 1,486-module focused-script run, full Lake
rebuild, or full repository examples run is claimed.

This coverage concerns the named main Theorems 1–3. The two statements
labelled Corollary 1 in the source are outside this completion claim.
Global surjectivity on every higher weighted space is not asserted.
The Hill operator is `-d²/dx² + q`; the missing exponent in the page-8
display is corrected consistently with formula (2) on page 5.

The work is on the separate `articles/kdv-estimates` worktree. Publication
is pending the earlier automatic approval review's GitHub destination
approval; no successful push or merge is claimed.
