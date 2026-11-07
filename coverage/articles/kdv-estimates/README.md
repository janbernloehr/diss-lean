# KdV estimates: whole-paper coverage in progress

The requested scope is now the entire pinned paper. **Whole-paper verification
is not complete.** The [coverage ledger](whole-paper.json) inventories all 27
named results, distinguishes the two occurrences of Corollary 1, and keeps the
numbered equations and a page-by-page audit of unnumbered claims open. Existing
main-theorem verification remains valid; a library module alone is not evidence
that every source hypothesis, constant and uniformity assertion matches.

Lemma 7 now has an explicit article theorem with the half-kinetic normalization,
exact homogeneous grading and zero constant coefficient. Equation (14)'s exact
monomial constraint is also proved. Both pass strict Lean checks.

Two source qualifications are recorded with formal proofs:

- Lemma D.1 needs a nonempty real slice, as used in its printed proof. The
  corrected identity theorem is proved; the constant function one on the ball
  of radius one half about i proves the hypothesis cannot be omitted.
- Lemma A.3 uses radius-twelve strips in print. At n=1 the strip contains zero,
  where the retained constant mode prevents a complementary inverse. The
  corrected radius-six statement is proved with the exact constant two in every
  shifted norm. It gives a genuine two-sided Neumann inverse at cutoff
  `n >= 4*norm(q)`. This does not certify the literal radius-twelve statement or
  the downstream Appendix A localization constants.

The real-exponent Corollary 1 (second occurrence, pages 4-5) is now proved
for every real `s >= 0`. Both parts use one constant, the exact Fourier source
norm, the exact complete homogeneous target with powers `2*s+1`, and the same
original physical coordinate pairs. The action sum is proved convergent.

The dynamical Corollary 1 (first occurrence, page 3) is now proved for
actual classical physical KdV trajectories and for the declared solution
concept of locally uniform physical-L2 limits of classical trajectories.
The equation is `q_t = 6*q*q_x - q_xxx`; ordinary smooth pointwise solutions
are connected to that Fourier equation by a proved adapter. An explicit
periodic local flux proves that the actual Hill discriminant is stationary
at every energy, hence every original physical action is conserved. The
mean is also proved conserved, so only initial mean zero is required.
The corollary has the exact exponent `m*m+m-1` and no supplied action- or
target-norm-conservation premise. Original Sobolev-norm approximation is
proved sufficient for the physical-L2 approximation used here.

This solution concept is explicit in `IsKdVSolutionByClassicalApproximation`.
The corollary trajectory is typed in the stated Sobolev space throughout.
Existence/uniqueness and regularity persistence for every Sobolev datum, and
equivalence with arbitrary distributional solution formulations, are separate
background obligations;
they are not asserted by this milestone. This is a scope qualification,
not an additional source correction. The A.3 and D.1 corrections above remain
unchanged.

The exact leading coefficients in Lemma 8 and Theorem 4, the remaining named
results and unnumbered claims still need source comparison and missing proofs.
Historical validation below concerns the main-theorem milestone. New proof validation is in
[conservation-validation.json](conservation-validation.json). The earlier
real-exponent and conditional dynamical milestone is recorded in
[corollary-validation.json](corollary-validation.json). The initial auxiliary
proof milestone remains recorded in [whole-paper-validation.json](whole-paper-validation.json).

## Verified main-theorem milestone

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
axiom checks. That original theorem milestone did not include a fresh complete
1,486-module focused-script run, full Lake rebuild, or repository examples run.
The later integration checks are recorded below.

That milestone concerns the named main Theorems 1–3. Both statements labelled
Corollary 1 were outside it. Their current statuses are described above: the
real-exponent statement is verified and the dynamical statement is verified
for the explicitly declared solution concept.
Global surjectivity on every higher weighted space is not asserted.
The Hill operator is `-d²/dx² + q`; the missing exponent in the page-8
display is corrected consistently with formula (2) on page 5.

The work is published on the separate `articles/kdv-estimates` branch in
[PR #4](https://github.com/janbernloehr/diss-lean/pull/4). PR #4 was merged as
`a1d8eb82cdbf5e39ec17f103f3901e8e24f57dfa`; this whole-paper continuation
is based on that commit, whose tree matches the validated merge resolution.

## Main integration validation

The merge retains the stronger spectral cutoff, combines the article imports,
and keeps frequency and energy discriminant gradients distinct, with the
energy construction under explicit `hillEnergyTraceGradient` names.
The physical normalization relation is checked in Lean.

1925 affected or missing modules passed fresh strict compilation. The combined
aggregate import, final main-theorem checks, KdV audit
(9959 declarations) and global NLS audit (60500 declarations)
passed. See `merge-validation.json` for the exact source hashes and scope.


All 7,729 examples are covered across the complete run and the corrected-command
recheck: the 7,721 unchanged examples passed the full run, and the eight corrected
anonymous commands passed in their original file scopes. Every nonexample command
was preserved and re-elaborated. No fresh all-green monolithic rerun is claimed.
The incoming mKdV/NLS audit also passed for 9768 declarations; its
prefix selection uses the same scope set with a faster ancestor lookup.

The corrected examples can be rechecked with pinned Lean 4.33.1:

```bash
lean -DautoImplicit=false -DwarningAsError=true --run scripts/CheckExamplesSubset.lean scripts/CheckExamples.lean 6634,39060,41187,60632,61159,61164,61174,73723 7729
```
