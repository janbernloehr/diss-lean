# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–20, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

## Theorem 1.1: printed height through four; higher exponents remain open

For every finite p > 1 the source requires one neighborhood and one positive
cutoff, with two eigenvalues in each distant quarter-pi disk, count 4N+2 in
the central box, the stated periodic/antiperiodic parity counts, no other
eigenvalues, and real spectrum for real-type potentials. The central box has
height `(1+8‖φ‖ₚ)^p`.

The following are verified ingredients:

- `exists_uniform_periodicCountingData` (declaration namespace
  `NLS.ZakharovShabat`, file `NLS/ZakharovShabat/PeriodicCounting.lean`) supplies
  one open convex neighborhood and every larger cutoff, with full algebraic
  multiplicities, disk and central parity, and spectral exhaustion. Its box
  initially has height N. The period-one source embedding supplies the even
  Fourier-support condition required by the parity conclusions.
- `periodicSpectrum_im_eq_zero_of_realType` in
  `NLS/ZakharovShabat/RealType.lean` supplies reality for every finite exponent.
- `exists_source_periodicCounting_printed_height_up_to_four` in
  `NLS/ZakharovShabat/SourcePrintedHeightFourCounting.lean` transfers the counts to
  each source's own printed-height box for **1 ≤ p ≤ 4**, on one open convex
  source neighborhood. It retains spectral exhaustion and identifies the
  actual moving rectangular integral with the central projection. Those
  integrals depend analytically on the source.

The initial numerical input is `printed_height_neumann_bound` in
`NLS/ZakharovShabat/PrintedHeight.lean`, proving
`(4p/B + B^(-p)) M < 1` for B=1+8M throughout 1<=p<=2.
Above two that coarse test can fail, but the sharper reciprocal estimate
retains the conjugate-root coefficient 2*(2/(q-1))^(1/q). The power-sum
inequality 2/(q-1)<=4^q holds through p=4. This gives
`freeL1Bound_le_height_eight`, and
`mem_resolventSet_of_printed_height_up_to_four` proves the unchanged
horizontal edges and exterior region. `abs_im_lt_printed_height_up_to_four`
places every spectral point strictly inside the printed height.

The counting proof is factored through
`exists_source_periodicCounting_printed_height_of_resolvent`, keeping the
old p<=2 API available. The new p<=4 source theorem retains a common open
convex neighborhood, every larger cutoff, both parity clauses, the full
central and disk multiplicities, exhaustion, and actual analytic moving
rectangular projections. Public examples check p=3 and p=4, including
729i at p=3 with norm bound one, where the coarse test exceeds one.

Above four the literal height remains a required open obligation. The
new constant-four power-sum test already fails at p=5, which only rules out
that use of this envelope estimate. No spectral counterexample is claimed.
The all-exponent height `(1+8pM)^p` remains available but is not accepted as
completion of the printed requirement. Neither improved finite-range
estimates nor green tests establish the full theorem for every finite p.


`FreeResolventHeightNecessity.lean` now gives an obstruction at the level
of the actual free operator norm, beyond the failure of the power-sum
test. For positive integer P and z=-i2^P it proves
`P/48 <= ||R_0(z)||_(lP -> l1) <= 2P+2^(-P)`. A finite input has norm at
most 96/P and an output coefficient sum of exactly -2. Any coefficient
C_P in `||R_0(z)|| <= C_P/|Im z|^(1/P)+1/|Im z|` must satisfy
`P <= 24 C_P+48`. There is no coefficient uniform in P; constant eight
fails for every integer P>240, with a checked example at P=256.

This is a proof-route obstruction, not a new source counterexample.
`negativeDyadicHeight_mem_free_resolvent` proves that these parameters
belong to the actual free periodic resolvent set at every finite exponent.
Theorem 1.1 above four remains required and unresolved. A proof of the
printed height must go beyond a uniform free lp-to-l1 norm estimate.


`ComponentProductResolvent.lean` now uses the off-diagonal structure in
the square: `||(Phi R_0)^2|| <= B(z)^2 ||phi_1|| ||phi_2||`. Thus the
actual resolvent contains both edges and the exterior of
`(1+8p sqrt(||phi_1|| ||phi_2||))^p` for every finite p. Period doubling
preserves this product. The original printed source height follows under
the additional hypothesis
`p sqrt(||phi.fst|| ||phi.snd||) <= ||phi||_p`, for example whenever
`p^2 ||phi.snd|| <= ||phi.fst||`.

The source norm is still the p-th root of the combined component
p-energies. It is not replaced by a sum of component norms. The new
all-p result has an extra hypothesis; the unrestricted printed height
above four remains unresolved. The supplementary geometric-mean height
is not adopted as a replacement for the source formula. At fixed z off
the free lattice, the product criterion gives an open potential region
containing every triangular potential, with an analytic actual resolvent.
The checked p=256 examples include two nonzero components and a successful
product test at z=i where the previous Neumann condition fails.

## Theorem 1.2: proved in the full printed range

The source statement on p. 19 requires the globally lexicographically
ordered endpoints, counted with algebraic multiplicity, to have lp
frequency displacements for every finite p>1, with a locally uniform
bound for the sum of both p-th powers over all integer indices.

`NLS/ZakharovShabat/SourcePeriodicOverview.lean` provides the source-facing
entry points:

- `sourcePeriodicEndpointEnergy_sum` proves the literal series is summable
  and equals the two full displacement norm powers. Neither a tail-only
  estimate nor Lean's default value for a nonsummable series is used.
- `sourceTheorem1_2` gives one positive constant on one open convex
  neighborhood in `CoeffPair p`, with its original finite-p component-sum
  norm. Every potential in that neighborhood satisfies the full series
  bound. No uniform global bound over all potentials is claimed.
- `sourceTheorem1_2_ordered_labels` retains `PeriodicEndpointLabeling` and
  both global lexicographic inequalities. Its `central.roots` and
  `central.count_eq` preserve all central repetitions and original
  algebraic multiplicities. Its `distant` field preserves both endpoints
  and their multiplicities in each distant disk. Its `exhaustive` theorem
  identifies all and only the original periodic eigenvalues.
- `PeriodicEndpointLabeling.eq_canonicalPeriodicEndpoints` makes these
  ordered sequences independent of the admissible cutoff and initial
  enumeration. Both displacement sequences belong to actual `Coeff p`.

The common bounds follow from
`exists_uniform_bounded_canonicalPeriodicDisplacements`, pulled back along
the continuous linear period-one source embedding. That construction uses
height-N counting boxes and finite central bounds. It does not require
Theorem 1.1's unresolved printed-height estimate above four. The public
checks include the literal series for general p and the instance p=5,
original central multiplicities, and coincident free endpoints with zero
energy. The full printed range 1<p<infinity is covered, unchanged.

## Corollary 1.3: proved in the full printed range

`sourceCorollary1_3_mem` proves membership of the literal midpoint
frequency displacement and unsquared gap in lp, using the same canonical
ordered endpoints. The identities
`sourcePeriodicMidpointDisplacement_apply` and
`sourcePeriodicGapDisplacement_apply` identify the sequence-space values
with `(lambda_n^-+lambda_n^+)/2-n*pi` and `lambda_n^+-lambda_n^-`.

`sourceCorollary1_3` gives both a common local positive norm bound and,
for any positive epsilon, one open source neighborhood and one cutoff
such that both lp tails are at most epsilon at every larger cutoff.
The neighborhood and cutoff may depend on epsilon, as in the existing
locally uniform tail statements. All finite p>1 and every complex source
potential are covered. No continuity or analyticity of the individually
lexicographically sorted endpoints is inferred from these bounds.

## Theorem 1.4: proved at p=2; all-p printed height refuted

The source statement on p. 20 concerns both ordinary boundary spectra,
using the original period-one source norm. Section 4, p. 32, defines them
as the restrictions of the operator with the same Dirichlet-reflected
potential to its Dirichlet and Neumann spaces. This is implemented by
`periodOneBoundaryPotential hp hp1` and `BoundaryCondition.spectrum`;
the Neumann problem does not use a second potential extension here.

The source-facing results in `SourceBoundaryOverview.lean` cover:

- `sourceBoundarySpectrum_closed_discrete`: both actual spectra are
  closed and discrete for every finite p>1. The existing
  `finite_spectrum_inter_of_isBounded` additionally gives finiteness in
  every bounded region.
- `exists_uniform_sourceBoundaryLabels`: one open convex neighborhood in
  the original `CoeffPair p` norm, one cutoff, both conditions, and all
  larger cutoffs. `BoundaryCountingData` gives high-disk multiplicity one,
  the central count 2N+1, and exhaustion in the height-N box.
  `disk_unique_simple` identifies the unique high-disk eigenvalue and
  its actual algebraic multiplicity one.
- `sourceBoundarySpectrum_im_eq_zero`: every spectral point is real at
  every real-type source, including all central and repeated eigenvalues.

The height-N box does not establish the printed box. The new
`SourceBoundaryPrintedHeight.lean` proves the missing transfer precisely:

- `BoundaryCondition.heightSpectrum` is the actual finite boundary
  spectrum intersected with `heightSpectralBox N H`, with the source's
  strict horizontal and nonstrict vertical inequalities.
- `heightSpectrum_eq_central` and
  `exists_source_boundaryCounting_printed_height_of_bound` preserve both
  central counts and exhaustion on a single source neighborhood whenever
  the original source-norm strip bound is available.
- `norm_periodOneBoundaryPotential_two_le` proves contractivity of the
  completed interval extension at p=2, in the original source norm.
  `sourceBoundarySpectrum_abs_im_lt_printed_height_two` then gives the
  unchanged (1+8||phi||_2)^2 strip, with both edges excluded from the spectrum.
- `sourceTheorem1_4_two` gives both printed-box counts 2N+1 and exhaustion,
  plus all `BoundaryCountingData`, on one open convex source neighborhood
  and for every larger cutoff. Together with the first group of results,
  this covers every clause of Theorem 1.4 at p=2.

The all-p printed height is refuted by the finite Fourier construction in
`SourceBoundaryHeightCounterexample.lean`. For every natural P>=1024,
`sourceBoundaryPrintedHeight_counterexample` produces an actual source
Dirichlet eigenvalue at i*2^P outside the printed box and all high disks,
for every cutoff. The source is `(u,0)` with opposite real coefficients on
the bands 2^P<=|n|<2^(2P), normalized by the positive kernel mass. Its
original source norm is at most 96/P<=3/32, so the printed height is at
most (7/4)^P<2^P. The finite equation is connected to the classical
fundamental solution and then to `BoundaryCondition.spectrum`; this is
not a counterexample to a mere numerical criterion.

`not_sourceTheorem1_4_printed_exhaustion` explicitly negates the weaker
pointwise all-source assertion at p=1024, hence also the printed
neighborhood conclusion. No replacement height is adopted. The Hilbert
result above and all finite-p height-N counting results remain valid.
Theorem 1.1's periodic height is a separate question, still open above
four. See `SOURCE_ERRATA.md` for the complete construction and source
comparison.

A proposed all-p replacement is now proved in
`SourceBoundaryExplicitHeight.lean`: height `(1+8*p*E_p*||phi||_p)^p`,
with E_p the proved interval-extension bound. The source norm remains
unchanged. `sourceTheorem1_4_proposed_height` gives the same two central
counts, simple high roots, and exhaustion on one open convex neighborhood,
for every larger cutoff. Closedness, discreteness, and real-type reality
continue to use the existing all-p source theorems. This proposed correction
is separate from the printed statement and is not adopted in its place.

`SourceBoundaryHeightNecessity.lean` proves that a coefficient C_p in this
shape of height must satisfy C_P>=P/96 at every integer P>1. This remains
necessary with arbitrary source-dependent cutoffs and all high disks.
Thus increasing eight to any fixed nonnegative constant cannot repair
the all-p statement. The lower bound is not claimed optimal.

## Theorem 1.5: proved in the full printed range

The source statement on p. 21 requires both globally lexicographically
ordered ordinary boundary sequences to have lp frequency displacements,
locally uniformly in every complex source, for every finite p>1.

`sourceTheorem1_5_mem` proves membership of each literal sequence
`canonicalPeriodOneBoundaryRoots ... b phi n - n*pi`. `sourceTheorem1_5`
proves summability of its p-power energy and one positive full-series
bound, simultaneously for both boundary conditions, on a common open
convex source neighborhood containing the base source and zero. This
bounds the actual full lp norms and includes every central index.

The canonical roots exhaust the original boundary spectrum by
`canonicalPeriodOneBoundaryRoots_exhaustive`, and repetitions have exactly
the original algebraic multiplicity by
`canonicalPeriodOneBoundaryRoots_multiplicity`. Their global ordering is
`monotone_canonicalPeriodOneBoundaryRoots`; uniqueness of complete ordered
labelings makes them independent of the cutoff and initial enumeration.
The public checks cover the literal sequences for general p, the shared
series bound at p=5, and global ordering.

No real-type assumption or smallness restriction is used. The source
neighborhood is the continuous linear pullback of the reflected-potential
neighborhood; no norm equality is needed for this qualitative local bound.
Theorem 1.5 is therefore covered for every finite p>1 independently of
Theorem 1.4's false all-p printed-height assertion. No continuity or
analyticity of individually sorted roots at arbitrary complex potentials
is claimed by these locally uniform bounds.

## Corollary 1.6: proved in the full printed range

The statement on p. 21 requires real finite-gap potentials to be dense in
the real source space for every finite p>1. The existing
`NLS/ZakharovShabat/SourceFiniteGapDensity.lean` proves exactly this:

- `sourceFiniteGapLocus`, defined in `SourceFiniteGap.lean`, means that
  only finitely many actual canonical periodic gaps are nonzero. Its
  ambient space is `realTypeSourceLocus p`, with the inherited original
  source norm. It is not a finite Fourier-support definition.
- `exists_real_sourceClosingApproximation` constructs a real source
  arbitrarily close to any real source and closes its original periodic
  spectrum in every sufficiently distant strip. Both spectral closing
  equations vanish there and the determinant order is exactly two.
- `finite_canonicalPeriodicGap_of_singleton_strips` uses the actual
  canonical endpoints and their spectral membership to conclude that
  every sufficiently distant gap vanishes. Thus the approximants satisfy
  the stated spectral definition, not only a target-coordinate condition.
- `exists_mem_sourceFiniteGapLocus_norm_sub_lt` supplies these approximants
  at every positive tolerance in the original norm, and
  `dense_sourceFiniteGapLocus` states the resulting density for all finite
  p>1. Existing public examples check actual spectral finite-gap
  approximation at p=3 and density at p=2 and p=3/2.

This completes the numbered density statement without an additional
assumption of density in a smoother space. The preceding unnumbered
regularity sentence needs a scope qualification. Its unrestricted complex
reading is refuted by `ComplexFiniteGapRegularityCounterexample.lean`:
`roughTriangularSource` has coefficients `(1/(1+|n|),0)`, free actual
periodic spectrum, and finitely many nonzero canonical gaps, but no smooth
periodic representative preserving its Fourier coefficients. A fortiori
it has no spatially real-analytic periodic representative. This holds at
every finite p>1. The triangular inverse is explicit and two-sided on
the original domain; the finite-gap property uses actual canonical gaps.

The counterexample is not of real type. Real-type finite-gap smoothness
and density remain valid, and spatial real analyticity is now proved by
`analyticOnNhd_sourceFiniteGapPhysicalPair`. The theorem applies to the
existing coefficient-preserving representative at every finite p>1.
`sourceFiniteGap_exists_analytic_representative` packages analyticity,
period one, and every original Fourier coefficient. The proof composes
the analytic finite-dimensional spectral reconstruction with finite
translation targets and bounded Sobolev evaluation. It uses translation
invariance of the exact canonical gap tail and makes no finite Fourier
support assumption. Thus the real-type qualification is both sufficient
for the proved regularity result and essential to the source sentence's
unrestricted complex interpretation.

The numbered overview audit leaves Theorem 1.1's printed height above
four unresolved and records Theorem 1.4's all-p printed height as refuted.
The latter still holds at p=2; no replacement height is adopted. This
audit does not certify the remaining chapters or unnumbered source claims.
The dissertation remains incomplete.
