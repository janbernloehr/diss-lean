# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–20, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

## Theorem 1.1: printed height proved through four; all-exponent assertion refuted

Source: dissertation, printed p. 17 (statement), especially clauses (ii)
and (iii), and p. 27 (proof). The central box uses the original source
height `(1+8||phi||_p)^p`, and this box together with the quarter-pi disks
must contain every periodic eigenvalue.

`SourcePeriodicHeightCounterexample.lean` now proves a counterexample
for every integer P>=100000000. The theorem
`sourcePeriodicPrintedHeight_counterexample` supplies a single original
source psi with equal component norms and `||psi||<=1/16`, an actual
periodic spectral point `z=i*2^P`, and nonmembership in the union of the
printed-height box and high disks for **every** cutoff N. Thus no
neighborhood/cutoff pair can satisfy the printed exhaustion at this
source. `not_sourceTheorem1_1_printed_exhaustion` explicitly negates the
all-source exhaustion assertion at the concrete finite exponent 100000000.
This is an operator-spectrum counterexample, not merely failure of a
sufficient resolvent estimate. The threshold is sufficient, not optimized.
The behavior of each individual exponent between four and this threshold
is not determined by this result.

The construction and its proved constants are:

1. At J=2P, the upper real profile U is the sum, for j=2,...,J, of
   `(4*4^j)` times the tent on `[2^(-j),2^(1-j)]` minus its reflection
   across 1/2. `DyadicTentSum.lean` proves that its original lP coefficient
   norm is at most 640 and its weighted interaction
   `A=integral_0^1 U(x) exp(-2H*x) dx` at H=2^P is at least (P-2)/4.
2. `LowerDyadicTent.lean` puts a tent V of area one on `[1-epsilon,1]`,
   epsilon=2^(-2P). Its original mean is one. Uniform and quadratic-tail
   Fourier bounds, after removing the mean, give an lP coefficient norm
   at most nine. Its interaction
   `B=integral_0^1 V(x) exp(2H*x) dx` is at least
   `exp(2H(1-epsilon))`.
3. `OrderedDyadicSource.lean` proves coefficient/physical compatibility,
   ordered support, and positivity of A and B. The complex interaction
   primitives are iA and -iB. The exact monodromy normalization multiplies
   U by `kappa=-(exp(H)-1)^2/(A*B)`, placing iH in the actual periodic
   spectrum at every finite target exponent p>=2.
4. `DyadicNormalizationBound.lean` proves
   `abs(kappa)<=12/(P-2)`. Indeed the numerator is at most exp(2H),
   the lower interaction cancels that exponential up to
   `exp(2H*epsilon)<=exp(1)<3`, and A>=(P-2)/4.
5. Diagonal similarity balances the component norms while preserving
   the actual spectral point. The original pair norm is exactly
   `2^(1/P) sqrt(abs(kappa)*norm(U_hat)*norm(V_hat))`, hence at most
   `2 sqrt(69120/(P-2))`. For P>=100000000 this is at most 1/16.
   The unchanged printed height is therefore at most `(3/2)^P<2^P`.
   The imaginary part also exceeds pi/4, excluding every disk centered
   on the real free lattice, independently of N.

The original finite-exponent pair norm is the P-th root of the combined
component coefficient energies from equation (1.2). The construction does
not replace it by a maximum norm or a physical-space norm. It uses genuine
continuous piecewise linear profiles and their original Fourier integrals;
no numerical truncation or Galerkin spectral assertion is involved.
The proof uses the existing actual monodromy/discriminant correspondence,
exponent compatibility, and domain-preserving diagonal similarity.

The verified positive results remain valid. `PrintedHeight.lean` gives
the printed height through p=2; `RefinedReciprocalNorm.lean` and
`PrintedHeightFour.lean` extend it through p=4.
`exists_source_periodicCounting_printed_height_up_to_four` in
`SourcePrintedHeightFourCounting.lean` retains the common open convex
source neighborhood, all larger cutoffs, central and distant algebraic
multiplicities, periodic/antiperiodic parity, spectral exhaustion, and
actual analytic moving rectangular projections for 1<=p<=4.
`periodicSpectrum_im_eq_zero_of_realType` retains spectral reality at all
finite exponents. The counterexample sources cannot be of real type.
Equal component norms alone do not imply real type.

At every finite exponent the height-N counting theorem
`exists_uniform_periodicCountingData` still gives one common neighborhood,
all sufficiently large cutoffs, full multiplicities and parity, and
exhaustion. Thus this erratum concerns the specified quantitative height,
not spectral discreteness or the existence of a central counting box.
The known sufficient height `(1+8pM)^p` and the component-product height
`(1+8p sqrt(norm(phi_1)*norm(phi_2)))^p` are separate proved alternatives.
No correction is adopted here.

Earlier estimates remain useful but are logically weaker evidence:
`reciprocal_power_coefficient_four_fails_at_five` refutes a sufficient
power-sum test, and `FreeResolventHeightNecessity.lean` rules out a
uniform free lp-to-l1 resolvent coefficient. Neither alone was a spectral
counterexample. The actual dyadic source above resolves the all-exponent
printed-height obligation negatively.

The necessary exponent dependence is now quantified in
`SourcePeriodicHeightNecessity.lean`. For every integer P>=3, any
nonnegative C_P giving the original-source strip bound
`abs(Im z)<=(1+C_P*norm(psi))^P` for all source spectra must satisfy
`P-2<=276480*C_P^2`. The same conclusion holds if only exhaustion by
a source-dependent central box and the high disks is required.
`sourcePeriodicHeightCoefficient_necessary` and
`sourcePeriodicCountingHeightCoefficient_necessary` prove these two
statements. The corresponding `not_exists_uniform_sourcePeriodic...`
theorems exclude every fixed nonnegative coefficient for all integer
exponents. These bounds follow from the actual balanced dyadic family;
they are not free-resolvent norm obstructions.

`SourcePeriodicExplicitHeight.lean` proves the separate proposed
correction `(1+8pM)^p` in the original source norm, for all finite p>=1.
`mem_resolventSet_of_sourcePeriodicExplicitHeight` includes both horizontal
edges and the entire closed exterior strip.
`sourcePeriodicSpectrum_abs_im_lt_explicit_height` gives strict exclusion
for spectral points. `sourceTheorem1_1_proposed_height` retains one open
convex source neighborhood, every larger cutoff, full central and distant
counting data and parity, central multiplicity 4N+2, exhaustion, equality
with the central cluster projection, and analyticity of the actual moving
rectangular integral. It specializes a general source counting transfer
for any nonnegative coefficient with a proved resolvent bound; the
existing printed-height API remains the coefficient-eight specialization.
No replacement has been adopted. The necessary square-root growth and
sufficient linear growth do not establish an optimal growth rate.

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
Theorem 1.1's now-refuted all-exponent printed-height estimate. The public
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

The numbered overview audit retains Theorem 1.1's printed height through
four and records both Theorem 1.1's and Theorem 1.4's all-p printed heights
as refuted.
The latter still holds at p=2; no replacement height is adopted. This
audit does not certify the remaining chapters or unnumbered source claims.
The dissertation remains incomplete.
