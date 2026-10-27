# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–21, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

## Original period-one distribution potentials, printed p. 18

[PeriodicFourierLebesguePeriodDoubling](../NLS/Fourier/PeriodicFourierLebesguePeriodDoubling.lean)
constructs the norm-preserving extension from original period-one distributions
to period two. Even Fourier coefficients retain their original amplitudes and
signed indices; odd coefficients vanish. Both realizations induce exactly the
same tempered distribution on every Schwartz test. The full Fourier-series
proof retains the inverse Jacobian, and applies even to nonmeasure inputs.

The scalar range is exactly the distributions still invariant under translation
by one. [NativePeriodOnePotential](../NLS/ZakharovShabat/NativePeriodOnePotential.lean)
lifts this equivalence to potential pairs, preserving the original finite
component-sum norm and both physical distributions. Its coefficients are exactly
the period-one parameter already used by the spectral theory, so the entire
native bounded-inverse spectrum agrees with the source spectrum.

This resolves the period-extension point left separate in the previous operator
comparison. The scalar results include infinity; the source pair-norm and
closed-operator claims retain finite p. Five examples check a negative Fourier
mode, an explicit nonmeasure input, scalar infinity, the closed operator at p=1,
and the source spectral identification at p=3.
Validation passes: 8,417 build jobs, 7,439 public examples and a
transitive axiom audit of 42,615 NLS declarations. The 21 inherited
warnings are unchanged; the new modules and examples introduce none.

The three assertion groups and four complete modules are recorded as
`SpectralOverviewPeriodExtensionSourceComparison-2026-10-27` in the
[source-review index](source-review-index.json). The remaining overview
comparison and existing source qualifications are unchanged.

## The operator on original periodic distributions, printed p. 18

[NativePeriodicOperator](../NLS/ZakharovShabat/NativePeriodicOperator.lean)
constructs the operator directly on pairs of original period-two distributions.
For every finite p>=1, its domain is exactly the full FL^{1,p} space, its
inclusion preserves the distributions, and its norm is the original finite
component-sum norm. Both signed differential expressions are proved as
distribution identities, using the coefficient-convolution product.

The partial operator is densely defined and closed in the base FLp topology.
Its independently defined bounded two-sided inverse into FL^{1,p} identifies
the full resolvent set with the coefficient-space one; the base resolvent is
compact and the spectrum is discrete. No smallness, smoothness or finite-support
condition is imposed on the potential.

[NativePeriodicHilbert](../NLS/ZakharovShabat/NativePeriodicHilbert.lean)
identifies the entire graph with the original physical L2 operator at p=2.
Both physical components represent the same distributions. For original
period-one L2 potentials, the spectrum is the union of the actual classical
periodic and antiperiodic spectra on the unit interval.

Five public examples check unequal free-mode amplitudes and signed indices,
an arbitrary distribution potential on a constant domain input, graph limits
at p=1, a free resolvent at p=3, and the classical signed spectral union.
Validation passes: 8,415 build jobs, 7,434 public examples and a
transitive axiom audit of 42,589 NLS declarations. The 21 inherited
warnings are unchanged; the new modules and examples introduce none.

The comparison records four assertion groups against four complete modules as
`SpectralOverviewNativePeriodicSourceComparison-2026-10-27` in the
[source-review index](source-review-index.json).
The period-one to period-two distribution extension, left separate by this
record, is now compared in the follow-up above. The earlier Theorem1.1
corrections and the precise2014 and G2 qualifications are unchanged.

## Renewed comparison of periodic enumeration, printed p. 17

The opening operator, enumeration, real ordering and eigenfunction-parity
assertions now have a renewed comparison against sixteen complete modules,
recorded as `SpectralOverviewRealPeriodicSourceComparison-2026-10-27` in the
[source-review index](source-review-index.json). It uses the unchanged physical
domain and endpoint interfaces from the complex-potential comparison below.

The actual spectral sets equal the full classical ODE eigenvalue sets.
Endpoint repetitions count the dimension of the entire physical generalized
eigenspace, with the operator domain retained at every link of a root chain.
Global lexicographic ordering and both full l2 displacement sequences remain
part of the endpoint specification. For real potentials, consecutive pairs
are strictly separated, including central indices and collapsed gaps.

Every eigenfunction at either endpoint has its index's exact unit-translation
sign in both physical components. This is an all-index statement for all
finite p>1, including the printed Hilbert case. Even and odd physical pairs
also count the full algebraic multiplicity of the respective classical
signed operators. The printed plus-or-minus boundary shorthand is realized
by two separate linear domains and the union of their spectra.

The whole-line spectrum and absolute-continuity assertion is a separate
comparison. This record does not certify the whole chapter or dissertation.

## Renewed comparison of the whole-line assertion, printed p. 17

The whole-line spectrum and absolute-continuity passage now has a renewed
comparison against thirty-five complete modules, recorded as
`SpectralOverviewWholeLineSourceComparison-2026-10-27` in the
[source-review index](source-review-index.json). It covers every original
real-type L2 potential, with its actual period-one physical extension.

The smooth compact test operator has a self-adjoint graph closure with the
full locally absolutely continuous differential domain. The independently
defined bounded-inverse spectrum equals the real axis minus all original
open periodic gaps. The proof supplies both band inclusion and gap resolvents,
including every endpoint and collapsed gap.

The scalar measures come from the actual closure's Cayley transform and
reproduce the original nonreal resolvent by integration. Physical Green-kernel
bounds give absolute continuity for compact inputs off a countable set of
repeated roots. Absence of atoms removes that exceptional set, and density
extends absolute continuity to every Hilbert vector. Both atomic and singular
continuous spectral mass are excluded. The comparison retains the real L2
hypothesis; it makes no corresponding claim for arbitrary complex or rougher
Fourier-Lebesgue potentials.

The later Fourier-Lebesgue operator-extension discussion remains a separate
source comparison. The precise2014 and G2 qualifications are unchanged.

## Renewed comparison of complex potentials, printed pp. 17–18

The gap definitions and the complex-potential paragraph now have a renewed
comparison against twelve complete Lean modules, recorded as
`SpectralOverviewComplexSourceComparison-2026-10-27` in the
[source-review index](source-review-index.json). The gap is the signed endpoint
difference, and the midpoint is the arithmetic mean; both retain the actual
physical spectral labels and their full l2 asymptotics.

The original physical operator is self-adjoint exactly for real-type
potentials, with the full adjoint domain. The two unit-interval boundary
conditions define separate operators, whose spectra are combined by union.
The potential `(1,-1)` supplies the actual nonreal eigenvalue `i`. Arbitrarily
small potentials `(r,-r)` supply the gap `2ir`, and `(1,i)` supplies a nonreal
midpoint. The nonreal-spectrum assertion is existential; it does not say that
every potential outside the real locus has nonreal eigenvalues.

This comparison reads the source's Floquet qualification as withdrawing the
preceding description by complements of real open intervals. The reviewed complex proofs still use
exact monodromy trace criteria. This comparison makes no assertion about
general complex whole-line bands, the neighboring real enumeration and
absolute-continuity claims, or the entire chapter.

## Theorem 1.1: printed height proved through four; all-exponent assertion refuted

Source: dissertation, printed p. 18 (statement), especially clauses (ii)
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
Theorem 1.1's periodic height has a separate counterexample at large
exponents, as recorded above. Its sharp exponent range above four remains
undetermined. See `SOURCE_ERRATA.md` for the constructions and source
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
The formalization of the dissertation remains incomplete.

## Initial whole-line band criterion (historical checkpoint)

The unnumbered paragraph on printed p.17 identifies the spectrum of the
periodically extended real L2 operator on the real line with the complement
of the open periodic gaps and says that its spectrum is absolutely
continuous. At this initial checkpoint the whole-line operator and
spectral-measure foundations were still outstanding. The later sections
build them and discharge the full assertion in the original source space.

[`SourceFloquetBandSet.lean`](../NLS/ZakharovShabat/SourceFloquetBandSet.lean)
defines the real complement of the union of the actual open canonical
gaps. For every finite p>1 real source, membership is equivalent to
|Re Delta(x)|<=2. Strict gap interiors have |Re Delta(x)|>2; the proof
covers every band endpoint and collapsed gap and proves the set closed.

[`FloquetQuadratic.lean`](../NLS/ZakharovShabat/FloquetQuadratic.lean)
proves the exact algebraic criterion: a real-trace two-by-two matrix of
determinant one has a characteristic root of modulus one if and only if
its trace lies in [-2,2].

[`L2FloquetBandCriterion.lean`](../NLS/ZakharovShabat/L2FloquetBandCriterion.lean)
transfers this criterion to the actual physical L2 monodromy of each
original real Hilbert source. A nonzero eigenvector with a unit multiplier
exists exactly on the closed band set. Its propagation by the constructed
physical fundamental matrix at nonnegative integer times is exactly the
corresponding power of the multiplier times the same initial vector.

At this historical stage, construction of the whole-line operator and
proofs of self-adjointness, the resolvent, spectrum equality and pure
absolute continuity remained outstanding. All are discharged in the
later sections below. The operator spectrum throughout is independently
defined through bounded two-sided inverses.

## Physical propagation through positive and negative periods

The next prerequisite for the printed p.17 whole-line assertion extends
the actual physical L2 fundamental matrix to all real times. It uses the
integer part and fractional part of time, together with integer powers
of the invertible physical monodromy. Negative integer powers use its
actual determinant-one inverse.

[`L2WholeLineFundamental.lean`](../NLS/ZakharovShabat/L2WholeLineFundamental.lean)
proves the exact formula on every closed integer period, continuity at
all seams, the integer-translation identity, the original identity value
at zero, and agreement with the previous nonnegative-time continuation.

[`L2WholeLineFloquetBound.lean`](../NLS/ZakharovShabat/L2WholeLineFloquetBound.lean)
proves exact scalar multiplier propagation for every integer power.
For every unit-modulus monodromy eigenvector, the propagated vector is
uniformly bounded on the full real line. In particular, every real point
of the canonical band set of an original Hilbert source admits a bounded
continuous propagated curve with nonzero initial vector.

[`L2WholeLineSolutionPeriods.lean`](../NLS/ZakharovShabat/L2WholeLineSolutionPeriods.lean)
identifies the propagated physical pair on each closed integer period
with the original L2 initial-value solution, using the transported initial
vector. In the local coordinate of every positive or negative period,
the original signed differential equation holds almost everywhere. No
pointwise regularity of the potential is assumed.

[`L2WholeLineDifferentialEquation.lean`](../NLS/ZakharovShabat/L2WholeLineDifferentialEquation.lean)
defines the actual period-one physical representative via fractional part.
Translation invariance and removal of the countable integer seams combine
the period equations into the signed differential equation almost everywhere
on the full real line. The literal physical differential expression equals
z times the same constructed solution almost everywhere.

These facts do not yet identify an operator spectrum. The remaining
operator work includes constructing the whole-line L2 domain and
unbounded realization, proving self-adjointness, identifying the
spectrum, and proving pure
absolute continuity. Bounded propagation is a prerequisite for that
work and is not used as a definition of the spectrum.

## The densely defined minimal whole-line physical operator

The construction now reaches an actual partially defined complex-linear
operator on the Hermitian Hilbert space L2(R; C2). Its domain is exactly
the L2 classes of smooth compactly supported pairs. Its action is the
original signed differential expression with the actual periodically
extended physical L2 potential.

[`L2WholeLinePotentialPeriods.lean`](../NLS/ZakharovShabat/L2WholeLinePotentialPeriods.lean)
proves that periodization recovers the original unit-interval L2 class
and preserves its L2 seminorm on every positive or negative integer period.

[`L2WholeLineLocalIntegrability.lean`](../NLS/ZakharovShabat/L2WholeLineLocalIntegrability.lean)
proves global strong measurability and square integrability on every
compact subset, including across integer seams. The potential is not
assumed to be square integrable over the full real line.

[`L2WholeLineTestOperator.lean`](../NLS/ZakharovShabat/L2WholeLineTestOperator.lean)
proves that potential multiplication maps continuous compactly supported
tests into L2. The full physical expression maps compactly supported C1
pairs into L2, with both signed derivative terms retained.

[`L2WholeLineTestDomain.lean`](../NLS/ZakharovShabat/L2WholeLineTestDomain.lean)
constructs the Hermitian whole-line L2 space and an injective complex-linear
inclusion of smooth compact tests with dense range. Density uses the
actual smooth compact approximation theorem in L2.

[`L2WholeLineMinimalOperator.lean`](../NLS/ZakharovShabat/L2WholeLineMinimalOperator.lean)
constructs the minimal partial linear operator on that dense domain.
On every test class its value agrees almost everywhere with the literal
physical differential expression, using the same original potential.

This is the minimal realization on compact tests. Identifying its closure
and the maximal differential domain, proving self-adjointness for real
potentials, identifying the spectrum and proving pure absolute continuity
remain unfinished. The bounded Floquet solutions established earlier
remain prerequisites for those spectral claims.

## Symmetry and closure for real whole-line potentials

[`L2WholeLineReality.lean`](../NLS/ZakharovShabat/L2WholeLineReality.lean)
transfers almost-everywhere properties of the original unit-interval
representative to the actual periodic potential on R. In particular,
every original real Hilbert source has conjugate off-diagonal potential
components almost everywhere on the full real line.

[`L2WholeLineSymmetry.lean`](../NLS/ZakharovShabat/L2WholeLineSymmetry.lean)
proves the Hermitian L2 pairing identity for the actual minimal operator.
The proof uses the original signed derivatives, removes boundary terms
by compact support, and cancels potential terms using the a.e. reality
relation. It establishes Mathlib's formal-adjoint relation and containment
in the actual Hilbert-space adjoint.

The adjoint is closed. Consequently the real minimal operator is closable,
its graph closure is a closed operator with dense domain, and the original
smooth compact test domain is a core for that closure. These statements
also apply explicitly to the unchanged original real Hilbert sources.

Self-adjointness requires equality with the adjoint and remains unfinished.
The maximal differential-domain characterization, band-spectrum identity
and pure absolute continuity are still separate proof obligations.

## Absolute continuity and Green's identity on the whole real line

[`L2WholeLinePeriodAbsoluteContinuity.lean`](../NLS/ZakharovShabat/L2WholeLinePeriodAbsoluteContinuity.lean)
proves absolute continuity of the actual unit-interval solution and of its
continuation in the local coordinate of every closed integer period.
[`L2WholeLineODEIntegrability.lean`](../NLS/ZakharovShabat/L2WholeLineODEIntegrability.lean)
proves continuity of the actual whole-line pair and integrability of its
physical differential-equation right-hand side on every compact interval.

[`L2WholeLineIntegralEquation.lean`](../NLS/ZakharovShabat/L2WholeLineIntegralEquation.lean)
assembles the closed-period identities into the original integral equation
between any two real times. It proves absolute continuity on every compact
interval, including negative times and intervals crossing integer seams.
This uses the existing Banach-valued primitive and fundamental-theorem
results, rather than inferring absolute continuity from an a.e. derivative.

[`L2WholeLineGreenIdentity.lean`](../NLS/ZakharovShabat/L2WholeLineGreenIdentity.lean)
proves the actual Hermitian boundary identity for two solutions of real
physical potentials, with factor conjugate(z)-w. At a real spectral
parameter the boundary current is conserved between any two real times.
No global L2 membership is imposed on these physical solutions.

These results concern the actual constructed solutions. Characterizing
arbitrary adjoint-domain elements, proving self-adjointness, identifying
the whole-line spectrum and proving pure absolute continuity remain open.

## The actual weak adjoint equation and absolutely continuous representatives

[`L2WholeLineAdjointEquation.lean`](../NLS/ZakharovShabat/L2WholeLineAdjointEquation.lean)
characterizes the actual Hilbert adjoint domain in both directions by the
original weak physical equation with an L2 image. That proposed image
equals the actual adjoint image. The equation integrates the unchanged
physical differential expression against smooth compact tests.

[`L2WholeLineWeakDerivative.lean`](../NLS/ZakharovShabat/L2WholeLineWeakDerivative.lean)
uses local L2 potential and global L2 input/image vectors to prove local
L1 integrability of the signed derivative candidate by Holder's inequality.
[`L2WholeLineWeakCoordinates.lean`](../NLS/ZakharovShabat/L2WholeLineWeakCoordinates.lean)
derives both scalar distributional derivative identities, using conjugated
coordinate tests in the actual compact smooth domain and the real-type
potential relation. The opposite derivative signs are retained.

Four general analytic prerequisites supply the missing regularity bridge.
[`CompactSmoothPrimitive.lean`](../NLS/FunctionalAnalysis/CompactSmoothPrimitive.lean)
constructs a compact smooth primitive of every zero-integral compact smooth
test. [`WeakDerivativeConstant.lean`](../NLS/FunctionalAnalysis/WeakDerivativeConstant.lean)
uses normalized bumps and the fundamental lemma to show that a locally
integrable Banach-valued function with zero weak derivative is constant a.e.
[`LocallyIntegrablePrimitive.lean`](../NLS/FunctionalAnalysis/LocallyIntegrablePrimitive.lean)
proves local absolute continuity and the compact-test equation for locally
integrable primitives. [`WeakDerivativeAbsoluteContinuity.lean`](../NLS/FunctionalAnalysis/WeakDerivativeAbsoluteContinuity.lean)
combines these facts: a locally integrable Banach-valued weak derivative
gives an a.e.-equal representative absolutely continuous on every compact
real interval, with that prescribed derivative almost everywhere.

[`L2WholeLineAdjointRegularity.lean`](../NLS/ZakharovShabat/L2WholeLineAdjointRegularity.lean)
applies this theorem to every vector in the actual real physical adjoint
domain. Its locally absolutely continuous representative realizes the
actual adjoint image under the original signed differential expression.
This also applies to the unchanged original real Hilbert sources.

The converse from arbitrary locally AC L2 representatives with an L2
physical differential image remains to be proved. Hence the maximal-domain
equality, local H1/core estimates, self-adjointness, whole-line spectrum and
pure absolute continuity are still unfinished.

## The self-adjoint whole-line operator and its maximal domain

[`PhysicalOperatorSupport.lean`](../NLS/ZakharovShabat/PhysicalOperatorSupport.lean)
shows that the original differential expression preserves compact support.
[`L2WholeLineMaximalDomain.lean`](../NLS/ZakharovShabat/L2WholeLineMaximalDomain.lean)
uses compact-test integration by parts to prove the converse to adjoint
regularity. The actual Hilbert adjoint domain is exactly the L2 classes
with a locally absolutely continuous representative whose original physical
differential expression belongs to L2. That expression is the actual
adjoint image.

[`ACIntegralAtInfinity.lean`](../NLS/FunctionalAnalysis/ACIntegralAtInfinity.lean)
proves a Banach-valued boundary theorem: an integrable locally AC function
with an integrable prescribed a.e. derivative tends to zero at both ends
of the real line, and the derivative has zero integral. Absolute continuity
is retained; a.e. differentiability alone does not justify this conclusion.
[`L2WholeLineAdjointSymmetry.lean`](../NLS/ZakharovShabat/L2WholeLineAdjointSymmetry.lean)
applies the theorem to the original Hermitian boundary form. L2 estimates
make that form and its derivative integrable. This proves symmetry on the
entire actual adjoint domain for real physical potentials.

[`SymmetricAdjoint.lean`](../NLS/FunctionalAnalysis/SymmetricAdjoint.lean)
proves that actual adjoints reverse dense operator inclusion, and that a
dense symmetric operator with a symmetric adjoint has a self-adjoint
adjoint. [`DoubleAdjointClosure.lean`](../NLS/FunctionalAnalysis/DoubleAdjointClosure.lean)
uses Hilbert-space orthogonal separation to identify the double adjoint
relation with the closed graph, and hence the double adjoint operator with
the actual graph closure.

[`L2WholeLineSelfAdjoint.lean`](../NLS/ZakharovShabat/L2WholeLineSelfAdjoint.lean)
combines these results. The original real minimal physical operator is
essentially self-adjoint. Its graph closure equals its actual Hilbert
adjoint and has the maximal locally AC differential domain. The original
compact smooth tests form a core for this maximal self-adjoint operator.
All assertions retain the unchanged signed physical expression and apply
to the original real Hilbert sources.

This establishes the operator and domain needed for the whole-line spectral
claim on printed p.17. Resolvent construction, identification of the band
spectrum, spectral measures and pure absolute continuity remain unfinished.
The exact2014 comparison and G2 interval-norm question remain separate.

## The original whole-line spectrum and bounded nonreal resolvent

[`L2WholeLineNonrealResolvent.lean`](../NLS/ZakharovShabat/L2WholeLineNonrealResolvent.lean)
defines the original physical pencil on the actual graph-closure domain.
Its resolvent set requires a bounded two-sided inverse; its spectrum is the
complement of that independently defined set. The inverse takes values in
the actual domain with its inherited L2 norm, so boundedness expresses
precisely the original Hilbert base-space bound.

[`SymmetricPencilEstimate.lean`](../NLS/FunctionalAnalysis/SymmetricPencilEstimate.lean)
proves the lower bound |Im z| times the input norm for a symmetric partial
operator's spectral pencil. It gives injectivity at nonreal parameters.
[`ClosedPencilRange.lean`](../NLS/FunctionalAnalysis/ClosedPencilRange.lean)
uses this bound and the original closed graph to prove closed range;
completeness of the inherited domain norm is not assumed.
[`SelfAdjointPencilRange.lean`](../NLS/FunctionalAnalysis/SelfAdjointPencilRange.lean)
uses orthogonal separation and the actual adjoint to prove dense range.
Closedness and density together give bijectivity on the actual domain.

[`SelfAdjointNonrealResolvent.lean`](../NLS/FunctionalAnalysis/SelfAdjointNonrealResolvent.lean)
constructs the bounded inverse and proves both inverse identities and the
base-space operator-norm bound 1/|Im z|. Applied to the original whole-line
operator, every nonreal parameter lies in its resolvent set and its spectrum
for real physical potentials lies on the real axis. The public examples
also cover the unchanged original real Hilbert sources.

Real gap resolvents and spectral membership of the Floquet bands, including
endpoints and collapsed gaps, remain to be proved. Spectral measures and
pure absolute continuity remain separate unfinished requirements. The
exact2014 comparison and G2 interval-norm question remain separate.

## Actual cutoff vectors and positive periodic Floquet mass

[`L2WholeLineWeylCriterion.lean`](../NLS/ZakharovShabat/L2WholeLineWeylCriterion.lean)
proves approximate-eigenvector criteria for the independently defined physical
spectrum, directly from the two-sided bounded resolvent equations.
[`L2WholeLineWeylGrowth.lean`](../NLS/ZakharovShabat/L2WholeLineWeylGrowth.lean)
provides a version with linearly growing squared input mass and uniformly
bounded squared residual. Both criteria use the actual closure domain.

[`L2WholeLineOfPair.lean`](../NLS/ZakharovShabat/L2WholeLineOfPair.lean)
constructs the original Hermitian L2 class from a square-integrable pair and
identifies its squared norm with the squared fibre-norm integral.
[`PhysicalOperatorProductRule.lean`](../NLS/ZakharovShabat/PhysicalOperatorProductRule.lean)
proves the signed differential product rule for scalar cutoffs.
[`L2WholeLineCutoff.lean`](../NLS/ZakharovShabat/L2WholeLineCutoff.lean)
places every smooth compact cutoff of the original locally AC solution in
the actual self-adjoint closure domain and computes its original image.

[`L2WholeLineFloquetMass.lean`](../NLS/ZakharovShabat/L2WholeLineFloquetMass.lean)
shows that a nonzero initial vector never vanishes. For a unit Floquet
multiplier the squared physical fibre norm is periodic, its unit-period
integral is positive, and its integral over n periods is exactly n times
that positive mass.
[`L2WholeLineCutoffResidual.lean`](../NLS/ZakharovShabat/L2WholeLineCutoffResidual.lean)
identifies the actual pencil residual with the signed cutoff derivative.
The squared cutoff and residual norms are exactly the mass integrals
weighted by the squared cutoff and squared derivative, respectively.

The next step is to choose expanding cutoffs and bound these integrals.
Floquet band membership, real-gap resolvents, full spectrum equality,
spectral measures and pure absolute continuity remain unfinished.
Exact2014 and G2 remain separate source questions.

## Floquet band membership in the original whole-line spectrum

[`ScaledCutoff.lean`](../NLS/FunctionalAnalysis/ScaledCutoff.lean)
constructs a fixed smooth compact scalar cutoff equal to one on [0,1].
Positive dilation preserves smoothness and compact support, gives equality
to one on [0,R], and divides the squared derivative integral by R.
[`CutoffMassEstimates.lean`](../NLS/FunctionalAnalysis/CutoffMassEstimates.lean)
proves that the cutoff retains the mass on [0,R]. A uniform density bound
controls the derivative-weighted mass uniformly for R at least one.

[`L2WholeLineBandSpectrum.lean`](../NLS/ZakharovShabat/L2WholeLineBandSpectrum.lean)
applies these estimates to the actual unit-multiplier Floquet solution.
Its positive periodic mass grows linearly, while the original cutoff
pencil residual stays bounded. The actual-domain growing-mass criterion
therefore proves membership in the independently defined physical spectrum.

For every unchanged original real Hilbert source, the full closed Floquet
band set is included in the whole-line operator spectrum. All endpoints
and collapsed gaps are included through the original monodromy criterion.

The opposite inclusion still requires bounded resolvents in real gaps.
Full spectral equality, spectral measures and pure absolute continuity
remain unfinished. Exact2014 and G2 remain separate source questions.

## Stable and unstable physical modes in the real gaps

[`FloquetHyperbolicRoots.lean`](../NLS/ZakharovShabat/FloquetHyperbolicRoots.lean)
proves that a unimodular quadratic with no unit-circle root has reciprocal
stable and unstable characteristic roots. The statement applies to the
actual determinant-one physical monodromy.
[`FloquetHyperbolicBasis.lean`](../NLS/ZakharovShabat/FloquetHyperbolicBasis.lean)
constructs a full eigenbasis from the two distinct roots.

[`L2FloquetGapBasis.lean`](../NLS/ZakharovShabat/L2FloquetGapBasis.lean)
applies this construction to every original real source parameter outside
the full closed bands. Every original physical solution decomposes into
the two propagated basis modes.
[`FloquetModeProjections.lean`](../NLS/ZakharovShabat/FloquetModeProjections.lean)
constructs the algebraic projections. They sum to the identity, are
idempotent, annihilate each other, and respect scalar monodromy action.
[`L2FloquetModeDecay.lean`](../NLS/ZakharovShabat/L2FloquetModeDecay.lean)
proves exact propagation at all signed integer translates, stable decay
along forward periods and unstable decay along backward periods.

Decay along fixed period sequences is not yet a uniform global kernel
bound or a bounded Green operator. Real-gap inverses, reverse spectral
inclusion, full spectral equality, spectral measures and pure absolute
continuity remain unfinished. Exact2014 and G2 remain separate questions.

## A bounded periodic Floquet change of basis

[`FloquetPeriodicFactor.lean`](../NLS/ZakharovShabat/FloquetPeriodicFactor.lean)
removes the exponential factor from each actual Floquet mode. The result
is one-periodic, with exact reconstruction and a uniform bound.
[`FloquetPeriodicFactorRegularity.lean`](../NLS/ZakharovShabat/FloquetPeriodicFactorRegularity.lean)
proves local absolute continuity and the exact derivative of this normalization.

[`L2FloquetPeriodicMatrix.lean`](../NLS/ZakharovShabat/L2FloquetPeriodicMatrix.lean)
assembles the original physical columns into a periodic matrix. Its exact
factorization proves pointwise invertibility. The matrix and its inverse
are continuous and uniformly bounded on the whole real line.
[`L2FloquetColumnRegularity.lean`](../NLS/ZakharovShabat/L2FloquetColumnRegularity.lean)
identifies the pair columns with those matrix entries, proves their local
absolute continuity, and verifies B_j prime = A B_j - log(mu_j) B_j
almost everywhere for the original physical coefficient.

The remaining real-gap construction is to solve the constant diagonal
scalar equations, transfer those solutions through this bounded change
of basis, and verify both physical pencil inverse identities. The reverse
spectral inclusion, full equality, spectral measures and pure absolute
continuity remain unfinished. Exact2014 and G2 remain separate questions.

## Bounded scalar solvers and physical L2 multiplication

[`SymmetricPencilSurjective.lean`](../NLS/FunctionalAnalysis/SymmetricPencilSurjective.lean)
proves that a surjective real symmetric pencil is injective.
[`L2WholeLineScalarMaps.lean`](../NLS/ZakharovShabat/L2WholeLineScalarMaps.lean)
constructs bounded coordinate projections and embeddings for the original
Hermitian L2 space, with exact almost-everywhere formulas.
[`L2WholeLineFreePotential.lean`](../NLS/ZakharovShabat/L2WholeLineFreePotential.lean)
identifies the actual zero potential.
[`L2WholeLineClosureRepresentative.lean`](../NLS/ZakharovShabat/L2WholeLineClosureRepresentative.lean)
gives the exact weak derivative of an AC representative of every vector
in the actual closure domain.

[`L2WholeLineScalarODEInverse.lean`](../NLS/ZakharovShabat/L2WholeLineScalarODEInverse.lean)
uses the verified zero-potential resolvent at i*alpha to construct a bounded
scalar solution map whenever Re(alpha) is nonzero. Its global L2 representative
is locally absolutely continuous and solves y prime = alpha*y+h almost everywhere.
[`L2WholeLineDiagonalInverse.lean`](../NLS/ZakharovShabat/L2WholeLineDiagonalInverse.lean)
assembles the two scalar solutions in the original physical pair coordinates.

[`L2WholeLineScalarMultiplication.lean`](../NLS/ZakharovShabat/L2WholeLineScalarMultiplication.lean)
and [`L2WholeLineMatrixMultiplication.lean`](../NLS/ZakharovShabat/L2WholeLineMatrixMultiplication.lean)
construct bounded operators from continuous uniformly bounded scalar and
matrix fields. The operators have the literal pointwise product formulas
almost everywhere on the full real line.

The remaining physical gap construction transfers these diagonal solutions
through the periodic matrix and verifies both inverse equations on the
actual domain. Reverse spectral inclusion, full equality, spectral measures
and pure absolute continuity remain unfinished in this milestone.
Exact2014 and G2 remain separate source questions.

## Equality of the actual whole-line spectrum and the closed Floquet bands

[`L2FloquetInhomogeneous.lean`](../NLS/ZakharovShabat/L2FloquetInhomogeneous.lean)
proves that the original periodic Floquet columns transfer the diagonal
inhomogeneous equation back to the physical equation. The logarithmic
terms cancel exactly, with the original signs of the pencil z-L.
[`L2WholeLineFloquetInverse.lean`](../NLS/ZakharovShabat/L2WholeLineFloquetInverse.lean)
composes bounded matrix multiplication and the scalar solution maps to
obtain a bounded physical solution operator. Its representatives are
locally absolutely continuous and satisfy Lf=z*f-g almost everywhere.

[`L2WholeLinePencilInverse.lean`](../NLS/ZakharovShabat/L2WholeLinePencilInverse.lean)
places these solutions in the actual graph-closure domain and computes
the actual closure image. At a real parameter, symmetry and surjectivity
give injectivity, hence both inverse equations. The resulting continuous
linear inverse has values in the actual domain with its inherited L2 norm.

[`L2WholeLineGapResolvent.lean`](../NLS/ZakharovShabat/L2WholeLineGapResolvent.lean)
applies this construction to every real point outside the closed source
bands. The stable and unstable multipliers have logarithms with nonzero
real parts, so the verified scalar inverses apply. Combining these real-gap
resolvents with the nonreal resolvents and the closed-band inclusion proves
`source_wholeLineSpectrum_eq_floquetBands`: the independently defined
spectrum of the original physical operator is exactly the full closed
Floquet band set, including all endpoints and collapsed gaps.

This establishes the spectral-set identity in the printed p.17 claim.
The accompanying assertion of absolute continuity still requires actual
spectral measures and exclusion of singular spectral components. Spectral
set equality alone does not establish that assertion. Exact2014 and G2
remain separate source questions.

## Absence of eigenvectors for the actual whole-line operator

[`L2WholeLineUnitModeNotL2.lean`](../NLS/ZakharovShabat/L2WholeLineUnitModeNotL2.lean)
excludes nonzero square-integrable unit-multiplier modes by positive periodic
mass. [`L2WholeLineModeNotL2.lean`](../NLS/ZakharovShabat/L2WholeLineModeNotL2.lean)
extends this to every nonzero multiplier: translation invariance of the
full mass would force its norm to be one.

[`FloquetQuadraticReduction.lean`](../NLS/ZakharovShabat/FloquetQuadraticReduction.lean)
factors the unimodular characteristic quadratic without requiring distinct
roots. Applying one characteristic factor produces a mode for the other.
[`L2WholeLineNoL2Solution.lean`](../NLS/ZakharovShabat/L2WholeLineNoL2Solution.lean)
uses this reduction and translation invariance to exclude every nonzero
original physical fundamental solution from global L2. The proof includes
repeated roots and does not assume an eigenbasis at band endpoints.

[`PhysicalWronskian.lean`](../NLS/ZakharovShabat/PhysicalWronskian.lean)
proves Wronskian conservation for arbitrary locally absolutely continuous
solutions of the original physical equation.
[`L2WholeLineACUniqueness.lean`](../NLS/ZakharovShabat/L2WholeLineACUniqueness.lean)
then identifies every such solution with the constructed fundamental
solution having its actual initial value.
[`L2WholeLineNoEigenvectors.lean`](../NLS/ZakharovShabat/L2WholeLineNoEigenvectors.lean)
applies this to the AC representative of an actual closure-domain vector.
The original self-adjoint whole-line operator has no nonzero eigenvectors
at any complex parameter, including every band endpoint, for every
unchanged original real Hilbert source.

This rules out point spectrum. Constructing the actual spectral measures
and excluding singular continuous spectrum remain necessary for the
printed absolute-continuity claim. Exact2014 and G2 remain separate questions.

## The actual unitary Cayley transform

[`SelfAdjointResolventIdentity.lean`](../NLS/FunctionalAnalysis/SelfAdjointResolventIdentity.lean)
proves the resolvent identity and the conjugate-parameter adjoint formula
for the actual bounded resolvents of a self-adjoint partial operator.
[`SelfAdjointCayley.lean`](../NLS/FunctionalAnalysis/SelfAdjointCayley.lean)
constructs U = 1 + 2i R(-i), proves both unitary inverse identities, and
shows that one has no nonzero fixed vector.

[`L2WholeLineCayley.lean`](../NLS/ZakharovShabat/L2WholeLineCayley.lean)
specializes these results to the closure of the original physical
whole-line operator. Its Cayley transform is exactly the expression
formed from the already constructed physical nonreal resolvent and is
star-normal, providing a bounded operator for continuous functional calculus.

The actual scalar spectral measures have not yet been constructed.
The spectral-set equality and absence of physical eigenvectors are
already proved, but exclusion of singular continuous spectrum remains
necessary for pure absolute continuity. Exact2014 and G2 remain separate questions.

## Actual scalar spectral measures of the physical Cayley transform

[`SelfAdjointCayleyEigenvectors.lean`](../NLS/FunctionalAnalysis/SelfAdjointCayleyEigenvectors.lean)
transfers absence of eigenvectors from a self-adjoint partial operator to
its actual bounded Cayley transform, using an actual domain vector supplied
by the nonreal resolvent.
[`L2WholeLineCayleyEigenvectors.lean`](../NLS/ZakharovShabat/L2WholeLineCayleyEigenvectors.lean)
specializes this to the original whole-line closure and unchanged real source.

[`VectorSpectralFunctional.lean`](../NLS/FunctionalAnalysis/VectorSpectralFunctional.lean)
constructs a positive real vector functional from a star-algebra homomorphism
into bounded Hilbert-space operators. Positivity follows from a continuous
square root and the Hilbert adjoint.
[`VectorSpectralMeasure.lean`](../NLS/FunctionalAnalysis/VectorSpectralMeasure.lean)
applies Riesz representation to construct its finite scalar measure, proves
the correct total mass, and establishes the squared-norm integral identity.
[`VectorSpectralIntegral.lean`](../NLS/FunctionalAnalysis/VectorSpectralIntegral.lean)
proves the full complex integral representation.

[`NormalOperatorSpectralMeasure.lean`](../NLS/FunctionalAnalysis/NormalOperatorSpectralMeasure.lean)
uses continuous functional calculus on the independently defined spectrum
of an actual bounded normal operator. The coordinate moment recovers that
operator itself.
[`L2WholeLineCayleySpectralMeasure.lean`](../NLS/ZakharovShabat/L2WholeLineCayleySpectralMeasure.lean)
constructs these measures for the original physical Cayley transform,
with total mass equal to the original vector's squared norm, complex
integral representation, squared-norm identity and coordinate moment.
The actual Cayley spectrum lies on the unit circle.

These are measures on the complex Cayley spectrum. Proving they have no
atoms, transporting them to the real line, identifying the unbounded
operator resolvent integral, and proving pure absolute continuity remain
unfinished. Exact2014 and G2 remain separate source questions.

## Atom exclusion and real-line transport of the actual measures

[`NormalOperatorPencilDense.lean`](../NLS/FunctionalAnalysis/NormalOperatorPencilDense.lean)
proves that every scalar pencil of a bounded normal operator without
eigenvectors has dense range.
[`VectorSpectralMeasureAtomBound.lean`](../NLS/FunctionalAnalysis/VectorSpectralMeasureAtomBound.lean)
bounds an actual spectral atom by the squared norm of a continuous test
operator whose function equals one at that point.
[`SpectralPeakFunction.lean`](../NLS/FunctionalAnalysis/SpectralPeakFunction.lean)
constructs continuous peaks epsilon/(epsilon+norm(x-a)), and
[`NormalSpectralPeakEstimates.lean`](../NLS/FunctionalAnalysis/NormalSpectralPeakEstimates.lean)
proves they are contractive and epsilon-small on the original pencil range.
[`NormalOperatorSpectralMeasureNoAtoms.lean`](../NLS/FunctionalAnalysis/NormalOperatorSpectralMeasureNoAtoms.lean)
combines these estimates with dense range to prove that the constructed
scalar CFC measures have no atoms.

[`L2WholeLineCayleyMeasureNoAtoms.lean`](../NLS/ZakharovShabat/L2WholeLineCayleyMeasureNoAtoms.lean)
applies this to the original physical Cayley operator. Every singleton,
complex coordinate fiber and countable spectral subset has zero measure.
In particular the exceptional inverse-Cayley fiber at one is null.
[`InverseCayleyCoordinate.lean`](../NLS/FunctionalAnalysis/InverseCayleyCoordinate.lean)
proves measurability, reality on the unit circle, and exact inversion
away from one for the original inverse Cayley coordinate.
[`L2WholeLineRealSpectralMeasure.lean`](../NLS/ZakharovShabat/L2WholeLineRealSpectralMeasure.lean)
transports the actual physical CFC measures to the real line. They are
finite, retain the original vector's squared norm as total mass, and
have zero mass on every countable real subset.

Identifying the actual unbounded operator resolvent integral remains the
next step. Atom exclusion alone does not exclude singular continuous
spectrum or prove pure absolute continuity. Exact2014 and G2 remain
separate source questions.

## The actual unbounded resolvent and its real spectral integral

[`CayleyResolventFunction.lean`](../NLS/FunctionalAnalysis/CayleyResolventFunction.lean)
constructs the continuous resolvent function on the actual Cayley spectrum.
Its denominator is nonzero for nonreal spectral parameters. The function
vanishes at the exceptional point one; away from one it equals the original
real resolvent kernel after inverse Cayley transport.
[`SelfAdjointCayleyResolvent.lean`](../NLS/FunctionalAnalysis/SelfAdjointCayleyResolvent.lean)
uses the original resolvent identity to identify the actual bounded
nonreal inverse of a self-adjoint partial operator with this continuous
functional calculus expression.

[`RealResolventKernel.lean`](../NLS/FunctionalAnalysis/RealResolventKernel.lean)
proves continuity and the inverse-imaginary-part bound for the scalar
kernel (z-t)^(-1). It is integrable against every finite real measure.
[`L2WholeLineSpectralResolventIntegral.lean`](../NLS/ZakharovShabat/L2WholeLineSpectralResolventIntegral.lean)
applies these results to the original physical operator. Its actual
resolvent vector expectation equals the integral of (z-t)^(-1) against
the actual real measure already constructed. The proof transports the
Cayley integral and uses the proved zero mass of the exceptional fiber.

This identifies the actual operator and measure through their resolvent,
without assuming a spectral representation as an extra hypothesis.
Local band-interior estimates and exclusion of singular continuous
spectrum remain unfinished; pure absolute continuity is not yet proved.
Exact2014 and G2 remain separate source questions.

## Poisson estimates and a sufficient absolute-continuity criterion

[`RealPoissonKernel.lean`](../NLS/FunctionalAnalysis/RealPoissonKernel.lean)
identifies the negative imaginary part of the original scalar resolvent
kernel with the unnormalized Poisson kernel epsilon/((x-t)^2+epsilon^2).
The kernel is nonnegative and integrable against every finite real measure.
Its integral bounds the mass of the centered interval [x-epsilon,x+epsilon]
by twice epsilon times the Poisson integral.

[`IntervalMeasureDomination.lean`](../NLS/FunctionalAnalysis/IntervalMeasureDomination.lean)
extends half-open interval estimates to domination by the actual Stieltjes
measure through its outer-measure construction. For finite real measures,
linear closed-interval bounds imply domination by Lebesgue measure.
[`PoissonAbsoluteContinuity.lean`](../NLS/FunctionalAnalysis/PoissonAbsoluteContinuity.lean)
combines these results: a uniform Poisson bound by C implies measure
domination by C times Lebesgue measure, and hence absolute continuity.
The uniform bound is an explicit hypothesis of this criterion.

[`L2WholeLinePoissonIntegral.lean`](../NLS/ZakharovShabat/L2WholeLinePoissonIntegral.lean)
identifies the actual physical real measure's Poisson transform with the
negative imaginary part of its original resolvent expectation. A bound
on this expectation gives the corresponding linear interval mass estimate.

The actual physical band-interior resolvent bounds, localization and
exclusion of singular continuous spectrum remain unfinished. The general
criterion does not itself prove pure absolute continuity for this operator.
Exact2014 and G2 remain separate source questions.

## A local criterion for the actual physical spectral measure

[`RealPoissonBounds.lean`](../NLS/FunctionalAnalysis/RealPoissonBounds.lean)
proves inverse-height and distance-from-center bounds for the original
Poisson kernel and its integrals against finite real measures.
[`LocalPoissonAbsoluteContinuity.lean`](../NLS/FunctionalAnalysis/LocalPoissonAbsoluteContinuity.lean)
uses these estimates to localize the verified uniform Poisson criterion.
A uniform bound for small positive heights and centers in a larger interval
implies absolute continuity of the measure on a smaller closed interval.
Large heights and centers outside the larger interval are controlled by
total mass and the positive distance between the interval boundaries.

[`L2WholeLineLocalSpectralAC.lean`](../NLS/ZakharovShabat/L2WholeLineLocalSpectralAC.lean)
applies this to the actual real spectral measure of the original physical
operator. A uniform small-height bound on its original resolvent expectation
near a real interval implies absolute continuity on a smaller interval.
The resolvent bound is an explicit hypothesis of this theorem.

Proving that physical bound from the original Floquet Green operator is
still required. Countable exceptional parameters and extension from compact
inputs to all Hilbert vectors must also be handled. Pure absolute continuity
of the physical operator remains unfinished. Exact2014 and G2 remain
separate source questions.

## Uniform physical Floquet mode-kernel estimates

[`L2FloquetNonrealBasis.lean`](../NLS/ZakharovShabat/L2FloquetNonrealBasis.lean)
uses the actual physical spectrum and cutoff criterion to exclude
unit-modulus monodromy multipliers at every nonreal parameter. It obtains
actual reciprocal stable and unstable multipliers and an eigenbasis.
[`FloquetRootProjection.lean`](../NLS/ZakharovShabat/FloquetRootProjection.lean)
identifies the original mode projection with (M-nu*Id)/(mu-nu).
Root magnitudes are controlled by the trace, and squared root separation
is the discriminant. [`FloquetLocalProjectionBound.lean`](../NLS/ZakharovShabat/FloquetLocalProjectionBound.lean)
therefore bounds both root projections uniformly near any parameter
where the discriminant is nonzero, without selecting continuous roots
or normalizing eigenvectors.

[`L2WholeLineFundamentalJoint.lean`](../NLS/ZakharovShabat/L2WholeLineFundamentalJoint.lean)
proves joint continuity of the original full fundamental matrix and inverse
in frequency, physical L2 potential and all real times. Signed monodromy
powers glue at every seam, including negative times.
[`L2WholeLineGreenIngredients.lean`](../NLS/ZakharovShabat/L2WholeLineGreenIngredients.lean)
gives compact frequency/time bounds for both matrix directions and applies
the local projection estimate to the actual physical monodromy.
[`FinTwoMatrixProductBound.lean`](../NLS/FunctionalAnalysis/FinTwoMatrixProductBound.lean)
tracks the dimension factors of the entrywise matrix norm.
[`L2WholeLineModeKernelBound.lean`](../NLS/ZakharovShabat/L2WholeLineModeKernelBound.lean)
combines the estimates for the actual projected fundamental kernel
F(t)*P*F(s)^(-1). It is uniformly bounded on compact input/output time
sets near every parameter with distinct Floquet roots, for either root order.

The actual resolvent still needs to be identified with the one-sided
Green integrals of these kernels. That identity will allow the local
spectral-measure criterion to be applied to compact inputs. Exceptional
parameters and extension to all vectors remain unfinished; pure absolute
continuity is not yet proved. Exact2014 and G2 remain separate questions.

## Scalar Green formulas and the original physical resolvent

[`ScalarACVariation.lean`](../NLS/FunctionalAnalysis/ScalarACVariation.lean)
uses the verified AC fundamental theorem and a smooth integrating factor
to prove variation of constants for locally absolutely continuous scalar
solutions with locally integrable forcing.
[`ScalarL2ExponentialTail.lean`](../NLS/FunctionalAnalysis/ScalarL2ExponentialTail.lean)
proves that a nondecaying exponential on an infinite half-line has zero
coefficient if the full function is globally L2. This includes zero real
part of the exponent.
[`ScalarL2OneSidedFormula.lean`](../NLS/FunctionalAnalysis/ScalarL2OneSidedFormula.lean)
combines these results to remove the growing tail and obtain forward
and backward one-sided exponential integral formulas.

[`L2WholeLineScalarGreenFormula.lean`](../NLS/ZakharovShabat/L2WholeLineScalarGreenFormula.lean)
identifies the already constructed bounded scalar inverse with those
Green integrals when the forcing vanishes on the relevant half-line.
[`L2WholeLineNonrealFloquetInverse.lean`](../NLS/ZakharovShabat/L2WholeLineNonrealFloquetInverse.lean)
identifies every global L2 locally AC physical pencil solution with the
original nonreal resolvent, using the actual closure domain and its inverse
identity. In particular, the bounded Floquet inverse is that same resolvent.
[`L2FloquetNonrealTrace.lean`](../NLS/ZakharovShabat/L2FloquetNonrealTrace.lean)
supplies the original trace-sum identity for its stable and unstable multipliers.

The scalar Green formulas still need to be recombined into the projected
full-fundamental matrix kernel. Uniform compact-input resolvent bounds,
the exceptional parameter set and extension of spectral absolute continuity
to all vectors remain unfinished. Pure absolute continuity is not yet
proved. Exact2014 and G2 remain separate source questions.

## Actual matrix Green formula and uniform physical resolvent bounds

[`L2FloquetKernelCancellation.lean`](../NLS/ZakharovShabat/L2FloquetKernelCancellation.lean)
cancels the original periodic Floquet factors and diagonal exponential
propagators into the projected full-fundamental matrix kernel.
[`L2FloquetGreenKernelAction.lean`](../NLS/ZakharovShabat/L2FloquetGreenKernelAction.lean)
identifies each root projection with its actual eigenbasis column and
expresses both kernel actions in the original ordered pair coordinates.
[`L2WholeLineDiagonalGreenFormula.lean`](../NLS/ZakharovShabat/L2WholeLineDiagonalGreenFormula.lean)
combines the existing scalar inverses into the stable forward integral
and unstable backward integral.

[`L2WholeLineFloquetGreenFormula.lean`](../NLS/ZakharovShabat/L2WholeLineFloquetGreenFormula.lean)
recombines these integrals and identifies them with the original physical
nonreal resolvent. The formula uses the actual kernels F(t)*P*F(s)^(-1),
the unchanged closure domain, and the original forcing signs (i*g1,-i*g2).
[`L2WholeLineGreenFormula.lean`](../NLS/ZakharovShabat/L2WholeLineGreenFormula.lean)
constructs the needed basis and bounds at every nonreal parameter, with
actual reciprocal stable/unstable roots and their physical trace identity.

[`L2WholeLineGreenKernelEstimate.lean`](../NLS/ZakharovShabat/L2WholeLineGreenKernelEstimate.lean)
controls matrix action and interval integrals by the original pair norm
and input L1 mass, retaining the dimension-two factor.
[`L2WholeLineLocalResolventBound.lean`](../NLS/ZakharovShabat/L2WholeLineLocalResolventBound.lean)
gives a uniform local pair bound for the actual resolvent on compact forcing.
[`L2WholeLineResolventExpectationBound.lean`](../NLS/ZakharovShabat/L2WholeLineResolventExpectationBound.lean)
then bounds the actual Hermitian expectation uniformly near every parameter
with distinct Floquet roots, independently of the nonzero imaginary part.
This includes approach to the real line.

Applying the proved local spectral-measure criterion, handling the
exceptional repeated-root set and extending from compact inputs to all
vectors remain unfinished. Pure absolute continuity is not yet proved.
Exact2014 and G2 remain separate source questions.

## Absolute continuity for compact physical inputs

[`L2WholeLineCompactLocalSpectralAC.lean`](../NLS/ZakharovShabat/L2WholeLineCompactLocalSpectralAC.lean)
applies the actual uniform Green expectation bound to the local Poisson
criterion. Every compact-input physical scalar measure is absolutely
continuous near each real parameter with distinct Floquet roots.
[`L2FloquetRepeatedRoots.lean`](../NLS/ZakharovShabat/L2FloquetRepeatedRoots.lean)
proves that the physical monodromy has distinct roots at all nonreal
parameters. Analyticity of its discriminant squared minus four, with a
nonzero value at i, makes the complex and real repeated-root sets countable.

[`RealLocalAbsoluteContinuity.lean`](../NLS/FunctionalAnalysis/RealLocalAbsoluteContinuity.lean)
combines local interval absolute continuity off a measure-null exceptional
set into absolute continuity on the whole real line.
[`L2WholeLineCompactSpectralAC.lean`](../NLS/ZakharovShabat/L2WholeLineCompactSpectralAC.lean)
uses actual atomlessness to remove the countable exceptional set. The
constructed physical spectral measure of every compactly supported input,
including every original smooth compact test vector, is absolutely continuous.
No additional physical resolvent bound is assumed.

Extension from this dense test domain to all Hilbert vectors remains
unfinished in this milestone. Exact2014 and G2 remain separate source questions.

## Pure absolute continuity of the original physical operator

[`VectorSpectralMeasureParallelogram.lean`](../NLS/FunctionalAnalysis/VectorSpectralMeasureParallelogram.lean)
proves regularity and the parallelogram identity for the actual CFC/Riesz
vector measures. Consequently the measure of a vector sum is bounded by
twice the sum of the two vector measures.
[`QuadraticMeasureDenseAC.lean`](../NLS/FunctionalAnalysis/QuadraticMeasureDenseAC.lean)
proves that finite quadratic vector measures with squared-norm total mass
inherit absolute continuity from a dense range. For a null set, its mass
is bounded by twice the squared norm of any approximation error.

[`L2WholeLinePureAbsoluteContinuity.lean`](../NLS/ZakharovShabat/L2WholeLinePureAbsoluteContinuity.lean)
transports the actual quadratic measure bound through the inverse Cayley
coordinate and applies the original smooth compact test-domain density.
For every real-type physical L2 potential and every whole-line Hilbert
vector, the constructed real scalar spectral measure is absolutely
continuous with respect to real Lebesgue measure. Every Lebesgue-null set
therefore has zero scalar spectral mass; this excludes both atoms and
singular continuous mass.

This completes the pure absolute-continuity assertion on printed p.17
for the original self-adjoint physical closure. The measure is the actual
CFC/Riesz measure with its proved original resolvent integral, and the
proof uses the actual Green kernel and the analytic countable exceptional
set. Together with the separately proved equality of the independently
defined spectrum and the full closed Floquet bands, this establishes the
physical spectral overview. It does not assert completion of the entire
dissertation. Exact2014 and G2 remain separate source questions.

## The complete source whole-line statement and all-index eigenfunction parity

[`SourceWholeLineSpectralOverview.lean`](../NLS/ZakharovShabat/SourceWholeLineSpectralOverview.lean)
provides a single theorem for the original real Hilbert source: the actual
physical closure is self-adjoint, its independently defined spectrum is
exactly the complement of the union of the original canonical open gaps,
and every actual scalar spectral measure is absolutely continuous with
respect to real Lebesgue measure. The statement retains all endpoints and
collapsed gaps and the actual inverse-Cayley measure construction.

The adjacent p.17 assertion about every endpoint eigenfunction is now
explicit at every canonical index.
[`DiscriminantRootParity.lean`](../NLS/ZakharovShabat/DiscriminantRootParity.lean)
uses the actual discriminant level and the parity decomposition to show
that the entire generalized root space has its signed-index parity.
This applies at both canonical real endpoints, including central indices.
[`SourceCanonicalEigenvectorParity.lean`](../NLS/ZakharovShabat/SourceCanonicalEigenvectorParity.lean)
transports this result to every eigenvector in the original component-sum
one-derivative source domain. Its actual continuous Fourier components are
one-periodic at even indices and one-antiperiodic at odd indices, for every
finite p>1 real source. There is no high-frequency cutoff in these results.

The initial band-criterion section above is a historical checkpoint;
its operator and spectral-measure obligations have now been discharged.
Remaining source comparisons, exact2014 and G2 are separate from these
page17 results. This is not a full-dissertation completeness certificate.

## Periodic self-adjointness in the original Hilbert and physical spaces

The opening p.17 real-type self-adjointness claim and the p.18 converse
now have an exact adjoint formulation. The periodic realization is the
period-two operator specified on p.18, retaining the original one-derivative
domain and the sum of both component coefficient energies.

[`ConjugatePencilSelfAdjoint.lean`](../NLS/FunctionalAnalysis/ConjugatePencilSelfAdjoint.lean)
proves that a dense symmetric operator equals its actual Hilbert adjoint
when its pencils at a pair of conjugate parameters are onto. The proof
establishes equality of domains through the adjoint pencil kernel.
[`SourceUnboundedOperator.lean`](../NLS/ZakharovShabat/SourceUnboundedOperator.lean)
constructs the original source operator as a partial linear map whose
domain is exactly the included one-derivative space, and proves density.
[`SourcePeriodicSelfAdjoint.lean`](../NLS/ZakharovShabat/SourcePeriodicSelfAdjoint.lean)
identifies coefficient duality with the actual source Hilbert inner product.
The existing nonreal resolvents at i and -i then prove self-adjointness.

[`PhysicalPeriodicSelfAdjoint.lean`](../NLS/ZakharovShabat/PhysicalPeriodicSelfAdjoint.lean)
uses the original Fourier isometry to realize the full domain in physical
period-two L2. Its operator equals the signed physical differential
expression almost everywhere for every L2 potential. The actual physical
operator is self-adjoint at real-type sources, with no assumed adjoint
domain or smoothness of the potential.
[`PeriodicSelfAdjointRealType.lean`](../NLS/ZakharovShabat/PeriodicSelfAdjointRealType.lean)
proves the converse by testing symmetry on two original Fourier modes.
Both the coefficient and physical operators are self-adjoint if and only
if the potential has real type. The equivalence also retains the original
period-one potential embedding, so non-real-type original potentials
give non-self-adjoint physical operators.

This is distinct from merely proving that the periodic eigenvalues are real.
The existing whole-line results are unchanged. The remaining dissertation
source audit, exact2014 comparison and G2 norm qualification remain separate.

## Separate periodic and antiperiodic adjoint domains

The two signs in the p.17 boundary shorthand now have separate densely
defined operators. Their domains are never combined as a union.
[`SourceParityOperatorDomain.lean`](../NLS/ZakharovShabat/SourceParityOperatorDomain.lean)
restricts the original one-derivative inclusion to each closed Fourier parity
space and proves injectivity and density at every finite Banach exponent.
[`SourceParityUnboundedOperator.lean`](../NLS/ZakharovShabat/SourceParityUnboundedOperator.lean)
constructs the actual partial operator and its spectral pencil on each
space. The full source inverse preserves the precise restricted domain
and gives both inverse identities for an even potential.

[`SourceParitySelfAdjoint.lean`](../NLS/ZakharovShabat/SourceParitySelfAdjoint.lean)
proves equality with the Hilbert adjoint separately on each parity space
for a real-type Hilbert potential. The proof uses the inherited inner
product, domain density and the restricted inverses at i and -i.
The original continuous physical domain representatives have endpoints
f(1)=f(0) in the even sector and f(1)=-f(0) in the odd sector.
[`PhysicalParitySelfAdjoint.lean`](../NLS/ZakharovShabat/PhysicalParitySelfAdjoint.lean)
transports each exact domain by the original Fourier isometry into the
physical period-two L2 parity subspace. The resulting self-adjoint operator
agrees almost everywhere with the original signed differential expression.

[`ParitySelfAdjointRealType.lean`](../NLS/ZakharovShabat/ParitySelfAdjointRealType.lean)
proves the converse separately for either sector. Testing symmetry on
two modes of that sector recovers every even potential coefficient; the
odd coefficients vanish by the explicit potential hypothesis. Thus each
source or physical parity operator is self-adjoint if and only if the
potential has real type, including the original period-one embedding.

The ambient physical spaces here are the Fourier parity subspaces of the
period-two L2 realization. This package proves their exact adjoint domains,
physical differential expressions and unit-interval endpoint conditions.
The full classical unit-interval package below completes the standalone
unit-interval L2/H1 domain identification for both signs. The remaining
source audit, exact2014 and G2 are recorded separately.

## Full classical unit-interval periodic and antiperiodic operators

The full classical domain comparison is now proved on ordinary unit-interval
L2, for both signs in the printed pp.17-18 boundary shorthand.
[`IntervalH1Reflection.lean`](../NLS/Fourier/IntervalH1Reflection.lean)
proves reflection for every absolutely continuous interval function whose
actual derivative is square integrable.
[`SignedIntervalH1Extension.lean`](../NLS/Fourier/SignedIntervalH1Extension.lean)
constructs the signed period-two extension and its actual normalized Fourier
coefficients. Only interval H1 regularity and the matching endpoint condition
are assumed; reconstruction includes the endpoints and the join.

[`ClassicalParityDomain.lean`](../NLS/ZakharovShabat/ClassicalParityDomain.lean)
identifies the full classical signed H1 domain with the original weighted
Fourier parity domain in both directions. Extension and restriction are
inverse on the closed unit interval.
[`ParityIntervalL2Extension.lean`](../NLS/ZakharovShabat/ParityIntervalL2Extension.lean)
extends arbitrary unit-interval L2 data into either original coefficient
parity space, preserves the original Hilbert norm, and proves that physical
restriction is a right inverse.
[`ParityIntervalL2Equiv.lean`](../NLS/ZakharovShabat/ParityIntervalL2Equiv.lean)
bundles actual physical restriction as a surjective linear isometry onto
ordinary unit-interval L2.

[`UnitParityOperatorDomain.lean`](../NLS/ZakharovShabat/UnitParityOperatorDomain.lean)
proves density and identifies the included operator domain exactly with the
L2 classes admitting a full classical H1 representative with the chosen
signed endpoint condition.
[`UnitParitySelfAdjoint.lean`](../NLS/ZakharovShabat/UnitParitySelfAdjoint.lean)
constructs the actual physical operator for any unit-interval L2 potential.
It agrees almost everywhere with the original differential expression on
every classical domain representative. Equality with its actual Hilbert
adjoint, including the domain, is equivalent to the potential being of real
type. The periodic endpoint f(1)=f(0) and antiperiodic endpoint f(1)=-f(0)
are explicit specializations, each defining its own operator.

This completes the unit-interval L2/H1 comparison left open in the preceding
parity package. Full dissertation semantic completion, exact2014 and G2
remain separate questions.

## Actual classical signed spectra and their period-two union

The spectrum comparison on printed pp.17-18 and p.29 is now proved using
the full classical unit-interval domains and independently defined
bounded-inverse resolvent sets.
[`SourceParityResolventSet.lean`](../NLS/ZakharovShabat/SourceParityResolventSet.lean)
defines each sector resolvent using its own pencil bijectivity. Its inverse
exists in the original weighted norm at every sector resolvent parameter,
including parameters singular in the opposite sector. For every finite
Banach exponent, the full period-two pencil is invertible exactly when
both separate parity pencils are invertible.

[`SourceParityCompactResolvent.lean`](../NLS/ZakharovShabat/SourceParityCompactResolvent.lean)
proves compactness of every complete sector inverse and uses the Fredholm
alternative to identify its spectral points with nonzero original-domain
kernel vectors.
[`SourceParitySpectralGeometry.lean`](../NLS/ZakharovShabat/SourceParitySpectralGeometry.lean)
proves openness of the resolvent, closedness and discreteness of the
spectrum, finite bounded portions, and equivalence with positivity of
the original algebraic parity multiplicity.

[`UnitParityResolvent.lean`](../NLS/ZakharovShabat/UnitParityResolvent.lean)
defines physical resolvent membership by an actual bounded two-sided
inverse on the included full classical domain. Exact pencil intertwining
identifies all admissible parameters and transports the compact inverse.
[`ClassicalSignedSpectrum.lean`](../NLS/ZakharovShabat/ClassicalSignedSpectrum.lean)
proves, for every actual physical L2 potential, that the union of the
periodic and antiperiodic spectra is precisely the original period-two
spectrum. Each signed spectrum retains its closedness, discreteness,
finite bounded portions and original parity multiplicity characterization.
At zero potential, zero belongs to the physical odd resolvent and the
physical even spectrum, so the separate resolvent sets are distinguished.

[`ClassicalSignedEigenvalues.lean`](../NLS/ZakharovShabat/ClassicalSignedEigenvalues.lean)
identifies the independently defined physical spectrum with the literal
differential-equation eigenvalues on all full classical signed H1 inputs.
No continuous or residual signed spectrum remains. The two signs each
retain their own linear operator domain; their spectra are combined by union.
[`PhysicalPeriodicSpectrum.lean`](../NLS/ZakharovShabat/PhysicalPeriodicSpectrum.lean)
defines the spectrum of the actual physical period-two partial operator
by bounded invertibility on its full domain. Its inverse is compact and
is the conjugate of the original source inverse. Thus the final union
equality holds between independently defined spectra of actual physical
operators on both sides, and also with the literal signed ODE eigenvalue sets.
Full dissertation semantic completion, exact2014 and G2 remain separate.

## Physical endpoint labels enumerate the actual signed spectra

The endpoint sequences in the opening spectral overview on printed p.17
are now connected explicitly to the actual physical operator spectra.
[`ClassicalSignedDiscriminant.lean`](../NLS/ZakharovShabat/ClassicalSignedDiscriminant.lean)
proves, for every complex physical L2 potential, that the independently
defined periodic spectrum is exactly the physical monodromy trace level
two, and the antiperiodic spectrum is exactly level minus two. Consequently
the two spectra are disjoint. These same trace criteria characterize
nonzero solutions of the original ODE on the full classical signed H1
domains. The independently defined physical period-two spectrum is
exactly the zero set of the physical discriminant squared minus four.
The existing intrinsic physical endpoint labels therefore exhaust that
actual operator spectrum, retaining their lexicographic ordering, l2
displacements, and physical analytic zero-order specification.

[`ClassicalSignedEndpointLabels.lean`](../NLS/ZakharovShabat/ClassicalSignedEndpointLabels.lean)
proves that real-type physical potentials give real endpoint labels,
non-strict order within each pair, and strict separation of consecutive
pairs. Every endpoint has its exact index trace level, including central
indices and collapsed gaps. Even indices exhaust the actual periodic
spectrum and odd indices exhaust the actual antiperiodic spectrum.

The comparison of full physical Jordan-chain dimensions with the existing
algebraic multiplicities remains separate. Full dissertation semantic
completion, exact2014 and G2 remain separate questions.

## Actual physical root chains and algebraic multiplicities

The multiplicity of the actual physical period-two operator is now defined
as the dimension of its full generalized eigenspace. This implements the
period-two multiplicity aspect of the opening spectral enumeration on p.17.
[`LinearPMapRootSpace.lean`](../NLS/FunctionalAnalysis/LinearPMapRootSpace.lean)
defines root chains by repeatedly applying the actual partial-operator
pencil, requiring its original domain at every step. It proves transport
of every finite level and the full increasing union under exact base and
domain isomorphisms. Full physical root vectors lie in the actual domain.

[`PhysicalPeriodicRootSpaces.lean`](../NLS/ZakharovShabat/PhysicalPeriodicRootSpaces.lean)
defines these chains for the actual physical period-two operator. Exact
Fourier synthesis and domain equivalence identify every finite level and
the full generalized eigenspace with the original coefficient root space.
The physical chains stabilize and their full space is finite dimensional
for every complex L2 potential, without a real-type assumption.

[`PhysicalPeriodicMultiplicity.lean`](../NLS/ZakharovShabat/PhysicalPeriodicMultiplicity.lean)
defines physical algebraic multiplicity from that actual full-space
dimension and proves equality with the existing coefficient multiplicity.
Positivity is equivalent to the independently defined physical spectrum;
vanishing is equivalent to actual bounded invertibility. The intrinsic
physical endpoint labels count precisely this dimension, and the physical
discriminant squared minus four has exactly this analytic zero order.
Every free signed lattice point has physical algebraic multiplicity two.

The signed physical Jordan-chain comparison is completed in the next subsection.
Full dissertation semantic completion, exact2014 and G2 remain separate.

## Actual classical signed root chains and algebraic multiplicities

[`SourceParityRootChains.lean`](../NLS/ZakharovShabat/SourceParityRootChains.lean)
identifies each separate source parity chain with the corresponding parity
part of the original full root chain. This holds at every finite level and
for the full generalized eigenspace; the latter is finite dimensional and
the chain sequence stabilizes.
[`ClassicalSignedRootSpaces.lean`](../NLS/ZakharovShabat/ClassicalSignedRootSpaces.lean)
defines root chains independently from the actual classical periodic and
antiperiodic partial operators on unit-interval L2. Exact domain and base
isomorphisms transport every level and the full union. Every intermediate
vector satisfies the original full classical H1 domain condition.

[`ClassicalSignedMultiplicity.lean`](../NLS/ZakharovShabat/ClassicalSignedMultiplicity.lean)
defines signed algebraic multiplicity as the dimension of the actual full
physical generalized eigenspace. It proves equality with the original
parity root dimension, positivity exactly on the actual signed spectrum,
and vanishing exactly on the actual resolvent set. The full physical
period-two multiplicity is the sum of the two signed multiplicities;
at either signed spectral point it equals that sign's multiplicity.
These assertions hold for arbitrary complex physical L2 potentials.
The free lattice point has multiplicity two in its parity and zero in
the other.

[`ClassicalSignedEndpointMultiplicity.lean`](../NLS/ZakharovShabat/ClassicalSignedEndpointMultiplicity.lean)
proves that for real-type physical potentials, the even endpoint pairs
count the full actual periodic algebraic multiplicity and the odd pairs
count the antiperiodic multiplicity. This includes central indices and
collapsed endpoint pairs. It completes the actual signed multiplicity
comparison underlying the real-type enumeration on printed p.17.

Even/odd indices are not asserted for all complex potentials. The separate
globally sorted signed complex eigenvalue lists and their source comparison
are constructed in the next subsection. Full dissertation semantic completion, exact2014 and G2
remain separate questions.

## Independent ordered physical signed eigenvalue lists

[`ClassicalSignedCharacteristicOrders.lean`](../NLS/ZakharovShabat/ClassicalSignedCharacteristicOrders.lean)
identifies both normalized source parity products with the actual physical
monodromy trace minus or plus two. Their analytic zero orders are exactly
the independently defined actual classical signed Jordan-chain dimensions
for every complex physical L2 potential.

[`CentralParityOrdering.lean`](../NLS/ZakharovShabat/CentralParityOrdering.lean)
sorts each finite central parity multiset on its own indices, retaining
all repetitions.
[`OrderedPeriodicParityPairs.lean`](../NLS/ZakharovShabat/OrderedPeriodicParityPairs.lean)
sorts the distant pairs and joins the lists using their real-part separation.
The complete source data retain every multiplicity, displacement and
quantitative pair bound. Order is asserted within each parity; complex
central roots of different signs need not occur in their index order.

[`ClassicalSignedPairCounts.lean`](../NLS/ZakharovShabat/ClassicalSignedPairCounts.lean)
transports these complete complex parity lists to the actual physical
signed spectra and multiplicities. Reindexing by 2n or 2n+1 preserves each
sign's exact full Jordan-chain count.
[`PhysicalSignedEnumeration.lean`](../NLS/ZakharovShabat/PhysicalSignedEnumeration.lean)
specifies and constructs the two separate physical lists using their
actual classical spectra, algebraic multiplicities, global lexicographic
order and l2 displacement from the corresponding signed free lattice.
[`PhysicalSignedEnumerationUniqueness.lean`](../NLS/ZakharovShabat/PhysicalSignedEnumerationUniqueness.lean)
proves that these independent conditions determine both lists uniquely,
including at repeated eigenvalues.

[`PhysicalSignedEnumerationComparison.lean`](../NLS/ZakharovShabat/PhysicalSignedEnumerationComparison.lean)
proves equality with every complete source construction sorted within its
parity. For arbitrary complex potentials, the physical signed lists equal
the combined physical endpoints at the printed even/odd indices outside
a finite central block. For real-type potentials, equality holds at every
index, including central and collapsed pairs. These are the separate-list
claims in the opening discussion of Section 7 and the real enumeration
on printed p.17.

The package below strengthens this pointwise cutoff to one common
physical neighborhood and proves the literal circular signed counts.
The remaining semantic source audit, exact2014 and G2 remain separate.
No continuous choice of complex root branches is asserted.

## Locally uniform physical signed counts on the literal circle

[`ClassicalSignedCircleCounts.lean`](../NLS/ZakharovShabat/ClassicalSignedCircleCounts.lean)
defines finite disk intersections of the actual classical signed spectra.
The sum of their full physical Jordan-chain dimensions agrees with the
original coefficient parity count on that same disk.

[`PhysicalSignedUniformCircleCounts.lean`](../NLS/ZakharovShabat/PhysicalSignedUniformCircleCounts.lean)
pulls the uniform coefficient neighborhoods back through the exact physical
L2 Fourier isometry and period-one map. On one open convex neighborhood,
every sufficiently large circle of radius (2N+1/2)pi avoids both signed
spectra and contains exactly 4N+2 periodic and 4N antiperiodic eigenvalues,
counted with their actual algebraic multiplicities. The existing spectral
circle/rectangle equality proves the circular selection; the statement
retains the literal circle in Section 7, printed p.47.

[`PhysicalSignedUniformEnumeration.lean`](../NLS/ZakharovShabat/PhysicalSignedUniformEnumeration.lean)
compares complete ordered endpoint pairs at a common construction cutoff.
The independent signed physical lists equal the combined physical labels
at indices 2n and 2n+1 whenever |n| exceeds one locally uniform cutoff.
This does not require continuity of individual complex roots or a local
bound on an arbitrarily chosen canonical cutoff.

[`PhysicalSignedSpectralOverview.lean`](../NLS/ZakharovShabat/PhysicalSignedSpectralOverview.lean)
combines the exact circular counts, simultaneous boundary exclusion,
independent-list equality and distant parity membership on one common
physical L2 neighborhood. Both signs and every larger cutoff work there.
The neighborhood is open and convex and contains the given potential
and zero. These statements hold for arbitrary complex L2 potentials.

This completes the locally uniform signed-counting and distant-parity
claims in the opening of Section 7. The remaining semantic source audit,
exact2014 and G2 qualifications are unchanged; whole-dissertation
completion is not asserted.

## An explicit nonreal eigenvalue of the actual physical operator

The p.18 statement that the spectrum can be nonreal for complex potentials
now has an explicit witness in the actual physical realization.
[`PhysicalConstantPeriodicSpectrum.lean`](../NLS/ZakharovShabat/PhysicalConstantPeriodicSpectrum.lean)
proves that the physical representative of the source constant potential
is the constant pair (a,b) almost everywhere. For a nonzero first amplitude,
the actual period-two bounded-inverse spectrum, and the union of the two
actual signed spectra, satisfy exactly z^2=(pi*k)^2+a*b for some integer k.

For the concrete physical potential (1,-1), i belongs to that actual
spectrum and to the union of the full classical signed ODE eigenvalue
sets. Its imaginary part is nonzero. The potential fails the physical
real-type condition, and each of its two signed realizations fails
self-adjointness. Thus the general complex case really admits nonreal
physical eigenvalues. No assertion that every non-real-type potential
has a nonreal spectrum is made.

This is a source-specific witness and exact constant-potential comparison.
The remaining semantic source audit, exact2014 and G2 qualifications
remain separate.

## Physical midpoint and gap asymptotics, including nonreal gaps

[`PhysicalPeriodicMidpointGap.lean`](../NLS/ZakharovShabat/PhysicalPeriodicMidpointGap.lean)
defines the midpoint and gap directly from the independently specified
physical periodic endpoint labels. Their exact comparison with the
original source sequences is proved. For every complex physical L2
potential, the midpoint displacement from n*pi and the full gap sequence
belong to l2, including the central indices.

The local uniformity in Corollary 1.3 is retained in the physical L2
topology: for each positive tolerance, one open neighborhood gives a
common norm bound for both sequences and one cutoff beyond which both
l2 truncation errors are below that tolerance at every larger cutoff. This statement
requires neither real type nor continuous individual complex labels.
A gap vanishes exactly when its two physical endpoint labels coincide.

[`PhysicalNonrealGap.lean`](../NLS/ZakharovShabat/PhysicalNonrealGap.lean)
gives an explicit form of the p.18 complex-gap assertion. Every physical
L2 neighborhood of zero contains a constant potential (r,-r), with r>0,
whose actual central endpoints are exactly (-i*r,i*r). Its ordered gap
is 2*i*r, with nonzero imaginary part, and its midpoint is zero. The proof
uses actual isolated spectral pairs and their lexicographic ordering.

[`PhysicalNonrealMidpoint.lean`](../NLS/ZakharovShabat/PhysicalNonrealMidpoint.lean)
adds an explicit nonreal midpoint for the constant potential (1,i).
Every actual spectral point satisfies 2*Re(z)*Im(z)=1. Square-summable
endpoint displacements place a pair in the right half-plane, where both
imaginary parts are positive; hence its actual midpoint is nonreal.

The remaining semantic source audit, exact2014 comparison and G2 norm
qualification remain separate.

## Real AKNS coordinates and the original classical complexification

The printed p.19 real-coordinate assertion is explicit in
[`AKNSPotentialReality.lean`](../NLS/ZakharovShabat/AKNSPotentialReality.lean).
The potential map (q+i*p,q-i*p) has its exact unnormalized inverse.
A conjugate pair corresponds exactly to real q and p, pointwise and almost
everywhere. Every real-type physical L2 potential is reconstructed from
two real L2 functions. This keeps the potential coordinates distinct from
the normalized unitary vector map T.

[`AKNSConjugation.lean`](../NLS/ZakharovShabat/AKNSConjugation.lean)
proves that complex conjugation preserves the full interval H1 class and
each original AKNS endpoint domain. The actual derivative expression
commutes with conjugation for almost-everywhere real coefficients. Real
coefficient functions and real input functions have real operator outputs.

[`AKNSComplexification.lean`](../NLS/ZakharovShabat/AKNSComplexification.lean)
shows that the real and imaginary parts of any original domain function
remain in the same endpoint domain and reconstruct that function exactly.
The actual physical operator decomposes into their two actions, almost
everywhere; for real potentials both component actions have real outputs.
Together with the existing physical unitary conjugation, this establishes
the real complexification statement on the full classical domains.
No global smooth extension or representative condition at null sets is
imposed on the L2 potential.

The page29 potential-normalization correction remains in force. The
remaining semantic source audit, exact2014 and G2 remain separate.
