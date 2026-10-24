# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–21, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

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

## Whole-line Floquet assertion: band criterion proved, operator theorem pending

The unnumbered paragraph on printed p.17 identifies the spectrum of the
periodically extended real L2 operator on the real line with the complement
of the open periodic gaps and says that its spectrum is absolutely
continuous. This assertion requires additional whole-line operator and
spectral-measure foundations. The existing closed coefficient operator
and physical periodic realization do not discharge that requirement.

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

Remaining work is to construct the densely defined operator on
L2(R;C^2), prove self-adjointness and identify its resolvent and spectrum,
and prove pure absolute continuity of its spectral measures. No operator
spectrum is defined by simply declaring it to be the band set. The new
results establish the monodromy criterion only.

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
