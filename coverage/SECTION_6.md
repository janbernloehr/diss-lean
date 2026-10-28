# Section 6: asymptotic behavior of the eigenvalues

This audit starts with Proposition 6.1 on printed page 35. Its source domain
is the full period-two coefficient space, with the original component-sum
norm. The existing period-one embeddings do not by themselves establish this
statement for arbitrary period-two input.

## Original P/Q spans, topology and complementary equation

The original P/Q decomposition now uses the literal two-mode resonant span
and the closed span of all other signed Fourier modes. Their ranges agree
with the actual projections and form a topological direct sum for every
finite Banach exponent, including p=1.

The original-domain Q equation directly gives (Id-T)Phi(v)=T*Phi(u).
Away from the free lattice, the original free resolvent on Q agrees with
the weighted complementary inverse. Its base-space bound is uniform over
the full closed strip; its derivative-domain bound may depend on z.

Seven further passages, S6-009 through S6-015, are reconciled. The review
retains the exact opposite shifts, Lemma 6.4's constant two at p=2 and the
proved constant one at p=1. No new counterexample is added.

[SourcePQTopology.lean](../NLS/ZakharovShabat/SourcePQTopology.lean)
identifies the literal spans, projection ranges, dimension and topological
direct sum in the original weighted pair norm.
[SourceQTransformation.lean](../NLS/ZakharovShabat/SourceQTransformation.lean)
derives the original-domain transformed Q equation and identifies its free
inverse with the original resolvent away from the free lattice.

Validation: `./scripts/check.sh` passes with 8,496 build jobs, 7,561
public examples and a transitive axiom audit of 44,182 NLS declarations.
The 21 inherited warnings are unchanged; the two new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The ordered ledger now has 39 reviewed groups: 30 matched, eight corrected
and one interpreted. Eight groups remain pending, S6-016 through S6-023:
the detailed Lemma 6.4 proof and the square/inverse estimates in Lemma 6.5.
The source-wide assertion inventory, exact cited 2014 Birkhoff construction
and Appendix G.2 norm interpretation remain unfinished.

Section6PQAssertionsSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records these seven passages.
Reconstruction uses the established inverse and actual domain-valued
solution; the proof does not cancel the potential map to infer a converse.

## Initial labels, source weights and Sobolev normalization

The initial eight Section 6 passages are now reconciled. Complete actual
periodic labels have displacement less than π/4 outside a common local cutoff
for every finite Banach exponent, including p=1. The central root multiset,
distant algebraic multiplicities and exact source-spectrum exhaustion are retained.

The source Sobolev normalization (1+|nπ|)^s is now explicitly equivalent to
(1+|n|)^s without changing Fourier coefficients. For s>=0, the original
pair norms have factors 1 and π^s, with the exact full signed power-sum formula.

The review also reconciles canonical local asymptotics, reflection, all four
boundary sequences, midpoint and gap asymptotics, and the source weight class.
Propositions 6.1 and 6.3 retain their proved corrected quantitative budgets,
including the additive leading Fourier tail. No new counterexample is added.

[SourcePeriodicBoundedLabels.lean](../NLS/ZakharovShabat/SourcePeriodicBoundedLabels.lean)
supplies complete bounded labels without requiring p>1.
[WeightComparison.lean](../NLS/SequenceSpaces/WeightComparison.lean) supplies
coefficient-preserving continuous equivalences for comparable weights.
[PiSobolevEquivalence.lean](../NLS/SequenceSpaces/PiSobolevEquivalence.lean)
gives the explicit source Sobolev norm comparisons and exact Fourier formula.

Validation: `./scripts/check.sh` passes with 8,494 build jobs, 7,558
public examples and a transitive axiom audit of 44,165 NLS declarations.
The 21 inherited warnings are unchanged; the three new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The ordered ledger now has 32 reviewed groups: 23 matched, eight corrected
and one interpreted. Fifteen groups remain pending, S6-009 through S6-023.
Continue with the free modes and P/Q decomposition. The source-wide assertion
inventory, exact cited 2014 Birkhoff construction and Appendix G.2 norm
interpretation remain unfinished.

Section6InitialAssertionsSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records S6-001 through S6-008.
The p=1 result asserts bounded displacement; summable canonical displacement
remains a 1<p<infinity result. The boundary comparison retains physical
finite-input/L2 identification and bounded completion for general rough inputs.

Earlier milestone entries below retain their historical validation and limitations.

## The final gap sum with a corrected constant

The final weighted gap-sum inference on p.44 is now proved with the valid
constant C_p = 2^(3*p-2). The sum of actual canonical gap powers is at most
C_p times the two leading Fourier-coefficient sums plus the two actual
whole-strip remainder sums. Both grouped coefficient sums and the gap sum
converge; all signed indices and the cutoff boundary are retained.

For every 1<p<infinity and every source weight, one open convex neighborhood
containing the input and zero supplies a cutoff valid for every larger cutoff.
The canonical gap comes from the original period-two spectral pair, including
multiplicities. Lemma 6.8 then supplies the corrected budget in the original
weighted pair norm, retaining the additive leading tail and floor(N/2).

The constant is deliberately nonoptimal. This step supplies the corrected
estimate; it does not assert necessity of this constant or add a refutation
of the printed 1/2^p factor.

[SourceGapCoefficientMajorant.lean](../NLS/ZakharovShabat/SourceGapCoefficientMajorant.lean)
defines the literal grouped leading and remainder tails and the canonical gap
tail. Its four-term estimate includes p=1 when the counted pair and strip bounds
are supplied. [SourceGapSumCorrected.lean](../NLS/ZakharovShabat/SourceGapSumCorrected.lean)
proves summability, the common-neighborhood comparison, its Lemma 6.8 budget,
and the reciprocal-constant form on an original unweighted neighborhood.

Validation: `./scripts/check.sh` passes with 8,491 build jobs, 7,555
public examples and a transitive axiom audit of 44,118 NLS declarations.
The 21 inherited warnings are unchanged; the two new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

S6-047 is classified as corrected. The ordered ledger now has twenty-four
reviewed groups (seventeen matched, six corrected, one interpreted) and
twenty-three pending groups, S6-001 through S6-023. Reconcile those earlier
groups next, then continue through the dissertation. The source-wide assertion
inventory, exact cited 2014 Birkhoff construction and Appendix G.2 norm
interpretation remain unfinished.

Section6CorrectedGapSumSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records this correction.
The earlier milestones below describe their evidence and remaining work at
the time; the corrected estimate above supersedes their pending-sum status.

## The actual determinant near its moving diagonal center

The original three-mode family now has actual coefficient and determinant
limits at its moving diagonal center. For each fixed n>0 and complex t, the
determinant at center(s)+s^3*t divided by s^6 tends to t^2-(2*r)^2, with
r=1/(pi*n)^2. Both original off-diagonal coefficients divided by s^3 tend
to 2*r at any moving strip parameter tending to pi*n.

The original diagonal has a quadratic norm bound for every finite Banach
exponent, including p=1. Cauchy's estimate gives a derivative bound that
vanishes with the amplitude. The same actual center solves the diagonal
equation, is eventually real and has displacement O(s^2) from pi*n.

[SourceCubicMovingCoefficient.lean](../NLS/ZakharovShabat/SourceCubicMovingCoefficient.lean)
controls the normalized actual remainder and both original coefficients along
moving spectral parameters. [SourceDiagonalSmallBound.lean](../NLS/ZakharovShabat/SourceDiagonalSmallBound.lean)
proves the quadratic original-norm bound and general Cauchy estimates.
[SourceCubicSmallDiagonal.lean](../NLS/ZakharovShabat/SourceCubicSmallDiagonal.lean)
specializes these bounds to the family on whole strips and refined disks.
[SourceCubicMovingCenter.lean](../NLS/ZakharovShabat/SourceCubicMovingCenter.lean)
uses the existing actual center, its equation and uniqueness to prove the
sharp displacement, convergence and eventual reality.
[SourceCubicMovingDeterminant.lean](../NLS/ZakharovShabat/SourceCubicMovingDeterminant.lean)
then proves the normalized residual and determinant limits for every fixed
complex cubic displacement. This is still a pointwise limit in t, not a
claim of uniform convergence on a contour or a completed root-selection proof.

Validation: `./scripts/check.sh` passes with 8,489 build jobs, 7,552
public examples and a transitive axiom audit of 44,099 NLS declarations.
The 21 inherited warnings are unchanged; the five new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The actual counted roots still need localization and identification with the
original canonical periodic pair. The final p.44 inequality remains unresolved;
S6-047 stays pending and the ordered ledger remains at twenty-three reviewed
and twenty-four pending groups. The broader completion qualifications remain.

The partial Section6MovingCenterSourceComparison-2026-10-28 record is in the
[source-review index](source-review-index.json). The original period-two
potential and the locally uniform cutoff requirement remain unchanged.

## The exact coefficient-side limit of the final p.44 sum

[ResonantCubicPerturbation.lean](../NLS/ZakharovShabat/ResonantCubicPerturbation.lean)
expands the actual cubic term of s*A+s^3*B into degrees 3,5,7,9 and bounds
its change by O(norm(s)^5) on whole closed strips.
[ResonantCubicSupport.lean](../NLS/ZakharovShabat/ResonantCubicSupport.lean)
proves that both cubic directions have outer support in [-n,2n] when the
physical inputs have support in [-2n,0] and [0,2n].
[ResonantCubicPerturbationTail.lean](../NLS/ZakharovShabat/ResonantCubicPerturbationTail.lean)
then gives summability and the vanishing normalized infinite perturbation tail.
This finite support concerns the cubic term, not the full coefficient remainder.

[ResonantCubicBackground.lean](../NLS/ZakharovShabat/ResonantCubicBackground.lean)
connects the scaled background and controls differences of actual strip suprema.
[SourceCubicCoefficientError.lean](../NLS/ZakharovShabat/SourceCubicCoefficientError.lean)
and [its tail estimates](../NLS/ZakharovShabat/SourceCubicCoefficientErrorTail.lean)
combine the cubic perturbation with the higher Neumann error in original
period-two coordinates. A [fourth-power concentration theorem](../NLS/SequenceSpaces/FourthPowerSingleLimit.lean)
proves convergence of the entire sum after establishing summability.

[SourceCubicCoefficientLimit.lean](../NLS/ZakharovShabat/SourceCubicCoefficientLimit.lean)
gives the limit C^4 for each original remainder-supremum tail divided by s^12,
where C=1/[pi*(n-1/2)]^2. Each leading Fourier tail has normalized value r^4,
where r=1/(pi*n)^2. These statements use p=4, unit weight, fixed n>0 and
cutoff N=abs(n). [SourceCubicPrintedSumLimit.lean](../NLS/ZakharovShabat/SourceCubicPrintedSumLimit.lean)
identifies the literal grouped source sum using proved summability. Its exact
normalized limit is 2*r^4+2*C^4, strictly below 16*r^4 for every n>=3.

Validation: `./scripts/check.sh` passes with 8,484 build jobs, 7,548
public examples and a transitive axiom audit of 44,034 NLS declarations.
The 21 inherited warnings are unchanged; the nine new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The actual counted-root gap asymptotics remain open. Neither a proof nor a
counterexample to the final 1/2^p weighted gap inequality follows yet.
S6-047 remains pending; no additional ordered group is classified as reviewed.
The partial Section6CubicPerturbationSourceComparison-2026-10-28 record is in
the [source-review index](source-review-index.json).

## Earlier supporting cubic estimates for the final p.44 sum

[ResonantTwoModeCubic.lean](../NLS/ZakharovShabat/ResonantTwoModeCubic.lean)
computes both actual cubic operator terms for a background with modes 0 and
plus/minus n. Among all signed indices abs(m)>=n>0, only m=n survives, with
value s^3/z^2. Its full closed-strip supremum is norm(s)^3/[pi*(n-1/2)]^2,
attained at the left real boundary. The scalar strict comparison needed by
the proposed limiting argument holds for every n>=3.

[ResonantCubicRemainder.lean](../NLS/ZakharovShabat/ResonantCubicRemainder.lean)
retains the small shifted-square factor in the actual error after cubic
subtraction. [ResonantCubicTail.lean](../NLS/ZakharovShabat/ResonantCubicTail.lean)
proves boundedness on whole strips, summability of the signed p-power tail
and the bound K_p*norm(phi)^(5p), for finite p>1 and every cutoff N>=1 under
the explicit half-contraction smallness condition. This uses genuine suprema
and infinite sums.

[ResonantCubicFourthTail.lean](../NLS/ZakharovShabat/ResonantCubicFourthTail.lean)
gives the normalized bound K_4*B^20*s^8 for a family bounded by B*s.
[SourceCubicTailFamily.lean](../NLS/ZakharovShabat/SourceCubicTailFamily.lean)
defines the original period-two family with first modes 0,-n,-2n and second
modes 0,n,2n, with amplitudes s,s,s^3/(pi*n)^2 for n>0. It is real type,
eventually lies in any original open neighborhood of zero and satisfies
the normalized infinite error-tail limit for both coefficient directions.

Validation: `./scripts/check.sh` passes with 8,475 build jobs, 7,544
public examples and a transitive axiom audit of 43,891 NLS declarations.
The 21 inherited warnings are unchanged; the five new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The error in this earlier milestone subtracts the family's own cubic term.
The current milestone above supplies the cubic comparison and actual full
coefficient-sum limit. The actual counted-root gap limit remains necessary.
S6-047 stays pending, as recorded in the partial
Section6CubicTailSourceComparison-2026-10-28 entry of the
[source-review index](source-review-index.json). The final 1/2^p inequality
is neither proved nor refuted by these supporting estimates.

## Lemma 6.9: the literal root proof and corrected sums

[ResonantProofRoots.lean](../NLS/ZakharovShabat/ResonantProofRoots.lean)
follows the source's two Rouche comparisons: first one zero of
h=lambda-pi*n-a, then two of h squared and the determinant.
[ZeroCountPowers.lean](../NLS/ComplexAnalysis/ZeroCountPowers.lean)
provides the power-count identity. Analyticity, finite zeros and nonvanishing
on the boundary establish a unique simple diagonal root. No determinant
zero lies outside the open refined disk in the strip.

[SourceLemma6_9ProofRoots.lean](../NLS/ZakharovShabat/SourceLemma6_9ProofRoots.lean)
transports these statements to the actual original coefficient functions.
The root pair retains both scalar zero orders and periodic algebraic
multiplicities. Its multiset equals the raw period-two canonical endpoint
pair on one common original open convex neighborhood, with the same gap norm.
Repeated roots and arbitrary complex period-two potentials are included.

[SourceLemma6_9ProofEstimates.lean](../NLS/ZakharovShabat/SourceLemma6_9ProofEstimates.lean)
proves the exact exterior infimum pi/4, its attainment, and strict separation
by the actual full-strip suprema. The coefficient-tail bound retains the
boundary at 2*abs(n). Pointwise factorization and residual norms require
no globally analytic square-root branch. The actual gap satisfies
norm(x-y)<=norm(x-y)/8+2*sqrt(productSup); Cauchy's 1/8 bound also gives
the factor-six squared-gap estimate.

The combined `sourceLemma6_9_proof` gives one neighborhood, cutoff and
chosen root pair for the counts, canonical identification and corrected
convergent displacement sums at every larger cutoff. The signed and positive
pair sums use the additive-leading-tail budget; the literal duplicated
positive label uses twice that budget. Existing local p=2 counterexamples
to the printed budget remain unchanged. The rendered intermediate gap display
also repeats the first label on its left; the proved bound uses the intended
difference of the two roots.

The [ordered ledger](SECTION_6_ASSERTIONS.md) reconciles S6-042 through S6-046
in Section6RootSourceComparison-2026-10-28 of the
[source-review index](source-review-index.json). S6-043 and S6-045 retain
the printed displacement-sum correction; S6-046 matches the periodic-pair
identification and transfers the corrected estimate. S6-047, containing the
final weighted sum with 1/2^p on the left, remains pending. Its preceding
middle inequality is separately refuted; that does not resolve the final sum.

Validation: `./scripts/check.sh` passes with 8,470 build jobs, 7,540
public examples and a transitive axiom audit of 43,792 NLS declarations.
The 21 inherited warnings are unchanged; the four new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.8(ii): the literal off-diagonal proof

[OffDiagonalProofRegions.lean](../NLS/ZakharovShabat/OffDiagonalProofRegions.lean)
formalizes the source strict far-k and far-l regions and their weak near
complement. The far regions overlap; the positive regional sums give an
upper bound. The exact cutoff is floor(abs(n)/2)+1, including odd and negative
frequencies. Both resonant indices are explicitly removed. Each regional
moment converges jointly and equals the q-th power of a genuine nested row norm.

[OffDiagonalProofHolder.lean](../NLS/ZakharovShabat/OffDiagonalProofHolder.lean)
proves `sourceEquation1_16` for the literal physical weighted summand and its
actual shifted input norm. The near case retains the outer potential tail
at N for abs(n)>=N. Taking N=abs(n) gives a stronger tail than the source
half-tail; the summed bound retains the common full cutoff N. Both potential
frequencies retain their boundary. The weighted actual double
series is bounded by these three positive tests without a disjointness assumption.

[OffDiagonalProofPowerSums.lean](../NLS/ZakharovShabat/OffDiagonalProofPowerSums.lean)
gives the exact two-kernel Young budgets and convergent outer sums. Each far
sum decays as N^(-1) at p>=2 and N^(-(p-1)) at 1<p<=2. The near bound uses
the p-power of the actual potential tail. The low-exponent comparison is
explicitly between convergent outer sums; the two far estimates combine
with twice their common regional constant.

[OffDiagonalProofBounds.lean](../NLS/ZakharovShabat/OffDiagonalProofBounds.lean)
recombines the literal regional moments and both potential factors.
[SourceLemma6_8OffDiagonalProof.lean](../NLS/ZakharovShabat/SourceLemma6_8OffDiagonalProof.lean)
applies the bound to the actual even vectors and original analytic coefficient
functions. One open convex neighborhood containing the potential and zero,
with one threshold, gives bounded full-strip images and both convergent weighted
supremum p-power tails at every larger cutoff. The final pair bound retains
the full Fourier tail at N and exchanges the distinguished component correctly.
The new exponent-only constant is explicit and not claimed optimal;
earlier constants and valid estimates remain available.

The [ordered ledger](SECTION_6_ASSERTIONS.md) reconciles S6-038 through S6-041.
Section6OffDiagonalSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) preserves the misplaced p.42
weight correction and its local/common-cutoff counterexample scope. The final
bound follows the p-power/full-pair display on p.43; it does not assert the
refuted unpowered or positive-component-only p.41 display.
The determinant and Lemma 6.9 passages are reconciled above; the final p.44 sum
remains unresolved.

Validation: `./scripts/check.sh` passes with 8,466 build jobs, 7,537
public examples and a transitive axiom audit of 43,746 NLS declarations.
The 21 inherited warnings are unchanged; the five new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.8(i): the literal diagonal proof

[SourceLemma6_8DiagonalProof.lean](../NLS/ZakharovShabat/SourceLemma6_8DiagonalProof.lean)
identifies the actual diagonal with the absolutely convergent sum of
`phi_second(n+m)/(lambda-pi*m) * u_first(-m)`, excluding m=n. The series
holds for finite p>=1 under the stated square contraction. For 1<p<infinity,
under half-contraction the original even vector has norm at most twice the
unweighted first potential component. Unit-weight inverse compatibility justifies that sharper factor;
the preceding weighted inequality alone is not used to infer it.

`exists_uniform_sourceDiagonalHolder` supplies bounded actual images and the
literal p-power Holder bound for their full-strip suprema.
`exists_uniform_sourceDiagonalHolder_sum` compares two convergent full signed
outer sums on one neighborhood, for every cutoff beyond a common threshold.

[DiagonalProofRegions.lean](../NLS/ZakharovShabat/DiagonalProofRegions.lean)
uses the exact displayed regions: far `|m-n| >= |n|/2`, near
`|m-n| < |n|/2`. The initial source prose uses a strict far inequality;
the formal partition follows the displays and includes the boundary in far.
The q-th powers of the row norms equal the literal source moments. Their split is an
identity between convergent sums; the zero denominator contributes zero.
The near-region potential tail retains its boundary at N, and the far kernel
uses ceil(N/2), including odd cutoffs.

[DiagonalProofPowerSums.lean](../NLS/ZakharovShabat/DiagonalProofPowerSums.lean)
provides the powered-Young budgets and the concave-exponent step. It proves
N^(-1) far decay for p>=2 and N^(-(p-1)) for 1<p<=2. The near estimate uses
the actual potential-tail p-power in both regimes. Every outer regional sum
is summable. Recombination gives `sourceLemma6_8_diagonal_proof`, with the
original unweighted pair norm and floor(N/2) tail. Its explicit
`diagonalProofConstant` is 2^p times the existing sharper
`diagonalSummationConstant`; the old result is unchanged.

The [ordered ledger](SECTION_6_ASSERTIONS.md) reconciles S6-035 through S6-037.
Section6DiagonalSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records the exact evidence.
The ordered off-diagonal review is reconciled above; the final p.44 summed inequality remains open.

Validation: `./scripts/check.sh` passes with 8,461 build jobs, 7,531
public examples and a transitive axiom audit of 43,596 NLS declarations.
The 21 inherited warnings are unchanged; the three new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.8: full-strip uniform convergence of the original scalar series

[ResonantSeriesApproximation.lean](../NLS/ZakharovShabat/ResonantSeriesApproximation.lean)
and [SourceLemma6_8UniformSeries.lean](../NLS/ZakharovShabat/SourceLemma6_8UniformSeries.lean)
complete the uniform-series argument at the start of the proof on p.41.
The finite sums contain the actual T_n powers and actual resonant sources.
Their coefficient extraction retains both physical signs; they agree with the
original source operator sums on the entire closed strip.

For m terms and shifted square norm at most one half, the diagonal error is
at most `2*c_p*‖φ‖*‖φ.fst‖*2^(-m)`, where c_p is the Lemma 6.4 constant.
The positive and negative off-diagonal errors, multiplied by w(2n), are at
most `2^(-m)*‖φ.snd‖` and `2^(-m)*‖φ.fst‖`, respectively. The diagonal proof
reverses the shift once. The off-diagonal proof uses the actual conjugated
square and preserves its one-half norm bound.

`exists_uniform_sourceResonantParitySeries_rate` gives local geometric rates.
`exists_uniform_sourceResonantParitySeries` chooses one epsilon truncation
length for all three series, all potentials in the neighborhood and all
sufficiently distant signed strips. `sourceLemma6_8_uniform_series` expresses
the conclusion with `TendstoUniformlyOn` on the full products of the potential
neighborhood and closed strip. Every scalar term and finite weighted sum is
jointly analytic before imposing contraction. The actual coefficient extensions
already supply analyticity near boundary points; convergence on the closed
strip alone is not used to infer that stronger conclusion.

`weightedMode_hasSum` and `weightedSignedPairMode_hasSum` also justify the
Fourier expansion of the corrected even vector in the actual weighted norm.
The first component uses the -k mode and the second uses k, matching the
printed basis order. The results include p=1 and free centers under the stated
contraction. The quantitative power-tail estimates still require 1<p<infinity.

The [ordered ledger](SECTION_6_ASSERTIONS.md) now reconciles S6-033 and S6-034.
The first retains the two existing local refutations of the printed
quantitative off-diagonal display; it records the p-power/full-pair replacement
without claiming a counterexample for one fixed potential beyond every
individual cutoff. The diagonal regional proof is now reconciled above;
the off-diagonal proof is also reconciled above.
Section6UniformSeriesSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records the exact evidence.

Validation: `./scripts/check.sh` passes with 8,458 build jobs, 7,528
public examples and a transitive axiom audit of 43,507 NLS declarations.
The 21 inherited warnings are unchanged; the two new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.7: direct transpose identities and ordered source review

[SourceLemma6_7ProofTranspose.lean](../NLS/ZakharovShabat/SourceLemma6_7ProofTranspose.lean)
formalizes the operator symmetry used before the diagonal coefficients are
compared on p.40. Its pairing is the unconjugated cross-component Fourier sum
on a base vector and an actual derivative-domain test. One derivative supplies
the l1 test required at every finite p≥1.

`weightedGreenPairing_complementaryProjection` transfers Q to the test.
`weightedGreenPairing_complementaryInverse_symm` gives the transpose identity
for the actual punctured inverse R=A⁻¹Q, including free centers.
`weightedGreenPairing_potentialInverse_transfer` reverses the factors in T=Phi R;
induction gives `weightedGreenPairing_powerPotential_symm` for every T^j Phi.
These assertions require no contraction assumption.

`weightedGreenPairing_correctedPotential_symm` proves the full corrected
potential identity when the shifted square is small. It uses potential
symmetry on f+R Hf and g+R Hg and cancels the equal R terms, with H=T_hat Phi.
`sourceCorrectedPotential_transpose` transports the result to the actual
original source correction and potential. `sourceGreenPairing_apply` identifies
its two literal Fourier sums. No reality condition is needed.

This is an explicit bilinear interpretation of the source's adjoint argument.
It does not assert a Hilbert adjoint on a general l^p space, a bounded
potential on the whole base space, or a full free inverse at a resonant center.
The p=3 integration example derives equality of the actual matrix diagonals
from this identity; the p=1 example checks the original Fourier formula.

The [ordered assertion ledger](SECTION_6_ASSERTIONS.md) reconciles S6-024
through S6-032 against thirty reviewed module bodies: common contraction,
P/Q reduction, full eigenvector reconstruction, matrix order, the corrected
reality statement, transpose symmetry, signed conjugation, parity series and
actual strip suprema. Seven rows are matched, one is corrected, and one retains
the domain interpretation. The other 38 rows remain pending ordered review,
even where earlier focused comparisons already exist.

Section6TransposeSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records the exact claims,
public declarations and snapshots. Earlier reviews and all outstanding
completion qualifications are preserved.

Validation: `./scripts/check.sh` passes with 8,456 build jobs, 7,526
public examples and a transitive axiom audit of 43,460 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.5: full Fourier convergence and the reciprocal-moment constants

[SourceLemma6_5ProofExpansion.lean](../NLS/ZakharovShabat/SourceLemma6_5ProofExpansion.lean)
and [SourceLemma6_5ProofMoments.lean](../NLS/ZakharovShabat/SourceLemma6_5ProofMoments.lean)
supply the remaining interfaces in the proof on pp.38–39, extraction
lines 2558–2661. The earlier literal component and Hölder results now
connect to a full vector-valued Fourier sum and direct scalar moment bounds.

| Assertion | Public entry point | Scope |
| --- | --- | --- |
| Full signed Fourier expansion | `sourceLemma65Vector_original_hasSum`, `sourceLemma65Vector_original_restricted_hasSum` | Product-index HasSum in the original weighted l1 pair norm, with both literal denominators and resonant exclusions. |
| Original-domain identification | `sourceLemma65Vector_original_coefficients`, `sourceLemma65Vector_original_components` | The limit has precisely both raw components of the actual g=A⁻¹ Q Φ A⁻¹ Q f. |
| Far reciprocal moment | `sourceLemma65Moment_far_le`, `sourceLemma65Moment_lattice_tail`, `sourceLemma65Moment_far_bracket` | Exact strict-far region, two one-factor tails and the printed half-radius bracket; zero center included. |
| Near reciprocal moment | `sourceLemma65Moment_selected_le`, `sourceLemma65Moment_near_all` | Full-moment factorization, nonnegative restriction, exact Fourier tail and inverse weight. |
| Endpoint and shared constant | `sourceLemma65Moment_far_all`, `sourceLemma65ProofConstant_pos`, `sourceLemma65ProofConstant_sq` | One positive exponent-only c_p; finite p≥1, using the supremum estimate at p=1. |
| Both recombined component estimates | `sourceLemma65Moment_half_to_full`, `sourceLemma65Moment_original_bounds` | Exact factor 2^(1/p), original signed shifts, symmetric tail boundary and every closed strip. |
| Corrected final Young display | `sourceLemma65Proof_young_budget`, `sourceLemma65Proof_corrected_chain` | The actual square is bounded by the Young majorant, then by the printed budget with that same constant. |

The explicit choice is c_p = sqrt(D_p), where D_p is the existing
`weightedDoubleConstant`. It is an enlarged constant for this Lemma 6.5
proof; it does not replace the separately proved choice c₂=2 in Lemma 6.4.
The near/far scalar estimates are derived directly from their selected
reciprocal moments. The final Young-budget comparison uses the existing
stronger square budget and algebra with c_p²=D_p.

Fourier convergence is asserted in the weighted l1 pair norm used in the
proof. The representative agrees coefficientwise with the actual original
derivative-domain vector; no stronger derivative-domain absolute convergence
is asserted. The p.39 equality remains formally refuted. Its correct
replacement is the chain of two inequalities above.

The first integration example checks the full literal series and original
domain identification at the free zero center with p=1. The second checks
the exact half-bracket at the negative odd strip −3 with p=3 and links it
to the corrected original shifted-norm estimate.

Section6ExpansionSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records five focused groups
and eleven reviewed module hashes. It supplies the interfaces left open in
the previous milestone's historical record. The full 47-group inventory,
the final p.44 summed constant and the other completion qualifications remain open.

Validation: `./scripts/check.sh` passes with 8,455 build jobs, 7,524
public examples and a transitive axiom audit of 43,447 NLS declarations.
The 21 inherited warnings are unchanged; the two new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.5: the literal double-inverse series and Hölder steps

[SourceLemma6_5ProofSeries.lean](../NLS/ZakharovShabat/SourceLemma6_5ProofSeries.lean)
and [WeightedSandwichAbsoluteSum.lean](../NLS/SequenceSpaces/WeightedSandwichAbsoluteSum.lean)
formalize the component series and estimates on printed p.38, extraction
lines 2558–2629. They use the actual original-domain vector
`g = A⁻¹ Q Φ A⁻¹ Q f`, every signed index, every point of its closed strip,
and every finite Banach exponent.

| Assertion | Public entry point | Scope |
| --- | --- | --- |
| Both original coefficient formulas | `sourceLemma65Proof_original_coefficients`, `sourceLemma65Proof_original_restricted` | Both exclusions and both original complex denominators; first physical component reflected, second input reflected. Free strip centers included. |
| Joint weighted absolute convergence | `SpectralWeight.sandwich_weighted_sum`, `SpectralWeight.shiftedNorm_sandwich_le_sum` | Full product-index sum, constant-one norm bound and actual shifted weighted l1 output; includes the conjugate endpoint. |
| Literal distance majorization | `sourceLemma65ProofTerm_summable`, `sourceLemma65Proof_original_majorants` | Convergent full sum controls both actual components in their original signed shifts. |
| Exact admissible partition | `sourceLemma65ProofNear_iff`, `sourceLemma65ProofFar_iff`, `sourceLemma65ProofTerm_split` | Closed half-radius near set, strict far set, both resonant indices excluded. |
| Near weight and exact remainder | `sourceLemma65ProofNear_weight`, `sourceLemma65Proof_near_tail_eq` | The factor 1/w(n), with every Fourier-tail boundary frequency retained. |
| Selected Hölder estimates | `sourceLemma65Proof_far_holder`, `sourceLemma65Proof_near_holder` | Finite p>1, exact restricted reciprocal moments and weighted numerator powers. |
| Original scalar norms | `sourceLemma65ProofNumerator_moment`, `sourceLemma65Proof_far_holder_norm`, `sourceLemma65Proof_near_holder_tail` | Exact full numerator factorization and selected-moment bounds, with the original input shift. |
| Explicit endpoint | `sourceLemma65Proof_far_one`, `sourceLemma65Proof_near_one`, `sourceLemma65Proof_endpoint` | p=1; far factor 2/(1+abs(n)), near tail divided by w(n), and their actual output norm bound. |

The printed far numerator is summed over all pairs. The selected-numerator
version above is stronger; the norm-product estimate and exact full-moment
factorization recover the printed bound before its scalar reciprocal
simplification. The near numerator remains restricted as printed.
The complement relation between the two index sets is relative to
nonresonant pairs. Neither a resonant pair nor a half-radius boundary is
silently placed in the wrong region.

One integration example combines the original-domain coefficient formula
and the p=1 norm bound at the free center of strip −4. The other checks
the negative boundary n=−4, k=l=−2, its retained potential coefficient,
and the p=3 near estimate.

This earlier step proves coordinate series and joint absolute scalar summability.
The expansion/moment milestone above now supplies the vector-valued `HasSum`
and direct comparisons with c_p²/⟨n/2⟩^(1/p) and c_p², using one explicit
exponent-only constant. The existing operator norm estimate remains valid.
Section6SandwichSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records six focused groups
and nine reviewed module hashes. The earlier p.39, p.42 and p.44 corrections
and the unresolved final p.44 summed constant retain their qualifications.

Validation: `./scripts/check.sh` passes with 8,453 build jobs, 7,522
public examples and a transitive axiom audit of 43,409 NLS declarations.
The 21 inherited warnings are unchanged; the two new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Propositions 6.1 and 6.3: correcting the proof's power comparison

[SourceGapProofPower.lean](../NLS/ZakharovShabat/SourceGapProofPower.lean)
compares the intermediate inequality on printed p.44, lines 3274–3279
of the source extraction. Write B₊ and B₋ for the full-strip suprema
of the two actual off-diagonal coefficients, and S for the full-strip
supremum of their product. The valid comparison is

    6^(p/2) S^(p/2) ≤ (6^(p/2)/2) (B₊^p + B₋^p).

The printed factor 3^(p/2) is too small at p=4. A balanced resonant
potential has actual coefficients a=0 and b₊=b₋=t throughout its strip.
For t>0, the printed left side is 36*t^4 and its right side is 18*t^4.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual coefficients and exact suprema | `sourceGapProof_actual_coefficients`, `sourceGapProof_stripSup_const` | The original analytic functions on the entire closed, unbounded strip. |
| Admissible arbitrarily small witnesses | `sourceGapProof_exists_small_witness` | Every signed index, t<pi/16, every prescribed norm radius, and squared-operator norm at most 1/2 throughout the strip. |
| Locally uniform cutoff refutation | `sourceGapProof_failure_near_zero` | Every open original p=4 neighborhood of zero and every common cutoff admit a positive-index witness. |
| Correct scalar and supremum estimates | `sourceGapProof_correct_scalar`, `sourceGapProof_correct_full_suprema` | Every nonnegative real exponent; bounded full-strip norm images supply the product comparison. |
| Correct original root estimate | `sourceGapProof_source_roots` | Every controlled original counted spectral pair, including repeated roots; finite p≥1. |
| Common neighborhood and root existence | `sourceGapProof_uniform_source_roots` | Finite p>1; one open convex neighborhood containing the input and zero, one signed cutoff, and actual counted root sequences. |

The counterexample potential may depend on the cutoff. It does not assert
infinitely many failures for one fixed potential. The first integration
example combines the conditional p=1 estimate with the full zero count.
The second constructs arbitrarily small witnesses on strip −3 satisfying
all original strip controls and the strict reversed power comparison.

This is a correction to the middle comparison only. The triangle inequality
on the next line is valid with any chosen Fourier coefficient; its index
must be aligned with the following sum. The final 1/2^p summed inequality
in lines 3284–3290 remains unresolved. Its failure does not follow from
this counterexample, and existing larger-constant gap bounds remain valid.
Section6GapPowerSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records four focused groups
and seven reviewed module hashes. The 47-group Section 6 inventory remains open.

Validation: `./scripts/check.sh` passes with 8,451 build jobs, 7,520
public examples and a transitive axiom audit of 43,350 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.8: correcting the weight in the off-diagonal proof series

[SourceLemma6_8ProofSeries.lean](../NLS/ZakharovShabat/SourceLemma6_8ProofSeries.lean)
compares the displayed equality on printed p.42. Its right side is
w(2n) times the unweighted remainder b_n⁻−φ⁻_(2n). The extra weight must
be removed there, or included on the left as well.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Literal denominators and indices | `sourceLemma68PrintedOffDiagonalSeries_restricted` | Exactly the two exclusions l≠n, k≠n and both λ−π-index denominators; the physical first-component signs remain reflected. |
| Correct weight and exceptional equality | `sourceLemma68PrintedOffDiagonalSeries_eq`, `sourceLemma68_printed_series_equality_iff` | The printed equality holds precisely if w(2n)=1 or the remainder is zero. |
| Original operator and full sum | `sourceLemma68_offDiagonal_original`, `sourceLemma68_offDiagonal_summable_norm`, `sourceLemma68_offDiagonal_hasSum` | Actual original-source second iterate, absolute joint convergence and product-index sum, for every finite p≥1 and source weight on the small-square domain. |
| Concrete original analytic coefficient | `sourceLemma68_printed_series_source_counterexample` | Constant weight two, amplitudes 1/100, every nonzero signed strip center; the exact weighted norm squared is 1/1250. |
| Simultaneous full-strip bounds | `sourceLemma68ProofFamily_square_half` | Both weighted and unit-weight squared operators are at most 1/2 for variable second amplitude of norm at most 1/100. |
| Locally uniform cutoff refutation | `sourceLemma68_printed_series_not_locally_uniform` | Every open neighborhood of one fixed constant background and every proposed cutoff admit an actual positive-index counterexample. |

The fixed background has first constant amplitude 1/100 and zero second
component. Perturbing its second component at frequency −2n gives exact
norm and distance formulas, a nonzero cubic remainder, and agreement with
the original analytic coefficient. The witness can depend on the cutoff;
this does not assert failure at infinitely many indices for one fixed potential.
The subsequent valid weighted Hölder estimate remains available through
`weighted_norm_tsum_offDiagonal_le` and
`weightedResonantBMinus_remainder_le`. The separate earlier corrections to
Lemma 6.8's main quantitative bounds retain their stated scopes.

Two integration examples connect the full joint sum to the original
operator at p=1, and combine the original analytic counterexample on strip
−3 with its exact norm and both full-strip half-bounds.
Section6OffDiagonalWeightSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records four focused groups
and fourteen reviewed module hashes. The 47-group inventory remains open.

Validation: `./scripts/check.sh` passes with 8,450 build jobs, 7,518
public examples and a transitive axiom audit of 43,328 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Lemma 6.5: correcting the final equality in the proof

[SourceLemma6_5ProofDisplay.lean](../NLS/ZakharovShabat/SourceLemma6_5ProofDisplay.lean)
formalizes the intermediate Young majorant on printed p.39 and its relation
to the original vector g=A⁻¹QΦA⁻¹Qf.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original-domain identification | `sourceLemma65YoungMajorant_domain_coefficients`, `sourceLemma65YoungMajorant_domain_operator` | Exact raw components and original differential potential action; both signed shifts. |
| First inequality | `sourceLemma65_square_le_young` | The actual squared-operator output's p-power is bounded by the intermediate Young expression. |
| Corrected second inequality | `sourceLemma65YoungMajorant_le` | The majorant is at most the established Lemma 6.5 bound's p-power times the shifted input norm's p-power. |
| Literal printed expression | `sourceLemma65PrintedProofBudget` | Retains 2*c_p^(2p), the exact tail cutoff, weight divisor and shifted input norm. |
| Strict witness | `sourceLemma65_printed_equality_strict` | Every positive c_p and nonzero potential: a nonzero resonant input gives zero majorant and a strictly positive printed expression. |
| Equality refuted | `not_sourceLemma65_printed_proof_equality` | No equality for all inputs in even one fixed strip. |

All these results allow every 1≤p<infinity, every source weight and every
point of every closed strip, including its free center and negative indices.
There is no extra normalization w(0)=1 or smallness condition. The valid
replacement uses the established exponent-only constant, without claiming
an optimal constant. Lemma 6.5's main upper-bound statement is unchanged;
the error is the equality sign in the proof's last display.

Two integration examples check p=1 with constant weight two and strip −3,
and the complete valid inequality chain plus original-domain realization
at p=3. Section6ProofEqualitySourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records four focused
groups and ten reviewed module hashes. The 47-group Section 6 inventory
remains in progress.

Validation: `./scripts/check.sh` passes with 8,449 build jobs, 7,516
public examples and a transitive axiom audit of 43,292 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

## Proposition 6.1: original norm and actual spectrum

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Coefficient-preserving unit weighting | `unitWeightedPairEquiv_fst`, `unitWeightedPairEquiv_snd` | Every integer frequency, both original components; the existing map is a linear isometry. |
| Same periodic operator input | `weightedBaseToPair_unitWeightedPairEquiv` | Equals `CoeffPair.toMax p φ`; no frequency doubling. |
| Same Fourier tail | `weightedPairFourierTail_unitWeightedPairEquiv` | Same cutoff, retaining its boundary frequencies, with exact norm equality. |
| Actual original spectrum | `sourcePeriodTwoSpectrum_iff` | Noninvertibility of `sourceSpectralPencil`, equivalently complement of `sourceResolventSet`. |
| Corrected quantitative bound | `exists_uniform_sourcePeriodTwoDisplacement` | Every finite p>1; one open convex neighborhood containing the input and zero; all larger cutoffs. |
| Multiplicities and complete distant strips | `PeriodicResonantPair`, together with `sourcePeriodTwoSpectrum_iff` | The two selected values exhaust each sufficiently distant strip; repetitions record algebraic multiplicity. |
| Locally small corrected budget | `exists_uniform_small_sourcePeriodTwoDisplacementBudget` | The neighborhood and cutoff may depend on the positive tolerance. |
| Qualitative ℓᵖ asymptotics | `sourceProposition6_1_asymptotics` | Actual high pairs, ℓᵖ displacement sequences, convergent full signed tails, and locally uniform small power sums. |

The new entry points are in `SourcePeriodTwoDisplacement` and
`SourcePeriodTwoAsymptotics`. Their quantitative input is the existing proved
weighted periodic-pair theorem. They identify its coefficients, exact norms,
and spectral pencil with those of the original period-two input.

Write B=‖φ‖, T=‖R_floor(N/2) φ‖, and δ=min(1,p−1). The proved bound is

```
C_p [ T^p + (B^p/N^δ + T^p)(1+B^p)B^p ].
```

`C_p = rootDisplacementSummationConstant p` depends only on p. In Lean,
`N/2` in this earlier API is natural-number division. The stronger full-cutoff
and ceiling-half source theorems below now establish the corresponding
corrected formulas with T=‖R_N φ‖ and T=‖R_ceiling(N/2) φ‖.
The tails sum both root displacements over all integer indices with |n|≥N.

The earlier qualitative theorem selects actual pairs at sufficiently distant
indices and leaves its finite central entries unspecified. Their values do
not affect ℓᵖ membership. The complete canonical construction below now fills
these entries; continuity of individual eigenvalue labels is not asserted.

## Proposition 6.1: complete canonical labels for arbitrary period-two input

The source assertion concerns the full eigenvalue sequences. The earlier
high-pair theorem left the finite central entries unspecified; existence
of the earlier canonical endpoints also required even Fourier support.
The following construction now covers every raw period-two input at finite
p>1, preserving the original component-sum norm and every Fourier frequency.

[SourcePeriodTwoCompleteLabels.lean](../NLS/ZakharovShabat/SourcePeriodTwoCompleteLabels.lean)
splices the actual central root multiset into actual distant pairs. The
central and distant multiplicities and both ℓᵖ displacement classes are
retained. `sourceProposition6_1_complete_asymptotics` also preserves the
corrected signed budget and arbitrarily small high tails on one open convex
neighborhood containing the input and zero. Its tail cutoff K is strictly
larger than the central cutoff N₀, whose block includes |n|≤N₀.

[SourcePeriodTwoOrderedLabels.lean](../NLS/ZakharovShabat/SourcePeriodTwoOrderedLabels.lean)
orders the central multiset and each distant pair lexicographically.
`rootDisplacementPowerTail_eq_of_high_pair_multiset` proves that this sorting
preserves the symmetric displacement sum past the central cutoff.
`sourceProposition6_1_ordered_asymptotics` therefore gives the same corrected
budget and local smallness for complete globally ordered labels.

[SourcePeriodTwoCanonicalEndpoints.lean](../NLS/ZakharovShabat/SourcePeriodTwoCanonicalEndpoints.lean)
fixes the sequences `sourcePeriodTwoCanonicalLeft` and
`sourcePeriodTwoCanonicalRight`. Complete ordered labelings agree even at
different central cutoffs, so these labels do not depend on the finite
enumeration used to construct them. They exhaust the original source-pencil
spectrum, retain every algebraic multiplicity of its coefficient-preserving
periodic realization, and have ℓᵖ displacements. At even-support inputs they
agree with the existing canonical periodic endpoints at that same input.

`sourceProposition6_1_canonical_asymptotics` transfers the locally uniform
corrected signed estimates to these fixed sequences, including complete
central data at a common cutoff for the neighborhood. Domination also
gives the literal positive-index sums. The three public examples cover an
actual odd Fourier mode, the positive-index estimate at p=3, and the free
spectrum with both copies of each eigenvalue.

This supplies the complete ordered sequences for the qualitative assertion;
it does not restore the false printed quantitative budget. Individual-label
continuity, arbitrary-input parity assignments, and sharp constants are not
asserted. The exact 2014 construction comparison and G.2 norm qualification
remain separate open items.

## Proposition 6.1: refutation of the printed quantitative bound

The formula on printed page 35 and the corresponding Lemma 6.9 display on
page 43 omit the additive leading-tail term. Their overall potential-norm
factor makes the printed p=2 budget quartic at zero, whereas a single
resonant input has quadratic displacement energy.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Literal Hilbert budget | `sourcePrintedHilbertDisplacementBudget` | Original pair norm and ceiling(N/2) tail. |
| Rounding-independent comparison | `sourcePrintedHilbertDisplacementBudget_le` | Ceiling budget is no larger than the existing floor-cutoff budget for every nonnegative constant. |
| Actual weighted periodic witness | `exists_periodicRoot_exceeding_printed_budget` | Upgrades the earlier reduced determinant witness to actual periodic spectral membership. |
| Actual original-pencil witness | `exists_sourcePeriodTwoRoot_exceeding_printed_budget` | Every open neighborhood of zero, every proposed uniform cutoff, and every nonnegative constant. |
| Refuted single-root consequence | `not_exists_locally_uniform_sourcePrintedDisplacementBudget` | No locally uniform printed estimate at zero. |
| A root is controlled by its pair tail | `sourcePeriodTwoRoot_sq_le_pair_tail` | Uses summability and nonnegativity; no assumption that the two labels are distinct. |
| Refuted full signed pair sum | `not_sourceProposition6_1_printed_pair_sum` | Rules out the printed budget for the sum over abs(n)≥N and labels exhausting the actual distant disk spectra; the literal positive range is treated below. |

These statements are in `SourcePeriodTwoDisplacementCounterexample`.
The construction inherited from `RootDisplacementSourceAudit` places small
single coefficients at the two resonant frequencies. Its roots are nπ±t,
its squared original norm is 2t², and its printed budget is at most 24C t⁴.
The resonance can be chosen beyond any proposed uniform cutoff.

This refutes the source's **locally uniform quantitative** claim at zero.
It does not refute the qualitative ℓᵖ assertion, nor does it assert that a
separate cutoff chosen individually for each fixed input must fail. The
counterexample covers both natural rounding conventions at N/2.

## Proposition 6.1: the literal positive-index sum

The display on printed page 35 sums over n≥N. The earlier implementation
uses |n|≥N, so its refutation alone does not refute the smaller printed sum.
[SourcePositiveDisplacementTail.lean](../NLS/ZakharovShabat/SourcePositiveDisplacementTail.lean)
makes the printed range explicit and supplies both needed comparisons.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Exact summation range | `sourcePositiveDisplacementPowerTail` | Sum of both displacement p-powers for n≥N, zero elsewhere. |
| Comparison with the signed tail | `summable_sourcePositiveDisplacementPowerTail`, `tsum_sourcePositiveDisplacementPowerTail_le` | Nonnegative domination transfers summability and the upper bound. |
| Corrected original spectral estimate | `exists_uniform_sourcePositiveDisplacement` | Finite p>1; actual counted pairs and original-pencil equivalence; one open convex neighborhood containing the input and zero; every later positive tail. |
| Actual positive-root lower bound | `sourcePeriodTwoRoot_sq_le_positive_pair_tail` | A positive-index root covered by either label contributes its squared displacement to the p=2 sum. |
| Literal pair-sum refutation | `not_sourceProposition6_1_printed_positive_pair_sum` | No nonnegative constant, uniform cutoff, and open neighborhood of zero can satisfy the printed positive-index bound for labels covering the actual distant positive disk spectra. |

The corrected theorem uses the earlier `sourcePeriodTwoDisplacementBudget`
with floor(N/2), retaining its additive leading-tail term. Stronger signed
full-cutoff and ceiling-half estimates are available below. The refutation
uses the existing positive-index spectral witness and the printed ceiling
budget. It establishes the literal summation range without asserting a new
source error or failure of every individually chosen fixed-input cutoff.

Three public examples distinguish a negative-index displacement from this
positive tail, check the corrected original spectral estimate at p=4, and
show that every proposed cutoff and zero-neighborhood contain an actual
positive root violating the budget for every pair of labels covering it.

## Corollary 6.2: arbitrary period-two input

The paragraph preceding the corollary discusses one-periodic input, but the
corollary itself states the period-two space. This scope is now realized
constructively by bounded restriction to [0,1] and re-expansion with unit
frequencies. No typo or change of the displayed input space is needed.
Merely keeping the even input coefficients would discard physical odd modes.

For raw period-two coefficients a, the unit-period sequence is

```
b_n = a_(2n) + i H(oddSamples(a))_(n−1),
```

where H is the established shifted discrete Hilbert transform. On one odd
input mode at 2k+1 with amplitude c, the output is
`c · 2i / (π(2k−2n+1))`. In particular, input mode 1 has nonzero output
`2i/π` at unit frequency zero. The public checks cover this value and its
nonvanishing at p=3. The map recovers embedded period-one input exactly.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Bounded scalar restriction | `periodTwoToUnit`, `norm_periodTwoToUnit_le` | Every 1<p<∞; even samples plus odd shifted Hilbert transform. |
| Exact finite physical coefficients | `periodTwoToUnit_finite_integral` | Every finitely supported period-two Fourier polynomial; both frequency signs and parities. |
| Arbitrary physical L² restriction | `periodTwoToUnit_two_ofFunction`, `periodTwoToUnit_two_reconstruct` | Actual unit-interval coefficients and almost-everywhere reconstruction, without period-one or endpoint-matching assumptions. |
| Original pair norm and phase | `norm_sourcePeriodTwoRestriction_le`, `sourcePeriodTwoRestriction_sourcePhase` | Same scalar bound in the source component-sum norm; commutes with the auxiliary potential phase. |
| Physical pair reflection | `sourcePeriodTwoRestriction_ofFunction`, `sourcePeriodTwoRestriction_reflection` | Restriction then completed extension equals literal physical reflection for arbitrary L² pairs. |
| Actual full boundary spectra | `sourcePeriodTwoBoundaryRoots_exhaustive`, `sourcePeriodTwoAuxiliaryRoots_exhaustive` | Both ordinary and both auxiliary spectra after restriction and their respective reflections. |
| Full Jordan multiplicities | `sourcePeriodTwoBoundaryRoots_multiplicity`, `sourcePeriodTwoAuxiliaryRoots_multiplicity` | Repeated canonical labels count actual original-domain full root-space dimensions. |
| Locally uniform full power sums | `sourceCorollary6_2` | One open convex neighborhood containing the input and zero; one positive bound for all four complete displacement power sums. |
| Full ℓᵖ membership | `sourceCorollary6_2_mem` | All integer indices, including central labels, for every finite p>1. |

The physical integral identification is proved for finite inputs at every
1<p<∞ and arbitrary L² input. On general ℓᵖ input, the bounded coefficient
map defines the completion; no pointwise representative of a general
Fourier–Lebesgue distribution is assumed. This step does not assert
continuity of individual canonical eigenvalue labels.

## Midpoint and gap consequences on page 35

`SourcePeriodTwoMidpointGap` works on the original raw period-two input.
It does not use `periodOnePotential`, which would double the input frequencies.
For every 1<p<∞, the actual distant counted pairs give
`(ξ_n+η_n)/2 − nπ ∈ ℓᵖ` and `ξ_n−η_n ∈ ℓᵖ` on one open convex
neighborhood containing the input and zero. The finitely many unspecified
entries of those selected sequences do not affect membership.

The contour midpoint and squared gap agree with these pairs at high indices.
`exists_uniform_small_sourcePeriodTwoMidpointGapTail` proves arbitrarily small
full signed tails of the sum of midpoint-displacement p-powers and squared-gap
p/2-powers, locally uniformly. `sourcePeriodTwoMidpointGap_summable` proves
both complete power sums converge; `sourcePeriodTwoMidpoint_mem` gives the
midpoint's actual ℓᵖ membership. This does not assign individual central pairs
to the fixed low-index contours or assert continuity of eigenvalue labels.

## Complete canonical midpoints and gaps

[SourcePeriodTwoCanonicalMidpointGap.lean](../NLS/ZakharovShabat/SourcePeriodTwoCanonicalMidpointGap.lean)
uses the actual ordered canonical pair at every integer index, including
all central eigenvalues. Its midpoint is half the sum of the two endpoints;
its gap is the right endpoint minus the left endpoint.

`sourcePeriodTwoCanonicalMidpointGap_memℓp` proves both the midpoint
displacement and the gap belong to ℓᵖ for arbitrary raw period-two input
and every finite p>1. `sourcePeriodTwoCanonicalMidpointGap_asymptotics`
proves a corrected joint signed power-tail bound and arbitrarily small
joint tails on one open convex neighborhood containing the input and zero.
The sufficient multiplier on the displacement budget is 2·2^(p−1);
no optimality is asserted. The tail cutoff K is strictly larger than N₀.

`sourcePeriodTwoCanonicalMidpointGap_eq_contours` identifies the canonical
midpoint and squared gap with the actual contour quantities at every index
strictly beyond one common cutoff, uniformly on an original-input
neighborhood. It uses equality of the counted pair multisets. It does not
identify individual central ordered pairs with the fixed central circles.

Three public examples recover the free midpoint and zero gap, identify the
entire canonical and contour tail functions past a common cutoff, and prove
reality of the midpoint and gap at every central and distant index for
real-type input. Individual eigenvalue-label continuity is not asserted.

## Proposition 6.3: exact weighted input and corrected bound

The displayed source weight assumptions are exactly those of `SpectralWeight`:
`w_n≥1`, symmetry, submultiplicativity, and monotonicity on nonnegative indices.
They do not require the extra normalization `w_0=1`. The public checks use
`WeightedCoeffPair.norm_rpow_eq_tsum` to verify the printed component-sum norm.
`sourceWeightedPeriodTwoInput` forgets the weight while retaining both raw
Fourier components at every integer frequency, without period doubling.
`sourceWeightedPeriodTwoSpectrum_iff` identifies the actual source pencil's
noninvertibility with the existing weighted spectral realization.

Write B=‖φ‖_(w,p), T=‖R_floor(N/2) φ‖_(w,p), and δ=min(1,p−1).
The corrected estimate in `sourceProposition6_3_corrected` is

```
Σ_(|n|≥N) w_(2n)^p |γ_n|^p
  ≤ C_p [ T^p + D_p B^p (B^(2p)/N^δ + T^(2p)) ].
```

Here `C_p=rootGapSummationConstant p` and
`D_p=offDiagonalSummationConstant p` depend only on p. The theorem uses the
actual contour squared gap through `‖γ_n²‖^(p/2)=|γ_n|^p`. It supplies actual
counted spectral pairs, their source spectral equivalence, and the sum bound
on one open convex neighborhood for every larger cutoff. The full-cutoff
and ceiling-half versions below retain this data with the sharper tail.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Small corrected budget | `exists_uniform_small_rootGapBudget` | Every source weight and 1<p<∞; one neighborhood and cutoff for each positive tolerance. |
| Small actual weighted gap tails | `sourceProposition6_3_small_tails` | All signed indices beyond every larger cutoff; actual intrinsic squared gap. |
| Full weighted gap-power convergence | `sourceProposition6_3_summable` | Includes the finitely many central contour values. |
| Weighted ℓᵖ gap membership | `sourceProposition6_3_gap_mem` | Any choice of square roots of the intrinsic squared gaps, weighted at 2n. |

## Proposition 6.3: printed quantitative estimate is false locally at zero

The printed page-36 p=2 estimate with unit weight has the same quartic budget
as the earlier root-displacement display. `SourceWeightedGapCounterexample`
now proves the failure for the actual gap, rather than inferring it from a
single displaced root. In every open weighted-input neighborhood of zero and
beyond every proposed cutoff, the two finite resonant modes produce actual
roots `nπ±t`. The full counted pair and spectral equivalence identify the
intrinsic squared gap with `4t²`. The printed budget is at most `24C t⁴`.

`exists_periodicGap_exceeding_printed_budget` exceeds the floor-cutoff budget.
`sourcePrintedHilbertGapBudget` records the ceiling-cutoff version for general
weights, and `exists_periodicGap_exceeding_printed_ceiling_budget` exceeds that
smaller budget too. The final negations
`not_sourceProposition6_3_printed_gap_sum` and
`not_sourceProposition6_3_printed_pair_sum` exclude the printed budget for
the full signed sums of intrinsic gaps and actual counted-pair gaps, already
at unit weight and p=2. The literal positive-index sums are addressed below.

This is a failure of the uniform cutoff on neighborhoods of zero. It does not
claim that every separately chosen cutoff for a fixed potential fails. The
qualitative weighted ℓᵖ asymptotics and the corrected budget remain proved.

## Proposition 6.3: the literal positive-index weighted gap sum

Printed page 36 sums over n≥N. The earlier signed sum has a larger left
side, so its refutation alone does not settle the literal display.
[SourcePositiveGapTail.lean](../NLS/ZakharovShabat/SourcePositiveGapTail.lean)
provides the positive-index intrinsic and labeled gap tails.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Exact intrinsic summand | `sourcePositiveGapPowerTail` | The weight at 2n times the p/2-power of the actual contour squared-gap norm, retained precisely when n≥N. |
| Domination by the signed tail | `summable_sourcePositiveGapPowerTail`, `tsum_sourcePositiveGapPowerTail_le` | Nonnegativity transfers summability and the signed upper bound. |
| Corrected weighted estimate | `sourceProposition6_3_corrected_positive` | Every source weight and finite p>1, actual counted spectral pairs, original-pencil equivalence, one open convex neighborhood containing the input and zero, and every later positive tail. |
| Exact labeled gap | `sourcePositiveRootGapPowerTail`, `sourcePositiveGapPowerTail_eq_rootGap` | Equals the intrinsic tail whenever the pairs represent the actual squared gaps; no choice of square-root branch is needed. |
| Printed intrinsic sum refuted | `not_sourceProposition6_3_printed_positive_gap_sum` | The actual positive-index gap exceeds the printed ceiling-half budget on every zero-neighborhood and beyond every proposed uniform cutoff at p=2, unit weight. |
| Printed labeled sum refuted | `not_sourceProposition6_3_printed_positive_pair_sum` | No choice of actual counted positive-index pairs repairs that literal bound. |

The corrected bound is the earlier `rootGapBudget` with floor(N/2) and
its additive leading-tail term. Stronger signed full-cutoff and ceiling-half
bounds remain available. The counterexample is the existing actual resonant
gap; this step verifies its implication for the exact printed sum. It makes
no claim that every separately chosen cutoff for a fixed input fails.

Three public examples distinguish a negative-index gap from this positive
tail, retain arbitrary source weights at p=3, and exhibit an actual positive
intrinsic gap violating the printed budget beyond every proposed cutoff.

## Equation (1.13), the P/Q equations, and the original derivative domain

`SourceWeightedPencil` adds the derivative-domain counterpart of the existing
coefficient-preserving weighted source inclusion. The two maps are injective,
and including the derivative domain into the base commutes with forgetting
the weight. The exact identity `sourceWeightedPencil_eq` identifies the original
source pencil with `weightedFreePencil − weightedDomainPotential`.
`sourceWeightedDomainPotential_eq` identifies the weighted potential with the
original operator at φ minus the original operator at zero. Thus the projected
equations concern the actual original operator on the weighted derivative
domain, rather than a separately stipulated coefficient equation.

`SourcePQSplitting` proves unique decomposition into the two raw resonant
amplitudes and a complementary vector. The synthesis uses physical frequencies
−n in the first component and n in the second. The theorem applies to every
positive weight, including the one-derivative weight, and every finite Banach
exponent. It realizes the direct decomposition in (1.13) on both domains.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original and weighted pencil equality | `sourceWeightedPencil_eq`, `sourceWeightedPencil_zero_iff` | Every weighted domain vector; exact source base/domain conventions. |
| Original eigenvalue equation | `sourceWeighted_eigenvalue_iff` | `sourceOperator f = λ • sourceDomainInclusion f` iff the actual weighted free/potential equation. |
| Unique resonant/complementary decomposition | `exists_unique_sourcePQDecomposition` | Exactly two resonant amplitudes and one complementary remainder; both base and derivative weights. |
| The projected equations | `sourceWeightedPencil_zero_iff_PQ`, `sourceWeightedPencil_add_zero_iff_PQ` | Equivalent to the original pencil at every frequency; no smallness assumption. |
| Actual complementary inverse | `sourceComplementaryFreeInverse_equation`, `sourceComplementaryFreeInverse_unique` | Solves the original zero-potential source equation with Q_n right-hand side, uniquely on the complementary weighted domain. |
| Removed resonant modes | `sourceComplementaryFreeInverse_resonant`, `sourceLemma6_4_resonant_zero` | Both modes vanish under the complementary inverse and its potential composition, also at λ=nπ. |

## Lemma 6.4: exact shifts, operator, and endpoints

For physical coefficients f₋ and f₊, the exact source norm is

```
‖f‖_(w,p;i)^p = Σ_k w_(k+i)^p (|f₋(-k)|^p + |f₊(k)|^p).
```

`sourceShiftedNorm_formula` proves this identity. The first component has the
opposite physical modulation, as required by the signed Fourier convention.
`sourceLemma6_4_operator` identifies the bounded weighted map T_n with the
actual potential part of the original operator applied to A_λ⁻¹ Q_n in the
weighted derivative domain.

`sourceLemma6_4` proves the unchanged displayed estimate

```
‖T_n f‖_(w,p;i) ≤ c_p ‖φ‖_(w,p) ‖f‖_(w,p;−i)
```

for every 1≤p<∞. The constant depends only on p; there is no weight-, shift-,
or strip-index-dependent factor. The parameter may lie anywhere in the entire
closed strip U_n, including λ=nπ. `sourceLemma6_4_two` retains the printed
constant two. `sourceLemma6_4_one` proves that the endpoint admits constant one,
using reciprocal-symbol contraction and the exact component-sum norm. This
is a sufficient constant, not a claim of optimality.

The focused public checks cover the original eigenvalue/PQ equivalences,
complementary inverse equation and uniqueness, raw domain coefficients,
shifted coefficient formula, both endpoints, and the resonant free center.
The p=1 check with constant weight two also verifies that no extra w_0=1
hypothesis was introduced. No correction to Lemma 6.4 is required.

## Lemma 6.5: the exact induced norm and common contraction threshold

`sourceSquareNorm_le_iff` characterizes the norm of the conjugated square
by its bound on every input measured in the source's n-shifted pair norm.
`sourceLemma6_5` proves the displayed estimate

```
‖T_n²‖_(w,p;n) ≤ C_p ‖φ‖_(w,p)
  [ ‖φ‖_(w,p)/(1+|n|)^(1/p) + ‖R_n φ‖_(w,p)/w_n ].
```

The range is every 1≤p<∞. The tail retains |k|≥|n|, including equality;
there is no half-cutoff in this lemma. The estimate applies to every signed
n and the entire closed U_n, including λ=nπ, for the original source weight
class. It requires no w_0=1 normalization. No correction to the main lemma statement is needed. The final equality
in its proof has the separate correction recorded above.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Exact induced shifted norm | `sourceSquareNorm_le_iff` | Equivalent to the input-wise estimate for every nonnegative proposed bound. |
| Original unweighted operator | `sourcePotentialInverse_operator` | Exactly the actual source potential part applied to the complementary domain inverse, for arbitrary original input. |
| Constant-free norm identification | `sourceSquareNorm_one`, `sourcePotentialInverse_square_norm` | Unit shifts and unit weighting preserve the squared operator norm. |
| Same weighted and original operator | `sourcePotentialInverse_weightedInput` | Every weighted input, preserving all raw coefficients. |
| Common local half-contraction | `sourceLemma6_5_uniform_half` | One open convex neighborhood containing φ and zero, one positive cutoff, both norms, all sufficiently large signed n and all of U_n. |

## Following paragraph: compatible squared Neumann inverses

`sourceComplementaryCorrection` constructs (Id−T_n)⁻¹ on the original
unweighted pair space from smallness of its square. The formula theorem
identifies (Id+T_n)(Id−T_n²)⁻¹; the even inverse has a proved convergent
operator-norm series. The left and right inverse identities and uniqueness
hold for every right-hand side. `sourceComplementaryCorrection_weightedInput`
shows that the weighted inverse restricts to the same original solution.
`exists_uniform_sourceComplementaryCorrection` constructs both compatible
bounded inverses on one neighborhood and every sufficiently distant closed
strip. It does not assume that the norm of T_n itself is less than one.

The public API checks include p=1, constant weight two, index −3 and its
free center, exact boundary retention in both Fourier components, and
weighted/unweighted compatibility. The actual Q-solution and resonant
determinant reduction are the next source-level audit step.

## Q-equation: actual original-domain solution and uniqueness

`sourceUnitDomainEquiv` is a coefficient-preserving continuous linear
equivalence onto the entire original derivative domain. Thus the source
Q-solution covers every original-domain input, not merely a specified range.
The base and domain complementary projections commute with the coefficient
inclusions. `sourceQEquation_iff` identifies the actual original equation
with the weighted equation.

`sourceQSolution` constructs v=A_λ⁻¹ Q_n T̂_n Φu in the original derivative
domain. It belongs to Q_n, satisfies A_λ v=Q_n Φ(u+v), and is the unique
complementary solution for every u. `sourceQSolution_potential` proves
Φv=T̂_n T_n Φu with the actual original-source operators. Its weighted and
original small-square assumptions are equivalent by
`sourcePotentialInverse_square_norm`; no new smallness restriction is added.

## Lemma 6.6: actual determinant and eigenfunction reconstruction

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual two-mode matrix | `sourceResonantMatrix` | Matrix of the corrected resonant map in the physical first-component −n and second-component n basis. |
| Full domain reconstruction | `sourceResonantReconstruction`, `sourceResonantReconstruction_eq` | Resonant domain lift plus the actual unique Q-solution. |
| Original amplitudes retained | `sourceResonantReconstruction_coordinates` | Its first coefficient at −n and second coefficient at n are exactly the specified amplitudes. |
| Full differential residual | `sourceResonantReconstruction_residual` | The actual source pencil applied to reconstruction equals the synthesized matrix residual, with matching sign. |
| Exact kernel correspondence | `sourceResonantReconstruction_kernel_iff`, `sourceResonantReconstruction_ne_zero_iff` | Exactly matrix-kernel vectors reconstruct pencil-kernel vectors; nonzeroness is preserved. |
| Converse reconstruction | `sourceResonantReconstruction_of_eigenvector` | Every original-domain eigenvector is recovered from its own resonant coefficients. |
| Actual spectrum | `sourceLemma6_6` | Original source spectral-pencil noninvertibility iff the matrix determinant is zero. |
| Full-domain eigenvectors | `sourceLemma6_6_eigenvector` | Nonzero original derivative-domain pencil kernel iff determinant zero. |
| Local uniform threshold | `sourceLemma6_6_uniform` | One open convex neighborhood containing φ and zero, one positive cutoff, all sufficiently large signed n and the entire closed U_n. |

Every statement allows 1≤p<∞. The strip includes the free center λ=nπ;
no puncture, p>1 hypothesis, or max-norm threshold loss is introduced.
The public free-potential check derives spectral membership at every lattice
center, including n=0 and negative n, at p=1 directly from the matrix criterion.
The high-frequency uniform statement itself retains the source's N≥1.
No source correction is required for Lemma 6.6.

## Resonant matrix coefficients and the printed basis order

The source prints the basis in (plus, minus) order; the library uses the
physical first-component −n and second-component n modes in (minus, plus)
order. `sourceCorrectionMatrix_entry` identifies the entries with actual
original-source corrected potential coefficients, evaluated on actual
resonant domain vectors. The common diagonal is `sourceResonantA`;
`sourceResonantBPlus` and `sourceResonantBMinus` are the physical-order
entries (1,0) and (0,1).

`sourcePrintedResonantMatrix_form` restores the printed order:

```
S_n = [[ λ−nπ−a_n, −b_n⁺ ], [ −b_n⁻, λ−nπ−a_n ]].
```

Reversing both rows and columns preserves the determinant.
`sourceSpectrum_iff_resonantScalarEquation` identifies the actual original
periodic spectrum with (λ−nπ−a_n)²=b_n⁺b_n⁻.

## Lemma 6.7: valid symmetries and the missing hypothesis

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Equal correction diagonals | `sourceLemma6_7_i` | Every complex potential; no reality hypothesis. |
| Original physical star | `sourcePotentialStar_fst`, `sourcePotentialStar_snd` | Component exchange, complex conjugation, and reversal k↦−k. |
| Exact reality condition | `sourceHasRealitySign_iff`, `sourceHasRealitySign_one_iff` | Original φ*=εφ matches the weighted condition; ε=1 matches the existing real-type predicate. |
| Corrected conjugation identities | `sourceLemma6_7_ii` | Under ε²=1 and φ*=εφ, both a_n and b_n⁺ obey their printed conjugation formulas. |
| Real diagonal on the real axis | `sourceResonantA_im_eq_zero` | Both real and imaginary type. |
| Local uniformity | `sourceLemma6_7_uniform` | One open convex neighborhood containing φ and zero, one positive cutoff, both conjugate parameters, the full closed strips, and all 1≤p<∞. |
| Constant-potential calculation | `sourceResonantA_constant_center` | Actual original coefficient ab/(2πn) at every nonzero center under the small-square condition. |
| Arbitrarily distant counterexample | `exists_large_nonreal_sourceResonantA` | Same fixed original potential (1,i), positive n beyond every proposed cutoff, squared norm ≤1/2, nonreal diagonal. |
| Printed claim refuted | `not_sourceLemma6_7_printed_diagonal` | No individual frequency cutoff makes unconditional diagonal reality true for that fixed potential. |

The displayed Lemma 6.7(ii) on printed page 40 states diagonal reality before
introducing φ*=±φ for the off-diagonal claim. Its proof starts with that
hypothesis and uses it for both conclusions. The counterexample verifies
that the unrestricted diagonal clause is false. The corrected sufficient
hypothesis is exactly the one used in the source's proof; no characterization
of all potentials with real diagonal is claimed. See `SOURCE_ERRATA.md`.

## Equations (1.14)–(1.15): original parity expansions

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original operator powers | `sourcePotentialInverse_pow_unitInput` | Every natural power agrees under the coefficient-preserving unit-weight inclusion. |
| Actual potential input | `sourceResonantPotentialVector_eq` | Difference of the actual source operator at φ and zero, applied to the original resonant domain vector. |
| Even Neumann vector | `sourceResonantEvenVector_hasSum` | Convergence of actual original even powers under the small-square hypothesis. |
| Diagonal formula | `sourceEquation1_14` | Original T applied to the even vector, evaluated in the second component at n. |
| Off-diagonal formulas | `sourceEquation1_15_plus`, `sourceEquation1_15_minus` | Original T² applied to the even vectors; leading physical coefficients φ.snd(2n), φ.fst(−2n). |
| Convergent coefficient series | `sourceResonantA_hasSum`, `sourceResonantBPlus_remainder_hasSum`, `sourceResonantBMinus_remainder_hasSum` | Odd diagonal series and strictly positive even remainder series. |
| Vanishing discarded terms | `sourceResonantA_even_term_zero`, `sourceResonantBPlus_odd_term_zero`, `sourceResonantBMinus_odd_term_zero` | No small-square assumption is needed for the individual cancellations. |

## Lemma 6.8: original joint analytic functions

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual coefficient agreement | `sourceResonantFunctions_eq` | Total extensions recover all three original coefficients on the small-square domain. |
| Joint analyticity | `analyticAt_sourceCorrectionEntryFunction` | Analytic in the original potential and spectral parameter together. |
| Uniform full-strip analyticity | `sourceLemma6_8_analytic` | One open convex neighborhood containing φ and zero, N≥1, every signed index with |n|≥N, entire closed strips, and actual coefficient agreement. |
| Weight compatibility | `sourceCorrectionEntryFunction_weightedInput` | Exact entry equality with arbitrary spectral weights on the common correction domain. |
| Uniform weight compatibility | `exists_uniform_sourceResonantFunctions_weightedInput` | All three coefficient functions agree on every distant closed strip on one weighted neighborhood. |

These analytic and parity statements hold for all 1≤p<∞, including p=1.
They make no global analyticity claim for the total extensions outside the
correction domain. The public checks also recover the actual original scalar
spectral equation using the analytic functions and check both signed Fourier
remainders under weighted inclusion.

## Lemma 6.8: quantitative original full-strip tails

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual original suprema | `sourceResonantDiagonalSup`, `sourceResonantBMinusSup`, `sourceResonantBPlusSup` | Full closed strips; weighted off-diagonal remainders retain physical frequencies −2n and 2n. |
| Exact weighted agreement | `sourceResonantSup_eq_weighted`, `exists_uniform_sourceResonantSup_eq` | Equality of full strip images; no majorant substituted for the supremum. |
| Boundedness and domination | `exists_uniform_sourceCoefficientStripBounds` | All three images bounded above, suprema nonnegative, and every actual strip value dominated by its supremum. |
| Exact diagonal budget | `sourceDiagonalTailBudget_weightedInput` | Original unweighted component-sum norm and original Fourier tail, with no comparison constant. |
| Exact unit-weight budgets | `sourceOffDiagonalTailBudget_unit`, `sourceUnitWeighted_component_norms` | Both pair and distinguished component norms are the original norms. |
| All three signed tails | `sourceLemma6_8_summability` | Summable p-power tails with explicit diagonal and off-diagonal budgets, for every larger cutoff. |
| Common neighborhood | `sourceLemma6_8_quantitative` | Bounded-image assertions and all tail estimates on one open convex neighborhood containing φ and zero, N₀≥2. |
| Original unweighted neighborhood | `sourceLemma6_8_unweighted` | Neighborhood in the original `CoeffPair p` space, preserving the full period-two input. |

For the diagonal let B=‖φ‖_p and T=‖R_floor(N/2) φ‖_p. Its budget is

```
C_p B^p (B^p/N^δ + T^p),     δ=min(1,p−1).
```

For each weighted off-diagonal remainder, let W=‖φ‖_{w,p},
T_w=‖R_floor(N/2) φ‖_{w,p}, and B_±=‖φ_±‖_{w,p}. Its budget is

```
D_p B_±^p (W^(2p)/N^δ + T_w^(2p)).
```

The left-hand sides sum the p-th powers of the actual suprema over all
integer n with |n|≥N. The off-diagonal supremum already includes w(2n),
so the weight is raised to p along with the remainder norm. The proof uses
strict 1<p<∞, not the analytic endpoint p=1. The earlier floor-half cutoff
includes its boundary. The full-cutoff and ceiling-half original-supremum
versions below retain all three quantitative estimates and strip bounds.

The page-41 printed off-diagonal display has neither these left-hand powers
nor the same inner norm. The formal result follows the p-power and full-pair
form of the concluding source proof. The locally uniform unpowered display
is refuted below; see `SOURCE_ERRATA.md` for the precise distinction.

## Lemma 6.8(ii): formal counterexample to the missing powers

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Exact finite correction | `cubicPotential_bplus`, `cubicPotential_bplus_center` | First mode 2n=a, second mode zero=b; the center coefficient is ab²/(2πn)² for n≠0. |
| Original source coefficient | `sourceCubicPotential_remainder_center`, `sourceCubicPotential_remainder_norm` | Actual original analytic remainder; equal positive amplitudes give t³/(2πn)². |
| Exact original norm | `sourceCubicPotential_norm_sq` | At p=2, squared norm is |a|²+|b|². |
| Sextic budget | `sourceUnpoweredRemainderBudget_cubic_le` | Budget ≤16C t⁶ even with the full inner pair norm, independently of the Fourier-tail cutoff. |
| Arbitrarily small witnesses | `exists_sourceRemainder_exceeding_unpowered_budget` | Every original open neighborhood of zero and every common cutoff; small correction and bounded distant strip images are included. |
| Unpowered sum refuted | `not_sourceLemma6_8_unpowered_sum` | Complete signed-tail sum cannot obey even the enlarged inner-norm budget locally uniformly. |
| Literal budget refuted | `not_sourceLemma6_8_printed_sum` | Positive-remainder part, unit weight, p=2, arbitrary tail-cutoff function κ(N); includes both half-cutoff roundings. |

The contradiction is cubic versus sextic scaling at a fixed chosen distant
index, with amplitude tending to zero inside the neighborhood. The potential
may depend on that index and amplitude. This does not establish failure for
one fixed potential beyond every individually chosen cutoff. The exact
coefficient formulas themselves allow every finite 1≤p<∞; the local
counterexample and sum negations are proved at p=2.

Changing the inner norm alone cannot rescue the unpowered display. The
separate argument below tests the positive-component factor after the
p-powers have been restored.

## Lemma 6.8(ii): independent component-factor counterexample

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Reversed two-mode calculation | `reverseCubicPotential_bminus`, `reverseCubicPotential_bminus_center` | First mode zero=a, second mode −2n=b; negative center coefficient a²b/(2πn)². |
| Actual source remainder | `sourceReverseCubicPotential_remainder_center`, `sourceReverseCubicPotential_remainder_norm_sq` | At a=1, b=t, squared remainder t²/(2πn)^4. |
| Exact component norms | `sourceReverseCubicPotential_component_norms` | Original first norm ‖a‖ and second norm ‖b‖. |
| Fixed background | `sourceReverseCubicPotential_distance_sq` | Original p=2 squared distance to the same constant potential (1,0) is ‖b‖² for a=1. |
| Background removed by the tail | `sourceReverseCubicPotential_tail_norm_sq_le` | Every cutoff K≥1 gives squared tail norm ≤‖b‖². |
| Quartic budget | `sourcePositiveComponentBudget_reverse_le` | The printed negative-remainder component budget is at most 2C t⁴. |
| Arbitrarily close witnesses | `exists_sourceRemainder_exceeding_component_budget` | Every original open neighborhood of (1,0), every common cutoff, small correction, and bounded distant strip images. |
| Correctly squared sum refuted | `not_sourceLemma6_8_positive_component_sum` | Unit weight, p=2, complete signed tail, any κ(N)≥1 for N≥2; includes floor and ceiling half-cutoffs. |

The left-hand powers are correct in this counterexample. The budget being
tested is specifically

```
C (‖φ_+‖^4/N + ‖R_K φ‖^4) ‖φ_-‖².
```

At the constructed potentials, the first component is fixed, the second
component has size t, and the cutoff removes the fixed background. Thus
its quartic order cannot dominate the actual quadratic squared remainder.
This establishes a separate defect in the component factor, without
reusing the unpowered cubic-versus-sextic comparison.

The coefficient identities include p=1; the counterexample and sum
negation use p=2. This is a locally uniform failure near a fixed background,
not an assertion that one fixed perturbed potential defeats every individual
cutoff. The full pair norm is a proved sufficient replacement, with no
claim of optimality or a sharp constant.

## Lemma 6.9: original determinant roots and corrected displacement

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original scalar determinant | `sourceResonantDeterminantFunction_eq_det`, `sourceResonantDeterminantFunction_eq_printed_det` | Equals the actual reduced matrix determinant in both basis orders on the correction domain. |
| Actual original spectrum | `sourceResonantDeterminantFunction_spectrum_iff` | Zeros are precisely noninvertible original period-two pencils on the strip. |
| Joint analyticity | `analyticAt_sourceResonantDeterminantFunction` | Original component-sum potential norm and spectral variable, including p=1 on the correction domain. |
| Genuine product supremum | `sourceResonantBProductSup`, `SourceResonantStripControl.product_bounds` | Full closed unbounded strip; bounded image, nonnegative supremum, pointwise domination. |
| Cauchy bound | `SourceResonantStripControl.deriv_bound` | Diagonal derivative norm at most 1/8 on the open π/4 disk. |
| Counted roots | `SourceResonantRootPair`, `.zero_count` | No other strip zeros; scalar order equals the two-element multiset's count; total count exactly two, including coincident roots. |
| Algebraic multiplicities | `SourceResonantRootPair.multiplicity_eq_count` | Same coefficient-preserving operator input `CoeffPair.toMax p φ`, without period doubling. |
| Localization and gap | `SourceResonantRootPair.left_bound`, `.right_bound`, `.gap_le` | Distance at most 3π/32; squared gap at most six times the actual product supremum. |
| One original neighborhood | `sourceLemma6_9` | Finite p>1; joint analyticity, strip control, counted pairs, summability and corrected power budget, for all later signed-tail cutoffs. |
| Label independence | `SourceResonantRootPair.eq_or_swap`, `sourceResonantRoot_displacementTail_eq` | Arbitrary exchanges at each mode preserve the complete displacement tail, including double roots. |
| Full signed two-root sum refuted | `not_sourceLemma6_9_printed_pair_sum` | At p=2, no locally uniform printed budget for the full signed sum of both counted scalar roots. |

The main theorem's displacement budget is exactly
`sourcePeriodTwoDisplacementBudget`, displayed above in the Proposition 6.1
audit. It includes the additive leading Fourier-tail term and uses floor(N/2).
The new `sourceLemma6_9_fullCutoff` and `sourceLemma6_9_ceilingHalf` retain
all its original determinant, root and neighborhood data with sharper tails.
The printed formula is not claimed. The new counterexample entry point
applies the previous actual-source spectral witness to these scalar root
pairs. Its failure is locally uniform, not a fixed-input assertion about
all individual cutoffs.

The literal display on page 43 has the positive-index range n≥N and repeats
the ξ⁺ displacement twice. The signed two-root refutation alone does not
establish that exact statement; the additional results below now do.

The neighborhood is open and convex, contains the specified original input
and zero, and is chosen before every distant index and every later cutoff.
Each pair exhausts both determinant zeros and original spectral points on
the whole strip. The proof uses the existing branch-free root-gap argument;
it requires neither a global square-root branch nor analytic root labels.
Finitely many central labels remain unspecified by this high-frequency result.

## Lemma 6.9: both positive-index sums and the literal repeated label

The display on printed page 43 sums over n≥N and repeats the ξ⁺ term twice.
The new results treat that literal display as well as the positive-index
sum of both roots, without silently changing the printed label.

[SourceLemma6_9PositiveCorrected.lean](../NLS/ZakharovShabat/SourceLemma6_9PositiveCorrected.lean)
proves `sourceLemma6_9_corrected_positive`. The same original determinant,
joint analyticity, full-strip control, counted pairs and open convex
neighborhood from `sourceLemma6_9` now give both positive-index estimates
at every later cutoff. The two-root sum is bounded by the existing corrected
`sourcePeriodTwoDisplacementBudget`; the repeated-first-root sum is bounded
by twice that budget. This factor follows from termwise domination and is
not claimed sharp. These bounds retain the additive leading-tail term and
the earlier floor(N/2) convention.

[SourceLemma6_9LiteralSum.lean](../NLS/ZakharovShabat/SourceLemma6_9LiteralSum.lean)
proves `not_sourceLemma6_9_printed_duplicated_positive_sum`. The resonant
input has actual spectral points nπ±t. Any two labels exhausting this strip
spectrum must put one of these points first, so its squared displacement is
t² whichever ordering is chosen. The printed Hilbert budget is at most
24C t⁴. The theorem therefore refutes the literal positive-index sum with
the first label repeated, locally uniformly at zero, for every choice of
actual counted determinant roots. It uses the printed ceiling-half budget.
It makes no claim that every individually chosen fixed-input cutoff fails.

The public examples distinguish two-root sums from both repeated-label
choices, check both corrected bounds at p=3 with the same counted roots,
and exhibit a violating repeated-label sum beyond every proposed cutoff.
This resolves the recorded literal-range and repeated-label proof gap;
it does not infer which label the author intended to print.

## Full-cutoff and ceiling-half completion

[FullCutoffSummability.lean](../NLS/ZakharovShabat/FullCutoffSummability.lean)
retains the component Fourier tails at N in the diagonal and off-diagonal
power-sum bounds. The exponent-only constants are unchanged. The earlier
proofs weakened these component tails to floor(N/2); no comparison from
the old final budget to a smaller new budget is assumed.

[SourceCoefficientFullCutoffs.lean](../NLS/ZakharovShabat/SourceCoefficientFullCutoffs.lean)
transports those bounds to the actual original full-strip suprema.
[SourceCoefficientCeilingCutoffs.lean](../NLS/ZakharovShabat/SourceCoefficientCeilingCutoffs.lean)
gives the ceiling-half versions of Lemma 6.8, including all three summable
p-power tails, bounded strip images, exact original diagonal and weighted
component norms, and an original unweighted-input neighborhood.

[FullCutoffRootMajorants.lean](../NLS/ZakharovShabat/FullCutoffRootMajorants.lean)
combines the stronger component estimates with the additive leading term.
[FullCutoffSpectralRoots.lean](../NLS/ZakharovShabat/FullCutoffSpectralRoots.lean)
retains the same actual root sequences, spectral equivalence, analytic and
algebraic multiplicities, midpoint and squared-gap identities.

[SourceFullCutoffEstimates.lean](../NLS/ZakharovShabat/SourceFullCutoffEstimates.lean)
proves the original corrected Propositions 6.1/6.3 and Lemma 6.9 with the
full Fourier tail R_N. Their original period-two norms, source pencil and
determinant, and one open convex neighborhood for every later cutoff are
preserved. The weighted gap is the actual contour squared gap.

[SourceCeilingCutoffEstimates.lean](../NLS/ZakharovShabat/SourceCeilingCutoffEstimates.lean)
then proves `sourceProposition6_1_corrected_ceilingHalf`,
`sourceProposition6_3_corrected_ceilingHalf`, and `sourceLemma6_9_ceilingHalf`.
Here ceiling(N/2) is represented by (N+1)/2 in natural division, with its
boundary mode retained. Since (N+1)/2<=N, tail monotonicity gives these
corollaries from the stronger full-cutoff estimates. The additive leading
tail is still necessary; all printed-bound counterexamples above remain.
Public examples check the odd boundary N=3 and original p=3 spectral,
intrinsic-gap and coefficient-supremum conclusions.

## Stronger cutoff bounds for the fixed canonical sequences

[SourcePeriodTwoCanonicalCutoffs.lean](../NLS/ZakharovShabat/SourcePeriodTwoCanonicalCutoffs.lean)
transfers the stronger corrected full-Fourier-cutoff displacement estimate
to the complete canonical eigenvalue sequences. The signed sum over |n|≥K
and the literal positive-index sum over n≥K satisfy the full-cutoff budget;
the positive sum also satisfies the ceiling-half budget on that same
neighborhood. These budgets retain the additive leading Fourier-tail term.

[SourceCanonicalWeightedGapTails.lean](../NLS/ZakharovShabat/SourceCanonicalWeightedGapTails.lean)
identifies both canonical gap-tail functions with the corresponding intrinsic
contour gap tails beyond one common cutoff. For every source weight and
finite p>1, `sourceProposition6_3_canonical_signed` and
`sourceProposition6_3_canonical_positive` give the full-cutoff and ceiling-half
corrected bounds and arbitrarily small tails on one open convex neighborhood
containing the original weighted input and zero.

`sourceProposition6_3_canonical_gap_mem` proves weighted ℓᵖ regularity of
the actual canonical gap at every integer index. Its finite central part
uses actual ordered eigenvalue pairs; it is not defined by choosing square
roots of the individual central-circle contour quantities. The tail proof
uses the eventual contour identification and adds the finite central part.

The cutoff condition remains K>N₀. No even-support assumption or normalization
w(0)=1 is required. Three public examples check a weight with w(0)=2, the
vanishing of both free gap tails, and simultaneous positive displacement and
gap bounds for the same fixed labels on a single original-input neighborhood.
The printed quantitative counterexamples and the qualifications concerning
central contours, individual-label continuity, and sharp constants remain.

## Remaining source audit

The prior ceiling-cutoff qualification is now closed for the corrected
Propositions 6.1/6.3 and Lemmas 6.8/6.9. Theorem 7.1 is audited in
[Section 7](SECTION_7.md), and Lemma 8.1's discriminant assertions are
already covered in [Section 8](SECTION_8.md). These results and the
candidate-label inventory do not certify the dissertation complete.
