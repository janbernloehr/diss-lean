# Section 10: potentials of almost real type

## Ordered comparison through Remark 10.9

Remark 10.9's ordered comparison now records the corrected signed term

    sum_(m!=n) gamma_m^2/[8*(tau_m-z)^2].

The actual supremum of the remainder over each original disk belongs to
l(p/4), locally uniformly in the original source topology for every finite
p>1. The coefficient one eighth and the moving midpoint denominator are
retained. This includes the central disks, collapsed gaps and exponents
below one, and supplies a stronger remainder than the printed sum of classes.

The existing optimality theorem covers every finite p>2 and every r<p/2.
In any open source neighborhood of zero, one actual real source and one
original isolating family make the squared gaps, signed lattice row and
literal quotient supremum belong to l(p/2) and fail membership in lr.
The witness may depend on r; the assertion is about the general exponent.
The actual inverse chart preserves the prescribed neighborhood, reality
and spectral actions. No new refutation is added.

This step changes documentation and comparison records only. The Lean
sources and dependency lock exactly match commit `91abb08`, whose completed
`./scripts/check.sh` run passed 8,511 build jobs, 7,580 public examples and
the transitive axiom audit of 44,300 NLS declarations, with 21 inherited
warnings. That validation is reused; the module hashes, declaration
references, source-review integrity and documentation links are checked
for this publication.

The [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md) now covers
41 of 52 groups: 33 matched and eight corrected occurrences. Eleven remain
pending, beginning with S10-042 and Lemma 10.10. Section 7's physical NLS
Dirichlet motion and unrestricted psi uniqueness, the exact cited 2014
construction, Appendix G.2 norm interpretation and the broader source
inventory remain unresolved.

The [exact Taylor theorem](../NLS/ZakharovShabat/SourceRemark10_9Taylor.lean)
and [linear-term identity](../NLS/ZakharovShabat/SourceMidpointQuotientTaylorGeometry.lean)
give the corrected formula. The
[optimality theorem](../NLS/ZakharovShabat/SourceRemark10_9Optimality.lean)
uses the existing [actual-source construction](../NLS/ZakharovShabat/SourceSquaredGapSharpness.lean)
and [inverse chart](../NLS/ZakharovShabat/SourceBirkhoffInverseChart.lean).
These are comparisons of the existing public proofs; the historical
counterexample entries below retain their original scope.

Earlier milestone entries retain their historical scope.

## Previous comparison milestone: through Lemma 10.8

Eight positive theorems in two modules expose the literal proof estimates
in Lemma 10.8. The principal inverse-square-root estimate holds with the
printed constant one on the closed complex half-unit ball. Its finite
product bound is exp(sum |x_m|)-1. The near/far gap bounds use the original
lp norm of the unsquared gaps, with the factor one quarter retained in the
near term. The original disks keep their supplied separation constant.

The literal unordered inverse-square-root product is identified through
the actual midpoint numerator. Its disk supremum on the common tail has
one uniformly bounded l(p/2) coefficient, including exponents below one.
The tail coefficient is zero on the finite head; the full quotient theorem
separately retains every original central disk. Two integration examples
check a complex radicand of norm one half, negative-index near/far bounds,
and the actual product and supremum together at exponent 3/4.

Validation: `./scripts/check.sh` passes with 8,511 build jobs, 7,580
public examples and a transitive axiom audit of 44,300 NLS declarations.
The 21 inherited warnings are unchanged; the new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md) now compares
40 of 52 groups: 33 matched and seven corrected occurrences. The free-sine
consequence retains its stronger l(p/2)+l(1+) decomposition. The existing
arbitrary-numerator topology correction remains: original lp local
uniformity for q>=p, and explicit bounded lq offset families for q<p.
The near/far proof uses the corrected lp gap norm. No new refutation is added.

Twelve groups remain pending, beginning with S10-041 and Remark 10.9.
Section 7's physical NLS Dirichlet motion and unrestricted psi uniqueness,
the exact cited 2014 construction, Appendix G.2 norm interpretation and
the broader source inventory remain unresolved.

The [scalar and near/far module](../NLS/ZakharovShabat/SourceLemma10_8ProofBounds.lean)
proves the printed scalar constant one directly. The older constant-two
estimate remains a valid looser bound. For the near/far split, lp applies
to gamma and l(p/2) applies to gamma squared. No stronger norm of the
unsquared gaps is assumed.

The [literal product module](../NLS/ZakharovShabat/SourceGapCorrectionProductEstimate.lean)
uses the actual midpoint displacement, so its unordered product agrees
with the source factors. A common l(p/2) row majorant bounds the actual
least upper bound on each distant original disk. The common neighborhood
works for complex sources, and the proof does not assume analyticity of
ordered spectral endpoints. The full-disk quotient and free-sine results
below retain the finite head and their exact sequence decompositions.

Earlier milestone entries retain their historical scope.

## Previous comparison milestone: through Lemma 10.7 and Figure 2.4

The ordered comparison now includes the canonical root in equation (2.13),
Lemma 10.7, equation (2.14) and Figure 2.4. The first 32 of 52 groups are
compared: 28 matched and four corrected occurrences. These four new groups
match the existing proofs.

The literal symmetric product retains the factor 2*i and pi_0=1. Its square
is the discriminant radicand off all gaps, and its free value at pi/2 is -2*i.
The same common source domain and original closed-disk complement support
joint analyticity and locally uniform convergence. A collapsed gap admits
the fixed-source analytic continuation 2*i*(tau_n-z)*f_n on the entire
selected disk, with a simple zero. On noncollapsed gaps, the two continuous
side values are opposite and vanish at both endpoints. Figure 2.4's real
gap signs and imaginary band signs hold for every signed index.

This step changes documentation and source-comparison records only. The Lean
sources and dependency lock exactly match commit `115ebf6`, whose completed
`./scripts/check.sh` run passed 8,509 build jobs, 7,578 public examples and the
transitive axiom audit of 44,286 NLS declarations, with 21 inherited warnings.
That validation is reused; no new full build is claimed. The current module
hashes, declaration references, source-review integrity and documentation
links are checked separately.

Twenty groups remain pending in the [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md),
beginning with S10-033 and Lemma 10.8. Section 7's physical NLS Dirichlet motion
and unrestricted psi uniqueness, the exact cited 2014 construction,
Appendix G.2 norm interpretation and the broader source inventory remain
unresolved.

The [product construction](../NLS/ZakharovShabat/SourceCanonicalRootProduct.lean)
and [unchanged-domain package](../NLS/ZakharovShabat/SourceLemma10_7.lean)
retain the preceding quotient theorem. The
[boundary data](../NLS/ZakharovShabat/SourceCanonicalRootBoundaryDomain.lean)
cover oriented side approaches for complex sources and the closed gap
parameter interval. The [normalization and signs](../NLS/ZakharovShabat/SourceCanonicalRootNormalization.lean)
include the central and negative indices. Strict gap signs concern the
interior of a noncollapsed real gap; the figure specifies phases, not unit
magnitudes. Collapsed continuation is at a fixed source, without claiming
a joint continuation through nearby reopened gaps.

Earlier milestone entries retain their historical scope.

## Previous comparison milestone: through Corollary 10.6

The Lemma 10.5 factor proof now retains the actual quadratic remainder
Q_k=k^2 times the square-root correction, with Q in l(p/2). Pairing k and -k
cancels the free spectral term. The paired linear error has the exact
lp/k+l(p/2)/k^2 form and also a single lp/k representation. The cross term
has bounded/k^2+l(p/2)/k^3+l(p/4)/k^4 coefficients, including exponents below one.

One source neighborhood and cutoff give the actual-gap bound
|Q_k| <= |gamma_k^2|/(2*pi^2) uniformly on each bounded spectral region.
Individual factor errors are bounded on compact subsets of their gap
complement. One module adds nine positive theorems. Two integration examples
at p=3/2 combine the refined terms in the actual paired factor and check
vanishing free remainders with the positive +/-2 block excess at z=i.

Validation: `./scripts/check.sh` passes with 8,509 build jobs, 7,578
public examples and a transitive axiom audit of 44,286 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md) now compares
28 of 52 groups: 24 matched and four corrected occurrences. The existing
proof-index correction a_-m to a_-k is applied to the cross term. Lemma 10.5
retains the exact symmetric normalization, locally uniform paired convergence,
nonvanishing and unchanged source domains. Corollary 10.6 retains all lp root
displacements, including collisions, and its literal unordered quotient
product on the printed closed-disk domain. No additional refutation is added.

Twenty-four groups remain pending, beginning with S10-029 and equation (2.13).
Section 7 physical NLS Dirichlet motion and unrestricted psi uniqueness,
the exact cited 2014 construction, Appendix G.2 norm interpretation and the
broader source inventory remain unresolved.

The new [refined error module](../NLS/ZakharovShabat/SourceStandardRootRefinedErrors.lean)
keeps the actual squared gap in the tail estimate. A finite-head/tail split
proves Q in l(p/2), and reflection plus the scalar Holder product proves the
l(p/4) coefficient. These sequence memberships are pointwise in the source
and spectral parameter. The pre-existing common tail bounds separately prove
local uniform convergence of the paired products; no full-family uniform
norm bound for the refined coefficient sequences is claimed here.

The unchanged product normalization and denominator arguments below identify
all omitted products and their literal quotient, on the same common domain.
The new comparison checks their hypotheses, signs, closed-disk bars and
sequence exponents against the rendered source on printed p.57.

Earlier milestone entries retain their historical scope.

## Previous comparison milestone: through Lemma 10.4

The ordered comparison now includes the standard-root definition, Lemma 10.3,
its boundary values and Lemma 10.4. The first 22 of 52 groups are compared:
19 matched and three corrected occurrences. Two of the corrections replace
the printed denominator w_m with the selected root w_n in Lemma 10.4 and its
proof; the earlier real-type-domain correction remains.

The reviewed proofs retain the same common source domain, the exact isolation
constant, every signed index and general finite piecewise C1 contours with
winding one. Side traces include both endpoints. The endpoint estimate uses
the sharp constant one for continuous data on the gap, with genuine integrability
and improper limits. The double truncation uses one common epsilon.

This step changes documentation and source-comparison records only. The Lean
sources and dependency lock exactly match commit `392775f`, whose completed
`./scripts/check.sh` run passed 8,508 build jobs, 7,576 public examples and the
transitive axiom audit of 44,255 NLS declarations, with 21 inherited warnings.
That validation is reused; no new full build is claimed. Current source-review
integrity, resolved declaration references and documentation links are checked.

Thirty groups remain pending in the [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md).
Continue with S10-023, deleted standard-root products and Lemma 10.5.
Section 7's physical NLS Dirichlet motion and unrestricted psi uniqueness,
the exact cited 2014 construction, Appendix G.2 norm interpretation and the
broader source inventory remain unresolved.

Earlier milestone entries retain their historical scope.

## Previous comparison milestone: through Lemma 10.2

The literal scalar contour in Lemma 10.2 now recovers every periodic
endpoint power sum, with the exact factor 2*Delta*DeltaPrime and normalization
1/(2*pi*i). A weighted argument principle counts analytic orders, which are
identified with the actual algebraic multiplicities of the isolated endpoint
pair. Collapsed gaps contribute twice. Every original isolating family is
supported, including central and negative indices.

Joint analytic integration proves analytic source dependence directly. One
fixed family of circles works for all nearby sources, indices and powers;
any existing Lemma 10.2 common domain is retained. Three modules add eight
positive theorems. Two integration examples at p=3/2 recover the signed
cotangent moments at -pi and the analytic cubic moment in midpoint/gap form.

Validation: `./scripts/check.sh` passes with 8,508 build jobs, 7,576
public examples and a transitive axiom audit of 44,255 NLS declarations.
The 21 inherited warnings are unchanged; the new modules and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The first twelve groups in the [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md)
are compared: eleven matched and one corrected. The correction reuses the
real-type source locus in Lemma 10.1; no new refutation is added. Common-domain
simplicity, exact disk separation and full lp/l(p/2) sequence estimates retain
their original scope. Forty later Section 10 groups remain pending comparison.

Continue with S10-013, the standard root and Lemma 10.3. Section 7's physical
NLS Dirichlet motion and unrestricted psi uniqueness, the exact cited 2014
construction, Appendix G.2 norm interpretation and broader source inventory
remain unresolved.

The [weighted argument principle](../NLS/ComplexAnalysis/WeightedArgumentPrinciple.lean)
removes the finite logarithmic principal parts, multiplies the analytic
remainder by an analytic weight and applies Cauchy's theorem. Each pole
contributes its weight times its analytic order. The
[actual contour formulas](../NLS/ZakharovShabat/SourceSection10PowerContours.lean)
identify those orders with the two canonical endpoint slots using the
original algebraic multiplicity enumeration. No periodic simplicity
assumption is needed.

The [analytic contour package](../NLS/ZakharovShabat/SourceSection10PowerContourAnalytic.lean)
proves nonvanishing on each original circle throughout the chosen source
neighborhood. The integrand is jointly analytic on its nonzero-denominator
domain. Fixed-circle analytic integration then gives the source analyticity
in the displayed proof, independently of endpoint-label analyticity.
`SourceLemma10_2Data.exists_power_sum_contours` retains any existing common
domain and chooses the local family before all indices and powers.

The following named-statement entries retain their historical audit scope;
they do not discharge the eleven ordered groups still pending.

This audit follows the source statements and proofs on printed pp. 54–60.
The neighborhood assertion is proved with the real-type locus used in
the proof. The printed all-complex version has a formal counterexample.
Lemmas 10.2 and 10.3 are covered on the same common domain, including the
preceding simple-root assertions and general piecewise C¹ contours.
Lemma 10.4 is covered with the selected-root index correction, actual
side traces, improper endpoint limits and the sharp constant one.
Lemma 10.5 is covered on the unchanged common domain, with literal
symmetric cutoffs, paired absolute convergence, both analytic domains
and nonvanishing. Corollary 10.6 is covered with its full displacement
space, literal unordered quotient product and printed closed-disk domain.
Equation (2.13), Lemma 10.7 and equation (2.14) are covered on the same
common domain, including collapsed gaps, actual side limits and Figure 2.4
on the real locus. Lemma 10.8 has full-disk supremum decompositions and
precise bounded-offset estimates. Its printed original-topology uniformity
claim is refuted at p=4, q=1 by a formal quotient counterexample. The
free-sine consequence is now proved in the stronger locally uniform
ℓ(p/2)+ℓ(1+) class on every original disk. Remark 10.9 now has a proved
ℓ(p/4) supremum remainder after its exact moving-denominator Taylor term.
The printed integer-kernel replacement is refuted by an actual real
source counterexample at p=8, arbitrarily near zero. Full p/2 optimality
is now proved for every finite p>2 and every proposed stronger exponent,
using actual real sources and original disk families. Remark 10.9 is
resolved with the corrected expansion. Lemma 10.10 is now covered on
the unchanged common domain, with actual analytic coefficients and one
locally uniform full-sequence bound. Equation (2.15) is now covered with
its literal absolutely convergent product, exact -i normalization, and
spectral and joint analyticity on the original domains. Lemma 10.11(i)
is now covered by one explicit analytic extension through every collapsed
gap on the unchanged source domain. Original circle periods and arbitrary
piecewise C¹ closed contours in the original cut disks now have zero
integral throughout that domain. The endpoint-path assertion is now
covered for the usual piecewise C¹ path class, with independently
truncated improper endpoint integrals and full limits at complex or
collapsed endpoints. The next source section is Section 11.

## Lemma 10.1: precise domain and quantifiers

For every finite p>1, `sourceLemma10_1` constructs one open connected
set W in the original complex coefficient source space, containing the
entire real-type source locus. For each ψ∈W it supplies an open connected
V with ψ∈V⊆W. The frozen base φ is real-type, but ψ and the other sources
in V need not be real-type.

One N, one positive central margin ε≤π/4, one real c≥1, and the family
`sourceIsolatingDisc hp hp1 φ N ε` are chosen for this V. These choices
precede every nearby source χ∈V and every signed spectral index. They are
not chosen separately for different χ or indices.

`SourceIsolatingNeighborhoods` records the literal conditions:

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Disks centered on the real line | `.discs` | Each disk is `ball (a : ℂ) r` with a real and r>0. |
| Full periodic gap containment | `.gap` | The entire straight segment between the actual canonical periodic endpoints, at every nearby complex source. |
| Dirichlet, Neumann, and critical roots | `.cluster` | All five actual cluster coordinates, including both periodic endpoints, for all χ∈V and all signed n. |
| Two-sided distance estimate (2.7) | `.set_distance` | One c≥1 gives c⁻¹\|i−j\|≤dist(D_i,D_j)≤c\|i−j\| for every i≠j. |
| Exact free tail | `.tail` | One cutoff, with D_n exactly the open radius-π/4 disk about nπ whenever \|n\| exceeds it. |
| Pairwise disjointness | `.disjoint` | Derived from the strictly positive lower bound; no extra hypothesis. |

The package additionally gives the same two-sided bounds for every pair
of points in the distinct disks through `.pointwise_distance`.
Collapsed periodic gaps are allowed; no simplicity is assumed here.

## Literal set distance and positive separation

`spectralSetDistance s t` is `Metric.infDist 0` of the image of subtraction
on s×t. `spectralSetDistance_isGLB` proves that, for nonempty s,t, it is the
greatest lower bound of the set of all actual `dist z w` with z∈s,w∈t.
Thus it is the source's infimum distance, not the Hausdorff distance.
The disks are nonempty because every radius is strictly positive.

Pairwise disjoint open disks alone would not suffice: tangent open disks
can have zero infimum distance. The construction first obtains disjoint
disks with central margin ε, then replaces each central margin by ε/2.
The tail disks remain unchanged. Continuity of all five coordinates at
the real base and a finite intersection give a neighborhood where the
nearby central clusters still fit in the smaller disks. Intersecting with
the original neighborhood retains all tail inclusions, and a contained
source norm ball supplies connectedness.

For a pair with at least one central index, shrinking loses at least
ε/2 from the sum of radii. `shrunk_disjoint_balls_pointwise_separation`
turns the original center-distance inequality into this positive
pointwise separation. For two tail indices, the free-disk estimate gives
at least (π/2)\|i−j\|, which also dominates ε/2. Thus all distinct pairs
have one positive lower bound δ=ε/2, before converting to index scale.

`exists_source_isolating_lattice_offset_bound` supplies R≥0 such that
every z∈D_n satisfies \|z−nπ\|≤R. With t=\|i−j\|≥1 and d=dist(z,w),
triangle inequalities give

```
πt ≤ 2R+d,       d ≤ πt+2R,       δ ≤ d.
```

`exists_index_comparison_constant` takes
c=max(1,max((1+2R/δ)/π,π+2R)) and derives c⁻¹t≤d≤ct. Passing the lower
bound to the infimum and choosing any point pair for the upper bound
gives the literal set-distance estimate. This includes central/central,
central/tail, and tail/tail pairs with the same c.

## Global connected neighborhood

The local neighborhoods cover the real-type locus. Their union is open.
Each local set is connected and meets that connected locus at its real
base. Adjoining the locus to each local set produces a family with a
common nonempty intersection; its union is connected and equals the
original union. Every point in the union retains one local family and
one local neighborhood contained in W.

The result also exposes the frozen real base and the explicit N,ε
construction, so later contour arguments can use the existing actual
isolating-center and radius APIs.

## The printed all-complex domain is false

The statement on p. 54 says a neighborhood of FL_c^p. The preceding
paragraph, the base potentials in the proof, and the final union use
FL_r^p. The corrected theorem above uses FL_r^p; the printed alternative
is independently refuted in `SourceIsolatingDomainCounterexample.lean`.

`sourceCollisionPotential` is the constant source (iπ,iπ). Its only
nonzero source Fourier coefficients are the two zero modes, and its
period-doubled operator potential is exactly `constantCollisionPotential`.
For raw frequency k the operator block is

```
L_k = [ -πk   iπ ]
      [  iπ   πk ].
```

The exact spectral-pencil calculation proves that the block is
square-zero at k=+1 and k=−1. `collisionMode_mem_root_two` puts every
vector in either two-dimensional block in the second actual periodic
root space. `collisionFourModeEmbedding_injective` proves independence
of all four component modes. The root-space definition of algebraic
multiplicity then yields `four_le_sourceCollisionMultiplicity`.
Only a lower bound of four is needed or claimed.

Conversely, `periodicMultiplicity_le_two_of_disjoint_clusters` uses the
actual canonical enumeration with algebraic multiplicity. For a spectral
point in one assigned set, disjointness excludes occurrences in every
other indexed pair. Its total multiplicity is therefore bounded by the
two slots of that one pair. This argument works for arbitrary sets; no
ball shape, real centering, or neighborhood topology is needed.

Consequently, `sourceCollisionPotential_not_isolatable` rules out any
disjoint isolating family for this source.
`not_sourceLemma10_1_all_complex` refutes a domain containing all complex
sources at every finite p>1. The correction is recorded in
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md).

## Lemma 10.1 verification

The public examples exercise the global theorem at p=3/2, zero-potential
local families and collapsed gaps, all ordinary cluster coordinates,
full gap segments, central and negative-index infimum distances, positive
real-centered disks, exact free tails, and disjointness. A tangent-disk
example checks that shrinking creates positive separation. A separate
example exposes the greatest-lower-bound characterization of set distance.
The counterexample checks include the multiplicity lower bound,
four-coordinate injectivity below two, impossibility of arbitrary
disjoint shapes, and negation of the printed all-complex domain.


## Lemma 10.2: one common analytic domain

For every finite p>1, `sourceLemma10_2` constructs W, open and connected
in the original complex coefficient space, with the entire real-type
locus contained in W. All fields of `SourceLemma10_2Data` use this same W:

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Retained Lemma 10.1 isolation | `.isolation` | Each ψ∈W has an open connected V with ψ∈V⊆W, one disk family and one constant satisfying all quantitative isolation conditions. |
| Periodic power sums, clause (i) | `.power_sums` | Actual left/right endpoint powers, for all signed n and all natural k (including k=0). |
| Midpoint and squared gap, clause (ii) | `.midpoint`, `.squared_gap` | Complex analytic at every point of W, including collapsed gaps. |
| Locally uniform sequence asymptotics | `.uniform_sequences` | One neighborhood, cutoff and bound for both complete sequences and all sufficiently distant tails. |
| Joint pair factor, clause (iii) | `.joint_factor` | Complex analytic on ℂ×W, at arbitrary complex spectral parameters. |
| Exact pair identity | `sourcePeriodicPair_factorization` | The actual product equals (τ_n−z)²−γ_n²/4 at every complex source and spectral parameter. |
| Preceding simple-root paragraph | `.simplicity` | Every ordinary boundary and critical coordinate is complex analytic, with nonzero spectral derivative of its defining characteristic. |

Complex analyticity is stronger than the stated real analyticity. No
analyticity or continuity of individually ordered periodic endpoints on
W is assumed. Their symmetric functions are obtained from the existing
spectral-cluster trace formulas. The midpoint and squared gap determine
all power sums through the symmetric-pair recurrence, including the
constant power. Composition with the source projection and polynomial
operations gives joint analyticity of the exact pair factor.

## Simplicity and connectedness on the same domain

`exists_local_source_allCriticalPoints_simple_analytic` intersects one
common distant-index analyticity neighborhood with finitely many central
analyticity neighborhoods and the all-index simplicity neighborhood.
This gives one open source set around each real-type base where all
critical coordinates are simple and analytic simultaneously.

`exists_sourceSimpleSpectralDomain_within` works inside any prescribed
open set containing the real locus. Intersect that set with the common
ordinary boundary-root domain and the interior of the all-critical-root
property. Take the connected component containing zero. Local
connectedness makes this component open, and connectedness of the real
locus places the entire locus in it. This avoids assuming that an
arbitrary intersection of connected sets is connected.

Applying the construction inside the Lemma 10.1 domain gives W above.
At each point ψ∈W, a source ball contained in both W and its previous
isolating neighborhood retains the same disks and distance constant.
`SourceIsolatingNeighborhoods.mono` records this restriction explicitly.

`SourceSimpleSpectralDomainData.boundary_multiplicity` identifies
simplicity with algebraic multiplicity one for the actual ordinary
boundary operator, using the characteristic's analytic order.
`.critical_order` proves analytic order one for the actual derivative
of the discriminant at each canonical critical point. These statements
hold for every ψ∈W, not just real-type sources, and include central and
negative indices. The individual periodic-label discontinuities are now proved on
this same domain in the follow-up below, while these symmetric and
simple-root analytic properties remain unchanged.

## Literal half-exponent and locally uniform sequences

`sourcePeriodicMidpointDisplacement` has coordinates τ_n−nπ in `Coeff p`.
`sourcePeriodicSquaredGapSequence` has coordinates γ_n² in `Coeff (p/2)`.
The second exponent is the literal extended-real division p/2, rather
than a new Banach exponent or an assumption p≥2. When 1<p<2, the norm
notation denotes the existing ℓ^(p/2) quasi-norm; the proof does not
assume a triangle inequality for that space.

`lp_norm_eq_sq_of_apply_eq_sq` proves the exact identity

```
‖(g_n²)_n‖_(p/2) = ‖g‖_p².
```

It compares the powered norms through their sums of nonnegative real
powers. The half exponent is positive because p is finite and greater
than one. Applying this identity to the full actual gap sequence gives
`norm_sourcePeriodicSquaredGapSequence`. Applying it after any finite
truncation gives `norm_sourcePeriodicSquaredGapSequence_tail`; no symmetry
of the removed set is needed.

The precise common-neighborhood statement is: for every φ∈W and η>0,
there are an open U with φ∈U⊆W, N≥2, and R≥0 such that every ψ∈U satisfies

```
‖(τ_n(ψ)−nπ)_n‖_p ≤ R,      ‖(γ_n(ψ)²)_n‖_(p/2) ≤ R²,
```

and, for every M≥N, their tails outside [−M,M] are bounded by η and η²
respectively. All choices precede ψ and M. U, N and R may depend on η;
a single neighborhood working for all tolerances is not asserted.
`exists_uniform_sourceLemma10_2_sequences` proves these bounds near
arbitrary complex base sources even without membership in W; the main
theorem then intersects U with W. Both complete sequences, including
all central indices, vanish at the free potential.

## Lemma 10.2 verification and remaining scope

Public examples instantiate the common domain at p=3/2 and explicitly
construct the squared-gap sequence at exponent 3/4 with its exact
quasi-norm. They exercise arbitrary powers at a negative index, joint
analyticity at a nonreal spectral point, boundary multiplicity and
critical zero order, common isolation and tail quantifiers, truncation
by the asymmetric set {0,−1,3}, the exact all-complex factorization, and
free collapsed gaps. No additional source correction is needed for
Lemma 10.2; the Lemma 10.1 domain correction remains in force.


## Lemma 10.3: the unchanged common domain

`SourceLemma10_2Data.standardRoots` produces `SourceLemma10_3Data` on
exactly its input W. No further shrinking or separate existential domain
is used. Consequently `sourceLemma10_3` supplies an open connected W
containing every real-type source, with all Lemma 10.2 properties retained.

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Principal-branch definition (2.9) | `sourceStandardRoot`, `normalizedStandardRoot` | The literal expression (τ_n−z)√(1−γ_n²/(4(τ_n−z)²)), with the principal square root. |
| Spectral analyticity | `SourceLemma10_3Data.spectral` | At every complex source, on the full complement of its actual closed gap. |
| Joint analyticity | `.joint` | On the moving-gap complement over the same W. |
| One local family | `.neighborhoods` | For every ψ∈W, one open connected V with ψ∈V⊆W and one `SourceStandardRootNeighborhoods` package. |
| Fixed-disk joint domain | `SourceStandardRootNeighborhoods.joint` | (ℂ∖D_n)×V, including points on the boundary of the open disk. |
| Two-sided root bound (2.10) | `.bounds` | The same c≥1 from quantitative isolation, for all nearby sources, all m≠n and all z∈D_m. |
| Normalized contour identity | `.contours` | Every finite piecewise C¹ contour inside D_m, avoiding G_m, with winding one about τ_m. The value is −1 if m=n and zero otherwise. |

The bound uses the exact identity |w_n(z)|²=|λ_n⁻−z||λ_n⁺−z|.
Both endpoint distances have the same lower and upper bounds from
`.pointwise_distance`. Nonnegativity transfers those bounds to |w_n|
without changing c. Gap containment and pairwise disjointness ensure
that z∈D_m avoids G_n when m≠n. Central and negative indices are included.

## General contours and the orientation convention

`PiecewiseC1Loop` consists of a finite number of paths between consecutive
vertices, each C¹ on the closed unit interval, with the last vertex equal
to the first. The definition allows corners, self-intersections, repeated
vertices and repeated traversals. Individual pieces need not be loops.
Its `integral f` is the finite sum of the actual complex one-form path
integrals. `normalizedIntegral f` multiplies that sum by (2πi)⁻¹.

`windingIntegral z` is the normalized integral of the reciprocal pole
1/(w−z). It is complex-valued; the contour theorem uses the conventional
orientation condition `windingIntegral τ_m = 1`. This condition concerns
the reciprocal pole, not the inverse standard root being evaluated.
The contour must avoid the entire closed gap. This winding-one convention
expresses a single counterclockwise circuit around the gap; simplicity
of the curve or a chosen homotopy is not an additional assumption.

`windingIntegral_circle` proves that a positively oriented circle has
value one about every point in its interior. `integral_circle` identifies
the piecewise-contour integral with the existing circle integral using
the same orientation. `repeatPath` constructs actual repeated traversals,
and `integral_repeatPath` proves that their integrals multiply by the
number of traversals. `polygon` constructs contours with literal straight
pieces and permits corners without matching endpoint derivatives.

## A single-valued primitive fixes the sign

Put t=τ_n, g=γ_n² and S(z)=√(1−g/(4(t−z)²)). The new correction is

```
F(z) = −log(1+S(z)).
```

Outside the actual gap, t−z is nonzero and the square-root radicand lies
in the principal slit plane. The principal square root has nonnegative
real part, so 1+S(z) lies in the open right half-plane. Thus this logarithm
is single-valued throughout the needed domain. Differentiating S² and
then the logarithm gives the formally checked identity

```
F′(z) = 1/w_n(z) + 1/(z−t).
```

`hasDerivAt_standardRootLogCorrection` proves this for arbitrary complex
t,g whenever the denominator and slit conditions hold. Applying the
actual source branch-cut theorem supplies these conditions off G_n.

`PiecewiseC1Loop.integral_eq_zero_of_primitive` evaluates the derivative
integral on each C¹ piece and telescopes the vertex differences. The
closed-chain condition cancels the final difference, even when the
pieces are not individually closed. Integrability follows from continuity
on the domain and C¹ regularity of the pieces; it is not an extra source
hypothesis. Therefore
`normalized_sourceStandardRoot_inv_piecewiseIntegral_eq_neg_winding`
proves the full formula

```
(2πi)⁻¹ ∫_Γ dz/w_n(z) = −windingIntegral(Γ,τ_n).
```

This holds at every complex source for every gap-avoiding piecewise C¹
contour, independently of W. It also covers collapsed gaps, clockwise
orientation and any number of traversals. No contour-deformation
hypothesis or reduction to the Hilbert exponent appears in the proof.

For m≠n, the inverse root is holomorphic on the whole convex disk D_m.
An actual primitive there makes its integral zero on every piecewise C¹
closed contour inside D_m. Combining this with the diagonal winding-one
formula proves `standardRoot_piecewiseIntegral_indexed` and the local
`.contours` field using the same family as the norm estimate.

## Collapsed gaps and the following boundary-value formulas

`sourceStandardRoot_analyticOnNhd_of_zeroGap` proves that a collapsed root
is analytic on all of ℂ, including its midpoint, where the original
complement-of-gap assertion says nothing. The exact value is τ_n−z.
At zero source this is nπ−z, fixing the sign of the contour normalization.

For noncollapsed gaps, the existing
`sourceStandardRoot_tendsto_gap_upper_side` and
`sourceStandardRoot_tendsto_gap_lower_side` prove (2.12) under arbitrary
approach from the corresponding open side in the coordinate
u=(z−τ_n)/(γ_n/2). Their limits are respectively
−i(γ_n/2)√(1−t²) and +i(γ_n/2)√(1−t²), for every −1≤t≤1.
The midpoint, both endpoints, and arbitrary complex gap directions are
included. These are stronger approach limits than just vertical paths
with the longitudinal parameter held fixed.

## Lemma 10.3 verification and remaining scope

The public checks instantiate the common domain at p=3/2, transfer any
Lemma 10.2 domain unchanged, expose the literal branch formula and free
sign, and check root bounds at central and negative indices. They test
joint analyticity outside the fixed open disk and both values of the
indexed contour identity. The general winding formula is exercised with
clockwise winding. A concrete two-piece repeated circle has period −2;
a concrete two-edge polygon has a genuine corner and nonclosed pieces
and integrates to zero in a gap-free convex disk. Additional checks cover
collapsed-root analyticity at its midpoint and complex upper/lower side
limits at the midpoint and an endpoint. No new source correction is
needed for Lemma 10.3.

Next: Lemma 10.4, its gap-side endpoint integral bound and the printed
index convention in its denominator. The dissertation remains incomplete.


## Lemma 10.4: actual traces and the selected-root correction

The source on printed p. 56 uses w_m in both the statement and proof,
with m unbound, while the path follows G_n. Equation (2.12) and the
substitution require w_n. `SOURCE_ERRATA.md` records the correction and
its precise formal evidence. The result below uses n consistently and
is proved for every original complex source with γ_n≠0, not only sources
in the almost-real neighborhood. All finite exponents p>1 are included.

| Requirement | Formal result | Exact scope |
| --- | --- | --- |
| Actual gap | `sourceStandardRoot_gapSegment_eq_periodicSegment` | The affine image of [-1,1] is exactly the canonical segment G_n. |
| Actual endpoints | `sourceStandardRoot_gap_left_endpoint`, `sourceStandardRoot_gap_right_endpoint` | Coordinates -1 and 1 are λ_n⁻ and λ_n⁺. |
| Boundary denominator | `sourceStandardRoot_tendsto_sideTrace` | The trace is the limit of the actual root under arbitrary approach within the appropriate open side, including endpoints. |
| Continuous side values | `sourceStandardRootSideTrace_continuous` | Continuity in the closed affine gap coordinate. |
| Genuine integrability | `sourceStandardRootSideIntegrand_intervalIntegrable` | Continuous f on G_n suffices for any two closed-gap endpoints. |
| Exact substitution | `sourceStandardRootSideIntegral_eq_weighted` | The signed inverse-square-root integral, with the actual half-gap Jacobian canceled. |
| Improper interpretation | `sourceStandardRootSideIntegral_tendsto`, `sourceStandardRootSideIntegral_double_trunc_tendsto` | Omitting the left branch point, or both branch points, converges to the same side integral. |
| One attained maximum | `sourceLemma10_4` | One z∈G_n maximizes |f| and controls both sides and all endpoints. |
| Literal supremum | `sourceLemma10_4`, `sourceLemma10_4_sup` | Real suprema of the actual sets of integral norms and data norms. |
| Sharp constant | `sourceLemma10_4_const_sharp` | Constant data c have supremum exactly |c|. |

The chosen side is represented by a Boolean and the stopping point by
t∈[-1,1]. Together they parametrize the two closed copies G_n⁺ and G_n⁻.
The upper and lower traces are respectively -iδ√(1-t²) and +iδ√(1-t²),
where δ=γ_n/2. Their identification with the actual root is proved by the
existing arbitrary-approach limit theorem; it is not an assumed boundary
formula. Both trace values vanish at the two branch points.

`sourceStandardRootSideIntegral` is defined by the literal affine pullback

```
∫_a^b f(τ_n + δ r) · δ / sourceStandardRootSideTrace(n,r,side) dr.
```

This is a boundary-trace integral; the value of the totalized principal
root formula on its branch cut is not substituted for its side limit.
Only f restricted to G_n is needed. Endpoint division is totalized in
Lean, but genuine integrability and the truncation-limit theorems prove
that endpoint values do not change the intended improper integral.
No assumption of an off-gap extension of f is made.

The main theorem chooses one attained maximum before quantifying over
all stopping points and both sides. The set of integral norms is
nonempty (it includes the left endpoint) and bounded above by that same
maximum. The supremum bound therefore concerns the literal real sSup,
not a newly defined quantity stipulated to satisfy the estimate. The
right-hand data supremum is likewise finite and attained on the actual
canonical gap.

For constants c, `sourceStandardRootSideIntegral_const_full` proves the
exact normalized values +ic on the upper side and -ic on the lower side.
Both full sides attain |c|; the entire set of values has supremum |c|.
The two endpoint integrals have opposite signs for arbitrary continuous
data, and stopping at the initial endpoint gives zero.

## Lemma 10.4: evidence for the index correction

For real-type ψ and m≠n, w_m is real on the whole closed real gap G_n,
and δ_n is real. Thus δ_n/w_m(τ_n) has imaginary part zero. It cannot
equal either ±i, as the printed substitution would require at r=0 with
constant data one. `sourceLemma10_4_printed_kernel_counterexample`
provides an actual noncollapsed real source for every selected index
and every finite exponent p>1. This formally refutes that wrong-index
kernel identity. It does not purport to disprove every possible
wrong-index integral bound.

Public checks expose the literal trace-based integrand and supremum,
exercise both endpoint singularities, one- and two-endpoint truncations,
midpoint stopping, both orientation signs, constant sharpness and a
nonconstant test function. An actual noncollapsed real source at p=3/2
and index -1 attains the sharp value one. The correction check also uses
actual noncollapsed sources, so neither sharpness nor the index witness
is conditional on an uninhabited hypothesis.

Next: Lemma 10.5, convergence, analytic domains and nonvanishing of the
omitted standard-root product. The dissertation remains incomplete.


## Lemma 10.5: the actual product and its normalization

The source on printed p. 57 defines

```
f_n(z) = (1/π_n) ∏_{m≠n} w_m(z)/π_m,   π_0=1, π_n=nπ for n≠0.
```

`sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ)` is literally
that finite product over [-N,N] with n erased. Its definition includes
the outer division by π_n at every cutoff, even before the cutoff
reaches n. `sourceStandardRootOmittedProduct` is the zero-mode prefactor
times the infinite product of positive/negative pairs, with the selected
factor replaced by one. `tendsto_sourceStandardRootOmittedPartialProduct`
identifies this value as the limit of the literal cutoffs at every source,
spectral point and omitted index. No limit or normalization is assumed.

The paired factors have summable norms of their deviations from one.
`exists_uniform_absolute_sourceStandardRootOmittedPairedFactor_tails`
strengthens this to a common vanishing bound on arbitrary finite subsets
of the high-frequency tail, uniformly for all nearby sources and all
spectral points in a prescribed bounded region. After a cutoff at least
|n|, omission no longer changes the tail. This gives the normal convergence
used in the analyticity proof. Absolute convergence concerns these paired
blocks, as in the source's displayed regrouping.

## Lemma 10.5: one unchanged common domain and local family

`SourceLemma10_3Data.omittedProducts` takes any open common domain W
with the Lemma 10.3 data and returns `SourceLemma10_5Data` on exactly W.
It does not construct a replacement W or shrink it. Each local package
is built from the already supplied V,D,c and extends its
`SourceStandardRootNeighborhoods`; its isolation, root bounds, root
analyticity and general contour identity remain available.

| Source requirement | Formal field or theorem | Exact scope |
| --- | --- | --- |
| Spectral domain | `sourceStandardRootOmittedDomain_eq_compl_iUnion` | The literal complement of the union of all G_m with m≠n. |
| Spectral analyticity | `SourceLemma10_5Data.spectral` | Every source in the same W and every integer n. |
| Joint analytic domain | `.joint` | The open moving-gap complement over W; openness is proved. |
| Local uniform convergence | `.locally_uniform` | Actual symmetric finite cutoffs, jointly in source and spectral point. |
| Uniform convergence on compact sets | `SourceLemma10_3Data.omittedCompact`, `.omittedSpectralCompact` | Joint compact sets and spectral compact sets at a fixed source. |
| Printed fixed-disk domain | `SourceOmittedRootNeighborhoods.omitted_joint` | (ℂ∖⋃_{m≠n} closure(D_m))×V, retaining the source's overlines. |
| Stronger fixed domain | `SourceLemma10_3Data.omittedFixed` | Analyticity and nonvanishing also on the complement of the open disks, including their boundaries. |
| Nonvanishing | `SourceLemma10_5Data.nonzero`, local `.omitted_nonzero` | The whole moving-gap domain, even for arbitrary complex sources, and the printed local fixed domain. |
| Omitted gap itself | `SourceOmittedRootNeighborhoods.omitted_disk` | The whole omitted disk D_n is analytic and nonzero, including all points of G_n and collapsed gaps. |

The joint proof uses the same analytic midpoint and squared-gap
coordinates as Lemma 10.3. Every finite cutoff is analytic, and the
uniform paired tails give a locally uniform limit on the open joint
domain. Restriction to a fixed source gives spectral analyticity.
Containment of each actual gap in its fixed disk gives the claimed local
joint domain. Pairwise disjointness puts all of D_n in the complement of
the unomitted gaps. Nonvanishing follows from summable paired deviations
and the nonzero actual factors; finite products alone would not suffice.

## Lemma 10.5: free normalization and ordering checks

`sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient` proves
that the actual free product is the filled quotient sin(z)/(z−nπ) on all
of ℂ. The omitted point is filled by cos(nπ), of norm one. The function
is entire and vanishes at every unomitted lattice point. These assertions
check the sign and the prefactor for positive, zero and negative indices,
and delimit the nonvanishing domain precisely.

`sourceStandardRootRelativeError_zero_source_positive_norm` proves the
exact harmonic error |z|/(π(k+1)) for an individual positive-index factor
at zero source. Its series is not summable when z≠0, whereas the paired
deviations are summable. A public check uses z=i and formally verifies
that this is in the actual free omitted domain. Pairing is therefore an
essential convergence convention, not merely a notation choice.

The source's isolated a_k a_{-m} in one intermediate estimate is recorded
as a proof-index typo: the next lines use the required a_k a_{-k}.
The statement of Lemma 10.5 itself needs no new correction.

Public checks instantiate the full package at p=3/2, transfer an arbitrary
Lemma 10.3 domain unchanged, expose the literal cutoff formula, and test
negative-index omission before its index enters the cutoff. They check
joint and spectral compact convergence, the printed closed-disk domain,
analyticity and nonvanishing on the entire omitted gap, and uniform
absolute tails over arbitrary finite sets. Free checks cover the omitted
negative center's sign, its unit norm, every other zero, entire extension,
and paired versus individual convergence at the same genuine domain point.

Next: Corollary 10.6, the quotient product with variable displaced roots.
The dissertation remains incomplete.


## Corollary 10.6: literal product and all root parameters

The source on printed p. 57, visually checked, states that

    ∏_{m≠n} (σ_m−λ)/w_m(λ)

is analytic on

    (ℂ \ ⋃_{m≠n} closure(U_m)) × ℓᵖ × V_φ.

The bar over U_m is present in the printed formula. The displacement
parameter is a=σ−σ⁰, where σ⁰_m=mπ. `exists_displacedRoots_iff_memℓp`
proves that `Coeff p` represents exactly this affine root space. No root
ordering, distinctness, size bound or numerator nonvanishing condition is
added. The omitted index ranges over all integers, including zero and
negative indices; p ranges over every finite exponent greater than one.

`sourceSingleRootQuotientPartialProduct` is the literal product over
[-N,N] with n erased. The existing finite quotient identity cancels both
π_n prefactors and every π_m factor exactly, including at early cutoffs.
`SourceSingleRootQuotientCommonDomain.lean` proves local uniform convergence
of these cutoffs in λ, a and ψ, hence uniform convergence on every compact
subset of the triple domain. The numerator is jointly entire and the
omitted-root denominator is analytic and nonzero there.

## Corollary 10.6: individual absolute convergence and unordered products

Unlike the separate factors in Lemma 10.5, the quotient factors have
absolutely summable individual deviations from one. For noncentral m,
put e_m=w_m/(πm)−1. The existing midpoint correction b_m and square-root
correction r_m satisfy

    e_m = b_m − λ/(πm) + r_m.

If d_m=a_m/(πm)−b_m−r_m, then exactly

    (σ_m−λ)/w_m(λ)−1 = d_m/(1+e_m)

where the denominator is nonzero. Hölder gives a_m/(πm)∈ℓ¹, and both b
and r already belong to ℓ¹. The normalized root errors e belong to ℓ²
and tend to zero along the cofinite filter. Eventually |1+e_m|≥1/2,
so the individual quotient error is bounded by 2|d_m|. The finitely many
remaining indices cause no summability problem.

`summable_norm_sourceSingleRootQuotientFactor_sub_one` proves the absolute
summability. `hasProd_sourceSingleRootQuotient_subtype` identifies the
unconditional product over {m∈ℤ | m≠n} with the analytic quotient on the
natural domain. `tendsto_finset_sourceSingleRootQuotient` gives convergence
over all finite subsets with n erased. These assertions do not rely on
choosing positive/negative pairs or a particular enumeration. The product
identity is asserted only where the unomitted actual gaps are avoided;
no analyticity is claimed for totalized division at excluded gap points.

## Corollary 10.6: unchanged domains and degeneracy checks

`SourceLemma10_5Data.quotients` constructs `SourceCorollary10_6Data` on
exactly the supplied W. Its local `SourceSingleRootQuotientNeighborhoods`
extends the earlier omitted-root package, preserving the same V, D and c.
Both the quotient and the literal unordered product are jointly analytic
on the printed closed-disk complement times all a and V. The larger open
moving-gap domain and the whole selected disk are also covered. In
particular, the selected gap's endpoints and collapsed case are included.

The free quotient is one at every point of its natural domain, including
λ=nπ. The omitted coordinate a_n has no effect on the function. Every
unomitted numerator root remains a zero. The explicit displacement

    a_0=i, a_{−1}=π+i, a_m=0 otherwise

has σ_0=σ_{−1}=i. At zero source, i lies in the actual natural domain;
with n=−1 the quotient equals zero. Thus a collision between the omitted
root and an unomitted root is allowed, and does not create a pole.

Public checks cover the complete package at p=3/2, the same-domain transfer,
literal finite normalization, unordered product identity, convergence over
all finite subsets, joint compact convergence, printed closed-disk
analyticity, selected-gap analyticity, arbitrary omitted-coordinate changes,
free values at nπ and i, and the explicit collision at p=3/2.
The source statement requires no new correction.

Next: equation (2.13) and Lemma 10.7, the canonical-root product and its
analytic domains. The dissertation remains incomplete.


## Equation (2.13) and Lemma 10.7: exact product and domains

The source on printed pp. 57–58, visually checked, defines the canonical
root by

    R(λ) = 2i w_n(λ) f_n(λ) = 2i ∏_{m∈ℤ} w_m(λ)/π_m,

with π_0=1 and π_m=mπ for nonzero m. Its literal finite products use
[-N,N]. Restoring an omitted index gives the same finite product once
N≥|n|. The limit factors through every omitted n, and its square is the
actual source Δ²−4 on the complement of ALL closed periodic gaps. The
paired convention from Lemma 10.5 is retained for the full standard-root
product; Corollary 10.6's unconditional quotient result is not incorrectly
applied to these separate factors.

`SourceCorollary10_6Data.canonicalRoots` constructs `SourceLemma10_7Data`
on exactly its supplied W. The package retains the entire preceding
corollary. The full joint moving-gap domain is open: it is the intersection
of the omitted domains for indices 0 and 1. The literal symmetric cutoffs
converge locally uniformly there. Uniform convergence on joint compacts
and on spectral compacts at a fixed source is explicit.

The printed fixed domain is

    (ℂ \ ⋃_{m∈ℤ} closure(U_m)) × V_φ.

The bar over U_m is present in the printed formula. Every local
`SourceCanonicalRootNeighborhoods` retains the original V, D and c and
proves analyticity on this exact closed-disk complement. Spectral
analyticity and nonvanishing on the full gap complement hold for every
original complex source, a stronger scope than restricting to W.

## Equation (2.14): actual boundary values on closed complex gaps

For the affine coordinate λ=τ_n+(γ_n/2)t, -1≤t≤1, the upper and lower
traces are the actual limits of the canonical root from the corresponding
open sides of the gap. The limits allow arbitrary approaches within each
side, including to the midpoint and both endpoints. The chosen sides
are oriented by the complex half-gap, as in the standard-root formulas.
The traces are defined by multiplying the corresponding standard-root
trace by 2i f_n at the same point.

`SourceCanonicalRootBoundaryData` includes:

- continuity of both traces on the CLOSED parameter interval [-1,1];
- actual upper and lower limits for every noncollapsed gap;
- the exact opposite-value relation (2.14);
- zero values at both endpoints on both sides;
- nonzero interior values for a noncollapsed gap;
- both traces' squares equal to the actual source Δ²−4 at the gap point.

The entire selected gap belongs to the omitted product's domain by the
original isolating family. These statements therefore hold for all
complex sources in the same W, with no new separation hypothesis or
source-neighborhood shrink.

The globally totalized algebraic expression for a standard root at a
point on its cut is not substituted for its boundary trace. In particular,
the raw midpoint expression of a noncollapsed gap must not be used to
claim the canonical-root square identity at that cut point. The package
states the raw root's square identity off the gaps and the trace square
identities on them.

## Lemma 10.7: collapsed gaps and the branch normalization

If γ_n=0, the canonical root is exactly

    R(λ) = 2i (τ_n−λ) f_n(λ)

and is analytic on the entire original selected disk D_n. Its value at
τ_n is zero, and its derivative there is -2i f_n(τ_n), which is nonzero.
Thus the analytic continuation has a simple zero. This is an extension
for the fixed source, not a joint extension through arbitrary nearby
sources where the gap could reopen.

At zero source, the actual root equals -2i sin(λ) on all of ℂ and is
entire. Its value at π/2 is -2i, the first cutoff at i is 2, and its
derivative at -π is +2i. These values check the factor 2i, the π_0=1
normalization and the choice of branch, beyond merely checking a square.

## Figure 2.4: real-source signs, including negative indices

For real-type sources and an open real gap, the upper and lower traces
are real and have opposite signs. Their signs relative to (-1)^n are
positive above and negative below. In the adjacent bands the canonical
root is purely imaginary, with sign (+i)(-1)^n on the left and
(-i)(-1)^n on the right. `sourceCanonicalRoot_figure_gap_signs` and
`sourceCanonicalRoot_figure_band_signs` give these four assertions for
every integer n. The equivalence between parity of |n| and n handles
negative indices and the change from band n−1 to band n.

These real/imaginary signs describe the figure on the real-type locus;
for complex sources the exact opposite boundary-value relation is used.
A genuine open gap at n=−1 witnesses a negative upper real value and a
positive lower real value. The proof obtains the source from the existing
real Floquet gap-opening theorem and derives strict endpoint separation.

Public checks include the full package at p=3/2, preservation of the
Corollary 10.6 domain, literal cutoff normalization, restoration at a
negative index, both compact convergence statements, the exact gap-union
and closed-disk domains, the discriminant identity and nonvanishing off
cuts, trace squares on cuts, endpoint and midpoint approaches, collapsed
continuation and its simple-zero derivative, and both negative-index
figure signs. No new source correction is required.

Next: Lemma 10.8, the quotient-product asymptotic estimate with its sequence
exponents and local uniformity. The dissertation remains incomplete.

## Lemma 10.8: supremum estimates on the complete original disk family

The displayed statement and proof on printed pp. 58–59 were visually
checked. Let a=σ−σ⁰ be the original ℓp numerator displacement and let
α=σ−τ be its offset from the source midpoints. The source's introduction
defines a sum of sequence classes as an exact decomposition, and ℓ(1+)
as membership in every finite exponent r>1.

`SourceLemma10_8Estimates` retains the whole Lemma 10.7 package on exactly
the supplied W. At each φ in W it keeps the original V, disk family D
and distance constant c. This family is chosen before a and before the
target exponent. Near each (a,φ), one open joint neighborhood supplies
all the estimates below. No real-type or near-zero restriction is added.

The positive distance inequality extends to the closure of each disk.
Consequently, its closure avoids every other actual gap and lies in the
selected omitted-root domain. Each closed disk is compact. Applying joint
continuity over finitely many such compact slices gives a common local
bound for the finite central part of the quotient error.

For the tail, `SourceQuotientAsymptoticGeometry` uses an auxiliary free
family with empty central disks and the usual quarter-π tail disks.
This is only an adapter to the existing tail estimates: every auxiliary
disk is a subset of the corresponding actual D_n, and all tail disks
agree exactly. The actual central disks remain nonempty and are covered
by the separate finite bound. The original separation constant is retained.

`sourceQuotientDiscSup` is literally

    E_n(a,ψ) = sup { |Q_n(λ,a,ψ)−1| : λ ∈ D_n }.

Its defining set is nonempty and bounded above. Every pointwise error is
at most E_n, and E_n is at most any upper bound for the disk image. This
is the least upper bound, not just a chosen dominating sequence. The
unordered product from Corollary 10.6 equals Q_n on each actual D_n.

## Lemma 10.8: exact sequence classes and uniformity proved so far

For each T≥0, consider the family of parameters in the joint neighborhood
for which α∈ℓq and ||α||q≤T. The bounds are uniform on this family:

| Offset exponent | Exact decomposition of E | Uniform bound |
| --- | --- | --- |
| 1<q<∞ | A_q+B_(p/2) | Separate bounds on both sequence norms |
| q=1 | A_(p/2)+B_(1+) | One pair chosen first; every finite r>1 projection of B has a uniform bound |
| q≥p, including ∞ | A_q+B_(p/2) | Locally uniform in the original ℓp root topology, with the same neighborhood and bounds for all q≥p |

The q=1 construction does not merely choose unrelated remainders for
different r. It gives functions into the actual `CoeffOnePlus` space,
then bounds every projection of those fixed functions. When p/2>1, the
whole endpoint sequence can be placed in ℓ(p/2); when p/2≤1, it belongs
to every ℓr for r>1. These alternatives give a genuine fixed pair and
cover the quasi-Banach range. Adding a zero component gives the printed
three-term decomposition at every finite q≥1.

For q≥p, the offset's original ℓp norm is bounded locally by the root
displacement norm and the midpoint-displacement bound. Contractive
sequence inclusion supplies q=∞ as well. For q<p, the proof currently
requires an explicit bound on ||α||q. It does not claim that this stronger
norm is locally bounded in the weaker ℓp topology.

For the free numerator a=0, α=−(τ−σ⁰) belongs to ℓp with a local norm
bound. The filled sine quotient divided by the omitted standard-root
product therefore has a full-disk supremum decomposition with q=p,
locally uniformly in the source. Away from λ=nπ the filled quotient
equals the printed sin(λ)/(λ−nπ); at the center it uses the removable
value cos(nπ), including the negative-index sign.

## Lemma 10.8: concrete checks and remaining source audit

Public checks instantiate the complete estimate package at p=3/2,
test the q=∞ target, identify the literal least upper bound, and project
one fixed endpoint remainder at both r=2 and r=3. An open neighborhood
of zero in W is shown to contain an actual non-real source, so the
general complex-source coverage is not vacuous.

At free source with free roots the supremum is zero on every actual disk.
An explicit finitely supported numerator displacement moves the zeroth
root onto −π, colliding with the −1 root. In the quotient with −1 omitted,
the numerator vanishes at −π while the omitted denominator is nonzero.
The actual selected central disk contains −π, and its supremum is at
least one. This witnesses that the finite head has not been discarded.

## Lemma 10.8: the original-topology claim is false in general

The p=4, q=1 case is now refuted by actual finite-block numerator
perturbations at the free source. This is stronger than observing that
an ℓ1 input norm need not be bounded in ℓ4.

For a_m=b on 1≤m≤L and zero elsewhere,
`sourceSingleRootQuotient_block_eq_finiteProduct` proves

    Q_n(nπ,a,0) = ∏_(1≤m≤L) (1−b/(π(n−m)))    (n outside the block).

If 0≤b≤π and 2L<n≤3L, the sum of the deficits is between b/(3π)
and one. The finite-product estimate gives |Q_n−1|≥b/(6π), hence
||B||₂²≥L(b/(6π))² for every ℓ2 majorant B. With L=k⁴ and b=δ/(2k),
the input has ||a||₄=δ/2 while ||B||₂≥δk/(12π). Increasing k yields
unbounded output norms on every ℓ4 neighborhood, with all offsets in ℓ1.

`not_locally_uniform_sourceQuotientDiscSup_mixed` applies the obstruction
to the literal supremum on any actual disk-estimate neighborhood of the
free source whose disks contain the free centers. The three printed
components would give an ℓ2 majorant by contractive ℓ1 inclusion and the
ℓ2 projection of the ℓ(1+) component. Their combined norm bound is
impossible, independently of how the components are chosen or cancel.
`exists_sourceQuotientDiscSup_uniformity_counterexample` constructs such
a neighborhood from `sourceLemma10_8_estimates` itself.

`SourceQuotientDiscEstimates.free_sup_mem_l2_of_summable` separately
proves individual ℓ2 membership for every summable free-source offset
in an actual estimate neighborhood. Thus the discrepancy is specifically
local uniformity, not the pointwise sequence class. Public checks also
test the exact finite product at a negative free center, constant small
input norm as the support grows, and an arbitrarily large output bound.

A sufficient correction is the already proved explicit ℓq offset bound
when q<p. The original-topology result for q≥p remains valid. The formal
counterexample uses p=4, q=1; it does not classify every pair q<p.

The free-sine display's unspecialized q is now the sole remaining
Lemma 10.8 audit question. Its unconditional q=p consequence is proved.
A general-q specialization requires appropriate estimates for the free
midpoint offset, which cannot be inferred from an arbitrary numerator's
offset. The present counterexample does not settle that separate claim.
After resolving it, proceed to Remark 10.9 and Lemma 10.10.

## Lemma 10.8: quadratic diagonal contribution to the free-sine audit

The remaining general-q question cannot be settled by the numerator
counterexample, which varies the roots while holding the source at zero.
The free numerator fixes those roots; its offset is the negative midpoint
displacement. The new work isolates an actual source contribution that
has better sequence summability than the existing endpoint-average bound.

For physical coefficients a,b, define f_j=b_j a_(−j). Hölder gives
f∈ℓ(p/2) and ||f||_(p/2)≤||a||p ||b||p, including p/2<1. The quadratic
diagonal is the signed row

    A2_n(z) = ∑_(j≠2n) f_j / (z+πn−πj).

`resonantDiagonalQuadratic_eq_physical` identifies this with the first
actual resolvent iterate. Sampling each z_n independently in its free
quarter-π disk and filling unused odd rows yields a sampled discrete
Hilbert transform at indices 2n. For finite r>1 and r≥p/2, contractive
sequence inclusion and the Hilbert bound give

    ||sup_(z∈disk_n) |A2_n(z)||r
      ≤ π⁻¹ (H_r+||HilbertSquare||) ||a||p ||b||p.

The supremum is literal. Its coefficient sequence is obtained from the
uniform bound over every independent selection, not merely from estimates
at one center. Bounded input families have a single ℓ(p/2)+ℓ(1+) pair;
the ℓ(1+) summand is fixed before choosing any projection exponent.

The actual diagonal's remainder is explicitly the diagonal row tested
against T_n² E_n, where E_n is the actual even corrected source vector.
`weightedResonantA_sub_quadratic` proves exact equality with that
remainder. The estimates retain the spectral square bound and reciprocal
row norm before giving |R_n(z)|≤C_p ||φ||⁴ on the contraction region.
No half-exponent sequence estimate for R is claimed from this pointwise
quartic inequality.

Period-one embedding removes the odd physical frequencies and produces

    A2_n(z,φ) = ∑_(m≠n) φ₂,m φ₁,−m / (z+πn−2πm).

At the free center this equals −(2π)⁻¹ times the source Hilbert row.
The components are independent complex sequences; reflection introduces
no complex conjugation. The source transport supplies a quadratic bound
for the actual free-disk supremum using the original pair norm.
`exists_local_sourceResonantDiagonalQuadraticExpansion` supplies one open
original-source neighborhood and one cutoff on which the actual analytic
diagonal differs from this term by at most C_p ||φ||⁴, throughout every
distant closed resonant strip. No contraction assumption is left as a
premise on that neighborhood.

This proves the needed summability for the quadratic contribution only.
The nonlinear remainder still requires sequence estimates, and the
diagonal centers must still be related quantitatively to the actual
periodic midpoints. The unconditional free-sine result remains q=p until
those steps, or another complete argument, resolve its printed general q.

## Lemma 10.8: midpoint-center comparison at the half exponent

The midpoint-to-center step left open above is now proved, locally
uniformly on the original source space. Write ζ_n for the named center
solving ζ_n=nπ+a_n(ζ_n) on distant strips, and τ_n for the actual canonical
periodic midpoint. Then

    |τ_n−ζ_n| ≤ (8/π) sup_(z∈strip_n) |b_n⁺(z)b_n⁻(z)|.

For distinct endpoints, subtracting the two root equations controls the
sum of their diagonal residuals. At a repeated endpoint, actual analytic
order two forces the determinant derivative to vanish, giving the same
bound. A repeated simple root would not suffice; the public checks
include a concrete failure when one simply duplicates a simple root.
Second-derivative bounds for the diagonal make the midpoint Taylor error
proportional to the squared gap. All estimates apply to complex sources.

The full off-diagonal coefficients are bounded by actual ℓp sequences,
including their leading Fourier coefficients and double reciprocal-row
remainders. Hölder places their product in ℓ(p/2), even below exponent
one. The comparison therefore produces an actual half-exponent tail
sequence with a locally uniform norm bound. The canonical midpoint has
an existing uniform coordinate bound, and the named diagonal center
always stays within π/4 of the free center. These control a fixed finite
head and give the full sequence result. The named center retains its
existing free fallback at central indices where its fixed-point
existence is unavailable.

`exists_uniform_sourceMidpointCenterError` proves the full neighborhood
and norm assertion. `memℓp_sourceMidpointDisplacement_iff_center` proves
that for any r≥p/2, midpoint and diagonal-center displacements have
equivalent ℓr membership. This resolves the midpoint transfer required
by the quadratic-diagonal approach. The nonlinear diagonal remainder at
the moving centers still needs sequence bounds; its quartic pointwise
bound is insufficient. The printed general-q free-sine claim remains
unresolved, and its unconditional q=p version remains proved.

## Lemma 10.8: completion of the refined free-sine consequence

Eight modules close the remaining Lemma 10.8 free-sine exponent audit.
The literal free-sine quotient error on every original isolating disk has
one locally uniformly bounded ℓ(p/2)+ℓ(1+) decomposition for every finite
p>1. This implies the printed consequence for every q≥1 by taking its
ℓq summand to be zero. The separate original-topology uniformity claim
for arbitrary numerators remains formally refuted at p=4, q=1.

`YoungConvolutionTranspose.lean` transposes the absolutely convergent
Banach-space convolution series through the conjugate pairing.
`UnweightedDoubleRowTesting.lean` tests the two remaining actual
resolvent symbols against arbitrary outer rows.
`ResonantDiagonalRemainderRows.lean` uses the auxiliary exponent 2p and
its conjugate to identify the exact transposed nonlinear diagonal
remainder. Young and Hölder retain two source-frequency reciprocal rows
instead of discarding their dependence on the index.

`ResonantDiagonalRemainderMajorants.lean` applies powered Young to both
rows. Each has an ℓp majorant; their product belongs to ℓ(p/2), including
the quasi-normed range p<2. The resulting majorant controls the actual
nonlinear remainder simultaneously over each full strip on the proved
contraction region. Its norm is quartic in the unweighted component norms.
`SourceDiagonalRemainderMajorants.lean` supplies the contractions on one
original-source neighborhood and cutoff, with a common majorant norm.

`SourceDiagonalCenterSummability.lean` combines the quadratic disk
estimate with this nonlinear bound at the moving diagonal centers.
A fixed finite head covers the named center's free fallback.
`SourcePeriodicMidpointRefined.lean` adds the previous midpoint-center
error. The full actual canonical midpoint displacement is locally
uniformly in every finite ℓr with r>1 and r≥p/2, on a single neighborhood
independent of r. Thus p>2 includes ℓ(p/2); p≤2 gives ℓ(1+), without
claiming ℓ1. One fixed mixed pair realizes these estimates.

`SourceFreeSineQuotientRefined.lean` inserts the actual free-minus-midpoint
offset into the existing full-disk quotient estimates. The theorem
`sourceLemma10_8_freeSine_refined` keeps the common almost-real source
domain and the original disk family, including every central disk and
the filled value at the removable free center. Its two summand maps are
chosen before every ℓ(1+) projection exponent, with uniform bounds on
one source neighborhood.

Lemma 10.8's audit is now resolved: bounded-offset estimates, the valid
original-topology range, the arbitrary-numerator uniformity counterexample,
and the unrestricted free-sine consequence are all accounted for. The
printed arbitrary-numerator uniformity assertion has not been proved;
it is false as stated. Next: Remark 10.9's sharpness expansion, then
Lemma 10.10 and the remaining Section 10 statements.

Validation: `./scripts/check.sh` passed (6,893 build jobs, the full public example suite, and the axiom audit of 31,950 NLS declarations). The build retains 21 existing warnings; the eight new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Remark 10.9: exact Taylor expansion and remaining sharpness audit

Five modules prove the exact Taylor expansion underlying Remark 10.9.
For every finite p>1, the literal supremum over each original isolating
disk of

    | product_(m≠n) (τ_m−z)/w_m(z) − 1 − sum_(m≠n) γ_m²/[8(τ_m−z)²] |

is an ℓ(p/4) sequence, locally uniformly in the original source topology.
The estimate includes every central disk, repeated roots and collapsed
gaps. It does not round the exponent up to one or require a distant-index
cutoff. The disk family and common almost-real domain are retained.

`InverseSqrtProductTaylor.lean` proves the exact algebraic identity

    (sqrt(1−q))⁻¹ − 1 − q/2
      = (sqrt(1−q)−1)² (1/2 + (sqrt(1−q))⁻¹).

A uniform inverse-root bound controls the absolutely convergent infinite
product after its signed linear term, without a small-radicand hypothesis.
`SourceMidpointQuotientTaylorGeometry.lean` derives that inverse-root bound
from the original two-sided disk separation, identifies the unordered
product with the actual midpoint-numerator quotient, and records the
coefficient 1/8 and the moving midpoint denominator explicitly.

`SourceMidpointQuotientTaylorMajorant.lean` squares the actual reciprocal
squared-gap row using quasi-norm Hölder. `SourceRemark10_9Taylor.lean`
constructs the literal supremum coefficient and gives one common norm
bound near each source. The public theorem is
`sourceRemark10_9_exactTaylor`.

`SourceSquaredGapRowLowerBound.lean` shows that the row centered at m+1
is at least |γ_m|². Thus improved summability of the absolute row would
force the same improvement for the actual squared gaps. This gives a
necessary condition, not an example realizing a sharp exponent.

At this milestone, the printed replacement of the exact leading sum
by sum_(m≠n) γ_m²/(m−n)² was unresolved. The subsequent actual-source
counterexample recorded here refutes its asserted remainder class at
p=8. The corrected moving-denominator expansion remains valid. The full
p/2 optimality assertion was proved in the subsequent optimality
milestone; Lemma 10.10 and the remaining Section 10 statements remain.

Validation: `./scripts/check.sh` passed (6,898 build jobs, the full public example suite, and the axiom audit of 31,985 NLS declarations). The build retains 21 existing warnings; the five new modules and eight focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Remark 10.9: actual-source counterexample to Remark 10.9's printed remainder

Four modules resolve the printed integer-kernel replacement in Remark
10.9. At p=8, every open neighborhood of zero in the original source
space contains a real potential and an original isolating-disk family
for which the literal printed remainder supremum is outside ℓ². Hence
it is outside the asserted ℓ(p/4)+ℓ(1+) class. This is a counterexample
using actual spectral data, not freely chosen abstract gaps.

`QuarterPowerWitness.lean` constructs the real ℓ⁸ sequence |n|^(-1/4),
zero at n=0, and proves that the squares of every nonzero real multiple
fail ℓ² membership. `SourceSquaredGapNonSummability.lean` scales this
sequence into the target of the already verified inverse Birkhoff chart,
restricted to an arbitrary prescribed open source neighborhood. The
chart preserves reality and the actual action-radius identity. The
bounded normalized-action roots and exact action-gap factorization then
force the actual squared gaps of the inverse source to lie outside ℓ².

`SourceRemark10_9LatticeTerm.lean` identifies the printed signed sum with
the nonnegative physical squared-gap row S for real sources. When the
midpoint displacement has norm at most one, the exact linear term L at
the free center nπ satisfies |L_n(nπ)| ≤ S_n/8. The printed row therefore
cannot be replaced by that Taylor term modulo an ℓ² error for the
constructed source.

`SourceRemark10_9Counterexample.lean` proves boundedness of each printed
supremum on every original disk before using it. If those suprema formed
an ℓ² sequence, combining them with the verified exact Taylor remainder
would give an ℓ² majorant for S on the tail. Finite-head completion and
the neighboring-row lower bound would put the squared gaps in ℓ², a
contradiction. The conditional obstruction works for every isolating
family containing the source; the final theorems construct such a family.

The public results are `sourceRemark10_9_printed_counterexample` and
`sourceRemark10_9_printed_decomposition_counterexample`. The latter
explicitly excludes a decomposition with one ℓ(8/4) summand and one
ℓ(1+) summand. The corrected moving-denominator expansion from the
previous milestone remains valid, including for these same sources and
disks. Seven public checks cover small nonzero real sources, both
remainder classes on the same data, the literal lattice sum, and bounded,
nonnegative suprema on all disks.

This p=8 obstruction at exponent two did not by itself prove full
optimality. The subsequent half-exponent optimality milestone recorded
here proves that assertion for every finite p>2 and every r<p/2, using
actual sources. The printed remainder formula remains refuted. The
next source statement is Lemma 10.10; the dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,902 build jobs, the complete public example suite, and the axiom audit of 32,016 NLS declarations). The build retains 21 existing warnings; the four new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Remark 10.9: full half-exponent optimality in Remark 10.9

Six modules prove the full p/2 optimality assertion for actual source
potentials. For every finite p>2, every r<p/2, and every open neighborhood
U of zero in the original source space, there is a real ψ in U and one
constructed original isolating-disk family such that all three sequences

- the actual squared spectral gaps γ_n²;
- the signed lattice sum sum_(m≠n) γ_m²/(m−n)²;
- the literal supremum over D_n of |product_(m≠n)(τ_m−z)/w_m(z)−1|

belong to ℓ(p/2) and fail membership in ℓr. The same source and disk
family witness all three conclusions. The witness may depend on r;
this is optimality of the general exponent, not a claim that every
potential has exactly that regularity. The free source has zero quotient
supremum and remains an explicitly checked smooth special case.

`StrictSquaredExponentWitness.lean` proves the sharp squared-sequence
behavior of |n|^(-1/(2r)) and its nonzero real multiples.
`SourceSquaredGapSharpness.lean` lifts these real sequence witnesses
through the actual inverse Birkhoff chart inside any prescribed source
neighborhood. The action-radius and normalized-action identities force
the actual squared gaps to fail the stronger exponent.

`SourceMidpointTaylorLowerBound.lean` identifies the linear Taylor sum
at nπ with a convergent nonnegative real sum. A unit bound on the midpoint
displacement gives the neighboring lower estimate

    |γ_m|² ≤ 8(π+1)² |L_(m+1)((m+1)π)|.

`SourceMidpointQuotientSup.lean` proves boundedness and nonnegativity of
the literal quotient supremum and retains its ℓ(p/2) upper membership on
every original disk for p>2. `SourceMidpointQuotientSharpness.lean` shows
that stronger quotient-supremum summability would force stronger
squared-gap summability, by combining the lower estimate with the exact
ℓ(p/4) Taylor remainder and restoring the finite central head.

`SourceRemark10_9Optimality.lean` chooses an intermediate exponent q
between max(r,1,p/4) and p/2. This lets the argument cover every r<p/2,
including r≤1 and the finite-support exponent zero. The public theorem
is `sourceRemark10_9_halfExponent_optimal`. Nine public checks cover the
generic original-topology statement, p=3 and p=8 specializations, the
finite-support endpoint, a central neighboring gap, all-disk upper
membership, and the free-source exception.

Remark 10.9's audit is now resolved: its full general-exponent optimality
assertion is proved, its printed remainder display is formally refuted,
and the exact moving-denominator ℓ(p/4) expansion is the proved correction.
Next: Lemma 10.10, equation (2.15), and the remaining Section 10 statements.
The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,908 build jobs, the complete public example suite, and the axiom audit of 32,050 NLS declarations). The build retains 21 existing warnings; the six new modules and nine focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.10: all critical offsets on the unchanged common domain

`SourceLemma10_10.lean` proves the source statement for every finite p>1
on the same common W as the preceding Section 10 data. Its exact identity
is

    critical_n = midpoint_n + gap_n² * sourceCriticalGapQuotient(ψ)_n.

The coefficient is the actual deleted-product derivative quotient,
not a sequence selected separately for each estimate. It belongs to ℓp;
each coordinate is complex analytic on W. For every φ∈W there is an open
connected V with φ∈V⊆W and a positive K, chosen before ψ∈V and n∈ℤ,
such that the full coefficient norm is at most K.
`SourceLemma10_10Data.locally_uniform_powerSum` also gives a common bound
for the literal sum over all signed indices of |a_n|^p. Thus the result
has the local uniformity in the original source topology required by the
printed statement and its proof.

`SourceCriticalGapCommonIsolation.lean` proves nonvanishing of the
quadratic offset coefficient for an arbitrary original isolating family.
The deleted periodic product is nonzero at the critical root. At a
collapsed gap, spectral exhaustiveness and disjointness identify the
critical root with the common endpoint; at an open gap, the existing
quadratic identity supplies nonvanishing. Both cases include central
indices and complex sources.

`SourceCriticalGapCommonAnalytic.lean` composes the jointly analytic
deleted product and its spectral derivative with the critical-root graph.
The denominator is nonzero throughout W, so the quotient is analytic
even where the selected gap vanishes. A finite block is uniformly bounded
on one neighborhood. Combining this with the existing distant-root ℓp
estimate proves the full-sequence bound in `SourceLemma10_10.lean`.

`SourceLemma10_8Estimates.criticalOffsets` upgrades any existing open W
without shrinking it, and retains all preceding common-domain data.
`sourceLemma10_10` constructs the resulting open connected neighborhood
of the entire real-type locus. Six public checks include complex central
collapsed gaps, preservation of W, simultaneous all-index identities and
power-sum bounds, p=3/2, and arbitrarily small real-base neighborhoods.

Next: equation (2.15), admissible paths, and Lemma 10.11. The dissertation
remains incomplete.

Validation: `./scripts/check.sh` passed (6,911 build jobs, the complete public example suite, and the axiom audit of 32,074 NLS declarations). The build retains 21 existing warnings; the three new modules and six focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Equation (2.15): full product and analytic domains

`SourceCriticalRootRatioProduct.lean` proves the literal identity

    Δ′(z,ψ) / canonicalRoot(z,ψ) = -i * product_m ((critical_m(ψ)−z)/w_m(z,ψ)).

The product runs over all integers and is an unconditional `HasProd`,
not only a symmetric paired limit. Individual factor deviations from one
are absolutely summable. The normalized symmetric cutoff products also
converge to the actual quotient. These facts hold for every complex source
at every spectral point outside its periodic gap segments.

The proof specializes the existing absolute quotient-factor estimate to
the actual critical displacement. Inserting a singleton into the omitted
product gives the full product without requiring nonzero numerator
factors. The selected-factor identity fixes the printed -i normalization.
In particular, a zero critical numerator factor makes both the quotient
and product zero. At the free source off the gaps, the product is one and
the quotient is -i.

`SourceCriticalRootRatioCommonDomain.lean` derives joint analyticity of
the actual quotient from the joint discriminant derivative and canonical
root on the retained moving-gap domain. The literal product is i times
that quotient on this open domain and is therefore jointly analytic too.
For any original isolating family, both functions are analytic on the
complement of the union of closed disks times the original source
neighborhood. The closure bars in the printed p.59 domain were checked
against the rendered PDF. Fixing a source gives the stated spectral
analyticity on the complement of the union of all gap segments.

The same module proves analyticity of the selected omitted critical
factor through its selected gap on the retained W, ready for the
removability argument in Lemma 10.11. This does not yet assert an extension
across all collapsed gaps or the admissible-path integral statement.

`SourceEquation2_15.lean` retains `SourceLemma10_10Data` together with the
literal product, normalization, convergence and both analytic domains.
`SourceLemma10_10Data.criticalRootProduct` works on any existing common W
without shrinking it; `sourceEquation2_15` constructs the open connected
common domain containing the entire real-type locus. Seven public checks
cover complex sources, zero factors, the free sign, literal cutoff limits,
the retained closed-disk domain and p=3/2.

Next: admissible paths and Lemma 10.11. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,914 build jobs, the complete public example suite, and the axiom audit of 32,104 NLS declarations). The build retains 21 existing warnings; the three new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11(i): one analytic extension across all collapsed gaps

`SourceCriticalRootRatioRegularizedProduct.lean` defines a single
function on the spectral plane:

    continuedRatio(z,ψ) = -i * product_m F_m(z,ψ),
    F_m = 1 if gap_m=0, and (critical_m−z)/w_m(z) otherwise.

The individual deviations from one are absolutely summable and the
product is unconditional. Off all gaps the filled factors equal the
original factors, so equation (2.15) identifies this function with the
actual discriminant derivative divided by the canonical root. If the
selected gap n is collapsed, the function agrees with the selected
omitted analytic product on its entire omitted domain, including the
common endpoint. No selected denominator is divided out at that point.

`SourceCriticalRootRatioOpenGapDomain.lean` reuses the existing
`sourceOpenGapComplement`, literally the complement of the union of all
nonzero gap segments. On W it equals the union of the original cut
complement and the omitted domains of all collapsed indices. Each set
in this cover is open, and on each the same continued product equals an
analytic function. This proves openness of the full enlarged spectral
domain and analyticity of the continued product there. The construction
works for every complex source in W, every signed index, and infinitely
many collapsed gaps. There is no real-source or finite-gap restriction.

`SourceLemma10_11i.lean` packages the full statement of part (i), retains
`SourceEquation2_15Data`, and gives agreement on every original disk whose
selected gap has collapsed. `SourceEquation2_15Data.collapsedContinuation`
upgrades the existing W without shrinking it. `sourceLemma10_11i`
constructs the resulting common open connected neighborhood of the entire
real-type locus, and `.exists_analytic_extension` exposes the literal
existential extension assertion on the printed noncollapsed-gap domain.

The free-source check distinguishes analytic continuation from Lean's
totalized division: at every free lattice point the continued function
is -i whereas the raw quotient is 0/0=0. The continued function is entire
at zero source, where all infinitely many gaps have collapsed. Other
public checks cover a complex collapsed central endpoint in its original
disk, the actual product limit, retention of W and p=3/2.

The admissible-path definition and both integral conclusions of part (ii)
remain for the next audit. This milestone does not claim their completion
or completion of the dissertation.

Validation: `./scripts/check.sh` passed (6,917 build jobs, the complete public example suite, and the axiom audit of 32,137 NLS declarations). The build retains 21 existing warnings; the three new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11(ii): original periods and arbitrary closed contours

`RealCenteredCircleHomotopy.lean` proves the projection geometry needed
to compare circles from different original disk families. Disjoint disks
with real centers have disjoint real projections. The two selected disks
both contain the selected gap's left endpoint, so their real projections
overlap. Every other-gap point must therefore lie on the same side of
both selected projections. Convexity of the relevant open half-plane
keeps the affine circle homotopy away from that point. The selected gap
stays inside both endpoint circles and also avoids the homotopy.

`SourceCriticalRootPeriodCircle.lean` extracts this geometry from every
original isolating family and proves equality of the actual quotient
integrals. Neither nesting nor a larger gap-avoiding outer disk is
assumed. Both the original boundary circles and the homotopy avoid all
gaps, including at complex sources and for collapsed selected gaps.

`SourceCriticalRootPeriod.lean` defines one indexed period by choosing an
isolating circle, proves independence of that choice, and identifies it
with each original fixed-circle integral throughout its original source
neighborhood. Joint analyticity of the actual quotient gives a complex
Fréchet derivative under the contour integral. The local representatives
therefore prove analyticity of the period on all of the retained W.

`SourceCriticalRootPeriodZero.lean` uses a real base only to obtain an
open zero germ. The Banach-space analytic identity theorem propagates
that germ throughout the preconnected W. It does not replace W by the
seed neighborhood. Every original selected circle consequently has zero
period at every complex source in W. The package retains the full
collapsed-gap continuation from part (i) and all preceding source data.

`SourceCriticalRootOriginalDiscPrimitive.lean` transfers the zero period
to a smaller enclosing circle and uses an annular primitive followed by
radial continuation. The resulting primitive is defined on the entire
original disk minus the selected gap, with the original outer radius
unchanged. Its derivative is the actual quotient. Primitive differences
telescope on every finite piecewise C¹ closed contour in that domain.
No separate integrability assumption is needed: continuity of the
quotient on each compact smooth piece supplies it. Corners, repeated
traversals and self-intersections are allowed; no prescribed homotopy
or winding number is required.

Eight public checks cover preservation of W and part (i), different
original circle families without nesting, analytic dependence on all W,
propagation from one real base, the full original central disk, general
piecewise contours, ordinary smooth curve integrals, and p=3/2.

The endpoint-path assertion is still outstanding. Its intended scope
includes complex endpoints and arbitrary admissible paths; a real-source
or half-plane result would not suffice. Endpoint integrals may need to be
expressed as improper limits of truncated integrals rather than assuming
absolute integrability for every admissible parametrization.

Validation: `./scripts/check.sh` passed (6,922 build jobs, the complete public example suite, and the axiom audit of 32,193 NLS declarations). The build retains 21 existing warnings; the five new modules and eight focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Lemma 10.11: arbitrary admissible endpoint paths

`SourceCriticalRootCommonEndpointLimit.lean` proves that every actual
primitive on an original cut disk has the same full relative limit at
both spectral endpoints. For a noncollapsed complex gap, existing
inverse-square-root estimates give finite limits along every approach
within the cut disk. The cosine coordinate then pulls the primitive back
to two analytic angle charts with opposite sheet coefficients. Its endpoint
difference is both equal and opposite on those charts, hence zero.
There is no assumption that the endpoints are real or horizontally ordered.
For a collapsed gap, the omitted quotient is analytic through the cut.
An analytic primitive on the full disk is adjusted by a constant to agree
with the given primitive on the whole cut disk, giving its endpoint limit.
All omitted-factor analyticity comes from the existing common W.

`ImproperPrimitivePathIntegral.lean` defines a truncated integral by

    integral_(u..v) quotient(path(t)) * path'(t) dt.

The improper integral is the limit as u approaches zero from above and v
approaches one from below, independently. Every compact interior truncation
is integrable, and the fundamental theorem of calculus evaluates it as
the primitive difference. Full relative boundary limits prove existence
of the improper limit. This does not infer absolute integrability from
an arbitrary path's approach to a square-root endpoint. When the full
curve integral is integrable and the path is C¹ up to its endpoints, the
improper definition agrees with the ordinary curve integral.

`PiecewiseImproperPathIntegral.lean` handles finite chains of continuous
paths, each C¹ on its open parameter interval. Derivatives need not match
or even exist at the endpoints of individual pieces. Its improper integral
is a limit of sums of actual truncated piece integrals. Primitive
differences telescope across all intermediate vertices, including corners.
The empty chain is allowed and also has zero integral when its endpoints
coincide. Thus the class includes ordinary finite piecewise C¹ contours
and also permits singular endpoint parametrizations.

`SourceAdmissibleEndpointPath.lean` defines admissibility exactly by
avoidance of every indexed gap in the path interior. For a piecewise path,
this includes the interior corner vertices. The common endpoint primitive
gives zero improper integral for every such path in every original D_n,
at every complex source in W. No half-plane restriction, supplied homotopy,
reality assumption, or full-path absolute-integrability hypothesis is used.
The ordinary curve integral vanishes whenever it is absolutely integrable.

`SourceLemma10_11.lean` packages these endpoint assertions alongside the
previous analytic continuation and original closed-contour conclusions.
`SourceLemma10_11CircleData.admissibleEndpoints` strengthens any existing
package without shrinking W or changing the original disks. The public
`sourceLemma10_11` constructs the full package for every finite p>1 on the
retained open connected neighborhood of the entire real-type locus.

Nine public checks cover the source's quantifiers and the integral
conventions. Besides unchanged W, complex central endpoints, cornered
paths and p=3/2, they prove nonzero reference integrals: integrating one
along the segment 0→1 yields one, and along any piecewise chain a→b yields
b−a. Thus the zero endpoint theorem concerns genuine integral limits,
not a function defined to equal zero or defined by primitive values.

Both parts of Lemma 10.11 are now covered with this explicit standard
path-integral interpretation. Next: Section 11. The dissertation as a
whole remains incomplete, and the earlier Section 10 source corrections
and counterexamples are retained.

Validation: `./scripts/check.sh` passed (6,927 build jobs, the complete public example suite, and the axiom audit of 32,249 NLS declarations). The build retains 21 existing warnings; the five new modules and nine focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.

## Individual labels on the same almost-real domain, printed p. 55

The unnumbered paragraph before Lemma 10.2 states that individual periodic
eigenvalue labels need not be continuous on the almost-real domain. This
is now proved for the actual central pair in
[SourceAlmostRealLabelDiscontinuity.lean](../NLS/ZakharovShabat/SourceAlmostRealLabelDiscontinuity.lean),
using the original-source witnesses from the [Section 8 audit](SECTION_8.md).

For every finite p>1 and every source neighborhood V of zero,
`exists_sourcePeriodicLabels_not_continuousWithinAt` gives a positive r
such that the constant source (r,-r) lies in the interior of V and both
central endpoint labels fail continuity within V there. The proof chooses
the existing witness inside that interior. Since V is a neighborhood of
the witness, continuity within V would imply the already refuted ambient
continuity. Openness of V itself is unnecessary.

`sourcePeriodicLabels_not_continuousOn` consequently rules out continuity
of either endpoint map on V. Applying it to the original domain supplied
by `sourceLemma10_2` gives `sourceLemma10_2_with_discontinuous_labels`.
The same W retains its openness, connectedness, entire real-type locus,
isolation data, all analytic symmetric coordinates and simple ordinary
roots, and the original locally uniform sequence estimates. No further
domain restriction is needed.

Three public examples cover the full common-domain package at p=3/2, an
arbitrary open neighborhood of the real locus at p=2, and a positive
closed source ball at p=4. These are existence statements for
discontinuities of the central labels. They do not assert discontinuity
at zero, at every source, or for every signed spectral index.
