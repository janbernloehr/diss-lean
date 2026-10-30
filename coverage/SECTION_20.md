# Section 20: original moments and renormalized frequencies

## Positive quarter-exponent remainder

The stronger action-gap remainder on p. 96 is now proved in
[SourceActionGapQuarter.lean](../NLS/ZakharovShabat/SourceActionGapQuarter.lean):
`gamma_n^2/4 = I_n + ell_n^(p/4) + ell_n^(1+)`.

The proof multiplies the normalized-action deviation by the actual
squared gap. Its sequence product estimate includes exponents below one.
A common connected complex neighborhood can be chosen inside any
prescribed open neighborhood of the real locus, preserving every real
source. The two remainder sequences are fixed before all auxiliary
exponents, with locally uniform bounds for all signed indices and
collapsed gaps.

Three positive theorems and four API examples close S20-052. The
[Section 20 ledger](SECTION_20_ASSERTIONS.md) now has 45 matched
groups, eight corrections or scope clarifications, one partial auxiliary
assertion and two contextual groups. The corrected contour constants and
the original action-image scope are preserved. No new refutation is added.

The complete ./scripts/check.sh passed: 8,561 build jobs, 7,644 public examples and a transitive axiom audit of 44,618 NLS declarations. The check includes the new module and four new API examples, with 21 inherited warnings and zero new warnings. The examples cover the exact p=8 endpoint target, a p/4 exponent below one, restriction inside a prescribed source domain, and a source exponent below two at a negative gap index. Source-review hashes, declaration references and local documentation links are checked separately. These checks do not certify complete formalization.

Next: the full-U_k auxiliary estimate S20-030, then Section 21. Wider
qualifications remain in the [completion assessment](COMPLETENESS.md).

The earlier ordered-review entry records both intermediate gaps before this addition.

## Ordered source comparison

The [ordered Section 20 ledger](SECTION_20_ASSERTIONS.md) classifies
56 passage groups on pp. 91–96: 44 matched, eight corrected or clarified,
two partial intermediate assertions and two contextual groups.

The main moment and frequency theorems are already proved: actual contour
moments, all-order vanishing at collapsed gaps, the physical H1 bracket,
the second-moment frequency formula, mixed sequence estimates, analytic
frequency maps including the infinity target, and the inverse/Fredholm
consequences on the original action image.

The off-diagonal proof retains `i/pi` and `-2*i/pi`, and the numerator
maximum is over the selected integration gap G_k. The cubic constant is
`-3*i*H2/4`. Existing positive Lean proofs already use these constants.
The comparison also records the auxiliary-domain restriction, collapsed
moment indices, finite-support label and compactness reference. The
regular diagonal zeta symbol in (4.9) is already correct.

Two positive intermediate assertions remain explicit: the auxiliary
estimate throughout U_k (S20-030), and the stronger p/4 action-gap
remainder (S20-052). The actual-gap estimate and p/3 remainder used in the
main theorems are already proved. The action-image qualification is
preserved: every real-source action and the nonnegative ell1 cone are
included, without asserting the whole nonnegative ell^(p/2) cone.

The review inspected 72 complete module bodies, the positive excerpt of
the factor module, and 99 public declaration references. It adds no Lean
code or refutations.

This documentation-only step reuses the successful full check from commit 42c1d69 on the exact unchanged Lean and dependency-lock snapshot: 8,560 build jobs, 7,640 public examples and 44,615 transitively audited NLS declarations, with 21 inherited warnings and zero new warnings. No new full build is claimed. Current module hashes, declaration references, source-review integrity and local documentation links are checked separately. These checks do not certify mathematical completeness.

Next: prove or link the two positive intermediate assertions, then proceed
to Section 21. Wider qualifications remain in the
[completion assessment](COMPLETENESS.md).

Earlier entries retain their historical scope and validation.

This audit covers the contour moments and numbered results on printed
pp. 91–96. For every finite 1<p<∞, `sourceSection20_original` constructs
an original Section 17 Birkhoff family D and `SourceSection20Data D A B U`.
An already chosen original family can be retained with `D.exists_section20`.
The moment atlas A uses that family's original normalized roots. The open
connected source domain U lies inside its original complex domain V,
contains every real source, and retains the Section 19 primitive on B.

## Assertion map

Here Q denotes the constructed `SourceSection20Data` and M a local
`SourceSecondMomentMixedData` supplied by `Q.moment_estimates`.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Definition of the moments, p. 92 | `Q.moment_contours` | Actual raw circle integrals of the retained Section 19 primitive to power m times the original psi function divided by the canonical root; one admissible circle family for all indices and orders |
| Opening physical energy bracket, p. 92 | `Q.sobolev_energy_bracket_complex`, `Q.sobolev_energy_bivector_complex`, `sourceSection20_original_complex_sobolev` | Full physical H¹ energy derivative along the actual original H¹ angle vector gives the restored original frequency on all H¹_c ∩ (U \ Zₙ); any representing Hilbert cotangent gives the original bivector |
| H¹ regularity of the original angle vector | `Q.sobolevThetaVector_inclusion_complex`, `Q.existsUnique_sobolevThetaVector_complex`, `Q.sobolevThetaVector_spatial_complex` | Explicit bounded derivative-graph recovery, original coefficients, unique lift, exact spatial derivative, and analytic H¹ dependence on the full complex open-gap domain; real type, nonzero direction, and family independence on the real locus |
| Complex H¹ domain and continuation | `Q.isConnected_sobolev_openGapDomain`, `Q.eqOn_sobolev_openGapDomain_of_real_germs` | The whole original H¹ open-gap domain is open and connected; real germs determine analytic maps on it, without any index-dependent shrinking of U |
| Physical momentum contour | `Q.momentum_contour`, `sourceFullAbelianMomentumContour_eq_physical_of_enclosing` | Actual physical H₂ equals −i/π times the quadratic contour of the retained primitive, at real finite-gap sources; any positive circle enclosing all open gaps is allowed |
| Physical angle–momentum bracket on H¹ | `Q.finiteGap_momentum_bracket`, `Q.sobolev_momentum_bracket`, `sourceSection20_original_momentum` | Actual original bivector equals 2πn at every real H¹ source with gap n open; the original constructor supplies all data |
| Complex momentum normalization | `Q.sobolev_momentum_bracket_complex` | Actual physical bracket equals 2πn throughout H¹_c ∩ (U \ Zₙ); the same original U is chosen before every n |
| Lemma 20.1(i) | `Q.lemma20_1` | Exact zero-order value 2πδₖₙ, with no factor i |
| Lemma 20.1(ii) | `Q.lemma20_1` | Every moment is complex analytic on U, including order zero |
| Lemma 20.1(iii) | `Q.lemma20_1` | Every odd moment vanishes |
| Lemma 20.1(iv) | `Q.lemma20_1` | Every positive-order moment vanishes when the selected gap collapses, including the diagonal case |
| Lemma 20.2 | `Q.physical_frequency` | Independently constructed physical frequency minus 4H₁ and the free dispersion equals −4/(2π) times the second-moment sum, for every real finite-gap source and every index |
| Equations (4.9)–(4.10) | `SourceSection20Data.diagonal_factor`, `.offDiagonal_factor`, `.zeta_product`, `.auxiliary_eq_zeta` | Literal factors and convergent negative product, with the unused root filled by its midpoint; the off-diagonal quotient identity has k≠n |
| Analyticity after (4.9), corrected | `Q.zeta_analytic`, `Q.auxiliary_analytic` | The regular product fills the selected gap; the printed auxiliary quotient is analytic on the omitted-gap domain with τₙ excluded |
| Failure of the unrestricted diagonal claim | `Q.printed_diagonal_auxiliary_not_continuous` | At the actual zero source the printed auxiliary factor for k=n is not continuous at nπ |
| Lemma 20.3, diagonal | `M.diagonal` | Ωₖₖ²=γₖ²/4 times π plus one locally bounded ℓ^(p/2)+ℓ^(1+) error |
| Lemma 20.3, off-diagonal | `M.rows`, `M.refined`, `M.row_power_sum` | Ωₙₖ²=γₖ³/(n−k) times the mixed error; row norms and actual coefficient power sums are bounded uniformly in n |
| Theorem 20.4, series | `Q.summable`, `Q.frequency_hasSum`, `Q.frequency_uniform` | Absolute convergence, the exact sum, and locally uniform convergence of symmetric partial sums on one neighborhood chosen before n |
| Theorem 20.4, extension and uniqueness | `Q.frequency_analytic`, `Q.unique_frequency` | Analytic continuation to U, uniquely determined by the physical real finite-gap values |
| Theorem 20.5, sequence map | `Q.sequence_analytic`, `Q.sequence_zero` | Analytic ℓ^r realization for every finite r>1 with r≥p/2, real coordinate values on real sources, and exact value zero at zero |
| Theorem 20.5, asymptotics | `Q.frequency_mixed` | The actual corrected sequence ω*+γ²/2 has one locally bounded ℓ^(p/3)+ℓ^(1+) decomposition |
| Compatibility of the source exponents | `Q.frequency_eq_of_coefficients` | Independently chosen original families give the same frequencies on real sources with identical Fourier coefficients |
| Identification with the original Section 18 action frequency | `Q.action_frequency`, `Q.action_frequency_complex`, `Q.hilbert_action_frequency` | Equality on every real source, and for the higher-exponent map on one common connected complex neighborhood containing the entire real locus |

## The same roots, primitive, and physical frequency

[`SourceSection20Domain.lean`](../NLS/ZakharovShabat/SourceSection20Domain.lean)
constructs the moment atlas from the original normalized roots, then
intersects the domains of the estimates, scalar frequencies, sequence maps,
and original Birkhoff family. The Section 19 construction supplies an open
connected subdomain retaining all real sources. Thus no supplied moment
atlas, local estimate, or frequency realization is a hypothesis of
[`SourceSection20Original.lean`](../NLS/ZakharovShabat/SourceSection20Original.lean).

[`SourceSection20Moments.lean`](../NLS/ZakharovShabat/SourceSection20Moments.lean)
uses proved neighborhood independence to identify the literal contour
integral with the very primitive retained by Q's Section 19 package.
The displayed contour representation uses admissible isolating circles.
Its raw-integral convention gives 2πδₖₙ at order zero and the coefficient
−4/(2π) in the frequency formula.

The physical frequency in Lemma 20.2 comes from the original Hilbert
Hamiltonian derivative. It is not defined to be this contour sum.
The identity works at every source exponent and includes collapsed
selected gaps. Analytic uniqueness uses agreement on actual real finite-gap
sources, the finite-gap density theorem, and the connected complex domain.

[`SourceSection20Frequencies.lean`](../NLS/ZakharovShabat/SourceSection20Frequencies.lean)
identifies these moments with any previously chosen original action
frequency. For the complex identity, the domain is the component of zero
in U intersected with the preimage of that frequency's action domain.
It is open, connected, and contains every real source. No equality on the
whole original complex domain V is asserted. The action-domain construction
used in the proof of Theorem 18.1 on p. 96 is audited separately in
[Section 18](SECTION_18.md).

## Mixed estimates and quantifiers

[`SourceSecondMomentMixed.lean`](../NLS/ZakharovShabat/SourceSecondMomentMixed.lean)
turns the existing refined estimates into fixed mixed remainder sequences.
Both components g and h, as well as the source neighborhood, are chosen
before the auxiliary exponent. The second component is one sequence in
every finite ℓ^q, q>1, with a locally uniform bound for each projection.
The off-diagonal bounds are uniform in the deleted index n. The first
component may be quasi-normed: neither p/2 nor p/3 is required to be at
least one. No analyticity of the chosen bounding sequences is asserted.

The refined estimates retain the actual diagonal and cubic moment
coefficients. The literal r-power sum is bounded on the whole integer
index set; the diagonal coefficient is zero, so this also gives the
printed sum over k≠n. The decomposition and factorization remain valid
at collapsed gaps.

For the scalar frequency series, one open neighborhood works for every
n. The convergence assertion is uniform in the source on that neighborhood
for each n; it does not assert a convergence rate uniform over n.
All target sequence exponents share U. At p=2 the target can be any finite
r>1; at p>2 it includes r=p/2. The follow-up below also proves the
l-infinity target on the same unchanged original complex source domain.

## Printed auxiliary factor

[`SourceSection20Factors.lean`](../NLS/ZakharovShabat/SourceSection20Factors.lean)
retains the literal negative product ζₖ and the printed quotient
ζₖⁿ=−i ζₖ/(τₙ−λ). The regular ζₙ is analytic across its selected gap.
At the actual zero source, ζₙ=−1 locally at nπ, so the diagonal auxiliary
quotient equals i/(nπ−λ) away from its center. Its noncontinuity is proved
for every original family constructed here. The unrestricted analyticity
sentence following (4.9) therefore needs a restriction to k≠n for the
auxiliary factor on the isolating disk. The diagonal factorization uses
the regular ζₙ. See [the source correction](../SOURCE_ERRATA.md).

## The physical H¹ angle tangent and energy bracket

[`SourceFiniteGapAngleWeighted.lean`](../NLS/ZakharovShabat/SourceFiniteGapAngleWeighted.lean)
proves `D.existsUnique_finiteGap_thetaHamiltonian_weighted`. For a real
finite-gap source represented in a spectral weight, the original angle
Hamiltonian has a unique tangent in that same weight. The proof uses the
actual action-reduction curve, its fixed closed-gap tail, and the analytic
weighted reconstruction. Differentiating the decoding identity recovers
the unchanged original Fourier coefficients. It does not assume that the
angle vector already has weighted regularity.

[`SourceFiniteGapAngleSobolev.lean`](../NLS/ZakharovShabat/SourceFiniteGapAngleSobolev.lean)
specializes this construction to H¹, using the existing physical H¹
representative of every real finite-gap source. The resulting
`D.finiteGapThetaSobolevVector E` is unique, independent of both the
auxiliary Birkhoff realization and normalized angle family, and nonzero
on an open selected gap. Its action derivative is exactly −δₙₖ.
`D.hasDerivAt_hilbertActionReduction_sobolev` proves that the actual
physical H¹ representatives of the action-reduction curve differentiate
to this tangent at every t<Iₙ(φ), including negative times.

[`SourceFiniteGapAngleEnergy.lean`](../NLS/ZakharovShabat/SourceFiniteGapAngleEnergy.lean)
then applies the full complex H¹ energy differential to that tangent.
The chain rule identifies it with the derivative of the independently
defined physical Hamiltonian along the original action-reduction curve.
Since this curve decreases Iₙ at unit speed, the physical frequency is
the negative energy derivative. The proof uses the physical H¹ energy,
not just a scalar contour functional with the same value at the base point.

At each real finite-gap source there is one Hilbert cotangent whose H¹
restriction is the full physical energy differential in every complex H¹
direction. Its source Poisson bivector against the original angle
cotangent is the same physical frequency, simultaneously for every open
gap. The equality is also proved for any other Hilbert cotangent with
that restriction; no such cotangent is assumed in the existence theorem.

[`SourceSection20EnergyBracket.lean`](../NLS/ZakharovShabat/SourceSection20EnergyBracket.lean)
attaches both identities to Q's actual original family. The final value is
ω*ₙ+4H₁+(2nπ)², where ω*ₙ is the already proved original moment sum.
The bracket requires an open selected gap because the angle cotangent is
singular at collapse. The existing moment-frequency extension still
includes collapsed gaps; no angle bracket there is asserted.

## Physical momentum and spatial translation on complex H¹

[`SourceSobolevMomentumDifferential.lean`](../NLS/ZakharovShabat/SourceSobolevMomentumDifferential.lean)
constructs `sourceSobolevMomentumCotangent`, a bounded complex-linear map
from H¹ sources to Hilbert cotangents. Its coefficients are the reflected
physical gradients (−ib′, ia′). Periodic integration by parts proves that
its restriction is the full complex derivative of the independently
defined physical momentum −i∫ab′. Density of H¹ variations proves uniqueness.
The actual source Hamiltonian direction is (a′,b′), with the period-one
Fourier multiplier 2πin and the original Poisson signs.

[`PhaseFlowDerivative.lean`](../NLS/SequenceSpaces/PhaseFlowDerivative.lean)
proves strong norm differentiation for arbitrary real diagonal frequencies
whenever the generator velocity belongs to the same finite-exponent
coefficient space. No frequency bound or finite-support hypothesis is
used. Bounded coordinate evaluations and the scalar fundamental theorem
supply the full Banach-space integral identity.

[`SourceSobolevMomentumTranslation.lean`](../NLS/ZakharovShabat/SourceSobolevMomentumTranslation.lean)
applies that theorem to actual period-one translation. Every complex H¹
source has an L² derivative along its translation orbit, at every real
time. At time zero it is the physical momentum Hamiltonian direction.
For any differentiable Hilbert functional, its original momentum bracket
is its actual translation derivative. Spatial invariance implies a zero
bracket.

[`SourceSobolevAngleMomentum.lean`](../NLS/ZakharovShabat/SourceSobolevAngleMomentum.lean)
defines the original angle–momentum bracket using the actual two
cotangents. It is analytic on the complex H¹ preimage of the original
open-gap domain. A constructed local analytic angle has translation
derivative equal to this bracket. Whenever an actual H¹ angle tangent
is available, the bracket is its negative physical momentum derivative.

[`SourceFiniteGapAngleMomentum.lean`](../NLS/ZakharovShabat/SourceFiniteGapAngleMomentum.lean)
uses the previously constructed H¹ angle tangent at real finite-gap
sources, so no new tangent regularity is assumed. The physical second
hierarchy Hamiltonian along the original action-reduction curve has
derivative minus the bracket, throughout the full pre-collapse interval.
At the base point, the bracket is therefore −dH₂/dt along that curve.
All these statements retain arbitrary original normalized angle families;
public checks also specialize them to the original Section 17 family used
in Section 20.

## Exact physical momentum normalization

[`SquareInversionContour.lean`](../NLS/ComplexAnalysis/SquareInversionContour.lean)
extracts the simple-pole coefficient of the squared inverse-frequency
phase with an exact analytic inverse-square remainder. The contour is
πiH₂. No differentiation of an asymptotic error term is assumed.
[`SourceFullAbelianMomentumContour.lean`](../NLS/ZakharovShabat/SourceFullAbelianMomentumContour.lean)
therefore identifies physical H₂ with −i/π times the quadratic contour
of the original full primitive. Neighborhood independence retains any
original ambient chart; annular Cauchy deformation permits any positive
circle enclosing all open gaps. Fixed finite gap support gives the local
identity needed along the actual action-reduction curve.

[`SourceAbelianMomentLinearShift.lean`](../NLS/ZakharovShabat/SourceAbelianMomentLinearShift.lean)
uses F₀=Fₖ−ikπ, the vanishing first moment, and the period 2πδₖₙ to
evaluate the linear psi contour.
[`SourceFullAbelianMomentumPoisson.lean`](../NLS/ZakharovShabat/SourceFullAbelianMomentumPoisson.lean)
identifies that contour with the actual angle bracket of the quadratic
contour. The primitive and moment atlas may use different ambient
neighborhoods, as they do in the retained Section 20 construction.

[`SourceFiniteGapMomentumNormalization.lean`](../NLS/ZakharovShabat/SourceFiniteGapMomentumNormalization.lean)
differentiates the local physical identity along the original
finite-gap action-reduction curve. This gives the physical bracket 2πn
and the physical H₂ action derivative −2πn.
[`SourceSobolevMomentumNormalization.lean`](../NLS/ZakharovShabat/SourceSobolevMomentumNormalization.lean)
extends the bracket identity to every real H¹ source with the selected
gap open, by H¹ finite-gap density. Real-form analytic uniqueness then
gives a constant complex germ at each such source.

[`SourceSection20MomentumBracket.lean`](../NLS/ZakharovShabat/SourceSection20MomentumBracket.lean)
packages the results with Q's original roots and Section 19 primitive.
Its constructor is unconditional. For each n, an open complex H¹ domain
contains every real H¹ source with gap n open and lies inside the original
Section 20 domain. The construction uses the interior of the equality
locus and verifies its neighborhood property at each real open-gap source.
It does not intersect infinitely many neighborhoods. Differentiating
these germs supplies the H¹ angle-vector recovery and energy identity
below. The subsequent connected-domain continuation extends both
identities to the whole original H¹ open-gap domain.

## H¹ angle recovery and the physical energy identity

[`SourceSobolevSpatialGraph.lean`](../NLS/ZakharovShabat/SourceSobolevSpatialGraph.lean)
constructs a bounded linear operator recovering H¹ coefficients from an
L² source and its period-one spatial derivative. Its multiplier has the
opposite signs at positive and negative frequencies; the zero mode is
retained. The operator is a left inverse of the actual derivative graph,
and its fixed norm bounds the H¹ norm independently of finite-gap support.
Testing a cotangent integration-by-parts identity on signed Fourier modes
gives the exact differentiated coefficients of the original Hamiltonian
vector, with both source reflections and Poisson signs preserved.

[`SourceSobolevAngleVector.lean`](../NLS/ZakharovShabat/SourceSobolevAngleVector.lean)
differentiates the actual constant momentum bracket and uses the original
theta Hessian symmetry. If L=dθₙ and T is the physical spatial derivative,
the resulting identity L(T h)=−dL[T a](h) places J L in H¹ and identifies
its spatial derivative with J(dL[T a]). The explicit graph recovery is
analytic in the H¹ source. Its identification with the actual vector uses
the proved constant momentum germ, not just analyticity of a candidate.

[`SourceSection20AngleSobolev.lean`](../NLS/ZakharovShabat/SourceSection20AngleSobolev.lean)
supplies that germ from Q's original momentum identity. At every real H¹
source with gap n open, the vector is unique, real type, nonzero, has
unchanged original Fourier coefficients, and decreases Iₙ at unit speed
while leaving the other actions unchanged. It is independent of the
auxiliary original family and equals the earlier finite-gap H¹ tangent.
Each real open-gap source also has a complex germ of actual vectors.

[`SourceSobolevAngleEnergy.lean`](../NLS/ZakharovShabat/SourceSobolevAngleEnergy.lean)
defines the physical directional bracket as −dH(a)[Xθₙ(a)], using the full
complex H¹ differential of the independently defined physical energy.
It is analytic on the H¹ preimage of the original open-gap domain. The
same value is the original Poisson bivector whenever an L² cotangent
represents dH; existence of such a cotangent is not asserted for arbitrary
H¹ sources. Any H¹ lift with the original coefficients gives the same
physical directional bracket.

[`SourceSection20SobolevEnergy.lean`](../NLS/ZakharovShabat/SourceSection20SobolevEnergy.lean)
first calibrates this bracket with the earlier finite-gap physical result.
H¹ finite-gap density preserving the selected open gap then proves
{θₙ,H}=ω*ₙ+4H₁+(2nπ)² on every real H¹ open-gap source. This also agrees
with any previously constructed original Hilbert action frequency.
Real-form analytic uniqueness gives complex germs. For each index one
open H¹ domain contains all its real open-gap sources and carries both
the actual analytic vector and the physical energy identity, inside Q's
original domain. The original constructor supplies every package before
choosing a source or index.

## Full complex-domain continuation

[`DenseLinearConnectedPreimage.lean`](../NLS/ComplexAnalysis/DenseLinearConnectedPreimage.lean)
proves that the preimage of an open connected set under a dense real
linear map is connected. Ball preimages are convex, and density lifts
every overlap in a chain of balls. Continuity of the linear map is not
needed for this connectedness theorem.

[`AnalyticNonzeroConnected.lean`](../NLS/ComplexAnalysis/AnalyticNonzeroConnected.lean)
proves connectedness of the nonzero locus of any nontrivial scalar
complex analytic function on an open connected domain, including
infinite-dimensional domains. On convex pieces, a complex line reduces
the problem to a discrete countable zero set in an open convex subset
of the plane. Two line segments can avoid that set while remaining in
the domain. Analytic uniqueness makes each open ball overlap contain a
nonzero point, which connects the local pieces. The countable-complement
argument adapts Mathlib's proof with attribution and its license retained.

[`SourceSection20SobolevDomain.lean`](../NLS/ZakharovShabat/SourceSection20SobolevDomain.lean)
applies both results to the dense physical H¹ inclusion and the actual
squared periodic gap from the original angular data. The H¹ preimage of
U is connected, and removing Zₙ preserves connectedness and openness.
A constructed real H¹ single-action source proves that each squared gap
is nontrivial. Thus `sourceSobolevOpenGapDomain U n` is exactly the full
H¹_c ∩ (U \ Zₙ), with the same U for all indices.

[`SourceSection20ComplexSobolev.lean`](../NLS/ZakharovShabat/SourceSection20ComplexSobolev.lean)
uses analytic uniqueness to extend the actual physical momentum and
energy germs to every complex point of that domain. The constant
momentum germ there identifies the analytic graph recovery with the
unique original H¹ angle vector and gives its exact spatial derivative.
The energy bracket uses the full H¹ differential, and any representing
Hilbert cotangent gives the original Poisson bivector. The unconditional
constructor chooses every original package and U before every complex
source and index. No further source-domain shrink occurs in this step.

## Validation and remaining scope

Six new modules and 35 public examples cover the common-domain constructor,
all four moment clauses, physical normalization, uniqueness, mixed estimates,
literal power sums, both factorizations, the convergent product, the actual
diagonal counterexample, and compatibility with the action frequency.
Checks include p=3/2 with p/2<1 and p=5/2 with target r=5/4 and p/3<1.
Full gate results are recorded in [the implementation status](../STATUS.md).

The subsequent physical bracket step adds four modules and 15 public
examples. They check weighted and H¹ tangent uniqueness, preservation of
the original coefficients, the action sign and unselected-action zeros,
independence of the auxiliary families, the full pre-collapse H¹ flow
derivative, the energy differential, and one cotangent for all open gaps.
An actual source realizing a single nonzero action supplies a nonzero
H¹ angle tangent without a supplied open-gap witness.

The momentum step adds five modules and 25 public examples. In addition
to generic complex H¹ derivatives and uniqueness, the checks fix both
signed Fourier normalizations and the zero-mode cotangent, verify the
actual translation derivative and local angle realization, and retain
the original family's physical H₂ derivative.

The normalization step adds seven modules and 23 public examples. They
check the residue sign with an explicit Laurent polynomial, the physical
contour, the original bivector, the negative physical action derivative,
zero and negative indices, the translation derivative, complex germs and
their zero differential, the per-index domains, family independence, and
the unconditional constructor. A constructed source with one nonzero
action at index −1 gives an actual bracket −2π.

The H¹ extension adds five modules and 15 public examples. Checks include
zero and signed graph recovery, the exact reflected coefficients, the
selected action sign and unselected zero, the physical momentum sign,
H¹ graph and neighborhood bounds, zero and negative energy indices, a
physical energy derivative along a complex H¹ line, bivector consistency,
full complex differential equality, a common local domain for the vector
and bracket, family independence, and a constructed nonzero source.

The full complex continuation adds four modules and 13 public examples.
They check connected complements of complex coordinate hyperplanes and
two zeros in a disk, the full H¹ open-gap domain, signed and zero-index
momentum, cancellation of mass between two indices on the same domain,
complex physical energy differentiation, lift uniqueness, the actual
spatial graph bound, bivector consistency, full complex differential
equality, vector-valued analytic uniqueness, and an unconditional
constructor with U chosen before all sources and indices.

The opening p. 92 physical identity now holds on the full stated domain
H¹_c ∩ (U \ Zₙ), where U is the constructed Section 20 neighborhood.
The full-domain continuation and common-domain requirements are resolved;
U is unchanged from the original Section 20 package. This does not assert
an angle bracket at a collapsed selected gap or a representing L² energy
cotangent at every H¹ source. The subsequent original moment and
Hamiltonian construction is audited in [Section 21](SECTION_21.md).
[Section 14](SECTION_14.md) now proves native fractional Sobolev
analyticity and analytic inverses. Its precise 2014 construction
comparison remains unverified.

## Infinity target and the copied cubic expansion

Theorem 20.5(i), printed p. 95, allows every target exponent above one.
[SourceSection20FrequencyTop.lean](../NLS/ZakharovShabat/SourceSection20FrequencyTop.lean)
now includes infinity on exactly the same original complex source domain U.
For every finite source exponent p>1, the actual frequency sequence in lp
embeds continuously into l-infinity. The proof identifies that image with
the existing `frequencySequence` constructor by proving membership and
checking every scalar moment coefficient. Thus the constructor's fallback
is excluded, and both complex and real analyticity hold for the same map.
Real-source coordinate values and the zero-source identity are retained.
The theorem `sequence_analytic_all` includes every finite permitted target
and infinity. This extends the target range, not the source exponent.

There is also a transcription discrepancy in the proof of Lemma 20.2.
Printed p. 93 repeats Corollary 19.3 with constant term +3H2/4, although
[Corollary 19.3's implemented formula](../NLS/ZakharovShabat/SourceSection19Laurent.lean)
and the original p. 91 display have constant term -3iH2/4. Both PDF displays
were checked. Their difference is -(3/4)(1+i)H2, independent of lambda.

[SourceFiniteGapNonzeroMomentum.lean](../NLS/ZakharovShabat/SourceFiniteGapNonzeroMomentum.lean)
constructs an actual real finite-gap source with nonzero physical H2.
A signed Fourier mode has nonzero momentum, and H1 finite-gap density
preserves this open condition. The reconstructed physical Hamiltonian
is identified with that momentum; no nonzero-H2 witness is assumed.

[SourceSection20CubeConstantCorrection.lean](../NLS/ZakharovShabat/SourceSection20CubeConstantCorrection.lean)
then proves that the nonzero constant discrepancy cannot be included in
an O(lambda^-2) remainder. Every retained original Section 19 domain
contains an actual finite-gap counterexample to the p. 93 reprint. The
correct Corollary 19.3 expansion holds at the same witness.

The existing [original moment-frequency theorem](../NLS/ZakharovShabat/SourceSection20Moments.lean)
remains proved with the correct Laurent coefficient. The discrepancy is
in the constant term and does not change the coefficient extracted by
the subsequent contour integral. Four public examples check the infinity
target at p=4, bounded literal frequencies at p=3/2, the correct and false
expansions at the same actual source, and the unit-momentum discrepancy.

## Sobolev convergence of finite-gap opening, printed p. 93

[WeightedActionOpening.lean](../NLS/SequenceSpaces/WeightedActionOpening.lean)
constructs the native weighted one-mode line with exactly one unit of raw
selected-coordinate amplitude. Forgetting the weight recovers the original
unweighted line without changing its amplitude parameter.

[SourceSobolevGapOpening.lean](../NLS/ZakharovShabat/SourceSobolevGapOpening.lean)
pulls this line through the actual analytic Sobolev inverse. For every real
order s>=0 and finite 1<p<=2, the curve is analytic in the full native weighted
source norm and converges to its initial source at zero amplitude.

[SourceFiniteGapSobolevOpening.lean](../NLS/ZakharovShabat/SourceFiniteGapSobolevOpening.lean)
identifies its raw coefficients with the previously proved Hilbert gap-opening
curve. Every real spectral finite-gap source admits this lift in every such
Sobolev order. The amplitudes 1/(l+1) give concrete finite-gap approximants
converging in the chosen Sobolev norm. They open the selected collapsed gap
and preserve the zero/nonzero status of every other gap, so the finite set of
open gaps is the original set together with the selected index.

Taking s=1 supplies the H1 convergence ingredient in the closed-gap argument
of Lemma 20.2. This construction preserves other actions and gap status. The separate
construction below fixes every other numerical gap length. The final frequency
proof uses fixed finite gap support. The known Laurent-coefficient and diagonal-factor source
corrections, exact2014 comparison and G2 norm qualification remain separate.

## Exact numerical gap-length approximation in H1, printed p. 93

[SymmetricExactGapOpening.lean](../NLS/ZakharovShabat/SymmetricExactGapOpening.lean)
inverts the actual signed-gap map over each fixed finite output support.
Varying one signed output coordinate gives a continuous symmetric finite-gap
curve with selected gap length abs(t) and every other numerical gap length fixed.

[SourceExactGapOpening.lean](../NLS/ZakharovShabat/SourceExactGapOpening.lean)
transports this curve through every real finite-gap Hilbert source. A symmetric
isospectral representative supplies its starting point; finitely many fixed
Birkhoff rotations move that point back to the original source. These rotations
preserve every action and hence the actual full spectrum at each parameter.

[SourceFiniteGapCurveSobolev.lean](../NLS/ZakharovShabat/SourceFiniteGapCurveSobolev.lean)
proves a general continuity upgrade: any Hilbert-continuous source curve whose
open gaps lie in one fixed finite set has a continuous lift at every nonnegative
real Sobolev order. Finite raw Birkhoff blocks are inserted in the native weighted
target, then the original Sobolev inverse recovers exactly the source coefficients.

[SourceExactGapOpeningSobolev.lean](../NLS/ZakharovShabat/SourceExactGapOpeningSobolev.lean)
applies this upgrade to the exact gap-length curve. The explicit amplitudes
1/(l+1) yield finite-gap approximants converging in the chosen Sobolev norm,
with the selected gap open and all other numerical gap lengths unchanged.
Taking order one proves the literal H1 approximation in the proof of Lemma 20.2.
The common finite support is the original open-gap set together with the selected index.

This resolves the previously unverified numerical-gap equality by a separate
construction. The earlier amplitude-line proof still preserves other actions;
these two constructions need not coincide. Continuity of the new curve is proved;
analyticity in its parameter is not asserted. The known Laurent-sign and diagonal
auxiliary-factor corrections, exact2014 and G2 qualifications remain separate.
