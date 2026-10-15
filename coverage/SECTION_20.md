# Section 20: original moments and renormalized frequencies

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
| Opening physical energy bracket, finite-gap case | `Q.finiteGap_energy_bracket`, `Q.finiteGap_energy_cotangent` | Constructed H¹ angle tangent and one actual physical energy cotangent give the original Poisson identity at every real finite-gap source, for every open selected gap; arbitrary complex H¹ sources remain open |
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
r>1; at p>2 it includes r=p/2. No ℓ∞ endpoint is claimed.

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

The equality of this bracket with 2πn remains to be proved. The next
proposed step identifies physical H₂ with the quadratic contour of the
same Section 19 primitive, then evaluates its angle bracket. The current
analyticity theorem does not replace that normalization or establish
H¹ regularity of the general angle vector.

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

The physical energy identity packaged here is for real finite-gap sources; the
analytic continuation and original action-frequency identification hold on
the stated complex neighborhoods. The opening p. 92 Poisson identity now
has the physical H¹ interpretation at real finite-gap sources. Extending
the H¹ angle tangent and bracket to arbitrary complex H¹ sources remains
open: the fixed-tail weighted reconstruction used above does not give
uniform H¹ control as the finite-gap supports grow. Establish that
regularity and continuation before proceeding to the original Section 21
assertions. Section 14's external Hilbert-map and full
fractional-smoothness qualifications also remain. The dissertation is
incomplete.
