# Section 7: the action-angle overview

Theorem 7.1 is stated on printed page 47. Its source is the unit-period
Fourier coefficient space, represented by `CoeffPair p` with the original
component-sum norm. The spectral realization uses `periodOnePotential`.
This differs from Section 6's arbitrary period-two input theorem.

## Theorem 7.1(i): one common action neighborhood

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Every scalar action on one domain | `SourceBirkhoffMapComplexData.actions_analytic` | Exact coordinate evaluation of the actual analytic rectangular sequence map and its action-radius identity. |
| Original common neighborhood | `exists_sourceAction_common_analytic_neighborhood` | One open set containing the entire real source locus; every action is complex and real analytic there, for every finite p>1. |
| Real source values | `SourceTheorem7_1Data.actions_real` | Original actions are real and nonnegative; zero precisely at their collapsed gaps. |

The older `exists_global_sourceComplexAction_analyticOnNhd` retained an
intersection with each indexed action domain. It alone does not supply the
common neighborhood required here. The new result removes that condition.
Scalar evaluation also avoids imposing a Banach half-exponent action space
when 1<p<2. The actions are the existing original spectral actions, whose
real restriction and Arnold integral were already identified.

## Theorem 7.1(ii): the two angle conventions

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Oriented real phase | `sourceAngularThetaRealPhase` | Signed eta coordinate divided by the canonical nonzero gap, multiplied by the beta phase. |
| Actual class modulo 2π | `sourceAngularThetaRealAngle` | Values in `Real.Angle = ℝ/(2πℤ)`, asserted on real open gaps. |
| Exact chart identification | `SourceAngularEtaAnalyticChartData.realThetaPhase_eq_exp_representative`, `.realThetaAngle_eq_representative` | Canonical half-gap charts give exp(iθ) with its sign and the same real class modulo 2π. |
| Relation to the complex phase | `SourceAngularThetaCommonDomainData.realThetaPhase_norm_and_sq`, `.exp_realThetaAngle` | Unit norm on real open gaps; phase squared equals the analytic exp(2iθ) phase. |
| Literal spectral formula | `SourceAngularEtaAnalyticChartData.exp_I_admissible_angle_eq_realPhase` | Left periodic anchor, actual terminal normalization, admissible C1 path, and actual/model integrability. Includes periodic Dirichlet terminals. |
| Common complex extension | `SourceTheorem7_1Data.angle_phase_analytic`, `.local_angles` | All open-gap phase domains lie in the same W; local complex and real analytic representatives, reality on real input, and exact original angle differentials. |

The complex extension is modulo π: local representatives have the same
exp(2iθ) phase, with the existing chart-overlap theorem giving integer-π
differences. The real class retains the finer modulo-2π information.
At a real base point, the chosen canonical half-gap chart agrees with that
class. No globally single-valued real representative or angle at a closed
gap is asserted. The path comparison retains its explicit integrability
conditions and does not claim integrability for arbitrary paths.

Public endpoint checks distinguish the phases +1 at the left endpoint
and −1 at the right endpoint when the beta and remainder corrections vanish.
Squaring alone would not distinguish these cases.

## Theorem 7.1(iii): actual canonical brackets at all exponents

| Relation | Entry point | Domain |
| --- | --- | --- |
| Action/action = 0 | `SourceTheorem7_1Data.canonical` | Every real source, including collapsed action gaps. |
| Angle/angle = 0 | `SourceTheorem7_1Data.canonical` | Both selected angle gaps open. |
| Angle/action = δ_nm | `SourceTheorem7_1Data.canonical` | Only the angle's gap must be open; the action gap is unrestricted. |
| Literal Fourier realization | `SourceAngularThetaCommonDomainData.thetaTheta_fourier_bracket_eq_zero`, `.thetaAction_fourier_bracket_eq_kronecker`, `sourceAction_fourier_bracket_eq_zero` | Actual derivatives, frequency reversal, physical sign −i, and proved absolute convergence. |

The canonical fields use `RegularSourceCotangent`: each coefficient witness
is identified with the actual action derivative or angle differential and
is proved square summable. This handles the full finite range 1<p<∞,
including below two. The older generic `sourceBracket` is only defined for
p≥2; restricting to it would miss part of this theorem's scope.

## Combined theorem and remaining work

`sourceTheorem7_1` constructs `SourceTheorem7_1Data` with one common open
neighborhood containing the entire real locus and one constructed angular
family. It combines all three assertions without hypotheses supplying the
canonical values, finite-source computations, or a common action domain.
Public checks include p=3/2, real/complex phase compatibility, local
derivative agreement, precise open-gap conditions, and the literal Fourier
bracket formula.

The discriminant and endpoint assertions, including Lemmas 8.1 and 8.2,
are audited in [Section 8](SECTION_8.md), with the necessary normalization
and quotient corrections. The unnumbered overview assertions below require
two further corrections. This audit does not certify the remaining
dissertation or the cited classical background as complete.

## The actual Hilbert isospectral tori on printed p. 45

The unnumbered overview describes each real Hilbert isospectral set as a
compact connected torus, with one circle for each noncollapsed periodic
gap. The earlier Lemma 17.5 implementation identified the entire image
under the original Birkhoff map and established compactness. The following
results now supply connectedness and the explicit product topology.

[RealActionTorusConnected.lean](../NLS/SequenceSpaces/RealActionTorusConnected.lean)
joins each finite coordinate-rotation sequence to its base by scaling all
of its angles. The finite rotation orbit is connected; its norm closure is
the full action torus at every finite Banach exponent. This includes tori
with infinitely many nonzero actions.

[SourceHilbertIsospectralConnected.lean](../NLS/ZakharovShabat/SourceHilbertIsospectralConnected.lean)
transfers connectedness through the actual global Hilbert Birkhoff
homeomorphism. `sourceHilbertIsospectralSet_compact_connected` constructs
the family internally and retains the original periodic spectrum and all
algebraic multiplicities. It imposes no finite-gap assumption.

[RealActionTorusProduct.lean](../NLS/SequenceSpaces/RealActionTorusProduct.lean)
defines the relative phase at each nonzero action by dividing the complex
coordinate by its base coordinate. This is a continuous bijection to the
product of unit circles. Surjectivity constructs actual ℓᵖ sequences using
a summable coordinate majorant; zero actions force both omitted coordinates
to vanish. Compactness turns the bijection into a homeomorphism from the
sequence norm topology to the product topology, for every finite Banach
exponent. No corresponding assertion at p=∞ is made.

[SourceHilbertIsospectralTorus.lean](../NLS/ZakharovShabat/SourceHilbertIsospectralTorus.lean)
restricts the original Hilbert homeomorphism to the actual isospectral set
and identifies its nonzero-action indices exactly with the original open
periodic gaps. `sourceHilbertIsospectralSet_homeomorphic_circles` constructs
a homeomorphism to one unit circle per such gap. For an actual finite-gap
source, `sourceHilbertIsospectralSet_homeomorphic_finiteTorus` gives a product
indexed by Fin(Nat.card(sourceHilbertOpenGapIndex φ)). Thus the circle-factor
count is the exact number of open gaps. This is an explicit torus model;
a separate covering-dimension or manifold-dimension invariant is not asserted.

Three public examples show that all gaps closed gives a singleton isospectral
set, exactly one open gap gives a circle, and a positive coordinate rotation
at p=3 induces exp(i t), checking the phase orientation. These coordinate
phases are not identified here with the Dirichlet-angle formula.

The overview's Dirichlet-eigenvalue/sign parametrization and the assertion
that squared gap lengths determine the spectrum remain separate source
comparisons. Existing action-to-spectrum injectivity is a different assertion.
The exact 2014 construction comparison and G.2 norm qualification remain open.

## The actual signed Dirichlet data separate isospectral sources

The page-45 overview describes isospectral sets using Dirichlet eigenvalues
and signs. The following results prove uniqueness for this literal data,
retaining the original periodic spectrum and all algebraic multiplicities.
They apply to every real source at every finite p>1, with no finite-gap or
Hilbert-regularity assumption.

[SourceDirichletSignData.lean](../NLS/ZakharovShabat/SourceDirichletSignData.lean)
proves that the full terminal anti-discriminant is real at every actual
Dirichlet root. The actual gap discriminant inequality and square identity
supply this fact, including at endpoints. Its sign is an element of
SignType, representing -1, 0 or 1. On an actual isospectral set, equal
Dirichlet roots and signs recover the full anti-discriminant value.

[SourceAngularPrimitiveSpectralData.lean](../NLS/ZakharovShabat/SourceAngularPrimitiveSpectralData.lean)
uses uniqueness of the actual normalized psi roots to identify entire
numerators across independent compatible families. The actual radicands,
prescribed root sheets and exterior primitives agree. This transports the
full sets of normalized regular Dirichlet primitive values when the
selected root and full terminal sheet value agree, including on a cut.

[SourceAngularBetaSpectralData.lean](../NLS/ZakharovShabat/SourceAngularBetaSpectralData.lean)
identifies the defining beta value sets, each chosen beta summand, and the
whole infinite correction. It explicitly transports the endpoint zero
convention. [SourceAngularEtaRemainderSpectralData.lean](../NLS/ZakharovShabat/SourceAngularEtaRemainderSpectralData.lean)
transports the actual omitted root products and normalized remainder
primitives. Independent annular Cauchy constructions therefore give the
same eta remainder at equal signed Dirichlet terminals, even when their
circles and anchors differ.

[SourceSignedDirichletUniqueness.lean](../NLS/ZakharovShabat/SourceSignedDirichletUniqueness.lean)
identifies the original rectangular Birkhoff coordinates. On open gaps,
the actual action factorization fixes the principal normalized action root;
on closed gaps, the proved zero coordinates avoid any division by the gap.
The constructed global Birkhoff injectivity theorem then proves
`source_eq_of_isospectral_dirichlet_roots_signs`.
`sourceSignedDirichletData_injOn_isospectralSet` states injectivity of the
literal map n ↦ (mu_n, sign(delta(mu_n))) on each actual isospectral set.

Three public examples check that sign zero detects the full complex terminal
value at p=3, opposite nonzero sheets have different signs, and these data
separate sources at p=3/2. The proofs use actual spectral and angular objects;
no norming-coordinate injectivity theorem is supplied as a premise.

This establishes uniqueness. Existence for arbitrary admissible signed
gap-circle data and continuity with the glued circle topology remain to be
proved. The abstract circle-product model above does not by itself identify
that particular parametrization. Squared-gap-length spectral uniqueness,
the exact cited 2014 construction comparison, and the G.2 norm qualification
also remain separate requirements.

## Prescribed actual Dirichlet terminals and the Hilbert sheet product

The page-45 Dirichlet/sign parametrization now has an existence theorem in
full terminal coordinates. For every real Hilbert source, every collection
of admissible pairs (mu_n, delta(mu_n)) is realized by exactly one source in
the original periodic isospectral set. Infinitely many open gaps are allowed.

[RealSheetRecurrence.lean](../NLS/FunctionalAnalysis/RealSheetRecurrence.lean)
proves that a complete bounded real sheet trajectory has a turning point
after any given time. A fixed velocity sign would make its position
monotone and convergent; the derivative limits contradict nonzero
acceleration at a sheet zero. [RealSheetTraversal.lean](../NLS/FunctionalAnalysis/RealSheetTraversal.lean)
locates the next upper or lower endpoint, uses nonzero acceleration to
obtain both velocity signs, and proves that every point on both branches
is attained. No recurrence or prescribed reachability premise is assumed.

[SourceDirichletRealSpectralSheet.lean](../NLS/ZakharovShabat/SourceDirichletRealSpectralSheet.lean)
proves reality of both coordinates of every point on the actual algebraic
sheet, including points not yet realized by a source.
[SourceDirichletSpectralTraversal.lean](../NLS/ZakharovShabat/SourceDirichletSpectralTraversal.lean)
applies the real ODE result to the original globally constructed indexed
flow, with velocity -delta/2 and the actual fixed discriminant. Its
terminal-pair range is precisely the entire original compact sheet.
Collapsed sheets are attained at time zero; open gaps include both signs
and both endpoints, with no index cutoff.

[SourceDirichletTerminalData.lean](../NLS/ZakharovShabat/SourceDirichletTerminalData.lean)
proves continuity of the actual full terminal data, invariance of whole
sheets under isospectrality, and injectivity on the isospectral set.
[SourceDirichletFinitePrescription.lean](../NLS/ZakharovShabat/SourceDirichletFinitePrescription.lean)
realizes every finite prescription using indexed flows while retaining all
unselected terminal pairs exactly. The original spectrum and all algebraic
multiplicities are preserved at every step.

[SourceDirichletSheetParametrization.lean](../NLS/ZakharovShabat/SourceDirichletSheetParametrization.lean)
uses compactness of the actual Hilbert isospectral set and the closed
coordinate constraints to realize arbitrary infinite prescriptions.
`sourceHilbertDirichletSheetHomeomorph` is the original terminal map as a
homeomorphism onto the product of the original algebraic sheets. Its target
uses the inherited topology of complex base/full-terminal pairs, so the
two branches meet at their common endpoints. Three public examples check
one sheet flip with all other terminals fixed, simultaneous left-endpoint
prescriptions for all indices, and uniqueness of any admissible prescription.

The continuity and injectivity prerequisites hold at every finite p>1;
these flow-based existence and homeomorphism theorems concern p=2. A target
presented literally as eigenvalues plus SignType values still needs an
explicit admissibility definition and comparison of its glued topology.
The discrete product topology on SignType is not claimed to work at an
endpoint. Squared-gap spectral uniqueness, the exact cited 2014 construction
comparison and the G.2 norm qualification remain open.

## The literal eigenvalue/sign parametrization and its glued topology

The remaining literal-coordinate and topology requirements from the two
preceding sections are now proved. The actual Hilbert eigenvalue/sign map
is a homeomorphism onto the product of admissible signed gaps. Every real
gap point may be prescribed, with sign -1 or 1 in the interior and sign zero
exactly at an endpoint. This permits infinitely many independent choices.

[RealSignedSheet.lean](../NLS/FunctionalAnalysis/RealSignedSheet.lean)
defines admissible base/sign data and reconstructs the full real terminal
as sign times the nonnegative square root of the height. Zero sign occurs
precisely at zero height. The induced topology is proved homeomorphic to
the original real sheet and, for a continuous nonnegative height, is a
quotient of two copies of the compact base interval. The two branches over
a common base are identified exactly where the height is zero. Thus the
sign coordinate does not carry the discrete product topology at endpoints.

[SourceDirichletRealSheetCoordinates.lean](../NLS/ZakharovShabat/SourceDirichletRealSheetCoordinates.lean)
uses the original discriminant to define the actual height Delta(mu)^2-4.
It proves continuity, nonnegativity throughout each real gap, and vanishing
exactly at the two periodic endpoints. Real-coordinate inclusion gives a
homeomorphism from the original complex algebraic sheet to its real sheet,
then to literal eigenvalue/SignType coordinates. The actual signed-gap
topology is the quotient of its two interval branches. Evaluation lemmas
identify the base and sign without a change of convention. These individual
sheet results hold for every finite p>1, including collapsed gaps.

[SourceSignedDirichletParametrization.lean](../NLS/ZakharovShabat/SourceSignedDirichletParametrization.lean)
composes the proved actual Hilbert terminal homeomorphism with those
coordinate homeomorphisms. `sourceHilbertSignedDirichletHomeomorph` is
exactly the original Dirichlet eigenvalue/sign map. The theorem
`existsUnique_isospectral_source_with_signed_dirichletData` realizes every
literal prescription satisfying the gap bounds and endpoint sign rule by
exactly one source with the original spectrum and all algebraic multiplicities.
No finite-gap or supplied inverse-map hypothesis is needed.

The selected 2013 preprint comparison agrees with its Proposition 9.3 and
Theorem 10.4: sigma is sign(delta(mu)), and the signed gaps use the joined
interval-branch topology. This does not identify that preprint with the
exact cited 2014 edition. Public examples check endpoint gluing versus
interior separation, reversal of every terminal sign with all Dirichlet
roots fixed, and the singleton signed gap at a collapsed p=3 coordinate.

Global prescribed-data existence and the product homeomorphism here concern
p=2. Squared-gap-length determination of the spectrum, a separate dimension
invariant, the exact 2014 comparison and the G.2 norm qualification remain
separate requirements; no overall completeness claim is made.

## The collapsed-gap locus on printed p. 46 has real codimension two

The paragraph following (2.3), visually checked in the original PDF, calls
Z_n={u : gamma_n(u)^2=0} a real analytic submanifold of codimension one.
The value one is incompatible with the actual real physical Hilbert geometry.

[PhysicalClosedGapGeometry.lean](../NLS/ZakharovShabat/PhysicalClosedGapGeometry.lean)
identifies the literal squared-gap equation with equality of the actual
periodic endpoints and with simultaneous vanishing of the two real
Birkhoff coordinates x_n and y_n. The global physical Birkhoff homeomorphism
and its inverse are real analytic. This same map sends Z_n exactly to the
kernel of the bounded coordinate evaluation (x,y) ↦ (x_n,y_n).
A bounded single-mode insertion is a right inverse of that evaluation;
its kernel quotient therefore has real dimension two.

[PhysicalClosedGapTangents.lean](../NLS/ZakharovShabat/PhysicalClosedGapTangents.lean)
identifies the kernel of the actual coordinate differential with the full
local curve tangent space at each point of Z_n. Every differentiable curve
locally in Z_n has velocity in that kernel. Conversely every kernel
direction is realized by a globally real analytic curve lying entirely in
Z_n, obtained by mapping a straight Birkhoff-coordinate line back through
the actual inverse. The original physical velocity is retained exactly.

The quotient by this tangent space has dimension two over R. The zero
potential belongs to every Z_n, and already refutes the printed universal
codimension-one value. Thus the valid real codimension is two. This
result concerns the real Hilbert statement on p. 46; it makes no claim
about the codimension of a complex spectral zero variety. The proof uses
an explicit global analytic normal form and an exact tangent-curve
characterization, rather than a generic manifold-library predicate.
See [the source discrepancy](../SOURCE_ERRATA.md).

## The psi product in the printed p. 46 overview needs a mode-dependent denominator

The unnumbered psi display on p. 46 has the fixed denominator pi_n in
every factor of the product over m≠n. The original PDF was visually
checked. The later normalized construction uses pi_m in those factors,
while retaining the outer factor -2/pi_n.

[SourceSection7PsiNormalization.lean](../NLS/ZakharovShabat/SourceSection7PsiNormalization.lean)
defines the literal printed cutoffs. For the actual free root sequence,
n=0 and lambda=0, their norms are at least 2*4^N and tend to infinity.
Consequently the printed product has no finite complex limit, and in
particular cannot represent the normalized free psi-function.

At the same source and spectral point, the established corrected product
with denominator pi_m equals -2 at every cutoff, including N=0. The
counterexample concerns the unnumbered overview's denominator index;
the later normalized construction remains valid. See
[the source discrepancy](../SOURCE_ERRATA.md).
