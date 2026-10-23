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
