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

Section 8's Lemma 8.1 is now audited in [Section 8](SECTION_8.md), with
its necessary normalization and quotient corrections. Next is Lemma 8.2. This audit
does not certify the remaining dissertation or the cited classical
background from the introductory overview as complete.
