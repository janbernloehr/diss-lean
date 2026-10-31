# Section 27: original Sobolev norms from the actions

## Ordered source comparison

The [ordered Section 27 comparison](SECTION_27_ASSERTIONS.md)
covers 18 groups on pp.115–116: 14 matched, three corrected and one contextual.
No partial or pending groups remain in this local ledger.

The comparison retains the physical trace, exact H1 coefficient 1/3,
literal all-order Lemma 27.2 constant and unrestricted m=1 endpoint.
The final derivative estimate keeps coefficient one on the highest
action term and the unweighted final mass factor.

Direct corrections retain the full mass remainder in the quarter-energy
step, make the zero-index split explicit and supply the final constant
budget. No new Lean proof or refutation is added in this comparison.

The unchanged Lean snapshot reuses the successful full check at commit 053f761701e1f096332b713a8c0d951b54d3e705: 8,581 build jobs, 7,690 public examples and an axiom audit of 44,704 NLS declarations, with 21 inherited warnings and zero new. All 55 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Section 28. The [broader completion qualifications](COMPLETENESS.md)
remain; these local ledger counts do not certify the whole dissertation.

Earlier entries retain their original implementation and validation scope.

## Positive quarter-energy estimate

The [quarter-energy estimate](../NLS/ZakharovShabat/SourceSection27QuarterEnergy.lean)
now retains the complete mass remainder from Lemma 26.3:

    pair derivative energy / 4 <= H_(2m+1) + C*(1+M^(2m))*M.

Here M is the total original action, equal to the scalar L2 energy.
One nonnegative C works for every real Hm source at each m>=1,
including zero mass. This directly corrects the intermediate
pure-power-only remainder on p.116. The existing final derivative
estimate retains coefficient one and the unweighted mass factor.

One positive theorem and two examples cover the m=2 estimate and
its uniform linear remainder on the closed mass ball M<=1.
No new refutation is added.

The full check passed: 8,581 build jobs, 7,690 public examples and an axiom audit of 44,704 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The ordered Section 27 comparison continues. The
[broader completion qualifications](COMPLETENESS.md) remain.

This audit covers formula (5.13), Lemmas 27.1–27.2, and the proof of
Theorem 23.2(ii) on printed pp. 115–116. The original indexed actions,
independently defined physical Hamiltonians, and exact physical Sobolev
norms are retained. Lemma 27.2 now has its literal printed coefficient
for every m>=1, including the unrestricted H1 endpoint.

For a real H^m source a, write

    S_k = sum_n <2*n*pi>^(2*k) |I_n|,   M = S_0,   S = S_1.

Here I_n is `sourceIndexedAction`, and the bracket is exactly 1+|2*n*pi|.
On real sources the original actions are nonnegative. The pair norms
include both components with this exact physical Fourier weight.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Formula (5.13) | `SourceSection26Data.section27_pair_top_jet_identity` | All real H^m sources, m>=1; half the sum of both component derivative energies, positive 4^m, original higher actions, and the physical remainder integral over [0,1]. |
| Higher-action trace | `SourceSection26Data.section27_hamiltonian_hasSum` | The scaled original series has sum H_(2m+1), with absolute convergence. |
| Lemma 27.1, kinetic estimate | `sourceSection27_energy_action_bound`, `sourceSection27_kinetic_summable` | H3-2*H1^2<=sum_n (2*n*pi)^2 I_n on every real H1 source, with absolute convergence and signed indices. |
| Lemma 27.1, H3 corollary | `sourceSection27_H3_action_mass_bound` | H3<=S+2*M^2 for the independently defined sharp odd Hamiltonian. |
| Lemma 27.1, physical H1 norm | `sourceSection27_H1_norm` | P^2/3<=S+M^2 with the literal pair norm and coefficient 1/3. |
| Lemma 27.2, all orders | `sourceSection27_hamiltonian_estimate_literal` | H_(2m+1)<=S_m+(64*pi)^(2m-2)*(1+S)^(4m-3)*S for every m>=1 and every real H^m input, with the original indexed actions. |
| Lemma 27.2, unrestricted m=1 | `sourceSection27_endpoint`, `sourceH1_energy_le_lemma272` | H3<=2*S+S^2, with no smallness, closed-gap, or supplied representation premise. |
| Stronger global H1 budget | `sourceH1_energy_le_quadratic_budget` | H3<=S-M+S^2 for every real H1 source. |
| Stronger closed-zero-gap budget | `sourceH1_energy_le_half_square_of_zero_action`, `sourceH1_zero_action_of_zero_gap` | H3<=S-M+S^2/2 when the central gap is collapsed, without a smallness restriction. |
| Sharp cubic input | `SourcePrimitivePowerAtlas.real_action_sq_le_cubic` | R_n>=(3/4)*I_n^2 at every index and every real source at every finite p>1, including collapsed gaps. |
| Actual finite-gap profile | `SourceFullAbelianUniformCauchyFamily.real_profile_eq_actual_correction_finiteGap` | The original open-gap cosine profile equals r*sin(theta)*(1+the explicit positive correction), including selected endpoints. |
| Last derivative estimate in Theorem 23.2(ii) | `exists_sourceSection27_derivative_bound` | m>=2, exact factor 1/4 on pair derivative energy, coefficient one on S_m, and one source-independent C multiplying (1+S)^(4m-3)*M. |
| Theorem 23.2(ii) | `exists_sourceSection27_sobolev_bound` | Every m>=1, one d before all sources, exact physical H^m pair norm, and the unweighted final factor M. |
| One original family | `SourceSection27Data.hamiltonian_estimate_literal`, `sourceSection27_original` | Exact all-order estimate on the retained original family and domains; existing weaker fields remain compatible. |

## Original actions and physical energy

[`SourceSection27Actions.lean`](../NLS/ZakharovShabat/SourceSection27Actions.lean)
identifies the original indexed actions with the real contour actions.
The kinetic series converges absolutely, so Lemma 27.1 uses its actual
sum. The physical correction from Proposition 21.3 is nonpositive,
and the quartic mass estimate gives the exact H1 norm coefficient 1/3.

`sourceSection27_H3_bridge` identifies the sharp Sobolev odd Hamiltonian
at m=1 with the independently defined H1 Hamiltonian. This prevents a
normalization change between Lemmas 27.1 and 27.2.
`sourceSection27_pair_jet_norm` proves that half the sum of both component
derivative energies equals the first component energy. It includes order
zero and recovers the literal pair factor in (5.13).

## The unrestricted endpoint

[`SourceH1ZeroModeActionBound.lean`](../NLS/ZakharovShabat/SourceH1ZeroModeActionBound.lean)
proves 2*M-I_0<=S from the exact bracket weights and absolute summability.
The actual energy identity and nonnegativity of the cubic moments reduce
a sufficient endpoint condition to R_0>=(3/4)*I_0^2 in
[`SourceH1ZeroModeMomentCriterion.lean`](../NLS/ZakharovShabat/SourceH1ZeroModeMomentCriterion.lean).

The scalar sine-profile estimate in
[`SineCorrectedCubicIntegral.lean`](../NLS/ComplexAnalysis/SineCorrectedCubicIntegral.lean)
and the positive exterior-kernel results in
[`SineExteriorKernelCorrection.lean`](../NLS/ComplexAnalysis/SineExteriorKernelCorrection.lean) and
[`SineIntegralKernelCorrection.lean`](../NLS/ComplexAnalysis/SineIntegralKernelCorrection.lean)
keep the exact constants. The original action and cubic moment are
2*r^2*A/pi and 2*r^4*B/pi. Their normalization in
[`SourcePrimitivePowerSharpCubic.lean`](../NLS/ZakharovShabat/SourcePrimitivePowerSharpCubic.lean)
therefore gives R_n>=(3/4)*I_n^2 from the positive profile representation.

That representation is now proved for actual finite-gap sources, as
explained below. [`SourceSharpCubicFiniteGapReduction.lean`](../NLS/ZakharovShabat/SourceSharpCubicFiniteGapReduction.lean)
proves continuity of the actual moments and supplies finite-gap density.
[`SourcePrimitivePowerGlobalCubic.lean`](../NLS/ZakharovShabat/SourcePrimitivePowerGlobalCubic.lean)
uses these results to extend the sharp cubic inequality to every real
source at every finite p>1. Closed gaps are treated separately without
dividing by their lengths.

[`SourceH1SharpEndpoint.lean`](../NLS/ZakharovShabat/SourceH1SharpEndpoint.lean)
constructs the moment atlas internally, applies the zero-mode estimate,
and proves H3<=S-M+S^2 and H3<=2*S+S^2. No supplied profile identity remains.
[`SourceSection27SharpEndpoint.lean`](../NLS/ZakharovShabat/SourceSection27SharpEndpoint.lean)
transfers this to the original indexed actions and combines it with the
previous m>=2 result to prove the literal all-order Lemma 27.2.

The earlier proof on S<=2 and the twice-remainder global bound remain
valid. The closed-zero-gap estimate H3<=S-M+S^2/2 is stronger on that class.
The scalar arithmetic obstruction concerns the source's proof alone,
not the now-proved conclusion; see [the resolved issue](../SOURCE_ERRATA.md).

## The actual finite-gap representation

[`SourceRealGapSeparation.lean`](../NLS/ZakharovShabat/SourceRealGapSeparation.lean)
and [`OrderedGapSeparation.lean`](../NLS/ComplexAnalysis/OrderedGapSeparation.lean)
use the neighboring bands to separate each fixed gap from every other
closed gap by a positive distance. The bound need not be uniform in the
index or the source.
[`SourceGapAngularDensity.lean`](../NLS/ZakharovShabat/SourceGapAngularDensity.lean)
defines d_m(theta)=gamma_m/(2*pi)*sin(theta)*f_m(theta) on [0,pi], and zero
outside. It is nonnegative and integrates to I_m/2.
[`SourceExteriorGapKernel.lean`](../NLS/ZakharovShabat/SourceExteriorGapKernel.lean)
uses these actual densities and endpoints to prove the joint integrable
majorant. [`SourceExteriorGapCorrection.lean`](../NLS/ZakharovShabat/SourceExteriorGapCorrection.lean)
defines the resulting nonnegative continuous correction V_n.

[`SourceFilledGapQuotient.lean`](../NLS/ZakharovShabat/SourceFilledGapQuotient.lean)
constructs Q_n=-i*F_n/root_n, filled analytically across the selected gap.
Its real part recovers the exact cosine profile, including endpoints.
The standard root has leading term -z, proved in
[`StandardRootInfinity.lean`](../NLS/ZakharovShabat/StandardRootInfinity.lean).
The actual finite-gap primitive has leading term -i*z, so
[`SourceFilledGapQuotientInfinity.lean`](../NLS/ZakharovShabat/SourceFilledGapQuotientInfinity.lean)
proves Q_n tends to one at complex infinity.

[`CauchyFiniteHoles.lean`](../NLS/ComplexAnalysis/CauchyFiniteHoles.lean)
and [`CauchyOuterLimit.lean`](../NLS/ComplexAnalysis/CauchyOuterLimit.lean)
keep the exact 2*pi*i value and outer-limit constants.
[`SourceFiniteGapQuotientCauchy.lean`](../NLS/ZakharovShabat/SourceFiniteGapQuotientCauchy.lean)
applies them to Q_n with holes at the finitely many exterior open gaps.
Thus (2*pi*i)*Q_n equals 2*pi*i minus the sum of the exterior contours.

[`SourceWeightedPrimitiveBoundary.lean`](../NLS/ZakharovShabat/SourceWeightedPrimitiveBoundary.lean)
retains analytic weights when shrinking primitive contours to their actual
arcosh profiles; the primitive index constants integrate to zero.
[`SourceExteriorQuotientContour.lean`](../NLS/ZakharovShabat/SourceExteriorQuotientContour.lean)
applies this to the quotient Cauchy weight.
[`SourceExteriorRootDenominator.lean`](../NLS/ZakharovShabat/SourceExteriorRootDenominator.lean)
proves that root_n(t)*(t-x) is minus the positive square-root magnitude
times |t-x|, on either exterior side and at closed-gap endpoints.
[`SourceExteriorKernelFiniteSum.lean`](../NLS/ZakharovShabat/SourceExteriorKernelFiniteSum.lean)
justifies Fubini, finite support, and the real-coordinate change of variables.
[`SourceExteriorContourKernel.lean`](../NLS/ZakharovShabat/SourceExteriorContourKernel.lean)
therefore identifies each contour as exactly -2*pi*i times its positive
angular kernel integral.

[`SourceFiniteGapProfileIdentity.lean`](../NLS/ZakharovShabat/SourceFiniteGapProfileIdentity.lean)
combines these formulas to prove Q_n=1+V_n and the actual finite-gap profile
identity. No external representation theorem is imported as an axiom.
Equation (2.15) of
[Korotyaev, *Hamiltonian and small action variables for periodic dNLS*](https://arxiv.org/pdf/0911.5235)
motivated the identity; all signs and constants here follow from the
repository's original root, contour and action definitions.
An infinite-gap profile identity is not asserted and is unnecessary for
the global cubic inequality and Lemma 27.2.

## Coefficient one in the derivative estimate

[`SourceSection27DerivativeBound.lean`](../NLS/ZakharovShabat/SourceSection27DerivativeBound.lean)
retains coefficient one on S_m. At an enlarged frequency threshold,
the central remainder is bounded by S_m/2+C_h*(1+S)^(4m-3)*M.
The physical remainder estimate with epsilon=1/4 then gives

    (||d^m a_1||^2 + ||d^m a_2||^2)/4 <= S_m + C*(1+S)^(4m-3)*M.

Both constants are chosen before all sources. The proof includes zero
mass and preserves the final unweighted factor M. Theorem 23.2(ii)
keeps its previously proved constants; its H1 branch already followed
directly from Lemma 27.1.

## Retained family and validation

[`SourceSection27Original.lean`](../NLS/ZakharovShabat/SourceSection27Original.lean)
retains the Section 26 family and original domains. Its identity uses the
actual physical polynomial remainder over the unit interval, and its
scaled higher-action series has the independently defined Hamiltonian as
its `HasSum` value. `SourceSection26Data.section27` augments an existing
family, and `sourceSection27_original` constructs one without an extra
premise. The exact all-order extension is now
`SourceSection27Data.hamiltonian_estimate_literal`.

The new public checks cover a negative-index cubic bound, the stronger H1
budget, the literal endpoint, all orders with exact constants, an actual
finite-gap quotient, and a selected endpoint. Earlier checks retain the
physical norm, contour, trace, derivative and family coverage. Full project
validation is recorded in [implementation status](../STATUS.md).
The separate [Section 14 edition comparison](SECTION_14.md) and
[Appendix G norm qualification](APPENDIX_G.md) remain; completion of this
lemma is not a completeness certificate for the dissertation.
