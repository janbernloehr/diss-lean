# Section 11: actions

This audit begins with printed p. 61 of the dissertation. The contour
construction, equation (2.16), and independence of general admissible
counterclockwise piecewise C¹ circuits are proved on the unchanged common
source domain from Section 10. The full Lemma 11.1 is now proved there:
analyticity, the exact complex Fréchet gradient in equation (2.17), zero
action at complex collapsed gaps, and real nonnegativity with the exact
zero-gap criterion. The analytic zero sets Z_n and the full statement of
Theorem 11.2 are also proved. Equation (2.18), the literal deleted product
and its recentered action formula are now proved on the original domain.
The fixed-domain disk index is corrected as documented in
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md). Equation (2.19), the complex
weighted gap integral, the collapsed limit and analytic extension are
also proved on the original domain. The remaining p. 62 estimates for
the literal gap supremum and normalized actions now hold locally uniformly
on that full domain. The continuation through Theorem 12.1 is recorded
in the [Section 12 audit](SECTION_12.md).

## One neighborhood for all original contours

For every finite p>1, `sourceSection11Contours` constructs an open connected
W containing the entire real-type source locus and retains the full
`SourceLemma10_11Data` on that W. The upgrade
`SourceLemma10_11Data.actionContours` does not shrink a given W.

For any complex φ∈W, take any open source neighborhood V⊆W of φ and any
original `SourceIsolatingNeighborhoods hp hp1 V D c`. Then
`SourceSection11ContourData.contours` supplies one open connected U with
φ∈U⊆V and one `SourceActionContourFamily hp hp1 U D`. The family is chosen
before the nearby source ψ∈U and signed index n. Its original disks D_n
are unchanged. `.neighborhoods` supplies such a family without requiring
the caller to provide isolation data.

The family records real centers a_n and three radii
0<r_n<R_n<T_n, with D_n=ball(a_n,T_n). For every ψ∈U, the entire actual
complex periodic segment G_n(ψ) lies in ball(a_n,r_n). Define
Γ_n to be the positive radius-R_n circle and
U'_n=ball(a_n,T_n) minus closedBall(a_n,r_n).

| Source assertion | Public API | Scope |
| --- | --- | --- |
| Fixed open neighborhood of the circle | `.collar_open`, `.sphere_subset_collar` | The whole annulus U'_n, independent of ψ. |
| Circle strictly inside its original disk | `.closedBall_subset_original` | The filled radius-R_n disk lies in D_n. |
| Collar avoids the moving gap | `.collar_subset_cutDisk` | U'_n⊆D_n\G_n(ψ) for all ψ∈U. |
| Collar avoids every other gap | `.collar_subset_rootDomain` | Uses the original common isolating family. |
| Counterclockwise enclosure | `.windingIntegral_eq_one` | Winding integral one about every point of G_n(ψ), including collapsed gaps. |
| Uniform signed tail | `.tail` | One cutoff K; for |n|>K, a_n=nπ, r_n=π/8, R_n=3π/16, T_n=π/4. |
| Actual action integrand analytic | `.analytic_integrand_on_collar` | λΔ′/canonicalRoot jointly analytic on all U'_n×U. |
| Fixed-circle action analytic | `.analytic_actionCircle` | The existing `sourceActionCircle`, with its literal 1/π normalization, is analytic on all U. |

## Complex-source stability

The ordered endpoints are not assumed continuous near an arbitrary complex
source. Instead, `SourceEquation2_15Data.eventually_gap_subset_ball` uses
openness of the full joint moving-gap complement to keep a compact sphere
away from all gaps on one nearby source neighborhood. The analytic
midpoint stays inside that sphere and belongs to the selected segment.
The segment is connected, so it cannot leave the ball without crossing
the sphere. This includes a collapsed segment without choosing endpoint
labels or a square-root branch.

`local_originalDisk_gap_radius` applies this argument to a smaller circle
inside a given original disk. `original_contourFamily` intersects these
neighborhoods for finitely many central indices and combines them with
the locally uniform free tail. A source ball inside that finite
intersection provides the one connected neighborhood U for all indices.

## Equation (2.16): the literal contour-independent action

`sourceIndexedAction hp hp1 n ψ` chooses the actual normalized circle
integral from any `SourceCriticalRootPeriodCircle`. The proof
`SourceCriticalRootPeriodCircle.action_eq` compares every pair of these
circles using the separating real projections of the original disk
families. Neither disk must contain the other. The arbitrary default
outside sources admitting these circles is never used on W: the preceding
simultaneous contour construction supplies a circle at every ψ∈W and n.

`SourceActionContourFamily.indexedAction_eq_circle` identifies the selected
inner circles, strictly inside their original disks, with this indexed
function. `sourceActionContour` is defined as 1/π times the sum of actual
weighted path integrals; it is not defined using the indexed action.
`sourceActionContour_circle` proves agreement with the existing circle
integral convention.

For any original family D, any nearby complex source ψ, and any finite
piecewise C¹ loop Γ inside D_n\G_n(ψ),
`SourceIsolatingNeighborhoods.actionContour_eq_mul_winding` proves

`sourceActionContour ψ Γ = sourceIndexedAction n ψ * windingIntegral Γ τ_n`.

There is no prescribed homotopy, primitive, source-reality or open-gap
hypothesis. The formula covers repeated traversals and reversed orientation
through the winding integral. Setting that winding integral to one gives
`.indexedAction_eq_circuit`. Comparing both sides through the indexed
action proves `sourceActionContour_eq_of_original_circuits`, including
circuits chosen in different original isolating families.

The general analytic input is
`PiecewiseC1Loop.integral_eq_circleIntegral_mul_winding_of_starConvex_cut`.
For a closed cut K star-convex about c∈K, it subtracts
`P/(z-c)`, where P is the inner circle integral divided by 2πi. The
remainder has zero circle period and therefore a primitive on the whole
original disk minus K. Primitive differences telescope across all contour
pieces. The remaining pole integral is exactly the conventional winding
integral. A straight segment, including a singleton, satisfies the cut
hypotheses.

## Analyticity and agreement with the existing actions

`SourceSection11ContourData.analytic_indexedAction` proves analyticity on
all of the unchanged W by local agreement with the simultaneous fixed
circles. `sourceIndexedAction_eq_sourceRealAction` identifies the indexed
function with the existing real action at every real-type source.
`sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero` then proves real
values, nonnegativity and the exact real zero-gap criterion.

The earlier `sourceComplexAction` is defined on a union of real-base
charts. That union is not assumed to contain W. The new indexed action is
an explicit analytic continuation of the same real action: the two
complex functions agree on a complex neighborhood of every real point of
W, by `.indexedAction_eq_complexAction_near_real`, and on every connected
overlap containing a real point, by
`.indexedAction_eq_complexAction_on_overlap`. Agreement on unrelated
components of their domain intersection is not asserted.

`SourceSection11ContourData.defineActions` keeps W and all preceding
results. `sourceEquation2_16` provides the full public definition package
for every finite p>1, with the literal weighted quotient circuit formula,
analyticity, real agreement and complex germ agreement.

## Lemma 11.1 and equation (2.17)

`SourceEquation2_16Data.actionGradients` upgrades the existing package on
the same W. `SourceLemma11_1Data.previous` retains the literal action
formula, contour independence, analyticity and agreement with the existing
actions. `sourceLemma11_1` constructs the full package for every finite
p>1, on the unchanged open connected neighborhood of the real-type locus.

For any original isolating family over an open source neighborhood V,
any ψ∈V∩W, any signed n, any finite piecewise C¹ loop Γ inside D_n\G_n(ψ)
with winding integral one about the actual midpoint, and any complex
source direction v, `.gradient` proves the literal identity

`(fderiv ℂ (sourceIndexedAction n) ψ) v = -(1/π) * Γ.integral (Δ_v/Q)`.

Here Δ_v is the actual source Fréchet derivative of the discriminant
applied to v, and Q is the actual canonical root. Both derivatives and
integrals refer to the existing definitions. There is no reality,
noncollapsed-gap, nesting, or supplied-homotopy hypothesis. The only local
restriction is the original open isolating source neighborhood V; W is
not replaced or shrunk.

The proof uses the following common-domain results:

| Step | Public API | Scope |
| --- | --- | --- |
| Differentiate Q²=Δ²−4 | `SourceEquation2_15Data.root_joint_fderiv` | Full joint Fréchet derivative at every point of the retained moving-gap complement. |
| Source and spectral root derivatives | `.root_source_fderiv`, `.root_spectral_deriv` | Both restrictions of that same joint derivative, at complex sources. |
| Interchange the relevant derivatives | `.criticalRatio_source_fderiv_eq_spectral` | ∂_v(Δ′/Q)=∂_z(Δ_v/Q) pointwise off all gaps. |
| Differentiate the action circle | `.fderiv_actionCircle_eq_gradient_integral` | Every positive circle avoiding the gaps at a source in W. |
| Identify the indexed derivative | `SourceEquation2_16Data.original_circle_gradient` | Local equality to the fixed original-circle action identifies the actual indexed derivative. |
| Allow arbitrary circuits | `.circuit_gradient` | The variation quotient's outer-circle period computes every winding-one contour in the original cut disk. |
| Complex collapsed gaps | `.indexedAction_zero_of_gap_zero` | Every collapsed canonical gap in W has zero indexed action. |

The outer-circle comparison is
`PiecewiseC1Loop.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut`.
It combines the previous cut-disk primitive argument with Cauchy-Goursat
on the annulus between an enclosing inner circle and the original outer
circle. This preserves the entire original disk in the general-circuit
gradient proof.

For a collapsed complex gap, the continued quotient from Lemma 10.11 is
analytic throughout the selected original disk. A smaller filled circle
lies strictly inside that disk; its weighted continued integrand has zero
integral and agrees with the actual action integrand on the circle. This
proves `.collapsed` without replacing the totalized quotient at its
singular point or imposing source reality.

`.real_properties` states real values, nonnegativity, and the equivalence
between zero action and zero **canonical gap** on the whole real locus.
`.action_pos_of_real_gap_ne_zero` gives strict positivity on every real
open gap. These follow through the proved agreement with the existing
real action and its real-gap integral results.

## The analytic zero sets Z_n

`sourceActionGapZeroLocus hp hp1 W₀ n` is defined literally by ψ∈W₀ and
γ_n(ψ)²=0. Here W₀ is the unchanged domain of Lemma 11.1. The theorem
`SourceLemma11_1Data.squared_gap_analytic` retrieves the analytic squared
canonical gap from the retained Lemma 10.2 data. Together with
`sourceActionGapZeroLocus_eq_preimage`, it provides one global analytic
defining equation for Z_n. This is the analytic zero-locus assertion;
no smoothness or nonsingularity of this zero set is claimed.

`.gapZeroLocus_isClosed` proves closedness relative to W₀, and
`.action_zero_on_gapZeroLocus` proves zero indexed action there, including
at non-real sources and the central gap. The equivalence between a zero
squared gap and a zero canonical gap uses the actual complex field.

## Theorem 11.2 on one common smaller domain

`SourceLemma11_1Data.normalizedActions` constructs an open W⊆W₀ containing
the entire real-type source locus. The original W₀ and its full preceding
package remain in `SourceTheorem11_2Data.previous`. The theorem
`sourceTheorem11_2` supplies both domains for every finite p>1.

Write F_n for the existing `sourceNormalizedActionComplexExtension` and
ξ_n for `sourceNormalizedActionRoot`. The following assertions all hold
on the same W, simultaneously for every signed index.

| Source assertion | Public API | Exact scope |
| --- | --- | --- |
| Analytic extension of I_n/γ_n² | `.analytic`, `.factorization`, `.normalized_eq_quotient` | F_n is analytic on W and I_n=γ_n²F_n everywhere, with the actual indexed action and canonical gap. On W\Z_n it is exactly the quotient. |
| Principal root | `.root_analytic`, `.root_sq` | ξ_n is literally `Complex.sqrt (4*F_n)`, analytic on W, and ξ_n²=4F_n. |
| Real analyticity | `.real_analytic` | Both functions are also analytic over ℝ on the same domain. |
| Positive real part | `.re_pos`, `.locally_uniform`, `SourceNormalizedActionUniformBounds.positive` | At every complex point of W, one open neighborhood and one positive lower bound work for Re F_n at every n. |
| Both sequence asymptotics | `.locally_uniform`, `SourceNormalizedActionUniformBounds.asymptotics` | Exact ℓ^(p/2)+ℓ^(1+) decompositions of 4F_n−1 and ξ_n−1, locally uniformly in the original source topology. |
| Nonvanishing and the real branch | `.root_ne_zero`, `.root_real_positive` | ξ_n never vanishes on W and is positive real at real-type sources, including collapsed gaps. |
| Free normalization | `.root_zero`, `sourceNormalizedActionComplexExtension_zero_source` | ξ_n(0)=1 and F_n(0)=1/4 for every n, including n=0. |
| Compatibility with existing actions | `.agreement` | Every ψ∈W belongs to every old complex-action chart domain, and both indexed actions agree there. |

The asymptotics choose one open U containing an arbitrary complex φ∈W,
with U⊆W, and four functions GA, GR, BA, BR before choosing ψ, n or q.
GA and GR take values in `Coeff (ENNReal.ofReal (p.toReal/2))`, including
the quasi-norm case p/2<1. BA and BR take values in the actual intersection
space `CoeffOnePlus`. Their coordinates satisfy

`GA(ψ)_n + BA(ψ)_n = 4F_n(ψ)−1`,
`GR(ψ)_n + BR(ψ)_n = ξ_n(ψ)−1`.

One pair of constants bounds the two half-exponent quasi-norms throughout
U. For every finite q>1, another pair bounds the ℓ^q projections of these
same BA and BR throughout the same U. BA and BR are continuous there.
Thus neither the neighborhood nor the one-plus summands depend on q.

The bridge `indexedAction_eq_complexAction_allIndices_near_real` is proved
by taking a single real-centered source ball inside a simultaneous-contour
neighborhood. For every n, its fixed circle defines a valid old action
chart on that same ball. Chart compatibility identifies the old and new
actions for every n at once. A finite intersection then combines that
ball with the previously proved analytic factors, analytic principal roots,
positive lower bounds and one-plus decompositions.

The final W is the union of all qualifying open neighborhoods inside W₀.
Any complex point of W belongs to one such neighborhood, which supplies
the local uniform bounds there. This proves the requested statement at
all complex points, rather than only at the real centers used to establish
existence. As a consequence, `.action_eq_zero_iff_gap_zero` also proves
the exact complex zero-gap criterion throughout W.

## Equation (2.18): the literal deleted product and recentered actions

`sourceActionChi hp hp1 n ψ z` is the actual unordered product over
integers m≠n of `(critical_m(ψ)−z)/w_m(ψ,z)`. Its equality to the
established analytic quotient is proved on the full moving complement
of the other gap segments. No division by the selected critical factor
is used to define it. The free value is one everywhere in that omitted
domain, including at the selected collapsed gap.

`SourceSimpleSpectralDomainData.criticalDisplacement_analytic` assembles
coordinate analyticity and the locally uniform ℓᵖ bound into analyticity
of the entire critical displacement. Substituting that map into
Corollary 10.6 proves joint spectral/source analyticity of χ_n.

`SourceLemma11_1Data.actionChi` upgrades any existing open W on the same
W. The public existence theorem `sourceEquation2_18` retains an open
connected neighborhood of the entire real-type source locus, for every
finite p>1, and the full preceding Lemma 11.1 package. Its assertions are:

| Assertion | Public API | Scope |
| --- | --- | --- |
| Literal product factorization Δ′/Q=−i(critical_n−z)χ_n/w_n | `.factorization` | Every spectral point off all actual gaps, at complex sources. |
| Joint analyticity of χ_n | `.joint` | The full moving complement of all gaps except n, over the unchanged W. |
| Original fixed domain | `.fixed` | `(ℂ ∖ ⋃_{m≠n} closure(D_m)) × V` for every original isolating family on V⊆W. |
| Through the selected disk | `.disk` | All of D_n×V, including both gap endpoints and collapsed gaps. |
| Recentered action formula | `.circuit` | I_n=(i/π)∮(critical_n−z)²χ_n/w_n on every finite piecewise C¹ winding-one circuit in the original D_n minus its gap, for ψ∈V∩W. |

The circuit proof subtracts critical_n times the vanishing unweighted
period from the weighted action integral. The factorization then gives
the exact i/π normalization. `PiecewiseC1Loop.integral_congr` transfers
pointwise identities along the actual contour pieces without imposing
global integrability or continuity. No reality, noncollapsed-gap or
prescribed-homotopy hypothesis is added to the recentered formula.

The printed fixed domain has U_n under a union over m≠n. The formal
fixed-domain statement uses U_m, agreeing with Corollary 10.6 and the
deleted product. It does not claim the incorrect printed domain.

## Equation (2.19) and extension on the original domain

`SourceEquation2_18Data.gapFormulas` upgrades the existing open connected
W containing the entire real-type source locus. It keeps that W and its
full preceding package. `sourceEquation2_19` is the public existence
theorem for every finite p>1.

Write τ_n for the canonical midpoint, δ_n=γ_n/2 for the half-gap,
λ_t=τ_n+δ_n t, and t_n=(critical_n−τ_n)/δ_n. All quantities use their
actual existing definitions, with `sourceActionCriticalCoordinate` for
t_n and the literal `sourceActionChi` for χ_n.

| Assertion | Public API | Exact scope |
| --- | --- | --- |
| Weighted gap integral | `.action_integral` | I_n=(2/π)∫[-1,1](critical_n−τ_n−δ_n t)²χ_n(λ_t)/sqrt(1−t²) dt for every complex ψ∈W, including zero gaps. |
| Equation (2.19) | `.normalized_integral` | 4I_n/γ_n²=(2/π)∫[-1,1](t_n−t)²χ_n(λ_t)/sqrt(1−t²) dt whenever the actual canonical gap is nonzero. |
| Endpoint integrability | `SourceEquation2_18Data.chi_gap_weighted_integrable` | Both complex weighted integrands are interval integrable, not just assigned a totalized integral. |
| Critical coordinate | `.previous.actionCriticalCoordinate_eq_gap_mul` | t_n=2γ_n B_n with the actual ℓᵖ coefficient from Lemma 10.10, also at collapse. |
| Filled normalized action | `sourceNormalizedIndexedAction`, `.analytic` | The literal indexed quotient off zero gaps, χ_n(τ_n)/4 at zero gaps, analytic on all of the original W. |
| Factorization through collapse | `.factorization` | I_n=γ_n² F_n at every complex point of the original W. |
| Collapsed limit | `.collapsed_limit` | 4I_n/γ_n² tends to χ_n(τ_n) along arbitrary complex approaches within W outside the selected zero-gap set. |
| Midpoint regularity | `.midpointChi_analytic` | χ_n(τ_n) is analytic on the same original W. |
| Compatibility with Theorem 11.2 | `.normalized_eq_theorem11_2` | F_n equals the previously established normalized extension on that theorem's smaller domain. |
| Collapsed principal root | `.normalizedRoot_sq_eq_chi_of_gap_zero` | On the smaller domain, ξ_n²=χ_n(τ_n) at zero gaps. |
| Free normalization | `sourceNormalizedIndexedAction_zero_source` | F_n(0)=1/4 for every signed index. |

The regular numerator `(critical_n−z)²χ_n(z)` is jointly analytic through
the selected gap. Its cosine mean is analytic using only the midpoint
and squared gap. Equality to the action holds on real sources, with a
separate collapsed-gap argument, and propagates across the entire
original connected W by real-form uniqueness and the analytic identity
theorem. No analytic labeling of individual endpoints is assumed.

`integral_div_sqrt_one_sub_sq_eq_cosine` proves the complex-valued
arccos substitution directly. `intervalIntegrable_div_sqrt_one_sub_sq`
uses the integrable inverse-square-root weight and a continuous complex
numerator; the values assigned at the two singular endpoints do not
affect the integral. This proves the source's literal weighted formulas.

For extension, `SourceEquation2_18Data.normalizedKernel_joint` establishes
joint analyticity of the existing rationalized kernel at all complex
sources in W. Its denominators remain nonzero on the original local
circles. The resulting candidates equal the actual indexed quotient at
nonzero gaps and the Cauchy midpoint value at zero gaps. Thus the explicit
filled function agrees locally with an analytic circle integral and is
analytic on all W. This proves the extension assertion on every original
V_φ⊆W; it is independent of the old complex-action chart domain.

## Page 62: uniform estimates on the entire original domain

`SourceEquation2_19Data.originalEstimates` retains the original open W and
all previous formulas and analytic extension results. The public existence
theorem `sourceSection11OriginalEstimates` gives such an open connected W
containing the entire real-type source locus, for every finite p>1.

| Assertion | Public API | Exact scope |
| --- | --- | --- |
| Literal gap supremum | `sourceActionChiGapSup`, `.chiGapSup_bddAbove`, `.norm_chi_sub_one_le_gapSup` | The actual supremum of ∣χ_n−1∣ over G_n is finite and bounds every point, including endpoints and collapsed complex gaps. |
| Collapsed and free values | `sourceActionChiGapSup_of_gap_zero`, `sourceActionChiGapSup_zero_source` | At collapse the supremum is the midpoint error; every free-source supremum is zero. |
| Original isolating families | `.chiGapSup_refined_on` | Any existing original family is allowed. One open neighborhood supports all indices and every finite r>1 with r≥p/2. |
| Critical coordinate | `.criticalCoordinate_halfExponent`, `.criticalCoordinate_locally_uniform` | The exact t_n has an actual ℓ^(p/2) coefficient, with norm at most 2‖γ‖_p‖B‖_p and locally uniform bounds on W. |
| Cosine identity through collapse | `.normalized_eq_cosineModel` | 4F_n is the actual normalized cosine model at every complex point of W, even at zero gaps. |
| Quantitative action error | `.norm_normalized_sub_one_le` | ‖4F_n−1‖≤8∣γ_n∣²∣B_n∣²+2(2∣γ_n∣∣B_n∣+1)² sup_G_n∣χ_n−1∣ on W. |
| Both source estimates together | `SourceSection11OriginalEstimates.locally_uniform` | One neighborhood and four actual summand functions give the two ℓ^(p/2)+ℓ^(1+) decompositions, before every index and one-plus exponent. |

The critical-displacement map is analytic into the original ℓᵖ space.
Pulling back the joint quotient-estimate neighborhood along its graph
therefore gives an open source neighborhood at any complex point of W.
Lemma 10.10 identifies its numerator-minus-midpoint offset with γ²B,
an actual bounded half-exponent sequence. Its inclusion into each refined
exponent gives the required quotient majorants. These cover the original
disks and finite central block; restricting them to G_n controls the
literal supremum. Compactness and analyticity independently establish
that this supremum is finite.

The cosine representation and its error estimate extend to collapsed
complex gaps using F_n=χ_n(τ_n)/4 and t_n=0 there. Uniform bounds for γ and
B then transfer the supremum estimate to 4F_n−1. Both estimates hold on
one neighborhood chosen before the refined exponent. The resulting
ℓ^(p/2) and genuine ℓ^(1+) summand functions are chosen before all
one-plus projections; each projection has a uniform norm bound on that
same neighborhood. Quasi-norms below exponent one are handled explicitly.

This proves the original-domain assertions directly. The known limitation
of Lemma 10.8 for arbitrary numerator offsets does not apply: here the
actual critical offset has the stronger half-exponent bound required by
the quotient estimates.

## Next source audit

The Section 11 audit now covers Lemma 11.1, Theorem 11.2, equations
(2.16)–(2.19), and the following original-domain uniform estimates.
The principal square root and positivity use Theorem 11.2's smaller
common domain; no such claims are added on the full original W.
Next is Section 12: equation (2.20), the normalized periods (2.21), and
Theorem 12.1 with its simultaneous domain, analytic root dependence,
uniform offset bounds and real-gap location. The dissertation remains
incomplete.

## Validation

The original-domain estimates step has seventeen focused checks covering
retention of W, the literal supremum and collapsed value, the complex
cosine identity and quantitative bound, the critical-coordinate sequence,
arbitrary original disk families, fixed summands before all one-plus
exponents, literal quotient agreement, exact collapsed error, free
values, and p=3/2, p=2 and p=4. At p=3/2, the critical-coordinate check
explicitly constructs an ℓ^(3/4) sequence. All pass without warnings.
The full `./scripts/check.sh` gate passed: 6,962 build jobs, the complete
public example suite, and the axiom audit of 32,580 NLS declarations.
There are 21 existing build warnings; the five new modules and seventeen
focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding equation (2.19) step:

The equation (2.19) step has eighteen focused checks covering the original
domain, both weighted identities and endpoint integrability, the exact
critical coordinate, analytic extension, factorization and collapsed
limits, original circles, compatibility with Theorem 11.2, midpoint
analyticity, the collapsed root square, free normalization, complex
integral constants, and p=3/2 and p=4. All pass without warnings.
The full `./scripts/check.sh` gate passed: 6,957 build jobs, the complete
public example suite, and the axiom audit of 32,536 NLS declarations.
There are 21 existing build warnings; the six new modules and eighteen
focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding equation (2.18) step:

The equation (2.18) step has ten focused checks: unchanged-domain
retention, the full critical displacement's analyticity, the moving and
fixed omitted domains, the entire selected original disk, exact quotient
factorization, general central circuits, the nonzero free value χ_0(0)=1,
the actual free quotient −i at z=i, and p=3/2. All pass without warnings.
The full `./scripts/check.sh` gate passed: 6,951 build jobs, the complete
public example suite, and the axiom audit of 32,456 NLS declarations.
There are 21 existing build warnings; the five new modules and ten
focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding Theorem 11.2 step:

The Theorem 11.2 step has fifteen focused checks: retention of the original
domain and lemma, the literal analytic zero locus and relative closedness,
zero action at complex central collapses, one chart neighborhood for all
indices, canonical-gap factorization, the exact quotient off Z_n, common
positive lower bounds at arbitrary complex points, exact sequence-summand
quantifiers, real and complex analyticity, principal-root square and
nonvanishing, positive real branch, complex zero-gap equivalence, actual
nonzero free normalization, and p=3/2 and p=4. All pass without warnings.
The full `./scripts/check.sh` gate passed: 6,946 build jobs, the complete
public example suite, and the axiom audit of 32,429 NLS declarations.
There are 21 existing build warnings; the four new modules and fifteen
focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding Lemma 11.1 step:

The full Lemma 11.1 step has eleven focused checks: unchanged W and
equation (2.16), joint root and mixed derivatives at complex sources,
the original central circle and general-circuit gradient formulas,
complex collapsed central gaps, canonical-gap real properties and strict
positivity, preservation of the older complex-action germs, the nonzero
identity ∮z(1/z)′ dz=−2πi checking the integration-by-parts sign, and p=3/2.
The full `./scripts/check.sh` gate passed: 6,942 build jobs, the complete
public example suite, and the axiom audit of 32,375 NLS declarations.
There are 21 existing build warnings; the six new modules and eleven
focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding equation (2.16) step:

The equation (2.16) step has eleven focused public checks: unchanged W and
Lemma 10.11, general winding at complex sources, different isolating
families, the literal central action formula, analyticity on W,
simultaneous-circle agreement, nonzero real actions, complex germs and
connected overlaps, the actual k-turn integral of 1/z equal to k·2πi,
and p=3/2. The full `./scripts/check.sh` gate passed: 6,936 build jobs,
the complete public example suite, and the axiom audit of 32,351 NLS
declarations. There are 21 existing build warnings; the five new modules
and focused checks are warning-free. No admitted proofs, additional axioms
or heartbeat overrides were introduced. The 156-label source inventory
and `git diff --check` also passed.

The preceding contour-construction step:

Nine public examples check the unchanged-domain upgrade, simultaneous
quantifiers, all-gap avoidance, central winding, both signed tails, the
literal normalized formula, joint and local action analyticity, actual
existence at every source in W, and the exponent p=3/2. The complete
`./scripts/check.sh` gate passed: 6,931 build jobs, the full public example
suite, and the axiom audit of 32,305 NLS declarations. The build retains
21 existing warnings; the four new modules and focused checks are
warning-free. No admitted proofs, additional axioms or heartbeat overrides
were introduced. The 156-label source inventory and `git diff --check`
also passed.

## The critical-point zero in the proof of Lemma 11.1

On printed p. 61, the proof says its recentered real action integrand is
strictly positive throughout the interior of an open gap. That pointwise
claim needs an exception at the canonical critical point.
[SourceActionIntegrandCriticalZero.lean](../NLS/ZakharovShabat/SourceActionIntegrandCriticalZero.lean)
defines the displayed real integrand, including the literal integer power
(-1)^(n+1), the factor x-critical_n, the discriminant derivative, and the
positive square root of Delta(x)^2-4.

For every finite p>1, every real source, and every open indexed gap,
`sourceRecenteredRealActionIntegrand_has_interior_zero` proves that the
critical coordinate lies strictly inside the gap, the square-root
denominator there is strictly positive, and the integrand is zero there.
Thus this is an ordinary interior zero, independent of any endpoint
convention for division by zero.

`not_sourceRecenteredRealActionIntegrand_pos_everywhere` refutes the
literal pointwise strictness sentence. The method
`SourceLemma11_1Data.action_pos_and_recenteredIntegrand_zero` retains the
proved strict positivity of the actual action alongside that zero.
The earlier action proof uses the strictly positive arcosh area and does
not require the false pointwise assertion.

Two public examples construct an actual Hilbert real-source witness at
any signed index, using the proved density of open gaps, and retain the
action conclusion for all finite p>1. This step does not separately prove
pointwise positivity away from the critical coordinate; the action
theorem and its integral proof remain unchanged.
