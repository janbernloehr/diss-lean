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
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md). Equation (2.19) and the ensuing
original-domain extension claims remain before Section 12.

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

## Remaining source assertions

The theorem uses the established rationalized circle construction for
analytic extension through collapsed gaps. It does not require the source's
particular removability proof. Equation (2.19), the preceding weighted
gap-integral formula for complex sources, their original-domain
quantifiers and the stated collapsed limit still need a separate
comparison. In particular, the established smaller-domain Theorem 11.2
does not by itself prove the proof's extension claim on every original
V_φ. Section 12 follows that audit.
The dissertation remains incomplete.

## Validation

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
