# Section 11: actions

This audit begins with printed p. 61 of the dissertation. The contour
construction, equation (2.16), and independence of general admissible
counterclockwise piecewise C¹ circuits are proved on the unchanged common
source domain from Section 10. Each indexed action is analytic on W and
has the stated real sign and zero-gap criterion. The gradient in equation
(2.17) and the full Lemma 11.1 remain next.

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

## Remaining source assertions

The exact Fréchet gradient in equation (2.17) still needs to be established
at all complex sources of W, as does the complex collapsed-gap zero
consequence in the proof of Lemma 11.1. Theorem 11.2 and its permitted later
shrink of W are separate. The full lemma and dissertation are not yet
complete.

## Validation

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
