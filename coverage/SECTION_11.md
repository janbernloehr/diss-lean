# Section 11: actions

This audit begins with printed p. 61 of the dissertation. The contour
construction preceding equation (2.16) and joint analyticity of its
integrand are proved on the unchanged common source domain from Section 10.
The general contour-independent action definition and full Lemma 11.1 are
next; existing action results on other domains do not alone settle those
statements on this retained W.

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

## Remaining source assertions

The chosen circle integrals use equation (2.16) literally. This milestone
does not yet prove independence of every admissible counterclockwise
piecewise C¹ circuit or every original isolating family. Those comparisons
must precede the global indexed-action statement on W.

The existing `sourceComplexAction` was glued from a different collection
of real-base charts. Agreement on the whole retained W must be proved,
or an extended action must be explicitly bridged to the existing one;
it is not justified merely by analyticity of the new local circle
integrals. Lemma 11.1 still requires its exact complex-source gradient,
real nonnegativity and vanishing precisely at a collapsed gap on this
same domain. Theorem 11.2 and its permitted later shrink of W are separate.

## Validation

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
