# Section 11 ordered assertion comparison

Twenty-one of 22 ordered Section 11 groups are compared: nineteen matched and two corrected occurrences. The literal gap-supremum and normalized-action expansions match on the original complex domain, with locally bounded half-exponent coefficients and fixed genuine one-plus summands. The actual critical offset supplies the stronger bound needed by Lemma 10.8. One group remains pending: the final positivity, uniform tail and principal-root claims. Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, the exact cited 2014 construction, Appendix G.2 norm interpretation and broader source inventory remain unresolved.

This inventory covers printed pp.61–62, using one-based newline positions in
the reviewed source extraction; form feeds do not add lines. The first twenty-one
groups have been compared to the statements and proofs identified below.
The remaining entries provide navigation for further semantic comparison.
Existing named-theorem audits retain their own scope; they do not automatically
settle every intermediate display or proof assertion in these pending entries.

All compared claims use the original finite-p source spaces with 1<p<infinity.
The original open connected W0 contains the entire real-type locus. Theorem 11.2
uses one smaller open W still containing that locus; connectedness of this W
is not required. Standard finite piecewise C1 regularity is explicit when
interpreting contour integrals.

| Group | Printed page | Source lines | Assertion | Status |
| --- | --- | --- | --- | --- |
| S11-001 | 61 | 4737–4741 | One source neighborhood with all original isolating disks, counterclockwise circuits and fixed open collars whose closures avoid the gaps. | matched |
| S11-002 | 61 | 4743–4748 | Definition (2.16): the literal action integral with coefficient 1/pi and spectral weight lambda. | matched |
| S11-003 | 61 | 4750–4752 | Joint analyticity on each collar and independence of both circuit and original isolating family. | matched |
| S11-004 | 61 | 4754–4761 | Lemma 11.1: action analyticity on the entire common domain and exact gradient (2.17). | matched |
| S11-005 | 61 | 4762–4763 | Lemma 11.1: real nonnegativity and equivalence of zero action with a collapsed gap. | matched |
| S11-006 | 61 | 4766–4768 | Proof of action analyticity, the gradient formula and complex collapsed-gap vanishing. | matched |
| S11-007 | 61 | 4769–4782 | Real-source recentering at the critical point and the literal positive-root gap integral. | matched |
| S11-008 | 61 | 4782–4784 | Pointwise sign of the recentered integrand and strict positivity of its integral. | corrected |
| S11-009 | 61 | 4786–4790 | Definition of Z_n as the squared-gap zero locus in the original common domain. | matched |
| S11-010 | 61 | 4795–4805 | Figure 2.6: simultaneous enclosing circuits and fixed open collars within the original disks. | matched |
| S11-011 | 62 | 4816–4822 | Analytic subvariety Z_n and the normalized-action extension problem. | matched |
| S11-012 | 62 | 4824–4832 | Theorem 11.2: one complex neighborhood and locally uniform p/2 plus 1+ normalized-action expansion. | matched |
| S11-013 | 62 | 4833–4842 | Positive real part bounded away from zero, analytic nonvanishing xi, its asymptotics and free value one. | matched |
| S11-014 | 62 | 4844–4853 | Equation (2.18): selected-root factorization, literal deleted product chi and its fixed joint domain. | corrected |
| S11-015 | 62 | 4855–4859 | Recentered action integral with coefficient i/pi and the squared critical factor. | matched |
| S11-016 | 62 | 4860–4869 | Complex gap-side parametrization and the actual weighted integral for the action. | matched |
| S11-017 | 62 | 4870–4876 | Equation (2.19): normalized-action formula and the critical-to-midpoint coordinate t_n. | matched |
| S11-018 | 62 | 4878–4884 | Small-gap estimate t_n=O(gap) and the exact collapsed limit of 4I_n/gap^2. | matched |
| S11-019 | 62 | 4885–4889 | Continuous removal across Z_n, analytic collapsed value and analytic extension. | matched |
| S11-020 | 62 | 4890–4895 | Full-domain locally uniform literal gap-supremum estimate for chi_n minus one. | matched |
| S11-021 | 62 | 4897–4906 | Locally uniform t_n estimate and normalized-action expansion from weighted moments. | matched |
| S11-022 | 62 | 4908–4917 | Real-locus positivity and tail limit, collapsed xi identity and the remaining common-neighborhood claims. | pending |

## Compared opening claims

### S11-001: One source neighborhood with all original isolating disks, counterclockwise circuits and fixed open collars.

- For any complex source in the unchanged W and any original isolating family on an open V within W, the contour package supplies one open connected U containing that source and contained in V, chosen before all signed indices and nearby sources.
- The original disk D_n is unchanged. Three positive nested radii give a common gap enclosure, a counterclockwise integration circle and the original disk. The fixed annular collar contains the circle, is open, and lies in D_n minus the moving gap for every source in U.
- The selected circle has actual winding integral one about every gap point, including collapsed gaps. All distant signed indices use the free center n*pi and radii pi/8, 3*pi/16, pi/4 with one common cutoff.
- Finitely many central gap-enclosure neighborhoods intersect one uniform-tail neighborhood. Complex stability uses openness of the joint gap complement, compactness of the sphere, continuity of the symmetric midpoint and connectedness of the gap; it does not assert continuity of ordered complex endpoints.

Public declarations:

- `NLS.ZakharovShabat.SourceActionContourFamily.closedBall_subset_original`
- `NLS.ZakharovShabat.SourceActionContourFamily.collar_open`
- `NLS.ZakharovShabat.SourceActionContourFamily.collar_subset_cutDisk`
- `NLS.ZakharovShabat.SourceActionContourFamily.sphere_subset_collar`
- `NLS.ZakharovShabat.SourceActionContourFamily.windingIntegral_eq_one`
- `NLS.ZakharovShabat.SourceEquation2_15Data.original_contourFamily`
- `NLS.ZakharovShabat.SourceLemma10_11Data.actionContours`
- `NLS.ZakharovShabat.SourceSection11ContourData.neighborhoods`
- `NLS.ZakharovShabat.sourceSection11Contours`

The printed local source neighborhood is chosen to support the common contours. The construction may shrink a supplied V to U while retaining global W and every original disk. It does not claim that arbitrary already-fixed V supports an interior common circle without this local refinement.

### S11-002: Definition (2.16): the literal action integral with coefficient 1/pi and spectral weight lambda.

- The action is an actual integral of lambda*Delta prime/canonicalRoot with the exact factor 1/pi, with no extra imaginary normalization.
- The indexed action chooses one original isolating circle and is proved equal to every such circle. The Section 11 inner circles, strictly inside the original disks, compute this same function.
- The arbitrary default of the choice-based indexed definition outside sources admitting isolating circles is not used on W, where the common contour package supplies one at every source and index.

Public declarations:

- `NLS.ZakharovShabat.SourceCriticalRootPeriodCircle.action_eq`
- `NLS.ZakharovShabat.SourceSection11ContourData.defineActions`
- `NLS.ZakharovShabat.sourceActionContour`
- `NLS.ZakharovShabat.sourceEquation2_16`
- `NLS.ZakharovShabat.sourceIndexedAction`
- `NLS.ZakharovShabat.sourceIndexedAction_eq_circle`

The literal contour and piecewise-path integrals are defined independently of the indexed action; equality is a theorem. Keep counterclockwise winding one explicit.

### S11-003: Joint analyticity on each collar and independence of both circuit and original isolating family.

- The source equation (2.15) package proves the weighted integrand jointly analytic on the full moving-gap complement; each fixed collar times its common local source neighborhood lies in this domain.
- The normalized actual integral of every piecewise C1 closed contour in an original cut disk is the indexed action times the actual winding integral about the selected midpoint.
- For winding-one circuits the action is therefore independent of the chosen contour and of the original isolating family, even when the two original disks are not nested.
- The contour-period proof subtracts a reciprocal pole carrying the circle period, constructs a primitive of the zero-period remainder on the whole cut disk, and integrates the pole by its winding. Neither a supplied homotopy nor an open-gap or real-source assumption is required.

Public declarations:

- `NLS.ZakharovShabat.SourceActionContourFamily.analytic_actionCircle`
- `NLS.ZakharovShabat.SourceActionContourFamily.analytic_integrand_on_collar`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.actionContour_eq_mul_winding`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.indexedAction_eq_circuit`
- `NLS.ZakharovShabat.sourceActionContour`
- `NLS.ZakharovShabat.sourceActionContour_eq_of_original_circuits`

Repeated or reversed contours retain their winding factor; the printed action independence is the winding-one specialization. Standard finite piecewise C1 contour regularity is explicit.

## Lemma 11.1 statements and initial proof

### S11-004: Lemma 11.1: action analyticity on the entire common domain and exact gradient (2.17).

- Every indexed action is complex analytic throughout the unchanged open common W for every finite p>1 and signed index. Local simultaneous fixed circles represent the same indexed function in an actual neighborhood of every complex source.
- Equation (2.17) has the exact coefficient -1/pi and no spectral weight: the complex Frechet derivative applied to every original CoeffPair p direction is the actual contour integral of the discriminant variation divided by the canonical root.
- The formula holds on every admissible winding-one finite piecewise C1 circuit in every original isolating family, including non-real sources and collapsed gaps. The local isolation neighborhood is open and contains the evaluation source; no replacement of W is made.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_16Data.actionGradients`
- `NLS.ZakharovShabat.SourceEquation2_16Data.circuit_gradient`
- `NLS.ZakharovShabat.SourceEquation2_16Data.original_circle_gradient`
- `NLS.ZakharovShabat.SourceSection11ContourData.analytic_indexedAction`
- `NLS.ZakharovShabat.sourceLemma11_1`

The gradient is expressed as the continuous complex Frechet derivative evaluated on every original source direction. The proof establishes that functional identity for all finite p>1 directly; it does not independently audit the cited Hilbert-space theorem.

### S11-005: Lemma 11.1: real nonnegativity and equivalence of zero action with a collapsed gap.

- On the entire real-type source locus, the indexed action equals the independently defined real action. Its imaginary part is zero, its real part is nonnegative, and the action vanishes exactly when the actual canonical gap is zero.
- Open real gaps have strictly positive action for every signed index, including the central gap. The discriminant derivative and upper-root parity factors cancel; the weighted upper boundary integral is the negative arcosh area, and the enclosing-circle orientation gives the positive factor 2/pi.
- The arcosh profile is continuous up to its zero endpoint values and strictly positive in an open gap. Its derivative is interval-integrable through the branch points: the radicand factors as the endpoint-distance product times a positive continuous deleted product.
- Integration by parts proves the strict integral sign. Circle independence transfers it from small midpoint circles to the indexed action; collapsed-gap analytic continuation gives the complementary zero case.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.action_pos_of_real_gap_ne_zero`
- `NLS.ZakharovShabat.exists_sourceActionCircle_positive_real_on_small_realGapCircles`
- `NLS.ZakharovShabat.intervalIntegrable_realGapHalfDiscriminant_arcosh_deriv`
- `NLS.ZakharovShabat.realGap_weighted_arcosh_integral_eq_and_neg`
- `NLS.ZakharovShabat.sourceActionCircle_nonneg_and_eq_zero_iff_gap_zero_on_midpointCircle`
- `NLS.ZakharovShabat.sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_all`
- `NLS.ZakharovShabat.sourceIndexedAction_eq_sourceRealAction`
- `NLS.ZakharovShabat.sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero`
- `NLS.ZakharovShabat.sourceRealAction_nonneg_and_eq_zero_iff_gap_zero`

This compares the lemma statement and its actual integral proof. It does not classify the subsequent literal real-gap display or its pointwise strict-positivity sentence, which remain in S11-007 and S11-008. The strict action result does not depend on that sentence.

### S11-006: Proof of action analyticity, the gradient formula and complex collapsed-gap vanishing.

- Joint analyticity of the literal weighted integrand on a fixed collar permits differentiation under its circle integral. Local equality of the indexed action and the circle action identifies their full Frechet derivatives.
- Differentiating the canonical-root square identity gives its source and spectral derivatives. Commutation of the mixed discriminant derivatives gives D_source(Delta prime/Q)=d_spectral(D_source Delta/Q). Spectral integration by parts supplies the negative sign in (2.17).
- The variation divided by the canonical root is analytic on each original closed disk minus the selected gap. The outer-circle winding formula extends the derivative identity to every original winding-one piecewise C1 circuit.
- At a complex collapsed gap the continued critical-root quotient is analytic throughout the original disk. Multiplication by the spectral coordinate preserves analyticity; Cauchy on an interior circle gives zero action. Agreement with the literal quotient is used only on that circle, away from the gap.

Public declarations:

- `NLS.ComplexAnalysis.PiecewiseC1Loop.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut`
- `NLS.ZakharovShabat.SourceEquation2_15Data.circleIntegral_criticalRatio_sourceFDeriv_eq_neg_variation`
- `NLS.ZakharovShabat.SourceEquation2_15Data.criticalRatio_source_fderiv_eq_spectral`
- `NLS.ZakharovShabat.SourceEquation2_15Data.fderiv_actionCircle_eq_gradient_integral`
- `NLS.ZakharovShabat.SourceEquation2_15Data.root_joint_fderiv`
- `NLS.ZakharovShabat.SourceEquation2_15Data.root_source_fderiv`
- `NLS.ZakharovShabat.SourceEquation2_15Data.root_spectral_deriv`
- `NLS.ZakharovShabat.SourceEquation2_16Data.circuit_gradient`
- `NLS.ZakharovShabat.SourceEquation2_16Data.indexedAction_zero_of_gap_zero`
- `NLS.ZakharovShabat.SourceLemma10_11iData.continued_analytic_originalDisk`
- `NLS.ZakharovShabat.SourceSection11ContourData.analytic_indexedAction`
- `NLS.ZakharovShabat.analyticOnNhd_sourceDiscriminantVariation_div_root`
- `NLS.ZakharovShabat.circleIntegral_mul_deriv_sourceDiscriminantVariation_div_root_eq_neg`

The same-domain differentiation proof replaces the printed citation-and-extension route and covers 1<p<infinity, without asserting an independent verification of reference [23, Theorem 13.1]. Analyticity at a collapsed root means the removable continuation, not a claim that totalized pointwise division is analytic there.

The [full lemma package](../NLS/ZakharovShabat/SourceLemma11_1.lean),
[indexed gradients](../NLS/ZakharovShabat/SourceIndexedActionGradient.lean),
[common-domain differentiation](../NLS/ZakharovShabat/SourceActionCommonGradient.lean)
and [real action properties](../NLS/ZakharovShabat/SourceRealAction.lean)
retain the original functions and domains. The [all-index positivity proof](../NLS/ZakharovShabat/SourceActionAllGapPositive.lean)
uses the [weighted arcosh identity](../NLS/ZakharovShabat/RealGapWeightedArcoshIntegral.lean)
and its [endpoint integrability](../NLS/ZakharovShabat/RealGapArcoshIntegrability.lean).
That statement comparison recorded 24 fully inspected modules. At that
documentation-only milestone, the Lean and dependency snapshot was unchanged
from the successful full gate at `7692c09`, so that validation was reused.

The next subsection compares the displayed real-gap calculation and its
corrected pointwise sign argument. The [historical critical-point correction](SECTION_11.md#the-critical-point-zero-in-the-proof-of-lemma-111)
is retained. No new refutation is needed.

## Literal real-gap calculation and corrected pointwise signs

### S11-007: Real-source recentering at the critical point and the literal positive-root gap integral.

- The indexed action equals 1/pi times the actual integral of (lambda-critical_n)*Delta prime/canonicalRoot on every original winding-one finite piecewise C1 circuit. More generally any complex recentering constant is allowed, since the unweighted period vanishes. This retains the original disks and common W, including complex and collapsed gaps.
- For real sources the same action equals 2/pi times the literal real gap integral. Its integrand retains the integer power (-1)^(n+1), the real critical coordinate, the actual discriminant derivative and the positive square root of Delta squared minus four. The statement covers all finite p>1 and every signed index.
- Casting that real integrand to Complex gives (x-critical_n.re) times the previously proved Section 10 real kernel. That kernel is minus the actual upper canonical boundary quotient in the gap interior, fixing the orientation and sign before integration.
- The actual weighted upper boundary integral equals the negative arcosh area for any real recentering constant. The shrinking-stadium and small-circle identity gives the action as -2/pi times the upper boundary integral. Together with circle independence, this fixes the exact 2/pi coefficient for the original indexed action.
- The literal real integrand is interval-integrable through both branch points, by the integrable boundary kernel times a continuous affine factor. At a collapsed gap the endpoint integral has zero length and agrees with the zero action. No assumed endpoint-integrability premise is introduced.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.action_eq_recentered_circuit`
- `NLS.ZakharovShabat.SourceLemma11_1Data.originalCircuit_realCalculation`
- `NLS.ZakharovShabat.sourceIndexedAction_eq_recenteredRealIntegral`
- `NLS.ZakharovShabat.sourceIndexedAction_eq_realGapArcoshIntegral`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_cast`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_eq_halfDiscriminant`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_intervalIntegrable`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_integral_eq_arcosh`
- `NLS.ZakharovShabat.sourceLemma10_11RealKernel_eq_neg_upper`
- `NLS.ZakharovShabat.sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_all`
- `NLS.ZakharovShabat.exists_sourceActionCircle_eq_upperBoundaryIntegral`

The proof identifies actual contour, side and real interval integrals, with their exact normalizations. It reuses the established shrinking-stadium identity through a small midpoint circle and circle independence; it does not postulate a deformation of each supplied piecewise circuit. The source open-gap formula is also proved in the collapsed zero-length case.

### S11-008: Pointwise sign of the recentered integrand and strict positivity of its integral.

- The displayed numerator is nonnegative on the entire closed real gap, including both endpoints and collapsed gaps. For an open gap, positivity of the denominator transfers interior quotient nonnegativity to the numerator, and continuity extends it to the endpoints.
- The corrected quotient statement is nonnegativity throughout the gap interior, strict positivity away from the canonical critical coordinate, and zero exactly at that coordinate. The denominator is strictly positive there, so this exception is an ordinary interior zero.
- A general mean-value and intermediate-value argument gives positive derivative before the unique interior critical point and negative derivative after it, for a function above its equal endpoint values. The actual signed half-discriminant satisfies those hypotheses, including continuity of its derivative and uniqueness of its critical point.
- The literal real integral is strictly positive on every open real gap. Its equality to the positive arcosh area gives the integral sign independently of the pointwise exception. Multiplication by 2/pi retains strict positivity of the actual action.
- The historical refutation of the everywhere-strict pointwise sentence is preserved. The new work proves the corrected sign statements and the literal integral identity; it adds no refutation.

Public declarations:

- `NLS.ZakharovShabat.sourceRecenteredRealActionNumerator_nonneg`
- `NLS.ZakharovShabat.sourceRealGapHalfDiscriminant_deriv_signs`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_pos`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_nonneg_and_eq_zero_iff`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_integral_pos`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_at_critical`
- `NLS.ZakharovShabat.sourceRecenteredRealActionIntegrand_denominator_pos`
- `NLS.ZakharovShabat.canonicalCriticalPoints_between_of_open_gap`
- `NLS.ZakharovShabat.critical_eq_canonicalCriticalPoints_of_mem_gap`
- `NLS.ComplexAnalysis.derivative_signs_of_unique_critical`

Corrected occurrence: exclude the canonical critical coordinate from the printed pointwise strict-positivity assertion. The closed-gap numerator inequality, real action positivity and exact zero-gap criterion remain valid. Existing historical evidence in SourceActionIntegrandCriticalZero.lean and SOURCE_ERRATA.md is unchanged; the added theorems are positive results.

The [general derivative-sign theorem](../NLS/ComplexAnalysis/SingleCriticalPointSign.lean)
is applied to the actual discriminant in the [corrected integrand signs](../NLS/ZakharovShabat/SourceActionIntegrandSign.lean).
The [literal real calculation](../NLS/ZakharovShabat/SourceLemma11_1RealCalculation.lean)
connects the indexed action, original circuits, the positive-root real integral
and the arcosh area. The comparison inspects 22 module bodies.

Two integration examples construct an actual open real gap at index -1 with
positive integrand values on both sides of its critical zero, and verify the
literal original-circuit formula at p=3/2, including its integer parity and
relative factor two. The full validation passes: 8,517 build jobs, 7,586
public examples and 44,355 transitively audited NLS declarations, with
21 inherited warnings and no new warnings. Source-review integrity and
documentation-link checks also pass.

The next subsection compares the squared-gap zero locus, contour figure
and analytic-zero-locus passage. Existing corrections and
the [wider completion qualifications](COMPLETENESS.md) remain in force.

## Zero-gap locus, closed collars and extension introduction

### Supplement to S11-001: One source neighborhood with all original isolating disks, counterclockwise circuits and fixed open collars.

- The rendered opening at line 4741 requires the closure of U_n prime to lie in the original isolating disk minus the moving gap. The earlier comparison recorded only containment of an open collar. This supplement supplies the stronger printed condition.
- The new compactCollar uses radii halfway between the existing inner radius and circle radius, and halfway between the circle radius and original outer radius. It is open, contains the same circle, and its entire closure lies in the existing collar.
- Consequently the closed collar lies in the original cut disk and avoids all other gaps, uniformly over the same source neighborhood. The original circles, disks and common W are unchanged.
- The literal weighted action integrand is jointly analytic in a neighborhood of each point of the collar closure times the source neighborhood. The strengthened neighborhood theorem makes this simultaneous for all signed indices.

Public declarations:

- `NLS.ZakharovShabat.SourceActionContourFamily.analytic_integrand_on_compactCollar_closure`
- `NLS.ZakharovShabat.SourceActionContourFamily.closure_compactCollar_subset_collar`
- `NLS.ZakharovShabat.SourceActionContourFamily.closure_compactCollar_subset_cutDisk`
- `NLS.ZakharovShabat.SourceActionContourFamily.closure_compactCollar_subset_rootDomain`
- `NLS.ZakharovShabat.SourceActionContourFamily.compactCollar`
- `NLS.ZakharovShabat.SourceActionContourFamily.compactCollar_open`
- `NLS.ZakharovShabat.SourceActionContourFamily.sphere_subset_compactCollar`
- `NLS.ZakharovShabat.SourceSection11ContourData.neighborhoods_with_collar_closures`

Supplement to the earlier S11-001 comparison: the source overline is now explicit and proved. This fills an implementation omission, not a correction to the dissertation. The preceding open-collar construction and its historical review are retained.

### S11-009: Definition of Z_n as the squared-gap zero locus in the original common domain.

- Z_n is literally the original domain W0 intersected with the zero set of the squared canonical periodic gap, for each signed index and every finite p>1.
- Membership is equivalent to membership in W0 and vanishing of the canonical gap itself. The actual indexed action vanishes on this set, including at complex collapsed gaps.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.action_zero_on_gapZeroLocus`
- `NLS.ZakharovShabat.mem_sourceActionGapZeroLocus_iff`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus_eq_preimage`

The definition uses the original source spaces and canonical spectral coordinates. No separate ordered-endpoint analyticity, real-source restriction or smaller normalized-action domain enters Z_n.

### S11-010: Figure 2.6: simultaneous enclosing circuits and fixed open collars within the original disks.

- The rendered figure places each gap inside a counterclockwise circuit, with a surrounding open collar inside its original isolating disk. The chosen circles have actual winding integral one around every gap point, including a collapsed gap.
- The strengthened collars contain those circles and have closures inside the original disks minus the moving gaps. One common source neighborhood supports all signed indices and every nearby complex source.
- The construction uses a finite central intersection and one uniform tail neighborhood. Choosing circles and annular collars realizes the geometric requirements illustrated by the schematic noncircular drawing.

Public declarations:

- `NLS.ZakharovShabat.SourceActionContourFamily.closedBall_subset_original`
- `NLS.ZakharovShabat.SourceActionContourFamily.closure_compactCollar_subset_cutDisk`
- `NLS.ZakharovShabat.SourceActionContourFamily.sphere_subset_compactCollar`
- `NLS.ZakharovShabat.SourceActionContourFamily.windingIntegral_eq_one`
- `NLS.ZakharovShabat.SourceSection11ContourData.neighborhoods_with_collar_closures`

The figure is compared as contour geometry, not as an assertion that the particular drawn shapes are the chosen contours. The original isolating families and circle orientations are retained.

### S11-011: Analytic subvariety Z_n and the normalized-action extension problem.

- The actual squared gap is analytic on the whole original W0 by the retained symmetric-root package. Frozen contour trace invariants recover the midpoint and squared gap, including at collisions, and transfer their source analyticity to those canonical coordinates.
- Z_n is therefore the zero locus of one explicit complex analytic scalar function on W0; its relative closedness is also proved. The analytic-subvariety terminology asserts this zero-locus description, without a smoothness or codimension claim.
- One smaller open complex neighborhood W inside W0 contains the entire real-type locus and supports every normalized indexed action simultaneously. Each extension is complex analytic, hence real analytic, and equals the literal quotient I_n/(gap_n^2) off Z_n.
- The common W is the union of open sets carrying all-index local data. Near each real source, a finite intersection combines common action charts and the normalized factors; a finite head and uniform tail supply all indices on one neighborhood. A countable intersection of independently chosen open sets is not used.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.gapZeroLocus_isClosed`
- `NLS.ZakharovShabat.SourceLemma11_1Data.normalizedActions`
- `NLS.ZakharovShabat.SourceLemma11_1Data.squared_gap_analytic`
- `NLS.ZakharovShabat.SourceSection11ContourData.indexedAction_eq_complexAction_allIndices_near_real`
- `NLS.ZakharovShabat.SourceSection11ContourData.normalizedActions_near_real`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.normalized_eq_quotient`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.real_analytic`
- `NLS.ZakharovShabat.analyticAt_canonicalPeriodicMidpoint_squaredGap_of_sourceIsolating`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedAction_allIndices_analytic_factor`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus_eq_preimage`
- `NLS.ZakharovShabat.sourceTheorem11_2`

This compares the zero-locus assertion and the announced common extension. The original W0 remains the domain of Z_n and Lemma 11.1; the normalized-action neighborhood W may shrink. Theorem 11.2 asymptotics, positivity and its subsequent proof passages remain separately pending.

The [closed-collar module](../NLS/ZakharovShabat/SourceActionContourCollarClosure.lean)
strengthens the [original contour family](../NLS/ZakharovShabat/SourceActionContourFamily.lean).
The [literal zero locus](../NLS/ZakharovShabat/SourceActionGapZeroLocus.lean)
uses the [analytic symmetric coordinates](../NLS/ZakharovShabat/SourceSymmetricContour.lean).
The [common normalized-action package](../NLS/ZakharovShabat/SourceTheorem11_2.lean)
and its [local construction](../NLS/ZakharovShabat/SourceNormalizedIndexedActionLocal.lean)
give the announced extension on one neighborhood. Sixteen module bodies are
recorded in this comparison.

The integration example lets spectral points approach a collar boundary while
the complex source varies. The limit stays outside every gap, and the actual
weighted action integrand converges. The full validation passes: 8,518 build jobs, 7,587
public examples and 44,364 transitively audited NLS declarations, with
21 inherited warnings and no new warnings. Source-review integrity and
documentation-link checks also pass.

The following subsection compares the full Theorem 11.2 statement.

## Opening comparison evidence and validation

The [common contour package](../NLS/ZakharovShabat/SourceSection11Contours.lean)
retains Lemma 10.11. The [contour family](../NLS/ZakharovShabat/SourceActionContourFamily.lean)
uses [complex gap stability](../NLS/ZakharovShabat/SourcePeriodicSegmentComplexStability.lean)
and [uniform tail circles](../NLS/ZakharovShabat/SourceNormalizedActionUniformTailCircles.lean).
The [indexed action](../NLS/ZakharovShabat/SourceIndexedAction.lean),
[actual piecewise contour integral](../NLS/ZakharovShabat/SourceActionPiecewiseContour.lean),
and [equation (2.16) package](../NLS/ZakharovShabat/SourceEquation2_16.lean)
give the literal normalization and contour-independent representation.
The [general period formula](../NLS/ComplexAnalysis/PiecewiseContourPeriod.lean)
uses a [primitive on the cut disk](../NLS/ComplexAnalysis/PrimitiveOnDiscComplement.lean)
and [actual finite piecewise C1 integrals](../NLS/ComplexAnalysis/PiecewiseC1Loop.lean).
The source review records fifteen inspected module bodies and twenty resolved
declaration references in the [public comparison snapshot](source-review-index.json).

That opening comparison changed documentation only. Its Lean and dependency
snapshot was unchanged from commit `7692c09`; the successful full validation
was reused: 8,514 build jobs, 7,584 public examples and a transitive axiom
audit of 44,339 NLS declarations, with 21 inherited warnings. Module hashes,
declaration references, review integrity and documentation links were checked
at that milestone. These checks do not certify source-wide completeness.

The opening comparison above is retained with its original evidence. Preserve the [existing Section 11 audit](SECTION_11.md)
and all wider qualifications in the [completion assessment](COMPLETENESS.md).
Correct constants with proved valid replacements; additional refutations
are not required.

## Theorem 11.2: normalized actions and principal roots

### S11-012: Theorem 11.2: one complex neighborhood and locally uniform p/2 plus 1+ normalized-action expansion.

- For each finite p>1, one open complex W contained in the preceding W0 contains the entire real-type source locus. The normalized action factors are complex analytic for every signed index, including at complex collapsed gaps.
- Off Z_n the factor F_n is exactly the indexed action divided by the squared canonical gap. The displayed normalization is 4F_n=1+GA_n+BA_n, with no extra sign or index-dependent factor.
- At every complex point of W, one open neighborhood admits fixed remainder maps GA and BA before the index and target exponent are chosen. GA belongs to ell-(p/2), BA belongs to the genuine intersection of all finite ell-q spaces q>1, and their stated norm or quasi-norm bounds are uniform on that neighborhood.
- For 1<p<=2, the half-exponent component is zero and the full deviation is the fixed one-plus sequence. For p>2, the full deviation belongs to ell-(p/2) and the one-plus component is zero. Only the bounds of finite-exponent one-plus projections may depend on q.
- The common W is a union of open sets carrying all-index local data. Near each real source, these local data are constructed by a finite intersection of common action charts, analytic factor and root neighborhoods, the positivity neighborhood and the sequence-majorant neighborhood. This supplies local uniformity at every complex point of W.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.normalizedActions`
- `NLS.ZakharovShabat.SourceNormalizedActionUniformBounds.asymptotics`
- `NLS.ZakharovShabat.SourceSection11ContourData.normalizedActions_near_real`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.analytic`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.locally_uniform`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.normalized_eq_quotient`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedActionDeviation_allExponents`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedAction_onePlus_continuous`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedAction_onePlus_decomposition`
- `NLS.ZakharovShabat.sourceTheorem11_2`

The full Theorem 11.2 action statement matches, with the original finite-p source space and one smaller common W. The original W0 remains the domain of Lemma 11.1 and Z_n. Connectedness of the smaller W is not asserted or required. The later intermediate proof passages remain separately pending.

### S11-013: Positive real part bounded away from zero, analytic nonvanishing xi, its asymptotics and free value one.

- The real part of F_n is positive and has a common positive lower bound for every signed index and every source in one neighborhood of each point of W. The local-data proof divides the bound for Re(4F_n) by four.
- The positive bound is proved using norm continuity of one finite-exponent sequence realization: a distant tail stays close to one and a finite central block retains a positive minimum. Real collapsed-gap positivity uses reality, continuity and nonvanishing on the connected real-type locus, anchored at the free value 1/4.
- The root is the principal complex square root xi_n=sqrt(4F_n). Positive real part places its argument in the analytic slit-plane domain. Its exact square is 4F_n, so positivity implies nonvanishing; on real sources it is the positive real square root.
- Each root is complex analytic on the same W, hence real analytic. The local uniform package gives xi_n=1+GR_n+BR_n with the same fixed-sequence and common-neighborhood quantifiers as the action expansion.
- At the zero source the proved factor is F_n=1/4 and the principal root is exactly one for every signed index, including n=0.

Public declarations:

- `NLS.ZakharovShabat.SourceNormalizedActionUniformBounds.asymptotics`
- `NLS.ZakharovShabat.SourceNormalizedActionUniformBounds.positive`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.re_pos`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.real_analytic`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_analytic`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_ne_zero`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_real_positive`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_sq`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_zero`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedActionRootDeviation_allExponents`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedActionRoot_allIndices_analytic`
- `NLS.ZakharovShabat.sourceNormalizedActionComplexExtension_re_pos_of_realType`
- `NLS.ZakharovShabat.sourceNormalizedActionComplexExtension_zero_source`
- `NLS.ZakharovShabat.sourceNormalizedActionRoot`

The positivity, principal branch, real analyticity, nonvanishing, locally uniform root expansion and free value all match the printed statement. Uniform means local in the source but simultaneous in all indices. No additional source correction or refutation is introduced; subsequent proof displays retain their separate pending statuses.

The [full theorem](../NLS/ZakharovShabat/SourceTheorem11_2.lean) assembles the
[local uniform data](../NLS/ZakharovShabat/SourceNormalizedIndexedActionLocal.lean),
[literal sequence decomposition](../NLS/ZakharovShabat/SourceNormalizedActionOnePlusDecomposition.lean)
and [analytic principal roots](../NLS/ZakharovShabat/SourceNormalizedActionRootAnalytic.lean).
The comparison records 33 inspected module bodies and 24 resolved declarations.

This step changes documentation and comparison records only. The Lean sources
and dependency locks match the fully validated snapshot at `d3b3ff7`:
8,518 build jobs, 7,587 public examples and 44,364 transitively audited NLS
declarations, with 21 inherited warnings. Source-review integrity and
documentation-link checks pass for the new records.

The following subsection compares equation (2.18) and its recentered action integral.

## Equation (2.18) and the recentered action integral

### S11-014: Equation (2.18): selected-root factorization, literal deleted product chi and its fixed joint domain.

- The function chi_n is the literal unordered product of (critical_m-lambda)/w_m(lambda) over exactly the signed indices m!=n. Absolute summability of the individual factor errors identifies it with the existing analytic quotient, including at coinciding numerator roots and numerator zeros.
- The actual discriminant-derivative/canonical-root quotient equals -i times (critical_n-lambda)/w_n(lambda) times chi_n. The proof separates entire numerator and canonical-root products and divides only by nonzero standard-root denominators, retaining zeros of the selected critical numerator.
- The full critical displacement is an analytic ell-p-valued map on the original W0. Substitution into the jointly analytic quotient of Corollary 10.6 proves joint analyticity of chi_n on the complement of all other moving gaps, without shrinking W0.
- The rendered sentence has closure(U_n) under the union over m!=n. The corrected fixed domain uses the other closed disks closure(U_m). The existing positive fixed-domain theorem proves this for every original isolating family on V contained in W0, and the selected-disk theorem proves joint analyticity on U_n times V.
- The domain-index correction is the existing SOURCE_ERRATA.md entry. The factorization, literal product, exact -i normalization, original source neighborhood and original disks are retained.

Public declarations:

- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_disk`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_fixed`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_joint`
- `NLS.ZakharovShabat.SourceEquation2_18Data.disk`
- `NLS.ZakharovShabat.SourceEquation2_18Data.factorization`
- `NLS.ZakharovShabat.SourceEquation2_18Data.fixed`
- `NLS.ZakharovShabat.SourceEquation2_18Data.joint`
- `NLS.ZakharovShabat.SourceLemma11_1Data.actionChi`
- `NLS.ZakharovShabat.SourceSimpleSpectralDomainData.criticalDisplacement_analytic`
- `NLS.ZakharovShabat.hasProd_sourceSingleRootQuotient_subtype`
- `NLS.ZakharovShabat.sourceActionChi`
- `NLS.ZakharovShabat.sourceActionChi_eq_quotient`
- `NLS.ZakharovShabat.sourceCriticalRootRatioExtension_eq_neg_I_chi`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_eq_selectedFactor_mul_chi`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_eq_selectedFactor_mul_extension`
- `NLS.ZakharovShabat.sourceEquation2_18`

Corrected occurrence: replace the fixed subscript n inside the union over m!=n by m. The product and factorization match as printed. The existing positive proofs supply the corrected fixed domain and the stronger moving-gap domain, including the selected disk. This comparison adds no refutation and leaves the historical erratum unchanged.

### S11-015: Recentered action integral with coefficient i/pi and the squared critical factor.

- The actual indexed action equals i/pi times the integral of (critical_n-lambda)^2/w_n(lambda) times the literal chi_n. The coefficient, squared numerator, standard-root branch and contour orientation match the printed display.
- The identity holds for every finite piecewise C1 circuit contained in an original isolating disk minus its selected gap, with winding one about the actual midpoint. It uses the original complex source domain and every signed index, including complex collapsed gaps.
- The unweighted discriminant-derivative/canonical-root integral vanishes on every such closed contour. A zero period propagates from a real-source germ throughout the connected original domain; the resulting primitive on the full original cut disk supplies the contour statement.
- Subtracting the actual critical point from the spectral weight therefore leaves the action unchanged. Equation (2.18) then changes (lambda-critical_n) times the quotient into i times the squared critical numerator divided by w_n and multiplied by chi_n. Linearity and contour congruence complete the literal integral identity.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_16Data.circuit`
- `NLS.ZakharovShabat.SourceEquation2_18Data.circuit`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.indexedAction_eq_circuit`
- `NLS.ZakharovShabat.SourceLemma10_11CircleData.originalDisk_loopIntegral_zero`
- `NLS.ZakharovShabat.SourceLemma11_1Data.action_eq_chi_circuit`
- `NLS.ComplexAnalysis.PiecewiseC1Loop.integral_congr`

The recentered contour formula matches on the unchanged original domain, with its exact i/pi constant. Winding-one finite piecewise C1 regularity is explicit; no real-source or open-gap restriction is imposed. The later gap parametrization and equation (2.19) remain separately pending.

The [literal product](../NLS/ZakharovShabat/SourceActionChi.lean),
[contour proof](../NLS/ZakharovShabat/SourceActionChiContour.lean) and
[common-domain package](../NLS/ZakharovShabat/SourceEquation2_18.lean)
supply these assertions. The [existing domain-index erratum](../SOURCE_ERRATA.md#equation-218-the-omitted-disk-domain-uses-the-union-index)
is retained. The comparison records 16 inspected module bodies and 22 resolved declarations.

This step changes documentation and comparison records only. The exact Lean
sources and dependency locks match the full validation at `d3b3ff7`:
8,518 build jobs, 7,587 public examples and 44,364 transitively audited NLS
declarations, with 21 inherited warnings. Source-review integrity and
documentation-link checks pass for the new records.

The following subsection compares the complex gap integral and equation (2.19).

## Complex gap integral and equation (2.19)

### S11-016: Complex gap-side parametrization and the actual weighted integral for the action.

- With tau_n the actual midpoint and delta_n=gamma_n/2, lambda_t=tau_n+delta_n*t. The literal unnormalized identity is I_n=(2/pi) times the integral from -1 to 1 of (critical_n-tau_n-delta_n*t)^2*chi_n(lambda_t)/sqrt(1-t^2).
- The literal complex gap side values are minus/plus i times half-gap times the positive real square root of 1-t^2. The side convention is the sign of Im((z-midpoint)/halfGap); arbitrary within-side approaches include both endpoints and the midpoint.
- The generic Joukowski ellipse period theorem proves actual contour contraction for arbitrary complex midpoint and nonzero half-gap in any prescribed open gap neighborhood. One R>1 works for every 1<r<=R. Its exact Jacobian/root is -2*pi*i, the annulus proof makes averages independent of r, and compact uniform convergence identifies the limiting cosine gap average.
- For the printed action passage, take U to be the original selected disk and f(z)=(critical-z)^2*chi(z). Joint chi analyticity restricted to that disk gives the analytic numerator, the actual source ellipses have winding one, and SourceEquation2_18Data.circuit identifies each ellipse integral with the actual action. This explicitly supports shrinking independently of analytic continuation of the final weighted formula.
- SourceActionChiCosine proves the actual action formula on the original connected W0 using an analytic symmetric cosine mean and real-form uniqueness. Its real-source agreement, including the collapsed case, and the exact chi=i*oldExtension conversion have been compared. The mean needs analytic midpoint and squared gap, without analytic ordered endpoints.
- ComplexArcsineIntegral proves the literal arccos substitution and endpoint integrability for continuous numerators. The resulting actual weighted-gap formula has coefficient 2/pi; no real-source restriction or domain shrink is imposed, and the unnormalized identity also holds at collapsed gaps.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_18Data.action_eq_chiCosineMean`
- `NLS.ZakharovShabat.SourceEquation2_18Data.action_eq_chiCosineMean_real`
- `NLS.ZakharovShabat.SourceEquation2_18Data.action_eq_chi_gapIntegral`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chiCosineMean_analytic`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chi_gap_continuous`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chi_gap_weighted_integrable`
- `NLS.ZakharovShabat.SourceEquation2_18Data.circuit`
- `NLS.ZakharovShabat.SourceEquation2_18Data.disk`
- `NLS.ZakharovShabat.SourceEquation2_18Data.joint`
- `NLS.ZakharovShabat.exists_local_eqOn_of_eqOn_realType`
- `NLS.ZakharovShabat.exists_standardRootEllipse_local_period`
- `NLS.ZakharovShabat.sourceStandardRootEllipseLoop_winding`
- `NLS.ZakharovShabat.sourceStandardRoot_eq_normalized_halfGap`
- `NLS.ZakharovShabat.sourceStandardRoot_tendsto_gap_lower_side`
- `NLS.ZakharovShabat.sourceStandardRoot_tendsto_gap_upper_side`
- `NLS.ZakharovShabat.standardRootEllipseLoop_weighted_integral`
- `NLS.ZakharovShabat.standardRootEllipseMap_deriv_div_root`
- `NLS.ZakharovShabat.standardRootEllipse_average_tendsto`
- `NLS.ComplexAnalysis.integral_div_sqrt_one_sub_sq_eq_cosine`
- `NLS.ComplexAnalysis.intervalIntegrable_div_sqrt_one_sub_sq`

Matched for every signed index and complex source in the original domain. The direct ellipse contraction is instantiated in the original disk using the preceding circuit formula; the final weighted identity also has its own analytic-continuation proof. No new constant correction or refutation is needed.

### S11-017: Equation (2.19): normalized-action formula and the critical-to-midpoint coordinate t_n.

- The coordinate is literally t_n=(critical_n-tau_n)/(gamma_n/2). Lemma 10.10 gives t_n=2*gamma_n*B_n with the actual critical-offset coefficient, also in the totalized collapsed case.
- Off the actual zero-gap locus, equation (2.19) is 4*I_n/gamma_n^2=(2/pi) times the integral from -1 to 1 of (t_n-t)^2*chi_n(tau_n+gamma_n*t/2)/sqrt(1-t^2). Dividing the preceding formula by the nonzero half-gap squared gives the exact factor four.
- The normalized integrand is genuinely interval integrable by continuity of its numerator and integrability of the arcsine weight. The original complex domain is unchanged. The filled quotient and its analytic extension at zero gaps are separate assertions.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_18Data.actionCriticalCoordinate_eq_gap_mul`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chi_gap_weighted_integrable`
- `NLS.ZakharovShabat.SourceEquation2_18Data.normalizedAction_eq_chi_gapIntegral`
- `NLS.ZakharovShabat.sourceActionCriticalCoordinate`

Matched with the exact factor four, coefficient 2/pi and denominator gamma_n/2 in t_n. S11-018 and S11-019 retain the pending collapsed-limit and analytic-removal comparisons.

The [complex boundary values](../NLS/ZakharovShabat/SourceStandardRootGapSideSourceJoint.lean),
[ellipse contraction](../NLS/ZakharovShabat/SourceStandardRootEllipsePeriod.lean),
[actual winding](../NLS/ZakharovShabat/SourceStandardRootLocalEllipses.lean),
[cosine representation](../NLS/ZakharovShabat/SourceActionChiCosine.lean) and
[weighted formulas](../NLS/ZakharovShabat/SourceActionChiGapIntegral.lean)
supply these assertions. The comparison records 22 inspected module bodies and 23 resolved declarations.

This step changes documentation and comparison records only. The exact Lean
sources and dependency locks match the full validation at `d3b3ff7`:
8,518 build jobs, 7,587 public examples and 44,364 transitively audited NLS
declarations, with 21 inherited warnings. Source-review integrity and
documentation-link checks pass for the new records.

The following subsection compares the collapsed limit and analytic extension.

## Collapsed normalized-action limit and analytic extension

### S11-018: Small-gap estimate t_n=O(gap) and the exact collapsed limit of 4I_n/gap^2.

- The exact t_n=2*gamma_n*B_n identity and Lemma 10.10 locally_uniform give one neighborhood V and K>0 with |t_n(psi)|<=2*K*|gamma_n(psi)| for every psi in V and every signed n, using the standard coordinate bound by the lp norm. This supplies the printed local O(gamma_n) statement, including the totalized zero value at collapse.
- The arccos substitution identifies the arcsine second moment with the cosine second moment. integral_shifted_cos_sq_complex at u=0 gives pi/2, hence the printed (2/pi) integral of t^2/sqrt(1-t^2) times the fixed midpoint value is exactly that midpoint value. Endpoint integrability is supplied separately.
- The filled indexed quotient is the literal I_n/gamma_n^2 off the zero-gap locus and chi_n(tau_n)/4 on it. The factor-four limit at each collapsed phi in W is chi_n(phi,tau_n(phi)) along arbitrary complex approaches in W outside the selected zero-gap set.
- The limit theorem follows from continuity of the independently constructed analytic circle extension. The printed scalar integral is separately evaluated by the verified arcsine substitution and second moment.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_18Data.actionCriticalCoordinate_eq_gap_mul`
- `NLS.ZakharovShabat.SourceEquation2_18Data.normalizedAction_tendsto_collapsed`
- `NLS.ZakharovShabat.SourceLemma10_10Data.locally_uniform`
- `NLS.ZakharovShabat.integral_shifted_cos_sq_complex`
- `NLS.ComplexAnalysis.integral_div_sqrt_one_sub_sq_eq_cosine`
- `NLS.ComplexAnalysis.intervalIntegrable_div_sqrt_one_sub_sq`

Matched with the exact factor four and midpoint value. The local small-gap estimate follows with constant 2*K from the actual locally bounded lp coefficient. The limit is taken at a collapsed source within the original W, with approaches outside the actual zero-gap locus.

### S11-019: Continuous removal across Z_n, analytic collapsed value and analytic extension.

- The filled indexed quotient is the literal I_n/gamma_n^2 off the zero-gap locus and chi_n(tau_n)/4 on it. The factor-four limit at each collapsed phi in W is chi_n(phi,tau_n(phi)) along arbitrary complex approaches in W outside the selected zero-gap set.
- The rationalized kernel K=(d/(4*(d+w))+2*d*B+q*B^2)/w, with d=tau-z and q=gamma^2, divides only by spectral denominators. The root and d+w are nonzero on the original local contours, including at collapse. Analytic midpoint, squared gap, B and deleted extension give joint analyticity over the full original W.
- The algebraic recentered-integrand identity splits off a holomorphic term and factors the actual action through q times the circle candidate. At q=0, K=-(1/8)/(z-tau)+2*B; Cauchy gives candidate i*E(tau)/4=chi(tau)/4 since E=-i*chi. This proves exact agreement of the filled function with each original local circle candidate without gap division at zero.
- The jointly analytic parameter-integral theorem gives Banach analyticity of each candidate on its full local source neighborhood. At every point of original W the preceding contour package supplies such a neighborhood, so agreement proves analyticity of the filled quotient on W. Continuity then yields the collapsed limit; the proof does not use the limit to establish the kernel.
- The analytic midpoint and joint chi map compose to prove analytic chi_n(tau_n) on the same W. This constructive contour proof supplies the source removal conclusion without invoking the uninspected cited book theorem A.6. The later uniform sequence estimates and principal-root closure are still pending.

Public declarations:

- `NLS.ZakharovShabat.SourceActionContourFamily.analytic_normalizedActionCircleCandidate`
- `NLS.ZakharovShabat.SourceActionContourFamily.normalizedIndexedAction_eq_circleCandidate`
- `NLS.ZakharovShabat.SourceEquation2_18Data.criticalRatioExtension_joint`
- `NLS.ZakharovShabat.SourceEquation2_18Data.indexedAction_eq_gap_sq_mul_normalized`
- `NLS.ZakharovShabat.SourceEquation2_18Data.normalizedIndexedAction_analytic`
- `NLS.ZakharovShabat.SourceEquation2_18Data.normalizedKernel_joint`
- `NLS.ZakharovShabat.SourceEquation2_19Data.midpointChi_analytic`
- `NLS.ZakharovShabat.normalizedActionCircleKernel_identity`
- `NLS.ZakharovShabat.normalizedActionCircleKernel_zeroGap`
- `NLS.ZakharovShabat.normalizedActionCircleQuotient_zeroGap`
- `NLS.ZakharovShabat.normalizedActionCircle_integral_factor`
- `NLS.ZakharovShabat.normalizedStandardRoot_add_ne_zero`
- `NLS.ZakharovShabat.sourceActionCircle_eq_squaredGap_mul_kernel`
- `NLS.ZakharovShabat.sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero`
- `NLS.ZakharovShabat.sourceNormalizedIndexedAction`
- `NLS.ZakharovShabat.sourceNormalizedIndexedAction_eq_collapsed`
- `NLS.ZakharovShabat.sourceNormalizedIndexedAction_eq_quotient`
- `NLS.ComplexAnalysis.analyticOnNhd_circleIntegral_of_jointAnalytic`

Matched on the original common domain, including non-real collapsed gaps and every signed index. The extension fills I_n/gamma_n^2 by chi_n(tau_n)/4 and is both continuous and analytic there. The constructive rationalized-contour proof replaces the source citation to Theorem A.6; this does not certify that cited external theorem or the wider 2014 construction.

The [original-domain kernel](../NLS/ZakharovShabat/SourceNormalizedActionCommonKernel.lean),
[collapsed circle value](../NLS/ZakharovShabat/SourceNormalizedActionCollapsedCircleValue.lean),
[filled indexed quotient](../NLS/ZakharovShabat/SourceNormalizedIndexedActionCommon.lean) and
[equation (2.19) package](../NLS/ZakharovShabat/SourceEquation2_19.lean)
supply these assertions. The comparison records 12 inspected module bodies and 24 resolved declarations.

This step changes documentation and comparison records only. The exact Lean
sources and dependency locks match the full validation at `d3b3ff7`:
8,518 build jobs, 7,587 public examples and 44,364 transitively audited NLS
declarations, with 21 inherited warnings. Source-review integrity and
documentation-link checks pass for the new records.

The following subsection compares the original-domain uniform estimates.

## Original-domain uniform gap and action estimates

### S11-020: Full-domain locally uniform literal gap-supremum estimate for chi_n minus one.

- The error epsilon_n is the literal supremum of |chi_n(lambda)-1| on the entire actual complex gap. Compactness and continuity make it finite and nonnegative. At a collapsed gap it equals |chi_n(tau_n)-1|, and at the free source it is zero.
- The actual critical-midpoint offset is gamma_n^2*B_n. It is an lp/2 coefficient with norm at most norm(B)*norm(gamma)^2. Local bounds for the actual B and gap sequences give an explicit stronger offset bound before choosing a refined exponent; this supplies the hypothesis needed by the corrected Lemma 10.8 estimates.
- The full critical displacement is analytic into lp on the original W. Pulling back one joint quotient-estimate neighborhood along its graph gives an open source neighborhood at each complex point of W. Every original isolating disk is retained; compact bounds fill the finite central block, and the same geometric data work for every refined exponent.
- For every finite r>1 with r>=p/2, the same neighborhood gives a bounded lr coefficient equal to the actual gap supremum at every signed index. Contractive inclusion of the bounded half-exponent offset supplies the majorant hypothesis. The literal chi/quotient equality and inclusion of the actual gap in its original disk transfer the all-disk pointwise bounds to the supremum.
- The refined bounds produce one pair of functions A into lp/2 and B into the genuine intersection l(1+), chosen before any projection exponent. When p/2>1, use the lr bound at r=p/2 for A and set B=0; when p/2<=1, set A=0 and use the actual sequence for B. Each finite r>1 projection of that same B is uniformly bounded on the same neighborhood.
- The previously recorded arbitrary-numerator topology correction is respected through the explicit locally bounded stronger critical offset. This specialization proves the printed gap-supremum claim on the original source topology; no additional correction or refutation is required.

Public declarations:

- `NLS.ZakharovShabat.SourceCorollary10_6Data.finiteClosedDiscBound`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.quotientDiscEstimates`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chiGapSup_bddAbove`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chiGapSup_decomposition`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chiGapSup_refined`
- `NLS.ZakharovShabat.SourceEquation2_18Data.chiGapSup_refined_on`
- `NLS.ZakharovShabat.SourceEquation2_18Data.norm_chi_sub_one_le_gapSup`
- `NLS.ZakharovShabat.SourceQuotientDiscEstimates.fillHead`
- `NLS.ZakharovShabat.SourceQuotientDiscEstimates.majorants`
- `NLS.ZakharovShabat.SourceSimpleSpectralDomainData.criticalDisplacement_analytic`
- `NLS.ZakharovShabat.norm_sourceCriticalHalfGapOffset_le`
- `NLS.ZakharovShabat.sourceActionChiGapSup`
- `NLS.ZakharovShabat.sourceActionChiGapSup_of_gap_zero`
- `NLS.ZakharovShabat.sourceActionChiGapSup_zero_source`
- `NLS.ZakharovShabat.sourceCriticalHalfGapOffset`
- `NLS.Coeff.norm_quasiExponentInclusion_le`
- `NLS.Coeff.exists_onePlus_decomposition_of_refined`

Matched with the literal gap supremum and original source topology. The stronger actual critical offset supplies the bounded-offset hypothesis required by the existing Lemma 10.8 correction. The neighborhood is chosen before all signed indices and refined exponents, and one genuine one-plus summand works for every finite projection.

### S11-021: Locally uniform t_n estimate and normalized-action expansion from weighted moments.

- The literal coordinate t_n=2*gamma_n*B_n is an actual lp/2 coefficient, with norm at most 2*norm(gamma)*norm(B). The scalar Holder estimate and bounded multipliers remain valid for 1<p<2, with their positive half-exponent quasi-norms. The bound is locally uniform on the original W.
- The filled indexed quotient has the exact cosine model at every complex source, including collapsed gaps where t_n=0. Its principal moment is 1+2*t_n^2. The complementary error is at most 2*(|t_n|+1)^2*epsilon_n.
- Consequently |4*F_n-1| is at most 8*|gamma_n|^2*|B_n|^2+2*(2*|gamma_n|*|B_n|+1)^2*epsilon_n. On a neighborhood where the lp norms of gamma and B are bounded by G and B0, this is dominated by 8*B0^2*|gamma_n|^2+L*epsilon_n, with L=2*(2*G*B0+1)^2.
- If the actual epsilon sequence has lr norm at most Q, the same neighborhood supplies an lr coefficient equal to 4*F_n-1 with norm at most L*Q+8*B0^2*G^2, for every finite r>1 with r>=p/2. The two-majorant theorem uses cutoff zero here, so it controls all signed indices and the exact sequence.
- One intersection of the source neighborhoods gives both supremum and action refined estimates. The final package then chooses four functions Gchi, GA into lp/2 and Bchi, BA into l(1+) before the index and one-plus exponent. Their exact sums are epsilon_n and 4*F_n-1; the half-exponent norms and each finite one-plus projection are uniformly bounded there.
- Off the zero-gap locus F_n is the literal I_n/gamma_n^2, proving the printed normalized-action expansion. The filled formula also covers complex collapse. The final real-locus positivity, locally uniform tail limit and principal-root claims in S11-022 remain separate; a uniform sequence-norm bound alone is not used to infer a uniform tail limit.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_18Data.criticalCoordinate_halfExponent`
- `NLS.ZakharovShabat.SourceEquation2_18Data.criticalCoordinate_locally_uniform`
- `NLS.ZakharovShabat.SourceEquation2_19Data.norm_normalized_sub_one_le`
- `NLS.ZakharovShabat.SourceEquation2_19Data.normalized_eq_cosineModel`
- `NLS.ZakharovShabat.SourceEquation2_19Data.normalized_refined_of_bounds`
- `NLS.ZakharovShabat.SourceEquation2_19Data.originalEstimates`
- `NLS.ZakharovShabat.SourceEquation2_19Data.uniform_refined`
- `NLS.ZakharovShabat.SourceSection11OriginalEstimates.locally_uniform`
- `NLS.ZakharovShabat.SourceSection11UniformAsymptotics`
- `NLS.ZakharovShabat.norm_normalizedActionCosineModel_sub_le`
- `NLS.ZakharovShabat.norm_sourceCriticalGapLinearOffset_le`
- `NLS.ZakharovShabat.norm_sourcePeriodicSquaredGapCoeff_le_sq`
- `NLS.ZakharovShabat.normalizedActionCosineModel_eq_one_add_error`
- `NLS.ZakharovShabat.normalizedActionCosineModel_one`
- `NLS.Coeff.norm_quasiHolderProduct_le`
- `NLS.Coeff.exists_tailCoeff_of_twoSequenceMajorants`
- `NLS.Coeff.exists_onePlus_decomposition_of_refined`

Matched on the original complex domain, including the half-exponent quasi-norm range. The normalized quotient has its exact factor four off zero gaps, and the filled model also covers collapse. Both decompositions use fixed summand functions and the same local neighborhood; S11-022 retains the separate positivity, uniform tail and principal-root comparison.

The [gap-supremum bounds](../NLS/ZakharovShabat/SourceActionChiUniform.lean),
[action bounds](../NLS/ZakharovShabat/SourceNormalizedIndexedActionUniform.lean),
[fixed one-plus decomposition](../NLS/SequenceSpaces/RefinedOnePlusDecomposition.lean) and
[common-domain package](../NLS/ZakharovShabat/SourceSection11OriginalEstimates.lean)
supply these assertions. The comparison records 25 inspected module bodies and 33 resolved declarations.

This step changes documentation and comparison records only. The exact Lean
sources and dependency locks match the full validation at `d3b3ff7`:
8,518 build jobs, 7,587 public examples and 44,364 transitively audited NLS
declarations, with 21 inherited warnings. Source-review integrity and
documentation-link checks pass for the new records.

Continue with S11-022: real-locus positivity, the locally uniform tail limit,
the collapsed square-root identity and the remaining common-neighborhood claims.
