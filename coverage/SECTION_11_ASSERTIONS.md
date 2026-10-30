# Section 11 ordered assertion comparison

The first three of 22 ordered Section 11 groups match: simultaneous common contours and collars, the actual action with coefficient 1/pi in equation (2.16), and joint analyticity with winding-one contour and isolating-family independence. A supplied local source neighborhood may shrink; the global W and original disks are retained. All signed indices and complex or collapsed gaps are included. Nineteen later groups remain pending in this ordered comparison. Section 10 retains 44 matched and eight corrected groups. Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, the exact cited 2014 construction, Appendix G.2 norm interpretation and the broader source inventory remain unresolved.

This inventory covers printed pp.61–62, using one-based newline positions in
the reviewed source extraction; form feeds do not add lines. The first three
groups have been compared to the statements and proofs identified below.
The remaining entries provide navigation for further semantic comparison.
Existing named-theorem audits retain their own scope; they do not automatically
settle every intermediate display or proof assertion in these pending entries.

All compared claims use the original finite-p source spaces with 1<p<infinity.
The common open connected W contains the entire real-type locus. Standard
finite piecewise C1 regularity is explicit when interpreting contour integrals.

| Group | Printed page | Source lines | Assertion | Status |
| --- | --- | --- | --- | --- |
| S11-001 | 61 | 4737–4741 | One source neighborhood with all original isolating disks, counterclockwise circuits and fixed open collars. | matched |
| S11-002 | 61 | 4743–4748 | Definition (2.16): the literal action integral with coefficient 1/pi and spectral weight lambda. | matched |
| S11-003 | 61 | 4750–4752 | Joint analyticity on each collar and independence of both circuit and original isolating family. | matched |
| S11-004 | 61 | 4754–4761 | Lemma 11.1: action analyticity on the entire common domain and exact gradient (2.17). | pending |
| S11-005 | 61 | 4762–4763 | Lemma 11.1: real nonnegativity and equivalence of zero action with a collapsed gap. | pending |
| S11-006 | 61 | 4766–4768 | Proof of action analyticity, the gradient formula and complex collapsed-gap vanishing. | pending |
| S11-007 | 61 | 4769–4782 | Real-source recentering at the critical point and the literal positive-root gap integral. | pending |
| S11-008 | 61 | 4782–4784 | Pointwise sign of the recentered integrand and strict positivity of its integral. | pending |
| S11-009 | 61 | 4786–4790 | Definition of Z_n as the squared-gap zero locus in the original common domain. | pending |
| S11-010 | 61 | 4795–4805 | Figure 2.6: simultaneous enclosing circuits and fixed open collars within the original disks. | pending |
| S11-011 | 62 | 4816–4822 | Analytic subvariety Z_n and the normalized-action extension problem. | pending |
| S11-012 | 62 | 4824–4832 | Theorem 11.2: one complex neighborhood and locally uniform p/2 plus 1+ normalized-action expansion. | pending |
| S11-013 | 62 | 4833–4842 | Positive real part bounded away from zero, analytic nonvanishing xi, its asymptotics and free value one. | pending |
| S11-014 | 62 | 4844–4853 | Equation (2.18): selected-root factorization, literal deleted product chi and its fixed joint domain. | pending |
| S11-015 | 62 | 4855–4859 | Recentered action integral with coefficient i/pi and the squared critical factor. | pending |
| S11-016 | 62 | 4860–4869 | Complex gap-side parametrization and the actual weighted integral for the action. | pending |
| S11-017 | 62 | 4870–4876 | Equation (2.19): normalized-action formula and the critical-to-midpoint coordinate t_n. | pending |
| S11-018 | 62 | 4878–4884 | Small-gap estimate t_n=O(gap) and the exact collapsed limit of 4I_n/gap^2. | pending |
| S11-019 | 62 | 4885–4889 | Continuous removal across Z_n, analytic collapsed value and analytic extension. | pending |
| S11-020 | 62 | 4890–4895 | Full-domain locally uniform literal gap-supremum estimate for chi_n minus one. | pending |
| S11-021 | 62 | 4897–4906 | Locally uniform t_n estimate and normalized-action expansion from weighted moments. | pending |
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

## Proof evidence and validation

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

This comparison changes documentation only. The exact Lean and dependency
snapshot is unchanged from commit `7692c09`; its successful full validation
is reused: 8,514 build jobs, 7,584 public examples and a transitive axiom
audit of 44,339 NLS declarations, with 21 inherited warnings. Current module
hashes, declaration references, review integrity and documentation links
have been checked. These checks do not certify source-wide completeness.

Continue with Lemma 11.1, beginning with action analyticity and the gradient
formula in S11-004. Preserve the [existing Section 11 audit](SECTION_11.md)
and all wider qualifications in the [completion assessment](COMPLETENESS.md).
Correct constants with proved valid replacements; additional refutations
are not required.
