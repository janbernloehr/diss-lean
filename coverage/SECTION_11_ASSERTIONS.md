# Section 11 ordered assertion comparison

The first six of 22 ordered Section 11 groups match: common contours and the action definition, the full assertions of Lemma 11.1, and its analyticity, gradient and complex collapsed-gap proof passage. The exact -1/pi Frechet formula holds for every original winding-one piecewise C1 circuit at every complex source in the retained W. Real nonnegativity and the exact zero-gap criterion follow from the actual arcosh integral proof. Sixteen later groups remain pending, beginning with the displayed real-gap calculation and the pointwise sign sentence. The direct differentiation proof replaces the cited Hilbert-extension route; the external citation is not independently audited. Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, the exact cited 2014 construction, Appendix G.2 norm interpretation and broader source inventory remain unresolved.

This inventory covers printed pp.61–62, using one-based newline positions in
the reviewed source extraction; form feeds do not add lines. The first six
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
| S11-004 | 61 | 4754–4761 | Lemma 11.1: action analyticity on the entire common domain and exact gradient (2.17). | matched |
| S11-005 | 61 | 4762–4763 | Lemma 11.1: real nonnegativity and equivalence of zero action with a collapsed gap. | matched |
| S11-006 | 61 | 4766–4768 | Proof of action analyticity, the gradient formula and complex collapsed-gap vanishing. | matched |
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
The new comparison records 24 fully inspected modules. The Lean and dependency
snapshot is unchanged from the successful full gate at `7692c09`, so that
validation is reused; current source-review integrity and documentation links pass.

Continue with the displayed real-gap calculation S11-007 and the pointwise
sign argument S11-008. The [historical critical-point correction](SECTION_11.md#the-critical-point-zero-in-the-proof-of-lemma-111)
is retained. No new refutation is needed.

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

This comparison changes documentation only. The exact Lean and dependency
snapshot is unchanged from commit `7692c09`; its successful full validation
is reused: 8,514 build jobs, 7,584 public examples and a transitive axiom
audit of 44,339 NLS declarations, with 21 inherited warnings. Current module
hashes, declaration references, review integrity and documentation links
have been checked. These checks do not certify source-wide completeness.

The opening comparison above is retained with its original evidence. Preserve the [existing Section 11 audit](SECTION_11.md)
and all wider qualifications in the [completion assessment](COMPLETENESS.md).
Correct constants with proved valid replacements; additional refutations
are not required.
