# Appendix F ordered assertion comparison

The ordered Appendix F comparison covers 31 groups on printed pp.131-134: 27 matched, three directly corrected and one contextual. No partial or pending mathematical group remains within this local comparison; all prerequisite proof steps have been published. It retains literal improper endpoint integrals, original isolating discs, unordered analytic branches, source neighborhoods, exact principal-root identities and the actual sequence limits. The finite-p tail estimate, full common-path coefficient and positive moving majorant are corrected directly. The indexed half-gap bound and final analytic conclusion retain their independent squared-gap and joint-primitive proofs; the printed root-identification and external extension-theorem routes are not claimed as those dependencies. Historical refutations and broader completeness qualifications remain unchanged; the local counts are not a dissertation completion percentage.

Source: printed pp.131–134, text lines 10764–11080. Line numbers count
newline characters and preserve form feeds. The rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| F-001 | 10766–10772 | Literal differential and endpoint average | matched |
| F-002 | 10774–10775 | Attribution and extension of the cited proof | contextual |
| F-003 | 10777–10780 | F.1(i): local half-gap bound at complex collapsed gaps | matched |
| F-004 | 10783–10785 | F.1(ii): one real-source neighborhood for every signed index | matched |
| F-005 | 10795–10801 | Differentiated quadratic discriminant identity | matched |
| F-006 | 10803–10813 | Deleted product, joint analyticity and exact zero set | matched |
| F-007 | 10814–10817 | Uniform product and derivative bounds near a collapsed gap | matched |
| F-008 | 10819–10826 | Half-gap boundary estimate and root-count argument | matched |
| F-009 | 10827–10836 | Distant quotient bound and uniform small-gap tail | corrected |
| F-010 | 10836–10844 | Finite-head intersection and real half-gap bound | matched |
| F-011 | 10847–10856 | F.2: analytic literal endpoint average | matched |
| F-012 | 10858–10861 | Analytic connecting integrals and change of boundary point | matched |
| F-013 | 10862–10866 | Analytic squared-gap zero set | matched |
| F-014 | 10866–10903 | Local analytic branches through complex noncollapsed endpoints | matched |
| F-015 | 10904–10907 | Admissible endpoint spokes on one neighborhood | matched |
| F-016 | 10908–10915 | Four-path decomposition and individual endpoint integrals | matched |
| F-017 | 10916–10930 | Literal deleted critical-root product and differential normalization | matched |
| F-018 | 10932–10941 | Affine quadratic factorization and square-root branch | matched |
| F-019 | 10943–10950 | Positive base-radicand lower bound | matched |
| F-020 | 10953–10965 | Uniform radicand control and analytic singular endpoint integral | matched |
| F-021 | 10966–10969 | Collapsed-gap formula and weak analyticity | matched |
| F-022 | 10970–10972 | Continuity reduction at the collapsed locus | matched |
| F-023 | 10982–10987 | Eventual half-gap estimate along collapsing sources | matched |
| F-024 | 10990–11001 | Uniform short endpoint-piece bound | matched |
| F-025 | 11002–11005 | Corrected full common-path coefficient in F.3 | corrected |
| F-026 | 11008–11020 | Common terminal point and rescaled path formula | matched |
| F-027 | 11023–11025 | Pointwise convergence of normalized root and numerator | matched |
| F-028 | 11027–11040 | Valid replacement for the moving square-root majorant | corrected |
| F-029 | 11043–11053 | Integrability and passage to the limit | matched |
| F-030 | 11056–11057 | Continuity and final analytic conclusion | matched |
| F-031 | 11060–11071 | F.3: analytic integrals between arbitrary spectral endpoints | matched |

## Compared passages

### F-001: Literal differential and endpoint average

- The differential is the actual discriminant derivative divided by the canonical root, and F is the literal half-sum of the two improper endpoint integrals.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianDifferential`
- `NLS.ZakharovShabat.sourceAbelianEndpointAverage`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.tendsto_endpointPolygonalIntegral`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_eq`
- `NLS.ZakharovShabat.sourceAbelianEndpointAverage_zero`

Endpoint limits are proved along nontrivial approach filters. Free normalization is -i*nu+i*pi*n for every signed index.

### F-002: Attribution and extension of the cited proof

- The source attributes the approach to reference [59] and extends it beyond index zero and exponent two.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaF1`
- `NLS.ZakharovShabat.sourceLemmaF2`
- `NLS.ZakharovShabat.sourceCorollaryF3`

The attribution is contextual; no fresh comparison with the cited external edition is claimed.

### F-003: F.1(i): local half-gap bound at complex collapsed gaps

- Every complex collapsed gap in a constructed connected almost-real domain has a neighborhood with the critical-midpoint offset at most half the gap norm.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaF1`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.sourceLemmaF1_i`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.exists_collapsedGap_bound`

The exact squared-gap identity supplies an alternative proof. No real-type assumption is imposed on the collapsed base point.

### F-004: F.1(ii): one real-source neighborhood for every signed index

- At every real source, one complex neighborhood controls the critical offset by the gap norm for all signed indices.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaF1`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.sourceLemmaF1_ii`

The neighborhood precedes every index; the finite head and infinite tail are combined explicitly.

### F-005: Differentiated quadratic discriminant identity

- The literal deleted periodic product gives the quadratic discriminant factorization and its differentiated identity at the indexed critical root.

Public declarations:

- `NLS.ZakharovShabat.canonicalDiscriminant_sq_sub_four_eq_midpoint_mul`
- `NLS.ZakharovShabat.discriminant_critical_midpoint_identity`
- `NLS.ZakharovShabat.canonicalCriticalPoints_midpoint_offset_identity`

The canonical factorization uses -4. Reversing the sign of the midpoint offset gives the displayed zero identity; it never divides by the gap.

### F-006: Deleted product, joint analyticity and exact zero set

- The literal deleted symmetric cutoffs converge locally uniformly in the spectral variable, retaining the omitted normalization. The product is entire and nonzero on the omitted-root domain, including the selected gap.
- The literal deleted periodic-pair product and its spectral derivative are jointly analytic on all C times the unchanged source domain W.
- Its zeros are precisely the actual endpoints indexed by m different from the deleted n.

Public declarations:

- `NLS.ZakharovShabat.deletedSpectralPairPartialProduct`
- `NLS.ZakharovShabat.tendstoLocallyUniformlyOn_deletedSpectralPairProduct`
- `NLS.ZakharovShabat.analyticOnNhd_canonicalDeletedPeriodicProduct`
- `NLS.ZakharovShabat.canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain`
- `NLS.ZakharovShabat.SourceLemma10_5Data.deletedPair_joint_full`
- `NLS.ZakharovShabat.SourceLemma10_5Data.deletedPair_derivative_joint_full`
- `NLS.ZakharovShabat.SourceLemma10_5Data.deletedPair_eq_zero_iff`

The proof combines the omitted-root square with the exact discriminant quotient, using the original common-domain isolation; it retains the deleted normalization and does not assume continuity of the endpoint labels. The six positive helpers are published.

### F-007: Uniform product and derivative bounds near a collapsed gap

- The independent squared-gap quotient argument gives the required collapsed-gap bound.
- The closure of each original isolating disc avoids every other gap.
- Compactness supplies one source neighborhood with a positive lower bound for the product and a positive upper bound for its spectral derivative on the whole closed disc.
- At a collapsed complex source a further source restriction retains both bounds and gives norm(gap)*r <= s.

Public declarations:

- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.exists_collapsedGap_bound`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.quotient_analytic`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.closedDisk_subset_omittedDomain`
- `NLS.ZakharovShabat.SourceLemma10_5Data.deletedPair_uniform_disk_bounds`
- `NLS.ZakharovShabat.SourceLemma10_5Data.deletedPair_collapsed_disk_bounds`

The original spectral disc and common source domain are retained; only the local source neighborhood is restricted. Gap-norm continuity follows from analytic squared gaps, with no endpoint-label continuity assumption. The six positive helpers are published.

### F-008: Half-gap boundary estimate and root-count argument

- On the half-gap circle, the scalar quadratic remainder is at most norm(gap)^2*r/2 and is strictly below s*norm(gap) under the stated smallness condition.
- The differentiated quadratic factorization retains the exact normalization. The strict boundary estimate and Rouche theorem give one zero counted with analytic multiplicity.
- Near a collapsed actual source, continuity places nearby half-gap discs inside the original isolating disc; the actual deleted-product bounds prove the literal differentiated-discriminant count.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_quadratic_boundary_estimate`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.sourceLemmaF1_i`
- `NLS.ComplexAnalysis.appendixF_quadratic_derivative`
- `NLS.ComplexAnalysis.appendixF_half_gap_zero_count`
- `NLS.ZakharovShabat.SourceLemma10_5Data.appendixF_local_half_gap_zero_count`

The literal derivative of Delta squared minus four divided by four has one analytic zero in the half-gap disc. The indexed critical-point half-gap conclusion retains its independent squared-gap proof; the complete printed root-identification route is not claimed as its dependency.

### F-009: Distant quotient bound and uniform small-gap tail

- Use the proved finite-p quotient norm bound and one uniformly small gap tail to obtain any prescribed positive linear gap constant at all distant indices.

Public declarations:

- `NLS.ZakharovShabat.exists_local_uniform_sourceCriticalGapQuotient`
- `NLS.ZakharovShabat.exists_local_sourceCriticalOffset_small_gap_tail`

This directly replaces the displayed square-sum estimate in the proof of F.1(ii), whose base source is real. No refutation of the printed exponent is added, and no unproved arbitrary-complex-base norm bound is claimed.

### F-010: Finite-head intersection and real half-gap bound

- Real interlacing gives the half-gap estimate. Continuity at open head gaps and the collapsed-gap estimate combine over the finite head.

Public declarations:

- `NLS.ZakharovShabat.norm_sourceCriticalPoint_sub_midpoint_le_halfGap_of_realType`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.sourceLemmaF1_ii`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.analyticAt_offset`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.continuousAt_gap_norm`

Only finitely many head neighborhoods are intersected; the uniform tail is obtained separately.

### F-011: F.2: analytic literal endpoint average

- On a constructed connected almost-real domain, every complex base point has one source neighborhood and isolating family for all signed indices and all boundary points. The literal endpoint average is analytic there.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaF2`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.sourceLemmaF2`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_eq`

The proof identifies genuine endpoint integrals with the constructed joint primitive and includes collapsed gaps. It does not assume continuity of lexicographic endpoint labels.

### F-012: Analytic connecting integrals and change of boundary point

- The actual polygonal connecting integral is the difference of endpoint averages and is analytic for every pair of boundary points on the same source ball.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.polygonalIntegral_eq_endpointAverage_sub`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_eq_add_polygonalIntegral`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.boundaryPolygonalIntegral_analytic`

Changing the boundary point retains the full coefficient of the connecting path.

### F-013: Analytic squared-gap zero set

- The squared gap is analytic on one open connected almost-real source domain, so its zero locus is the zero set of an analytic scalar function.

Public declarations:

- `NLS.ZakharovShabat.exists_global_source_analytic_midpoint_squaredGap`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.squaredGap_analytic`

The current comparison uses the analytic scalar defining function; it does not introduce a separate analytic-subvariety data structure.

### F-014: Local analytic branches through complex noncollapsed endpoints

- At every distinct complex canonical pair, there are two local analytic branches through the prescribed base values, with the actual unordered pair and any positive tolerance.

Public declarations:

- `NLS.ComplexAnalysis.exists_local_analytic_pair_branches`
- `NLS.ZakharovShabat.exists_appendixFOpenGapBranches`

This proves the branch selection without continuous original labels. The source quarter-distance tolerance is obtained once its positive margin is supplied; geometric boundary selection is kept in the following group.

### F-015: Admissible endpoint spokes on one neighborhood

- Opposite real projections separate the straight spoke from the selected gap. Explicit quarter-gap and quarter-spoke tolerances keep the spoke in the original closed disc when both endpoints belong to it.
- Both original boundary rays and analytic unordered branches are constructed on one source neighborhood with the printed quarter-distance margins. Both punctured endpoint spokes avoid all source gaps.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_opposite_segments_avoid`
- `NLS.ComplexAnalysis.appendixF_perturbed_spoke_avoids_gap`
- `NLS.ComplexAnalysis.appendixF_perturbed_spoke_in_disc`
- `NLS.ComplexAnalysis.appendixF_exists_boundary_ray`
- `NLS.ZakharovShabat.SourceLemma10_2Data.appendixF_common_open_gap_spokes`

Both original boundary points, the positive distance margins and the common source neighborhood are constructed. Canonical endpoint labels need not be continuous.

### F-016: Four-path decomposition and individual endpoint integrals

- The four actual endpoint and connecting integrals add to twice the endpoint average, and each independently chosen endpoint-to-boundary integral is analytic.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_fourPath_split`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.selectedEndpointIntegral_analytic`

Endpoint choices require no regularity. The four-path identity uses the genuine polygonal endpoint integrals and retains both full connecting coefficients.

### F-017: Literal deleted critical-root product and differential normalization

- The literal product omits precisely n and is identified with the analytic deleted quotient without dividing by a selected critical factor.
- The actual critical displacement is an analytic map into the original ell-p space on the full retained domain, including at complex source points.
- Substitution gives joint spectral/source analyticity on the full omitted moving-gap domain and on the entire selected original disc times the unchanged local source neighborhood.
- The differential factorization retains exactly minus i times the selected critical-root ratio times the literal chi product.
- Corollary 10.6 supplies a connected open almost-real domain with the required data for every finite p greater than one.

Public declarations:

- `NLS.ZakharovShabat.sourceActionChi`
- `NLS.ZakharovShabat.sourceActionChi_eq_quotient`
- `NLS.ZakharovShabat.sourceCriticalRootRatioExtension_eq_neg_I_chi`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_eq_selectedFactor_mul_chi`
- `NLS.ZakharovShabat.SourceSimpleSpectralDomainData.criticalDisplacement_analytic`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_joint`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_fixed`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.chi_disk`
- `NLS.ZakharovShabat.sourceCorollary10_6`

The assertion uses SourceCorollary10_6Data on its retained W, its original V subset W and the original isolating family. The full Banach-space critical displacement is substituted into the joint quotient; no real-base exterior restriction replaces the complex-domain claim. Common bounds and improper-path limits are supplied in the later groups.

### F-018: Affine quadratic factorization and square-root branch

- The affine endpoint parameterization has the exact quadratic factorization in the source.
- The principal square root respects multiplication by any nonnegative real factor, including zero.
- The actual normalized root has the literal endpoint-spoke formula, including the initial endpoint.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_endpoint_segment_factorization`
- `NLS.ZakharovShabat.sourcePeriodicPair_factorization`
- `NLS.ComplexAnalysis.appendixF_sqrt_nonnegative_scale`
- `NLS.ZakharovShabat.appendixF_normalized_root_on_endpoint_spoke`

Nonnegative real scaling fixes the principal branch, yielding the displayed identity for the actual normalized standard root, including the initial endpoint.

### F-019: Positive base-radicand lower bound

- For positive sigma and t in [0,1], the displayed scalar radicand is at least sigma/(1/2+sigma), which is strictly positive.
- For nonzero complex gap and positive real outward displacement, the base radicand is exactly sigma*(1+t*sigma)/(1/2+t*sigma)^2.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_endpoint_radicand_lower`
- `NLS.ZakharovShabat.appendixF_endpoint_base_radicand`

The scalar inequality retains the printed constant. The exact complex-to-real identity supplies its use in the following whole-neighborhood branch argument.

### F-020: Uniform radicand control and analytic singular endpoint integral

- Individual endpoint-to-boundary integrals are analytic by their identification with the joint primitive. The positive scalar radicand lower bound is separately proved.
- Positive helpers give explicit uniform nearby-source radicand bounds, a jointly continuous and source-analytic nonzero principal-root factor, and the exact inverse-square-root substitution.
- The literal normalized-root endpoint integral is interval integrable and analytic under explicit branch and path-regularity hypotheses.
- The actual source supplies the standard root, chi and critical-point analyticity. The inverse-square-root parameter integral is identified with the literal improper endpoint integral, retaining its full -i displacement coefficient.
- Both actual endpoint integrals are analytic on a single source neighborhood, with branches, path admissibility and integrability constructed from explicit source data.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_endpoint_radicand_lower`
- `NLS.ComplexAnalysis.appendixF_inverse_sqrt_integral_analytic`
- `NLS.ComplexAnalysis.appendixF_inverse_sqrt_intervalIntegrable`
- `NLS.ComplexAnalysis.appendixF_inverse_sqrt_substitution`
- `NLS.ComplexAnalysis.appendixF_local_uniform_lower_bound`
- `NLS.ComplexAnalysis.appendixF_sqrt_norm_lower`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.selectedEndpointIntegral_analytic`
- `NLS.ZakharovShabat.appendixF_endpoint_integral_analytic`
- `NLS.ZakharovShabat.appendixF_endpoint_integrand_weight`
- `NLS.ZakharovShabat.appendixF_endpoint_uniform_branches`
- `NLS.ZakharovShabat.appendixF_endpoint_uniform_radicand`
- `NLS.ZakharovShabat.appendixF_source_root_eq_of_endpoint_pair`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_endpoint_parameter_identity`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_source_endpoint_integral_analytic`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_open_endpoint_integrals_analytic`

The final source-assembly theorem retains explicit Section 10, isolating-family and local Cauchy-family data. Branch selection, admissibility, integrability and regular-factor analyticity are derived. The identification with the literal improper integral uses the independent primitive and its genuine endpoint limit.

### F-021: Collapsed-gap formula and weak analyticity

- At a collapsed gap the filled primitive derivative is -i times the literal chi product throughout the whole omitted-gap domain.
- Every admissible C1 path in the original closed isolating disc computes the actual endpoint average, including paths through the collapsed point and the exact segment displacement coefficient.
- The regular chi integral is Banach analytic on the original source neighborhood. A constructed source-chart cover identifies its collapsed restriction with the actual endpoint average.
- The chart construction gives a connected neighborhood of the real locus inside the Section 10 domain. One local source neighborhood and its original isolating family support the collapsed analytic extensions for every index and boundary point.

Public declarations:

- `NLS.ZakharovShabat.exists_global_sourceCriticalRootRatio_analytic_of_zeroGap`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.fullPrimitive_collapsed_endpoint_value`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_collapsed_differential`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_primitive_hasDerivAt`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_endpoint_path`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_average_path`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_average_segment`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_regular_chi_integral_analytic`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_average_analytic_extension`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_derivative_omitted`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_original_path`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_collapsed_original_segment`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.appendixF_original_chi_integral_analytic`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_original_collapsed_analytic_extension`
- `NLS.ZakharovShabat.exists_appendixF_source_chart_cover`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_local_collapsed_analytic_extensions`
- `NLS.ZakharovShabat.exists_appendixF_collapsed_analytic_extensions`

Only the local source neighborhood is restricted. The original isolating discs are retained, and the auxiliary Cauchy chart need not contain those spectral discs. The final existence theorem constructs both the Section 10 data and chart cover.

### F-022: Continuity reduction at the collapsed locus

- The corrected midpoint identity, derived integral convergence and vanishing short piece prove convergence of actual improper endpoint averages for open-gap source sequences at a common boundary point.
- Analyticity of the actual connecting integral transfers the limit to any fixed original boundary point.
- A subsequence argument handles arbitrary mixtures of collapsed and open gaps; the sequence criterion proves continuity at the collapsed source.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_analytic`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_exists_endpointAverage_limit`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_mixed_endpointAverage_limit`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_endpointAverage_continuousAt_collapsed`

The source-specific sequence argument is proved. Fixed-boundary transport uses the actual connecting integral identified directly with a difference of independent joint-primitive values; it does not assume endpoint-average continuity.

### F-023: Eventual half-gap estimate along collapsing sources

- At each complex collapsed gap, any sequence converging to the base point is eventually in a neighborhood carrying the half-gap estimate.
- Published source proofs derive gap convergence directly from squared-gap analyticity and the local half-gap bound from the unchanged Lemma 10.10 data, without continuous endpoint labels.

Public declarations:

- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.sourceLemmaF1_i`
- `NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain.exists_collapsedGap_bound`
- `NLS.ZakharovShabat.SourceLemma10_2Data.appendixF_gap_tendsto_zero`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_eventually_half_gap`

The published open-neighborhood statement is stronger than the displayed eventual estimate and does not divide by the vanishing gap.

### F-024: Uniform short endpoint-piece bound

- The pi*M estimate retains its explicit half-gap and regular-factor hypotheses. Independently, one local positive constant for the actual Cauchy boundary profile is derived at every complex point of the source ball. It controls all angles and both sides before those choices, and gives vanishing along collapsing gap norms.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_gapBoundary_norm_le_gap`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_gapBoundary_tendsto_zero`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_exists_local_uniform_gapBoundary_bound`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_gapBoundary_tendsto_zero_locally`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.fullPrimitive_tendsto_gapBoundary`

Uniformity is proved by compactness of the fixed inner disc and joint analyticity of the Cauchy quotient. This is for a fixed signed gap; it does not claim one constant over all indices.

### F-025: Corrected full common-path coefficient in F.3

- The literal endpoint average changes by the full connecting path integral. The common-path coefficient is 1/i=-i.
- The exact midpoint identity expresses the actual improper endpoint average as the full -i displacement integral plus its one-sided boundary value; that remainder tends to zero along collapsing source sequences.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_eq_add_polygonalIntegral`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_fourPath_split`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_product`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_integral_identity`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_remainder_tendsto_zero`

The coefficient is corrected directly. Historical refutations are preserved without extension.

### F-026: Common terminal point and rescaled path formula

- The selected cut closed disc lies inside the complement of every actual gap.
- For an arbitrary countable family of actual potentials in the original local source neighborhood, one original boundary point and all punctured midpoint spokes avoid every gap.
- The actual normalized root has the rescaled principal-root expression at positive midpoint-path parameters.
- For a countable family with open selected gaps, one original boundary point lies on a chosen side of each gap and every positive spoke is admissible.
- The improper endpoint identity gives the exact actual normalized-root midpoint integral and its short-piece remainder.
- The exact rescaling identifies the actual interval integral with the literal principal-root expression and gives the corrected improper endpoint identity with its short-piece term.

Public declarations:

- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.closedCutDisk_subset_rootDomain`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.exists_common_source_midpoint_spokes`
- `NLS.ZakharovShabat.appendixF_normalized_root_on_spoke`
- `NLS.ZakharovShabat.appendixF_midpoint_spoke_mem_side`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.appendixF_exists_common_sided_spokes`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_integral_identity`
- `NLS.ZakharovShabat.appendixF_spoke_quotient_eq_rescaled`
- `NLS.ZakharovShabat.appendixF_spoke_integral_eq_rescaled`
- `NLS.ZakharovShabat.appendixF_source_spoke_integral_eq_rescaled`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_rescaled_endpoint_identity`

Common original boundary geometry, pointwise principal-root rescaling and the exact integral identities are proved. The individual endpoint identity retains explicit admissibility, side and integrability hypotheses; the assembled sequence theorem derives them eventually.

### F-027: Pointwise convergence of normalized root and numerator

- At every positive parameter the actual source standard root converges to the linear collapsed root.
- The literal rescaled principal square root and numerator both converge to t, with the critical offset and gap limits derived from the common source data.
- Joint analyticity of chi_n on the original closed disc supplies the actual full integrand limit with coefficient -i times the moving displacement.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma10_2Data.appendixF_source_root_spoke_tendsto`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_source_rescaled_terms_tendsto`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_source_integrand_tendsto`

The published pointwise statements are restricted to t>0, sufficient for the almost-everywhere argument. The initial endpoint has measure zero. Source-family domination and integral substitution are tracked separately.

### F-028: Valid replacement for the moving square-root majorant

- The positive weight sqrt(t+norm(epsilon))/sqrt(abs(t-norm(epsilon))) bounds any complex square-root quotient off its one moving singular point when the numerator offset has norm at most norm(epsilon).

Public declarations:

- `NLS.ComplexAnalysis.appendixF_square_root_norm_lower`
- `NLS.ComplexAnalysis.appendixF_quotient_le_positive_majorant`
- `NLS.ComplexAnalysis.appendixF_positive_majorant_le`

The absolute lower distance corrects the weight on both sides of the moving point. No new proof that the printed version is wrong is added; the null singleton is excluded explicitly.

### F-029: Integrability and passage to the limit

- For 0 <= e <= 1 the corrected positive majorant is integrable on [0,1], and its L1 distance from one is at most 4*sqrt(2e). Its L1 distance therefore tends to zero when e tends to zero and this range holds eventually.
- The moving-majorant theorem and normalized-root specialization give integral convergence under common regular-factor bounds and measurability; eventual normalized-gap smallness is derived.
- The actual source supplies a common chi bound and measurability, one original boundary point and convergence of the full sequence of normalized-root integrals.
- The assembled midpoint identity derives eventual integrability and the vanishing short piece, proving convergence of actual improper endpoint averages at the common boundary point.
- The actual connecting polygonal integral is analytic on the original source neighborhood inside a Cauchy chart. Its limit transfers the argument to every fixed original boundary point.

Public declarations:

- `NLS.ComplexAnalysis.appendixF_inverse_sqrt_distance_interval`
- `NLS.ComplexAnalysis.appendixF_positive_majorant_integrable`
- `NLS.ComplexAnalysis.appendixF_positive_majorant_L1_bound`
- `NLS.ComplexAnalysis.appendixF_positive_majorant_tendsto_L1`
- `NLS.ComplexAnalysis.appendixF_tendsto_integral_moving_majorant`
- `NLS.ComplexAnalysis.appendixF_tendsto_intervalIntegral_positive_majorant`
- `NLS.ZakharovShabat.appendixF_collapsing_spoke_integral_tendsto_of_gap_zero`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.appendixF_chi_uniform_closedDisk_bound`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.appendixF_spoke_integrand_measurable`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_source_spoke_integral_tendsto_locally`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_exists_common_convergent_spokes`
- `NLS.ZakharovShabat.SourceCorollary10_6Data.appendixF_source_spoke_intervalIntegrable`
- `NLS.ZakharovShabat.SourceLemma10_10Data.appendixF_source_spoke_eventually_intervalIntegrable`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_integral_identity`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_midpoint_remainder_tendsto_zero`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_exists_endpointAverage_limit`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.appendixF_frontier_subset_rootDomain`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_original_boundary_integral_analytic`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.appendixF_fixed_endpointAverage_limit`

The majorant range is an eventual condition derived from gap convergence and nonzero limiting displacement. The connecting-integral proof uses the independent joint primitive directly without assuming endpoint-average continuity.

### F-030: Continuity and final analytic conclusion

- The actual endpoint average is analytic at every allowed complex source on the constructed common neighborhood.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaF2`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_analytic`

The analytic conclusion follows from the independent joint primitive. Continuity is also supplied by the explicit corrected source-sequence argument. The cited external extension theorem [23, A.6] is not separately formalized as this proof route.

### F-031: F.3: analytic integrals between arbitrary spectral endpoints

- The actual double improper integral between either endpoint of gap n and either endpoint of gap m equals i*pi*(n-m) and is analytic, including collapsed gaps and arbitrary pointwise endpoint choices.

Public declarations:

- `NLS.ZakharovShabat.sourceCorollaryF3`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.tendsto_endpointIntegral`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointToEndpointIntegral_eq`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointToEndpointCurveIntegral_eq`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointToEndpointIntegral_analytic`

Endpoint approaches are nontrivial and their limits are proved. Every integrable admissible C1 endpoint path agrees with the value.

## Evidence and validation

The [half-gap count](../NLS/ZakharovShabat/AppendixFHalfGapCount.lean)
retains the exact scalar estimate and actual source discs. The
[original-boundary spokes](../NLS/ZakharovShabat/AppendixFOpenGapSpokes.lean)
and [actual endpoint integrals](../NLS/ZakharovShabat/AppendixFSourceEndpointAnalytic.lean)
supply the open-gap construction. The
[original collapsed formulas](../NLS/ZakharovShabat/AppendixFOriginalCollapsed.lean)
and [source chart cover](../NLS/ZakharovShabat/AppendixFSourceChartCover.lean)
retain the original spectral discs and constructed neighborhoods. The
[midpoint identity](../NLS/ZakharovShabat/AppendixFMidpointIdentity.lean),
[rescaled integral](../NLS/ZakharovShabat/AppendixFRescaledIdentity.lean) and
[fixed-boundary limit](../NLS/ZakharovShabat/AppendixFFixedBoundary.lean)
retain the corrected full coefficient and the actual source sequences.

The majorant integrability and explicit L1 bound use 0 <= e <= 1,
derived eventually along the source sequence. The half-gap conclusion
and final analytic theorem retain the independent squared-gap and
joint-primitive proofs. The external extension theorem is not
separately claimed as this proof route.

This comparison records 83 complete module bodies and resolves
143 declarations. It reconciles the preceding Appendix F comparison
and twelve implementation steps. Historical refutations remain
unchanged. It does not claim a fresh review of every transitive proof.

The unchanged Lean snapshot reuses the successful full check recorded at commit 0766280d71852193457d5a4f3ccbc4cc2e6e24de: 8,638 build jobs, 7,729 public examples and an axiom audit of 44,972 NLS declarations, with 21 inherited warnings and zero new. All 143 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix G. The
[broader completion qualifications](COMPLETENESS.md) remain.
