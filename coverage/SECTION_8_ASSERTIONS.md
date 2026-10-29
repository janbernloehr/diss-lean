# Section 8 ordered assertion comparison

This ledger follows printed pp.47–52 in extraction order. All 36 passage
groups have now been compared: 28 matched and eight corrected. The exact
exterior sine bound resolves the earlier partial S8-014 comparison. Counts
describe scope, not a completion percentage; the earlier named-statement
audits remain available in [Section 8](SECTION_8.md).

Corrected constants are proved directly. The finite determinant uses circle
index 2M and prefactors -1 and 4, retaining the odd boundary pair. The real
band to the right of gap n ends at the next gap's left endpoint, and the
deleted-product midpoint factorization uses -4. Section 7's two partial
clauses, the source-wide inventory and external-construction qualifications
remain unresolved.

Source locations use the cached pdftotext extraction identified in the
[source-review index](source-review-index.json). Printed pp.47–52 were
visually inspected as well as compared with the extracted formulas.

| Group | Source lines | Requirement | Status |
| --- | --- | --- | --- |
| S8-001 | 3474–3488 | Discriminant extension, classical full product and parity levels | matched |
| S8-002 | 3490–3498 | Complex parity labels, local central parity counts and distant identification | matched |
| S8-003 | 3498–3526 | Lexicographically ordered actual parity sequences and Hilbert displacements | matched |
| S8-004 | 3535–3547 | Equation (2.4) with corrected parity prefactors | corrected |
| S8-005 | 3550–3561 | Finite-p counted parity sequences and extension definition | matched |
| S8-006 | 3563–3581 | Lemma 8.1(i): parity product joint analyticity | matched |
| S8-007 | 3583–3586 | Lemma 8.1(ii): corrected compatibility and unique extension | corrected |
| S8-008 | 3588–3599 | Lemma 8.1(iii): uniform exterior trace and derivative asymptotics | corrected |
| S8-009 | 3601–3608 | Lemma 8.1(iv): full product and periodic zero set | matched |
| S8-010 | 3610–3621 | Finite even products, locally uniform convergence and trace asymptotic chain | corrected |
| S8-011 | 3632–3651 | Original parity projection, finite rank and corrected determinant cutoff | corrected |
| S8-012 | 3653–3667 | Analytic projection transport, conjugated determinant and limit analyticity | corrected |
| S8-013 | 3669–3669 | Compatibility by Hilbert agreement and source-norm density | matched |
| S8-014 | 3670–3673 | Cauchy derivative estimate and exterior sine bound | matched |
| S8-015 | 3674–3676 | Full product factorization and actual algebraic multiplicities | matched |
| S8-016 | 3678–3701 | Complex lexicographic discontinuity and Figure 2.1 | matched |
| S8-017 | 3705–3713 | Lemma 8.2(i): endpoint continuity at real bases under complex perturbations | matched |
| S8-018 | 3714–3718 | Lemma 8.2(ii): strict separation of successive real gap pairs | matched |
| S8-019 | 3720–3744 | Local endpoint discs, Rouche counts and ordered endpoint identification | matched |
| S8-020 | 3745–3766 | Real order, signed levels (2.5) and distinct gaps | matched |
| S8-021 | 3768–3781 | Closed-gap definition and exact discriminant superlevel characterization | matched |
| S8-022 | 3784–3787 | Lemma 8.3: local uniform critical-root counts, exhaustion and reality | matched |
| S8-023 | 3790–3797 | Rouche proof for distant and central critical-root counts | matched |
| S8-024 | 3798–3803 | Real critical roots and extrema in all real gaps | corrected |
| S8-025 | 3805–3807 | Locally uniform bounded critical-root displacement | matched |
| S8-026 | 3814–3823 | Lemma 8.4: sampled l-p errors and Cauchy derivative estimate | matched |
| S8-027 | 3828–3840 | Lemma 8.5: ordered critical labels, literal derivative product and real-base continuity | matched |
| S8-028 | 3843–3854 | Critical-root displacement from sampled derivative errors and the sine bound | matched |
| S8-029 | 3855–3865 | Entire critical product, removable quotient and asymptotic identification | matched |
| S8-030 | 3867–3868 | Rouche continuity of critical labels | matched |
| S8-031 | 3870–3877 | Unique strict gap extrema, including collapsed gaps | matched |
| S8-032 | 3880–3883 | Lemma 8.6: locally uniform squared-gap critical offset | matched |
| S8-033 | 3886–3893 | Deleted product and corrected midpoint factorization | corrected |
| S8-034 | 3904–3913 | Uniform deleted-product estimate and evaluation at the critical root | matched |
| S8-035 | 3915–3927 | Cauchy derivative control and integral sinc identity | matched |
| S8-036 | 3929–3945 | Differentiated factorization, nonzero tail denominator and squared-gap conclusion | matched |

## Reviewed opening and Lemma 8.1 proof

### S8-001: Discriminant extension, classical full product and parity levels

- The source discriminant is jointly analytic and agrees with the physical Hilbert monodromy trace. Its squared value minus four has the literal full endpoint product with prefactor -4.
- The levels two and minus two are exactly the original even and odd parity spectra. For real sources the canonical endpoints have their index-prescribed signed levels.

Public evidence: `NLS.ZakharovShabat.sourceDiscriminant_eq_l2_of_two_le`, `NLS.ZakharovShabat.sourceDiscriminant_ordered_product`, `NLS.ZakharovShabat.canonicalDiscriminant_parity_levels_finite`, `NLS.ZakharovShabat.parityAlgebraicMultiplicity_pos_iff`, `NLS.ZakharovShabat.sourcePeriodicEndpoints_signed_discriminant`.

The source period-one embedding retains the original operator domain and source norm. The opening roadmap for subsequent estimates and continuity is assessed in the later passage groups, not counted as a separate completed result here.

### S8-002: Complex parity labels, local central parity counts and distant identification

- Intersecting the uniform circle and parity-count neighborhoods gives, for all sufficiently large M, exactly 4M+2 even-sector and 4M odd-sector eigenvalues inside radius (2M+1/2)*pi, counted with original algebraic multiplicity.
- Distant counted pairs lie in their index parity. Separately ordering the two parity sequences preserves the distant pair multisets and actual central counts.

Public evidence: `NLS.ZakharovShabat.exists_uniform_centralCircle`, `NLS.ZakharovShabat.exists_uniform_central_parity_multiplicity_sums`, `NLS.ZakharovShabat.CompletePeriodicParityPairs.distant_root`, `NLS.ZakharovShabat.CompletePeriodicParityPairs.exists_parity_ordered`, `NLS.ZakharovShabat.exists_uniform_source_section8_ordered_pairs`.

The common neighborhood is obtained by intersection and pullback along the continuous linear source embedding. Central parity lists are constructed independently; taking alternating slots of the globally sorted complex full spectrum is not assumed. No separate counterexample is added to this explanatory ordering warning.

### S8-003: Lexicographically ordered actual parity sequences and Hilbert displacements

- Actual parity sequences can be sorted within each pair and between every two same-parity indices, without a real-type premise. Their displacements belong to l2 at Hilbert exponent.
- Reindexing by 2n and 2n+1 gives the two displayed source lattices. Beyond both cutoffs, ordered-pair uniqueness identifies these slots with the corresponding globally ordered distant endpoints.

Public evidence: `NLS.ZakharovShabat.CompletePeriodicParityPairs.exists_parity_ordered`, `NLS.ZakharovShabat.exists_ordered_completePeriodicParityPairs`, `NLS.ZakharovShabat.memℓp_parityRescale`, `NLS.ZakharovShabat.PeriodicEndpointPair.ordered_unique`, `NLS.ZakharovShabat.canonicalPeriodicEndpoints_spec`.

CompletePeriodicParityPairs retains central multisets and all distant multiplicities. The last identification uses the maximum of the chosen parity and canonical cutoffs. It does not assert a central cross-parity ordering or analytic individual root labels.

### S8-004: Equation (2.4) with corrected parity prefactors

- The symmetric even product has prefactor -1 and limit Delta-2; the symmetric odd product has prefactor 4 and limit Delta+2. Both converge locally uniformly on the whole spectral plane.

Public evidence: `NLS.ZakharovShabat.exists_source_section8_ordered_determinant_products`, `NLS.ZakharovShabat.evenSpectralPairCutoff`, `NLS.ZakharovShabat.oddSpectralPairCutoff`, `NLS.ZakharovShabat.centralParityNormalization_ne_zero`.

These are the positive corrected formulas for (2.4), including pi_0=1. The new implementation adds no refutation of the printed constants.

### S8-005: Finite-p counted parity sequences and extension definition

- At each finite p>1, one original open convex neighborhood supplies ordered actual parity lists with lp displacements at every sufficiently large cutoff.
- The corrected even product plus two defines the source discriminant; the odd product gives the same value after subtracting two.

Public evidence: `NLS.ZakharovShabat.exists_uniform_source_section8_ordered_pairs`, `NLS.ZakharovShabat.exists_source_section8_ordered_determinant_products`, `NLS.ZakharovShabat.canonicalDiscriminant`, `NLS.ZakharovShabat.canonicalDiscriminant_eq_odd_sub_two_finite`.

The reference to (2.4) uses the correction recorded in S8-004. Hilbert agreement is an extension above two and a restriction below two. The assertion does not include p=1 or infinity.

### S8-006: Lemma 8.1(i): parity product joint analyticity

- Both corrected products are jointly complex analytic in the spectral parameter and the original potential, including at root collisions.
- The printed scalar rescalings are analytic as well; analyticity alone is independent of their normalization.

Public evidence: `NLS.ZakharovShabat.analyticOnNhd_canonicalParityProduct_periodOne`, `NLS.ZakharovShabat.SourceLemma8_1Data.parity_analytic`, `NLS.ZakharovShabat.SourceLemma8_1Data.printed_analytic`, `NLS.ZakharovShabat.sourceLemma8_1`.

The proof uses intrinsic symmetric polynomials and local uniform analytic approximation. It does not assume analytic eigenvalue coordinates. Compatibility with the trace uses the corrected constants in the next group.

### S8-007: Lemma 8.1(ii): corrected compatibility and unique extension

- With prefactors -1 and 4, Delta=f+2=g-2 on the entire finite-p source domain.
- Agreement with the classical discriminant on finite Fourier inputs uniquely determines the jointly continuous extension, hence the analytic extension.

Public evidence: `NLS.ZakharovShabat.SourceLemma8_1Data.compatibility`, `NLS.ZakharovShabat.sourceDiscriminant_unique_joint_continuous`, `NLS.ZakharovShabat.sourceDiscriminant_finite_eq_classical`, `NLS.ZakharovShabat.sourceDiscriminant_eq_l2_of_le_two`, `NLS.ZakharovShabat.sourceDiscriminant_eq_l2_of_two_le`.

The original norms and exponent inclusions are retained. The normalization correction is necessary for the shifted identities. No additional incompatibility proof is introduced.

### S8-008: Lemma 8.1(iii): uniform exterior trace and derivative asymptotics

- For every tolerance, one original open convex neighborhood and positive threshold control the additive trace error and additive derivative error by epsilon*exp(abs(Im z)) throughout the original exterior.
- The derivative quotient by -2*sin(z) converges uniformly to one there. The trace quotient is proved where 2*cos(z) has an explicit positive lower bound relative to exp(abs(Im z)).

Public evidence: `NLS.ZakharovShabat.exists_uniform_sourceDiscriminant_exterior`, `NLS.ZakharovShabat.exists_uniform_sourceDiscriminant_cosine_quotient`.

The full exterior is unchanged for the additive trace estimate and sine quotient. The cosine quotient retains its denominator condition; it is not asserted uniformly across cosine zeros. Existing positive corrections are reused.

### S8-009: Lemma 8.1(iv): full product and periodic zero set

- Delta squared minus four is the product of the corrected parity factors and the full symmetric endpoint product with prefactor -4.
- Its zero set is exactly the original periodic spectrum, and its analytic zero order is the original algebraic multiplicity.

Public evidence: `NLS.ZakharovShabat.sourceDiscriminant_ordered_product`, `NLS.ZakharovShabat.canonicalParityProducts_mul`, `NLS.ZakharovShabat.canonicalPeriodic_eq_discriminant_sq_sub_four_finite`, `NLS.ZakharovShabat.canonicalDiscriminant_sq_eq_four_iff_finite`, `NLS.ZakharovShabat.analyticOrderAt_canonicalDiscriminant_sq_sub_four`.

Both printed scalar rescalings cancel in their product, so this full-product normalization is unchanged. Coincident roots and central algebraic multiplicities are retained.

### S8-010: Finite even products, locally uniform convergence and trace asymptotic chain

- Finite even cutoffs equal the normalized intrinsic central even polynomials at index 2M. These converge jointly locally uniformly to the corrected even product.
- The ratio of the even product to 2*cos(z)-2 tends to one on the original exterior, locally uniformly in the potential. The resulting trace estimate is the additive estimate of S8-008.

Public evidence: `NLS.ZakharovShabat.CompletePeriodicParityPairs.cutoffs_eq_normalizedParity`, `NLS.ZakharovShabat.exists_uniform_canonicalParityProducts_weighted`, `NLS.ZakharovShabat.tendstoLocallyUniformlyOn_canonicalParityProduct_joint`, `NLS.ZakharovShabat.exists_uniform_exterior_canonicalProducts`, `NLS.ZakharovShabat.exists_uniform_sourceDiscriminant_exterior`.

The finite even product already has prefactor -1. Its limit is the corrected f. The last printed asymptotic-chain step is replaced by the proved additive trace estimate or by a cosine quotient with the stated denominator bound.

### S8-011: Original parity projection, finite rank and corrected determinant cutoff

- The original resolvent contour projection restricted to a Fourier parity is analytic and has finite-dimensional range; its domain lift retains the original unbounded operator.
- Every sufficiently large even cutoff equals minus the actual even contour determinant divided by its normalization at circle index 2M. The odd cutoff has factor 4 and retains its positive boundary pair 2M+1.

Public evidence: `NLS.ZakharovShabat.parityContourProjection`, `NLS.ZakharovShabat.analyticAt_parityContourProjection`, `NLS.ZakharovShabat.finiteDimensional_range_parityContourProjection`, `NLS.ZakharovShabat.contourLift_parityProjection`, `NLS.ZakharovShabat.reducedParityContourOperator_self_apply`, `NLS.ZakharovShabat.CompletePeriodicParityPairs.section8_cutoffs_eq_contourDeterminants`, `NLS.ZakharovShabat.exists_source_section8_cutoff_determinants`, `NLS.ZakharovShabat.exists_source_section8_ordered_determinant_products`.

The circle radius is (2M+1/2)*pi for a product over even modes through 2M. Both the negative even prefactor and the doubled circle index are explicit. Callers of the source existence theorem supply neither contour admissibility nor hypothetical root sequences; both are constructed.

### S8-012: Analytic projection transport, conjugated determinant and limit analyticity

- Local analytic projection transport conjugates the actual parity reduction to an operator on a fixed original finite-dimensional range, preserving the determinant.
- The corrected normalized central parity polynomials are jointly analytic on a common neighborhood for all large cutoffs. Their locally uniform limit is jointly analytic on the full source domain.

Public evidence: `NLS.ZakharovShabat.reducedParityContourOperator_conjugate`, `NLS.ZakharovShabat.parityContourDeterminant_eq_reduced`, `NLS.ZakharovShabat.analyticAt_reducedParityContourOperator`, `NLS.ZakharovShabat.analyticAt_parityContourDeterminant`, `NLS.ZakharovShabat.exists_uniform_analytic_normalizedCentralParityPolynomials`, `NLS.ZakharovShabat.localUniformAnalyticApproximation_canonicalParityProduct`, `NLS.ZakharovShabat.analyticOnNhd_canonicalParityProduct_periodOne`.

The conjugated displayed even determinant keeps the same negative prefactor as S8-011. Transport is used locally for each fixed cutoff and point; the proof of common-neighborhood analyticity does not require one global trivialization for every cutoff. The odd intrinsic approximants remove the boundary factor only in the limit.

### S8-013: Compatibility by Hilbert agreement and source-norm density

- Hilbert compatibility transfers below two by exact exponent inclusion, and above two by continuity on the dense Hilbert image. Finite Fourier density supplies uniqueness in the original source norm.

Public evidence: `NLS.ZakharovShabat.canonicalParity_shifted_eq_finite`, `NLS.ZakharovShabat.sourceDiscriminant_unique_continuous`, `NLS.ZakharovShabat.sourceDiscriminant_unique_joint_continuous`.

This is compatibility of the corrected products. Below two the direction is restriction to the stronger source space, not density of all Hilbert inputs in it.

### S8-014: Cauchy derivative estimate and exterior sine bound

- Cauchy estimates give the derivative error on the original exterior. The exact intermediate bound norm(cos(z)/sin(z)) <= exp(abs(Im(z)))/norm(sin(z)) <= 4 now holds throughout that exterior, including its lower horizontal strip.
- The positive proof obtains norm(sin(z)) >= 1/2 outside all quarter-pi free discs and combines this with the exponential difference bound.

Public evidence: `NLS.ZakharovShabat.section8_norm_sin_sq`, `NLS.ZakharovShabat.section8_centered_sine_lower`, `NLS.ZakharovShabat.section8_half_le_norm_sin`, `NLS.ZakharovShabat.section8_exp_abs_im_le_four_norm_sin`, `NLS.ZakharovShabat.section8_exterior_sine_quotient`, `NLS.ZakharovShabat.exists_uniform_discriminant_derivative_error_exp`, `NLS.ZakharovShabat.exists_uniform_discriminant_derivative_div_free`.

This resolves the quantitative refinement left partial by the preceding review. The integration example turns an additive error epsilon*exp(abs(Im(z))) into a quotient error at most 2*epsilon. No assertion that the printed constant is false is needed.

### S8-015: Full product factorization and actual algebraic multiplicities

- The intrinsic parity factors multiply to the original full canonical product. Each parity factor has precisely its original algebraic zero orders; the full order is the original periodic algebraic multiplicity.
- The determinant reduction retains the original generalized root chains, so multiplicity is not inferred only from a set-level root equality.

Public evidence: `NLS.ZakharovShabat.canonicalParityProduct_spec`, `NLS.ZakharovShabat.canonicalParityProducts_mul`, `NLS.ZakharovShabat.parityContourDeterminant_eq_prod`, `NLS.ZakharovShabat.reducedParityContourOperator_rootMultiplicity`, `NLS.ZakharovShabat.analyticOrderAt_canonicalDiscriminant_sq_sub_four`.

The source product argument is implemented through exact finite multiplicities and the canonical entire products. All spectral points, including repeated central roots, are covered.

The new direct [source determinant interface](../NLS/ZakharovShabat/SourceSection8ParityDeterminants.lean)
constructs the common source neighborhood and ordered roots. Two integration
examples below exponent two derive the difference four between the parity
limits and convergence of the actual even contour determinants.

## Remaining Section 8 passages

### S8-016: Complex lexicographic discontinuity and Figure 2.1

- In every original source neighborhood of zero there is a constant complex source at which both actual central periodic endpoint labels are discontinuous.
- A continuous source curve makes two simple central roots cross a vertical line, changing the lexicographic choice as in Figure 2.1.

Public evidence: `NLS.ZakharovShabat.sourceConstantCrossing`, `NLS.ZakharovShabat.continuous_sourceConstantCrossing`, `NLS.ZakharovShabat.orderedEndpoint_vertical_crossing_neg`, `NLS.ZakharovShabat.orderedEndpoint_vertical_crossing_zero`, `NLS.ZakharovShabat.exists_sourcePeriodicLabels_not_continuousAt`.

The existing witness theorem is reused. The source warning is existential for general complex potentials; it does not assert discontinuity at every complex source or at zero itself.

### S8-017: Lemma 8.2(i): endpoint continuity at real bases under complex perturbations

- At every real-type original source, both ordered periodic endpoint maps are continuous at every signed index under arbitrary complex source perturbations.
- The implementation also proves continuity of both full lp displacement sequences and one neighborhood controlling all coordinate changes.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_2`, `NLS.ZakharovShabat.SourceLemma8_2Data.continuous_left`, `NLS.ZakharovShabat.SourceLemma8_2Data.continuous_right`, `NLS.ZakharovShabat.continuousAt_sourcePeriodicEndpointDisplacements_of_realType`, `NLS.ZakharovShabat.exists_uniform_sourcePeriodicEndpoint_neighborhood`.

No root simplicity, noncollapsed-gap or real-perturbation restriction is imposed. The full sequence-norm conclusion is stronger than the printed coordinatewise statement.

### S8-018: Lemma 8.2(ii): strict separation of successive real gap pairs

- At each real-type source, the endpoints within a gap are weakly ordered and successive gaps are strictly separated at every integer index.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_2`, `NLS.ZakharovShabat.SourceLemma8_2Data.interlacing`, `NLS.ZakharovShabat.SourceLemma8_2Data.disjoint_gaps`.

The within-gap inequality permits coincident endpoints. The strict inequalities between distinct gaps include central indices and remain valid when either neighboring gap collapses.

### S8-019: Local endpoint discs, Rouche counts and ordered endpoint identification

- Joint continuity gives locally uniform periodic products and stable analytic counts on every spectral-free circle near the source. Compact root confinement keeps nearby roots inside neighborhoods of the old spectrum.
- Stable prefix and suffix counts in real-diameter discs bound the real part of each ordered slot. Imaginary-part confinement then gives complex coordinate continuity even at repeated endpoint values.

Public evidence: `NLS.ZakharovShabat.tendstoLocallyUniformlyOn_periodicProduct_family`, `NLS.ZakharovShabat.eventually_periodicProduct_count_eq`, `NLS.ZakharovShabat.eventually_periodicSpectrum_mem_open`, `NLS.ZakharovShabat.eventually_canonicalPeriodicSlot_re_le_of_barrier`, `NLS.ZakharovShabat.eventually_le_canonicalPeriodicSlot_re_of_barrier`, `NLS.ZakharovShabat.continuousAt_canonicalPeriodicSlot_im_of_realType`, `NLS.ZakharovShabat.continuousAt_canonicalPeriodicSlot_of_realType`.

The formal proof uses real-diameter barriers to implement the source small-disc ordering argument. Counts are analytic multiplicities, not just the number of distinct root values. The continuous original embedding pulls the neighborhood back to the source norm.

### S8-020: Real order, signed levels (2.5) and distinct gaps

- The real ordered endpoints have the signed discriminant level (-1)^n*Delta=2 for every positive, zero and negative index.
- Adjacent pairs have opposite levels, yielding strict separation; lexicographic order reduces to the real order at real-type sources.

Public evidence: `NLS.ZakharovShabat.sourcePeriodicEndpoints_signed_discriminant`, `NLS.ZakharovShabat.SourceLemma8_2Data.real_endpoints`, `NLS.ZakharovShabat.SourceLemma8_2Data.interlacing`.

The signed level identity retains integer powers and the original source potential. Both restriction below exponent two and extension above it have already been justified in the discriminant compatibility comparison.

### S8-021: Closed-gap definition and exact discriminant superlevel characterization

- The closed source gaps are exactly the real points where norm(Delta) is at least two; their interiors are exactly the points where it is greater than two.
- On gap n the signed value (-1)^n*Delta is at least two, with a strict inequality in every nonempty gap interior. Equality in modulus occurs exactly at an endpoint.

Public evidence: `NLS.ZakharovShabat.sourceRealPeriodicGap`, `NLS.ZakharovShabat.SourceLemma8_2Data.closed_gaps`, `NLS.ZakharovShabat.SourceLemma8_2Data.open_gaps`, `NLS.ZakharovShabat.SourceLemma8_2Data.endpoint_set`, `NLS.ZakharovShabat.SourceLemma8_2Data.existsUnique_gap`, `NLS.ZakharovShabat.signed_discriminant_ge_two_on_canonicalGap`, `NLS.ZakharovShabat.signed_discriminant_gt_two_on_canonicalGap_interior`.

The product-sign and level-continuity proof supplies the superlevel characterization directly. Collapsed gaps are included as singletons and each superlevel point belongs to exactly one gap.

### S8-022: Lemma 8.3: local uniform critical-root counts, exhaustion and reality

- One open convex original neighborhood and positive cutoff give exactly one simple critical root in each distant quarter-pi disc, exactly 2K+1 central roots for every larger cutoff K, and exhaustion of all roots.
- The distant and central boundaries are zero-free; central labels retain analytic multiplicity. At real-type sources every critical root is real.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_3`, `NLS.ZakharovShabat.SourceLemma8_3Data.central_roots`, `NLS.ZakharovShabat.SourceLemma8_3Data.central_multiplicity`, `NLS.ZakharovShabat.SourceLemma8_3Data.central_box_selection`, `NLS.ZakharovShabat.SourceLemma8_3Data.central_box_count`, `NLS.ZakharovShabat.discriminant_critical_im_eq_zero_of_realType`.

The central circle used in the printed proof and the earlier height-K central box select the same critical roots after increasing the cutoff. Reality is supported by the real-rooted full-product derivative argument, not merely conjugation symmetry.

### S8-023: Rouche proof for distant and central critical-root counts

- The locally uniform exterior derivative ratio supplies a strict Rouche inequality with tolerance one half on all sufficiently distant free circles and all sufficiently large central circles.
- The free derivative counts transfer as one and 2K+1, with boundary nonvanishing. Exterior nonvanishing and the free-disc geometry exclude any further critical roots.

Public evidence: `NLS.ZakharovShabat.exists_uniform_discriminant_derivative_rouche`, `NLS.ZakharovShabat.exists_uniform_discriminant_critical_counts`, `NLS.ZakharovShabat.exists_uniform_discriminant_critical_distribution`, `NLS.ZakharovShabat.exists_discriminant_critical_counts`.

The same source neighborhood and cutoff work for every larger central circle, including both signed distant tails. Exhaustion is proved, rather than inferred from a single central count.

### S8-024: Real critical roots and extrema in all real gaps

- The band to the right of gap n is (lambda_n^+,lambda_(n+1)^-). It is nonempty, and the discriminant real part has square strictly below four there.
- Each real gap contains a critical point: Rolle supplies one in an open gap and endpoint multiplicity covers a collapsed gap. Distinct gap witnesses saturate the central critical multiset and identify the canonical indexed roots.

Public evidence: `NLS.ZakharovShabat.sourceRealBand`, `NLS.ZakharovShabat.sourceRealBand_nonempty`, `NLS.ZakharovShabat.sourceDiscriminant_realBand_sq_lt_four`, `NLS.ZakharovShabat.exists_critical_between_canonicalPeriodicEndpoints`, `NLS.ZakharovShabat.canonicalPeriodicLeft_critical_of_eq_right`, `NLS.ZakharovShabat.realGapCriticalPoint_centralRoots_eq`, `NLS.ZakharovShabat.canonicalCriticalPoints_eq_realGapCriticalPoint`, `NLS.ZakharovShabat.sourceLemma8_5_real`.

Printed p.50 gives the right-hand band endpoint with index n-1; the proved replacement uses n+1. The square bound is stronger than the needed signed upper bound. This is a positive correction, with no additional refutation theorem.

### S8-025: Locally uniform bounded critical-root displacement

- The complete canonical critical sequence has a locally uniform bound on its displacement from pi*n, over all signed indices.

Public evidence: `NLS.ZakharovShabat.exists_uniform_critical_displacements`, `NLS.ZakharovShabat.sourceLemma8_5`, `NLS.ZakharovShabat.SourceLemma8_5Data.displacement`.

The later proved full lp displacement bound implies the displayed O(1) estimate by the coordinate norm bound. Central roots are included through a bounded finite head, and the same source neighborhood controls all indices.

### S8-026: Lemma 8.4: sampled l-p errors and Cauchy derivative estimate

- For every sampler in the quarter-pi free discs, the actual trace and derivative errors form lp sequences with one locally uniform norm bound.
- One majorant on the half-pi discs gives the trace estimate; Cauchy on the quarter-pi discs gives the derivative factor 4/pi.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_4`, `NLS.ZakharovShabat.SourceLemma8_4Data.disc_majorants`, `NLS.ZakharovShabat.SourceLemma8_4Data.sampled_norms`, `NLS.ZakharovShabat.exists_uniform_discriminant_disc_majorants`, `NLS.ZakharovShabat.exists_uniform_discriminant_value_derivative_majorants`, `NLS.ZakharovShabat.exists_uniform_sampled_discriminant_errors`.

The majorant is selected before the spectral sampling points. No continuity of the sampler or of the complex endpoint labels is assumed. Closed quarter-pi discs are covered, including their centers.

### S8-027: Lemma 8.5: ordered critical labels, literal derivative product and real-base continuity

- The actual critical roots admit a complete lexicographic enumeration with exact multiplicities and locally uniformly bounded lp displacement.
- The literal symmetric product with prefactor two and pi_0=1 converges locally uniformly on the whole spectral plane to the derivative. Each coordinate is continuous at real-type sources.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_5`, `NLS.ZakharovShabat.sourceLemma8_5_data`, `NLS.ZakharovShabat.SourceLemma8_5Data.product`, `NLS.ZakharovShabat.sourceLemma8_5_real`, `NLS.ZakharovShabat.exists_uniform_ordered_critical_products`.

Sorting changes only a finite central block and preserves the distant labels. The norm estimate includes that entire central block; no globally continuous labeling at arbitrary complex sources is assumed.

### S8-028: Critical-root displacement from sampled derivative errors and the sine bound

- At a distant critical root the sampled derivative-error estimate bounds sin(lambda_n^bullet). The inverse sine estimate on its free disc then bounds lambda_n^bullet-pi*n by an lp majorant.
- A bounded finite central replacement produces a full lp displacement sequence with a common neighborhood norm bound.

Public evidence: `NLS.ZakharovShabat.norm_critical_displacement_le`, `NLS.ZakharovShabat.exists_criticalDisplacementCoeff_le`, `NLS.ZakharovShabat.exists_uniform_critical_displacements`.

The printed intermediate assertion is sin(lambda_n^bullet) in lp, not lambda_n^bullet itself. The exact free derivative factor -2 is retained in the bound and absorbed only into the final lp coefficient.

### S8-029: Entire critical product, removable quotient and asymptotic identification

- The normalized entire critical product has the same finite analytic zero orders as the discriminant derivative, so their quotient extends across all common zeros.
- The quotient tends to one on the free-disc exterior. Maximum modulus yields a global bound, and Liouville plus an escaping exterior sequence makes the quotient identically one.

Public evidence: `NLS.ZakharovShabat.CriticalPointLabeling.analyticOnNhd_quotient`, `NLS.ZakharovShabat.CriticalPointLabeling.tendsto_quotient_of_separated`, `NLS.ZakharovShabat.CriticalPointLabeling.isBounded_quotient`, `NLS.ZakharovShabat.CriticalPointLabeling.quotient_eq_one`, `NLS.ZakharovShabat.CriticalPointLabeling.product_eq_derivative`, `NLS.ZakharovShabat.CriticalPointLabeling.tendstoLocallyUniformlyOn_derivative_product`.

The proof explicitly bridges the exterior asymptotic to the whole plane. Root-set equality alone is not used to infer removability; central repeated roots retain their full analytic orders.

### S8-030: Rouche continuity of critical labels

- Locally uniform derivative dependence preserves critical counts on each zero-free circle. Ordered prefix and suffix barriers and imaginary-part confinement give coordinate continuity at real-type sources.

Public evidence: `NLS.ZakharovShabat.tendstoLocallyUniformlyOn_discriminant_derivative_family`, `NLS.ZakharovShabat.eventually_discriminant_critical_count_eq`, `NLS.ZakharovShabat.eventually_canonicalCriticalPoints_re_le_of_barrier`, `NLS.ZakharovShabat.eventually_le_canonicalCriticalPoints_re_of_barrier`, `NLS.ZakharovShabat.continuousAt_canonicalCriticalPoints_of_realType`, `NLS.ZakharovShabat.analyticAt_sourceCanonicalCriticalPoint_of_realType`.

The proof parallels the periodic-endpoint count argument under arbitrary complex perturbations. At real type every critical root is simple, so the implementation also obtains local coordinate analyticity.

### S8-031: Unique strict gap extrema, including collapsed gaps

- Every canonical critical root of a real source lies in its indexed closed gap and is the unique critical point there.
- All such critical roots are simple zeros of the derivative and hence strict real local extrema, including collapsed gaps. There are no other real local extrema.

Public evidence: `NLS.ZakharovShabat.canonicalCriticalPoints_mem_canonicalPeriodicGap`, `NLS.ZakharovShabat.analyticOrderAt_discriminant_critical_eq_one_of_realType`, `NLS.ZakharovShabat.discriminant_second_derivative_ne_zero_at_critical_of_realType`, `NLS.ZakharovShabat.discriminant_critical_strict_local_extremum`, `NLS.ZakharovShabat.existsUnique_localExtremum_in_canonicalPeriodicGap`, `NLS.ZakharovShabat.isLocalExtr_real_discriminant_iff_canonical`, `NLS.ZakharovShabat.sourceLemma8_5_real`.

Strictness is expressed on a punctured real neighborhood, so it remains meaningful at a singleton gap. The proof combines exact global multiplicities, central count saturation, the second-derivative test and Fermat's theorem.

### S8-032: Lemma 8.6: locally uniform squared-gap critical offset

- One open convex original neighborhood and one positive cutoff give the actual critical midpoint offset as the squared gap times an lp coefficient sequence with a uniform norm bound.

Public evidence: `NLS.ZakharovShabat.sourceLemma8_6`, `NLS.ZakharovShabat.sourceCriticalGapTailCoefficient_apply`, `NLS.ZakharovShabat.SourceLemma8_6Data.offset`, `NLS.ZakharovShabat.SourceLemma8_6Data.norm_offset_le`, `NLS.ZakharovShabat.SourceLemma8_6Data.collapsed_gap`.

The statement is for arbitrary complex sources at every finite p>1. It includes all sufficiently distant signed indices and collapsed gaps; the finite central extension of the coefficient is zero.

### S8-033: Deleted product and corrected midpoint factorization

- The deleted endpoint product has the literal outer factor 1/pi_n^2 and omits exactly the nth pair; its cutoffs converge locally uniformly on the whole plane.
- With that normalization the exact midpoint factorization is Delta^2-4=-4*((tau_n-z)^2-gamma_n^2/4)*Delta_n(z).

Public evidence: `NLS.ZakharovShabat.sourceDeletedPeriodicProduct_formula`, `NLS.ZakharovShabat.sourceDiscriminant_midpoint_factorization`, `NLS.ZakharovShabat.canonicalDiscriminant_sq_sub_four_eq_midpoint_mul`.

The positive correction is the prefactor -4. The normalization includes pi_0=1, the removed index, coincident endpoints and evaluations at removed roots. Historical refutations are left unchanged; none is added.

### S8-034: Uniform deleted-product estimate and evaluation at the critical root

- The deleted product differs from the squared filled free sine quotient by a locally uniformly bounded lp majorant on every half-pi disc.
- At the actual distant critical roots, the deleted-product value minus one and its derivative have bounded lp tail representatives on one common source neighborhood.

Public evidence: `NLS.ZakharovShabat.exists_uniform_canonicalDeletedPairError_majorants`, `NLS.ZakharovShabat.exists_uniform_sampled_canonicalDeletedPairErrors`, `NLS.ZakharovShabat.exists_uniform_deletedProduct_critical_coefficients`, `NLS.ZakharovShabat.memℓp_canonicalDeletedCriticalValueError`, `NLS.ZakharovShabat.memℓp_canonicalDeletedCriticalDerivative`.

The critical displacements and centered sine-quotient estimates control evaluation at moving roots. Central indices are filled by finite modification for full lp membership; local tail norm bounds are asserted on a common cutoff.

### S8-035: Cauchy derivative control and integral sinc identity

- Cauchy converts the deleted-product value majorant on half-pi discs into a derivative majorant with factor 4/pi on quarter-pi discs.
- The filled sinc equals the integral from zero to one of cos(s*z), including at z=0. After translation and squaring, its value error and derivative are O(z-pi*n) uniformly on fixed-radius free discs.

Public evidence: `NLS.ZakharovShabat.exists_uniform_canonicalDeletedPairError_majorants`, `NLS.ZakharovShabat.section8_freeSineQuotient_zero_integral`, `NLS.ZakharovShabat.section8_freeSineQuotient_sq_integral`, `NLS.ZakharovShabat.deriv_freeSineQuotient_sq_center`, `NLS.ZakharovShabat.exists_freeSquaredSine_displacement_bounds`.

The new integral identity supplies the literal source display at its removable center. The derivative estimate is proved through entire increment bounds and the vanishing center derivative; the integration example verifies this for the literal squared integral.

### S8-036: Differentiated factorization, nonzero tail denominator and squared-gap conclusion

- Differentiating the corrected factorization at a critical point gives 2*a*G(c)+(a^2-gamma^2/4)*Gprime(c)=0. Thus B*a=gamma^2*Gprime(c)/4 for B=2*G(c)+a*Gprime(c).
- The coefficient error B-2 has locally bounded lp tail representatives. Independent uniform smallness estimates give norm(B)>=1 on a common tail, so a=gamma^2*Gprime(c)/(4*B) with locally bounded lp coefficients.

Public evidence: `NLS.ZakharovShabat.discriminant_critical_midpoint_identity`, `NLS.ZakharovShabat.canonicalCriticalOffsetCoefficient_identity`, `NLS.ZakharovShabat.exists_uniform_criticalOffsetCoefficient_error`, `NLS.ZakharovShabat.exists_uniform_small_deletedProduct_critical_values`, `NLS.ZakharovShabat.exists_uniform_small_criticalOffsetCoefficient_error`, `NLS.ZakharovShabat.exists_uniform_criticalOffsetCoefficient_lower_bound`, `NLS.ZakharovShabat.canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient`, `NLS.ZakharovShabat.exists_uniform_critical_midpoint_gap_sq_lp`, `NLS.ZakharovShabat.SourceLemma8_6Data.denominator_ne_zero`.

The common factor -4 cancels from the zero differentiated equation. Dividing the coefficient equation by two gives the printed normalized (1+lp) form. Uniform nonvanishing is proved separately from bounded lp norms, and only B is divided by, never the gap.

The [positive sine estimates](../NLS/ZakharovShabat/SourceSection8SineEstimates.lean)
prove the exact exterior constant and the literal sinc integral. Two integration
examples connect these to quotient-error control and the vanishing derivative
at every signed free center.

## Remaining work beyond this section

All 36 ordered Section 8 groups are compared, with eight proved corrections.
Continue the ordered source comparison with Section 9. Preserve Section 7's
physical NLS Dirichlet-motion and unrestricted psi-characterization clauses,
the exact cited 2014 construction, Appendix G.2 norm interpretation and the
broader source inventory; this section ledger does not settle those tasks.
