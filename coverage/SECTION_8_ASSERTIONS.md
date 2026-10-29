# Section 8 ordered assertion comparison

This ledger follows printed pp.47–52 in extraction order. The first fifteen
passage groups, through the proof of Lemma 8.1, have been compared: eight
matched, six corrected and one partial. The remaining 21 groups are pending
this ordered review; the earlier named-statement audits remain available in
[Section 8](SECTION_8.md). Counts describe scope, not a completion percentage.

Corrected constants are proved directly. The finite determinant uses circle
index 2M and prefactors -1 and 4, retaining the odd boundary pair. S8-014
retains a quantitative refinement of the intermediate sine bound; the main
derivative asymptotic is already proved. Section 7's two partial clauses,
the source-wide inventory and external-construction qualifications remain.

Source locations use the cached pdftotext extraction identified in the
[source-review index](source-review-index.json). Printed pp.47–49 were
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
| S8-014 | 3670–3673 | Cauchy derivative estimate and exterior sine bound | partial |
| S8-015 | 3674–3676 | Full product factorization and actual algebraic multiplicities | matched |
| S8-016 | 3678–3701 | Complex lexicographic discontinuity and Figure 2.1 | pending |
| S8-017 | 3705–3713 | Lemma 8.2(i): endpoint continuity at real bases under complex perturbations | pending |
| S8-018 | 3714–3718 | Lemma 8.2(ii): strict separation of successive real gap pairs | pending |
| S8-019 | 3720–3744 | Local endpoint discs, Rouche counts and ordered endpoint identification | pending |
| S8-020 | 3745–3766 | Real order, signed levels (2.5) and distinct gaps | pending |
| S8-021 | 3768–3781 | Closed-gap definition and exact discriminant superlevel characterization | pending |
| S8-022 | 3784–3787 | Lemma 8.3: local uniform critical-root counts, exhaustion and reality | pending |
| S8-023 | 3790–3797 | Rouche proof for distant and central critical-root counts | pending |
| S8-024 | 3798–3803 | Real critical roots and extrema in all real gaps | pending |
| S8-025 | 3805–3807 | Locally uniform bounded critical-root displacement | pending |
| S8-026 | 3814–3823 | Lemma 8.4: sampled l-p errors and Cauchy derivative estimate | pending |
| S8-027 | 3828–3840 | Lemma 8.5: ordered critical labels, literal derivative product and real-base continuity | pending |
| S8-028 | 3843–3854 | Critical-root displacement from sampled derivative errors and the sine bound | pending |
| S8-029 | 3855–3865 | Entire critical product, removable quotient and asymptotic identification | pending |
| S8-030 | 3867–3868 | Rouche continuity of critical labels | pending |
| S8-031 | 3870–3877 | Unique strict gap extrema, including collapsed gaps | pending |
| S8-032 | 3880–3883 | Lemma 8.6: locally uniform squared-gap critical offset | pending |
| S8-033 | 3886–3893 | Deleted product and corrected midpoint factorization | pending |
| S8-034 | 3904–3913 | Uniform deleted-product estimate and evaluation at the critical root | pending |
| S8-035 | 3915–3927 | Cauchy derivative control and integral sinc identity | pending |
| S8-036 | 3929–3945 | Differentiated factorization, nonzero tail denominator and squared-gap conclusion | pending |

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

- Cauchy estimates on smaller exterior discs give the derivative error on the same original exterior. A positive uniform bound on exp(abs(Im z))/abs(sin z) converts it into the required sine quotient.
- The implemented reciprocal-sine theorem supplies a finite constant depending only on the excluded-disc radius. Its explicit constant 4 is proved for abs(Im z)>=1.

Public evidence: `NLS.ZakharovShabat.exists_uniform_discriminant_derivative_error_exp`, `NLS.ZakharovShabat.exists_bound_exp_im_div_sin_of_separated`, `NLS.ZakharovShabat.exp_abs_im_le_four_norm_sin`, `NLS.ZakharovShabat.exists_uniform_discriminant_derivative_div_free`.

The complete derivative conclusion is proved, but the literal intermediate constant 4 throughout the lower horizontal strip has not been established by this comparison. This is a remaining quantitative refinement, not a claim that the printed bound is false. No refutation is requested or added.

### S8-015: Full product factorization and actual algebraic multiplicities

- The intrinsic parity factors multiply to the original full canonical product. Each parity factor has precisely its original algebraic zero orders; the full order is the original periodic algebraic multiplicity.
- The determinant reduction retains the original generalized root chains, so multiplicity is not inferred only from a set-level root equality.

Public evidence: `NLS.ZakharovShabat.canonicalParityProduct_spec`, `NLS.ZakharovShabat.canonicalParityProducts_mul`, `NLS.ZakharovShabat.parityContourDeterminant_eq_prod`, `NLS.ZakharovShabat.reducedParityContourOperator_rootMultiplicity`, `NLS.ZakharovShabat.analyticOrderAt_canonicalDiscriminant_sq_sub_four`.

The source product argument is implemented through exact finite multiplicities and the canonical entire products. All spectral points, including repeated central roots, are covered.

The new direct [source determinant interface](../NLS/ZakharovShabat/SourceSection8ParityDeterminants.lean)
constructs the common source neighborhood and ordered roots. Two integration
examples below exponent two derive the difference four between the parity
limits and convergence of the actual even contour determinants.

## Remaining work

Continue with S8-016 through S8-036. The exact lower-strip constant in S8-014
remains to be compared or proved; the general bounded reciprocal sine already
suffices for Lemma 8.1(iii). Preserve Section 7's physical NLS Dirichlet-motion
and unrestricted psi-characterization qualifications, the exact cited 2014
construction, Appendix G.2 norm interpretation and the broader source inventory.
