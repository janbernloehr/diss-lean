# Section 7: ordered assertion comparison

This ledger follows the extraction order of printed pp.45–47. The unit-period
source space and its physical spectral realization are retained. All 21 passage
groups have now been compared: eighteen are matched, one is corrected and two
are partial. These counts describe review scope, not a completion percentage.

S7-002 retains the unresolved physical NLS motion clause. S7-013 has a proved
corrected product and exact periods, but its unrestricted uniqueness wording
is not covered by the existing theorem for placed real roots. The corrected
real codimension in S7-014 is two. The exact cited 2014 construction remains
a separate qualification. Existing focused proofs are in [Section 7](SECTION_7.md).

Source locations use the pinned text extraction recorded in the
[source-review index](source-review-index.json). The three rendered source
pages were inspected. No extra counterexample is required to justify a
proved replacement constant.

| Group | Source lines | Passage | Status |
| --- | --- | --- | --- |
| S7-001 | 3305–3312 | Lax conservation and invariant isospectral sets | matched |
| S7-002 | 3312–3316 | Actual Dirichlet eigenvalues and sheet signs | partial |
| S7-003 | 3318–3319 | Compact connected tori, exact dimension and generic infinitely many gaps | matched |
| S7-004 | 3319–3321 | Squared gaps determine the periodic spectrum | matched |
| S7-005 | 3322–3325 | Action radii and Dirichlet angles | matched |
| S7-006 | 3326–3331 | Classical fundamental solution and discriminant trace | matched |
| S7-007 | 3333–3344 | Periodic zeros and normalized product (2.1) | matched |
| S7-008 | 3346–3352 | Arnold action formula (2.2) | matched |
| S7-009 | 3362–3371 | Contour orientation, canonical root domain and sign | matched |
| S7-010 | 3374–3375 | One common analytic action neighborhood | matched |
| S7-011 | 3376–3379 | Classical anti-discriminant | matched |
| S7-012 | 3381–3396 | Angle formula (2.3), admissible paths and terminal root sign | matched |
| S7-013 | 3397–3410 | Psi product, asymptotics and period normalization | partial |
| S7-014 | 3412–3415 | Angle conventions and the collapsed-gap locus | corrected |
| S7-015 | 3416–3418 | Hilbert canonical Poisson relations | matched |
| S7-016 | 3420–3426 | Rough Fourier-Lebesgue input and non-measure assertion | matched |
| S7-017 | 3428–3432 | Entire product extension and agreement with classical discriminant | matched |
| S7-018 | 3433–3438 | Extended roots, actions, psi, anti-discriminant and density transfer | matched |
| S7-019 | 3450–3455 | Theorem 7.1 common neighborhood and analytic actions | matched |
| S7-020 | 3458–3459 | Theorem 7.1 real mod-2pi angles and mod-pi extension | matched |
| S7-021 | 3461–3468 | Theorem 7.1 exact canonical relations and domains | matched |

## Reviewed opening passages

### S7-001: Lax conservation and invariant isospectral sets

- The full original periodic spectrum, with all algebraic multiplicities, is conserved along every global ordinary physical NLS solution on the real Hilbert source space.
- The actual isospectral sets cover the real source space, and any two are equal or disjoint. The class of a solution is exactly its initial class at every time.

Public evidence: `NLS.ZakharovShabat.sourceIsospectralSet_eq_or_disjoint`, `NLS.ZakharovShabat.iUnion_sourceIsospectralSet`, `NLS.ZakharovShabat.sourceIsospectralSet_of_isOrdinaryNLSSolutionOn_univ`, `NLS.ZakharovShabat.mem_sourceIsospectralSet_of_isOrdinaryNLSSolutionOn_univ_iff`, `NLS.ZakharovShabat.isospectral_of_isOrdinaryNLSSolutionOn_univ`.

The conservation conclusion is proved through the physical solution and uniqueness theorems. The cited Lax-pair derivation is contextual and is not independently reconstructed. Partition statements hold for finite p>=1; physical solution invariance is asserted for 1<p<=2, including the source Hilbert case.

### S7-002: Actual Dirichlet eigenvalues and sheet signs

- Each actual Hilbert isospectral set is homeomorphic to the product of its signed Dirichlet gap sheets. The base coordinate is the original Dirichlet eigenvalue, and the sign is its actual anti-discriminant sign.
- Every allowable full signed data family determines a unique source in that isospectral set. The two sheet branches are glued at the endpoints, where the sign is zero.
- The additional assertion of nonconservation under physical NLS, and its rough description of signs as directions of NLS motion, remain outside this completed comparison.

Public evidence: `NLS.ZakharovShabat.sourceHilbertSignedDirichletHomeomorph`, `NLS.ZakharovShabat.sourceHilbertSignedDirichletHomeomorph_base`, `NLS.ZakharovShabat.sourceHilbertSignedDirichletHomeomorph_sign`, `NLS.ZakharovShabat.existsUnique_isospectral_source_with_signed_dirichletData`, `NLS.ZakharovShabat.sourceSignedDirichletSheet_sign_zero_iff_endpoint`, `NLS.ZakharovShabat.isQuotientMap_sourceSignedDirichletSheet_branches`.

The parameterization uses the original Hilbert topology and includes infinitely many open gaps and endpoint data. Indexed spectral flows are not being identified with ordinary physical NLS time. The dynamical clause remains unresolved, so this passage is partial.

### S7-003: Compact connected tori, exact dimension and generic infinitely many gaps

- The original Hilbert isospectral set is compact and connected and is homeomorphic to a product of circles indexed by its noncollapsed gaps.
- Its covering dimension equals the number of open gaps, including infinity. Infinite dimension holds on a residual set of real Hilbert sources.

Public evidence: `NLS.ZakharovShabat.sourceHilbertIsospectralSet_compact_connected`, `NLS.ZakharovShabat.sourceHilbertIsospectralSet_homeomorphic_circles`, `NLS.ZakharovShabat.sourceHilbertIsospectralSet_coveringDimension_eq_gapCount`, `NLS.ZakharovShabat.eventually_residual_sourceHilbertIsospectralSet_infinite_coveringDimension`.

Dimension is the proved numerical covering dimension in the original Hilbert topology. Generic means residual. This is not a comparison with the exact construction of the cited 2014 edition.

### S7-004: Squared gaps determine the periodic spectrum

- Equality of the complete indexed sequences of squared periodic gaps for two real Hilbert sources implies equality of their full original periodic spectra and all algebraic multiplicities.

Public evidence: `NLS.ZakharovShabat.source_isospectral_of_squared_gaps`.

The global Hilbert theorem has no assumed injectivity premise and no finite-gap restriction. No corresponding surjectivity claim at p>2 is inferred.

### S7-005: Action radii and Dirichlet angles

- The original action factors as its actual squared gap times a differentiable normalized factor on a neighborhood of each real source. The factor is real and strictly positive at every real source, including collapsed gaps.
- The real rectangular Birkhoff coordinates satisfy x_n^2+y_n^2=2 I_n. Their sine/cosine action-angle expression uses the original signed Dirichlet eta and beta data.

Public evidence: `NLS.ZakharovShabat.exists_local_sourceNormalizedActionComplexExtension_differentiableOn`, `NLS.ZakharovShabat.sourceNormalizedActionComplexExtension_im_eq_zero_of_realType`, `NLS.ZakharovShabat.sourceNormalizedActionComplexExtension_re_pos_of_realType`, `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_action_radius`, `NLS.ZakharovShabat.SourceSection14OriginalData.real_rectangular_formula_of_eta`.

The informal squared-radius description has the exact factor two in rectangular coordinates. Angles require the selected gap to be open; the action-radius identity includes collapsed gaps. The literal path formula is compared in S7-012. The exact cited 2014 construction remains a separate comparison.

### S7-006: Classical fundamental solution and discriminant trace

- The original L2 fundamental solution has identity initial matrix and uniquely solves the integral equation; it satisfies the physical differential equation almost everywhere and recovers the classical solution for continuous inputs.
- The discriminant is the trace of its time-one monodromy. It agrees with the canonical source discriminant and is jointly analytic in the spectral parameter and physical L2 potential.

Public evidence: `NLS.ZakharovShabat.l2FundamentalMatrix_zero`, `NLS.ZakharovShabat.l2SolutionCurve_eq_integral`, `NLS.ZakharovShabat.l2SolutionCurve_unique_integral`, `NLS.ZakharovShabat.ae_physicalOperator_l2SolutionCurve`, `NLS.ZakharovShabat.l2FundamentalMatrix_of_continuous`, `NLS.ZakharovShabat.canonicalDiscriminant_eq_l2_source`, `NLS.ZakharovShabat.analyticOnNhd_l2Discriminant_joint`.

The source is the unit-period coefficient pair with its physical L2 realization. For L2 input the differential equation is asserted almost everywhere; a pointwise equation for arbitrary representatives is not required.

### S7-007: Periodic zeros and normalized product (2.1)

- The original periodic spectrum is exactly the zero set of the entire physical trace expression Delta^2-4.
- The literal symmetric endpoint products in (2.1) converge locally uniformly on the whole complex plane to that expression, with leading factor -4 and denominator pi_n^2, where pi_0=1 and pi_n=n*pi otherwise.

Public evidence: `NLS.ZakharovShabat.l2Discriminant_sq_eq_four_iff`, `NLS.ZakharovShabat.sourceSection7_periodic_product`, `NLS.ZakharovShabat.canonicalPeriodicEndpoints_product`, `NLS.ZakharovShabat.canonicalPeriodicProduct_eq_l2Discriminant`.

The product uses the actual indexed endpoints and includes spectral zeros and multiple zeros. Symmetric finite cutoffs specify the infinite product. No nonvanishing restriction is introduced.

### S7-008: Arnold action formula (2.2)

- The physical indexed action equals the actual contour integral of z*Delta-prime divided by the canonical root, with the exact factor 1/pi.
- A positive isolating circle exists for every real Hilbert source and index, including collapsed gaps; the general circuit formula retains the winding-one and isolation assumptions.

Public evidence: `NLS.ZakharovShabat.physicalIndexedAction_eq_circuit`, `NLS.ZakharovShabat.physicalIndexedAction_eq_circle`, `NLS.ZakharovShabat.exists_physicalIndexedAction_circle`, `NLS.ZakharovShabat.physicalActionContour_eq`.

Circuits are piecewise C1, lie inside one original isolating disc away from its selected closed gap, and have winding one around its midpoint. The formula uses the original physical trace and canonical root, not a renamed model integral.

### S7-009: Contour orientation, canonical root domain and sign

- The canonical root is analytic off the union of all closed periodic gap segments and its square is the canonical discriminant squared minus four.
- On the nonempty real band strictly between the right endpoint of gap zero and the left endpoint of gap one, i times the root is real and strictly positive.

Public evidence: `NLS.ZakharovShabat.sourceCanonicalRootDomain`, `NLS.ZakharovShabat.sourceCanonicalRoot_analyticOnNhd`, `NLS.ZakharovShabat.sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four`, `NLS.ZakharovShabat.sourceRealBand_nonempty`, `NLS.ZakharovShabat.sourceSection7_canonical_root_sign`.

The sign is the displayed strict-band convention, with no value on a removed cut asserted. Counterclockwise orientation is the winding-one condition in S7-008. These facts hold for every finite p>1, hence in the Hilbert case.

### S7-010: One common analytic action neighborhood

- There is one open complex neighborhood containing the entire real source locus on which every indexed original action is analytic.

Public evidence: `NLS.ZakharovShabat.exists_sourceAction_common_analytic_neighborhood`.

The same neighborhood works for all indices; it is not an intersection with separate action domains. The theorem holds at each finite p>1, including p=2.

### S7-011: Classical anti-discriminant

- The physical anti-discriminant is the sum of the two off-diagonal entries of the actual time-one fundamental matrix.
- It agrees with the source anti-discriminant candidate and the continuous classical formula, and is jointly analytic in the spectral parameter and physical L2 input.

Public evidence: `NLS.ZakharovShabat.l2AntiDiscriminant`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_l2`, `NLS.ZakharovShabat.l2AntiDiscriminant_of_continuous`, `NLS.ZakharovShabat.analyticOnNhd_l2AntiDiscriminant_joint`.

Anti-trace means the off-diagonal sum. It is not the difference of the diagonal entries.

Section7OpeningSourceComparison-2026-10-29 in the
[source-review index](source-review-index.json) records these eleven passages.
The new direct interfaces are in
[SourceIsospectralPartition.lean](../NLS/ZakharovShabat/SourceIsospectralPartition.lean)
and [SourceSection7ClassicalOverview.lean](../NLS/ZakharovShabat/SourceSection7ClassicalOverview.lean).

## Reviewed remaining passages

### S7-012: Angle formula (2.3), admissible paths and terminal root sign

- On the unchanged original complex domain, with only the selected gap required to be open, there exist original isolating circles and C1 paths from each left endpoint to its actual Dirichlet eigenvalue.
- Every selected numerator integral is integrable. The continued root at each terminal equals the actual anti-discriminant, including zero terminal values. The off-diagonal integrals form an absolutely convergent series.
- The literal diagonal integral plus that series differs from the original angle by an integer multiple of 2*pi. Normalized integrable diagonal choices have the same angle class; the off-diagonal values are independent of admissible integrable choices.

Public evidence: `NLS.ZakharovShabat.SourceLemma12_12Data.section7_exists_angle_path_sum`, `NLS.ZakharovShabat.SourceLemma12_12Data.section7_exists_angle_path_sum_of_circles`, `NLS.ZakharovShabat.sourceSection13OriginalDomain`, `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_integral_choice_period`, `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_im_eq_zero`, `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_local_representative`, `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_pathIntegral_eq_value`, `NLS.ZakharovShabat.SourceLemma12_12Data.original_theta_common_domain`.

All geometry and integrability are constructed for the existence formula. Comparison of arbitrary supplied paths retains the stated admissibility and integrability hypotheses (including the quadratic model integrand for diagonal path comparisons); no claim is made that every C1 path is automatically integrable. Off-diagonal gaps may be collapsed. Real sources give real angles, and analytic representatives are local modulo pi.

### S7-013: Psi product, asymptotics and period normalization

- The corrected literal symmetric psi product converges at every spectral point, retaining -2/pi_n outside the product and using pi_m for each retained factor, with pi_0=1.
- The actual psi candidate is entire. At p=2 the constructed deleted root displacements belong to l2; the simultaneous family has exact Kronecker periods with factor 1/(2*pi) on every admissible original winding-one circuit.
- The real root sequence solving the original equation is unique within the original real placement domain. An unrestricted characterization among all entire products with l2 displacements has not been established by this comparison.

Public evidence: `NLS.ZakharovShabat.sourceSection7_psi_product`, `NLS.ZakharovShabat.analyticOnNhd_sourcePsiCandidate`, `NLS.ZakharovShabat.sourceTheorem12_1`, `NLS.ZakharovShabat.SourceTheorem12_1Data.circuit`, `NLS.ZakharovShabat.SourceLemma12_10Data.original_diagonal_raw_circuit`, `NLS.ZakharovShabat.SourceLemma12_4Data.originalRealSolution_unique`, `NLS.ZakharovShabat.SourceLemma12_4Data.existsUnique_originalRealSolution`.

The printed repeated denominator pi_n is corrected to pi_m by a positive convergence theorem; no additional refutation is added. Existing uniqueness requires real roots placed in assigned original isolating discs, which are then proved to lie in the gaps. That premise is not explicit in the overview characterization, so its unrestricted uniqueness clause remains unresolved and this group is partial.

### S7-014: Angle conventions and the collapsed-gap locus

- The actual real angle is defined modulo 2*pi on its open-gap locus, with local analytic representatives modulo pi.
- The actual real Hilbert squared-gap zero set has a global analytic chart onto a closed coordinate plane of real codimension two. Its tangent space is the kernel of a surjective two-coordinate differential and equals the space of velocities of curves in the zero set.

Public evidence: `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_local_representative`, `NLS.ZakharovShabat.physicalClosedGap_global_chart`, `NLS.ZakharovShabat.physicalGapCoordinates_fderiv_surjective`, `NLS.ZakharovShabat.physicalSquaredGap_zero_iff_closed`, `NLS.ZakharovShabat.mem_physicalClosedGapTangent_iff_curve`, `NLS.ZakharovShabat.physicalClosedGapTangent_codimension_two`.

The corrected real codimension is two. The original physical Hilbert space and squared-gap locus are retained; no complex codimension claim is inferred. Existing positive geometry supplies this comparison without a new counterexample.

### S7-015: Hilbert canonical Poisson relations

- At the Hilbert exponent, the actual action derivatives commute; the angle/action bracket is the Kronecker delta and the angle/angle bracket vanishes on exactly the stated open-gap domains.

Public evidence: `NLS.ZakharovShabat.sourceTheorem7_1`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.corollary13_2_regular`, `NLS.ZakharovShabat.sourceAction_fourier_bracket_eq_zero`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaTheta_fourier_bracket_eq_zero`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaAction_fourier_bracket_eq_kronecker`.

Specialize the finite-p theorem to p=2. The Fourier brackets are absolutely convergent pairings of actual derivatives, with frequency reversal and physical sign -i. Only gaps belonging to angle variables must be open; action gaps may be collapsed.

### S7-016: Rough Fourier-Lebesgue input and non-measure assertion

- For every finite p>2, there is an actual real Fourier-Lebesgue source pair whose first original unit-period distribution is not represented by any complex measure.
- The second component is the conjugate reflection of the first component coefficients, so the obstruction lies in the dissertation real source space.

Public evidence: `NLS.ZakharovShabat.exists_real_source_first_component_not_measure`.

The theorem reuses the existing non-measure distribution and supplies its real source pair. The sentence about standard ODE theory is motivation: no impossibility of every possible generalized fundamental-solution theory is asserted.

### S7-017: Entire product extension and agreement with classical discriminant

- The corrected even spectral product plus two defines the actual source discriminant, jointly entire in the spectral parameter and finite-p source pair for p>1.
- Above two it agrees with the physical Hilbert monodromy trace along the Hilbert inclusion; below two it is the restriction to the stronger source space. Classical finite Fourier agreement uniquely determines the jointly continuous extension.

Public evidence: `NLS.ZakharovShabat.canonicalDiscriminant`, `NLS.ZakharovShabat.analyticOnNhd_canonicalDiscriminant_periodOne`, `NLS.ZakharovShabat.sourceDiscriminant_eq_l2_of_two_le`, `NLS.ZakharovShabat.sourceDiscriminant_eq_l2_of_le_two`, `NLS.ZakharovShabat.sourceDiscriminant_finite_eq_classical`, `NLS.ZakharovShabat.sourceDiscriminant_unique_joint_continuous`.

The normalization is the already corrected parity product. The discriminant is not obtained by arbitrarily choosing a square root of the full product. All source norms and the direction of each exponent inclusion are retained.

### S7-018: Extended roots, actions, psi, anti-discriminant and density transfer

- The canonical root is the limit of the actual root products and is analytic off the original cuts. The original contour action construction extends to every finite p>1 on a common complex neighborhood.
- The normalized psi family and actual anti-discriminant are constructed; the latter is the difference of the two auxiliary characteristic products and agrees with the classical anti-trace at Hilbert inputs. The angle is the constructed path sum in S7-012.
- The canonical relations hold for every finite p>1. Angle commutation above two follows through finite Fourier real sources and norm density; below two it follows by restriction of the actual regular cotangents.

Public evidence: `NLS.ZakharovShabat.tendsto_sourceCanonicalRootPartialProduct`, `NLS.ZakharovShabat.sourceCanonicalRoot_analyticOnNhd`, `NLS.ZakharovShabat.exists_sourceAction_common_analytic_neighborhood`, `NLS.ZakharovShabat.sourceTheorem12_1`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_products`, `NLS.ZakharovShabat.analyticOnNhd_sourceAntiDiscriminantCandidate_joint`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_l2`, `NLS.ZakharovShabat.SourceLemma12_12Data.section7_exists_angle_path_sum`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaThetaBracket_eq_zero_of_two_le`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaRegularCotangent_bivector_eq_zero`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.corollary13_2_regular`.

This matches the mathematical construction and transfer claims, not a textual comparison with the exact cited 2014 procedure, which remains open. The separate unrestricted psi-characterization clause in S7-013 is not discharged here. Finite Fourier support in the density proof does not mean finitely many open gaps.

### S7-019: Theorem 7.1 common neighborhood and analytic actions

- For each finite p>1 there is one open complex neighborhood containing the entire real source locus on which every indexed action is complex analytic, and hence real analytic.
- The same constructed neighborhood also supports the open-gap angle phases and local representatives.

Public evidence: `NLS.ZakharovShabat.sourceTheorem7_1`, `NLS.ZakharovShabat.SourceTheorem7_1Data.actions_analytic`, `NLS.ZakharovShabat.SourceTheorem7_1Data.real_subset`, `NLS.ZakharovShabat.SourceTheorem7_1Data.local_angles`.

The neighborhood is common to all indices. No restriction to a bounded source set, finite number of indices or finite-gap sources is introduced.

### S7-020: Theorem 7.1 real mod-2pi angles and mod-pi extension

- On the real open-gap locus, the actual angle is a Real.Angle class, with a unit-modulus exp(i*theta) phase. Its square is the complex analytic exp(2*i*theta) phase.
- At every point of the complex open-gap domain there is a local analytic representative, real on real sources, whose differential is the actual angular differential.

Public evidence: `NLS.ZakharovShabat.SourceTheorem7_1Data.real_angle_phase`, `NLS.ZakharovShabat.SourceTheorem7_1Data.angle_phase_analytic`, `NLS.ZakharovShabat.SourceTheorem7_1Data.local_angles`, `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_phase`, `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_local_representative`.

The source wording is interpreted with its explicit modular conventions: real angles modulo 2*pi and complex analytic continuation modulo pi. No globally single-valued real representative or angle at a collapsed selected gap is claimed.

### S7-021: Theorem 7.1 exact canonical relations and domains

- All three canonical identities hold for the same constructed family at every finite p>1 on precisely their source domains.
- The brackets have literal absolutely convergent Fourier formulas using the actual action and angle differentials, frequency reversal and the factor -i. Action/action requires no open gap, angle/action requires only the angle gap, and angle/angle requires both angle gaps.

Public evidence: `NLS.ZakharovShabat.sourceTheorem7_1`, `NLS.ZakharovShabat.SourceTheorem7_1Data.canonical`, `NLS.ZakharovShabat.sourceAction_pairing_summable_norm`, `NLS.ZakharovShabat.sourceAction_fourier_bracket_eq_zero`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaTheta_pairing_summable_norm`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaTheta_fourier_bracket_eq_zero`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaAction_pairing_summable_norm`, `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaAction_fourier_bracket_eq_kronecker`.

The actual regular cotangents identify these formulas with the source bracket above two and extend the literal convergent pairing below two. The range is strictly 1<p<infinity.

Section7RemainingSourceComparison-2026-10-29 in the
[source-review index](source-review-index.json) records these ten passages.
The new direct interfaces are [the corrected product](../NLS/ZakharovShabat/SourceSection7PsiProduct.lean),
[the constructed angle path sum](../NLS/ZakharovShabat/SourceSection7AngleFormula.lean)
and [the actual real rough source](../NLS/ZakharovShabat/SourceSection7RoughInput.lean).

## Remaining work

Resolve the physical NLS motion clause in S7-002 and the unrestricted
psi-function characterization in S7-013. The source-wide assertion inventory,
exact cited 2014 Birkhoff construction and Appendix G.2 norm interpretation
remain unfinished. A completed ordered comparison does not certify all its
passages as proved.
