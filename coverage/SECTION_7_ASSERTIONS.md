# Section 7: ordered assertion comparison

This ledger follows the extraction order of printed pp.45–47. The unit-period
source space and its physical spectral realization are retained. Of 21 passage
groups, ten are matched, one is partial and ten await this ordered review.
These counts describe review scope, not a completion percentage.

The opening comparison covers S7-001 through S7-011. S7-002 remains partial:
the signed Dirichlet parametrization is proved, while its statement about
motion under physical NLS still needs a direct comparison. Existing focused
proofs of later formulas and Theorem 7.1 remain available in
[Section 7](SECTION_7.md); pending here does not declare those results unproved.
The exact cited 2014 construction remains a separate qualification.

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
| S7-012 | 3381–3396 | Angle formula (2.3), admissible paths and terminal root sign | pending |
| S7-013 | 3397–3410 | Psi product, asymptotics and period normalization | pending |
| S7-014 | 3412–3415 | Angle conventions and the collapsed-gap locus | pending |
| S7-015 | 3416–3418 | Hilbert canonical Poisson relations | pending |
| S7-016 | 3420–3426 | Rough Fourier-Lebesgue input and non-measure assertion | pending |
| S7-017 | 3428–3432 | Entire product extension and agreement with classical discriminant | pending |
| S7-018 | 3433–3438 | Extended roots, actions, psi, anti-discriminant and density transfer | pending |
| S7-019 | 3450–3455 | Theorem 7.1 common neighborhood and analytic actions | pending |
| S7-020 | 3458–3459 | Theorem 7.1 real mod-2pi angles and mod-pi extension | pending |
| S7-021 | 3461–3468 | Theorem 7.1 exact canonical relations and domains | pending |

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

The informal squared-radius description has the exact factor two in rectangular coordinates. Angles require the selected gap to be open; the action-radius identity includes collapsed gaps. The literal path formula is reserved for S7-012. The exact cited 2014 construction remains a separate comparison.

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

## Remaining work

Resolve the physical NLS motion clause in S7-002, then reconcile S7-012
through S7-021 in source order using their actual proofs and domains.
The source-wide assertion inventory, exact cited 2014 Birkhoff construction
and Appendix G.2 norm interpretation remain unfinished.
