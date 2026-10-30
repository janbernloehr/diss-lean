# Section 16 ordered assertion comparison

All 27 ordered Section 16 passage groups are compared: 20 matched and seven corrected. Two new positive theorems prove the intermediate rectangular gradient estimates in the source operator norm and in physical Holder-conjugate pair norms for actual sequence entries. They retain all real spectral finite-gap sources, all signed indices and every finite p>1, with y in the second expression. The positive quotient-product convention, negative y term in Fourier reconstruction and bounded inverse norm in the cutoff estimate are retained directly. Two further positive theorems prove the separate own-index quotient-product and psi-numerator asymptotics for the original n-dependent root family at every real source, without a finite-gap hypothesis. One common majorant is chosen before the deleted and sampled indices. The auxiliary asymptotic retains its separate Banach-analytic lp sequence proof on the unchanged complex W. The full Birkhoff map and its actual Jacobian retain the compatible V inside W containing the entire real locus. The exact cited 2014 edition, earlier source qualifications and the wider dissertation inventory remain unresolved. No new refutation is added.

Source: printed pp. 75–77, text lines 6109–6343. Line numbers count newline characters,
preserving form-feed characters. All three rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S16-001 | 6111–6118 | Analyticity of the actual operator-valued Jacobian. | matched |
| S16-002 | 6120–6130 | Physical conjugate gradients represent the entire Jacobian. | matched |
| S16-003 | 6131–6137 | The signed free Fourier modes and period convention. | matched |
| S16-004 | 6147–6159 | The free rectangular gradients and exact Fourier Jacobian. | matched |
| S16-005 | 6161–6165 | Lemma 16.1 in the full physical conjugate pair norm. | matched |
| S16-006 | 6167–6172 | Equation (3.3) at real collapsed gaps. | matched |
| S16-007 | 6174–6179 | The positive quotient product and its analytic auxiliary. | corrected |
| S16-008 | 6181–6186 | Finite-gap regularity and existence of conjugate gradients. | matched |
| S16-009 | 6188–6190 | The two G.7 estimates used in Lemma 16.1. | matched |
| S16-010 | 6191–6198 | Anti-discriminant samples and the moving-root derivative term. | matched |
| S16-011 | 6200–6203 | The G.6 anti-discriminant gradient error. | matched |
| S16-012 | 6205–6208 | Separate own-index product asymptotics and the resulting auxiliary error. | matched |
| S16-013 | 6211–6214 | Uniform auxiliary gradients and the delta times gradient term. | matched |
| S16-014 | 6216–6223 | The auxiliary-weighted anti-discriminant error. | matched |
| S16-015 | 6226–6240 | Combining the errors and including the finite open-gap head. | matched |
| S16-016 | 6250–6258 | Lemma 16.2 for the actual rectangular coordinate gradients. | matched |
| S16-017 | 6260–6263 | The rectangular formula used in the product rule. | matched |
| S16-018 | 6264–6269 | Root error, finite-gap beta decay, vanishing tail and Cauchy bounds. | matched |
| S16-019 | 6270–6274 | The two intermediate rectangular gradient estimates, with y corrected. | corrected |
| S16-020 | 6276–6283 | Normalization by the exact free Fourier inverse. | matched |
| S16-021 | 6284–6289 | Unconditional inverse Fourier reconstruction with the corrected sign. | corrected |
| S16-022 | 6290–6297 | Equation (3.4) for every complex source and input vector. | corrected |
| S16-023 | 6300–6303 | Lemma 16.3: isomorphism equivalence and analytic compact perturbation. | matched |
| S16-024 | 6305–6311 | The normalized remainder series. | corrected |
| S16-025 | 6312–6320 | Literal finite-rank gradient-basis cutoffs. | corrected |
| S16-026 | 6322–6337 | A sufficient original-norm tail bound with its reconstruction constant. | corrected |
| S16-027 | 6339–6343 | Operator-norm convergence and compactness at every real source. | matched |

## Compared passages

### S16-001: Analyticity of the actual operator-valued Jacobian.

- The Jacobian is the full complex Frechet derivative of the actual lp-pair-valued Birkhoff map. Differentiating its Banach-valued analyticity gives analytic dependence in bounded-operator norm.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffJacobian`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_analytic`
- `NLS.ZakharovShabat.sourceSection16_original`

The working Chapter 3 domain is the constructed V inside the earlier angular W, as recorded in S14-004. This common restriction contains the whole real source locus.

### S16-002: Physical conjugate gradients represent the entire Jacobian.

- Every bounded coordinate differential has an actual pair of Holder-conjugate Fourier sequences. Frequency reversal gives the physical gradient convention for the unconjugated bilinear variation formula.
- The pairing with every complex input vector equals the corresponding actual Jacobian coordinate at every point of V. The conjugate exponent is finite because 1<p<infinity.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.jacobian_gradients`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_coordinates`
- `NLS.CoeffPair.dualPairing_conjugateGradient`

The phrase L2-gradient denotes this extension of the physical bilinear gradient convention; literal square-integrable representatives are not asserted at arbitrary complex sources for every p.

### S16-003: The signed free Fourier modes and period convention.

- In the period-one coefficient convention the physical e_plus at -2n is the second component at -n, and e_minus at -2n is the first component at n. The period-two realization doubles these frequencies.
- The explicit free gradients and their recovered coefficients use these same component placements and signs for positive, central and negative indices.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffFreeXGradient`
- `NLS.ZakharovShabat.sourceBirkhoffFreeYGradient`
- `NLS.ZakharovShabat.conjugateGradient_sourceGapWeightedEtaFreeCotangent`

The factor two belongs to the physical period-two indexing, not to the period-one sequence index.

### S16-004: The free rectangular gradients and exact Fourier Jacobian.

- The free x gradient is minus the sum of the two physical modes divided by sqrt(2). The free y gradient is minus their difference divided by i*sqrt(2), expressed in the component order of the preceding row.
- At zero the actual full derivative equals the explicitly invertible Fourier map for every finite p>1. The Hilbert calculation extends by restriction below two and finite Fourier-support density above two.

Public declarations:

- `NLS.ZakharovShabat.conjugateGradient_sourceBirkhoffFreeCotangents`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.birkhoffXY_fderiv_zero`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_zero`
- `NLS.ZakharovShabat.sourceBirkhoffFourierEquiv`

The mathematical free formula is proved internally. The exact [23] Theorem 17.2 text is not independently certified.

### S16-005: Lemma 16.1 in the full physical conjugate pair norm.

- At every real spectral finite-gap source, both signed original gap-sequence gradient errors have Holder-conjugate pair norms in outer lp. The plus coordinate has free gradient -2 in the second component at -n; the minus coordinate has -2 in the first component at n.
- The proof includes all signed indices and every finite p>1. The finite set of open gaps is included by finite modification.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.lemma16_1`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.gapWeightedEta_lemma16_1`

Finite-gap means finitely many open canonical spectral gaps, with no finite Fourier-support assumption or supplied H1 regularity premise.

### S16-006: Equation (3.3) at real collapsed gaps.

- The actual derivative includes both the fixed-source anti-discriminant derivative and its spectral derivative multiplied by the moving Dirichlet-root derivative.
- Both moving-terminal terms carry the same sign. The delta(mu_n) times auxiliary-derivative term is zero at real collapsed gaps; this vanishing is proved from the actual spectral identity.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.equation3_3`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.gapWeightedEta_fderiv_closed`
- `NLS.ZakharovShabat.sourceGapWeightedEtaClosedCotangent`

The grouping of the printed plus/minus sign in (3.3) is correct. The equation uses the corrected auxiliary from S16-007; no discrepancy is assigned to the grouping.

### S16-007: The positive quotient product and its analytic auxiliary.

- With A the deleted single spectral product and P the omitted standard-root product, the positive quotient product is Q=A/P and the actual psi numerator is -2*A. Consequently phi=Q/psi=-1/(2*P).
- The corrected positive product removes the printed leading minus. The auxiliary extends analytically throughout the original angular W because P is analytic and nonzero at the Dirichlet terminal.
- The literal quotient equals this extension at every real source, where the psi numerator is nonzero. At a general complex point the quotient identification explicitly assumes that numerator is nonzero.

Public declarations:

- `NLS.ZakharovShabat.sourceGapWeightedEtaAuxiliary`
- `NLS.ZakharovShabat.sourceGapWeightedEtaAuxiliary_eq_quotient`
- `NLS.ZakharovShabat.SourceSection15OriginalData.auxiliary_eq_real_quotient`
- `NLS.ZakharovShabat.SourceSection15OriginalData.auxiliary_analytic`

The existing sign correction is retained directly. No new witness or refutation is added, and no global nonvanishing claim for the complex psi numerator is inferred.

### S16-008: Finite-gap regularity and existence of conjugate gradients.

- The spectral finite-gap condition bootstraps the original source to every nonnegative Sobolev weight and therefore to an actual H1 realization. This is derived from the original coefficients.
- The gradients are obtained from full complex differentials on an open neighborhood of the real source. Merely asserting real scalar analyticity would not substitute for this complex differential representation.

Public declarations:

- `NLS.ZakharovShabat.sourceFiniteGap_mem_all_sobolev`
- `NLS.ZakharovShabat.sourceFiniteGap_mem_H1`
- `NLS.ZakharovShabat.sourceFiniteGap_exists_physical_hilbert_domain_below_two`
- `NLS.CoeffPair.conjugateGradient`

Above and below the Hilbert exponent the realization and restriction arguments retain the same physical coefficients.

### S16-009: The two G.7 estimates used in Lemma 16.1.

- The actual midpoint derivatives form an outer lp sequence, and the actual Dirichlet derivatives differ from the free half-sum functional by an outer lp sequence.
- The H1 realization supplies the required hypothesis. Independent Hilbert estimates with the requested outer exponent, followed by bounded restriction, cover p<2. Bounded conjugate-gradient recovery gives the physical pair norms.

Public declarations:

- `NLS.ZakharovShabat.exists_global_source_spectral_gradients_sobolev_memlp`
- `NLS.ZakharovShabat.memlp_source_midpoint_fderiv_below_two`
- `NLS.ZakharovShabat.memlp_source_dirichlet_fderiv_error_below_two`
- `NLS.CoeffPair.memlp_conjugateGradient`

The free modes are those displayed in Section 16. Earlier qualifications on literal Appendix G displays remain in their own comparison records.

### S16-010: Anti-discriminant samples and the moving-root derivative term.

- Both delta(mu_n) and its spectral derivative at the actual Dirichlet roots belong to lp. A common source neighborhood and cutoff give a tail majorant, and finite modification retains all central samples.
- The Dirichlet derivative error is lp and its free functional has a common bound, so the full Dirichlet derivatives are uniformly bounded in n. Multiplication by the lp spectral derivative therefore gives an lp sequence of moving-root cotangents.

Public declarations:

- `NLS.ZakharovShabat.memℓp_sourceAntiDiscriminant_at_dirichletRoots`
- `NLS.ZakharovShabat.exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail`
- `NLS.ZakharovShabat.memlp_sourceGapWeightedEtaClosedCotangent_of_gradient_estimates`

This conclusion holds with the actual roots and source norm. It does not require an estimate uniform over an arbitrary source norm ball.

### S16-011: The G.6 anti-discriminant gradient error.

- At the actual Dirichlet roots, subtracting the free anti-discriminant cotangent gives an outer lp sequence. Multiplication by i identifies the displayed signed cosine times the physical mode difference.
- Physical H1 estimates cover p>=2, and exact derivative restriction from independently summable Hilbert cotangents covers 1<p<2.

Public declarations:

- `NLS.ZakharovShabat.memlp_source_antiDiscriminantCotangent_boundary_error`
- `NLS.ZakharovShabat.memlp_source_antiDiscriminantCotangent_error_below_two`
- `NLS.ZakharovShabat.memlp_source_antiDiscriminant_conjugate_boundary_error`

The spectral variable is held fixed for this cotangent. The separate moving-root contribution is retained in S16-010 and equation (3.3).

### S16-012: Separate own-index product asymptotics and the resulting auxiliary error.

- Two new positive theorems establish Q_n(mu_n)-1 in lp and psi_n(mu_n)+2*cos(pi*n) in lp for the actual original root family, at every real source and every finite p>1. All signed indices, the central head and collapsed gaps are included; no finite-gap hypothesis is needed.
- The shared actual-gap majorant is chosen before both the deleted index and the sampled gap index. Real Dirichlet interlacing permits sampling on the diagonal n=k. Filling the deleted coordinate with its midpoint leaves the deleted numerator unchanged.
- The signed omitted product P differs from cos(pi*n) by an lp sequence and is bounded. The exact identity psi=-2*Q*P then gives the second error as -2*((Q-1)*P+(P-cos(pi*n))). This avoids exchanging the quantifiers in the weaker fixed-family estimates.
- The needed auxiliary conclusion 2*phi_n+cos(pi*n) in lp is already proved directly as a full Banach-analytic sequence on the unchanged complex W. The original preconnected-domain argument fixes and propagates the omitted-product parity branch.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.original_ownIndex_quotient_error_memlp`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_ownIndex_psi_error_memlp`
- `NLS.ZakharovShabat.SourcePsiSquaredGapComplexExtension.exists_local_shared_actualGap_quotient_majorant`
- `NLS.ZakharovShabat.memlp_sourceStandardRootOmittedProduct_boundary_sub_free`
- `NLS.ZakharovShabat.SourceLemma12_12Data.dirichlet_omitted_normalized_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.auxiliary_remainder_analytic`

The positive Q convention from S16-007 is retained. The two separate product estimates are proved for all real sources, a stronger scope than the finite-gap source used here. The full-complex local uniformity and analyticity in the next source sentence concern the auxiliary and are supplied by its separate original-domain theorem. No new refutation is added.

### S16-013: Uniform auxiliary gradients and the delta times gradient term.

- One original-source neighborhood bounds the complete auxiliary error sequence. Nested-ball Cauchy estimates then bound every actual auxiliary Frechet derivative by C and every physical conjugate gradient by 2*C, uniformly in n.
- The lp anti-discriminant samples multiplied by these bounded gradients form an lp sequence. At the real closed gaps used by (3.3) the anti-discriminant sample is exactly zero.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.auxiliary_error_local_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.auxiliary_gradient_local_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.auxiliary_gradient_represents`
- `NLS.memlp_smul_of_bounded_vector`

The local bound is valid at every complex point of the original W; the gradient pairing represents the full actual differential.

### S16-014: The auxiliary-weighted anti-discriminant error.

- The auxiliary is bounded because its signed normalization error is lp. Multiplying it by the G.6 error and the moving-root error therefore preserves lp summability.
- The exact closed-cotangent decomposition also retains the auxiliary normalization error multiplied by the bounded free anti-discriminant cotangent. This accounts for the leading signed mode in the next display.

Public declarations:

- `NLS.ZakharovShabat.sourceGapWeightedEtaClosedCotangent_sub_free`
- `NLS.ZakharovShabat.memlp_sourceGapWeightedEtaClosedCotangent_of_gradient_estimates`
- `NLS.memlp_smul_of_bounded_scalar`
- `NLS.memlp_smul_of_bounded_vector`

The estimates use bounded scalar/vector products in the actual operator norm and then the bounded physical gradient map; no isometric identification of these two norms is assumed.

### S16-015: Combining the errors and including the finite open-gap head.

- Outside the finite set of open gaps the actual eta derivative equals the exact closed-gap expression. Its error from the signed free functional is lp by the three preceding estimates.
- Finite modification supplies the full sequence, including each open gap. Recovering the physical coefficients gives exactly the two -2 free modes in Lemma 16.1, which feed the rectangular estimate.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.gapWeightedEta_fderiv_finiteGap_tail`
- `NLS.ZakharovShabat.memlp_sourceGapWeightedEtaClosedCotangent_finiteGap_all_exponents`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.memlp_gapWeightedEta_fderiv_sub_free_finiteGap_all_exponents`
- `NLS.ZakharovShabat.conjugateGradient_sourceGapWeightedEtaFreeCotangent`

The tail equality is simultaneous in all signed indices and sign parameters. All finite p>1 are retained.

### S16-016: Lemma 16.2 for the actual rectangular coordinate gradients.

- At every real spectral finite-gap source the actual x and y sequence-coordinate gradients differ from their explicit free gradients by outer lp sequences in the full Holder-conjugate pair norm.
- The theorem identifies the scalar and actual sequence derivatives on a neighborhood and covers every finite p>1.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.lemma16_2`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.birkhoff_lemma16_2`

No additional Sobolev or open-gap premise is supplied by the caller.

### S16-017: The rectangular formula used in the product rule.

- The original sequence entries have the sum in x and difference in y, with their exact sqrt(8) and i*sqrt(8) denominators.
- The actual rectangular derivatives are the same normalized sum and difference of the signed weighted derivatives.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.equation3_2`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.birkhoffXY_fderiv_eq_weighted`

These identities retain the common Chapter 3 domain and the original root family.

### S16-018: Root error, finite-gap beta decay, vanishing tail and Cauchy bounds.

- The actual xi-1 sequence is lp at every real source. At a real finite-gap source the beta series has only finitely many nonzero gap-index terms; the reciprocal estimate gives |beta_n|<=K/|n| outside one symmetric cutoff.
- Real interlacing makes the eta coordinates zero at every collapsed gap, hence outside a finite set. The product rule there removes both the normalization and beta derivative terms exactly.
- Separate Cauchy estimates give uniform-in-n bounds for all three full derivatives and their physical gradients. The root bound holds near each real source; beta and eta bounds hold at every point of their original complex domains.

Public declarations:

- `NLS.ZakharovShabat.memlp_sourceNormalizedActionRoot_sub_one`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.betaCorrection_finiteGap_inverse_index_bound`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.birkhoffWeighted_fderiv_closed`
- `NLS.ZakharovShabat.sourceNormalizedActionRoot_gradient_local_bound`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.betaCorrection_gradient_local_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_gradient_local_bound`

For each fixed eta sign the neighborhood and constant precede all n; a finite intersection handles both signs. The beta decay is for the fixed finite-gap source, not uniform over an arbitrary neighborhood of finite-gap sources.

### S16-019: The two intermediate rectangular gradient estimates, with y corrected.

- The new direct theorems prove that dx minus (dz_plus+dz_minus)/sqrt(8), and dy minus (dz_plus-dz_minus)/(i*sqrt(8)), have outer lp source-operator norms.
- The original-family interface gives the same estimates for physical Holder-conjugate gradients of actual sequence entries, with all signed indices and the finite open-gap head included.
- The proof subtracts the normalized eta free-mode errors from the rectangular free-mode errors. Exact cancellation retains both denominators and the sine orientation.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.memlp_birkhoffXY_fderiv_sub_eta_finiteGap`
- `NLS.ZakharovShabat.SourceSection15OriginalData.gradient_reduction_finiteGap`

The printed unscripted z in the second expression is replaced directly by y. Two positive theorems and public examples at p=3/2 and p=4 are added; no refutation is added.

### S16-020: Normalization by the exact free Fourier inverse.

- A_phi is exactly the bounded free Fourier inverse composed with the actual Jacobian. Its difference from identity equals that inverse composed with the actual Fourier remainder.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobian`
- `NLS.ZakharovShabat.sourceBirkhoffFourierEquiv`
- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobian_sub_id`

The inverse is a bounded linear equivalence for every finite p>1. No general-p isometry is assumed.

### S16-021: Unconditional inverse Fourier reconstruction with the corrected sign.

- The inverse of two single output modes at -n is a*d_plus_n minus b*d_minus_n. Mapping the unconditional lp coordinate series through the bounded inverse proves the full reconstruction in the original source norm.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffFourierInverse_single`
- `NLS.ZakharovShabat.sourceBirkhoffFourierInverse_hasSum`

The printed positive y-gradient term is replaced by a negative term. Existing historical sign evidence is preserved without adding a new witness.

### S16-022: Equation (3.4) for every complex source and input vector.

- Substituting the exact coordinate derivatives into the corrected inverse Fourier series gives A_phi h as the sum of dx_{-n}(h)*d_plus_n minus dy_{-n}(h)*d_minus_n.
- The series converges unconditionally in the original source norm at every complex point of V and for every complex input vector. The preceding gradient representation gives the physical pairing interpretation.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.normalizedJacobian_hasSum`
- `NLS.ZakharovShabat.SourceSection16OriginalData.jacobian_gradients`

The corrected negative y term and frequency reversal are retained.

### S16-023: Lemma 16.3: isomorphism equivalence and analytic compact perturbation.

- Composition with the explicit Fourier equivalence transports bounded linear isomorphisms in both directions between the Jacobian and A_phi.
- A_phi varies real analytically on the complete real source space and differs from identity by a compact operator at every real source and every finite p>1.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.lemma16_3`
- `NLS.ZakharovShabat.sourceBirkhoffJacobian_isomorphism_iff_normalized`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.normalizedJacobian_real_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_normalizedJacobian_sub_id`

The isomorphism equivalence is not by itself an invertibility proof; the later Section 17 argument supplies invertibility.

### S16-024: The normalized remainder series.

- Apply the corrected inverse Fourier series to (d_phi Omega-d_0 Omega)h. The two coefficients are the actual rectangular derivative errors, and the y-gradient basis term carries a minus sign.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobian_sub_id`
- `NLS.ZakharovShabat.sourceBirkhoffFourierInverse_hasSum`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_coordinates`

The operator equality is exact. The source series is interpreted with the corrected reconstruction sign.

### S16-025: Literal finite-rank gradient-basis cutoffs.

- The cutoff truncates both actual Fourier-remainder outputs and applies the bounded inverse. Its exact finite sum uses the corrected negative y-gradient term.
- The range lies in the span of the reconstructed x and y coordinate modes in the finite index set. Finite dimensionality proves that the operator has finite rank.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobianCutoff`
- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobianCutoff_apply`
- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobianCutoff_finiteDimensional`

Reindexing n to -n identifies the literal symmetric cutoffs in the source. The construction also permits arbitrary finite index sets.

### S16-026: A sufficient original-norm tail bound with its reconstruction constant.

- The valid operator-norm bound is ||FourierInverse|| times the maximum of the two lp majorant tail norms. These majorants are constructed from the actual rectangular derivative errors at the finite-gap source.
- It follows by coordinate/operator norm bounds, the output product norm, and bounded reconstruction into the genuine source p-norm. This supplies the required vanishing estimate without the printed coefficient-to-source isometry equality.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobianCutoff_error_le`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_jacobianRemainder_rowMajorants_finiteGap`
- `NLS.Coeff.norm_pairOutputCutoff_sub_le`

The existing correction retains the necessary multiplicative operator norm. No new proof that the printed equality is wrong is added.

### S16-027: Operator-norm convergence and compactness at every real source.

- Finite-exponent lp tails tend to zero, so the actual finite-rank cutoffs converge in operator norm at every real finite-gap source, including along the symmetric integer cutoffs.
- Finite-gap sources are proved dense in the original source norm. Continuity of the actual Jacobian and closedness of the compact operators extend compactness to all real sources; bounded Fourier inversion gives the statement for A_phi-identity.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.normalizedCutoff_tendsto`
- `NLS.ZakharovShabat.SourceSection15OriginalData.normalizedCutoff_symmetric_tendsto`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_jacobianRemainder_finiteGap`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.continuous_jacobianRemainder_real`
- `NLS.ZakharovShabat.dense_sourceFiniteGapLocus`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_jacobianRemainder_real`

Analytic dependence supplies continuity, but density and norm-closedness are the additional ingredients needed for this conclusion.

## Evidence and validation

The [new intermediate gradient estimates](../NLS/ZakharovShabat/SourceBirkhoffGradientReduction.lean)
use the existing rectangular and eta free-mode error estimates. The
[new own-index product estimates](../NLS/ZakharovShabat/SourcePsiOwnIndexAsymptotics.lean)
specialize the shared actual-gap majorant to the original Dirichlet roots. The
[original Section 16 interface](../NLS/ZakharovShabat/SourceSection16Original.lean)
retains the actual Jacobian and physical gradients. The
[Fourier reconstruction](../NLS/ZakharovShabat/SourceBirkhoffFourierSeries.lean) and
[normalized cutoffs](../NLS/ZakharovShabat/SourceBirkhoffNormalizedCutoff.lean)
supply the corrected sign and sufficient reconstruction constant.

This comparison freshly inspected 47 module bodies and reused three full readings from
the Section 15 comparison after verifying their exact hashes. It resolves 84 declarations.
Four positive theorems and four public examples are added. The full transitive dependency
graph is covered by the axiom audit, not a fresh semantic reading of every dependency.

The fresh full check passed 8,559 build jobs, all 7,635 public examples and the transitive axiom audit of 44,604 NLS declarations. It reported 21 inherited warnings and no new warnings. Four new examples exercise the gradient and product estimates at p=3/2 and p=4, including ambient interval notation. Source hashes, declaration references, review integrity and documentation links are checked separately; those checks do not certify mathematical completeness.

Next: continue the ordered comparison with Section 17, Diffeomorphism property.
