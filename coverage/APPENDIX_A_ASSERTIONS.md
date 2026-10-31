# Appendix A ordered assertion comparison

The ordered Appendix A comparison covers 32 groups on printed pp.121–124: 27 matched, four directly corrected and one contextual, with no partial or pending groups in this local comparison. Original smooth-test distributions, physical Lp quotients, positive periods, normalized 1/L actions, exact Section 2 weights and all stated exponent ranges are retained. Corrections keep weighted-c0 norm convergence at infinity, explicitly rescale the printed chirp to the physical period, retain the Holder product factor C_p<=2*p, and use the original weight in its proof. A.3, A.5 and A.6 retain their source assertions and witnesses. This comparison adds no Lean proof or refutation and does not repeat every transitive dependency proof. The four Section 28 complex intermediate qualifications and broader completeness qualifications remain.

Source: printed pp.121–124, text lines 9915–10157. Line numbers count
newline characters and preserve form feeds. All four rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| A-001 | 9919–9927 | Smooth periodic test functions and derivative norms | matched |
| A-002 | 9929–9932 | Frechet property and density in continuous functions | matched |
| A-003 | 9933–9939 | Original distribution dual and finite-order criterion (A.1) | matched |
| A-004 | 9942–9943 | Least distribution order | matched |
| A-005 | 9944–9950 | Unique continuous extension and complex measure representation (A.2) | matched |
| A-006 | 9953–9956 | Regular complex Borel measures and order-zero equivalence | matched |
| A-007 | 9956–9960 | Original normalized L1 action | matched |
| A-008 | 9971–9976 | Fourier coefficients and uniqueness | matched |
| A-009 | 9978–9980 | Theorem A.1(i), growth at the least order | matched |
| A-010 | 9982–9988 | Theorem A.1(ii), polynomial synthesis and uniqueness | matched |
| A-011 | 9990–9993 | Distributional derivative and physical Fourier multiplier | matched |
| A-012 | 9995–10004 | Original Fourier-Lebesgue spaces, norms, completeness and reflexivity | matched |
| A-013 | 10005–10011 | Fourier-series norm convergence and infinity endpoint | corrected |
| A-014 | 10012–10015 | Sobolev identification, physical L2 and Parseval | matched |
| A-015 | 10017–10023 | L1 Fourier bound and interpolation transition | matched |
| A-016 | 10034–10036 | Lemma A.2 conjugate exponent embedding | matched |
| A-017 | 10039–10044 | Lemma A.3 one distribution in all FLp above two that is not a measure | matched |
| A-018 | 10047–10052 | Absolute Fourier synthesis and continuous representative | matched |
| A-019 | 10054–10056 | Wiener algebra and pseudomeasure dual | matched |
| A-020 | 10057–10060 | Lemma A.4 reverse conjugate exponent embedding | matched |
| A-021 | 10063–10068 | Lemma A.5 one continuous function outside all FLp below two | matched |
| A-022 | 10070–10074 | Printed chirp and its physical period | corrected |
| A-023 | 10076–10077 | Remark A.6 Riemann-Lebesgue decay | matched |
| A-024 | 10077–10083 | Remark A.6 nonsurjectivity and contextual characterization | matched |
| A-025 | 10086–10094 | Convolution criterion, growth and convergence conventions | matched |
| A-026 | 10105–10109 | Lemma A.7 product and exact Young bound (A.3) | matched |
| A-027 | 10111–10118 | Lemma A.8 embedding and corrected product constant (A.4) | corrected |
| A-028 | 10120–10129 | Inverse-weight Holder factor and physical weight convention | corrected |
| A-029 | 10132–10134 | Interval sources and periodic boundary mismatch | contextual |
| A-030 | 10136–10140 | Lemma A.9 exponent ranges, including half regularity | matched |
| A-031 | 10142–10143 | Subcritical interval-periodic Sobolev identification | matched |
| A-032 | 10144–10155 | Holder proof, reciprocal exponent and endpoint handling | matched |

## Compared passages

### A-001: Smooth periodic test functions and derivative norms

- Tests are actual smooth complex-valued functions of arbitrary positive physical period L.
- The Nth defining norm is the sum of the physical derivative sup norms from order zero through N.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.smooth`
- `NLS.Fourier.SmoothPeriodicTest.periodic`
- `NLS.Fourier.SmoothPeriodicTest.cNorm_apply`

The topology and norm are on the original function carrier, with derivatives in the physical x variable.

### A-002: Frechet property and density in continuous functions

- The closed compatible derivative-jet realization gives the complete, metrizable, locally convex test topology.
- Original smooth periodic tests are dense in continuous functions on the physical circle.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.derivativeJetEquiv`
- `NLS.Fourier.SmoothPeriodicTest.isClosed_range_derivativeJet`
- `NLS.Fourier.SmoothPeriodicTest.denseRange_toContinuousCLM`

The public completeness instances were read in full. Density is proved directly; the source citation is not an additional hypothesis.

### A-003: Original distribution dual and finite-order criterion (A.1)

- A distribution is a complex-linear continuous functional on all original smooth tests.
- Continuity is equivalent to one finite derivative order and one strictly positive bound chosen before all tests.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.continuous_iff_finite_order`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.exists_order`

This retains the quantifier order and the strict positivity of the constant in (A.1).

### A-004: Least distribution order

- The order is the least natural number satisfying the finite-order estimate, including for the zero functional.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.order`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.hasOrderAtMost_order`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.order_le`

The chosen order is minimal, rather than an arbitrary available upper bound.

### A-005: Unique continuous extension and complex measure representation (A.2)

- Order zero is equivalent to a unique continuous extension to the physical continuous-function space.
- Every such extension has a unique complex-measure representation with the exact factor 1/L.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.order_zero_iff_physical_extension`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.existsUnique_normalized_measure`
- `NLS.Fourier.complexMeasureContinuousIntegral_surjective`

The measure representation and continuous integral modules were read in full; the normalized action is retained.

### A-006: Regular complex Borel measures and order-zero equivalence

- Actual complex measures have finite variation and regular variation on the compact physical circle.
- They correspond bijectively to original distributions of least order zero.

Public declarations:

- `NLS.Fourier.complexMeasure_finite_variation`
- `NLS.Fourier.complexMeasure_variation_regular`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.complexMeasureOrderZeroEquiv`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.order_zero_iff_measure`

The Radon qualification uses the actual Borel measure and its variation, not a renamed bounded functional.

### A-007: Original normalized L1 action

- An interval-integrable function defines an order-zero original distribution with action (1/L) times the integral of the function times the test.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.ofL1_apply`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.ofL1_order`

The pairing is complex bilinear and contains no implicit conjugation.

### A-008: Fourier coefficients and uniqueness

- The nth coefficient is evaluation on the negative physical mode exp(-i*2*pi*n*x/L).
- All coefficients determine the original distribution uniquely and agree with normalized integrals on L1 data.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.mode_apply_physical`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.ext_coefficients`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.ofL1_coefficient`

Positive periods and signed indices, including zero, are retained.

### A-009: Theorem A.1(i), growth at the least order

- A distribution with finite order N has cofinite two-sided Fourier growth O(|n|^N), with the same N.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.coefficients_isBigO_of_order`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.hasOrderAtMost_order`

The claim includes N=0 and applies in particular at the least order. The asymptotic does not restrict the zero Fourier coefficient.

### A-010: Theorem A.1(ii), polynomial synthesis and uniqueness

- Every polynomially growing complex sequence has exactly one realization on all original smooth periodic tests.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.existsUnique_of_polynomial_isBigO`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.polynomial_growth_iff_existsUnique`

The coefficient at zero is arbitrary, and uniqueness is on the full original distribution space.

### A-011: Distributional derivative and physical Fourier multiplier

- The distributional derivative is minus the transpose of the physical test derivative.
- Its nth coefficient is i*2*pi*n/L times the original coefficient.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.derivative_apply`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.derivative_coefficient`

The formula includes negative and zero frequencies and arbitrary positive periods.

### A-012: Original Fourier-Lebesgue spaces, norms, completeness and reflexivity

- The original Fourier-Lebesgue subtype has exactly the weighted coefficient norm.
- It is complete for all Banach exponents and reflexive for 1<p<infinity.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.coefficientsIsometry`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_eq`
- `NLS.Fourier.PeriodicFourierLebesgue.completeSpace`
- `NLS.Fourier.PeriodicFourierLebesgue.bidual_surjective`

The Sobolev weight is the Section 2 weight (1+|n|)^s. Its tempered inverse supplies the original distribution realization.

### A-013: Fourier-series norm convergence and infinity endpoint

- Finite Fourier polynomials converge in the original Fourier-Lebesgue norm for every finite Banach exponent.
- At infinity, this norm convergence holds exactly when the weighted coefficients tend to zero.
- For every exponent, the same truncations converge when evaluated against each original smooth test.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.tendsto_truncate`
- `NLS.Fourier.PeriodicFourierLebesgue.tendsto_truncate_top_iff`
- `NLS.Fourier.PeriodicFourierLebesgue.truncate_eq_ofContinuous`
- `NLS.Fourier.PeriodicFourierLebesgue.tendsto_truncate_action`

Retain the weighted-c0 condition at infinity. Testwise convergence is not asserted to be strong-dual convergence. No new refutation is needed.

### A-014: Sobolev identification, physical L2 and Parseval

- The p=2 Fourier-Lebesgue norm is the Fourier definition of the Sobolev norm.
- At s=0 it is isometric to the actual physical L2 quotient under normalized Haar measure, with the exact 1/L interval Parseval factor.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.l2Isometry`
- `NLS.Fourier.PeriodicFourierLebesgue.l2Isometry_norm`
- `NLS.Fourier.PeriodicFourierLebesgue.l2Isometry_parseval_interval`

The normalization is explicit. The later interval Sobolev equivalence is not claimed to be an isometry.

### A-015: L1 Fourier bound and interpolation transition

- Every physical L1 Fourier coefficient and the FL-infinity norm are bounded by the normalized L1 norm.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.norm_ofIntervalL1_le`
- `NLS.Fourier.norm_fourierCoeff_le_integral_norm`

The interpolation transition is realized by the continuous maps in A.2; the introductory comparison of spaces is context.

### A-016: Lemma A.2 conjugate exponent embedding

- For 1<=p<=2 and conjugate q, the actual physical Lp quotient embeds continuously and injectively into original FLq, with norm at most one.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.ofLp`
- `NLS.Fourier.PeriodicFourierLebesgue.ofLp_injective`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_ofLp_le`
- `NLS.Fourier.PeriodicFourierLebesgue.ofLp_apply_interval`

The rendered source uses L^(p-prime) to FLp for 2<=p<=infinity. This is the same assertion after renaming the conjugate exponents; the prime is not discarded.

### A-017: Lemma A.3 one distribution in all FLp above two that is not a measure

- One original distribution, chosen before all p>2, belongs to every such FLp including infinity and is not represented by any actual complex measure.

Public declarations:

- `NLS.Fourier.exists_fourierLebesgue_above_two_not_measure`
- `NLS.Fourier.nonMeasureDistribution_not_measure`

This is the source existential assertion A.3. Its witness is retained; it is not an added refutation of a printed formula.

### A-018: Absolute Fourier synthesis and continuous representative

- Original FL1 elements have absolute and uniform physical Fourier synthesis with sup norm bounded by the FL1 norm.
- The resulting uniformly continuous function is the unique continuous representative of the entire distribution.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.hasSum_continuousRepresentative`
- `NLS.Fourier.PeriodicFourierLebesgue.summable_norm_continuousRepresentative`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_continuousRepresentative_le`
- `NLS.Fourier.PeriodicFourierLebesgue.existsUnique_continuousRepresentative`
- `NLS.Fourier.PeriodicFourierLebesgue.uniformlyContinuous_continuousRepresentative`

The convergence is in the actual continuous-function sup norm, at the original physical period.

### A-019: Wiener algebra and pseudomeasure dual

- Original FL1 is a complete commutative normed Wiener algebra with norm-one identity and an injective continuous representative algebra map.
- FL-infinity is isometrically the continuous dual of FL1, with the bilinear pairing using opposite signed Fourier indices.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.wienerContinuousAlgHom`
- `NLS.Fourier.PeriodicFourierLebesgue.continuousRepresentative_injective`
- `NLS.Fourier.PeriodicFourierLebesgue.pseudomeasureDualIsometry`
- `NLS.Fourier.PeriodicFourierLebesgue.unweightedDualEquiv_apply`

The source says this algebra fact is not subsequently used; it is nevertheless implemented on the original distribution carrier.

### A-020: Lemma A.4 reverse conjugate exponent embedding

- For 1<=p<=2, original FLp embeds continuously and injectively into the physical Lq quotient for the conjugate exponent, with norm at most one and a unique representing class.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.lpRepresentative`
- `NLS.Fourier.PeriodicFourierLebesgue.lpRepresentative_injective`
- `NLS.Fourier.PeriodicFourierLebesgue.existsUnique_lpRepresentative`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_lpRepresentative_le`
- `NLS.Fourier.PeriodicFourierLebesgue.lpRepresentative_one`
- `NLS.Fourier.PeriodicFourierLebesgue.lpRepresentative_two`

The conjugate prime was checked on the rendered page. At p=1 the map agrees with continuous synthesis, and at p=2 with the established isometry.

### A-021: Lemma A.5 one continuous function outside all FLp below two

- For every positive period, one continuous function lies outside all original FLp with 1<=p<2.

Public declarations:

- `NLS.Fourier.printedChirpAtPeriod_mem_original_iff`

The proved membership criterion is exactly p>=2, including infinity. The same witness is used for all excluded exponents.

### A-022: Printed chirp and its physical period

- The printed coefficients exp(i*n*log n)/(sqrt(n)*log(n)^2), n>=2, give uniform convergence of ordinary positive-index cutoffs on the entire real line.
- The literal phase exp(i*n*pi*x) has period two. At period L use the explicitly proved rescaling x to 2*x/L, giving phase exp(i*2*pi*n*x/L).

Public declarations:

- `NLS.Fourier.tendstoUniformly_printedChirp_original`
- `NLS.Fourier.periodTwoCoefficient_printedChirpFunction`
- `NLS.Fourier.fourierCoeff_printedChirpAtPeriod`
- `NLS.Fourier.tendstoUniformly_printedChirpAtPeriod_original`

The physical period is corrected directly. The public uniform-convergence interfaces were read; this review does not repeat every transitive oscillatory estimate.

### A-023: Remark A.6 Riemann-Lebesgue decay

- Fourier coefficients of every physical L1 function tend to zero along the cofinite filter on signed integer frequencies.

Public declarations:

- `NLS.Fourier.tendsto_intervalFourierCoefficient_cofinite`
- `NLS.Fourier.tendsto_fourierCoeff_cofinite`
- `NLS.Fourier.circleL1Fourier`

This gives the actual continuous L1-to-c0 Fourier map.

### A-024: Remark A.6 nonsurjectivity and contextual characterization

- The physical L1-to-c0 Fourier map is not surjective; its range is dense and nonclosed.
- The proof uses open mapping and actual Rudin-Shapiro polynomials.

Public declarations:

- `NLS.Fourier.circleL1Fourier_not_surjective`
- `NLS.Fourier.denseRange_circleL1Fourier`
- `NLS.Fourier.not_isClosed_range_circleL1Fourier`

The source remark about a useful characterization remaining unknown is historical context, not a theorem that no characterization can exist. Nonsurjectivity itself is part of A.6.

### A-025: Convolution criterion, growth and convergence conventions

- An original distributional Fourier product exists uniquely exactly when the convolution genuinely converges at each frequency and the resulting coefficients have polynomial growth.

Public declarations:

- `NLS.Fourier.SmoothPeriodicTest.Distribution.exists_unique_fourierProduct_iff`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.exists_unique_symmetricFourierProduct_iff`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.HasFourierProduct.symmetric`

Unordered HasSum and symmetric integer cutoffs have separate explicit criteria. Do not replace convergence by a default-valued tsum or omit output growth. Historical examples are unchanged.

### A-026: Lemma A.7 product and exact Young bound (A.3)

- Every Banach Young triple, including infinity endpoints, gives absolutely convergent convolution coefficients and a unique original product.
- The bilinear product has exact operator norm one and is independent of the representing exponents.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.youngProduct`
- `NLS.Fourier.PeriodicFourierLebesgue.summable_norm_youngProduct_terms`
- `NLS.Fourier.PeriodicFourierLebesgue.youngProduct_unique`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_youngProductCLM`
- `NLS.Fourier.PeriodicFourierLebesgue.youngProduct_eq_of_val_eq`

Agreement with pointwise multiplication is retained for continuous factors when one factor is Wiener. The constant in (A.3) remains one.

### A-027: Lemma A.8 embedding and corrected product constant (A.4)

- For each finite Banach p, the FL^(1,p)-to-FL1 inclusion is continuous, injective and preserves the original distribution.
- The product estimate retains the inverse-weight Holder factor C_p, with C_p<=2*p.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.sobolevToWiener`
- `NLS.Fourier.PeriodicFourierLebesgue.sobolevToWiener_val`
- `NLS.Fourier.PeriodicFourierLebesgue.sobolevToWiener_injective`
- `NLS.Fourier.PeriodicFourierLebesgue.norm_sobolevProduct_le`
- `NLS.WeightedCoeff.sobolevEmbeddingConstant_le_two_mul`

Correct (A.4) directly to norm(u*v)<=C_p*norm(u)*norm(v). The theorem includes p=1 and adds no infinity endpoint or new refutation.

### A-028: Inverse-weight Holder factor and physical weight convention

- C_p is the conjugate-sequence norm of the reciprocal weight (1+|n|)^(-1).
- That reciprocal sequence belongs to every conjugate exponent above one, including infinity, and the original norm convention stays fixed.

Public declarations:

- `NLS.WeightedCoeff.sobolevEmbeddingConstant`
- `NLS.Weight.inverse_sobolev_one_memlp`
- `NLS.WeightedCoeff.norm_sobolevToL1CLM_le`

Use the exact Section 2 weight. The physical rescaling (1+|2*n/L|) in the printed proof is not silently substituted for it. The finite factor is retained in the corrected estimate.

### A-029: Interval sources and periodic boundary mismatch

- Arbitrary interval Sobolev data need not satisfy periodic endpoint matching; the following embeddings accept this general input.

Public declarations:

- `NLS.Fourier.ofL1_mem_fourierLebesgue_of_intervalSobolev`
- `NLS.Fourier.ofL1_mem_fourierLebesgue_of_intervalHalfSobolev`

Read this as motivation about general interval data, not as universal nonmembership in FL1 for every input. No new negative theorem is added.

### A-030: Lemma A.9 exponent ranges, including half regularity

- For 0<=s<1/2, original interval data embeds into FLq whenever q>1/(s+1/2).
- At s=1/2 the result holds for every q>1. L2 supplies all q>=2, including infinity, and ordinary L2 handles s=0.

Public declarations:

- `NLS.Fourier.ofL1_mem_fourierLebesgue_of_intervalSobolev`
- `NLS.Fourier.ofL1_mem_fourierLebesgue_of_intervalHalfSobolev`
- `NLS.Fourier.ofL1_mem_fourierLebesgue_of_intervalL2`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalFourierEmbedding`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalHalfFourierEmbedding`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalL2TargetEmbedding`

Positive regularity uses actual finite Slobodeckij interval energy. No endpoint matching is required, and zero regularity does not use the fractional graph norm at s=0.

### A-031: Subcritical interval-periodic Sobolev identification

- For 0<s<1/2, the genuine intrinsic interval Sobolev space is continuously linearly equivalent to original FL^(s,2).
- Both directions preserve physical representatives and have explicit analysis and synthesis norm bounds.

Public declarations:

- `NLS.Fourier.IntrinsicIntervalSobolev.originalSobolevEquiv`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalSobolevEquiv_ofFunction_val`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalSobolevEquiv_symm_represents`
- `NLS.Fourier.IntrinsicIntervalSobolev.norm_originalSobolevEquiv_le`
- `NLS.Fourier.IntrinsicIntervalSobolev.norm_originalSobolevEquiv_symm_le`
- `NLS.Fourier.PeriodicFourierLebesgue.l2Isometry`

The identification retains the exact Section 2 Fourier weight and physical dilation constants; it is not asserted isometric. The s=0 case is ordinary L2.

### A-032: Holder proof, reciprocal exponent and endpoint handling

- The subcritical Holder argument gives the stated finite exponent range with explicit physical bounds.
- The L2 inclusion handles q>=2 and infinity; the separate half-regularity construction handles q>1.

Public declarations:

- `NLS.Fourier.IntrinsicIntervalSobolev.norm_originalFourierEmbedding_le`
- `NLS.Fourier.IntrinsicIntervalSobolev.norm_originalHalfFourierEmbedding_le`
- `NLS.Fourier.IntrinsicIntervalSobolev.norm_originalL2TargetEmbedding_le`
- `NLS.Fourier.IntrinsicIntervalSobolev.originalFourierEmbedding_eq_originalSobolevEquiv_val`

The reciprocal-exponent formula is used in its finite Holder range. The remaining endpoints use the separate verified maps, preserving the original normalized interval action.

## Evidence and validation

The [test space](../NLS/Fourier/SmoothPeriodicTestSpace.lean) and
[original distributions](../NLS/Fourier/SmoothPeriodicDistribution.lean)
retain the physical functions and their continuous dual. The
[Fourier–Lebesgue spaces](../NLS/Fourier/PeriodicFourierLebesgueSpace.lean),
[corrected Sobolev product](../NLS/Fourier/PeriodicSobolevEmbedding.lean) and
[interval embeddings](../NLS/Fourier/PeriodicIntrinsicSobolevEmbedding.lean)
retain exact weights, normalization and exponent endpoints.

This comparison read 30 complete public module bodies and resolves 104
declarations. It reconciles the prior Appendix A review, including full
reads of the original distribution and continuous-integral modules that
were previously only partly inspected. It does not claim to repeat every
transitive interpolation, fractional-energy or oscillatory-sum argument.
Historical refutations remain unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check recorded at commit cec78d328ace97d075ff5832a67c11eb4da30118: 8,582 build jobs, 7,692 public examples and an axiom audit of 44,706 NLS declarations, with 21 inherited warnings and zero new. All 104 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix B. The
[broader completion qualifications](COMPLETENESS.md) remain.
