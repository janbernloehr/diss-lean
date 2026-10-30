# Section 19 ordered assertion comparison

All 48 ordered Section19 groups are classified: 33 matched, eight corrected or scope-clarified, two partial auxiliary assertions and five contextual groups. The main statements of Lemmas19.1,19.2,19.4 and Corollary19.3 are already proved for the actual canonical primitive on one original source domain. The positive gap-error comparison retains pi*(D*E+abs(critical-midpoint)); critical-point notation, canonical root normalization, selected indices and the local scope at infinity are clarified directly. S19-015 retains the unlinked positive companion minimum and S19-032 the unlinked strict band monotonicity assertion. Neither missing auxiliary statement is assumed in the existing proofs of the main conclusions. The Laurent proof uses internal WKB asymptotics, a local sinh inverse estimate and sampled analytic order in place of the printed principal-arcsine argument. No literal formalization of those intermediate principal-arcsine displays or exact external [23] comparison is claimed. No Lean changes or new refutations are added; wider qualifications remain unresolved.

Source: printed pp. 87–91, text lines 6980–7441. Line numbers count newline
characters and preserve form feeds. All five rendered source pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S19-001 | 6980–6986 | Canonical differential product (4.6). | corrected |
| S19-002 | 6988–6992 | Primitive and finite-gap Laurent overview. | corrected |
| S19-003 | 6993–6996 | Joint and filled spectral analyticity of the differential. | corrected |
| S19-004 | 6997–7006 | Definition by the average of endpoint integrals. | matched |
| S19-005 | 7007–7016 | Improper convergence and admissible path independence. | matched |
| S19-006 | 7017–7021 | Equality of the two endpoint integrals. | matched |
| S19-007 | 7031–7034 | Analytic primitive despite lexicographic endpoint labels. | contextual |
| S19-008 | 7036–7047 | Lemma 19.1(i): joint analyticity and source gradient. | matched |
| S19-009 | 7050–7057 | Lemma 19.1(ii): index shift and endpoint values. | matched |
| S19-010 | 7059–7063 | Lemma 19.1(iii): locally uniform gap bound. | matched |
| S19-011 | 7066–7068 | Lemma 19.1(iv): analyticity of the square. | matched |
| S19-012 | 7071–7074 | Lemma 19.1(v): real arcosh boundary profiles. | matched |
| S19-013 | 7076–7076 | Lemma 19.1(vi): exact free primitive. | matched |
| S19-014 | 7078–7084 | Proof of joint and spectral analyticity. | matched |
| S19-015 | 7085–7092 | Positive real-gap companion expression. | partial |
| S19-016 | 7094–7100 | Local contour and logarithm neighborhood. | corrected |
| S19-017 | 7102–7117 | Logarithmic primitive and gradient formula. | matched |
| S19-018 | 7118–7122 | Analytic continuation of the source derivative. | matched |
| S19-019 | 7132–7139 | Endpoint normalization and primitive shift. | matched |
| S19-020 | 7141–7165 | Signed finite telescoping across bands. | matched |
| S19-021 | 7167–7186 | Real-band canonical root and integral -i pi. | matched |
| S19-022 | 7189–7200 | Canonical denominator in the continued shift formula. | corrected |
| S19-023 | 7201–7210 | Selected-gap differential factorization (4.7). | matched |
| S19-024 | 7213–7223 | Opposite boundary values and analytic square filling. | matched |
| S19-025 | 7224–7234 | Collapsed-gap clause and all-index gap bound. | corrected |
| S19-026 | 7235–7242 | Real-gap integral and arcosh value. | matched |
| S19-027 | 7244–7248 | Free differential and free primitive. | matched |
| S19-028 | 7250–7250 | Notation F=F0. | contextual |
| S19-029 | 7261–7269 | Figure 4.1 boundary sign picture. | contextual |
| S19-030 | 7272–7281 | Lemma 19.2: convergent physical Hamiltonian Laurent series. | matched |
| S19-031 | 7283–7292 | Finite product, exterior growth and coefficient determination. | matched |
| S19-032 | 7293–7301 | Real-band monotonicity and root sign. | partial |
| S19-033 | 7306–7316 | Derivative of the real-band arcsine branch. | matched |
| S19-034 | 7317–7337 | Exact primitive on a real spectral band. | matched |
| S19-035 | 7339–7346 | Half-integer discriminant asymptotics. | matched |
| S19-036 | 7347–7355 | Uniform arcsine error transfer. | matched |
| S19-037 | 7357–7359 | Primitive approximation along half-integer points. | matched |
| S19-038 | 7361–7362 | Hamiltonian convention relative to reference 23. | contextual |
| S19-039 | 7373–7382 | Sine addition, branch selection and Laurent coefficients. | matched |
| S19-040 | 7384–7384 | Transition to the cubic expansion. | contextual |
| S19-041 | 7386–7391 | Corollary 19.3: cubic Laurent part and remainder. | matched |
| S19-042 | 7393–7400 | Lemma 19.4: locally uniform mixed gap error. | matched |
| S19-043 | 7403–7403 | Exact zero-potential error clause. | matched |
| S19-044 | 7406–7413 | Endpoint integral with the selected-gap product. | matched |
| S19-045 | 7416–7418 | Critical displacement and refined product estimate. | matched |
| S19-046 | 7419–7426 | Product-error supremum estimate. | corrected |
| S19-047 | 7428–7435 | Standard-root derivative and elementary primitive. | corrected |
| S19-048 | 7438–7441 | Collapsed gaps and reciprocal-root integral bound. | matched |

## Compared passages

### S19-001: Canonical differential product (4.6).

- The full product uses the critical points lambda_m^bullet, with leading factor -i. It converges unconditionally, and symmetric cutoff products have the same limit.

Public declarations:

- `NLS.ZakharovShabat.sourceCriticalRootRatio_product`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_hasProd`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_symmetricProducts`

Restore the missing critical-point bullet in (4.6). The existing positive product theorem supplies the correction directly.

### S19-002: Primitive and finite-gap Laurent overview.

- The primitive is single valued and analytic on the complement of noncollapsed gaps. At every real finite-gap source it has a convergent physical Hamiltonian Laurent expansion in an exterior region.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.spectral_analytic`
- `NLS.ZakharovShabat.SourceSection19Data.laurent`

The informal meromorphic statement is read at infinity. No global meromorphic continuation through open cuts is claimed.

### S19-003: Joint and filled spectral analyticity of the differential.

- One open moving-cut joint domain supports the actual quotient and primitive differential; spectral slices fill collapsed gaps.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianDifferentialData`
- `NLS.ZakharovShabat.SourceSection19Data.spectral_analytic`
- `NLS.ZakharovShabat.SourceSection19Data.source_derivative`

Read the indexed union in the printed fixed-exterior domain as the union of U_m. The implementation proves joint analyticity on the larger moving-cut domain of a common restricted source neighborhood containing the full real locus.

### S19-004: Definition by the average of endpoint integrals.

- The original definition is the half-average of the two actual improper endpoint integrals, and equals the same normalized primitive.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianEndpointAverage`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointAverage_eq`
- `NLS.ZakharovShabat.SourceSection19Data.endpoint_integrals`

The factor one half is literal; no integral value is supplied as an assumption.

### S19-005: Improper convergence and admissible path independence.

- Every admissible interior C1 path and finite piecewise interior C1 path from either endpoint has the same improper integral. The two truncation parameters tend independently to their endpoints.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.endpointPath_integral`
- `NLS.ZakharovShabat.SourceSection19Data.endpointPiecewisePath_integral`

Convergence follows from the actual primitive derivative and endpoint limits. This replaces the informal singularity argument and needs no separate absolute-integrability premise for the improper limit; interiors and intermediate corners avoid the cuts.

### S19-006: Equality of the two endpoint integrals.

- Each selected endpoint integral equals F_n, including when the gap collapses.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.endpointIntegral_eq`
- `NLS.ZakharovShabat.SourceSection19Data.endpoint_integrals`

The root-complement filter is proved nontrivial at the endpoint, so equality does not come from a vacuous limit.

### S19-007: Analytic primitive despite lexicographic endpoint labels.

- The endpoint-label discussion motivates constructing the analytic primitive without differentiating individual lexicographically chosen endpoints.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianDifferentialData.analytic`

Joint analyticity is proved. This review does not add or claim a standalone theorem that the lexicographic endpoint maps fail continuity.

### S19-008: Lemma 19.1(i): joint analyticity and source gradient.

- The same primitive is jointly analytic off the moving cuts, and its source Frechet derivative is the actual discriminant cotangent divided by the canonical root.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.source_derivative`
- `NLS.ZakharovShabat.SourceFullAbelianDifferentialData.source_hasFDerivAt`

The source domain may be restricted inside the original Birkhoff domain; every real source remains. Spectral analyticity includes filled collapsed gaps.

### S19-009: Lemma 19.1(ii): index shift and endpoint values.

- F_n=F_0+i*pi*n, and one relative endpoint extension has value i*pi*(n-j) at either endpoint of gap j.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.index_shift`
- `NLS.ZakharovShabat.SourceSection19Data.endpointExtension_eqOn`
- `NLS.ZakharovShabat.SourceSection19Data.endpointExtension_value`

Continuity is relative to the filled spectral domain with the selected endpoint adjoined, rather than continuation through the interior of an open cut.

### S19-010: Lemma 19.1(iii): locally uniform gap bound.

- A single local source neighborhood and positive constant bound both boundary values by B*norm(gamma_n), for every signed index. The literal supremum range is bounded.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.uniform_gap_bounds`
- `NLS.ZakharovShabat.SourceAbelianMixedGapData.uniform_boundary_sup`

The quantifiers precede the index and side; there is no tail-only restriction.

### S19-011: Lemma 19.1(iv): analyticity of the square.

- F_n squared is analytic off the noncollapsed cuts, and also has an agreeing analytic continuation across its own selected gap.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.square_analytic`

The selected-gap filling is stronger than the printed assertion, while other open gaps remain excluded.

### S19-012: Lemma 19.1(v): real arcosh boundary profiles.

- For real sources the upper and lower boundary limits are respectively plus and minus arcosh of the signed half-discriminant on the entire closed gap.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.real_gap_boundary`

The limits allow arbitrary approach from the corresponding open half-plane, including approach to endpoints.

### S19-013: Lemma 19.1(vi): exact free primitive.

- At zero, F_n(z)=-i*z+i*pi*n=i*w_n(z).

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.zero`

This is an exact identity, including the filled zero gap.

### S19-014: Proof of joint and spectral analyticity.

- Local joint charts agree with the actual global primitive, so its full moving-cut joint differential and filled spectral slices are proved.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceFullAbelian_almostReal_differential`
- `NLS.ZakharovShabat.SourceSection19Data.spectral_analytic`

This supplies the analytic continuation argument internally; the reference to Appendix F is navigational.

### S19-015: Positive real-gap companion expression.

- The normalized primitive has exact exponential and companion-multiplier identities, and the real arcosh profile is continuous with zero endpoints and positive interior.

Public declarations:

- `NLS.ZakharovShabat.SourceAbelianDiscPrimitive.extension_exp_neg`
- `NLS.ZakharovShabat.sourceRealGapArcoshProfile_spec`

These results support the local logarithm construction, but this review has not identified a direct Lean statement for the printed strictly positive minimum of the real companion expression over the whole closed gap. That auxiliary assertion remains to be reconciled; the gradient theorem is already proved.

### S19-016: Local contour and logarithm neighborhood.

- An open neighborhood of each off-cut spectral/source point supports a normalized Floquet logarithm with the exact joint differential.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceAbelianLogChart_joint_neighborhood`
- `NLS.ZakharovShabat.sourceAbelianLogChart_exp`

Use the selected index n consistently in U_n prime contained in U_n minus G_n. The signed multiplier is (-1)^n*(Delta+R)/2, with R the canonical root. The implementation uses local normalized logarithms and gluing, rather than requiring the printed single principal-log annulus.

### S19-017: Logarithmic primitive and gradient formula.

- The exponential normalization is exact, and restricting the joint logarithm differential gives partial Delta divided by R.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianLogChart_exp`
- `NLS.ZakharovShabat.sourceAbelianLogChart_source_fderiv`
- `NLS.ZakharovShabat.SourceAbelianDiscPrimitive.extension_eventually_eq_log_at_endpoint`

Principal logarithms are used only where their branch is justified. No arbitrary additive period remains.

### S19-018: Analytic continuation of the source derivative.

- The exact Floquet exponential identity propagates across the whole connected complex cut complement. Local normalized germs yield the full derivative at all off-cut points.

Public declarations:

- `NLS.ZakharovShabat.sourceFullAbelianPrimitive_exp`
- `NLS.ZakharovShabat.SourceAbelianUniformDiscFamily.fullPrimitive_joint_hasFDerivAt`

The argument uses proved agreement of germs and spectral uniqueness, not merely equality of squares.

### S19-019: Endpoint normalization and primitive shift.

- The normalization shift and all endpoint constants are exact for every signed normalization and endpoint index.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianHalfPlanePrimitive_endpoint_limit`
- `NLS.ZakharovShabat.SourceSection19Data.index_shift`
- `NLS.ZakharovShabat.SourceSection19Data.endpoint_limit`

The real normalization is continued to complex sources on the common domain.

### S19-020: Signed finite telescoping across bands.

- The adjacent-band increment is -i*pi. Successor and predecessor induction give the complete signed-index shift.

Public declarations:

- `NLS.ZakharovShabat.sourceRealBandIntegral_tendsto_endpoints`
- `NLS.ZakharovShabat.sourceAbelianHalfPlanePrimitive_succ`
- `NLS.ZakharovShabat.sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add`

Integer induction replaces the two displayed finite telescoping sums and includes negative indices.

### S19-021: Real-band canonical root and integral -i pi.

- On the band after gap n, R=-i*(-1)^n*sqrt(4-Delta^2). Independent endpoint limits of the actual quotient integral give -i*pi.

Public declarations:

- `NLS.ZakharovShabat.sourceCanonicalRoot_eq_signed_sqrt_on_realBand`
- `NLS.ZakharovShabat.sourceRealBandIntegral_tendsto_endpoints`

The square root here is the nonnegative real root, multiplied by the displayed canonical phase. Collapsed adjacent gaps are allowed.

### S19-022: Canonical denominator in the continued shift formula.

- The normalization integral and its source continuation use Delta prime divided by the canonical root R. They give F_0-F_n=-i*pi*n.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianDifferential`
- `NLS.ZakharovShabat.SourceSection19Data.endpoint_integrals`
- `NLS.ZakharovShabat.SourceSection19Data.index_shift`

Keep R in the p.89 normalization paragraph. The printed positive root sqrt(4-Delta^2) omits the canonical phase; the earlier real-band calculation retains that phase explicitly.

### S19-023: Selected-gap differential factorization (4.7).

- Separating the selected critical factor gives Delta prime/R=((lambda_n^bullet-z)/w_n)*(-i*chi_n), with chi_n analytic through the selected gap.

Public declarations:

- `NLS.ZakharovShabat.sourceCriticalRootRatio_eq_selectedFactor_mul_extension`
- `NLS.ZakharovShabat.exists_global_sourceCriticalRootRatioExtension_analytic`

The deleted product is the actual spectral product and is analytic on the domain excluding only the other cuts.

### S19-024: Opposite boundary values and analytic square filling.

- The opposite sides give opposite normalized primitive profiles. Their squares agree with an analytic continuation through the selected closed gap.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.square_analytic`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.gapBoundary_lower_eq_neg_upper`

The analytic square extension includes both endpoints and collapsed gaps; continuity alone is not assumed to imply holomorphy without the implemented extension argument.

### S19-025: Collapsed-gap clause and all-index gap bound.

- The collapsed selected gap has F_n=0; the same local all-index bound holds for every noncollapsed gap.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.endpointExtension_value`
- `NLS.ZakharovShabat.SourceSection19Data.uniform_gap_bounds`

In the collapsed-gap sentence, replace F by F_n. The zero-index F at gap n has value -i*pi*n. The bound uses magnitudes for complex gaps.

### S19-026: Real-gap integral and arcosh value.

- The real upper-side partial quotient integral equals the positive arcosh profile; the lower-side integral is its negative. Endpoint integrability is proved.

Public declarations:

- `NLS.ZakharovShabat.sourceRealGap_upperIntegral_eq_arcosh`
- `NLS.ZakharovShabat.sourceRealGap_lowerIntegral_eq_neg_arcosh`
- `NLS.ZakharovShabat.sourceRealGap_sideQuotients_intervalIntegrable`

The canonical sheet orientation fixes the sign; the result holds across the whole closed real gap.

### S19-027: Free differential and free primitive.

- The exact free primitive is -i*z+i*pi*n, with spectral derivative -i away from the cuts.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.zero`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_product`

The free identity fixes both the derivative sign and the additive normalization.

### S19-028: Notation F=F0.

- F denotes F_0; the relationship F=F_n-i*pi*n is already proved.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.index_shift`

This is a notation declaration.

### S19-029: Figure 4.1 boundary sign picture.

- Figure 4.1 illustrates boundary directions and signs, with zero endpoint values. Exact real-gap arcosh and real-band arcsine formulas provide the corresponding mathematical values.

Public declarations:

- `NLS.ZakharovShabat.sourceRealGapArcoshProfile_spec`
- `NLS.ZakharovShabat.sourceAbelianPrimitive_eq_arcsin_on_band`

The labels +1, -1, +i and -i indicate directions/signs, not constant magnitudes. The diagram is not an additional numerical-value theorem.

### S19-030: Lemma 19.2: convergent physical Hamiltonian Laurent series.

- Every real finite-gap source at finite p>1 has a convergent exterior Laurent series whose coefficients are the physical NLS Hamiltonians. One radius works for all normalization indices.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.laurent`
- `NLS.ZakharovShabat.exists_sourceFullAbelian_finiteGap_hamiltonian_laurent`

The smooth periodic representative and its discriminant equality are constructed, not supplied as hypotheses.

### S19-031: Finite product, exterior growth and coefficient determination.

- The finitely many noncollapsed cuts have compact union. The actual quotient is bounded in an exterior region, has a normalized analytic inversion germ, and the primitive has a convergent Laurent expansion with leading term -i*z and zero additional constant.

Public declarations:

- `NLS.ZakharovShabat.isCompact_compl_sourceOpenGapComplement_finiteGap`
- `NLS.ZakharovShabat.exists_sourceFiniteGap_logDerivative_exterior_bound`
- `NLS.ZakharovShabat.exists_sourceFiniteGap_exterior_quadratic_remainder`
- `NLS.ZakharovShabat.exists_sourceFullAbelian_finiteGap_laurent`

Exterior circle bounds, maximum modulus and the zero outer period replace the printed finite-product growth shortcut. The proof does not require a global meromorphic continuation across open cuts.

### S19-032: Real-band monotonicity and root sign.

- The canonical root has the exact signed imaginary square-root expression, and the discriminant lies strictly between -2 and 2 in each open real band.

Public declarations:

- `NLS.ZakharovShabat.sourceCanonicalRoot_eq_signed_sqrt_on_realBand`
- `NLS.ZakharovShabat.sourceDiscriminant_realBand_sq_lt_four`

The printed strict monotonicity of (-1)^(n+1)*Delta on the whole closed band is not established by the two cited statements alone. A direct monotonicity theorem remains to be reconciled; the following arcsine derivative and band-value conclusions are independently proved.

### S19-033: Derivative of the real-band arcsine branch.

- The real-band arcsine expression differentiates to the actual oriented canonical quotient.

Public declarations:

- `NLS.ZakharovShabat.hasDerivAt_sourceRealBandArcsinPrimitive`

The implementation writes the equivalent i*(-1)^n*arcsin(Delta/2) expression and proves the discriminant is in the open arcsine interval.

### S19-034: Exact primitive on a real spectral band.

- On each real open band, F equals the arcsine primitive minus i*pi/2-i*pi*n. The band primitive is continuous and its endpoint values are plus and minus i*pi/2.

Public declarations:

- `NLS.ZakharovShabat.sourceAbelianPrimitive_eq_arcsin_on_band`
- `NLS.ZakharovShabat.continuous_sourceRealBandArcsinPrimitive`
- `NLS.ZakharovShabat.sourceRealBandArcsinPrimitive_left`
- `NLS.ZakharovShabat.sourceRealBandArcsinPrimitive_right`

Endpoint values are read through the proved relative limits. The full primitive agrees with the real-source primitive used in this formula.

### S19-035: Half-integer discriminant asymptotics.

- The actual smooth periodic discriminant differs from 2*cos(i*sigma_N) by at most C/(2*abs(r))^N for every real abs(r)>=1, hence also at both tails of the half-integer sample sequence.

Public declarations:

- `NLS.ZakharovShabat.exists_classicalDiscriminant_hamiltonian_error_bound`
- `NLS.ZakharovShabat.nlsHamiltonianPhase`

This is an internal all-order WKB proof with physical Hamiltonians. It does not assert an independent comparison with the exact cited edition of [23].

### S19-036: Uniform arcsine error transfer.

- At every real zero of cosine, one local inverse estimate controls small phase differences by the discriminant error, with a neighborhood independent of the sample index.

Public declarations:

- `NLS.ComplexAnalysis.exists_norm_sub_le_two_mul_sinh_sub`
- `NLS.ComplexAnalysis.norm_cosh_shift_sub`
- `NLS.ComplexAnalysis.exists_norm_phase_sub_le_discriminant_error`

This is an alternative proof of the required error transfer using complex sinh near zero. The displayed principal-arcsine difference is not separately exported or claimed as a literal Lean theorem.

### S19-037: Primitive approximation along half-integer points.

- The normalized analytic phase has an order-N error against the physical Hamiltonian correction on every escaping positive sequence of real cosine zeros.

Public declarations:

- `NLS.ZakharovShabat.exists_nlsHamiltonian_sampled_phase_error`
- `NLS.ZakharovShabat.exists_sourceFullAbelian_hamiltonian_laurent_of_classical_discriminant`

The implemented sampled phase estimate supplies the needed approximation directly, without the intermediate principal-arcsine formula. Its discriminant identity is proved for the actual full primitive.

### S19-038: Hamiltonian convention relative to reference 23.

- The footnote explains a convention change relative to reference [23]. The internal construction fixes the physical Hamiltonians through the differential recurrence.

Public declarations:

- `NLS.ZakharovShabat.nlsHamiltonianPhase`

No independent comparison of the external book conventions is claimed in this review.

### S19-039: Sine addition, branch selection and Laurent coefficients.

- The half-integer sample error determines every Taylor coefficient of the normalized analytic inversion phase. These coefficients form a genuinely convergent physical Hamiltonian series.

Public declarations:

- `NLS.ZakharovShabat.iteratedDeriv_nlsHamiltonian_of_discriminant`
- `NLS.ZakharovShabat.exists_nlsHamiltonian_series_of_discriminant`

The proof explicitly chooses pi*(j+1/2), proves cosine vanishes there, and applies analytic order uniqueness. The local sinh estimate replaces the printed sine-addition/principal-arcsine branch calculation.

### S19-040: Transition to the cubic expansion.

- The sentence introduces the cubic expansion used later.

This is a transition, not a separate assertion.

### S19-041: Corollary 19.3: cubic Laurent part and remainder.

- The cubic Laurent part is i*z^3-(3*i/2)*H1*z-(3*i/4)*H2-(3*i/8)*(H3-2*H1^2)/z. The error is bounded by K/norm(z)^2 in every exterior complex direction.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.cube_asymptotic`
- `NLS.ZakharovShabat.SourceSection19Data.cube_isBigO`

The shifted normalizations share one radius and one positive bound before the index is chosen.

### S19-042: Lemma 19.4: locally uniform mixed gap error.

- The literal two-sided gap-error supremum equals gamma_n*(g_n+h_n), with fixed locally bounded g in ell^(p/2) and h in every finite ell^q, q>1.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.gapErrorSup`
- `NLS.ZakharovShabat.SourceAbelianMixedGapData.bounded`
- `NLS.ZakharovShabat.SourceAbelianMixedGapData.mixed_displacement`

The supremum range is bounded before sSup is used. The sequences are chosen before all auxiliary exponents, and the quasi-norm range p/2<1 is retained. No analyticity of the bounding sequences is claimed.

### S19-043: Exact zero-potential error clause.

- At zero the gap error vanishes exactly.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.zero`

This retains the precise free normalization, with no asymptotic remainder.

### S19-044: Endpoint integral with the selected-gap product.

- The actual endpoint integral uses the selected critical factor and the deleted product chi_n.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.endpoint_integrals`
- `NLS.ZakharovShabat.sourceCriticalRootRatio_eq_selectedFactor_mul_extension`

The integral and factorization refer to the same canonical quotient and the same selected gap.

### S19-045: Critical displacement and refined product estimate.

- The exact squared-gap critical offset and the refined deleted-factor estimates supply locally uniform ell^(p/2)+ell^(1+) gap-error majorants.

Public declarations:

- `NLS.ZakharovShabat.exists_local_uniform_sourceCriticalPoint_gap_distance_bound`
- `NLS.ZakharovShabat.exists_local_sourceFullAbelian_gap_all_exponent_tails`
- `NLS.ZakharovShabat.SourceAbelianMixedGapData.mixed_displacement`

The proof retains the actual critical displacement and the factor pi; quasi-norm addition is used when p/2<1. Finite central gaps are included by the final mixed-data constructor.

### S19-046: Product-error supremum estimate.

- If D bounds abs(lambda_n^bullet-z) and E bounds abs(chi_n(z)-1) over the closed gap, both boundary errors satisfy abs(F_n-i*w_n)<=pi*(D*E+abs(lambda_n^bullet-tau_n)).

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.gapBoundary_sub_root_norm_le_of_factor_error`
- `NLS.ZakharovShabat.sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound`

Use norms and retain the factor pi in the p.91 estimate. The existing positive comparison theorem supplies a sufficient complete error bound directly; no optimality claim or new refutation is added.

### S19-047: Standard-root derivative and elementary primitive.

- Subtracting i*w_k from the primitive gives a numerator defect equal to the deleted-factor error plus the critical-to-midpoint offset. Integrating this defect yields the complete positive error bound.

Public declarations:

- `NLS.ZakharovShabat.sourceCriticalRootGapNumerator_sub_linear`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.gapBoundary_sub_root_norm_le_of_factor_error`

The exclusion in the printed derivative sentence must use G_k when differentiating w_k. The implementation uses the equivalent quadratic differential equation, avoiding a separate branch-dependent primitive formula.

### S19-048: Collapsed gaps and reciprocal-root integral bound.

- Collapsed gaps have zero error. For noncollapsed gaps the standard-root side-integral estimate retains pi, and the critical offset is included in the complete comparison bound.

Public declarations:

- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.fullPrimitive_sub_root_eq_zero_of_collapsed`
- `NLS.ZakharovShabat.sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound`
- `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.gapBoundary_sub_root_norm_le_of_factor_error`

A constant numerator in the normalized side-integral bound gives the reciprocal-root estimate. The later sequence estimate absorbs the fixed factor pi into its locally uniform majorants.

## Evidence and validation

The [original package](../NLS/ZakharovShabat/SourceSection19Original.lean)
retains the same primitive, source domain and normalization throughout.
The [positive gap comparison](../NLS/ZakharovShabat/SourceFullAbelianGapComparison.lean)
retains the factor π. The
[sampled phase proof](../NLS/ZakharovShabat/NLSHamiltonianPrimitiveCoefficients.lean)
identifies the physical Laurent coefficients without assuming the printed inverse-arcsine displays.

This review inspected 37 complete module bodies and resolved 76 declaration references.
It does not claim a fresh semantic reading of every transitive dependency.
Historical refutation modules are unchanged; no new refutation was added.

This documentation-only step reuses the successful full check from commit c8cbe87 on the exact unchanged Lean and dependency-lock snapshot: 8,559 build jobs, 7,635 public examples and 44,604 transitively audited NLS declarations, with 21 inherited warnings and zero new warnings. No new full build is claimed. Current module hashes, declaration references, source-review integrity and local documentation links are checked separately; these checks do not certify mathematical completeness.

Next: reconcile the two positive auxiliary assertions S19-015 and S19-032,
then continue the ordered comparison with Section 20.
