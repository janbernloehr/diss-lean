# Section 13 ordered assertion comparison

All fourteen ordered Section 13 passage groups match the existing positive proofs on the retained Section 12 domain, for every finite p greater than one. Arbitrary-path integrals use continuous paths and root continuations with C1 parameterization on the open interval and independent improper limits at both endpoints. Chosen paths are integrable; absolute integrability is not asserted for every admissible path. Beta covers collapsed complex gaps; eta and theta exclude their own closed-gap locus. Series convergence is locally uniform for each fixed index on a common neighborhood; index decay is pointwise in the source. The three canonical brackets use the actual original action and local angle derivatives with their stated open-gap hypotheses. Hilbert approximation above two and coefficient-preserving restriction below two cover all finite p greater than one. The exact cited edition of [23] remains unaudited. This completes the ordered Section 13 comparison, not the dissertation-wide semantic audit: Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, the exact cited 2014 Birkhoff construction, Appendix G.2 norm interpretation and the broader source inventory retain their qualifications.

Source: printed p. 72, text lines 5823–5909. Line numbers count newline characters,
preserving the form-feed characters in the extracted text. The rendered page was inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S13-001 | 5825–5834 | The same common psi domain and the literal angle sum. | matched |
| S13-002 | 5836–5843 | Eta as an actual endpoint integral modulo 2*pi. | matched |
| S13-003 | 5844–5851 | Off-diagonal beta endpoint integrals throughout W. | matched |
| S13-004 | 5852–5861 | Admissible paths and the prescribed terminal square-root sign. | matched |
| S13-005 | 5863–5866 | Periodic terminals: beta is zero and eta is unaffected modulo 2*pi. | matched |
| S13-006 | 5867–5877 | Theorem 13.1(i): beta analyticity and the uniform reciprocal-index estimate. | matched |
| S13-007 | 5879–5879 | Theorem 13.1(ii): eta has real analytic representatives modulo pi. | matched |
| S13-008 | 5881–5886 | Theorem 13.1(iii): local uniform beta-series convergence, analyticity and decay. | matched |
| S13-009 | 5888–5895 | Theorem 13.1(iv): the literal real theta sum and its analytic extension. | matched |
| S13-010 | 5896–5898 | Assembly of Liouville coordinates and transition to canonicity. | matched |
| S13-011 | 5900–5902 | Corollary 13.2: action-action brackets vanish on the full real locus. | matched |
| S13-012 | 5903–5904 | Corollary 13.2: angle-angle brackets vanish when both angle gaps are open. | matched |
| S13-013 | 5905–5906 | Corollary 13.2: the mixed bracket is the Kronecker delta. | matched |
| S13-014 | 5908–5909 | The Hilbert case, continuity above two and compatibility below two. | matched |

## Compared passages

### S13-001: The same common psi domain and the literal angle sum.

- The integration interface uses the exact W and root maps retained from Lemma 12.12. W is open, simply connected and contains the entire real-type source locus for every finite p greater than one. No replacement root family or further global intersection is introduced.
- Every complex source has a common smaller source neighborhood with original isolating disks containing all periodic segments and their actual Dirichlet terminals. The original numerator is used in each angular integrand.
- Theta_n is literally the chosen eta_n plus the sum of the off-diagonal beta terms. Its asserted domain excludes the nth closed-gap locus Z_n; the sum and the eta class are justified in the subsequent passages.

Public declarations:

- `NLS.ZakharovShabat.sourceSection13OriginalDomain`
- `NLS.ZakharovShabat.SourceLemma12_12Data.angular_extension`
- `NLS.ZakharovShabat.SourceLemma12_12Data.angular_original_disks`
- `NLS.ZakharovShabat.sourceAngularOriginalTheta`
- `NLS.ZakharovShabat.sourceAngularOriginalTheta_eq_series`

The objects and domain match. The attribution to [23, Section 15] is contextual; this comparison does not independently certify the exact cited edition.

### S13-002: Eta as an actual endpoint integral modulo 2*pi.

- The integrand is exactly the Section 12 psi numerator divided by the continued square root of the actual discriminant squared minus four. Its initial point is the actual left periodic endpoint and its terminal is the actual Dirichlet root.
- At every complex open gap, a normalized integrable path exists. Choosing one of its values defines eta; the fallback zero branch in the total definition is never used on this proved domain.
- Every admissible path in the stated interior-C1 class has an improper integral obtained by independent limits of both endpoint cutoffs. Its limit differs from the chosen eta by an integer multiple of 2*pi, also across different original disks.

Public declarations:

- `NLS.ZakharovShabat.sourceAngularIntegrand`
- `NLS.ZakharovShabat.sourceAngularOriginalEtaIntegralValues`
- `NLS.ZakharovShabat.sourceAngularOriginalEta`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_integral_values_nonempty`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_integral_mem`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_exists_improper_integral`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_improperIntegral_spec`

The literal integral and its 2*pi class match on W minus Z_n. The regularity convention is a continuous path and continuous root continuation with C1 parameterization on the open interval. Absolute integrability is constructed for chosen paths and is not asserted for every admissible path.

### S13-003: Off-diagonal beta endpoint integrals throughout W.

- For every m different from n and every complex source in W, the normalized primitive definition has exactly one beta value. The construction includes both collapsed periodic gaps and periodic Dirichlet terminals.
- One constructed continuously differentiable path in an original disk realizes every off-diagonal numerator. Its actual endpoint integral equals beta, and its independently truncated integrals converge to that value.
- Every other normalized admissible interior-C1 path has the same improper limit. No caller-supplied integrability, primitive or limiting value is used in this comparison.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_value_unique`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_mem_values`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_dirichlet_integral_path`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_exists_improper_integral`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_improper_limit`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_improperIntegral_eq_value`

The full-domain beta definition matches, including collapsed complex gaps. Off-diagonal beta is single-valued; it is not merely specified modulo a period.

### S13-004: Admissible paths and the prescribed terminal square-root sign.

- The path interior lies inside the supplied isolating disk and outside the selected periodic segment. The continued root is continuous on the closed path and its square is the actual spectral radicand at every parameter value.
- At a nonperiodic Dirichlet terminal, the root equals the actual anti-discriminant delta(mu_m). The constructed path supplies this normalization rather than asking the caller to assume its existence.
- On the path interior, any such continuation has one fixed sign relative to the canonical root. Different disks are compared through a common transverse path in their open convex intersection; the disks need not be nested.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularAdmissiblePathRootData`
- `NLS.ZakharovShabat.sourceAngularAdmissiblePathRootData_of_continuousOn`
- `NLS.ZakharovShabat.SourceAngularAdmissiblePathRootData.exists_fixed_sign`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_dirichlet_integral_path`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_dirichlet_common_integral_path`

The admissibility and sign convention match. As in the existing original-domain interfaces, singular endpoint integrals are treated as improper limits for interior-C1 paths; no C1 regularity at the endpoints is required for the arbitrary-path result.

### S13-005: Periodic terminals: beta is zero and eta is unaffected modulo 2*pi.

- The off-diagonal primitive has the same limit at both periodic endpoints. Therefore its path integral is zero on either continued sheet, including when the selected gap collapses.
- For diagonal eta at an open gap, the normalized remainder has zero endpoint value. The model integral is determined modulo 2*pi by its terminal root value. At either periodic terminal that root is zero on both sheets, so no terminal sign prescription is needed.
- These are actual improper-limit conclusions. The beta proof uses the normalized zero periods; the eta remainder subtracts the model with exactly the normalized diagonal period.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.angular_original_endpoint_primitive`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_periodic_terminal_improper_limit`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_common_improper_remainder`
- `NLS.ZakharovShabat.SourceAngularAdmissiblePathRootData.improper_model_integral_periods`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_admissible_improper_limit`

The printed endpoint alternatives match. Eta retains its own open-gap domain, while beta also covers a collapsed selected gap.

### S13-006: Theorem 13.1(i): beta analyticity and the uniform reciprocal-index estimate.

- Each off-diagonal beta is complex analytic, hence real analytic, on all of the unchanged W. Cauchy reconstruction on original annuli uses analytic symmetric spectral data and the actual Dirichlet terminal; it does not require analytic ordered periodic endpoints or division by a vanishing gap.
- For every complex base source, one open neighborhood and one positive C are chosen before all nearby sources and all n,m. The literal estimate is norm(beta_m^n)<=C*(norm(gamma_m)+norm(mu_m-tau_m))/abs(n-m).
- On a selected annulus, the coefficient is rho^2*(A+rho)*M/(rho-r)^3. The tail uses fixed r=pi/16, R=pi/8 and rho=3*pi/32. A finite intersection and a sum of the remaining selected constants give one bound for all pairs.

Public declarations:

- `NLS.ZakharovShabat.sourceTheorem13_1_original_beta`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.angular_original_annulus_chart`
- `NLS.ZakharovShabat.SourceLemma12_12Data.angular_original_annulus_tail`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_uniform_selected_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_uniform_bound`
- `NLS.ZakharovShabat.SourceAngularJointAnnulusChartData.norm_beta_le_of_midpointFilledRegularFactor_bound`

The analytic assertion, numerator weight, reciprocal index and local uniformity match. No constant correction is needed. The referenced external proof is not separately audited.

### S13-007: Theorem 13.1(ii): eta has real analytic representatives modulo pi.

- On W minus Z_n the single-valued phase exp(2*i*eta_n) is nonzero and complex analytic. Original annular charts supply local analytic representatives at every complex source with its selected gap open.
- Every actual normalized integral agrees with such a representative modulo an integer multiple of pi. The representatives and the actual chosen integral are real at real-type sources.
- The 2*pi ambiguity between actual path integrals is retained separately from the pi ambiguity used for analytic charts; the proof does not conflate these two statements.

Public declarations:

- `NLS.ZakharovShabat.sourceTheorem13_1_original_eta`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_analytic_chart`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_phase_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_pathIntegral_phase`
- `NLS.ZakharovShabat.SourceLemma12_12Data.eta_original_value_local_representative`

The modulo-pi analytic extension matches on its exact open-gap domain. No global single-valued analytic branch of eta is claimed.

### S13-008: Theorem 13.1(iii): local uniform beta-series convergence, analyticity and decay.

- The diagonal summand is explicitly zero. Holder pairs the actual lp gap and Dirichlet-minus-midpoint sequences with the shifted punctured reciprocal lattice in the conjugate exponent. The literal beta series is absolutely summable.
- Near every complex source, one open neighborhood works for every n. For each fixed n, symmetric finite sums converge uniformly on that neighborhood to the actual beta correction. The convergence rate is not asserted to be uniform in n.
- The analytic finite sums and Banach-space holomorphic limit argument give a complex analytic correction on W. Shifted Holder decay makes both the absolute sum and the correction tend to zero as abs(n) tends to infinity, at each source.

Public declarations:

- `NLS.ZakharovShabat.sourceAngularBetaSeriesTerm`
- `NLS.ZakharovShabat.sourceAngularBetaCorrection`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_series`
- `NLS.ZakharovShabat.summable_norm_sourceAngularBetaSeriesTerm_of_bound`
- `NLS.ZakharovShabat.exists_local_uniform_sourceAngularBetaSeries_of_bound`
- `NLS.ZakharovShabat.sourceAngularBetaSeriesAnalyticData_of_uniform_bound`
- `NLS.ZakharovShabat.sourceAngularBetaCorrection_decay_of_bound`

The series and o(1) assertions match. The source states local uniform convergence in the source variable and pointwise signed-index decay; no stronger uniform-in-n convergence rate or locally uniform decay is inferred.

### S13-009: Theorem 13.1(iv): the literal real theta sum and its analytic extension.

- Theta_n is exactly eta_n plus the absolutely convergent beta correction. Changing the normalized eta integral changes theta by an integer multiple of 2*pi.
- At real-type sources where the nth gap is open, eta and all beta terms are real, so the literal theta value is real. Adding the analytic correction to an eta chart gives an analytic theta representative modulo pi.
- The actual Frechet derivative of each local theta representative is the branch-independent logarithmic phase differential used in the Poisson brackets.

Public declarations:

- `NLS.ZakharovShabat.sourceAngularOriginalTheta_eq_series`
- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_integral_choice_period`
- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_im_eq_zero`
- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_phase`
- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_local_representative`
- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_local_differential_representative`
- `NLS.ZakharovShabat.sourceTheorem13_1_original`

The assertion matches on the angle domain specified at the start of Section 13. The printed real-locus wording is read on that existing domain, excluding Z_n; no angle value at its own collapsed gap is asserted.

### S13-010: Assembly of Liouville coordinates and transition to canonicity.

- The complete angular interface is constructed with W in all three domain slots and the same Section 12 family. It contains the original beta values, estimates and series, eta charts, theta phases and reality properties.
- Together with the retained original actions, these are the action-angle objects whose canonical relations follow. This sentence summarizes their assembly on the stated open-gap angle domains; global rectangular Birkhoff coordinates are the subject of Section 14.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.original_theta_common_domain`
- `NLS.ZakharovShabat.sourceTheorem13_1_original`
- `NLS.ZakharovShabat.sourceCorollary13_2_original`

Matched as an assembly of the preceding mathematical objects. It does not claim simultaneous angle values on closed gaps, a global angle chart, or completion of the later Birkhoff construction.

### S13-011: Corollary 13.2: action-action brackets vanish on the full real locus.

- The regular action cotangent has the actual indexed action derivative as its underlying functional. Equality of complex germs with the previously constructed action identifies the complete derivative.
- Action variations are contour integrals of regular discriminant variations. Discriminant commutation and bilinear contour integration give zero action-action pairing for all signed n,m and all real-type sources at every finite p greater than one.
- The pairing is the absolutely convergent Fourier sum with reversed frequency and sign -i. Its square-summable coefficient witness is uniquely determined by the cotangent. Neither action gap is required to be open.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.originalActionCotangent`
- `NLS.ZakharovShabat.SourceLemma12_12Data.action_original_fderiv_eq_complexAction`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_corollary13_2`
- `NLS.ZakharovShabat.sourceActionRegularCotangent_bivector_eq_zero`
- `NLS.Poisson.RegularSourceCotangent.bivector_eq_tsum`
- `NLS.Poisson.RegularSourceCotangent.summable_norm`

The zero bracket and its full real domain match, including closed gaps and exponents below two.

### S13-012: Corollary 13.2: angle-angle brackets vanish when both angle gaps are open.

- Each regular angle cotangent is the actual derivative of a local representative of the literal original theta sum. The Fourier pairing is independent of the representative and of the coefficient witness.
- The Hilbert angle-angle identity is obtained from the proved finite-gap identity and density within the joint open-gap domain. Exponent compatibility and real Fourier approximation transfer it above two; restriction of the same regular coefficients transfers it below two.
- Both selected angle gaps must be open, exactly excluding Z_n union Z_m. The statement applies to every signed index pair and every finite p greater than one.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.theta_original_regularCotangent_representative`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_corollary13_2`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaRegularCotangent_bivector_eq_zero`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaThetaBracket_eq_zero_of_realType`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaThetaBracket_eq_zero_of_two_le`

The angle-angle identity matches with precisely its two open-gap hypotheses. The earlier physical NLS Dirichlet-motion obligation in Section 7 is not declared resolved by this spectral bracket comparison.

### S13-013: Corollary 13.2: the mixed bracket is the Kronecker delta.

- At exponents at least two, the actual full terminal-kernel sum converges both to the theta-action bracket and to the normalized psi period on a real-centered action circle. Contour comparison identifies that period with the exact Kronecker delta.
- Below two, action and angle differential compatibility preserves the complete regular coefficient pairs and their Fourier pairing. The same identity therefore holds for all finite p greater than one.
- Only the angle gap n is required to be open. The action index m may have a collapsed gap; the original indexed action derivative is still the one used in the bracket.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.original_corollary13_2`
- `NLS.ZakharovShabat.sourceCorollary13_2_original`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaActionRegular_bivector_eq_kronecker`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaAction_eq_kronecker`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.psi_period_on_realCentered_action_chart`

The mixed bracket, normalization and exact domain match. No extra open-gap condition is imposed on the action.

### S13-014: The Hilbert case, continuity above two and compatibility below two.

- Symmetric Fourier truncations preserve real type and converge in the actual finite-p source norm. Since the required nonzero-gap loci are open, the truncations eventually stay in the same bracket domain. The analytic angle-angle bracket is continuous there, so its finite-Fourier zero identity passes to the limit.
- Each finite Fourier source above two is the inclusion of a real Hilbert source. Exponent-compatible phase germs identify their complete angle derivatives; the actual action germs are compatible as well.
- For 1<p<2, inclusion into the Hilbert source space preserves the physical spectral data. The actual derivatives restrict from the Hilbert derivatives, with the same square-summable coefficient pairs, so the absolutely convergent brackets agree. This supplies the case left implicit by the printed proof.
- The formalization also gives direct contour proofs of the action-action and mixed identities, rather than relying on the cited Hilbert theorem as an axiom.

Public declarations:

- `NLS.ZakharovShabat.tendsto_sourceSymmetricTruncate`
- `NLS.ZakharovShabat.eq_of_continuousOn_of_finite_realType`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaThetaBracket_eq_zero_of_finite_realType`
- `NLS.ZakharovShabat.exists_realHilbertSource_of_finite_support`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaDifferential_exponent`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaRegularCotangent_coefficients_exponent`
- `NLS.ZakharovShabat.fderiv_sourceComplexAction_exponent`
- `NLS.ZakharovShabat.sourceActionRegularCotangent_coefficients_exponent`
- `NLS.Poisson.RegularSourceCotangent.bivector_restrict`

The mathematical continuity argument matches, with the below-two compatibility made explicit. The bibliographic attribution to [23, Section 18] is not an independent verification of that edition. No correction or new refutation is needed here.

## Evidence and validation

The [common original domain](../NLS/ZakharovShabat/SourceSection13OriginalDomain.lean)
and [constructed endpoint integrals](../NLS/ZakharovShabat/SourceAngularOriginalEndpointIntegrals.lean)
supply the actual angular objects. The [beta](../NLS/ZakharovShabat/SourceAngularOriginalBetaImproper.lean)
and [eta](../NLS/ZakharovShabat/SourceAngularOriginalEtaImproper.lean) improper-limit proofs
identify arbitrary admissible paths. [Theorem 13.1](../NLS/ZakharovShabat/SourceTheorem13_1Original.lean)
and [Corollary 13.2](../NLS/ZakharovShabat/SourceCorollary13_2Original.lean)
retain these same objects and domains.

This comparison freshly inspected 46 module bodies and resolved 76 public declarations.
It adds no Lean theorem, definition, example, constant correction or refutation.

This documentation-only step reuses the exact Lean and dependency snapshot of commit `b05a5f2`. Its completed full check passed 8,557 build jobs, 7,631 public examples and the transitive axiom audit of 44,598 NLS declarations, with 21 inherited warnings and no new warnings. No new full build is claimed. Current source hashes, declaration references, review integrity and documentation links are checked separately.

Continue in source order with Section 14, Overview.
