# Section 9 ordered assertion comparison

This ledger follows printed pp.52–54 in source order. All fifteen groups
have been compared: twelve matched and three corrected. The three corrected
groups apply the same auxiliary D*/N* label correction to the characteristic
display, the anti-discriminant difference and its analytic-extension proof.
Counts describe reviewed scope, not a completion percentage.

The new local branch construction supplies the implicit-function step at
arbitrary complex simple roots. Corrected formulas are proved positively;
no additional refutations are added. Section 7's physical NLS Dirichlet
motion and unrestricted psi characterization, the exact cited 2014
construction, Appendix G.2 norm interpretation and broader source inventory
remain unresolved.

Source positions use the cached extraction identified in the
[source-review index](source-review-index.json). Printed pp.52–54 were
visually inspected. The auxiliary labels use the original endpoint domains
on p.33, extraction lines 2113–2125. See [Section 9](SECTION_9.md) and the
[errata](../SOURCE_ERRATA.md) for the normalization context.

| Group | Source lines | Requirement | Status |
| --- | --- | --- | --- |
| S9-001 | 3950–3966 | Ordinary Dirichlet physical monodromy, zeros and the literal negative product. | matched |
| S9-002 | 3968–3978 | Ordinary Neumann physical monodromy, zeros and the literal negative product. | matched |
| S9-003 | 3980–3983 | Extension from Hilbert sources using asymptotic spectral products. | matched |
| S9-004 | 3994–4010 | Lemma 9.1(i): joint analyticity, exact ordinary products and spectra. | matched |
| S9-005 | 4012–4017 | Lemma 9.1(ii): continuity at each real-type base. | matched |
| S9-006 | 4019–4023 | Lemma 9.1(iii): ordinary Dirichlet and Neumann roots in their indexed periodic gaps. | matched |
| S9-007 | 4026–4031 | Proof of Lemma 9.1: analytic products, Rouche continuity and transported signed discriminant levels. | matched |
| S9-008 | 4034–4046 | Auxiliary analogues and the two physical monodromy displays. | corrected |
| S9-009 | 4048–4051 | Anti-discriminant as the monodromy off-diagonal sum and auxiliary difference. | corrected |
| S9-010 | 4055–4058 | Lemma 9.2(i): analytic extension of the anti-discriminant. | matched |
| S9-011 | 4061–4063 | Lemma 9.2(ii): discriminant identity at simple Dirichlet roots. | matched |
| S9-012 | 4065–4068 | Lemma 9.2(iii): locally uniform full value and derivative sample sequences in lp. | matched |
| S9-013 | 4078–4081 | Proof of analytic extension by the auxiliary difference. | corrected |
| S9-014 | 4082–4085 | Proof of the Dirichlet identity by Hilbert agreement, simple-root branches and density. | matched |
| S9-015 | 4086–4093 | Auxiliary sine errors, lp disk majorants and the Cauchy derivative estimate. | matched |

## S9-001: Ordinary Dirichlet physical monodromy, zeros and the literal negative product.

- The ordinary Dirichlet characteristic is the literal physical monodromy expression (m4+m3-m2-m1)/(2i) for every Hilbert source.
- Its zeros are exactly the actual interval Dirichlet spectrum, with analytic zero order equal to algebraic multiplicity. The canonical symmetric product has prefactor -1 and denominator pi_0=1.

Public evidence: `NLS.ZakharovShabat.l2SeparatedCharacteristic`, `NLS.ZakharovShabat.periodOneBoundaryCharacteristic_eq_l2`, `NLS.ZakharovShabat.l2SeparatedCharacteristic_source_eq_zero_iff`, `NLS.ZakharovShabat.sourceBoundarySpectrum_iff_l2_endpoint`, `NLS.ZakharovShabat.analyticOrderAt_l2SeparatedCharacteristic_source`, `NLS.ZakharovShabat.SourceLemma9_1Data.product`.

Physical agreement is proved by finite Fourier density and continuity, without a continuous-representative hypothesis. The entire function is normalized, not just its zero set. Every central and repeated root is retained.

## S9-002: Ordinary Neumann physical monodromy, zeros and the literal negative product.

- The ordinary Neumann characteristic is the literal monodromy expression (m4-m3+m2-m1)/(2i), with the opposite separated endpoint sign.
- The same actual-spectrum, multiplicity and negative-product statements hold for the complete Neumann root sequence.

Public evidence: `NLS.ZakharovShabat.l2SeparatedCharacteristic`, `NLS.ZakharovShabat.l2SeparatedCharacteristic_eq_zero_iff`, `NLS.ZakharovShabat.periodOneBoundaryCharacteristic_eq_l2`, `NLS.ZakharovShabat.analyticOrderAt_l2SeparatedCharacteristic_source`, `NLS.ZakharovShabat.SourceLemma9_1Data.product`.

The common BoundaryCondition argument is instantiated with neumann. This preserves the physical endpoint domain and the exceptional zero-mode denominator.

## S9-003: Extension from Hilbert sources using asymptotic spectral products.

- The normalized boundary products extend to every finite source exponent p>1. They agree with the physical Hilbert characteristics in the appropriate exponent-inclusion direction.
- Agreement on finite Fourier sources uniquely determines the continuous extension for each spectral parameter.

Public evidence: `NLS.ZakharovShabat.sourceBoundaryCharacteristic_eq_l2_of_two_le`, `NLS.ZakharovShabat.sourceBoundaryCharacteristic_eq_l2_of_le_two`, `NLS.ZakharovShabat.sourceBoundaryCharacteristic_unique_continuous`, `NLS.ZakharovShabat.BoundaryCondition.tendstoLocallyUniformlyOn_canonicalProduct`.

Above two this is extension from Hilbert sources; below two it is restriction along the inclusion into the Hilbert space. No assertion that all Hilbert sources belong to a stronger source space is made.

## S9-004: Lemma 9.1(i): joint analyticity, exact ordinary products and spectra.

- Both actual ordinary characteristic functions are jointly analytic in the spectral parameter and original complex source.
- Their literal symmetric root products converge locally uniformly on the whole spectral plane at each fixed source, and their zeros and analytic orders are exactly the actual spectra and algebraic multiplicities.

Public evidence: `NLS.ZakharovShabat.sourceLemma9_1_data`, `NLS.ZakharovShabat.SourceLemma9_1Data.analytic`, `NLS.ZakharovShabat.SourceLemma9_1Data.product`, `NLS.ZakharovShabat.SourceLemma9_1Data.spectrum`, `NLS.ZakharovShabat.SourceLemma9_1Data.multiplicity`, `NLS.ZakharovShabat.localUniformAnalyticApproximation_boundaryCharacteristic`, `NLS.ZakharovShabat.analyticOnNhd_periodOneBoundaryCharacteristic_joint`.

Joint analyticity is proved by uniform approximation with intrinsic central polynomials on actual Banach neighborhoods, then composition with the original interval extension. This does not assert joint local uniformity for lexicographically labeled finite cutoffs.

## S9-005: Lemma 9.1(ii): continuity at each real-type base.

- Each ordinary signed boundary coordinate is continuous at every real-type source under arbitrary complex source perturbations.
- The implementation also proves continuity in the full lp displacement norm and one source neighborhood controlling all signed coordinates of both ordinary sequences.

Public evidence: `NLS.ZakharovShabat.sourceLemma9_1_real`, `NLS.ZakharovShabat.SourceLemma9_1RealData.continuous`, `NLS.ZakharovShabat.SourceLemma9_1RealData.norm_continuity`, `NLS.ZakharovShabat.SourceLemma9_1RealData.exists_uniform_coordinate_neighborhood`, `NLS.ZakharovShabat.exists_sourceBoundaryDisplacement_analytic_common_domain`.

The coordinate result includes the finite central block. No global continuity of lexicographic labels at arbitrary complex bases is assumed.

## S9-006: Lemma 9.1(iii): ordinary Dirichlet and Neumann roots in their indexed periodic gaps.

- At real-type sources both ordinary roots at index n lie in the original closed periodic gap n, with strict separation from the neighboring gaps.
- The endpoints may coincide. In a collapsed gap either boundary root equals the common endpoint.

Public evidence: `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_mem_gap`, `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_interlacing_chain`, `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap`, `NLS.ZakharovShabat.SourceLemma9_1RealData.real`.

The chain is lambda_(n-1)^+ < lambda_n^- <= mu_n,nu_n <= lambda_n^+ < lambda_(n+1)^-. It places no ordering between mu_n and nu_n and covers every integer index.

## S9-007: Proof of Lemma 9.1: analytic products, Rouche continuity and transported signed discriminant levels.

- Joint analytic approximation supplies the product argument omitted in the source. Stable Rouche prefix and suffix counts and imaginary-part confinement give the real-base coordinate continuity.
- The indexed gap inequalities are transferred from real finite Fourier approximants using continuity. The signed discriminant level at either boundary root follows on that original indexed gap.

Public evidence: `NLS.ZakharovShabat.localUniformAnalyticApproximation_boundaryCharacteristic`, `NLS.ZakharovShabat.continuousAt_canonicalBoundaryRoots_re_of_realType`, `NLS.ZakharovShabat.continuousAt_canonicalBoundaryRoots_of_realType`, `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_mem_gap_finite`, `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_mem_gap`, `NLS.ZakharovShabat.signed_discriminant_periodOneBoundaryRoot_ge_two`.

The proof retains the original gap index through approximation; the unsigned or signed superlevel condition alone would not identify it. The continuity proof permits complex perturbations and counts multiplicities.

## S9-008: Auxiliary analogues and the two physical monodromy displays.

- Both actual auxiliary characteristics have the same joint analyticity, literal negative products, exact spectra and zero multiplicities. At real-type sources their coordinates are continuous and lie in the same original indexed periodic gaps.
- The physical monodromy display with +i(m3+m2) is the actual Neumann* characteristic; the display with -i(m3+m2) is the actual Dirichlet* characteristic.

Public evidence: `NLS.ZakharovShabat.sourceLemma9_1_auxiliary`, `NLS.ZakharovShabat.SourceLemma9_1AuxiliaryData.product`, `NLS.ZakharovShabat.SourceLemma9_1AuxiliaryData.multiplicity`, `NLS.ZakharovShabat.SourceLemma9_1AuxiliaryRealData.interlacing`, `NLS.ZakharovShabat.canonicalPeriodicEndpoints_sourcePhase`, `NLS.ZakharovShabat.sourceAuxiliaryCharacteristic_eq_l2_monodromy`, `NLS.ZakharovShabat.sourceLemma9_1_printed_starredDirichlet`, `NLS.ZakharovShabat.sourceLemma9_1_printed_starredNeumann`.

The correction preserves the endpoint-domain labels defined on printed p.33. Phase conjugation preserves periodic spectrum and multiplicities; ordered spectral-data uniqueness preserves the gap indices. The existing positive normalization identities are reused; no new counterexample or refutation is added.

## S9-009: Anti-discriminant as the monodromy off-diagonal sum and auxiliary difference.

- The anti-discriminant is the actual physical monodromy off-diagonal sum m2+m3.
- With the original endpoint-domain labels its auxiliary expression is actual Neumann* minus actual Dirichlet*. This is the difference of the printed plus and minus monodromy expressions.

Public evidence: `NLS.ZakharovShabat.l2AntiDiscriminant`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_l2`, `NLS.ZakharovShabat.classicalAntiDiscriminant_eq_auxiliary_sub`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_products`.

This is the same auxiliary-label correction as S9-008, applied to the difference formula. The printed algebra is valid if its symbols denote the printed expressions, while the domain-consistent symbolic difference is N*-D*.

## S9-010: Lemma 9.2(i): analytic extension of the anti-discriminant.

- The normalized anti-discriminant is jointly analytic on the entire original complex source space at every finite p>1.
- Physical Hilbert agreement in both exponent directions and finite Fourier uniqueness fix the exact function.

Public evidence: `NLS.ZakharovShabat.SourceLemma9_2Data.analytic`, `NLS.ZakharovShabat.sourceLemma9_2`, `NLS.ZakharovShabat.sourceAntiDiscriminant_eq_l2_of_two_le`, `NLS.ZakharovShabat.sourceAntiDiscriminant_eq_l2_of_le_two`, `NLS.ZakharovShabat.sourceAntiDiscriminant_unique_joint_continuous`.

The legacy name sourceAntiDiscriminantCandidate denotes the proved normalized extension. Equality is literal, not only equality of squares or zeros.

## S9-011: Lemma 9.2(ii): discriminant identity at simple Dirichlet roots.

- At every actual ordinary Dirichlet zero, Delta(z)^2-4 equals delta(z)^2.
- The identity is also instantiated at every canonical signed Dirichlet coordinate.

Public evidence: `NLS.ZakharovShabat.sourceLemma9_2_identity`, `NLS.ZakharovShabat.SourceLemma9_2Data.identity`, `NLS.ZakharovShabat.sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot`.

The implementation strengthens the source simple-eigenvalue assertion to all zeros, including multiple zeros, by substituting into the global characteristic identity.

## S9-012: Lemma 9.2(iii): locally uniform full value and derivative sample sequences in lp.

- The full actual value and derivative sample sequences delta(mu_n) and deltaPrime(mu_n) are lp elements.
- At each arbitrary complex source one open neighborhood and one finite norm bound control both complete sequences for every nearby source.

Public evidence: `NLS.ZakharovShabat.sourceDirichletAntiDiscriminantSamples`, `NLS.ZakharovShabat.sourceDirichletAntiDiscriminantDerivativeSamples`, `NLS.ZakharovShabat.sourceDirichletAntiDiscriminantSamples_apply`, `NLS.ZakharovShabat.sourceDirichletAntiDiscriminantDerivativeSamples_apply`, `NLS.ZakharovShabat.SourceLemma9_2Data.value_norm`, `NLS.ZakharovShabat.SourceLemma9_2Data.derivative_norm`, `NLS.ZakharovShabat.sourceLemma9_2`.

These are the actual canonical samples, including all central indices. The full-sample neighborhood is not required to be convex or contain zero; neither condition is stated in the source.

## S9-013: Proof of analytic extension by the auxiliary difference.

- Subtracting the two jointly analytic actual auxiliary characteristics gives the analytic anti-discriminant on the original source domain.

Public evidence: `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate`, `NLS.ZakharovShabat.analyticOnNhd_sourceAntiDiscriminantCandidate_joint`, `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_eq_products`.

This proof uses actual N*-D*, consistently with S9-008 and S9-009. The three corrected groups record one existing label discrepancy at its three occurrences, not three independent errors.

## S9-014: Proof of the Dirichlet identity by Hilbert agreement, simple-root branches and density.

- Any simple ordinary characteristic zero at an arbitrary complex original source now constructs an analytic local branch, with no preselected continuous root map. The characteristic derivative remains nonzero on its open neighborhood.
- Actual restricted-operator algebraic multiplicity one gives a local analytic eigenvalue branch retaining that multiplicity. On the Dirichlet branch the exact discriminant identity holds throughout the neighborhood.
- Separately, the global identity Delta^2-4=delta^2-4*chiD*chiN extends from finite Fourier inputs by density and joint continuity, yielding the identity even at multiple zeros.

Public evidence: `NLS.ZakharovShabat.exists_local_analytic_sourceBoundary_zero`, `NLS.ZakharovShabat.exists_local_analytic_sourceBoundary_eigenvalue`, `NLS.ZakharovShabat.sourceLemma9_2_local_analytic_branch`, `NLS.ComplexAnalysis.exists_analytic_implicitBanachRoot`, `NLS.ZakharovShabat.deriv_periodOneBoundaryCharacteristic_ne_zero_of_multiplicity_one`, `NLS.ZakharovShabat.sourceDiscriminant_sq_sub_four_finite_of_exponent`, `NLS.ZakharovShabat.sourceDiscriminant_sq_sub_four`.

The new branch theorem supplies the source implicit-function intermediate statement. It does not identify the branch with a globally lexicographic coordinate at complex sources. The identity itself uses a stronger global proof and needs no simplicity assumption.

## S9-015: Auxiliary sine errors, lp disk majorants and the Cauchy derivative estimate.

- The two auxiliary free-sine errors have common locally uniform lp majorants on half-pi disks. Their difference cancels the free sine, and the derivative difference cancels the free cosine.
- Cauchy estimates on quarter-pi disks supply the explicit factor 4/pi with the same majorant chosen before the spectral samples.
- Tail Dirichlet roots lie in their free disks. A common bounded spectral box and compact-parameter bounds control the central roots and both sampled quantities, giving full locally uniform lp bounds.

Public evidence: `NLS.ZakharovShabat.exists_uniform_auxiliaryCharacteristic_disc_majorants`, `NLS.ZakharovShabat.exists_uniform_sourceAntiDiscriminant_disc_majorants`, `NLS.ZakharovShabat.exists_uniform_sampled_sourceAntiDiscriminant`, `NLS.ZakharovShabat.exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail`, `NLS.ZakharovShabat.exists_local_uniform_sourceAntiDiscriminant_on_ball`, `NLS.ZakharovShabat.exists_local_uniform_sampled_sourceAntiDiscriminant_at_dirichletRoots`, `NLS.ZakharovShabat.SourceLemma9_2Data.disc_majorant`.

The majorant is selected before the samples; no sampler continuity is assumed. The finite central estimate is essential because central roots need not lie in their corresponding free disks. It does not assume continuity of central complex labels.

The [new local branch module](../NLS/ZakharovShabat/SourceSection9SimpleBranches.lean)
contains three positive existence and identity theorems. Integration examples
at p=3/2 construct a Neumann branch through the free zero mode and an analytic
square root of the moving shifted discriminant along a complex Dirichlet branch.

Continue in source order with Section 10. This section ledger preserves all
the unresolved qualifications listed above.
