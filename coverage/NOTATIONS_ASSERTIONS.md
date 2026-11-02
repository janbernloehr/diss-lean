# Notation-page comparison

The 38 notation groups on printed p.145 are mapped to their original objects, normalization conventions and explicit domains. The two printed columns interleave in the text extraction; each exact source interval is retained. These are definition and convention comparisons, with the qualifications below. This documentation step adds no Lean proof or refutation and does not certify whole-dissertation completeness.

| Group | Source text lines | Notation | Status |
| --- | --- | --- | --- |
| NOT-001 | 11770–11794 | Original periodic Fourier-Lebesgue carriers and their scalar weighted coefficient realization. | matched |
| NOT-002 | 11801–11807, 11813–11813 | Common almost-real neighborhood and local isolating disc families. | matched |
| NOT-003 | 11808–11808 | Full closed vertical strip of half-width pi/2. | matched |
| NOT-004 | 11816–11816 | Open disk centered at n*pi with radius pi/4. | matched |
| NOT-005 | 11821–11821 | The real isospectral set is exactly equality of the entire discriminant. | matched |
| NOT-006 | 11770–11783 | Actual physical expression diag(i,-i) times the derivative plus the off-diagonal potential. | matched |
| NOT-007 | 11804–11807 | The vector transformation T has factor 1/sqrt(2). | matched |
| NOT-008 | 11859–11861 | Principal square root of the normalized action. | matched |
| NOT-009 | 11867–11875 | Free reference roots and the zero-index product denominator. | matched |
| NOT-010 | 11878–11883 | F_n is the endpoint-normalized primitive and F is F_0. | matched |
| NOT-011 | 11851–11854 | The literal psi product has prefactor -2/pi_n and factor denominators pi_m. | matched |
| NOT-012 | 11863–11866 | The modified zeta omits two indices and retains i divided by the additionally omitted standard root. | matched |
| NOT-013 | 11867–11871 | Chi is the product of critical-root numerators divided by standard roots, omitting n. | matched |
| NOT-014 | 11885–11885 | The standard root uses (tau-z)*sqrt(1-gamma^2/(4*(tau-z)^2)). | matched |
| NOT-015 | 11886–11891 | The canonical root is 2i times the symmetric product of standard roots divided by pi_m. | matched |
| NOT-016 | 11774–11776 | The physical real form is conjugate pairing of the two fields. | matched |
| NOT-017 | 11790–11794 | The real sequence carrier consists of real raw coefficients with the original weighted norm. | matched |
| NOT-018 | 11795–11796 | The nonnegative cone has real nonnegative coordinates. | matched |
| NOT-019 | 11819–11819 | Z_n is the zero-gap locus within the selected common source neighborhood. | matched |
| NOT-020 | 11826–11827 | The two canonical sequences enumerate the actual periodic endpoints. | matched |
| NOT-021 | 11829–11830, 11834–11838 | G_n is the straight segment, gamma_n the oriented endpoint difference, and tau_n their midpoint. | matched |
| NOT-022 | 11832–11832 | Mu_n denotes the canonical ordinary Dirichlet root. | matched |
| NOT-023 | 11840–11840 | The discriminant is the trace of the monodromy. | matched |
| NOT-024 | 11842–11842 | The anti-discriminant is the sum of the off-diagonal monodromy entries. | matched |
| NOT-025 | 11786–11789 | P swaps the two vector components. | matched |
| NOT-026 | 11791–11794 | R multiplies the first component by i and the second by -i. | matched |
| NOT-027 | 11796–11800 | J sends (u_minus,u_plus) to (u_plus,-u_minus). | matched |
| NOT-028 | 11808–11818 | The signed free waves are (0,exp(i*n*pi*x)) and (exp(-i*n*pi*x),0). | matched |
| NOT-029 | 11831–11834 | Sesquilinear and real dual products retain the Section 2 Fourier conventions. | matched |
| NOT-030 | 11836–11836 | The Poisson bracket has factor -i and physical matrix J. | matched |
| NOT-031 | 11851–11856 | H1 is the physical mass and H=H3 is kinetic plus quartic NLS energy. | matched |
| NOT-032 | 11863–11866 | The gap-weighted coordinates are gamma_n times exp(plus/minus i eta_n) on open gaps. | matched |
| NOT-033 | 11855–11861 | The single-omitted zeta is the product of (sigma_k-z)/w_k over k different from m. | matched |
| NOT-034 | 11872–11877 | Sine is minus the symmetric free product, with the exceptional denominator at zero. | matched |
| NOT-035 | 11846–11850 | The discriminant derivative has the critical-point product with prefactor two. | matched |
| NOT-036 | 11841–11845 | The squared discriminant minus four is -4 times the paired endpoint product. | matched |
| NOT-037 | 11892–11894 | The starred terminal root is normalized to the anti-discriminant at the Dirichlet root. | matched |
| NOT-038 | 11823–11823, 11825–11825, 11828–11828 | The dot denotes the spectral derivative, d the source differential, and the partial symbol its gradient representative. | matched |

## Compared notation

### NOT-001: Original periodic Fourier-Lebesgue carriers and their scalar weighted coefficient realization.

The positive physical period and real Sobolev order remain explicit. The native carrier uses original smooth-test distributions. Pair conventions retain the separate infinity norm described in the Section 2 comparison; this row does not identify it with the maximum product norm. The zero-order abbreviations specialize s=0 and physical period one, using the exact equality of the order-zero weight with the unit weight; H^s specializes p=2.

Public declarations:

- `NLS.Fourier.FourierLebesgueSpace`
- `NLS.Fourier.PeriodicFourierLebesgue.coefficientsIsometry`
- `NLS.Weight.sobolev_zero_eq_one`

### NOT-002: Common almost-real neighborhood and local isolating disc families.

Finite p>1; one local family works for every nearby source and every spectral index. Real centers, quantitative separation and the exact free tail remain part of the theorem.

Public declarations:

- `NLS.ZakharovShabat.sourceLemma10_1`

### NOT-003: Full closed vertical strip of half-width pi/2.

The unpunctured strip is used, including its central lattice point.

Public declarations:

- `NLS.ZakharovShabat.resonantStrip`

### NOT-004: Open disk centered at n*pi with radius pi/4.

The definition retains the open boundary convention.

Public declarations:

- `NLS.ZakharovShabat.refinedResonantDisk`

### NOT-005: The real isospectral set is exactly equality of the entire discriminant.

Finite p>1 and the real-type source locus are retained.

Public declarations:

- `NLS.ZakharovShabat.mem_sourceIsospectralSet_iff_discriminant_eq`

### NOT-006: Actual physical expression diag(i,-i) times the derivative plus the off-diagonal potential.

The definition uses actual component derivatives; domains and almost-everywhere realizations retain their separate existing hypotheses.

Public declarations:

- `NLS.ZakharovShabat.physicalOperator`

### NOT-007: The vector transformation T has factor 1/sqrt(2).

This is the vector-coordinate normalization. The separately normalized potential transformation remains as in the existing AKNS domain comparison.

Public declarations:

- `NLS.ZakharovShabat.aknsToZS`

### NOT-008: Principal square root of the normalized action.

At a collapsed gap the analytic normalized-action extension is used. The raw quotient 4I/gamma^2 is interpreted only off collapse.

Public declarations:

- `NLS.ZakharovShabat.sourceNormalizedActionRoot`

### NOT-009: Free reference roots and the zero-index product denominator.

Zero displacement gives n*pi. The denominator is n*pi for nonzero n and one at n=0.

Public declarations:

- `NLS.ZakharovShabat.displacedRoots`
- `NLS.ZakharovShabat.singleSpectralDenominator`

### NOT-010: F_n is the endpoint-normalized primitive and F is F_0.

The original complex primitive uses the common Section 19 source data. Either endpoint integral agrees with it on the root domain; F_n=F_0+i*pi*n. No claim is made from the real-source primitive alone.

Public declarations:

- `NLS.ZakharovShabat.SourceSection19Data.endpoint_integrals`
- `NLS.ZakharovShabat.SourceSection19Data.index_shift`

### NOT-011: The literal psi product has prefactor -2/pi_n and factor denominators pi_m.

The denominator printed on this final notation page agrees with the implemented correction to the earlier Section 7 display. This row concerns the product identity; unrestricted period uniqueness is established in its separate Section 7 publication.

Public declarations:

- `NLS.ZakharovShabat.sourceSection7_psi_product`

### NOT-012: The modified zeta omits two indices and retains i divided by the additionally omitted standard root.

The selected psi family is an explicit displacement parameter although the notation suppresses it. The product identity is literal, with no division by numerator factors; its analytic use retains the established root-domain hypotheses.

Public declarations:

- `NLS.ZakharovShabat.sourcePsiZeta_eq_product`

### NOT-013: Chi is the product of critical-root numerators divided by standard roots, omitting n.

The product and its root domain retain the finite-exponent and omitted-factor hypotheses. The derivative quotient carries its separately proved -i factor.

Public declarations:

- `NLS.ZakharovShabat.sourceActionChi`

### NOT-014: The standard root uses (tau-z)*sqrt(1-gamma^2/(4*(tau-z)^2)).

The formula uses the principal square root and its existing spectral-domain interpretation.

Public declarations:

- `NLS.ZakharovShabat.normalizedStandardRoot`

### NOT-015: The canonical root is 2i times the symmetric product of standard roots divided by pi_m.

The definition and its convergence retain the common root domain and finite p>1. This is not a claim about arbitrary branch choices.

Public declarations:

- `NLS.ZakharovShabat.sourceCanonicalRoot`

### NOT-016: The physical real form is conjugate pairing of the two fields.

In ordinary scalar Fourier coefficients physical conjugation reverses the frequency. The native bridge acts on every original smooth periodic test, preserves the exact symmetric weighted norm, and identifies the real-pair condition at every positive period, real Sobolev order and Banach exponent including infinity. The existing zero-order source locus has the same coefficient reflection. The coordinatewise-real sequence target and the Section 2 pair-norm convention remain distinct.

Public declarations:

- `NLS.Fourier.PeriodicFourierLebesgue.norm_conjugate`
- `NLS.Fourier.PeriodicFourierLebesgue.sobolev_real_pair_iff`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.conjugate_apply`
- `NLS.Fourier.SmoothPeriodicTest.Distribution.eq_conjugate_iff_coefficients`
- `NLS.ZakharovShabat.IsRealType`
- `NLS.ZakharovShabat.realTypeSourceLocus`

### NOT-017: The real sequence carrier consists of real raw coefficients with the original weighted norm.

Take the product of two such real spaces for the rectangular pair target. Positive weighting preserves and reflects reality. These are not the physical conjugate-pair source coordinates.

Public declarations:

- `NLS.WeightedCoeff.realLocus`
- `NLS.WeightedRealCoeff`

### NOT-018: The nonnegative cone has real nonnegative coordinates.

Zero coefficients are included. The inherited weighted cone is identified with the unweighted cone by positive weighting.

Public declarations:

- `NLS.WeightedCoeff.nonnegativeLocus`

### NOT-019: Z_n is the zero-gap locus within the selected common source neighborhood.

The analytic defining function is the squared canonical gap; its zero set is exactly the zero set of the oriented gap. The chosen ambient W remains explicit.

Public declarations:

- `NLS.ZakharovShabat.mem_sourceActionGapZeroLocus_iff`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus`

### NOT-020: The two canonical sequences enumerate the actual periodic endpoints.

The original global lexicographic labeling and multiplicities are retained, with the established finite p>1 and period-one embedding hypotheses.

Public declarations:

- `NLS.ZakharovShabat.canonicalPeriodicEndpoints_exhaustive`
- `NLS.ZakharovShabat.canonicalPeriodicLeft`
- `NLS.ZakharovShabat.canonicalPeriodicRight`

### NOT-021: G_n is the straight segment, gamma_n the oriented endpoint difference, and tau_n their midpoint.

For complex sources the segment is the real affine segment joining complex endpoints. The midpoint and gap formulas retain their literal factors.

Public declarations:

- `NLS.ZakharovShabat.canonicalPeriodicGap`
- `NLS.ZakharovShabat.canonicalPeriodicMidpoint`
- `NLS.ZakharovShabat.sourcePeriodicSegment`

### NOT-022: Mu_n denotes the canonical ordinary Dirichlet root.

Specialize the boundary condition to dirichlet. The actual ordinary interval extension and original algebraic multiplicities are retained.

Public declarations:

- `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots`
- `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_exhaustive`
- `NLS.ZakharovShabat.canonicalPeriodOneBoundaryRoots_multiplicity`

### NOT-023: The discriminant is the trace of the monodromy.

The classical definition is literal; the completed source function agrees on dense finite Fourier data and retains the previously reviewed extension.

Public declarations:

- `NLS.ZakharovShabat.canonicalDiscriminant_finite_eq_classical`
- `NLS.ZakharovShabat.classicalDiscriminant`

### NOT-024: The anti-discriminant is the sum of the off-diagonal monodromy entries.

The completed source candidate uses the domain-based Neumann-minus-Dirichlet auxiliary characteristics. Its finite-source normalization agrees with the actual monodromy anti-trace.

Public declarations:

- `NLS.ZakharovShabat.classicalAntiDiscriminant`
- `NLS.ZakharovShabat.sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent`

### NOT-025: P swaps the two vector components.

The matrix acts as the existing Prod.swap operation. Its ODE covariance uses the separately signed potential swap; the vector swap itself introduces no sign.

Public declarations:

- `NLS.ZakharovShabat.classicalODECoefficient_swap`

### NOT-026: R multiplies the first component by i and the second by -i.

The exact coefficient phase acts componentwise, with the same physical normalization.

Public declarations:

- `NLS.ZakharovShabat.auxiliaryPotential_apply`

### NOT-027: J sends (u_minus,u_plus) to (u_plus,-u_minus).

Signed pair coordinates require frequency reflection; the physical formula has the printed signs.

Public declarations:

- `NLS.Poisson.signedJ`
- `NLS.Poisson.signedJ_physical`

### NOT-028: The signed free waves are (0,exp(i*n*pi*x)) and (exp(-i*n*pi*x),0).

Substitute z=n*pi and the two coordinate vectors in the literal free evolution. These are period-two spectral waves; unit-period Fourier extraction uses its established rescaling.

Public declarations:

- `NLS.ZakharovShabat.classicalFreeVector`

### NOT-029: Sesquilinear and real dual products retain the Section 2 Fourier conventions.

The pair product sums component sesquilinear products. Physical real duality uses the bilinear product with opposite scalar Fourier indices. Conjugate Sobolev orders and exponents are explicit, and the separate infinity pair norm remains as in Section 2.

Public declarations:

- `NLS.WeightedCoeff.sobolevBilinearPairing_apply`
- `NLS.WeightedCoeffPair.sobolevSesquilinearPairing_physical`

### NOT-030: The Poisson bracket has factor -i and physical matrix J.

Automatic full-gradient recovery uses finite source exponents, including p=1 with its separate infinity pair norm. Functionals on an infinity-exponent source require supplied representatives as already qualified in Section 2. No closure assertion for arbitrary nested brackets is added.

Public declarations:

- `NLS.Poisson.commonSobolevBracket_physical`

### NOT-031: H1 is the physical mass and H=H3 is kinetic plus quartic NLS energy.

The hierarchy identities retain the unit-period normalization. The integration-by-parts identity for H3 is stated for smooth periodic fields; the same integral energy is defined on all complex H1 pairs. The full H0 mass identity is also covered by the published Appendix H physical Hamiltonian integral step.

Public declarations:

- `NLS.ZakharovShabat.appendixH_hamiltonian_eq_integral_of_coefficients`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_one`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_three`
- `NLS.ZakharovShabat.periodOneSobolevHamiltonian_eq_integral`
- `NLS.ZakharovShabat.periodOneSobolevMass_eq_integral`

### NOT-032: The gap-weighted coordinates are gamma_n times exp(plus/minus i eta_n) on open gaps.

The eta is the original normalized integral phase. Collapsed gaps use the analytic extension and its open-gap limits, rather than assigning an angle there.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_signed`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_phase_limit`

### NOT-033: The single-omitted zeta is the product of (sigma_k-z)/w_k over k different from m.

The entire selected root family is an explicit displacement parameter; the product is evaluated on the standard-root omitted domain. Numerator zeros are allowed.

Public declarations:

- `NLS.ZakharovShabat.hasProd_sourceSingleRootQuotient_subtype`

### NOT-034: Sine is minus the symmetric free product, with the exceptional denominator at zero.

Set the displacement sequence to zero; the symmetric finite products converge with exactly the printed minus sign.

Public declarations:

- `NLS.ZakharovShabat.appendixDProduct_zero`
- `NLS.ZakharovShabat.tendsto_appendixDProduct`

### NOT-035: The discriminant derivative has the critical-point product with prefactor two.

The critical sequence is the actual complete ordered sequence. Its product retains the exceptional zero denominator and symmetric cutoff normalization.

Public declarations:

- `NLS.ZakharovShabat.discriminant_derivative_eq_canonicalCriticalProduct`
- `NLS.ZakharovShabat.singleSpectralPartialProduct`

### NOT-036: The squared discriminant minus four is -4 times the paired endpoint product.

The actual canonical endpoints give the complete entire product. The zero-mode denominator is one, the prefactor is -4, and local uniform convergence includes the free lattice.

Public declarations:

- `NLS.ZakharovShabat.canonicalPeriodicEndpoints_product`
- `NLS.ZakharovShabat.canonicalPeriodic_eq_discriminant_sq_sub_four_finite`
- `NLS.ZakharovShabat.spectralPairPartialProduct`
- `NLS.ZakharovShabat.tendstoLocallyUniformlyOn_entireSpectralPairProduct`

### NOT-037: The starred terminal root is normalized to the anti-discriminant at the Dirichlet root.

At a nonzero terminal anti-discriminant the prescribed analytic sheet realizes this equality and persists locally. The square identity includes zero terminal values and multiple roots; no regular analytic square-root neighborhood is asserted at a zero terminal value.

Public declarations:

- `NLS.ZakharovShabat.exists_local_sourceAngularRootSheet_dirichlet_normalization`
- `NLS.ZakharovShabat.sourceAngularRootSheet_dirichlet_base`
- `NLS.ZakharovShabat.sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot`

### NOT-038: The dot denotes the spectral derivative, d the source differential, and the partial symbol its gradient representative.

This row reconciles notation, rather than asserting differentiability for an arbitrary function. The source discriminant uses deriv in the complex spectral variable and fderiv in the potential; their interchange theorem retains finite p>1. For a finite source exponent the full continuous differential has a unique reciprocal-Sobolev gradient under the physical bilinear pairing: the finite conjugate pair norm for p>1, and the separate infinity pair norm for p=1. No automatic representation of every functional on an infinity-exponent source is asserted; any use there retains its supplied-representative hypothesis.

Public declarations:

- `NLS.WeightedCoeffPair.existsUnique_sobolevFiniteGradient`
- `NLS.WeightedCoeffPair.existsUnique_sobolevOneGradient`
- `NLS.WeightedCoeffPair.sobolevFiniteGradient_represents`
- `NLS.WeightedCoeffPair.sobolevOneGradient_represents`
- `NLS.ZakharovShabat.fderiv_source_discriminant_deriv_eq_deriv_spectral_fderiv_source`
- `NLS.ZakharovShabat.sourceDiscriminantCotangent`

## Scope and evidence

The original positive period, all real Sobolev orders, physical conjugation and exact weighted norm are retained in the [native conjugation bridge](../NLS/Fourier/NativePeriodicConjugation.lean). Pair norms and reciprocal-domain hypotheses remain as in [Section 2](SECTION_2.md).

The [Section 7 comparison](SECTION_7_ASSERTIONS.md) records the psi normalization and period uniqueness. The [Appendix H comparison](APPENDIX_H_ASSERTIONS.md) supplies actual Hamiltonian integrals at the original regularity.

The supporting-module hashes and the inspected body scopes are recorded in the source-review index. This mapping combines selected body reads with earlier source comparisons; it does not claim a fresh audit of every transitive dependency.

The [broader completion qualifications](COMPLETENESS.md) remain, including the exact 2014 construction comparison and the unresolved rough description of sheet signs as NLS motion directions.

## Validation

The unchanged Lean snapshot reuses the full check at commit c23702bdbb42dd6a2566cd5173c587f7ce41d82e: 8,654 build jobs, 7,729 public examples and an axiom audit of 45,116 NLS declarations. The 21 inherited warnings are unchanged and there are no new warnings. All 76 declaration references, 55 supporting-module hashes, the review index and local links are checked again. This establishes validation of the recorded snapshot, not complete formalization of the dissertation.
