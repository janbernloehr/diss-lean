# Appendix H ordered assertion comparison

The fourteen ordered Appendix H groups comprise twelve matched, one directly corrected and one contextual passage. No partial or pending mathematical group remains within this local comparison. The original kth Hamiltonian is identified with the literal physical integral on every complex H^(k-1) source, using actual L2 representatives and the exact (-i)^(k+1) normalization. H.1 retains the actual weak H^-1 derivative and a fixed graded lower-jet polynomial. The smooth odd-Hamiltonian display uses (-1)^(m+1) on the unchanged unreduced H.1 remainder. The H.2 polynomial absorbs this phase and is chosen before all real H^m sources. The integration-by-parts reduction preserves total weight and balanced field counts. The precise 2014 reference comparison and broader dissertation completeness remain separate. Historical refutations are unchanged; no new refutations are added.

Source: printed pp.138–139, text lines 11372–11427. Line numbers count newline characters and preserve form feeds. The rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| H-001 | 11374–11375 | Literature introduction to the Hamiltonian hierarchy. | contextual |
| H-002 | 11375–11379 | The kth Hamiltonian on complex H^(k-1) has the actual physical integral with factor (-i)^(k+1). | matched |
| H-003 | 11381–11384 | The initial density and derivative-plus-product Riccati recurrence retain their source indices and signs. | matched |
| H-004 | 11395–11398 | H.1 separates the kth derivative of the second field from a fixed lower-jet remainder on H^(k-1). | matched |
| H-005 | 11400–11400 | The remainder q_k is homogeneous of total weight k+1 when each field and each derivative counts once. | matched |
| H-006 | 11401–11401 | Each monomial of the nonlinear Hamiltonian density has total derivative count at most k-2. | matched |
| H-007 | 11402–11402 | Every monomial of the nonlinear Hamiltonian density has equal first-field and second-field counts. | matched |
| H-008 | 11404–11405 | The original u_k polynomials have weight k and use derivatives only through k-1. | matched |
| H-009 | 11405–11406 | Field rescaling holds for every complex scalar, including zero. | matched |
| H-010 | 11408–11411 | The smooth real odd Hamiltonian is the top-derivative square integral plus (-1)^(m+1) times the unreduced H.1 remainder integral. | corrected |
| H-011 | 11413–11415 | Removing a factor of derivative order m+n leaves total derivative count at most m-2-n. | matched |
| H-012 | 11415–11417 | Repeated integration by parts lowers every nonlinear factor to derivative order at most m-1. | matched |
| H-013 | 11419–11424 | For each m>=1, one lower-jet polynomial gives H.2 for every real H^m source. | matched |
| H-014 | 11424–11425 | The same reduced polynomial has total weight 2m+2 and balanced field counts. | matched |

## Compared passages

### H-001: Literature introduction to the Hamiltonian hierarchy.

The attribution to references [23] and [39] is contextual. This local comparison does not resolve the precise 2014 edition comparison.

### H-002: The kth Hamiltonian on complex H^(k-1) has the actual physical integral with factor (-i)^(k+1).

Lean uses density index n=k-1. The new Parseval specialization identifies the literal integral for the synthesized L2 representatives on every complex source at the printed regularity, including H^0 for mass. The representative-independent version assumes only the original Fourier coefficients and L2 membership.

Public declarations:

- `NLS.ZakharovShabat.sobolevNLSHamiltonian_succ_eq_tsum`
- `NLS.ZakharovShabat.summable_norm_sobolevRiccatiMean`
- `NLS.ZakharovShabat.analyticAt_sobolevNLSHamiltonian`
- `NLS.ZakharovShabat.sobolevNLSHamiltonian_eq_classical`
- `NLS.ZakharovShabat.appendixH_hamiltonian_eq_physical_integral`
- `NLS.ZakharovShabat.appendixH_hamiltonian_eq_integral_of_coefficients`

### H-003: The initial density and derivative-plus-product Riccati recurrence retain their source indices and signs.

The antidiagonal sum is the source sum after shifting u_(n+1) to index n. Original period-one differentiation multiplies coefficients by 2*pi*i*j. The next density at the minimal source regularity is the actual weak H^-1 recurrence.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiDensity_zero`
- `NLS.ZakharovShabat.nlsRiccatiDensity_one`
- `NLS.ZakharovShabat.nlsRiccatiDensity_succ_succ`
- `NLS.ZakharovShabat.sobolevRiccatiDensity_succ_succ`
- `NLS.ZakharovShabat.weakSobolevRiccatiDensity_apply`
- `NLS.ZakharovShabat.weakSobolevRiccatiDensity_eq_classical_coefficients`

### H-004: H.1 separates the kth derivative of the second field from a fixed lower-jet remainder on H^(k-1).

The equality holds coefficientwise, in H^-1, and in actual tempered distributions. No additional regularity is assumed. Smooth density and continuity identify the independent recurrence with the physical hierarchy.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaH1`
- `NLS.ZakharovShabat.sourceLemmaH1_weak`
- `NLS.ZakharovShabat.sourceLemmaH1_distribution`
- `NLS.ZakharovShabat.weakSobolevRiccatiDensity_unique`

### H-005: The remainder q_k is homogeneous of total weight k+1 when each field and each derivative counts once.

The polynomial is fixed independently of its input. The jet (field,j) has total weight j+1.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiRemainder_totalWeight`
- `NLS.ZakharovShabat.sourceLemmaH1_polynomial`

### H-006: Each monomial of the nonlinear Hamiltonian density has total derivative count at most k-2.

The bound is on the sum of derivative orders, and therefore bounds every individual jet. Integer grading retains the negative bound at k=1; the remainder is zero there.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiRemainder_hamiltonian_grades`
- `NLS.ZakharovShabat.nlsRiccatiRemainder_hamiltonian_monomial`
- `NLS.ZakharovShabat.nlsRiccatiRemainder_vars`

### H-007: Every monomial of the nonlinear Hamiltonian density has equal first-field and second-field counts.

Field charge is the second-field count minus the first-field count. Multiplication by the first field changes the remainder charge one to zero.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiRemainder_fieldCharge`
- `NLS.ZakharovShabat.nlsRiccatiRemainder_hamiltonian_grades`
- `NLS.ZakharovShabat.sourceLemmaH1_polynomial`

### H-008: The original u_k polynomials have weight k and use derivatives only through k-1.

Canonical polynomial evaluation equals the actual smooth recurrence. The total derivative bound is stronger than the required individual jet bound, with the same shifted Lean index.

Public declarations:

- `NLS.ZakharovShabat.evaluate_nlsRiccatiPolynomial`
- `NLS.ZakharovShabat.nlsRiccatiPolynomial_totalWeight`
- `NLS.ZakharovShabat.nlsRiccatiPolynomial_derivativeOrder`
- `NLS.DifferentialPolynomial.DerivativeOrderLE.jet_order`

### H-009: Field rescaling holds for every complex scalar, including zero.

Recurrence uniqueness proves u_k(a,c*b)=c*u_k(c*a,b) directly. Continuity transfers it to the available Sobolev densities and the weak H^-1 boundary without dividing by c.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiDensity_field_rescaling`
- `NLS.ZakharovShabat.sobolevRiccatiDensity_field_rescaling`
- `NLS.ZakharovShabat.weakSobolevRiccatiDensity_field_rescaling`

### H-010: The smooth real odd Hamiltonian is the top-derivative square integral plus (-1)^(m+1) times the unreduced H.1 remainder integral.

Adopt the exact phase from (-i)^(2m+2) directly. The same H.1 polynomial is retained before reduction; the final H.2 polynomial absorbs the phase. Historical refutations are unchanged and no new refutation is added.

Public declarations:

- `NLS.ZakharovShabat.appendixH_odd_remainder_phase`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_odd_real_H1_remainder`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_odd_leading_remainder`
- `NLS.DifferentialPolynomial.integral_balanced_derivatives`

### H-011: Removing a factor of derivative order m+n leaves total derivative count at most m-2-n.

The exact monomial grading subtracts the removed jet order from the bound 2*m-2. The integration-by-parts implementation uses this subtraction for either field, with the coefficient and all remaining factors retained.

Public declarations:

- `NLS.ZakharovShabat.nlsRiccatiRemainder_hamiltonian_monomial`
- `NLS.DifferentialPolynomial.weight_erase_one`
- `NLS.DifferentialPolynomial.monomial_factor_jet`

### H-012: Repeated integration by parts lowers every nonlinear factor to derivative order at most m-1.

The construction records an explicit polynomial total derivative, terminates by the maximal jet order, preserves both gradings, and gives the same actual integral on every smooth periodic source.

Public declarations:

- `NLS.DifferentialPolynomial.exists_graded_jet_reduction`
- `NLS.DifferentialPolynomial.integral_evaluate_eq_of_total_derivative`
- `NLS.ZakharovShabat.exists_nlsOddRemainder_jet_reduction`
- `NLS.ZakharovShabat.exists_classicalNLSHamiltonian_odd_reduced_polynomial`

### H-013: For each m>=1, one lower-jet polynomial gives H.2 for every real H^m source.

The polynomial is chosen before the potential and uses only jets through m-1. The leading term is the actual squared L2 weak derivative with unit-period Parseval. The full H^m domain is retained; H^(2m) is not required. The complex counterpart uses the unconjugated bilinear leading integral.

Public declarations:

- `NLS.ZakharovShabat.sourceCorollaryH2`
- `NLS.ZakharovShabat.sourceCorollaryH2_integral`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_eq_physical_integral`
- `NLS.ZakharovShabat.hierarchySobolevJetL2_distribution_iterate`
- `NLS.ZakharovShabat.integral_sq_sobolevTopJetPhysical`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_unique_continuous`

### H-014: The same reduced polynomial has total weight 2m+2 and balanced field counts.

Both gradings survive the polynomial integration-by-parts reduction and multiplication by the exact scalar phase. These properties hold for the same polynomial in the physical H.2 formula.

Public declarations:

- `NLS.ZakharovShabat.sourceH2Polynomial_properties`
- `NLS.ZakharovShabat.exists_classicalNLSHamiltonian_odd_reduced_polynomial`

## Evidence and validation

The [physical Hamiltonian integral](../NLS/ZakharovShabat/AppendixHPhysicalHamiltonian.lean) retains the original regularity and normalization.
[H.1](../NLS/ZakharovShabat/SourceLemmaH1.lean) and its
[distributional identity](../NLS/ZakharovShabat/SourceLemmaH1Distribution.lean) give the weak derivative and fixed remainder.
The [polynomial reduction](../NLS/DifferentialPolynomial/IntegrationByPartsReduction.lean) records the total derivative explicitly.
[H.2](../NLS/ZakharovShabat/SourceCorollaryH2.lean) uses the same reduced polynomial for all real H^m sources.
The [phase identity](../NLS/ZakharovShabat/SourceAppendixHRemainderPhase.lean) supplies the adopted correction to the unreduced display.

The comparison records 31 complete module bodies and 46 declaration references, reconciling the earlier source and phase comparisons and the physical-integral proof publication.
It does not claim a fresh review of every transitive proof. The previous named reviews retain their historical scope.

The unchanged Lean snapshot reuses the successful full check at commit 215e703ba0c1fde380f6f2f40d6cb88810691848: 8,645 build jobs, 7,729 public examples and an axiom audit of 45,003 NLS declarations. The check has 21 inherited warnings and no new warnings. All 46 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix I. The [broader completion qualifications](COMPLETENESS.md) remain.
