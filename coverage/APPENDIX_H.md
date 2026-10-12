# Appendix H: current source audit

This compares the formulas and numbered results on printed pages 138–139
with the public Lean API. It supersedes the historical Appendix H progress
notes in `COVERAGE.md`, without certifying the rest of the dissertation.
All listed declarations are in `NLS.ZakharovShabat`.

| Source requirement | Public entry points | Current scope |
| --- | --- | --- |
| Riccati recurrence | `nlsRiccatiDensity_succ_succ`, `sobolevRiccatiDensity_succ_succ`, `weakSobolevRiccatiDensity_apply` | Actual differentiation and products, with Fourier convolution on Sobolev inputs and a weak derivative at the final H^-1 boundary. The Lean index n denotes u_(n+1). |
| Hamiltonian normalization | `classicalNLSHamiltonian`, `sobolevNLSHamiltonian_succ_eq_tsum`, `sobolevNLSHamiltonian_eq_classical` | The original factor (-i)^(k+1) and integral of the first field times u_k over the unit period. The Fourier mean is absolutely convergent; smooth agreement uses actual physical integrals. |
| Printed H^(k-1) domain | `analyticAt_sobolevNLSHamiltonian`, `sobolevNLSHamiltonian_one`, `sobolevNLSHamiltonian_two` | Every admissible k<=s+1 on the full complex H^s source; mass includes H^0, and momentum retains the original 2*pi frequency and sign. |
| H.1 leading derivative | `sourceLemmaH1`, `sourceLemmaH1_weak`, `sourceLemmaH1_distribution` | u_(k+1)=-b^(k)+q_k on all complex H^(k-1) sources, including its actual H^-1 and tempered-distribution meanings. |
| H.1 polynomial restrictions | `sourceLemmaH1_polynomial` | One input-independent polynomial of total weight k+1; after multiplication by the first field, balanced field counts and at most k-2 derivatives. Every remainder jet has order at most k-2. |
| Rescaling used in H.1's proof | `nlsRiccatiDensity_field_rescaling`, `sobolevRiccatiDensity_field_rescaling`, `weakSobolevRiccatiDensity_field_rescaling` | u_k(a,c*b)=c*u_k(c*a,b) for every complex scalar, including zero; actual classical, Sobolev, and weak densities are identified. |
| H.2's single polynomial | `sourceCorollaryH2`, `sourceH2Polynomial_properties` | For each m>=1, one polynomial works for every real H^m source, uses jets through m-1, has total weight 2m+2, and has balanced field counts. |
| H.2's physical integral | `sourceCorollaryH2_integral`, `sobolevOddHamiltonian_eq_physical_integral` | Actual squared top derivative plus the same lower-jet polynomial on real inputs; bilinear top-derivative formula on all complex H^m pairs. |
| Top derivative and extension | `hierarchySobolevJetL2_distribution_iterate`, `integral_sq_sobolevTopJetPhysical`, `sobolevOddHamiltonian_unique_continuous` | Actual distributional derivatives, square integrability and exact unit-period Parseval; unique continuous Hamiltonian extension from smooth sources. |
| Hamiltonian rescaling consequence | `sobolevNLSHamiltonian_field_rescaling`, `sobolevOddHamiltonian_field_rescaling` | Moving a scalar between the fields preserves the physical Hamiltonian, on both its original regularity range and the sharper H^m odd-Hamiltonian domain. |
| Reciprocal rescaling | `sobolevNLSHamiltonian_reciprocal_rescaling`, `sobolevOddHamiltonian_reciprocal_rescaling` | For c nonzero, replacing (a,b) by (c*a,c^(-1)*b) preserves the actual Hamiltonians on those same domains. |

The highest derivative in H.1 need not be a function at the printed
regularity. It is interpreted as the actual weak derivative, not assumed
to have extra regularity. At k=1 the remainder polynomial vanishes, which
also accounts for the negative derivative-count bound.

The H.2 identity retains its H^m domain; it does not require H^(2m). The
polynomial is chosen before the potential, and its physical integral is
not replaced by a spectral action sum. The Sobolev rescaling identities
follow from the physical smooth identities, continuity, and dense smooth
Fourier sources. No nonzero-scalar hypothesis enters the basic rescaling
identity; that hypothesis is used only for reciprocal rescaling.

No source correction is recorded here for H.1 or H.2. The separate accepted
factor-two correction to Lemma 27.2 and its optional original m=1 sharpening
remain as recorded in `SOURCE_ERRATA.md`; these are not consequences of
merely proving the Appendix H identities.
