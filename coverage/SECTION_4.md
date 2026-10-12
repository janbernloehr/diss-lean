# Section 4: Dirichlet and Neumann spectra

This is a statement-by-statement audit against the original spaces and
physical expressions on printed pages 28 onward. Existing later results do
not by themselves certify this section or the full dissertation complete.

## Equations (1.6)–(1.7) and the AKNS coordinates (pages 28–29)

All coordinates and potentials may be complex. The original scalar H¹
condition is absolute continuity on [0,1] and square integrability of the
actual derivative. Domain vectors are actual closed-interval functions.
The physical L² and H¹ norms use the sum of the component energies.

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Normalized T and inverse | `aknsCoordinateEquiv`, `zsToAKNS_aknsToZS`, `aknsToZS_zsToAKNS` | Exact normalized vector coordinates, arbitrary complex pairs. |
| Both endpoint conditions in (1.6) | `aknsToZS_dirichlet_iff`, `aknsToZS_neumann_iff` | Equal ZS components iff second AKNS component vanishes; opposite iff first vanishes. |
| Original H¹ domain correspondence | `hasClassicalIntervalDomain_aknsToZS_iff`, `hasAKNSIntervalDomain_zsToAKNS_iff` | Both directions, both boundaries; no assumed periodicity or external regularity. |
| Actual closed-interval AKNS domain | `AKNSIntervalDomain`, `mem_aknsIntervalSubmodule_iff` | Membership is exactly representability by original H¹ data with the specified endpoints. |
| Physical L² unitary | `aknsL2Equiv` | Linear isometric equivalence of the original component-sum Lebesgue spaces, with a.e. pointwise realization. |
| Exact physical H¹ norm | `classicalIntervalNorm_aknsToZS`, `norm_aknsDomainOfFunction`, `aknsDomainEquiv` | Full value and derivative energies, including arbitrary original-domain representatives. |
| Original AKNS inclusion | `aknsInclusion`, `aknsInclusion_injective`, `aknsInclusion_denseRange`, `aknsInclusion_realization` | Injective dense inclusion giving the original function's actual L² class. |
| Original AKNS operator | `aknsIntervalOperator`, `aknsIntervalOperator_realization` | Bounded domain-to-L² map at arbitrary L² potentials; actual differential expression a.e. |
| Unitary conjugation | `aknsL2Equiv_inclusion`, `aknsL2Equiv_operator` | Exact identities for the actual inclusion and operator with their domain isometry. |
| Actual derivative intertwining | `deriv_aknsToZS`, `physicalOperator_aknsToZS` | Pointwise at differentiable points and a.e. on arbitrary original interval H¹ data. |
| Physical eigenvalue equations | `akns_eigenEquation_iff` | Equivalent a.e. equations under the domain correspondence, for both boundaries. |
| Component system (1.7) | `aknsAction_eigen_iff` | Exact signs and coefficients in both equations. |
| Correct potential transformation | `aknsPotential_eq_sqrt_two_smul`, `aknsAction_intertwining` | The potential map is (q+i*p,q-i*p), agreeing with printed page 19. |
| Page 29 normalization failure | `aknsAction_printed_normalization_false`, `physicalOperator_printed_akns_normalization_false` | Exact constant-data counterexamples to using normalized T on potentials as printed. |

These public entry points are in `NLS.ZakharovShabat`; Sobolev linear closure
is in `NLS.Fourier.HasIntervalH1Regularity.linearCombination`. The five new
modules are `IntervalH1Linear`, `AKNSCoordinates`, `AKNSClassicalDomain`,
`AKNSPhysicalNorms`, and `AKNSIntervalOperator`. The public examples cover
both boundary conditions, norm identities, domain membership, density,
actual inclusions/operator realizations, and the normalization counterexample.

The normalization discrepancy and its correction are recorded in
[SOURCE_ERRATA.md](../SOURCE_ERRATA.md). This audit concerns the classical
L² setting. It does not extend the interval regularity definition to all
Fourier–Lebesgue exponents; the source's later extension has 1<p<infinity.

## Reflection formulas and Lemma 4.1 (pages 28–29)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Even/odd eigenfunction extensions | `aknsIntervalExtension` | Dirichlet is even/odd; Neumann is odd/even. |
| Signed-swap coordinate formulas | `aknsToZS_intervalExtension`, `akns_intervalExtension_zsToAKNS` | Exact pointwise formulas for arbitrary original functions. |
| Common potential extension | `aknsPotential_intervalExtension`, `memLp_aknsPotentialExtension` | q even, p odd; actual Dirichlet potential extension in either boundary problem; arbitrary L² input. |
| Actual periodic H¹ AKNS representatives | `aknsCircleExtension`, `aknsCircleExtension_regular`, `aknsCircleExtension_reconstruct` | Circle functions recover the full closed-period piecewise extension, including both endpoints. |
| Extended AKNS equation | `akns_interval_equation_transfer` | Actual derivatives and a.e. equations for either original endpoint domain. |
| Both parts of Lemma 4.1 | `sourceLemma4_1` | Actual periodic H¹ circle representative, exact extension, and physical equation with the Dirichlet-reflected potential. |
| Original source potential | `sourceDirichletPotentialCoefficients`, `sourceDirichletPotentialCoefficients_coefficients`, `sourceDirichletPotentialCoefficients_reconstruct` | Exact normalized physical Fourier integrals in `CoeffPair 2`, with a.e. reconstruction. |
| Original weighted source domain | `sourceClassicalIntervalExtension`, `sourceClassicalIntervalExtension_coefficients` | Original component-sum weighted space, exact physical Fourier coefficients. |
| Actual source circle representative | `sourceClassicalCircleExtension`, `sourceClassicalCircleExtension_regular`, `sourceClassicalCircleExtension_reconstruct`, `sourceClassicalCircleExtension_restrict` | Periodic H¹ regularity, closed-period reconstruction, and exact original closed-interval values. |
| Actual original-norm operator equation | `source_classical_interval_equation_transfer` | The actual `sourceOperator` and `sourceDomainInclusion`, for arbitrary original L² potentials. |
| Nonzero source eigenvector | `sourceClassicalIntervalExtension_ne_zero`, `source_classical_interval_eigenvector_transfer` | Nonzero original interval functions remain nonzero in the actual source domain. |
| Boundary eigenvalues are periodic | `source_classical_interval_eigenvalue_mem_spectrum` | Membership in the complement of the actual original source resolvent set. |
| Exhaustion paragraph after the lemma | `source_periodicSpectrum_eq_classicalEigenvalues_union` | The source spectrum equals the union of the two original physical interval eigenvalue sets. |

The new entries are in `NLS.ZakharovShabat`, in `AKNSReflection.lean` and
`SourceLemma4_1.lean`. They reuse the proved physical reflection and
classical Fourier extension infrastructure while identifying the original
source spaces explicitly. No isometry of maximum and component-sum norms
is asserted. The physical equation transfer needs only its stated domain
and a.e. equation; Fourier and spectral conclusions require original L²
potentials. The spectrum-union theorem is a set identity, with no new
multiplicity assertion. The AKNS potential-normalization correction is
retained; the reflection signs and Lemma 4.1 need no further correction.

Public examples exercise both boundary conditions, endpoint reconstruction,
negative Fourier indices, the physical equation, nonzero original source
eigenvectors, and full spectral exhaustion.

## Next source assertions

Next audit the Fourier representations (1.8)–(1.9) on page 30 and their
original-space interpretation, followed by the extension/isomorphism
assertions. Existing Fourier and boundary-basis modules provide supporting
results but do not by themselves certify these source identifications.
