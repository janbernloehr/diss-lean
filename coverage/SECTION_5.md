# Section 5: auxiliary Dirichlet and Neumann spectra

This is a statement-by-statement audit against the original physical domains,
reflections and norms, beginning on printed page 33. Existing later results
alone do not certify the section or the dissertation complete.

## Original auxiliary domains and operators: equation (1.10)

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Physical H¹ endpoint conditions | `HasClassicalAuxiliaryDomain` | Absolute continuity, square-integrable derivative, and the printed equations at both endpoints; D*: f₋+i f₊=0, N*: f₋−i f₊=0. |
| Physical closed-interval domain | `ClassicalAuxiliaryDomain`, `mem_classicalAuxiliarySubmodule_iff` | Actual functions on [0,1], with the physical H¹ norm. |
| Domain phase identification | `hasClassicalAuxiliaryDomain_phase_iff`, `classicalAuxiliaryDomainPhase` | Both directions; the phase (f₋,i f₊) takes the ordinary domain to the auxiliary domain. Physical H¹ norms are preserved. |
| Actual physical inclusion and operator | `classicalAuxiliaryInclusion`, `classicalAuxiliaryOperator` | Bounded maps from the original H¹ domain into the original component-sum physical L² space. |
| Physical realization on arbitrary representatives | `classicalAuxiliaryInclusion_ofFunction`, `classicalAuxiliaryOperator_realization_ofFunction`, `classicalAuxiliaryOperator_ofFunction` | Inclusion gives the original function's L² class, and the operator gives the class of its actual differential expression. |
| Dense injective inclusion | `classicalAuxiliaryInclusion_injective`, `classicalAuxiliaryInclusion_denseRange` | Original physical spaces. |
| Differential expression and potential phase | `physicalOperator_auxiliaryPhase` | Pointwise conjugation changes the potential to (i φ₋,−i φ₊). |
| Operator phase identity | `classicalAuxiliaryOperator_phase`, `classicalAuxiliaryInclusion_phase` | Actual physical domain and base maps. |

These entries are in `ClassicalAuxiliaryPhase`, `ClassicalAuxiliarySpace`,
`AuxiliaryPhysicalL2`, and `ClassicalAuxiliaryOperator`. The physical H¹
norm and the weighted Fourier coefficient norm are related by the existing
continuous equivalence `classicalAuxiliaryIntervalEquiv`; equality of these
different norms is not asserted.

## Reflections and Lemma 5.1

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Actual interval extension | `auxiliaryIntervalExtension_left`, `auxiliaryIntervalExtension_right` | Retains f on [0,1]; on the second half uses ±(−i f₊(2−x),i f₋(2−x)), with + for D* and − for N*. |
| Correct potential extension | `intervalExtension_physicalAuxiliaryPotential` | Phase conversion of the Neumann-reflected potential equals the Dirichlet reflection of the converted potential. |
| Physical equation transfer | `physical_auxiliary_interval_equation_transfer` | Actual differential expression over [0,2], both signs; no extra L² assumption on the potential. |
| Original weighted extension | `sourceClassicalAuxiliaryExtension` | Actual weighted coefficient pair, in the original component-sum norm. |
| Actual periodic H¹ representatives | `sourceClassicalAuxiliaryCircleExtension`, `sourceClassicalAuxiliaryCircleExtension_regular` | Continuous circle representatives with physical H¹ regularity. |
| Entire-period reconstruction | `sourceClassicalAuxiliaryCircleExtension_reconstruct` | Equality with the printed reflection throughout [0,2]. |
| Endpoint-inclusive restriction | `sourceClassicalAuxiliaryCircleExtension_restrict` | Equality with the original function throughout [0,1]. |
| Lemma 5.1, both parts | `sourceLemma5_1` | Periodic H¹ extension satisfying L(φneu)F=λF almost everywhere on the full period. |
| Actual potential coefficients | `sourceNeumannPotentialCoefficients_coefficients`, `sourceNeumannPotentialCoefficients_reconstruct` | Normalized physical Fourier integrals of an L² Neumann-reflected potential and a.e. reconstruction. |
| Actual function coefficients | `sourceClassicalAuxiliaryExtension_coefficients` | Normalized physical Fourier integrals of the entire auxiliary reflection. |
| Original-norm source equation | `source_classical_auxiliary_equation_transfer` | The actual source operator on the original weighted domain, for L² potentials. |
| Nonzero eigenfunctions retained | `sourceClassicalAuxiliaryExtension_ne_zero`, `source_classical_auxiliary_eigenvector_transfer` | Nonzero physical functions yield nonzero original weighted eigenvectors. |
| Original periodic spectrum | `source_classical_auxiliary_eigenvalue_mem_spectrum` | Each physical auxiliary eigenvalue lies in the spectrum defined by actual original-pencil bijectivity. |

The new original-norm and physical transfer entries are in
`NLS.ZakharovShabat.SourceLemma5_1`. The physical statement is proved by
phase conjugation of the ordinary physical reflection theorem and by
reconstruction of the actual periodic Sobolev representative. The coefficient
statement is a separate realization for square-integrable potentials.

Public checks exercise both literal endpoint equations and both reflected
signs, the full physical theorem without a potential-integrability hypothesis,
endpoint restriction, negative-frequency physical coefficient identities,
potential reconstruction, nonzero source eigenvectors and spectral membership.
No correction is required for these source statements.

## Next source assertions

Audit the actual physical Fourier expansions (1.11)–(1.12), their mode labels,
phase factors and normalization. Then identify the auxiliary Fourier spaces
and their complementary decomposition in the original norms. Analyticity,
counting and later auxiliary results require their own source-space audits.
