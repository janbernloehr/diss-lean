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

## Physical Fourier expansions (1.11)–(1.12), pages 33–34

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original coefficient phase isometry | `sourceAuxiliaryPhaseTwo` | Exact component-sum norm at p=2. |
| Literal auxiliary modes | `physicalAuxiliaryBoundaryMode`, `sourceAuxiliaryBoundaryMode_physical` | (ε exp(−iπnx), i exp(iπnx)), unnormalized, both boundary signs. |
| Actual sesquilinear pairing | `intervalAuxiliaryBoundaryPairing`, `intervalAuxiliaryBoundaryPairing_eq_phase` | Physical integral, conjugate in the auxiliary mode; exact inverse-phase comparison. |
| Actual reflection coefficients | `sourceAuxiliaryIntervalExtensionCoefficients_integrals` | Both components are normalized physical Fourier integrals. |
| Printed component formula | `sourceAuxiliaryIntervalExtensionCoefficients_raw` | Both signs, arbitrary signed frequencies; the first line of (1.11) is unchanged. |
| Half-pairing series | `sourceEquation1_11_1_12_coefficients` | Convergence in the original component-sum coefficient norm, using the auxiliary mode. |
| Actual reflected physical sum | `sourceCircleSynthesis_auxiliaryIntervalExtension` | Reconstructs the printed phase-twisted extension a.e. on [0,2]. |
| Physical L² series | `sourceEquation1_11_1_12_L2` | Convergence in normalized component-sum period-two L². |
| Exact original energy | `norm_sourceAuxiliaryIntervalExtensionCoefficients`, `sourceEquation1_11_1_12` | Preserves the original interval L² energy. |
| Compatibility with Lemma 5.1 | `sourceAuxiliaryIntervalExtensionCoefficients_eq_classical` | On the auxiliary physical H¹ domain, equals the actual source-domain inclusion of the Sobolev extension. |
| Printed mode mismatch | `physicalAuxiliaryBoundaryMode_ne_ordinary_zero` | Ordinary and auxiliary D* modes differ already at zero frequency. |
| Printed series counterexample | `sourceEquation1_11_printed_ordinary_mode_false` | For constant data (1,i), the ordinary-mode series in the second line of (1.11) cannot sum to the auxiliary reflected coefficients. |

These entries are in `NLS.ZakharovShabat.SourceAuxiliaryBoundaryFourier`.
The complete series theorem covers arbitrary L² interval input, hence also
H¹ input, without imposing endpoint equations for L² convergence. It does
not assert uniform or H¹ convergence for arbitrary L² data. The coefficient
phase is an isometry in the original norm, and physical realization is proved
through the actual Fourier integrals and a.e. reconstruction.

The second line of (1.11) needs E_m^d* in place of E_m^dir. The first line
and the factor 1/2 need no change. Equation (1.12) already uses the correct
N* mode. This correction is explicitly tracked in `SOURCE_ERRATA.md`.
The public checks cover both literal physical modes, a negative frequency,
the full L² sum and energy, the original norm, the component coefficients,
Sobolev compatibility, and the formal printed-series counterexample.

## Original weighted auxiliary spaces and decomposition, page 34

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original weighted auxiliary spaces | `sourceWeightedAuxiliarySubspace`, `sourceWeightedAuxiliarySubspaceInfty` | All real Sobolev orders; finite component-sum norm and separate signed coupled-supremum norm. |
| Actual phase conditions | `mem_sourceWeightedAuxiliarySubspace`, `mem_sourceWeightedAuxiliarySubspaceInfty` | Raw first-component frequency reversal versus matching signed indices; both auxiliary signs. |
| Closedness | `isClosed_sourceWeightedAuxiliarySubspace`, `isClosed_sourceWeightedAuxiliarySubspaceInfty` | The actual original ambient topologies. |
| Corrected topological decomposition | `isCompl_sourceWeightedAuxiliarySubspaces`, `isTopCompl_sourceWeightedAuxiliarySubspaces`, and `Infty` counterparts | D* and N* have zero intersection and span the entire original space. |
| Complete scalar amplitude parametrization | `sourceWeightedAuxiliaryAmplitudeEquiv`, `sourceWeightedAuxiliaryAmplitudeEquivInfty` | Continuous linear equivalences onto the actual subspaces. |
| Explicit amplitude assemblies | `sourceWeightedAuxiliaryAmplitudeEquiv_apply`, `sourceWeightedAuxiliaryAmplitudeEquivInfty_apply` | (ε reflection(a),i a) in raw coordinates; (ε a,i a) in signed infinity coordinates. |
| Exact original amplitude norms | `norm_sourceWeightedAuxiliaryAmplitudeEquiv`, `norm_sourceWeightedAuxiliaryAmplitudeEquivInfty` | Factors 2^(1/p) for finite p and 2 for the source infinity norm. |
| Physical H¹ isomorphism | `sourceClassicalAuxiliaryBoundaryEquiv` | Original physical interval H¹ domain to original one-derivative auxiliary coefficient space, as a continuous linear equivalence. |
| Actual forward and inverse maps | `sourceClassicalAuxiliaryBoundaryEquiv_ofFunction`, `sourceClassicalAuxiliaryBoundaryEquiv_symm_apply` | Reflected Fourier coefficients and endpoint-inclusive physical restriction. |
| Finite-exponent mode series | `hasSum_sourceWeightedAuxiliaryModes`, `existsUnique_sourceWeightedAuxiliaryExpansion` | Norm convergence and exactly one weighted scalar amplitude sequence for every auxiliary vector. |
| Actual distributional sum | `hasSum_sourceAuxiliaryDistribution` | Every Banach exponent, including infinity, and every real Sobolev order. |
| Original synthesis identification | `sourceAuxiliaryDistribution_eq_sourcePair`, `sourceAuxiliaryDistribution_eq_sourcePairInfty` | The sums are the actual original raw or signed pair distributions. |
| Infinity amplitude representation | `existsUnique_sourceWeightedAuxiliaryInftyExpansion` | Unique amplitude assembly together with its actual distributional sum; no infinity-norm convergence assertion. |
| Literal physical modes | `sourceAuxiliaryDistribution_single`, `sourceAuxiliaryDistributionMode_physical` | The same weighted single modes act by integrals of (ε exp(−iπnx), i exp(iπnx)) against Schwartz tests. |
| Printed repeated-summand failure | `not_isCompl_sourceWeightedAuxiliaryDirichlet_self`, `not_isCompl_sourceWeightedAuxiliaryDirichletInfty_self` | A nonzero weighted zero mode refutes the repeated D* summand in both original norm conventions. |

These entries are in `SourceAuxiliarySpaces` and `SourceAuxiliarySeries`.
The physical H¹ norm is not identified isometrically with the weighted
coefficient norm. The finite and infinity amplitude factors explicitly
record the original norm difference from the auxiliary maximum norm.

Public checks include both complementary decompositions, the exact signed
infinity membership condition and factor, a p=1 norm expansion, p=3 with
negative Sobolev order and negative frequency, actual Schwartz-wave
integrals, unique infinity representation, both physical H¹ maps, and
both forms of the printed repeated-summand counterexample.

## Next source assertions

Audit the completed bounded auxiliary extension maps on page 34, including
the original input and target norms and arbitrary physical L² identification.
Then prove original-domain operator invariance and identify the actual
restricted source pencils. Proposition 5.2's spectrum, counting, reality
and numerical-height assertions retain separate audits.
