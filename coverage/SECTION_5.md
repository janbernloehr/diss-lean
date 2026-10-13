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

## Completed auxiliary extensions, operators, and spectra, page 34

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Original input phase | `sourceAuxiliaryInputPhase` | Isometry for every finite Banach exponent. |
| Completed auxiliary extension | `sourceAuxiliaryExtensionToBoundary` | Actual original weighted zero-order target, 1 < p < ∞. |
| Sufficient original-norm bound | `norm_sourceAuxiliaryExtensionToBoundary_le`, `norm_auxiliarySourceExtension_improved_le` | Ordinary interval-extension constant; no optimality assertion. |
| Exact Hilbert norm | `norm_sourceAuxiliaryExtensionToBoundary_two` | Isometry at p=2. |
| Physical coefficients and unique completion | `sourceAuxiliaryExtensionToBoundary_finite_integrals`, `sourceAuxiliaryExtensionToBoundary_unique`, `tendsto_sourceAuxiliaryExtension_truncate` | Actual physical integrals on finite inputs, density and original-norm convergence. |
| Actual distributional reflection | `sourceAuxiliaryExtensionDistributionCLM`, `sourceAuxiliaryExtensionDistribution_coefficients`, `tendsto_sourceAuxiliaryExtensionDistribution_truncate` | Paired periodic distributions with exact signed coefficients and truncation limits. |
| Arbitrary physical L² input | `sourceAuxiliaryExtensionToBoundary_two_ofFunction`, `sourceAuxiliaryExtensionToBoundary_two_physical` | Actual reflection coefficients and a.e. synthesis on the doubled interval. |
| Sobolev compatibility | `auxiliarySourceExtension_two_classical` | Actual inclusion of the H¹ auxiliary extension. |
| Common reflected potential | `sourceAuxiliaryReflectedPotential`, `sourceAuxiliaryReflectedPotential_ofFunction` | Ordinary Neumann reflection for both auxiliary signs; physical identification at p=2. |
| Actual original-domain invariance | `sourceOperator_mem_auxiliarySourceSpace`, `sourceAuxiliaryReflectedPotential_invariant` | Finite p including 1 for already-reflected input; completed input requires p>1. |
| Restricted operator and inclusion | `sourceAuxiliaryOperator`, `sourceAuxiliaryInclusion`, `norm_sourceAuxiliaryOperator_le` | Actual restrictions in original norms, with a sufficient operator bound. |
| Actual restricted pencil | `sourceAuxiliaryPencil`, `sourceAuxiliaryPencil_eq_conj` | Defined as z·inclusion − operator, with exact continuous conjugacy. |
| Full resolvent and spectrum | `sourceAuxiliaryResolventSet_eq`, `sourceAuxiliarySpectrum_eq` | Resolvent defined by actual pencil bijectivity; spectrum by its complement. |
| Closed discrete spectrum | `isClosed_sourceAuxiliarySpectrum`, `discreteTopology_sourceAuxiliarySpectrum`, `finite_sourceAuxiliarySpectrum_inter` | Every finite Banach exponent; finite in arbitrary bounded regions. |
| Classical physical spectrum | `sourceAuxiliarySpectrum_eq_classical`, `sourceAuxiliarySpectrum_reflected_ofFunction` | Equality with actual physical auxiliary eigenvalues for every L² potential. |

These entries are in `SourceAuxiliaryExtension`,
`SourceAuxiliaryExtensionPhysical`, `SourceAuxiliaryOperators`, and
`SourceAuxiliarySpectra`. Public checks cover generic completion uniqueness,
p=2 physical reconstruction and Sobolev compatibility, p=1 invariance, p=3
bounds and analyticity, finite-input Fourier integrals at negative frequency,
distributional limits, literal pencil and resolvent definitions, discreteness,
bounded finiteness, and classical physical spectrum identification.

## Proposition 5.2: original Jordan multiplicities, counts, and reality

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Actual Jordan recursion | `mem_sourceAuxiliaryRootSpace_succ`, `sourceAuxiliaryRootSpace_succ` | Original auxiliary domain, pencil, and inclusion at every step; finite p including 1. |
| Full original root space | `mem_sourceAuxiliaryRootSpaceTop`, `sourceAuxiliaryRootSpaceTopEquiv` | All finite chains; continuous equivalence with the auxiliary coefficient root space. |
| Finite-dimensional stabilization | `finiteDimensional_sourceAuxiliaryRootSpaceTop`, `exists_sourceAuxiliaryRootSpace_eq_top` | Every spectral parameter, including outside the spectrum. |
| Original algebraic multiplicity | `sourceAuxiliaryAlgebraicMultiplicity`, `sourceAuxiliaryAlgebraicMultiplicity_eq`, `sourceAuxiliaryAlgebraicMultiplicity_pos_iff` | Defined as the dimension of the actual full original root space, positive precisely on the restricted spectrum. |
| Actual finite spectral clusters | `sourceAuxiliaryCentralSpectrum`, `sourceAuxiliaryEnclosedSpectrum`, membership theorems | Finite sets from the actual restricted spectrum intersected with the geometric regions. |
| Uniform original counts | `exists_uniform_sourceAuxiliaryCountingData` | One open convex connected original-input neighborhood containing the input and zero; both signs, all larger cutoffs, 1 < p < ∞. |
| Central algebraic count | `SourceAuxiliaryCountingData.central_multiplicity` | 2N+1 for each auxiliary condition, in the height-N central box. |
| High-disk simplicity | `SourceAuxiliaryCountingData.disk_multiplicity`, `SourceAuxiliaryCountingData.disk_unique_simple` | Exactly one spectral point in each high quarter-pi disk, full original algebraic multiplicity one. |
| Exhaustive localization | `SourceAuxiliaryCountingData.spectrum_subset` | No further spectral values outside the height-N box and high disks. |
| Original reflected real type | `isRealType_sourceAuxiliaryReflectedPotential` | Common completed Neumann reflection preserves real type. |
| Proposition 5.2(iv) | `sourceAuxiliarySpectrum_im_eq_zero_of_realType`, `sourceAuxiliaryReflectedSpectrum_im_eq_zero_of_realType` | Both actual original auxiliary spectra are real for real-type input. |
| Physical Jordan multiplicity | `sourceAuxiliaryAlgebraicMultiplicity_eq_classical`, `sourceAuxiliaryAlgebraicMultiplicity_reflected_ofFunction` | Equality with the independently defined full physical auxiliary root-space dimensions, for every interval L² potential. |
| Prescribed heights for real spectra | `sourceAuxiliaryHeightSpectrum_eq_central_of_realType` | Every nonnegative height gives the same central cluster. |
| Real-type counts and localization at prescribed height | `SourceAuxiliaryCountingData.central_height_multiplicity_of_realType`, `SourceAuxiliaryCountingData.spectrum_subset_height_of_realType` | Includes the positive printed height; no analogous claim for arbitrary complex potentials. |
| Final proof count discrepancy | `exists_sourceAuxiliaryZero_printedBox_count` | The literal printed zero-input box has count 2N+1, not 2N−1, for every sufficiently large cutoff. |

These entries are in `SourceAuxiliaryRootSpaces`, `SourceAuxiliaryReality`,
`SourceAuxiliaryCounting`, `SourceAuxiliaryPhysicalMultiplicity`, and
`SourceAuxiliaryHeightClusters`. Counts measure full Jordan multiplicities,
not just eigenspace dimensions or distinct spectral values. Public checks
exercise p=1 chain recursion and stabilization, p=3 uniform neighborhoods,
high-disk uniqueness and full multiplicity, central sums, reality, even
height-zero real clusters, physical multiplicity equality, and the literal
printed-box counterexample.

## Proposition 5.2 proof: actual original contour ranks and domain lifts

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Full ambient phase conjugation | `mem_resolventSet_auxiliaryPotential_iff`, `resolventToDomain_auxiliaryPhase`, `resolvent_auxiliaryPhase_conj` | Actual resolvent and domain-valued inverse; zero extensions off the resolvent set included. |
| Actual contour conjugation | `resolventCircleIntegral_auxiliaryPhase_conj`, `resolventRectangleIntegral_auxiliaryPhase_conj` | Normalized operator-valued integrals on admissible circle and four-edge rectangle contours. |
| Auxiliary complementary projection | `BoundaryCondition.auxiliaryProjection`, `sourceAuxiliaryProjection` | Coefficient phase projection and its original-norm realization, with membership and identity on the selected auxiliary subspace. |
| Preservation by contour integrals | `sourceAuxiliaryProjection_commute_circleIntegral`, `sourceAuxiliaryProjection_commute_centralIntegral` | Both signs, the same already Neumann-reflected potential. |
| Actual original restrictions | `sourceAuxiliaryCircleProjection_apply`, `sourceAuxiliaryCentralProjection_apply` | The typed restrictions act exactly as the original ambient integrals on auxiliary vectors. |
| Actual restricted ranges | `sourceAuxiliaryCompressionRangeEquiv` | Isometry to the intersection of the ambient original range with the auxiliary subspace. |
| Finite-rank idempotence | `sourceAuxiliaryCircleProjection_properties`, `sourceAuxiliaryCentralProjection_properties` | Actual circle and rectangle restrictions, not merely abstract rank assignments. |
| One-derivative lifts | `sourceAuxiliaryCircleProjection_exists_domain`, `sourceAuxiliaryCentralProjection_exists_domain` | Every projected vector comes from the original weighted auxiliary domain. |
| Unchanged range on domain input | `range_sourceAuxiliaryCircleProjection_comp_inclusion`, `range_sourceAuxiliaryCentralProjection_comp_inclusion` | Exact range equality for the restrictions displayed in the proof. |
| Full original Jordan rank formulas | `sourceAuxiliaryCircleProjection_rank_eq_sum`, `sourceAuxiliaryCentralProjection_rank_eq_sum` | Sums over actual original auxiliary spectral clusters of full-chain algebraic multiplicities. |
| Completed original potential map | `sourceAuxiliaryReflectedPotentialCLM`, `sourceAuxiliaryReflectedPotentialCLM_apply` | Actual common Neumann reflection as a bounded linear map in the original norms. |
| Uniform analytic families | `exists_uniform_sourceAuxiliaryContourData` | One open convex connected neighborhood containing the input and zero, both signs, all larger cutoffs. |
| Counted ranks | `SourceAuxiliaryContourData.central_rank`, `SourceAuxiliaryContourData.disk_rank` | 2N+1 centrally and one in every high quarter-pi disk. |
| Counted domain ranks | `SourceAuxiliaryContourData.central_domain_rank`, `SourceAuxiliaryContourData.disk_domain_rank` | The same ranks after restricting input to the original one-derivative domain. |

These entries are in `AuxiliaryContourPhase`, `SourceAuxiliaryContours`,
`SourceAuxiliaryContourDomains`, `SourceAuxiliaryContourRanks`, and
`SourceAuxiliaryContourCounting`. The range comparison uses continuous
norm changes and the exact phase conjugation; it does not assume that the
original norm equals the auxiliary maximum norm. Public checks include the
p=1 ambient resolvent identity, actual original integral action, domain lifts,
unchanged ranges, full Jordan rank sums, p=3 counted domain ranks,
finite-rank idempotence, and the uniform original-input analytic family.

## Proposition 5.2: literal printed-height audit

| Source assertion | Entry point | Scope |
| --- | --- | --- |
| Exact original potential phase norm | `sourceAuxiliaryPotentialPhase`, `sourceAuxiliaryPotentialPhase_eq_sourcePhase` | Linear isometry at every finite Banach exponent; agrees with the existing source phase. |
| Finite Fourier input under inverse phase | `sourceAuxiliaryPotentialPhase_symm_ofFinsupp` | Explicit coefficients (−i a, i b); support remains finite. |
| Actual completed spectral transport | `sourceAuxiliarySpectrum_eq_sourcePhaseBoundary` | Auxiliary restrictions at the original input equal ordinary restrictions at its phase rotation. |
| Printed Hilbert height | `sourceAuxiliarySpectrum_abs_im_lt_printed_height_two` | Strict bound abs(Im z) < (1+8‖φ‖)² for both auxiliary spectra in the original input norm. |
| Specified-height cluster identification | `sourceAuxiliaryHeightSpectrum_eq_central_of_bound` | Uses an actual spectral height bound and H≤N, rather than silently replacing the box. |
| Literal p=2 counts and exhaustion | `sourceProposition5_2_two` | Both signs, one open convex connected neighborhood containing the input and zero, all larger cutoffs; original full Jordan multiplicities. |
| Small original counterexample norm | `norm_sourceAuxiliaryHeightCounterexample_le` | At most 3/32 for every natural exponent P≥1024. |
| Explicit all-cutoff height failure | `sourceAuxiliaryPrintedHeight_counterexample` | Actual auxiliary D* eigenvalue i·2^P outside both the printed box and all high quarter-pi disks, for every cutoff. |
| Refuted unrestricted exhaustion | `not_sourceProposition5_2_printed_exhaustion` | The literal universal assertion fails already at p=1024. |

These entries are in `SourceAuxiliaryPotentialPhase`,
`SourceAuxiliaryPrintedHeight`, and `SourceAuxiliaryHeightCounterexample`.
The counterexample concerns the actual original spectrum and norm and is a
finite Fourier input. It does not refute high-disk simplicity or central
counts in the proved height-N boxes, or the earlier real-type results.
It is separate from the final 2N−1 count typo in the proof.

Public checks include finite-input phase transport at p=1, the exact phase
norm, strict p=2 height, the complete uniform literal-height counting theorem,
the counterexample's original norm bound, its explicit spectral membership
and escape for every large natural exponent and every cutoff, and the
negation of universal printed exhaustion at p=1024.

## Section 5 outcome and next source assertions

The auxiliary extensions, spaces, physical correspondence, actual operators,
Jordan counts, reality, and actual contour-rank proof have been audited in
the original norms. The ordinary-mode typo in (1.11), repeated D* summand,
and final 2N−1 count are formally corrected. The printed numerical height
is proved at p=2 and refuted as an assertion for every 1<p<∞. Its optimal
validity range is not claimed, and no replacement bound is adopted.

Continue with Section 6, beginning with Proposition 6.1's original-norm
quantitative eigenvalue-displacement estimate and its locally uniform cutoff.
Keep the subsequent weighted-gap assertions, four boundary asymptotics,
and midpoint/gap corollaries separate until their exact formulations are
matched to the existing coefficient and physical constructions.
