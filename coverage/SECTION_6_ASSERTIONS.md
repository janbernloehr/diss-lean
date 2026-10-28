# Section 6: ordered assertion ledger

This ledger follows the 47 passage groups located in the cached extraction of
[the dissertation](https://janbernloehr.de/Download/fs16/diss.pdf). It is a
navigation inventory with an assertion-level review of the listed passages.
Each classification retains its proof references and scope qualifications;
the count is not a dissertation completion percentage.

All 47 groups, S6-001 through S6-047 (printed pp.35–44), are reconciled:
37 matched, nine corrected and one interpreted. Their scope qualifications
remain part of the comparison; the broader dissertation audit is unfinished.
**Matched** records the mathematical assertions and their exact scope.
**Corrected** records a formula or constant adjustment with a proved valid replacement.
Existing refutations are retained; additional refutations are not required.
**Interpreted** makes an operator-domain interpretation explicit rather than
claiming a literal formalization of the source's adjoint notation.

The extraction positions are newline-based and tied to SHA-256
`64640083a811e0e05710297d056d23d7e1f2aadad7fb1f1a1271819b90978619`.
The source PDF and inspected page hashes, module snapshots and declaration
references are recorded in Section6TransposeSourceComparison-2026-10-28,
Section6UniformSeriesSourceComparison-2026-10-28,
Section6DiagonalSourceComparison-2026-10-28,
Section6OffDiagonalSourceComparison-2026-10-28 and
Section6RootSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json). The
[completion qualifications](COMPLETENESS.md) remain in force.

| ID | Extraction lines | Passage | Status |
| --- | --- | --- | --- |
| S6-001 | 2280–2285 | Initial spectral sequence and O(1) statement | matched |
| S6-002 | 2287–2292 | Proposition 6.1 qualitative local asymptotics | matched |
| S6-003 | 2294–2309 | Proposition 6.1 literal positive-index quantitative budget | corrected |
| S6-004 | 2312–2316 | Reflection argument for interval eigenvalues | matched |
| S6-005 | 2318–2328 | Corollary 6.2 on arbitrary period-two input | matched |
| S6-006 | 2331–2336 | Canonical midpoint and gap asymptotics | matched |
| S6-007 | 2339–2368 | Source weights, original weighted norm and Sobolev examples | matched |
| S6-008 | 2370–2384 | Proposition 6.3 literal positive-index gap budget | corrected |
| S6-009 | 2387–2398 | Lyapunov-Schmidt attribution and free modes | matched |
| S6-010 | 2399–2409 | Closed strips and P/Q topological decomposition | matched |
| S6-011 | 2410–2421 | Free multiplier, actual potential and projected equations | matched |
| S6-012 | 2422–2432 | Complementary inverse geometry and transformed Q equation | matched |
| S6-013 | 2442–2448 | Id-T formulation | matched |
| S6-014 | 2449–2474 | Exact opposite component shifts | matched |
| S6-015 | 2476–2486 | Lemma 6.4 all finite Banach exponents | matched |
| S6-016 | 2488–2525 | Full reciprocal series, shifted Holder and Young proof | matched |
| S6-017 | 2528–2534 | Square decay and Neumann inversion | matched |
| S6-018 | 2544–2555 | Lemma 6.5 and exact retained-boundary tail | matched |
| S6-019 | 2558–2578 | Actual double inverse and full double coefficients | matched |
| S6-020 | 2580–2584 | Near/far partition | matched |
| S6-021 | 2586–2605 | Far weighted Holder estimate | matched |
| S6-022 | 2606–2629 | Near geometry, weight gain and tail estimate | matched |
| S6-023 | 2631–2661 | Component recombination and printed final equality | corrected |
| S6-024 | 2663–2684 | Common half-contraction and compatible Neumann inverses | matched |
| S6-025 | 2686–2694 | Reduced map and Lemma 6.6 | matched |
| S6-026 | 2696–2715 | Full original-domain reconstruction and converse | matched |
| S6-027 | 2725–2754 | Actual matrix entries and printed basis order | matched |
| S6-028 | 2755–2764 | Lemma 6.7 and required reality hypothesis | corrected |
| S6-029 | 2766–2796 | Equal diagonals via transposition/conjugation | interpreted |
| S6-030 | 2799–2853 | Reality identities using the stated type assumption | matched |
| S6-031 | 2856–2880 | Matrix form and full parity series (1.14)-(1.15) | matched |
| S6-032 | 2883–2888 | Actual suprema on closed unbounded strips | matched |
| S6-033 | 2891–2915 | Lemma 6.8 analytic scope and printed bounds | corrected |
| S6-034 | 2917–2933 | Uniform series and corrected potential vector | matched |
| S6-035 | 2935–2941 | Actual diagonal coefficient sum | matched |
| S6-036 | 2952–2970 | Diagonal Holder estimate | matched |
| S6-037 | 2972–3036 | Diagonal near/far power sums in both exponent ranges | matched |
| S6-038 | 3037–3058 | Off-diagonal double sum and inserted weight factor | corrected |
| S6-039 | 3060–3096 | Three index regions and (1.16) | matched |
| S6-040 | 3097–3147 | High-exponent off-diagonal sum estimates | matched |
| S6-041 | 3149–3174 | Low-exponent off-diagonal sum estimates | matched |
| S6-042 | 3176–3183 | Actual determinant and Rouche preparation | matched |
| S6-043 | 3185–3207 | Lemma 6.9 roots, gap and literal duplicated positive sum | corrected |
| S6-044 | 3217–3232 | Uniform strip bounds, Rouche counts and no exterior roots | matched |
| S6-045 | 3233–3259 | Branch-free root estimate, Cauchy derivative and gap | corrected |
| S6-046 | 3261–3270 | Identification with actual periodic pairs | matched |
| S6-047 | 3272–3293 | Final weighted gap estimate and source constants | corrected |

## Reviewed assertions

### S6-001: Initial spectral sequence and O(1) statement

- For every finite Banach exponent p>=1, the complement of the original source-pencil resolvent set is closed and discrete.
- SourcePeriodicBoundedLabeling splices the complete central root multiset with the actual two eigenvalues in every distant radius-pi/4 disk. Its central and distant data retain algebraic multiplicities, including a repeated root of multiplicity two.
- The two sequences exhaust exactly the original period-two spectrum, and both displacements from n*pi have norm less than pi/4 for abs(n)>N. This gives the stated O(1) asymptotics, including p=1.
- One open convex original-input neighborhood containing the potential and zero admits such labels at every larger cutoff.

Public evidence: `NLS.ZakharovShabat.isOpen_sourceResolventSet`, `NLS.ZakharovShabat.discreteTopology_sourceResolventSet_compl`, `NLS.ZakharovShabat.SourcePeriodicBoundedLabeling`, `NLS.ZakharovShabat.SourcePeriodicBoundedLabeling.exhaustive`, `NLS.ZakharovShabat.SourcePeriodicBoundedLabeling.displacement_lt`, `NLS.ZakharovShabat.exists_sourcePeriodicBoundedLabeling`, `NLS.ZakharovShabat.exists_uniform_sourcePeriodicBoundedLabeling`.

The p=1 assertion is bounded displacement and exact spectral enumeration. No p=1 summable displacement, unique ordered labeling, or individual-label continuity is asserted.

### S6-002: Proposition 6.1 qualitative local asymptotics

- For 1<p<infinity, fixed globally ordered complete canonical endpoints enumerate the actual raw period-two spectrum with full algebraic multiplicities.
- Both complete displacement sequences belong to ell-p. Given epsilon>0, one original open convex neighborhood containing the input and zero and one cutoff make the full signed joint power tail less than epsilon for every larger cutoff.
- The canonical sequences are independent of the chosen admissible central cutoff; no even-support or frequency-doubling assumption is introduced.

Public evidence: `NLS.ZakharovShabat.sourcePeriodTwoCanonicalEndpoints_spec`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalEndpoints_exhaustive`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalEndpoints_global_multiplicity`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalEndpoints_memℓp`, `NLS.ZakharovShabat.sourceProposition6_1_canonical_asymptotics`.

Local asymptotics concern the fixed canonical sequences and their tails. Individual complex labels are not asserted to be continuous.

### S6-003: Proposition 6.1 literal positive-index quantitative budget

- The actual complete canonical labels satisfy summable positive-index power tails on the literal n>=K range, including its boundary.
- One original neighborhood and cutoff give both the full-Fourier-cutoff and ceiling-half corrected budgets for every K>N0. Increasing the threshold by one gives the source convention K>=N0.
- The valid budgets retain the additive leading Fourier tail and the original component-sum norm. The multiplicative printed budget is not asserted.

Public evidence: `NLS.ZakharovShabat.sourceProposition6_1_canonical_fullCutoff`, `NLS.ZakharovShabat.sourceProposition6_1_canonical_positive_cutoffs`, `NLS.ZakharovShabat.sourcePeriodTwoDisplacementBudget_fullCutoff`, `NLS.ZakharovShabat.sourcePeriodTwoDisplacementBudget_ceilingHalf`.

This reconciles the already proved replacement and preserves the earlier source review. No additional refutation is required.

### S6-004: Reflection argument for interval eigenvalues

- The original completed interval extension is bounded and complex linear for 1<p<infinity. Its finite-input coefficients are the actual normalized Fourier integrals of signed reflection, and finite truncations converge in the original norm.
- The periodic spectrum of a reflected potential is exactly the union of the two actual original boundary spectra. Complete boundary labels exhaust those spectra and preserve their full Jordan multiplicities.
- For arbitrary period-two inputs, bounded restriction to the unit interval precedes reflection. Restriction is physically identified on finite Fourier inputs for all 1<p<infinity and on arbitrary L2 inputs; its completed maps apply to general Fourier-Lebesgue inputs.

Public evidence: `NLS.ZakharovShabat.sourceLemma4_3`, `NLS.ZakharovShabat.sourceIntervalExtensionToBoundary_finite_integrals`, `NLS.ZakharovShabat.tendsto_sourceIntervalExtension_truncate`, `NLS.ZakharovShabat.sourcePeriodicSpectrum_eq_sourceBoundary_union`, `NLS.ZakharovShabat.mem_sourceBoundarySpectrum_reflected_iff`, `NLS.ZakharovShabat.sourceBoundaryAlgebraicMultiplicity_eq`, `NLS.ZakharovShabat.sourcePeriodTwoRestriction_ofFunction`, `NLS.ZakharovShabat.sourcePeriodTwoRestriction_reflection`, `NLS.Fourier.periodTwoToUnit_finite_integral`.

The bounded completion carries rough inputs. This passage reuses the corrected Section 4 normalization and does not assert pointwise reflection for arbitrary distributions.

### S6-005: Corollary 6.2 on arbitrary period-two input

- All four ordinary and auxiliary boundary sequences are defined on arbitrary original period-two inputs by restriction followed by the corresponding reflection and phase maps.
- They exhaust the actual original restricted spectra and their repetitions equal the full Jordan algebraic multiplicities.
- For 1<p<infinity, one open convex original-input neighborhood containing the potential and zero and one positive constant bound all four complete displacement power sums, including central indices. All four displacement sequences belong to ell-p.

Public evidence: `NLS.ZakharovShabat.sourcePeriodTwoBoundaryRoots`, `NLS.ZakharovShabat.sourcePeriodTwoAuxiliaryRoots`, `NLS.ZakharovShabat.sourcePeriodTwoBoundaryRoots_exhaustive`, `NLS.ZakharovShabat.sourcePeriodTwoAuxiliaryRoots_exhaustive`, `NLS.ZakharovShabat.sourcePeriodTwoBoundaryRoots_multiplicity`, `NLS.ZakharovShabat.sourcePeriodTwoAuxiliaryRoots_multiplicity`, `NLS.ZakharovShabat.sourceCorollary6_2`, `NLS.ZakharovShabat.sourceCorollary6_2_mem`.

The physical finite-input/L2 and rough-input completion qualifications from S6-004 remain in force. No even-support assumption is made.

### S6-006: Canonical midpoint and gap asymptotics

- The midpoint is the average of the actual complete canonical endpoints, and the gap is right endpoint minus left endpoint, at every integer index.
- The complete midpoint displacement and gap both belong to ell-p for 1<p<infinity. Their joint power tails are locally uniformly small on one original neighborhood for all sufficiently large cutoffs.
- At distant indices their midpoint and squared gap agree with the intrinsic contour invariants. No such contour identity is asserted for the arbitrary central cluster.

Public evidence: `NLS.ZakharovShabat.sourcePeriodTwoCanonicalMidpoint`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalGap`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalMidpointGap_memℓp`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalMidpointGap_asymptotics`, `NLS.ZakharovShabat.sourcePeriodTwoCanonicalMidpointGap_eq_contours`.

The statement applies to the complete canonical sequences; the contour comparison retains its distant-index restriction.

### S6-007: Source weights, original weighted norm and Sobolev examples

- SpectralWeight imposes the literal lower bound one, symmetry, submultiplicativity and monotonicity in the nonnegative integer index. Normalized does not add w(0)=1; constant weights above one remain allowed.
- The original weighted pair norm has exactly the combined full signed coefficient p-power sum, not a maximum of the two component norms.
- The source bracket is 1+|n*pi|. For every s>=0 its s-th power is a source weight. The coefficient-preserving Sobolev equivalence has norm factors 1 and pi^s, and its inverse preserves every coefficient too.
- The pi-scaled pair norm to power p is exactly the sum of (1+|n*pi|)^(s*p) times the two raw coefficient p-powers. Generic comparable weights also give coefficient-preserving scalar and pair continuous linear equivalences.

Public evidence: `NLS.SpectralWeight`, `NLS.SpectralWeight.constant`, `NLS.SpectralWeight.piSobolev`, `NLS.WeightedCoeffPair.norm_rpow_eq_tsum`, `NLS.WeightComparison.equiv`, `NLS.WeightComparison.pairEquiv`, `NLS.WeightComparison.norm_pairEquiv_le`, `NLS.WeightComparison.norm_pairEquiv_symm_le`, `NLS.SpectralWeight.piSobolevPairEquiv`, `NLS.SpectralWeight.piSobolevPairEquiv_fst`, `NLS.SpectralWeight.piSobolevPairEquiv_snd`, `NLS.SpectralWeight.piSobolevPairEquiv_symm_fst`, `NLS.SpectralWeight.piSobolevPairEquiv_symm_snd`, `NLS.SpectralWeight.piSobolevPairEquiv_norm_bounds`, `NLS.SpectralWeight.piSobolevPairEquiv_norm_rpow_eq_tsum`.

The finite-p norm and power-sum formulas include p=1; the generic continuous equivalences also allow the infinity exponent. The references to introductions [28,29] are contextual attributions.

### S6-008: Proposition 6.3 literal positive-index gap budget

- For every source weight and 1<p<infinity, the actual canonical gaps retain the weight w(2*n) and literal positive-index range n>=K.
- One open convex weighted neighborhood containing the potential and zero supports summability, full-cutoff and ceiling-half corrected budgets, and locally small tails for every K>N0. Increasing the threshold by one gives the source K>=N0 convention.
- The complete canonical gap has weighted ell-p membership, including the finite central contribution. The corrected budgets retain the additive leading Fourier tail and original weighted pair norm.

Public evidence: `NLS.ZakharovShabat.sourceCanonicalWeightedGapTails_eq`, `NLS.ZakharovShabat.sourceProposition6_3_canonical_signed`, `NLS.ZakharovShabat.sourceProposition6_3_canonical_positive`, `NLS.ZakharovShabat.sourceProposition6_3_canonical_gap_mem`, `NLS.ZakharovShabat.rootGapBudget_fullCutoff`, `NLS.ZakharovShabat.rootGapBudget_ceilingHalf`.

The printed multiplicative budget is replaced by its established valid correction. Existing refutations remain historical evidence; this step adds none.

Section6InitialAssertionsSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records these eight passages.

### S6-009: Lyapunov-Schmidt attribution and free modes

- Each free periodic eigenvalue n*pi has algebraic multiplicity two. Its generalized root space equals the ordinary two-mode space.
- The signed modes have first physical frequency -n and second physical frequency n. Weighted resonant synthesis retains their raw amplitudes and the free-pencil multiplier z-n*pi.

Public evidence: `NLS.ZakharovShabat.periodicAlgebraicMultiplicity_zero`, `NLS.ZakharovShabat.periodicRootSpaceTop_zero_eq_range`, `NLS.ZakharovShabat.sourceSignedFourierMode`, `NLS.ZakharovShabat.resonantSynthesis_fst`, `NLS.ZakharovShabat.resonantSynthesis_snd`, `NLS.ZakharovShabat.pencil_resonantSynthesis`.

The historical attribution is contextual. Expected closeness of perturbed eigenfunctions motivates the splitting; it is not treated as a quantified eigenfunction theorem.

### S6-010: Closed strips and P/Q topological decomposition

- The strip is the full closed set |Re(z)-n*pi|<=pi/2, including its center and boundary.
- The resonant space is the literal span of two individual signed modes, has complex dimension two and equals the P projection range.
- For every finite Banach exponent and every positive weight, the closure of the span of the nonresonant individual modes equals the coordinate kernel and Q projection range.
- These literal spaces are topological complements in the original weighted pair norm. The full signed Fourier series converges in that norm.

Public evidence: `NLS.ZakharovShabat.resonantStrip`, `NLS.ZakharovShabat.sourceResonantModeSpan`, `NLS.ZakharovShabat.sourceNonresonantModeSpan`, `NLS.ZakharovShabat.sourceResonantModeSpan_finrank`, `NLS.ZakharovShabat.resonantProjection_range_eq_sourceSpan`, `NLS.ZakharovShabat.sourceNonresonantModeSpan_closure_eq_ker`, `NLS.ZakharovShabat.complementaryProjection_range_eq_sourceClosedSpan`, `NLS.ZakharovShabat.sourcePQ_isTopCompl`, `NLS.ZakharovShabat.sourceSignedFourierModes_hasSum`.

The closure in the printed Q definition is retained. The density and topological decomposition statements require finite p; no density claim is made at p=infinity.

### S6-011: Free multiplier, actual potential and projected equations

- The weighted free pencil is the original pencil at zero potential. The off-diagonal convolution map is the potential part of the original source operator.
- The free multiplier preserves the resonant and complementary spaces on the actual weighted derivative domain.
- The original eigenvalue equation is equivalent to its P and Q equations on that domain. The split formulation uses resonant u, complementary v and f=u+v.

Public evidence: `NLS.ZakharovShabat.sourceWeightedPencil_eq`, `NLS.ZakharovShabat.sourceWeightedDomainPotential_eq`, `NLS.ZakharovShabat.pencil_resonantSynthesis`, `NLS.ZakharovShabat.weightedFreePencil_resonantProjection`, `NLS.ZakharovShabat.pencil_complementaryProjection`, `NLS.ZakharovShabat.sourceWeightedPencil_zero_iff_PQ`, `NLS.ZakharovShabat.sourceWeightedPencil_add_zero_iff_PQ`.

The differential equations retain their actual derivative-domain hypotheses; the potential is not asserted to act boundedly on the base space alone.

### S6-012: Complementary inverse geometry and transformed Q equation

- On the full closed strip, m!=n implies |z-m*pi|>=|n-m|>=1. The complementary inverse has base-space norm at most one uniformly over the strip.
- The inverse takes values in the actual weighted derivative domain, has complementary range, satisfies both inverse identities there and is unique.
- Away from the free lattice, the original free resolvent applied to Qf equals the coefficient-preserving inclusion of the weighted complementary inverse.
- The actual Q equation implies Phi(v)=T(Phi(u+v)), and hence its Id-T rearrangement.

Public evidence: `NLS.ZakharovShabat.resonantStrip_denominator_lower`, `NLS.ZakharovShabat.resonantStrip_denominator_one_le`, `NLS.ZakharovShabat.norm_complementaryFreeInverse_le`, `NLS.ZakharovShabat.pencil_complementaryFreeDomainInverse`, `NLS.ZakharovShabat.complementaryFreeDomainInverse_pencil`, `NLS.ZakharovShabat.complementaryFreeDomainInverse_unique`, `NLS.ZakharovShabat.sourceFreeResolvent_complementary`, `NLS.ZakharovShabat.sourceQEquation_transformed`.

The uniform bound is in the base-space norm. The derivative-domain bound depends on z. The original free-resolvent comparison excludes the free lattice; the complementary inverse itself includes the strip center.

### S6-013: Id-T formulation

- The actual T=Phi*A_inverse*Q is identified with the original source operator.
- The complementary-domain Q equation gives (Id-T)Phi(v)=T*Phi(u) without smallness, high-frequency or reality assumptions.
- Under the established square-norm condition, the inverse reconstructs a unique complementary domain vector solving the original Q equation, with the printed corrected-potential identity.

Public evidence: `NLS.ZakharovShabat.sourceLemma6_4_operator`, `NLS.ZakharovShabat.sourceQEquation_transformed`, `NLS.ZakharovShabat.weightedQSolution`, `NLS.ZakharovShabat.weightedQSolution_nonresonant`, `NLS.ZakharovShabat.weightedQSolution_potential_source`, `NLS.ZakharovShabat.weightedQSolution_equation`, `NLS.ZakharovShabat.weightedQSolution_unique`.

The transformed equation is a forward implication for a given v. Reconstruction uses the actual inverse and domain-valued solution; no converse is inferred merely by cancelling the potential map.

### S6-014: Exact opposite component shifts

- Scalar modulation shifts the actual Fourier coefficients, and its norm equals the scalar shifted norm with the full weighted coefficient power sum.
- Pair modulation uses physical shift -i in the first component and +i in the second. Reindexing the first component by -k gives w(k+i)^p times the sum of the two signed coefficient powers.
- Both directions of shifted norm comparison retain factor w(i), without an additional pair-norm factor.

Public evidence: `NLS.SpectralWeight.modulation_apply`, `NLS.SpectralWeight.norm_modulation`, `NLS.SpectralWeight.shiftedNorm_rpow_eq_tsum`, `NLS.SpectralWeight.pairModulation`, `NLS.SpectralWeight.shiftedPairNorm_rpow`, `NLS.ZakharovShabat.sourceShiftedNorm_formula`, `NLS.SpectralWeight.shiftedPairNorm_le`, `NLS.SpectralWeight.norm_le_shiftedPairNorm`.

Finite-p formulas include p=1 and retain the original component-sum power norm. The source reference for shifted norms is contextual.

### S6-015: Lemma 6.4 all finite Banach exponents

- For every source weight, finite p>=1, n, z in the full closed strip and integer shift i, the actual T map satisfies the opposite-shift bound with an exponent-only constant.
- At p=2 the literal printed constant two is retained. At p=1 the proved bound has constant one.
- T annihilates the resonant modes and is the actual original potential composed with the complementary domain inverse.

Public evidence: `NLS.ZakharovShabat.sourceLemma6_4`, `NLS.ZakharovShabat.sourceLemma6_4_two`, `NLS.ZakharovShabat.sourceLemma6_4_one`, `NLS.ZakharovShabat.sourceLemma6_4_operator`, `NLS.ZakharovShabat.sourceLemma6_4_resonant_zero`.

This reconciles the statement of Lemma 6.4. Its detailed Fourier-series, Holder and Young proof passage is S6-016. Enlarged constants for Lemma 6.5 do not replace c_2=2 here.

Section6PQAssertionsSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records these seven passages.

### S6-016: Full reciprocal series, shifted Holder and Young proof

- The weighted l1 representative of A_inverse Q has unchanged actual derivative-domain coefficients. Its full signed Fourier series converges with the literal denominator z-m*pi and the exclusion m!=n.
- Each scalar shifted norm is the exact absolutely weighted reciprocal sum. Holder bounds it by the conjugate punctured-lattice norm times the input shifted norm; for p>1 that lattice norm is the displayed reciprocal power sum.
- Young bounds the actual T output power by the two scalar l1 powers. Holder recombines these with exactly the opposite input shift and the original full pair norm.

Public evidence: `NLS.ZakharovShabat.sourceLemma64Vector_original_coefficients`, `NLS.ZakharovShabat.sourceLemma64Vector_original_hasSum`, `NLS.ZakharovShabat.sourceLemma64Proof_shifted_sum`, `NLS.ZakharovShabat.sourceLemma64Proof_holder_display`, `NLS.ZakharovShabat.sourceLemma64Proof_young_power`, `NLS.ZakharovShabat.sourceLemma64Proof_holder_power`, `NLS.ZakharovShabat.sourceLemma6_4_one`, `NLS.ZakharovShabat.sourceLemma6_4_two`.

The literal finite conjugate-power formula is restricted to p>1; the general Holder map and the separately proved constant-one estimate cover p=1. Fourier HasSum convergence is in the original weighted l1 norm with identification of original-domain coefficients.

### S6-017: Square decay and Neumann inversion

- Two opposite-shift applications restore the input shift. The squared operator in that shifted norm is bounded for every finite Banach exponent.
- For every positive epsilon, one potential neighborhood and one cutoff bound the squared norm by epsilon uniformly throughout all distant closed strips.
- The squared Neumann series converges as a series of operators on the original weighted space. Its factorization supplies both inverse identities for Id-T and the unique actual-domain Q solution.

Public evidence: `NLS.ZakharovShabat.shiftedPairNorm_weightedPotentialInverse_sq_le`, `NLS.ZakharovShabat.exists_uniform_complementarySquare_bound`, `NLS.ZakharovShabat.weightedEvenCorrection_hasSum`, `NLS.ZakharovShabat.weightedCorrection_formula`, `NLS.ZakharovShabat.weightedCorrection_left`, `NLS.ZakharovShabat.weightedCorrection_right`, `NLS.ZakharovShabat.exists_uniform_unique_weightedQSolution`.

Smallness is imposed on the shifted square; no unsupported smallness assumption on T itself is introduced.

### S6-018: Lemma 6.5 and exact retained-boundary tail

- For every source weight, every finite p>=1 and every point of each full closed strip, the induced shifted square norm has the displayed original-norm budget with an exponent-only constant.
- The potential remainder retains exactly |k|>=|n|, including the boundary, and its term is divided by w(n). The bracket in this estimate is 1+|n|.
- The conjugated operator norm is characterized by its action on all inputs in the exact source shifted pair norm.

Public evidence: `NLS.ZakharovShabat.sourceLemma6_5`, `NLS.ZakharovShabat.sourceSquareNorm_le_iff`, `NLS.ZakharovShabat.weightedPairFourierTail_fst`, `NLS.ZakharovShabat.weightedPairFourierTail_snd`, `NLS.ZakharovShabat.weightedSquareBound_eq_source`.

The constant is an explicit valid choice, without an optimality claim. The pi-scaled Sobolev example uses a different argument of the same bracket and does not change this integer-index decay.

### S6-019: Actual double inverse and full double coefficients

- The vector is the actual A_inverse Q Phi A_inverse Q f on the original derivative domain. Both signed coefficient series retain the two excluded indices and both complex denominators.
- The full double Fourier series converges absolutely in the original weighted l1 space. Its representative has exactly the original-domain coefficients.
- The literal weighted distance-denominator majorant is jointly summable and bounds both scalar components with their original opposite shifts.

Public evidence: `NLS.ZakharovShabat.sourceLemma65Proof_original_restricted`, `NLS.ZakharovShabat.sourceLemma65Vector_summable`, `NLS.ZakharovShabat.sourceLemma65Vector_original_coefficients`, `NLS.ZakharovShabat.sourceLemma65Vector_original_restricted_hasSum`, `NLS.ZakharovShabat.sourceLemma65ProofTerm_summable`, `NLS.ZakharovShabat.sourceLemma65Proof_original_majorants`.

No stronger absolute convergence in the derivative-domain norm is asserted. The formulas hold at the free center because the resonant denominators are excluded.

### S6-020: Near/far partition

- The far region uses a strict half-radius inequality in at least one of the two distances; the near region uses both weak inequalities.
- They partition the admissible nonresonant index pairs, and the full convergent majorant splits into their two subsums.

Public evidence: `NLS.ZakharovShabat.sourceLemma65ProofNear`, `NLS.ZakharovShabat.sourceLemma65ProofFar`, `NLS.ZakharovShabat.sourceLemma65ProofFar_iff`, `NLS.ZakharovShabat.sourceLemma65ProofTerm_split`.

The printed complement is taken inside k,l!=n. Boundary points belong to the near region.

### S6-021: Far weighted Holder estimate

- Submultiplicativity gives the exact source shifted weight comparison. The selected Holder display retains both its reciprocal moment and weighted numerator moment.
- The full numerator moment factors into the original scalar norms. The selected far reciprocal moment is bounded by two one-factor tails, giving the printed half-bracket decay.
- The p=1 endpoint uses a uniform reciprocal bound, and the zero strip is included. One explicit positive exponent-only proof constant supplies the estimate.

Public evidence: `NLS.ZakharovShabat.sourceLemma65Proof_submultiplicative`, `NLS.ZakharovShabat.sourceLemma65Proof_far_holder`, `NLS.ZakharovShabat.sourceLemma65ProofNumerator_moment`, `NLS.ZakharovShabat.sourceLemma65Moment_far_le`, `NLS.ZakharovShabat.sourceLemma65Moment_far_bracket`, `NLS.ZakharovShabat.sourceLemma65Moment_far_all`, `NLS.ZakharovShabat.sourceLemma65ProofConstant`.

The chosen Lemma 6.5 proof constant is enlarged. It does not replace the separately proved c_2=2 in Lemma 6.4.

### S6-022: Near geometry, weight gain and tail estimate

- Opposite near windows force the potential frequency into the retained-boundary tail. The relevant output and input distance bounds give the source weight gain by monotonicity.
- The near Holder display retains 1/w(n) and its selected numerator moment. Replacing the potential by its exact remainder leaves the entire near subsum unchanged.
- The near estimate uses the same exponent-only proof constant, including p=1, and reflection supplies the other physical orientation.

Public evidence: `NLS.ZakharovShabat.resonantWindows_tail`, `NLS.ZakharovShabat.resonantWindows_output_distance`, `NLS.ZakharovShabat.resonantWindow_input_distance`, `NLS.ZakharovShabat.sourceLemma65ProofNear_weight`, `NLS.ZakharovShabat.sourceLemma65ProofNear_tail`, `NLS.ZakharovShabat.sourceLemma65Proof_near_holder`, `NLS.ZakharovShabat.sourceLemma65Proof_near_tail_eq`, `NLS.ZakharovShabat.sourceLemma65Moment_near_all`, `NLS.ZakharovShabat.sourceLemma65Proof_true_reflection`.

All half-radius equalities and the tail boundary are retained; the source weight need not satisfy w(0)=1.

### S6-023: Component recombination and printed final equality

- The near and far estimates combine with exactly the factor 2^(1/p), the original scalar norms, both opposite input shifts and the exact potential remainder.
- One positive exponent-only constant c_p=sqrt(D_p) realizes the proof estimates, with c_p squared equal to the existing double-inverse constant.
- The final Young display is a proved chain of two inequalities in the original shifted pair norm. The printed second equality is replaced by the valid upper bound.

Public evidence: `NLS.ZakharovShabat.sourceLemma65Moment_half_to_full`, `NLS.ZakharovShabat.sourceLemma65Moment_recombine`, `NLS.ZakharovShabat.sourceLemma65Moment_recombine_true`, `NLS.ZakharovShabat.sourceLemma65Moment_original_bounds`, `NLS.ZakharovShabat.sourceLemma65ProofConstant_pos`, `NLS.ZakharovShabat.sourceLemma65ProofConstant_sq`, `NLS.ZakharovShabat.sourceLemma65Proof_corrected_chain`.

Retain the established correction and historical review. No additional refutation is needed or added. The main Lemma 6.5 estimate remains valid.

Section6RemainingProofSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records these eight passages.

### S6-024: Common half-contraction and compatible Neumann inverses

- One open convex potential neighborhood and one cutoff N>=1 give both printed half-contractions on every distant closed strip. The proof controls one Fourier tail on the neighborhood, uses tail monotonicity, and transports the unit-weight norm isometrically to the original component-sum space.
- The squared Neumann factorization is a two-sided inverse; its even series converges in the original operator norm. The weighted and original inverses agree on every weighted input.
- The actual derivative-domain Q solution is unique and satisfies Phi v=T_hat T Phi u. The inverse expansion and commutation give both product orders in Id+T_hat T=T_hat.
- Substitution of weightedQSolution_total_potential into sourceWeightedPencil_add_zero_iff_PQ gives the displayed P equation A u=P T_hat Phi u. This is a composition of the cited identities, with the original resonant/complementary conditions retained.

Public evidence: `sourceLemma6_5_uniform_half`, `sourcePotentialInverse_square_norm`, `exists_uniform_weightedFrequencyNeighborhood`, `sourceComplementaryCorrection_formula`, `sourceComplementaryCorrection_even_hasSum`, `sourceComplementaryCorrection_left`, `sourceComplementaryCorrection_right`, `sourceComplementaryCorrection_weightedInput`, `exists_uniform_sourceComplementaryCorrection`, `sourceQSolution_potential`, `sourceQSolution_unique`, `weightedCorrection_expand`, `weightedCorrection_commute`, `weightedQSolution_total_potential`, `sourceWeightedPencil_add_zero_iff_PQ`.

### S6-025: Reduced map and Lemma 6.6

- The resonant map is the free diagonal minus the corrected potential, with actual synthesis and coefficient extraction.
- Its matrix determinant vanishes exactly at a noninvertible original source pencil, equivalently at an original periodic eigenvalue. The source domain is covered by an equivalence, not only an inclusion.
- One neighborhood and cutoff make the criterion uniform on all distant closed strips, including p=1.

Public evidence: `weightedResonantMap`, `weightedResonantMatrix`, `sourceUnitDomainEquiv`, `sourceLemma6_6`, `sourceLemma6_6_eigenvector`, `sourceLemma6_6_uniform`.

### S6-026: Full original-domain reconstruction and converse

- The constructed v is the actual domain-valued complementary free inverse of the corrected potential. It belongs to the complementary derivative domain and solves the Q equation.
- The full reconstruction has the prescribed two resonant amplitudes. Its differential residual is exactly the synthesized matrix residual.
- Nonzero resonant data reconstruct a nonzero vector; every original eigenvector is recovered. Thus both directions of the source proof retain the nonzero requirement.

Public evidence: `weightedQSolution`, `complementaryFreeDomainInverse_nonresonant`, `weightedQSolution_potential`, `weightedQSolution_equation`, `sourceResonantReconstruction_eq`, `sourceResonantReconstruction_coordinates`, `sourceResonantReconstruction_ne_zero_iff`, `sourceResonantReconstruction_residual`, `sourceResonantReconstruction_kernel_iff`, `sourceResonantReconstruction_of_eigenvector`.

### S6-027: Actual matrix entries and printed basis order

- Matrix entries are evaluations of the actual original corrected potential on the two resonant domain modes.
- The printed (plus,minus) basis reverses the library physical (minus,plus) order. Reversing both indices gives exactly the displayed off-diagonal signs and leaves the determinant unchanged.
- The scalar determinant formula and its connection to the original periodic spectrum use these same entries.

Public evidence: `sourceCorrectionMatrix_entry`, `sourcePrintedResonantMatrix_form`, `sourcePrintedResonantMatrix_det`, `sourceResonantMatrix_det_formula`, `sourceSpectrum_iff_resonantScalarEquation`.

The mathematical matrix assertions are compared. The historical attribution to references [37,18] is not independently checked here.

### S6-028: Lemma 6.7 and required reality hypothesis

- The two diagonal entries agree for arbitrary complex potentials at every finite Banach exponent.
- The printed unconditional parameter-conjugation identity for a_n is false. The single fixed original potential (1,i) gives a_n(n*pi)=i/(2*pi*n) and violates it beyond every proposed cutoff, while satisfying half-contraction.
- The corrected statement assumes phi*=epsilon*phi, epsilon^2=1, for both the diagonal and signed off-diagonal conjugation conclusions. One common local cutoff supplies the conditions at z and conjugate(z).

Public evidence: `sourceLemma6_7_i`, `sourceResonantA_constant_center`, `exists_large_nonreal_sourceResonantA`, `not_sourceLemma6_7_printed_diagonal`, `sourceHasRealitySign_iff_coeff`, `sourceLemma6_7_ii`, `sourceLemma6_7_uniform`.

Corrected means a formal refutation and a separately scoped valid replacement; the printed unconditional statement is not marked proved.

### S6-029: Equal diagonals via transposition/conjugation

- The original cross-component unconjugated Fourier pairing is defined on a base coefficient vector and a derivative-domain test; its formula preserves the actual raw coefficients.
- Q transfers to the derivative-domain test. The actual punctured complementary inverse R=A^-1 Q is transpose symmetric, including at the free center. Potential multiplication is symmetric on two derivative-domain tests.
- Transposing T=Phi R reverses the two factors. Induction gives the full identity for every T^j Phi before any small-square assumption.
- When the shifted square is small, the full corrected potential is transpose symmetric on arbitrary derivative-domain tests. The proof cancels the equal R terms in the potential symmetry identity for f+R Hf and g+R Hg, where H=T_hat Phi.
- The original-source theorem uses the actual source correction and potential difference. The p=3 negative-strip integration example derives equality of the actual matrix diagonals directly from this full identity.

Public evidence: `sourceGreenPairing`, `sourceGreenPairing_apply`, `sourceGreenPairing_unitInput`, `weightedGreenPairing_complementaryProjection`, `weightedGreenPairing_complementaryInverse_symm`, `weightedGreenPairing_potential_symm`, `weightedGreenPairing_potentialInverse_transfer`, `weightedGreenPairing_powerPotential_symm`, `weightedGreenPairing_add_right`, `weightedGreenPairing_correctedPotential_symm`, `sourceCorrectedPotential_transpose`.

The source adjoint notation is implemented as its bilinear transpose identity on stated domains. No Hilbert adjoint on a general l^p space, bounded potential on the entire base space, or full free inverse at a resonant center is asserted. This domain interpretation remains explicit, rather than being counted as a literal formalization of every adjoint symbol.

### S6-030: Reality identities using the stated type assumption

- The proof explicitly assumes phi*=epsilon*phi. Physical conjugation reverses Fourier indices and exchanges components with the stated sign.
- The potential, domain-valued complementary inverse and T intertwine at conjugate spectral parameters. Uniqueness of the inverse transfers this to the full correction.
- Extraction on the two resonant modes gives the diagonal and signed off-diagonal parameter-conjugation identities. Both signs are covered; the type condition is retained throughout.

Public evidence: `sourcePotentialStar_fst`, `sourcePotentialStar_snd`, `sourceHasRealitySign_iff_coeff`, `weightedConjugation_domainPotential`, `weightedConjugation_domainInverse`, `weightedConjugation_potentialInverse`, `weightedConjugation_correction`, `weightedConjugation_correctedSynthesis`, `weightedResonantA_conj`, `weightedResonantBPlus_conj`, `sourceLemma6_7_ii`.

The formal proof uses signed conjugation and inverse uniqueness in place of manipulating Hilbert adjoints. It proves the displayed coefficient identities under the hypothesis used in the source proof.

### S6-031: Matrix form and full parity series (1.14)-(1.15)

- The displayed common-diagonal matrix has the printed basis order.
- Even terms of the diagonal and odd terms of each off-diagonal vanish individually, before any contraction condition.
- The even vector is the convergent sum of actual original operator powers. Continuous extraction yields the odd diagonal series and strictly positive even remainder series.
- Equations (1.14) and (1.15) retain the actual original T and the leading raw coefficients: second component at 2n, first component at -2n.

Public evidence: `sourcePrintedResonantMatrix_form`, `sourceResonantEvenVector_hasSum`, `sourceResonantA_even_term_zero`, `sourceResonantBPlus_odd_term_zero`, `sourceResonantBMinus_odd_term_zero`, `sourceResonantA_hasSum`, `sourceResonantBPlus_remainder_hasSum`, `sourceResonantBMinus_remainder_hasSum`, `sourceEquation1_14`, `sourceEquation1_15_plus`, `sourceEquation1_15_minus`.

### S6-032: Actual suprema on closed unbounded strips

- The source coefficient suprema are suprema of their actual images on the full closed unbounded strip, not only bounds for sampled values.
- Uniform bounds establish bounded-above images, nonnegative suprema and pointwise domination. The quantitative uniform theorem uses 1<p<infinity, as in the following Lemma 6.8.
- Equality of the original and weighted coefficient functions on the whole common correction strip gives equality of the actual supremum sets and values.

Public evidence: `sourceResonantDiagonalSup`, `sourceResonantBMinusSup`, `sourceResonantBPlusSup`, `sourceCoefficientStripBounds_of_bound`, `exists_uniform_sourceCoefficientStripBounds`, `sourceResonantSup_eq_weighted`, `exists_uniform_sourceResonantSup_eq`.

A real-valued sSup alone is not evidence of boundedness. The cited bounded-image theorem supplies that evidence for the actual coefficient functions.

### S6-033: Lemma 6.8 analytic scope and printed bounds

- The actual original coefficients have jointly analytic extensions on neighborhoods of every distant full closed strip. One potential neighborhood and one cutoff work together; this analytic assertion extends to p=1.
- For 1<p<infinity, the diagonal p-power sum has the stated original unweighted pair norm, exponent min(1,p-1), and retained-boundary Fourier tail. The current interface uses floor(N/2); previously published full-cutoff and ceiling-half variants retain their recorded scopes.
- The proof-consistent off-diagonal estimate sums p-powers of the actual weighted strip suprema, uses the full inner weighted pair norm, and retains the distinguished component to power p. The full signed tail is summable for every larger cutoff on one common neighborhood.
- The literal display omits the left-hand p-powers and uses the positive component inside the budget. Existing original p=2 cubic witnesses refute the locally uniform unpowered budget near zero; independent reversed cubic witnesses refute the component budget near (1,0) even with the left powers restored.

Public evidence: `sourceLemma6_8_analytic`, `sourceResonantFunctions_eq`, `analyticAt_sourceCorrectionEntryFunction`, `sourceDiagonalTailBudget`, `sourceDiagonalTailBudget_weightedInput`, `sourceOffDiagonalTailBudget`, `sourceOffDiagonalTailBudget_unit`, `sourceCoefficientPowerTail`, `SourceCoefficientTailEstimates`, `sourceLemma6_8_summability`, `sourceLemma6_8_quantitative`, `sourceLemma6_8_unweighted`, `exists_uniform_diagonalSummability`, `exists_uniform_offDiagonalSummability`, `sourceCubicPotential_remainder_center`, `sourceCubicPotential_remainder_norm`, `not_sourceLemma6_8_unpowered_sum`, `not_sourceLemma6_8_printed_sum`, `sourceReverseCubicPotential_remainder_center`, `sourceReverseCubicPotential_remainder_norm_sq`, `not_sourceLemma6_8_positive_component_sum`.

The counterexamples refute the locally uniform statements with common cutoffs. Their potentials may depend on the chosen index; they do not prove failure beyond every individual cutoff for one fixed potential. The literal printed off-diagonal display is not marked proved. This row compares the statement and existing proof-consistent interfaces; the diagonal and off-diagonal proof passages are reconciled below in S6-035 through S6-041.

### S6-034: Uniform series and corrected potential vector

- Every scalar parity term is built from the actual T_n powers and the actual resonant potential source. Its total extension is jointly analytic in potential and lambda near each point of the full closed strip, without a contraction hypothesis.
- The finite sums coincide exactly with the original source operator-power coefficients. Their physical extraction is first component at -n and second component at n; the leading remainder frequencies remain -2n and 2n.
- Under shifted half-contraction, the m-term diagonal error is at most 2*c_p*norm(phi)*norm(phi_first)*2^(-m), where c_p is the Lemma 6.4 complementaryConstant. A single reversal of the signed shift is retained.
- The weighted positive and negative remainder errors are at most 2^(-m) times the respective distinguished component norms. The factor w(2n) is retained; the bound uses the actual conjugated-square norm, not a replacement full-space contraction assumption.
- One open convex neighborhood containing phi and zero and one distant-index cutoff give geometric rates and one epsilon truncation length for all three series, every nearby potential, both signs of the index and every point of each unbounded closed strip. The resulting TendstoUniformlyOn theorems use the original coefficient functions.
- The corrected even vector is the actual inverse applied to Phi e_n. Its shifted norm is at most twice the opposite component norm. Its finite even approximants have geometric shifted-norm error.
- The displayed Fourier expansion of this vector is justified by a full weighted-norm HasSum of its two physical mode sequences: first at -k and second at k. The generic mode theorem applies to the actual corrected vector at every finite p>=1.

Public evidence: `weighted_resonantCoordinate_le_shifted`, `shiftedPairNorm_square_le_opNorm`, `weightedResonantParityPartialSum`, `weightedResonantParityPartialSum_eq`, `weightedResonantA_partialSum_error`, `weightedResonant_even_partialSum_error`, `weightedResonantBPlus_partialSum_error`, `weightedResonantBMinus_partialSum_error`, `weightedResonantParityTermFunction`, `weightedResonantParityPartialSumFunction`, `weightedResonantParityPartialSumFunction_eq`, `analyticAt_weightedResonantParityTermFunction`, `analyticAt_weightedResonantParityPartialSumFunction`, `exists_uniform_resonantParitySeries_rate`, `weightedMode_hasSum`, `weightedSignedPairMode_hasSum`, `forgetPairWeight_potentialInverse_pow`, `weightedResonantParityPartialSumFunction_forget`, `sourceResonantParityTermFunction`, `sourceResonantParityPartialSumFunction`, `sourceResonantParityTermFunction_eq`, `sourceResonantParityPartialSumFunction_eq`, `sourceResonantParityPartialSumFunction_weightedInput`, `analyticAt_sourceResonantParityTermFunction`, `exists_uniform_sourceResonantParitySeries_rate`, `exists_uniform_sourceResonantParitySeries`, `sourceLemma6_8_uniform_series`, `weightedResonantEvenVector`, `sourceResonantEvenVector`, `sourceResonantEvenVector_hasSum`, `shiftedPairNorm_evenCorrection_le_two`, `shiftedPairNorm_source_one`, `shiftedPairNorm_evenVector_one_le`, `exists_uniform_resonantEvenBounds`, `exists_uniform_resonantEvenApproximation`.

The analytic and convergence claims cover all finite p>=1. The quantitative power-tail estimates retain 1<p<infinity. Analyticity at boundary points comes from the actual open operator-inverse extension; uniform convergence only on a closed strip is not used alone to infer analyticity across its boundary. The error bounds hold also for m=0 and at free centers whenever their stated half-contraction holds.

### S6-035: Actual diagonal coefficient sum

- The actual original diagonal coefficient equals the signed Fourier sum of phi_second(n+m)/(lambda-pi*m) times the first component of the actual even vector at -m. The resonant term m=n is explicitly removed.
- The signed sum is absolutely convergent. Its physical-coordinate version is obtained by an actual frequency reflection, not a replacement scalar model.
- These identities hold for every finite p>=1 and every signed strip, including free centers, under the stated actual square contraction.

Public evidence: `sourceResonantA_signed_series`, `summable_sourceResonantA_signed_series`, `sourceResonantA_physical_series`, `sourceEquation1_14`, `sourceResonantEvenVector`, `sourceResonantFunctions_eq`, `weightedResonantA_eq_tsum`, `summable_weightedResonantA_terms`.

The source coefficient and even vector are the existing original differential-operator realizations. The theorem does not define the coefficient to be the desired scalar series. The p=1 endpoint is a series statement; the following conjugate-moment estimates require p>1.

### S6-036: Diagonal Holder estimate

- Holder bounds the actual diagonal by the norm of the first component of the actual even vector times the displayed reciprocal conjugate moment.
- Unit-weight isometry and half-contraction bound the whole original even vector by twice the unweighted first potential component. Weighted/unit inverse compatibility supplies this smaller norm for weighted inputs.
- Raising the pointwise bound gives exactly the factor 2^p, the distinguished unweighted component to power p and the reciprocal moment to power p/q.
- One open convex neighborhood containing the potential and zero, with one distant-strip cutoff, gives bounded actual images, nonnegative genuine full-strip suprema and the same p-power Holder bound.
- For every larger cutoff, both full signed outer tails are summable and their sums satisfy the displayed Holder comparison.

Public evidence: `sourceResonantA_signed_holder`, `norm_sourceResonantEvenVector_one_le`, `sourceResonantA_signed_holder_half`, `diagonalHolder_power_le`, `sourceResonantA_signed_holder_power`, `exists_uniform_sourceDiagonalHolder`, `exists_uniform_sourceDiagonalHolder_sum`, `forgetPairWeight_resonantEvenVector`, `norm_forget_evenVector_one_le_unweighted`, `norm_tsum_complementaryRow_le`, `norm_complementaryRowEnvelope_eq`, `exists_uniform_resonantDiagonalBound`, `exists_uniform_sourceResonantFunctions_weightedInput`, `summable_diagonalMomentPowerTail`.

The preceding weighted norm inequality alone does not yield the smaller unweighted factor printed in the second display. The proof uses the unit-weight inverse and its compatibility instead. The full-strip supremum is justified by boundedness; the spectral parameter dependence of the even vector is retained before taking that supremum. All quantitative assertions require 1<p<infinity.

### S6-037: Diagonal near/far power sums in both exponent ranges

- The literal inner moment is absolutely convergent and splits exactly into far |m-n|>=|n|/2 and near |m-n|<|n|/2 terms. The removed zero denominator contributes zero because q>0.
- Genuine coefficient rows identify each literal regional moment with the q-th norm power and its p/q power with the p-th norm power. The integer cutoff is ceil(|n|/2), including the equality case and odd cutoffs.
- Every distant far row is dominated by the fixed reciprocal kernel tail at ceil(N/2). Every near row sees only potential frequencies of magnitude at least N, retaining the tail boundary.
- Powered Young gives both exact regional kernel budgets. Contractive exponent inclusion proves the displayed concave p/q step when p<=q; the conjugate identities identify the two exponent regimes.
- One positive exponent-only regional constant gives far decay N^(-1) for p>=2 and N^(-(p-1)) for 1<p<=2, and the near bound by the p-power of the actual potential tail. All outer regional sums are summable.
- Recombining the actual regions and the original Holder sum proves the diagonal estimate first with unweighted distinguished components and the full cutoff, then with the printed original pair norm and floor(N/2) tail. One neighborhood works for every larger cutoff.

Public evidence: `diagonalFarRow`, `diagonalNearRow`, `diagonalFarRow_apply`, `diagonalNearRow_apply`, `diagonalFarRow_add_near`, `diagonal_near_potential_tail`, `norm_diagonalFarRow_le`, `norm_diagonalNearRow_le`, `norm_diagonalHalfKernel_le`, `diagonalRow_power_sum_le`, `diagonalFarRow_sum_le`, `diagonalNearRow_sum_le`, `diagonalFarMoment`, `diagonalNearMoment`, `diagonalFarMoment_eq`, `diagonalNearMoment_eq`, `diagonalFarMoment_power_eq`, `diagonalNearMoment_power_eq`, `summable_diagonalMoment`, `diagonalMoment_split`, `diagonal_far_region_iff`, `diagonalFarMoment_sum_le_kernel`, `diagonalNearMoment_sum_le_kernel`, `diagonalFarMoment_concave_le`, `diagonalNearMoment_concave_le`, `diagonalRegionConstant`, `diagonalRegionConstant_pos`, `diagonalRegion_decay_power`, `diagonalMoment_region_bounds`, `diagonal_conjugate_regimes`, `diagonalFarMoment_sum_ge_two`, `diagonalFarMoment_sum_le_two`, `diagonalMomentPowerTail`, `diagonalMomentPower_eq`, `summable_diagonalMomentPowerTail`, `diagonalMomentPowerTail_sum_le`, `diagonalSummationConstant`, `diagonalProofConstant`, `diagonalProofConstant_pos`, `exists_uniform_sourceDiagonalProofBound`, `diagonalProof_component_budget_le_pair`, `sourceLemma6_8_diagonal_proof`.

The displayed inequalities use a weak far cutoff and a strict near cutoff; the preceding prose uses > for the far region. The formal partition follows the displayed inequalities and explicitly retains equality. The new diagonalProofConstant is an admissible, non-optimal exponent-only constant, equal to 2^p times the existing sharper diagonalSummationConstant. The sharper result is preserved. This completes the diagonal proof passage. The off-diagonal proof is reconciled below; the final p.44 summed inequality remains open.

### S6-038: Off-diagonal double sum and inserted weight factor

- The actual negative and positive remainders equal the signed physical double Fourier series, with their respective reflected potential and even-vector components. Joint absolute convergence justifies both summation orders, including the free center and finite p=1.
- The p.42 right side contains an extra w(2n). It equals the weighted remainder; the literal unweighted equality holds only if the weight equals one or the remainder vanishes.
- The existing constant-weight-two counterexample uses original analytic coefficient functions and both weighted and unit contraction domains. Its variable-amplitude version refutes validity on any neighborhood of one fixed background with a common distant cutoff.
- Submultiplicativity and symmetry transfer the output weight to the two actual potential coefficients and the shifted input, and the complementary denominators are bounded by the punctured reciprocal kernels.

Public evidence: `weightedPotentialInverse_sq_fst_apply`, `weightedPotentialInverse_sq_snd_apply`, `weightedResonantBMinus_remainder_eq_tsum`, `weightedResonantBPlus_remainder_eq_tsum`, `sourceLemma68_offDiagonal_summable_norm`, `sourceLemma68_offDiagonal_original`, `sourceLemma68_offDiagonal_hasSum`, `sourceLemma68PrintedOffDiagonalSeries_eq`, `sourceLemma68_printed_series_equality_iff`, `sourceLemma68_printed_series_source_counterexample`, `sourceLemma68_printed_series_not_locally_uniform`, `sourceLemma68PrintedOffDiagonalSeries_restricted`, `norm_complementarySymbol_centered_le`, `weightedOffDiagonalTerm`, `norm_weightedOffDiagonalTerm_le`, `NLS.SpectralWeight.double_index_weight_le`.

The misplaced weight is a source correction, not a newly asserted literal equality. The local counterexample allows the potential to depend on the chosen frequency; it does not give one fixed potential defeating every individual cutoff. The earlier correction and its scope are preserved.

### S6-039: Three index regions and (1.16)

- The literal far-k and far-l regions use strict half-radius inequalities and may overlap. Their union and the weak near region cover all nonresonant pairs; the near region includes equality and is exactly the complement of their union.
- The integer cutoff floor(abs(n)/2)+1 is equivalent to the strict real half-radius, including odd and negative frequencies. Both resonant indices are explicitly removed in the physical predicates and moments.
- Each regional reciprocal moment converges jointly and equals the q-th power of a genuine nested sequence norm. Its p/q power equals the p-th norm power.
- The physical weighted summand in (1.16) is exactly the normalized two-index Holder test. Joint convergence and two Holder inequalities give the actual weighted potential norm, shifted input norm and literal moment root with constant one.
- In the near region both actual potential frequencies lie in the full retained-boundary tail at N for abs(n)>=N. Taking N=abs(n) gives the stronger outer-potential tail at abs(n), hence the indicated half-tail. Summation retains the tail at the common cutoff N.
- The sum of the three positive regional tests dominates every actual weighted term. The overlap is used as an upper bound, not asserted to be a disjoint sum identity.

Public evidence: `OffDiagonalProofRegion`, `offDiagonalProofCutoff`, `OffDiagonalProofRegion.left`, `OffDiagonalProofRegion.right`, `OffDiagonalProofRegion.contains`, `offDiagonalProofCutoff_iff`, `offDiagonalProofNear_iff`, `offDiagonalProofRegions_cover`, `offDiagonalProofNear_complement`, `offDiagonalProofNear_tail_indices`, `offDiagonalProofCutoff_real_iff`, `offDiagonalProofNear_real_iff`, `offDiagonalProofLeftKernel`, `offDiagonalProofRightKernel`, `offDiagonalProofLeftKernel_apply`, `offDiagonalProofRightKernel_apply`, `offDiagonalProofRow`, `offDiagonalProofMomentTerm`, `offDiagonalProofMoment`, `offDiagonalProofMomentTerm_eq`, `offDiagonalProofMoment_eq`, `summable_offDiagonalProofMomentTerm`, `offDiagonalProofMoment_power_eq`, `norm_iteratedRow_mono_kernels`, `offDiagonalProofKernels_exponent`, `norm_offDiagonalProofRow_le_inner`, `norm_offDiagonalProofFarRow_eq`, `norm_offDiagonalProofFarRow_le`, `offDiagonalProofNearRow_eq_tail`, `norm_offDiagonalProofNearRow_le`, `offDiagonalProofMoment_concave_le`, `offDiagonalProofTest`, `summable_offDiagonalProofTest`, `offDiagonalProofTest_holder`, `offDiagonalProofNearTest_eq_tail`, `offDiagonalProofNearTest_holder`, `offDiagonalProofWeightedTerm`, `offDiagonalProofWeightedTerm_eq`, `summable_offDiagonalProofWeightedTerm`, `offDiagonalProofWeightedSum_eq`, `sourceEquation1_16`, `sourceEquation1_16_near`, `norm_weightedOffDiagonalTerm_le_proof_regions`, `norm_tsum_offDiagonal_proof_regions_le`.

These are the source n-dependent strict-far/weak-near regions. Earlier disjoint floor(N/2) majorants remain available but are not identified with these literal sets. Zero denominators vanish through punctured kernels, and the finite conjugate-moment identities require 1<q<infinity.

### S6-040: High-exponent off-diagonal sum estimates

- Powered Young gives the exact two-kernel budget for each literal far moment, with the fixed strict kernel cutoff floor(N/2)+1, and the full potential-tail kernel budget for the literal near moment.
- All outer regional power sums converge. A common explicit exponent-only constant bounds each far sum by norm(a)^p/N when p>=2 and the near sum by norm(tail_N a)^p.
- The two actual far row norms agree by a jointly summable kernel swap. Bounding the actual shifted even vector gives the literal three-region remainder bound with both potential factors retained.
- The complete majorant power sum converges and is bounded first by the product of the two weighted component norms and the product of their full-cutoff tails, then by the original weighted pair norm with its full Fourier cutoff.
- One open convex neighborhood containing the potential and zero, and one threshold, give bounded original coefficient images, nonnegative genuine full-strip suprema, convergent signed p-power tails and both original coefficient-label estimates at every larger cutoff.

Public evidence: `offDiagonalProofFarMoment_sum_le_kernel`, `offDiagonalProofNearMoment_sum_le_kernel`, `offDiagonalProofMoment_power_summable`, `offDiagonalProofMoment_sum_concave_le`, `norm_offDiagonalProofHalfKernel_le`, `offDiagonalProofRegionConstant`, `offDiagonalProofRegionConstant_pos`, `offDiagonalProofMoment_region_bounds`, `offDiagonalProofFarMoment_sum_ge_two`, `offDiagonalProofFarMoment_sum_le_two`, `offDiagonalProofRowTail`, `offDiagonalProofRowTail_power`, `offDiagonalProofFarRow_norm_eq`, `offDiagonalProofBound`, `offDiagonalProofBound_nonneg`, `weighted_norm_tsum_offDiagonal_proof_le`, `offDiagonalProofConstant`, `offDiagonalProofConstant_pos`, `offDiagonalProofBound_summable_and_le`, `offDiagonalProofBound_sum_le_of_norm_bounds`, `weightedResonantBMinus_remainder_proof_le`, `weightedResonantBPlus_remainder_proof_le`, `exists_uniform_sourceOffDiagonalProofBound`, `summable_offDiagonalProof_dominated_tail`, `offDiagonalProofBound_minus_sum_le_pair`, `offDiagonalProofBound_plus_sum_le_pair`, `sourceLemma6_8_offDiagonal_proof`, `shiftedPairNorm_evenVector_one_le`, `shiftedPairNorm_evenVector_zero_le`, `exists_uniform_sourceResonantFunctions_weightedInput`, `weightedStripSup_bounds`, `norm_offDiagonal_componentTails_le_fullCutoff`.

The recombined statement follows the p-power/full-pair estimate on p.43. It does not reinstate the refuted p.41 unpowered or positive-component-only formula. The new exponent-only constant is explicit and not claimed optimal; earlier constants and estimates remain unchanged.

### S6-041: Low-exponent off-diagonal sum estimates

- Contractive exponent inclusion proves the concave p/q comparison for every literal regional moment when p<=q. A separate theorem compares convergent outer sums with the displayed p-moment sum.
- For 1<p<=2, each far-k and far-l outer sum has decay N^(-(p-1)); their sum therefore has the same decay with twice the regional constant. The near sum retains the actual full potential tail.
- The same regional recombination and original full-strip theorem cover every finite p>1, including p=2 consistently in both exponent regimes. The distinguished potential component is exchanged correctly between the negative and positive remainder.

Public evidence: `offDiagonalProofMoment_concave_le`, `offDiagonalProofMoment_power_summable`, `offDiagonalProofMoment_sum_concave_le`, `offDiagonalProofMoment_region_bounds`, `offDiagonalProofFarMoment_sum_le_two`, `offDiagonalProofBound_summable_and_le`, `sourceLemma6_8_offDiagonal_proof`, `diagonal_conjugate_regimes`.

The quantitative moment and power-tail assertions require 1<p<infinity. The p=1 series identity and convergence are separate earlier results. Completing this proof passage does not resolve the final p.44 summed eigenvalue inequality.

### S6-042: Actual determinant and Rouche preparation

- The scalar determinant is exactly (lambda-pi*n-a)^2-bPlus*bMinus and equals the actual reduced matrix determinant in both physical and printed basis orders on the original contraction domain.
- It is jointly analytic in the original component-sum potential space and spectral parameter. One open convex neighborhood containing the potential and zero and one distant cutoff support this statement on every full closed strip.
- Under the same strip control, the determinant differs from the centered square by strictly less than the modulus of that square on the exact pi/4 boundary.

The closeness is a boundary comparison sufficient for Rouche, not an unqualified estimate at the free center where the centered square vanishes. The actual correction domain and original norm are retained.

Public evidence: `sourceResonantDeterminantFunction`, `sourceResonantDeterminantFunction_eq_det`, `sourceResonantDeterminantFunction_eq_printed_det`, `analyticAt_sourceResonantDeterminantFunction`, `exists_uniform_sourceResonantDeterminant_control`, `SourceResonantStripControl.quadratic_comparison`.

### S6-043: Lemma 6.9 roots, gap and literal duplicated positive sum

- Every sufficiently distant signed strip has exactly two roots with analytic multiplicity. They lie in the open pi/4 disk, exhaust the original periodic spectrum there, and retain its actual algebraic multiplicities, including a double root.
- The square of the root gap is at most six times the genuine full-strip supremum of the actual off-diagonal product. A common original open convex neighborhood and one cutoff support the root and gap statements.
- The printed positive-index sum repeats the first root label. Existing original p=2 witnesses refute both the signed two-root budget and the literal duplicated-positive-root budget on every neighborhood of zero with a common cutoff; choosing different root labels does not repair them.
- The corrected signed and positive two-root sums converge and retain an additive leading Fourier tail outside the nonlinear potential-norm factors. The literal duplicated-positive-root sum is bounded by twice that corrected budget, with the same chosen roots, neighborhood and all larger cutoffs.

The missing leading tail is a substantive correction; the duplicated label is separately retained rather than silently changed. The refutations concern the locally uniform assertion at zero, not every potential-specific eventual estimate. Finite 1<p<infinity and the original component-sum norm are preserved.

Public evidence: `SourceResonantRootPair`, `SourceResonantRootPair.zero_count`, `sourceLemma6_9`, `SourceLemma69Proof`, `sourceLemma6_9_proof`, `not_sourceLemma6_9_printed_pair_sum`, `not_sourceLemma6_9_printed_duplicated_positive_sum`, `sourceLemma6_9_corrected_positive`, `sourcePositiveDisplacementPowerTail_self_summable_and_le`, `sourcePeriodTwoDisplacementBudget`, `rootDisplacementBudget`.

### S6-044: Uniform strip bounds, Rouche counts and no exterior roots

- Both leading signed Fourier coefficients are bounded by the full pair tail at 2*abs(n), with equality at the retained boundary allowed. Each full coefficient is bounded by that tail plus its actual remainder.
- One common original neighborhood and cutoff provide the literal diagonal pi/32 and off-diagonal pi/16 bounds. The sum of the actual diagonal supremum and the square root of the actual product supremum is strictly less than the exterior infimum, exactly pi/4 and attained on the refined boundary.
- The literal first Rouche comparison gives one zero for h=lambda-pi*n-a. The analytic zero count of a power multiplies by its exponent, so h squared has two zeros; the second strict comparison transfers this count to the determinant.
- The diagonal zero is unique and simple on the whole strip. Finiteness and nonvanishing on the boundary justify the use of analytic orders. The determinant has no root in the strip outside the open refined disk, including its boundary.

The source R_(2n) shorthand is interpreted as the symmetric Fourier cutoff 2*abs(n) for signed indices. Suprema are actual bounded full-strip images. A natural-order count of one alone is not used to infer simplicity without the additional analyticity, finiteness and nonvanishing conditions.

Public evidence: `sourceResonantLeading_le_fullTail`, `sourceResonant_fullCoefficient_le_tail_add`, `exists_uniform_sourceResonantDeterminant_control`, `SourceResonantStripControl.product_bounds`, `resonantProof_exterior_isLeast`, `resonantProof_exterior_inf`, `SourceResonantStripControl.sup_separation`, `resonantProof_boundary_comparisons`, `analyticZeroCount_pow`, `resonantProof_two_step_rouche`, `resonantProof_unique_simple_diagonal`, `SourceResonantStripControl.two_step_rouche`, `sourceLemma6_9_proof_roots`.

### S6-045: Branch-free root estimate, Cauchy derivative and gap

- For any pointwise square root of bPlus*bMinus, the determinant factors and a zero satisfies either sign of the root equation. Its residual modulus is exactly the real square root of the product norm. No globally analytic square-root branch is assumed.
- The pointwise p-power displacement estimate explicitly retains both signed leading Fourier coefficients and both remainders. Summation yields the corrected budget, not the printed estimate that omits the additive leading tail.
- A pi/4 closed ball about every refined-disk point stays in the strip. Cauchy gives the actual diagonal derivative bound 1/8, and the complex mean-value inequality gives the corresponding Lipschitz estimate.
- The actual gap obeys norm(x-y)<=norm(x-y)/8+2*sqrt(productSup), hence its square is at most six times productSup. The rendered first line of the source intermediate gap display repeats xiPlus on the left; the proved inequality uses xiPlus-xiMinus as required by the next line and conclusion.

The pointwise square-root notation is sufficient for the source argument; it does not assert analytic factor functions on the whole strip. The repeated left-hand label is a typographical correction, while the claimed printed displacement-sum consequence needs the substantive leading-tail correction already refuted in S6-043.

Public evidence: `resonantProof_root_factorization`, `resonantProof_root_alternatives`, `resonantProof_root_modulus`, `sourceResonantRoot_displacement_rpow_le`, `resonantRoot_displacement_rpow_le`, `exists_uniform_resonantDisplacementMajorant`, `sourceLemma6_9_proof`, `closedBall_refined_point_subset_strip`, `norm_deriv_le_on_refined_disk`, `norm_diagonal_sub_le_on_refined_disk`, `SourceResonantStripControl.deriv_bound`, `SourceResonantStripControl.gap_linear`, `norm_gap_sq_le_of_residual_bounds`, `SourceResonantStripControl.proof_roots`.

### S6-046: Identification with actual periodic pairs

- The counted determinant roots identify the complete original periodic spectral pair on each distant strip. The bridge carries algebraic multiplicity, using the independent spectral count rather than inferring multiplicity from equal zero sets.
- One common original open convex neighborhood and threshold identify the determinant-root multiset with the raw period-two canonical endpoint multiset. The norm of their difference equals the canonical gap norm, also when the roots coincide.
- The same chosen roots admit the corrected signed and positive-index displacement estimates at every larger cutoff. Label invariance of the signed sum transports the established budget onto the pair selected for the canonical identification.

This row matches the spectral-pair identification and its transfer mechanism; its quantitative consequence uses the corrected budget from S6-043 and does not reinstate the false literal budget. It applies to arbitrary raw period-two input, with no period-one embedding, reality, distinctness or continuous-label-choice assumption. The final weighted-gap inference is now supplied by corrected row S6-047.

Public evidence: `SourceResonantRootPair.toEndpoints`, `sourceLemma6_9_proof_canonical`, `sourceLemma6_9_proof`, `sourceProposition6_1_canonical_asymptotics`, `PeriodicEndpointPair.multiset_eq`, `sourceResonantRoot_displacementTail_eq`, `SourceResonantRootPair.of_periodic`, `mem_periodicSpectrum_iff_weightedDeterminant_zero`.

### S6-047: Final weighted gap estimate and source constants

- The counted original periodic pair gives the weighted p-power gap bound with C_p=2^(3*p-2). The leading physical coefficients are the first component at -2*n and the second at 2*n. Both remainders use the actual functions on the whole strip; their suprema include w(2*n).
- The grouped leading and remainder tails are summable. The actual canonical gap tail is dominated by their sum times C_p, for every signed index with abs(n)>=N, including the cutoff boundary. No reality or distinct-root assumption is introduced.
- For every source weight and 1<p<infinity, one open convex weighted neighborhood containing the input and zero supplies a cutoff valid for all larger cutoffs. The original canonical gap norm agrees with the counted source pair, retaining the established algebraic multiplicities.
- Lemma 6.8 bounds the coefficient-side sum by the corrected rootGapBudget, in the original weighted pair norm with the additive leading Fourier tail and floor(N/2). The original unweighted space also has the reciprocal-constant form with 1/C_p on the left.
- The constant is deliberately nonoptimal. The passage is classified as corrected on the strength of this valid replacement; no new refutation of the printed constant is required or asserted. All previous source corrections remain in force.

Public evidence: `rootGapSummationConstant_eq_rpow`, `sourceGapLeadingPowerTail`,
`sourceGapRemainderPowerTail`, `sourceCanonicalWeightedGapPowerTail`,
`sourceResonantRootPair_gap_le_four_terms`, `sourceCanonicalGapSum_le_coefficients`,
`sourceGapCoefficientSums_le_budget`, `exists_uniform_sourceGapCoefficientData`,
`sourceProposition6_3_coefficient_sum_corrected`,
`sourceProposition6_3_coefficient_sum_unweighted`.

Section6CorrectedGapSumSourceComparison-2026-10-28 in the
[source-review index](source-review-index.json) records this correction.
The earlier coefficient-side and moving-center asymptotic modules remain
supporting results; they are not needed for the corrected-constant proof.

## Remaining work

Continue with Section 7 and then the later sections in source order.
The source-wide inventory, exact cited Birkhoff construction and Appendix
G.2 interpretation remain unfinished. Preserve each reviewed group's exact
scope and corrections when using this ledger in the overall assessment.
