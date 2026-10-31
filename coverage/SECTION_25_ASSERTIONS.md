# Section 25 ordered assertion comparison

The ordered Section 25 comparison covers 37 groups on printed pp. 107–112: 28 matched, seven corrected and two contextual, with no partial or pending groups in this local ledger. The original operator and exact physical norms, closed-strip P/Q splitting, actual inverse and matrix coefficients are retained. Every complex H1 or M1 source, signed index and equality at the quadratic threshold is included where the corresponding statement permits it. The printed localization radius, central box, canonical multiplicities and gap constants are preserved. The auxiliary diagonal root is unique and simple even when the determinant has a double root. Direct corrections use the actual denominator kernel, the component-product diagonal estimate, both inverse exponents, the immediate lemma reference, the imaginary factor and the exact inclusive Fourier-tail transport. The global complex gap estimate uses a positive horizontal-packing and spectral-height budget on one common open neighborhood chosen before all weights and sources. Historical attributions and the later-use transition are contextual. Existing refutations remain unchanged; this documentation step adds no Lean proof or refutation. Broader completeness and Appendix G.2 qualifications remain.

Source: printed pp. 107–112, text lines 8782–9220, excluding the
Section 24 footnote at 8794–8795. Line numbers count newline characters
and preserve form feeds. All six rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S25-001 | 8784–8791 | Original operator and quantitative localization objective | matched |
| S25-002 | 8791–8793 | Fixed-L2-norm spectral translation and lack of uniform asymptotic localization | matched |
| S25-003 | 8806–8810 | Theorem 25.1 exact high-index threshold and radius | matched |
| S25-004 | 8812–8814 | Theorem 25.1 central box | matched |
| S25-005 | 8817–8821 | Historical comparison and quadratic threshold | contextual |
| S25-006 | 8822–8829 | Lyapunov-Schmidt approach and free double modes | matched |
| S25-007 | 8831–8840 | Closed strips and weighted complementary mode projections | matched |
| S25-008 | 8841–8855 | Original eigenvalue equation and P/Q splitting | matched |
| S25-009 | 8857–8868 | Complement inverse and actual potential-resolvent operator | matched |
| S25-010 | 8878–8882 | Uniform first-operator shifted bound | matched |
| S25-011 | 8884–8889 | Regularity factor and quadratic square threshold | matched |
| S25-012 | 8891–8895 | Lemma 25.2 square bound with constant four | matched |
| S25-013 | 8897–8910 | Actual two-resolvent Fourier expansion | matched |
| S25-014 | 8912–8917 | M1 weight inequality | matched |
| S25-015 | 8919–8930 | Weighted l1 convolution and Holder estimate | matched |
| S25-016 | 8933–8938 | Two explicit summation constants | corrected |
| S25-017 | 8940–8950 | Component estimates and squared operator bound | matched |
| S25-018 | 8960–8968 | One-half contraction, inverse and Q solution | matched |
| S25-019 | 8969–8978 | Reduced matrix with equal diagonal coefficients | matched |
| S25-020 | 8979–8990 | Formula (5.7) literal diagonal and off-diagonal inverse series | matched |
| S25-021 | 8992–8994 | Joint analyticity and coefficient symmetries | matched |
| S25-022 | 8996–9004 | Lemma 25.3 diagonal and separate-component remainder bounds | matched |
| S25-023 | 9006–9028 | Convergent inverse and first diagonal bound | corrected |
| S25-024 | 9029–9038 | Second diagonal representation and combined constant | corrected |
| S25-025 | 9039–9050 | Off-diagonal shifted Fourier remainder | matched |
| S25-026 | 9062–9075 | Lemma 25.4 exact canonical roots, multiplicities, radius and gap bound | matched |
| S25-027 | 9077–9092 | Determinant radius from coefficient estimates | matched |
| S25-028 | 9094–9107 | Rouche root count and canonical enumeration | matched |
| S25-029 | 9109–9120 | Theorem 25.1 remaining horizontal spectral box | corrected |
| S25-030 | 9122–9131 | Imaginary-part estimate from physical H1 norm | corrected |
| S25-031 | 9133–9134 | Transition to weighted gap estimates | contextual |
| S25-032 | 9136–9148 | Proposition 25.5 inclusive tail with constants 6 and 1152 | matched |
| S25-033 | 9148–9156 | Common complex neighborhood and global constant 265 | matched |
| S25-034 | 9167–9183 | Squared gap and both Fourier remainder estimates | matched |
| S25-035 | 9185–9196 | Tail summation and exact inclusive physical cutoff | corrected |
| S25-036 | 9198–9208 | Central complex gap budget and global cutoff choice | corrected |
| S25-037 | 9210–9217 | Formula (5.8) individual weighted gap estimate | matched |

## Compared passages

### S25-001: Original operator and quantitative localization objective

- The localization concerns the actual period-one Zakharov-Shabat source and its original periodic spectrum. The Section 25 family extends the same Section 24 data.

Public declarations:

- `NLS.ZakharovShabat.sourceSection25_original`
- `NLS.ZakharovShabat.sourceH1_spectrum_subset`
- `NLS.ZakharovShabat.SourceSection24Data.section25`

The introductory purpose is quantitative control of the higher-action asymptotic; later action estimates remain in their own sections.

### S25-002: Fixed-L2-norm spectral translation and lack of uniform asymptotic localization

- Opposite Fourier waves translate the actual constant spectrum by n*pi while preserving the physical L2 norm. Every positive L2 ball fails uniform asymptotic free-lattice localization at a fixed positive radius scale.

Public declarations:

- `NLS.ZakharovShabat.sourcePlaneWave_mem_spectrum_iff_constant`
- `NLS.ZakharovShabat.sourcePlaneWave_physical_norm_sq`
- `NLS.ZakharovShabat.not_uniform_L2_sphere_spectral_localization`
- `NLS.ZakharovShabat.not_uniform_L2_ball_spectral_localization`

These existing source theorems are retained unchanged. The claim is failure of uniform asymptotic localization, not failure of every coarse enclosure. No new obstruction proof is added.

### S25-003: Theorem 25.1 exact high-index threshold and radius

- At 8*P^2<=1+abs(n), both canonical endpoints are within P^2/(1+abs(n))+sqrt(2)*P/(1+abs(2*n))<pi/5 of n*pi. P is the exact original component-sum H1 norm with weight 1+abs(2*n*pi).

Public declarations:

- `NLS.ZakharovShabat.sourceH1_uniform_localization`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_norm_sq`
- `NLS.ZakharovShabat.quadraticLocalizationRadius_lt_pi_div_five`

Every complex H1 source, signed index and threshold equality is included. There is no extra qualitative cutoff.

### S25-004: Theorem 25.1 central box

- Every remaining indexed eigenvalue lies in the box abs(Re z)<=(8*P^2-1/2)*pi and abs(Im z)<=P. The endpoints exhaust the full periodic spectrum.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_uniform_localization`
- `NLS.ZakharovShabat.sourceH1_spectrum_subset`
- `NLS.ZakharovShabat.H1_canonicalEndpoints_mem_centralBox`

The same physical norm and canonical labels are used for the high-index discs and central box.

### S25-005: Historical comparison and quadratic threshold

- The remark compares previous thresholds and highlights the quadratic threshold of Theorem 25.1.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_uniform_localization`

Historical attribution and comparisons with cited publications are contextual. The actual quadratic estimate is covered in S25-003.

### S25-006: Lyapunov-Schmidt approach and free double modes

- Each free n*pi has algebraic multiplicity two, with exactly the two signed Fourier modes. Explicit resonant reduction reconstructs actual domain eigenvectors from the two-dimensional kernel.

Public declarations:

- `NLS.ZakharovShabat.periodicAlgebraicMultiplicity_zero`
- `NLS.ZakharovShabat.periodicRootSpaceTop_zero_eq_range`
- `NLS.ZakharovShabat.weighted_eigenvector_iff_resonant_det_zero`

The free statement includes n=0 and excludes additional Jordan chains. Historical attribution of the method is contextual.

### S25-007: Closed strips and weighted complementary mode projections

- The closed strips and actual signed Fourier masks give the P/Q splitting. Its two parts are orthogonal in the exact weighted Hilbert norm, with synthesis and coordinates realizing the resonant subspace.

Public declarations:

- `NLS.ZakharovShabat.resonantStrip`
- `NLS.ZakharovShabat.resonantProjection`
- `NLS.ZakharovShabat.complementaryProjection`
- `NLS.ZakharovShabat.resonant_add_complementary`
- `NLS.ZakharovShabat.weightedResonantSplit_inner_eq_zero`
- `NLS.ZakharovShabat.resonantSynthesis_coordinates`
- `NLS.WeightedCoeffPair.norm_rpow_eq_tsum`

Orthogonality uses the sum of the two scalar Hilbert inner products after the exact weighting isometries. The positive orthogonality proof and its public example passed the full checks and are committed and pushed.

### S25-008: Original eigenvalue equation and P/Q splitting

- The weighted free pencil is the restriction of the original differential pencil. It preserves both Fourier subspaces, and the complete reconstructed residual is precisely the synthesized P-equation residual.

Public declarations:

- `NLS.ZakharovShabat.weightedFreePencil_eq_original`
- `NLS.ZakharovShabat.pencil_resonantSynthesis`
- `NLS.ZakharovShabat.pencil_complementaryProjection`
- `NLS.ZakharovShabat.weightedReconstruction_residual`

All vectors lie in the actual one-derivative domain; the potential and physical signs are retained.

### S25-009: Complement inverse and actual potential-resolvent operator

- The complementary free inverse solves the Q equation in both orders, including at the resonant center. T_n is the actual potential composed with that inverse, and its equation agrees with the original source operator.

Public declarations:

- `NLS.ZakharovShabat.pencil_complementaryFreeDomainInverse`
- `NLS.ZakharovShabat.complementaryFreeDomainInverse_pencil`
- `NLS.ZakharovShabat.complementaryFreeDomainInverse_unique`
- `NLS.ZakharovShabat.weightedPotentialInverse_eq_original`
- `NLS.ZakharovShabat.weightedQSolution_potential_source`

The resonant modes are removed before inversion. Derivative gain and uniqueness are proved on the entire closed strip.

### S25-010: Uniform first-operator shifted bound

- For every integer shift i, the actual Hilbert operator satisfies norm_i(T_n f)<=2*norm(phi)*norm_(-i)(f), uniformly at all closed-strip points.

Public declarations:

- `NLS.ZakharovShabat.shiftedPairNorm_weightedPotentialInverse_two_le`

The reversal of the shift and exact constant two are retained; no M1 assumption is needed for this first-operator bound.

### S25-011: Regularity factor and quadratic square threshold

- An exact linear factor in the spectral weight yields a square bound decaying as 1/(1+abs(n)) and a one-half contraction at the quadratic threshold, uniformly on bounded source sets.

Public declarations:

- `NLS.SpectralWeight.HasLinearFactor`
- `NLS.ZakharovShabat.sourceM1_square_bound`
- `NLS.ZakharovShabat.sourceM1_square_contraction`

The cited lower-regularity refinements are contextual. The present quantitative result covers the full M1 class.

### S25-012: Lemma 25.2 square bound with constant four

- The actual conjugated square has operator norm at most 4*norm(phi)^2/(1+abs(n)) for every M1 weight and every closed-strip parameter.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_square_bound`
- `NLS.ZakharovShabat.norm_weightedPotentialSquareInShift_linear`

Conjugation realizes exactly the printed shifted norm. Zero and negative indices and arbitrary complex pairs are included.

### S25-013: Actual two-resolvent Fourier expansion

- The double complementary inverse has the literal signed Fourier coefficient expansion, and its full weighted absolute double series is summable.

Public declarations:

- `NLS.ZakharovShabat.complementarySandwich`
- `NLS.ZakharovShabat.complementarySandwich_apply`
- `NLS.ZakharovShabat.linearWeightAbsoluteSeries`
- `NLS.ZakharovShabat.summable_and_linearWeightAbsoluteSeries_le`

The reciprocal symbols remove the excluded resonant modes. Actual infinite sources are allowed; no finite-support premise is imposed.

### S25-014: M1 weight inequality

- The exact factorization w(k)=(1+abs(k))*v(k) proves the displayed signed ratio w(k-n)<=bracket(k-n)*w(k+l)*w(-l-n)/(bracket(k+l)*bracket(l+n)).

Public declarations:

- `NLS.SpectralWeight.HasLinearFactor`
- `NLS.SpectralWeight.linear_signed_ratio`

The residual v is a normalized monotone submultiplicative spectral weight, and all three indices are arbitrary integers.

### S25-015: Weighted l1 convolution and Holder estimate

- The coefficient product on the two-dimensional lattice has squared sum exactly equal to the product of squared Hilbert norms. Cauchy-Schwarz gives absolute summability and the scalar bound 4/(1+abs(n)).

Public declarations:

- `NLS.ZakharovShabat.summable_convolution_coeff_product_sq`
- `NLS.ZakharovShabat.tsum_convolution_coeff_product_sq`
- `NLS.ZakharovShabat.summable_and_linearWeightKernel_pairing_le`
- `NLS.ZakharovShabat.summable_and_linearWeightAbsoluteSeries_le`

The proof uses the actual complementary denominators and exact shifted component norms.

### S25-016: Two explicit summation constants

- Replace the two printed auxiliary summation estimates by the verified bound for the actual denominator kernel: its squared double sum is at most 16/(1+abs(n))^2. Its square root supplies the required constant four.

Public declarations:

- `NLS.ZakharovShabat.resonantStrip_denominator_lower_pi`
- `NLS.ZakharovShabat.norm_complementarySymbol_sq_le`
- `NLS.ZakharovShabat.tsum_linearWeightKernel_sq_le`
- `NLS.ZakharovShabat.summable_and_linearWeightKernel_pairing_le`

This positive estimate keeps the pi/2 denominator gain. It does not assert separate proofs of the printed constants 32/5 and 5/2, and adds no refutation of them.

### S25-017: Component estimates and squared operator bound

- Both signed scalar components satisfy the constant-four estimate. Multiplication by the actual potential gives the squared operator estimate with constant 16 and hence Lemma 25.2.

Public declarations:

- `NLS.ZakharovShabat.shiftedNorm_complementarySandwich_linear`
- `NLS.ZakharovShabat.shiftedPairNorm_weightedPotentialInverse_sq_linear`
- `NLS.ZakharovShabat.norm_weightedPotentialSquareInShift_linear`

The actual Hilbert pair norm combines the two component energies. The alternate positive kernel estimate changes no final constant.

### S25-018: One-half contraction, inverse and Q solution

- At the exact threshold the squared operator is a one-half contraction. The convergent even Neumann inverse gives a unique Q solution and the displayed identity Phi(v)=T_hat*T_n*Phi(u).

Public declarations:

- `NLS.ZakharovShabat.sourceM1_square_contraction`
- `NLS.ZakharovShabat.weightedEvenCorrection_hasSum`
- `NLS.ZakharovShabat.weightedCorrection_formula`
- `NLS.ZakharovShabat.weightedQSolution_equation`
- `NLS.ZakharovShabat.weightedQSolution_unique`
- `NLS.ZakharovShabat.weightedQSolution_potential_source`

Both inverse orders and the original derivative domain are retained, including equality at the threshold.

### S25-019: Reduced matrix with equal diagonal coefficients

- The reduced matrix has the displayed common diagonal and b-plus in its upper-right entry in the source basis order. Its determinant vanishes exactly for an actual weighted eigenvector.

Public declarations:

- `NLS.ZakharovShabat.weightedSourceResonantMatrix_form`
- `NLS.ZakharovShabat.weightedSourceResonantMatrix_det`
- `NLS.ZakharovShabat.weighted_eigenvector_iff_source_resonant_det_zero`

Reversing both basis indices reconciles physical mode order and preserves the determinant. The equal diagonals are proved for the actual inverse.

### S25-020: Formula (5.7) literal diagonal and off-diagonal inverse series

- Formula (5.7) gives both diagonal representations and both Fourier remainders using the actual inverse (I-T_n^2)^-1. The corresponding parity series converge to those coefficients.

Public declarations:

- `NLS.ZakharovShabat.weightedResonantA_parity`
- `NLS.ZakharovShabat.weightedResonantA_parity_zero`
- `NLS.ZakharovShabat.weightedResonantBPlus_remainder`
- `NLS.ZakharovShabat.weightedResonantBMinus_remainder`
- `NLS.ZakharovShabat.weightedResonantA_hasSum`
- `NLS.ZakharovShabat.weightedResonantBPlus_remainder_hasSum`
- `NLS.ZakharovShabat.weightedResonantBMinus_remainder_hasSum`

The original first component is read at -n and the second at n after period-one normalization; physical doubled-frequency signs are explicit.

### S25-021: Joint analyticity and coefficient symmetries

- The coefficients are jointly analytic in the source and spectral parameter. Their conjugation symmetries exchange off-diagonal entries with the source reality sign and conjugate the common diagonal.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_coefficients_joint_analytic`
- `NLS.ZakharovShabat.weightedResonantA_conj`
- `NLS.ZakharovShabat.weightedResonantBPlus_conj`
- `NLS.ZakharovShabat.weightedResonantBMinus_conj`

The reality-sign premise is retained for both symmetry conclusions. Analyticity itself holds for arbitrary complex sources.

### S25-022: Lemma 25.3 diagonal and separate-component remainder bounds

- Lemma 25.3 retains diagonal constant one and off-diagonal constant eight with each remainder using its own component norm. The analytic extensions agree with the inverse-defined coefficients throughout the full closed strip.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_coefficients`
- `NLS.ZakharovShabat.sourceM1_coefficients_joint_analytic`

All M1 weights and original complex sources are included at the exact quadratic threshold; extension defaults outside the correction domain are not used.

### S25-023: Convergent inverse and first diagonal bound

- Uniform geometric error estimates justify the actual parity series on the entire strip. The corrected diagonal estimate is 2*norm(first)*norm(second)/(1+abs(n)), preserving both component norms.

Public declarations:

- `NLS.ZakharovShabat.weightedResonantA_partialSum_error`
- `NLS.ZakharovShabat.weightedResonantBPlus_partialSum_error`
- `NLS.ZakharovShabat.weightedResonantBMinus_partialSum_error`
- `NLS.ZakharovShabat.norm_weightedResonantA_le_component_product`
- `NLS.ZakharovShabat.sourceM1_diagonal_component_bound`

The exact quadratic condition supplies the half-contraction used in the geometric estimates. The positive component-product proof passed the full checks and is committed and pushed; no new refutation is added.

### S25-024: Second diagonal representation and combined constant

- Both diagonal expressions use (I-T_n^2)^-1. The positive product estimate and 2ab<=a^2+b^2 give the final total-norm bound with constant one.

Public declarations:

- `NLS.ZakharovShabat.weightedResonantA_parity`
- `NLS.ZakharovShabat.weightedResonantA_parity_zero`
- `NLS.ZakharovShabat.norm_weightedResonantA_linear`
- `NLS.ZakharovShabat.sourceM1_diagonal_component_bound`

This directly corrects the omitted inverse exponents and the intermediate component-square estimates. The statement of Lemma 25.3 keeps its final constants.

### S25-025: Off-diagonal shifted Fourier remainder

- Evaluation of the resonant coordinate gains exactly w(2*n). The square bound and even inverse give each Fourier remainder constant eight times the squared pair norm and its own component norm.

Public declarations:

- `NLS.ZakharovShabat.weighted_resonant_coordinate_le`
- `NLS.ZakharovShabat.weightedResonantBPlus_remainder_linear`
- `NLS.ZakharovShabat.weightedResonantBMinus_remainder_linear`

Both physical Fourier signs and the shifted norms are explicit; neither remainder substitutes the other component norm.

### S25-026: Lemma 25.4 exact canonical roots, multiplicities, radius and gap bound

- The actual determinant has exactly the canonical endpoint pair throughout the closed strip, with analytic order equal to the multiset count. Both roots lie in the source disc and their squared separation is at most six times the full-strip product supremum.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_canonical_pair`
- `NLS.ZakharovShabat.linearWeight_exists_resonantRoots`
- `NLS.ZakharovShabat.linearWeight_determinant_sourceDisc_zeroCount`
- `NLS.ZakharovShabat.linearWeight_determinant_root_gap_le`

The original algebraic multiplicities are retained. Coincident endpoints count twice; no analytic root branches or distinct-root premise are chosen.

### S25-027: Determinant radius from coefficient estimates

- The coefficient bounds give weighted product decay and force every determinant zero into the exact radius P^2/bracket(n)+sqrt(2)*P/bracket(2*n), strictly below pi/5.

Public declarations:

- `NLS.ZakharovShabat.linearWeight_offDiagonal_product_le`
- `NLS.ZakharovShabat.linearWeight_offDiagonal_product_bracket_le`
- `NLS.ZakharovShabat.linearWeight_determinant_root_localization`
- `NLS.ZakharovShabat.quadraticLocalizationRadius_lt_pi_div_five`

The argument applies at threshold equality and throughout the closed strip. It uses the actual coefficients and exact Hilbert norm.

### S25-028: Rouche root count and canonical enumeration

- The auxiliary function h(z)=z-n*pi-a_n(z) has exactly one simple root in the printed source disc and no other root in the strip. The determinant has total analytic multiplicity two there, identified with the original canonical endpoints.

Public declarations:

- `NLS.ZakharovShabat.linearWeight_diagonal_simple_root`
- `NLS.ZakharovShabat.linearWeight_determinant_zeroCount`
- `NLS.ZakharovShabat.linearWeight_determinant_sourceDisc_zeroCount`
- `NLS.ZakharovShabat.linearWeight_canonicalEndpointPair`
- `NLS.ZakharovShabat.sourceH1_canonical_pair`

The auxiliary root is constructed by contraction at the exact threshold. The determinant count uses a direct Rouche comparison on the pi/4 circle followed by localization to the smaller source disc. The positive simple-root proof and its public examples passed the full checks and are committed and pushed.

### S25-029: Theorem 25.1 remaining horizontal spectral box

- Use the precise Lemma 25.4 localization at the quadratic threshold to place all remaining endpoints in the stated central horizontal box.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_uniform_localization`
- `NLS.ZakharovShabat.sourceH1_spectrum_subset`
- `NLS.ZakharovShabat.H1_canonicalEndpoints_mem_centralBox`

The immediate reference is clarified from the printed Lemma 6.9 to Lemma 25.4. The complete original spectrum and canonical labels are retained.

### S25-030: Imaginary-part estimate from physical H1 norm

- The positive spectral-height proof gives abs(Im lambda)<=P in the exact original physical H1 norm for every complex source. In the displayed complex identity use 2*i*Im(lambda)=lambda-conj(lambda).

Public declarations:

- `NLS.ZakharovShabat.abs_im_le_H1_norm`
- `NLS.ZakharovShabat.sourceH1_uniform_localization`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_norm_sq`

The existing proof obtains the height bound from the actual operator and coefficient estimates. It does not require the printed intermediate identity without the factor i, and no refutation is added.

### S25-031: Transition to weighted gap estimates

- The sentence announces the use of the following weighted gap estimates in Section 28.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_gap_tail`
- `NLS.ZakharovShabat.sourceM1_gap_individual`

It introduces no additional estimate; the tail and individual statements are compared below.

### S25-032: Proposition 25.5 inclusive tail with constants 6 and 1152

- For every complex M1 source and inclusive cutoff N with 8*P^2<=1+N, the weighted squared-gap tail is summable and bounded by 6*norm(R_N source)^2+1152*P^6/(1+N).

Public declarations:

- `NLS.ZakharovShabat.sourceM1_gap_tail`
- `NLS.ZakharovShabat.norm_weightedPairFourierTail_normalizedWeightedPeriodOne`
- `NLS.ZakharovShabat.M1_canonicalGap_tail_summable_and_le`

N=0, negative indices and both boundary frequencies are included. The tail estimate needs no extra complex neighborhood assumption.

### S25-033: Common complex neighborhood and global constant 265

- One open neighborhood T of the entire real source locus is chosen before every M1 weight and source. On T, the globally summable gap squares obey 265*pi^2*w[16*P^2]^2*(1+P^2)*P^2.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.section25_gap_neighborhood`
- `NLS.ZakharovShabat.SourceSection25Data.gap_bound`
- `NLS.ZakharovShabat.SourceSection24Data.section25`
- `NLS.ZakharovShabat.sourceSection25_original`

T is the intersection of the retained original domain U with the spectral-height neighborhood, and T is contained in U. No weight-dependent or source-dependent replacement of T is made.

### S25-034: Squared gap and both Fourier remainder estimates

- The factor-six squared-gap estimate combines with both leading Fourier terms and their separate remainder bounds. The resulting positive sums retain both component energies and the squared errors.

Public declarations:

- `NLS.ZakharovShabat.M1_canonicalGap_tail_summable_and_le_parameter`
- `NLS.ZakharovShabat.sourceM1_coefficients`
- `NLS.ZakharovShabat.linearWeight_determinant_root_gap_le`

The proof handles arbitrary M1 weights, including superlinear growth, and actual canonical gaps. It does not require a linear upper bound on the weight.

### S25-035: Tail summation and exact inclusive physical cutoff

- Use the inclusive original-source tail R_N. Its period-doubled physical realization has cutoff 2*N, with equal tail norm. Summing the squared reciprocal bracket gives the final 1152 constant.

Public declarations:

- `NLS.ZakharovShabat.weightedPairFourierTail_normalizedWeightedPeriodOne`
- `NLS.ZakharovShabat.norm_weightedPairFourierTail_normalizedWeightedPeriodOne`
- `NLS.ZakharovShabat.M1_canonicalGap_tail_summable_and_le`
- `NLS.ZakharovShabat.sourceM1_gap_tail`

This keeps source and physical cutoffs distinct instead of relabeling the printed R_(2N) as the original R_N. The cutoff endpoints and N=0 are preserved.

### S25-036: Central complex gap budget and global cutoff choice

- The central complex gap budget uses horizontal packing plus bounded spectral heights. Together with the tail bound and cutoff choice it proves the printed global constant 265*pi^2 on one common neighborhood.

Public declarations:

- `NLS.ZakharovShabat.M1_canonicalGap_central_budget_of_height_one`
- `NLS.ZakharovShabat.gap_global_265_height_budget`
- `NLS.ZakharovShabat.M1_canonicalGap_global_summable_and_le_of_height_one`
- `NLS.ZakharovShabat.SourceSection24Data.section25_gap_neighborhood`

This supplies a direct positive replacement for the arbitrary-isolating-disc diameter argument. No new assertion or refutation about those disc diameters is needed.

### S25-037: Formula (5.8) individual weighted gap estimate

- At the exact quadratic threshold each weighted off-diagonal is at most twice its component norm, giving w(2*n)*norm(gap_n)<=sqrt(12)*P.

Public declarations:

- `NLS.ZakharovShabat.linearWeight_offDiagonal_le`
- `NLS.ZakharovShabat.sourceM1_gap_individual`

Every M1 weight, including superlinear ones, and every signed index is covered. The original source gap and component-sum norm are used.

## Evidence and validation

The [original Section 25 package](../NLS/ZakharovShabat/SourceSection25Original.lean)
retains the source domain and one common complex neighborhood. The
[localization API](../NLS/ZakharovShabat/SourceSection25Localization.lean)
keeps original physical norms, canonical labels and multiplicities. The
[component-product estimate](../NLS/ZakharovShabat/SourceSection25DiagonalProduct.lean),
[orthogonality proof](../NLS/ZakharovShabat/SourceSection25OrthogonalSplit.lean) and
[simple diagonal root](../NLS/ZakharovShabat/SourceSection25DiagonalRoot.lean)
supply the positive intermediate statements used in this comparison.

This comparison read 54 complete module bodies and resolves 99 public declarations.
It reconciles the earlier named comparison and both positive proof steps.
Reading every transitive dependency again is not claimed. The historical
refutations are unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit b99e74d3669fa2d4bdc76e76be15ef2729fb1349: 8,578 build jobs, 7,684 public examples and a transitive axiom audit of 44,695 NLS declarations, with 21 inherited warnings and zero new. All 99 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered comparison for Section 26. The
[broader completion qualifications](COMPLETENESS.md) remain.
