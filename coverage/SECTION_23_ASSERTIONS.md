# Section 23 ordered assertion comparison

The ordered Section 23 comparison covers 38 groups on printed pp. 103–106: 33 matched, three corrected and two contextual, with no partial or pending groups in this local ledger. It retains the original family, literal physical and coordinate norms, the factor-two action identity, potential-independent common constants, full real weighted neighborhoods, the native real analytic Sobolev inverse and positive-integer one-smoothing scope. Actual Hamiltonian derivatives give the printed rectangular oscillator signs. The endpoint asymptotics include both integer tails and closed gaps. The constant label b_m is corrected directly to d_m, the weight estimate keeps the M1 hypothesis and its corrected geometric bound, and the higher-action trace uses all integer indices with positive factor 1/4^m. The printed narrower Abel strip is a valid forward statement; the exact characterization retains half-width a/pi. The informal norm-comparison chain is contextual motivation for the precise estimates with lower-order terms. Existing corrections and refutations are preserved. No new Lean proof or refutation is added in this documentation step. The exact 2014 construction, Appendix G.2 and wider dissertation-completeness qualifications remain.

Source: printed pp. 103–106, text lines 8402–8665. Line numbers count newline
characters and preserve form feeds. All four rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S23-001 | 8404–8406 | Transition from low to high regularity | contextual |
| S23-002 | 8406–8409 | Original canonical bi-analytic Sobolev diffeomorphism | matched |
| S23-003 | 8409–8411 | Analytic transformed Hamiltonian depending only on actions | matched |
| S23-004 | 8411–8414 | Real coordinate Hamilton equations and frequency derivative | matched |
| S23-005 | 8416–8417 | Derivative at zero is the Fourier transform | matched |
| S23-006 | 8417–8422 | Exact Parseval identity and higher-order norm motivation | matched |
| S23-007 | 8423–8432 | Physical Fourier indexing and literal Sobolev source norm | matched |
| S23-008 | 8434–8443 | Literal component-sum target norm | matched |
| S23-009 | 8454–8460 | Theorem 23.1 upper Birkhoff norm estimate | matched |
| S23-010 | 8464–8470 | Theorem 23.1 inverse norm estimate | matched |
| S23-011 | 8473–8474 | Constants independent of the source; b_m label | corrected |
| S23-012 | 8475–8482 | Highest-order linearity and uniform one-smoothing assertion | matched |
| S23-013 | 8483–8487 | Action definition and weighted action norm relation | matched |
| S23-014 | 8489–8496 | Theorem 23.2 upper action estimate | matched |
| S23-015 | 8501–8503 | Theorem 23.2 lower action estimate | matched |
| S23-016 | 8506–8506 | Remark 23.3 common constants | matched |
| S23-017 | 8509–8517 | Weight class M and its four exact axioms | matched |
| S23-018 | 8517–8524 | Weighted source space and norm | matched |
| S23-019 | 8527–8536 | Weighted real target and even-frequency weight | matched |
| S23-020 | 8539–8539 | Real-order Sobolev weight | matched |
| S23-021 | 8541–8552 | Abel weight and holomorphic strip with norm traces | matched |
| S23-022 | 8554–8558 | Gevrey weights | matched |
| S23-023 | 8560–8565 | Logarithmic weights and strict growth hierarchy | matched |
| S23-024 | 8566–8569 | Exact linear-factor subclass M1 | matched |
| S23-025 | 8571–8572 | Piecewise linear positive extension to the real line | matched |
| S23-026 | 8574–8581 | Theorem 23.4 complex neighborhood and weighted action estimate | matched |
| S23-027 | 8583–8587 | Theorem 23.4 target membership and map estimate | matched |
| S23-028 | 8590–8595 | Exponential growth bound and stated weight scope | corrected |
| S23-029 | 8597–8601 | Corollary 23.5 complex real-order action estimate | matched |
| S23-030 | 8605–8607 | Corollary 23.5 real target membership and norm estimate | matched |
| S23-031 | 8610–8612 | Higher actions and equality with ordinary actions at level one | matched |
| S23-032 | 8612–8617 | Higher-action asymptotic comparisons | matched |
| S23-033 | 8619–8623 | Higher-action trace indices and normalization | corrected |
| S23-034 | 8633–8636 | Physical first and third Hamiltonians | matched |
| S23-035 | 8638–8643 | General higher Hamiltonian leading term and derivative order | matched |
| S23-036 | 8643–8649 | Norm comparison outline and meaning of asymptotic notation | contextual |
| S23-037 | 8651–8659 | Spectral localization threshold and finite low-mode error | matched |
| S23-038 | 8660–8662 | Weighted gap-to-action proof outline | matched |

## Compared passages

### S23-001: Transition from low to high regularity

- The overview changes emphasis from low to high regularity. The original Section 20 family extends to the Section 23 estimates without choosing new moments, roots or Birkhoff maps.

Public declarations:

- `NLS.ZakharovShabat.sourceSection23_original_estimates`

This is an introductory transition. It adds no separate quantitative assertion.

### S23-002: Original canonical bi-analytic Sobolev diffeomorphism

- The retained original map induces an onto native real Sobolev homeomorphism with globally real analytic forward and inverse maps at every nonnegative real order. Its full weighted derivatives satisfy the canonical identities.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.originalWeightedRealSobolevHomeomorph`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.originalWeightedRealSobolevHomeomorph_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.originalWeightedRealSobolevHomeomorph_symm_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.originalWeightedBirkhoff_canonical`

The Hilbert instance gives the printed Sobolev scale, including order zero. The physical bracket convention is {x_n,y_k}=-delta_nk. The precise qualification about the 2014 construction remains in the completeness record.

### S23-003: Analytic transformed Hamiltonian depending only on actions

- The transformed Hamiltonian is a real analytic function of the actual actions. Its native weighted action domain is open and contains the entire nonnegative cone. It agrees with the physical H1 Hamiltonian for every real H1 source. The standard weighted action presentation has the same values.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.full_action_analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.full_action_domain`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.real_full_action_analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.real_full_action_values`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.full_action_physical_identity`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_real_full_action_analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_physical_identity`

The full Hamiltonian includes its kinetic and mass terms. It is not merely the renormalized correction. The native Sobolev inverse in S23-002 retains the original coordinate interpretation.

### S23-004: Real coordinate Hamilton equations and frequency derivative

- Along each original ordinary flow, the real coordinates satisfy x_dot=-omega*y and y_dot=omega*x. The actual ordinary frequency is the literal coordinate derivative of the full action Hamiltonian and is conserved along the flow.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.ordinary_original_rectangular_oscillators`
- `NLS.ZakharovShabat.SourceSection20Data.ordinary_original_frequency_conserved`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.full_action_coordinate_derivative`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.full_action_frequency_ordinary`

The printed rectangular signs are correct. They agree with z=(x-i*y)/sqrt(2) and the negative first complex phase; no sign correction is made to this display.

### S23-005: Derivative at zero is the Fourier transform

- The full derivative of the original physical Birkhoff map at zero is the physical Fourier transform. Both rectangular coordinate derivatives are given by the corresponding physical Fourier integrals.

Public declarations:

- `NLS.ZakharovShabat.SourceSection14OriginalData.physicalBirkhoffMap_hasFDerivAt_zero`
- `NLS.ZakharovShabat.SourceSection14OriginalData.physicalBirkhoffMap_fderiv_zero`
- `NLS.ZakharovShabat.intrinsicPhysicalBirkhoffMap_fderiv_zero_coordinates`

This is a derivative of the original map on its full physical space, not only a finite-coordinate restriction.

### S23-006: Exact Parseval identity and higher-order norm motivation

- Parseval holds exactly on the real Hilbert source with the literal component-sum source and target norms. The following higher-order estimates use the same original map.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_parseval`
- `NLS.ZakharovShabat.sourceSection23_original_estimates`

The discussion of higher-order analogues is motivation; the exact quantitative statements are S23-009 through S23-016.

### S23-007: Physical Fourier indexing and literal Sobolev source norm

- The physical source norm is the sum of both Fourier-component energies with weight (1+|2*n*pi|)^(2*s). For integer order m, sourcePiSobolevCoordinates gives the exact norm at every lower integer order k<=m. The weighted physical norm identity also retains real orders through piSobolev.

Public declarations:

- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_fst`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_snd`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_norm_sq`
- `NLS.ZakharovShabat.normalizedWeightedSource_physical_norm`

The source uses the negative Fourier wave for its first component. Reflection of its raw coefficient label preserves the norm because the weight is even; no missing component or period factor is suppressed.

### S23-008: Literal component-sum target norm

- The target norm is the square root of the sum of the weighted squared x and y coordinates, with the literal 2*n*pi frequency. The order-zero target norm is the source Hilbert norm.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.sobolevCoordinates_fst`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.sobolevCoordinates_snd`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.sobolevCoordinates_norm_sq`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.sobolevCoordinates_zero_norm`

The norm is the component-sum Hilbert norm, not the maximum of the two scalar norms.

### S23-009: Theorem 23.1 upper Birkhoff norm estimate

- For each integer m>=1 there is a positive c_m, chosen before the source, bounding the target Hm norm by c_m times the source Hm norm plus (1+the source H1 norm)^(2*m) times its H0 norm.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.birkhoff_upper`

The original map, exact source norm and printed exponent 2*m are retained.

### S23-010: Theorem 23.1 inverse norm estimate

- For each integer m>=1 there is a positive d_m bounding the source Hm norm by d_m times the target hm norm plus (1+the target h1 norm)^(4*m-3) times its h0 norm.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.birkhoff_lower`

The endpoint m=1 is included. All three coordinate norms belong to the same original map.

### S23-011: Constants independent of the source; b_m label

- The two positive constants are selected after m and before every potential. The prose label b_m is normalized directly to d_m, matching Theorem 23.1.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.c_pos`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.d_pos`

Only this constant label is corrected. No proof that the printed label is wrong is added.

### S23-012: Highest-order linearity and uniform one-smoothing assertion

- At m>=2 the leading Hm/hm terms appear linearly while the other terms use lower norms. Separately, the actual original forward and inverse Fourier remainders gain one derivative, are real analytic on the native real spaces, and are bounded on every norm ball.

Public declarations:

- `NLS.ZakharovShabat.SourceSection23SobolevBounds.birkhoff_upper`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.birkhoff_lower`
- `NLS.ZakharovShabat.SourceSection23Data.oneSmoothing`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeForwardFourierRemainder_literal_coordinates`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeInverseFourierRemainder_literal_coordinates`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeForwardFourierRemainder_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeInverseFourierRemainder_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeForwardFourierRemainder_uniform_ball`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.nativeInverseFourierRemainder_uniform_ball`

One-smoothing is supported by its own positive theorems, not inferred from the norm estimates alone. Its scope here is positive integer order, with no order-zero or fractional smoothing endpoint asserted.

### S23-013: Action definition and weighted action norm relation

- The original indexed actions agree with the retained complex action functions on the original domain. On the real form, each action is (x_n^2+y_n^2)/2. The exact squared coordinate norm is twice the weighted action sum.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.indexed_action_eq_complex`
- `NLS.ZakharovShabat.sourceIndexedWeightedActionTerm_eq`
- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_norm_sq`
- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_weighted_norm_sq`

The factor two is retained throughout the conversion of action estimates to coordinate estimates. The final lower-order action factor is the unweighted action sum.

### S23-014: Theorem 23.2 upper action estimate

- For each m>=1 the actual weighted indexed actions are summable, and their sum is bounded by c_m^2 times the source Hm norm squared plus (1+the H1 norm)^(4*m) times the H0 norm squared.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.action_summable`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.action_upper`
- `NLS.ZakharovShabat.exists_sourceWeightedAction_sobolev_upper_bound`

The positive proof controls the actual physical Hamiltonian and its lower-order terms. Constants are independent of the source.

### S23-015: Theorem 23.2 lower action estimate

- The source Hm norm squared is bounded by d_m^2 times the weighted order-2m action sum plus (1+the order-2 action sum)^(4*m-3) times the unweighted action sum.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.action_lower`
- `NLS.ZakharovShabat.exists_sourceSobolev_weightedAction_lower_bound`

Both m=1 and every higher integer order are included. The last factor is not replaced by a stronger weighted action norm.

### S23-016: Remark 23.3 common constants

- One common positive pair c_m,d_m simultaneously satisfies all four Birkhoff and action estimates. The pair is selected before the potential.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_sobolev_joint_bounds`
- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_sobolev_bounds`

The constants may depend on m. No single constant uniform in all Sobolev orders is asserted.

### S23-017: Weight class M and its four exact axioms

- The weight class has exactly the four displayed properties: values at least one, evenness, submultiplicativity and monotonicity in the nonnegative index.

Public declarations:

- `NLS.SpectralWeight`
- `NLS.SpectralWeight.apply_neg`
- `NLS.SpectralWeight.mono_abs`
- `NLS.SpectralWeight.constant`

The printed word normalized does not impose w(0)=1. Constant weights above one are allowed.

### S23-018: Weighted source space and norm

- The normalized weighted source describes exactly the original weighted Fourier range. Its norm is the literal component-sum weighted physical energy. The real locus is preserved.

Public declarations:

- `NLS.ZakharovShabat.normalizedWeightedSource_physical_norm`
- `NLS.ZakharovShabat.mem_range_originalWeightedSourceCLM_iff`
- `NLS.ZakharovShabat.range_originalWeightedSourceCLM_eq_normalized`

Period-one sources occupy the even Fourier labels, so the actual scalar summands use w(2*n). This is the source convention behind the printed sum over physical labels m.

### S23-019: Weighted real target and even-frequency weight

- The weighted real target consists of the original coordinates with finite sum of w(2*n)^2 times x_n^2+y_n^2. On the M1 source range this sum is twice the actual weighted action sum.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_weighted_norm_sq`
- `NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood`

The even-frequency weight is literal. The target norm uses both real components.

### S23-020: Real-order Sobolev weight

- For every real s>=0 the weight is exactly (1+|n*pi|)^s and its weighted physical source is the usual period-one Sobolev space with the displayed norm.

Public declarations:

- `NLS.SpectralWeight.piSobolev`
- `NLS.SpectralWeight.piSobolev_apply`
- `NLS.ZakharovShabat.normalizedWeightedSource_physical_norm`

Noninteger orders are retained; the pi factor is not absorbed into an unspecified equivalent norm.

### S23-021: Abel weight and holomorphic strip with norm traces

- The Abel weight is (1+|n*pi|)^s*exp(a*|n|), with s>=0 and a>0. Every source in that weighted space has the stated holomorphic extension to the printed narrower strip and Sobolev-norm boundary traces.

Public declarations:

- `NLS.SpectralWeight.abel_apply`
- `NLS.ZakharovShabat.source_abel_printed_strip_forward`
- `NLS.ZakharovShabat.source_abel_range_iff_physical_strip_extensions`
- `NLS.Fourier.hasSobolevNormStripTraces_iff_physical`

The printed forward implication is valid. Under the even physical labels, the exact characterization has half-width a/pi; a/(2*pi) is only a narrower forward strip. Norm-continuous physical traces, not merely pointwise or almost-everywhere boundary values, are retained. The earlier converse correction remains unchanged.

### S23-022: Gevrey weights

- The Gevrey weight is (1+|n|)^s*exp(a*|n|^sigma) and belongs to M for the printed s>=0, a>0 and 0<sigma<1. For s>=1 its linear factor gives membership in M1.

Public declarations:

- `NLS.SpectralWeight.gevrey`
- `NLS.SpectralWeight.gevrey_apply`
- `NLS.SpectralWeight.hasLinearFactor_gevrey`

This family uses the unscaled polynomial bracket, as printed. Its membership in M does not require s>=1.

### S23-023: Logarithmic weights and strict growth hierarchy

- The logarithmic weight has the exact denominator 1+(log(1+|n|))^sigma. It lies strictly between the Gevrey and Abel growth scales: the relevant weight ratios tend to zero, allowing independent polynomial orders and positive exponential parameters. These comparisons induce bounded injective coefficient inclusions preserving the coefficients.

Public declarations:

- `NLS.SpectralWeight.logarithmic`
- `NLS.SpectralWeight.logarithmic_apply`
- `NLS.SpectralWeight.gevrey_div_logarithmic_tendsto_zero`
- `NLS.SpectralWeight.logarithmic_div_abel_tendsto_zero`
- `NLS.SpectralWeight.exists_coefficient_inclusion_of_ratio_tendsto_zero`

The direction of weighted-space inclusion reverses the weight-growth ordering. The claims retain the printed open interval for sigma.

### S23-024: Exact linear-factor subclass M1

- M1 means exactly w(n)=(1+|n|)*v(n) for some v in M. The Sobolev, Abel, Gevrey and logarithmic families have this property for their stated order-at-least-one instances.

Public declarations:

- `NLS.SpectralWeight.HasLinearFactor`
- `NLS.SpectralWeight.withLinearFactor_apply`
- `NLS.SpectralWeight.hasLinearFactor_piSobolev`
- `NLS.SpectralWeight.hasLinearFactor_abel`
- `NLS.SpectralWeight.hasLinearFactor_gevrey`
- `NLS.SpectralWeight.hasLinearFactor_logarithmic`

A general lower linear bound alone is not substituted for the required factorization.

### S23-025: Piecewise linear positive extension to the real line

- The extension agrees with every integer value, is even and strictly positive, and is affine on each unit interval.

Public declarations:

- `NLS.SpectralWeight.realExtension_affine`
- `NLS.SpectralWeight.realExtension_intCast`
- `NLS.SpectralWeight.realExtension_neg`
- `NLS.SpectralWeight.realExtension_pos`

This is the literal piecewise linear interpolation w[t], not a floor-step extension.

### S23-026: Theorem 23.4 complex neighborhood and weighted action estimate

- For each M1 weight there is one open complex weighted neighborhood containing the whole real weighted locus. Its decoded sources stay inside the original source domain. The actual absolute weighted action sum is summable and is bounded by 2048^2*w[16*norm^2]^2*norm^2.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood`
- `NLS.ZakharovShabat.exists_sourceM1Action_neighborhood`
- `NLS.ZakharovShabat.exists_zero_sourceM1Action_bound`

The constant is chosen before the source, and the zero potential is included without dividing by its norm. A single neighborhood contains all real sources; it is not just a neighborhood of one selected potential.

### S23-027: Theorem 23.4 target membership and map estimate

- The restriction of the same original Birkhoff map has values in the weighted real target and norm at most 2048*w[16*norm^2]*norm. The same constant 2048 supplies the action-square bound.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood`
- `NLS.ZakharovShabat.SourceSection17OriginalData.section23_weighted_norm_sq`

The action estimate on the complex neighborhood and the coordinate estimate on the entire real weighted locus have the distinct scopes printed in the theorem.

### S23-028: Exponential growth bound and stated weight scope

- The general positive growth bound is w(n)<=w(0)*w(1)^|n|, so the growth is at most exponential. The claimed estimates retain the theorem assumption w in M1, including its exponentially growing examples.

Public declarations:

- `NLS.SpectralWeight.le_geometric`
- `NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood`

Correct the displayed geometric bound directly and retain the M1 restriction in the following prose. No normalization w(0)=1 or extension of Theorem 23.4 to every M weight is introduced. No new refutation is added.

### S23-029: Corollary 23.5 complex real-order action estimate

- For each real r>=1 an open complex neighborhood contains the full real Hr locus, lies in the retained original domain after decoding, and satisfies the actual absolute action estimate with exponent 4*r. The positive constant is 2048*(1+17*pi)^r.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.section23_realSobolev_neighborhood`
- `NLS.ZakharovShabat.realSobolevEstimateConstant_pos`

The real order is unrestricted above one; it is not rounded to an integer. The action weight is exactly (1+|2*n*pi|)^(2*r).

### S23-030: Corollary 23.5 real target membership and norm estimate

- The same original map sends the real Hr source to the real hr target with norm bounded by c_r*(1+source_norm)^(2*r)*source_norm, using the same positive c_r as in the action estimate.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.section23_realSobolev_neighborhood`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.realSobolevCoordinates_norm_le`

Membership in the actual target and the printed exponent 2*r are both retained.

### S23-031: Higher actions and equality with ordinary actions at level one

- The higher actions use the original spectral primitive and contours. Spectral power zero is exactly the original ordinary indexed action.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_zero`
- `NLS.ZakharovShabat.SourceSection24Data.higherAction_eq_original_primitive`

The Lean spectral power k corresponds to printed action level k+1. Thus printed odd level 2*m+1 uses power 2*m.

### S23-032: Higher-action asymptotic comparisons

- The higher action is asymptotic to either original periodic endpoint raised to the spectral power times the original action, and to (n*pi)^k times that action. More generally any sample in the original periodic segment gives the same asymptotic.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic_leftEndpoint`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic_rightEndpoint`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic_gapSample`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic`

The cofinite integer filter includes both signed tails. All natural powers and finite p>1 are allowed, including the printed m=0 case. Closed gaps are included without dividing by the action. The positive endpoint step has passed its full checks and is committed and pushed.

### S23-033: Higher-action trace indices and normalization

- The corrected trace sums the original higher actions over every integer index and equals H_(2*m+1)/4^m for each m>=1. The Hamiltonian is the independently defined physical Sobolev Hamiltonian. The original complex Hm preimage and analytic extension are retained.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.odd_trace`
- `NLS.ZakharovShabat.SourceSection24Data.trace_printed_level`
- `NLS.ZakharovShabat.SourceSection19Data.indexedHigherAction_oddHamiltonian_trace`

Use the full integer sum and the positive factor 1/4^m, with no alternating sign. The printed level/power conversion is explicit. Existing correction and refutation records are preserved without new refutations.

### S23-034: Physical first and third Hamiltonians

- The first physical Hamiltonian is the period-one mass integral. The third is the kinetic-plus-quartic energy integral, and the sharp odd-Hamiltonian extension agrees with this H3.

Public declarations:

- `NLS.ZakharovShabat.sobolevNLSHamiltonian_one`
- `NLS.ZakharovShabat.sobolevNLSHamiltonian_one_eq_periodOneSobolevMass`
- `NLS.ZakharovShabat.periodOneSobolevMass_re_eq_integral_norm_sq`
- `NLS.ZakharovShabat.periodOneSobolevHamiltonian_eq_integral`
- `NLS.ZakharovShabat.periodOneSobolevQuartic_re_eq_integral_norm_four`
- `NLS.ZakharovShabat.sourceSection27_H3_bridge`

On the real form the second physical component is the complex conjugate of the first. The scalar mass integral is retained, with its factor relative to the two-component source norm handled explicitly.

### S23-035: General higher Hamiltonian leading term and derivative order

- For every m>=1 one polynomial, chosen before the source, uses jets of order at most m-1. The physical H_(2*m+1) is the squared L2 norm of the mth derivative plus the integral of that lower-jet polynomial. Its entire complex Hm extension agrees with the classical expression on smooth fields.

Public declarations:

- `NLS.ZakharovShabat.exists_classicalNLSHamiltonian_odd_real_reduced_polynomial`
- `NLS.ZakharovShabat.nlsOddReducedPolynomial_order`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_real_decomposition`
- `NLS.ZakharovShabat.analyticAt_sobolevOddHamiltonian`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_eq_classical`

The polynomial is independently constructed on physical derivatives. It is not defined by subtracting an action sum or allowed to depend on the individual potential.

### S23-036: Norm comparison outline and meaning of asymptotic notation

- The displayed chain of informal norm comparisons motivates replacing a formal leading-term comparison by the quantitative two-sided estimates with lower-order terms. Those precise estimates are retained above.

Public declarations:

- `NLS.ZakharovShabat.sobolevOddHamiltonian_real_decomposition`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.action_upper`
- `NLS.ZakharovShabat.SourceSection23SobolevBounds.action_lower`

The display supplies no limiting parameter for its asymptotic notation. No additional global equivalence or limit theorem is claimed from it; the explicit bounds are the mathematical conclusion.

### S23-037: Spectral localization threshold and finite low-mode error

- The actual complex H1 norm determines a uniform quadratic spectral threshold. Above it, both canonical periodic endpoints lie within the quantified free-lattice disks and the real higher actions have explicit comparisons. The finitely many remaining indices satisfy central estimates with an H1 error. These support the quantitative action estimates.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_uniform_localization`
- `NLS.ZakharovShabat.sourceSection26_exterior`
- `NLS.ZakharovShabat.sourceSection26_central`
- `NLS.ZakharovShabat.sourceSection26_meanValue_complex`
- `NLS.ZakharovShabat.SourceSection26Data.action_estimate`
- `NLS.ZakharovShabat.exists_sourceSection26_remainder_bounds`

The exact threshold is 8*P^2<=1+|n|; high-mode comparisons retain n!=0 and the central estimate includes n=0. The sentence about avoiding auxiliary spectral quantities describes a proof method, not a separate Lean theorem or a claim that every transitive dependency was reread.

### S23-038: Weighted gap-to-action proof outline

- A uniform local bound controls each actual action by a constant times the actual squared gap, including collapsed gaps. The weighted gap estimate gives a summable majorant and a quantitative action budget. The resulting complex neighborhood estimate is the original Theorem 23.4 statement.

Public declarations:

- `NLS.ZakharovShabat.exists_local_sourceAction_gap_bound`
- `NLS.ZakharovShabat.sourceComplexAction_le_gap_sq_of_normalized_bound`
- `NLS.ZakharovShabat.sourceM1_complex_actions_summable_and_le`
- `NLS.ZakharovShabat.SourceSection25Data.gap_bound`
- `NLS.ZakharovShabat.SourceSection20Data.section23_weighted_neighborhood`

The quantitative theorem retains the M1 assumption. The zero source and the rest of the real locus are both included. This comparison verifies the stated mathematical ingredients, not a claim about avoiding auxiliary quantities in every proof dependency.

## Evidence and validation

The [original Section 23 package](../NLS/ZakharovShabat/SourceSection23Original.lean)
retains the original source, moments, roots and Birkhoff map. The
[positive endpoint comparisons](../NLS/ZakharovShabat/SourceIndexedHigherActionEndpointAsymptotic.lean)
supply the literal first asymptotic in the outline. The
[original Section 24 package](../NLS/ZakharovShabat/SourceSection24Original.lean)
retains the corrected trace and physical Hamiltonian meaning.

This comparison read 55 complete module bodies and resolved 117 public
declarations. It reconciles the four earlier named comparisons, the separately
indexed Remark 23.3 and the positive endpoint comparison. Reading every
transitive proof dependency again is not claimed. Historical correction and
refutation records are unchanged; only the direct label and scope clarification
is appended to the errata. No new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit 187a774df4feadf6559c1a25f240e5ccfd1a4cfe: 8,572 build jobs, 7,672 public examples and a transitive axiom audit of 44,674 NLS declarations, with 21 inherited warnings and zero new. All 117 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered assertion comparison for Section 24.
