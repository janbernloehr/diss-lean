# Section 26 ordered assertion comparison

The ordered Section 26 comparison covers 28 groups on printed pp. 112–115: 20 matched and eight directly corrected, with no partial or pending groups in this local ledger. The original indexed actions, closed-gap mean-value points, signed indices, exact physical norms, threshold equality and all permitted orders are retained. The actual finite polynomial support, conjugate jets, unit-interval integrals, interpolation exponents and arbitrary-epsilon Young absorption are compared. Direct corrections use the positive Hamiltonian sign, natural polynomial multiplicities, the strict supremum derivative range, the repeated-factor index, mass exponent numerator D-2 and physical norm coefficient 2^(2m-1). The final action bound keeps its literal leading 2^m with a remainder constant chosen before all real Hm sources. Existing refutations remain unchanged; this documentation step adds no Lean proof or refutation. Broader completeness, the exact cited 2014 construction and Appendix G.2 qualifications remain.

Source: printed pp. 112–115, text lines 9221–9488. Line numbers count
newline characters and preserve form feeds. All four rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S26-001 | 9223–9224 | Quantitative action objective | matched |
| S26-002 | 9226–9230 | Proposition 26.1 mean-value identity and radius | matched |
| S26-003 | 9232–9234 | Exterior comparison | matched |
| S26-004 | 9236–9239 | Central comparison | matched |
| S26-005 | 9241–9244 | Actual gap sample and displacement | matched |
| S26-006 | 9245–9247 | Two-sided spectral point bound | matched |
| S26-007 | 9249–9249 | Central sample bound | matched |
| S26-008 | 9259–9268 | Weighted action norm and trace objective | matched |
| S26-009 | 9270–9274 | Lemma 26.2 signed Hamiltonian term | corrected |
| S26-010 | 9276–9282 | Exterior summation and trace sign | corrected |
| S26-011 | 9284–9289 | Central mass summation | matched |
| S26-012 | 9292–9297 | Real pair and physical derivative energy | matched |
| S26-013 | 9298–9301 | Physical kinetic-plus-remainder Hamiltonian | matched |
| S26-014 | 9303–9315 | Homogeneity and balanced monomial counts | matched |
| S26-015 | 9317–9320 | Multi-index constraints | corrected |
| S26-016 | 9322–9331 | Finite monomial majorant and uniform constants | matched |
| S26-017 | 9341–9350 | Lemma 26.3 uniform physical remainder and Hamiltonian bounds | matched |
| S26-018 | 9353–9362 | Field-count lower bound four | matched |
| S26-019 | 9363–9377 | Two-factor extraction and integral estimate | matched |
| S26-020 | 9381–9391 | Formula (5.11) interpolation ranges | corrected |
| S26-021 | 9392–9396 | Formula (5.12) product exponents | matched |
| S26-022 | 9398–9415 | Repeated-index factor extraction | corrected |
| S26-023 | 9416–9425 | Highest-norm exponent | matched |
| S26-024 | 9427–9432 | Mass exponent intermediate identity | corrected |
| S26-025 | 9443–9447 | Combined monomial estimate | matched |
| S26-026 | 9449–9466 | Young conjugates and exact mass power | matched |
| S26-027 | 9468–9471 | Uniform finite sum and physical norm splitting | corrected |
| S26-028 | 9473–9486 | Original Theorem 23.2(i) consequence | corrected |

## Compared passages

### S26-001: Quantitative action objective

- Quantitative higher-action control follows from the original periodic-spectrum localization, on the same real source spaces and retained original family.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_original`
- `NLS.ZakharovShabat.sourceSection26_meanValue_complex`
- `NLS.ZakharovShabat.sourceSection26_exterior`

The source purpose is supported by the actual gap and action estimates; the citation is historical attribution, not an additional mathematical premise.

### S26-002: Proposition 26.1 mean-value identity and radius

- Every real H1 source and natural m has an actual closed-gap sample zeta with the original complex equality J_(n,2m+1)=zeta^(2m)*I_n and the exact quadratic radius at 8P^2<=1+|n|.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_meanValue_complex`
- `NLS.ZakharovShabat.sourceSection26_meanValue`

P is the exact physical pair H1 norm. Signed indices, m=0, collapsed gaps and threshold equality are included. The implementation spectral-power index 2m denotes printed action level 2m+1.

### S26-003: Exterior comparison

- For nonzero signed n at the inclusive quadratic threshold, the two-sided action comparison retains 2^(-m), 4^m and the physical frequency weight (1+|2n*pi|)^(2m).

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_exterior`
- `NLS.ZakharovShabat.sourceRealHigherAction_H1_exterior_bounds`

The real parts in the inequalities equal the actual real original actions; no division by an action or gap is used.

### S26-004: Central comparison

- At the strict complementary threshold, 4^m times the norm of the original higher action is bounded by (16*pi)^(2m)*P^(4m)*I_n.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_central`
- `NLS.ZakharovShabat.sourceRealHigherAction_H1_central_bound`

Every natural m and signed n, including zero, is admitted under the stated strict threshold. Zero is also handled separately in the later summation when it does not meet this threshold.

### S26-005: Actual gap sample and displacement

- The sample lies between the canonical real endpoints, so their norm localization controls the whole closed gap. At a nonzero index the exact threshold gives radius at most 3/8, hence the printed half-unit bound.

Public declarations:

- `NLS.ZakharovShabat.sourceRealHigherAction_H1_meanValue_localization`
- `NLS.ZakharovShabat.H1_gap_point_localization`
- `NLS.ZakharovShabat.quadraticLocalizationRadius_le_three_eighths`

The nonzero integer arithmetic keeps both signs of n and includes equality at the source threshold. The stronger proved radius supplies the displayed consequence.

### S26-006: Two-sided spectral point bound

- Half-unit localization around n*pi gives the squared two-sided comparison and every even-power comparison, with the same physical bracket and factors.

Public declarations:

- `NLS.ZakharovShabat.spectral_point_sq_bounds`
- `NLS.ZakharovShabat.spectral_point_even_power_bounds`

The printed unsquared bounds are equivalent to the proved squared bounds since both sides are nonnegative; taking nonnegative square roots gives (1/sqrt(2))*<2n*pi> <= 2*|zeta| <= <2n*pi>. No spectral sign is assumed.

### S26-007: Central sample bound

- Every point between the central canonical endpoints satisfies |zeta|<=8*pi*P^2 under 1+|n|<8P^2.

Public declarations:

- `NLS.ZakharovShabat.H1_gap_point_central_bound`

This is a bound on the actual closed interval, with the exact physical H1 norm and including n=0.

### S26-008: Weighted action norm and trace objective

- The literal weighted action l1 norm is the sum of physical-weighted original action magnitudes. Summability and higher-action control lead to the original Theorem 23.2(i) upper bound.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedWeightedActionTerm`
- `NLS.ZakharovShabat.sourceIndexedWeightedActionTerm_eq`
- `NLS.ZakharovShabat.sourceWeightedAction_summable_and_le_higher_sum`
- `NLS.ZakharovShabat.exists_sourceSection26_action_leading_bound`

The weighted sum uses signed integer indices and the original indexed actions. The final exact leading-coefficient theorem passed the full checks and is committed and pushed.

### S26-009: Lemma 26.2 signed Hamiltonian term

- Lemma 26.2 has +2^m times the independently defined physical odd Hamiltonian at every m>=1. Both the printed full-mass remainder and the stronger half-mass form are proved, with absolute summability.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_action_estimate_half_mass`
- `NLS.ZakharovShabat.sourceSection26_action_estimate`
- `NLS.ZakharovShabat.sourceSection26_printed_estimate_of_odd`

Replace the alternating sign directly by the physical positive sign. At odd m the printed sign already agrees. The previous actual-source refutation is preserved unchanged and no new refutation is added.

### S26-010: Exterior summation and trace sign

- For nonzero exterior modes, the weighted action is at most 8^m times the nonnegative higher action. The summable trace identity is exactly 8^m*sum J_(n,2m+1)=+2^m*H_(2m+1).

Public declarations:

- `NLS.ZakharovShabat.sourceWeightedActionTerm_le`
- `NLS.ZakharovShabat.sourceWeightedAction_summable_and_le_higher_sum`
- `NLS.ZakharovShabat.eight_pow_mul_tsum_realHigherActions`
- `NLS.ZakharovShabat.sourceRealHigherActions_summable`

Correct the repeated alternating sign. The pointwise proof separates n=0 before applying the nonzero exterior estimate, so small source norms need no impossible negative natural cutoff. Its summable positive majorant gives the same final bound for every source, including zero.

### S26-011: Central mass summation

- The central physical weight is at most <16*pi>^(2m)*(1+P)^(4m), and the ordinary action trace contributes exactly half the squared pair mass.

Public declarations:

- `NLS.ZakharovShabat.central_action_weight_le`
- `NLS.ZakharovShabat.sourceRealActions_summable`
- `NLS.ZakharovShabat.sourceWeightedAction_summable_and_le_higher_sum`

The central bound admits n=0 or the strict complementary threshold. The stronger half-mass sum implies the displayed full-mass estimate; the finite-cutoff presentation is not needed to exclude any small-norm source.

### S26-012: Real pair and physical derivative energy

- The two real-source components are physical conjugates; their derivatives retain conjugate reflection and equal L2 norms. Unit-interval Parseval identifies the scalar top-derivative integral with its coefficient norm, and the component-sum pair energy is twice it.

Public declarations:

- `NLS.ZakharovShabat.realTypeHigherSobolevSource_coefficients`
- `NLS.ZakharovShabat.hierarchySobolevJetL2_real`
- `NLS.ZakharovShabat.integral_sq_sobolevTopJetPhysical`
- `NLS.ZakharovShabat.sobolevOddKinetic_real`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_real_norm_sq`
- `NLS.ZakharovShabat.sourceSection27_pair_jet_norm`

The highest derivative is the actual weak derivative for arbitrary Hm data. Smooth comparison agrees with classical derivatives. The new weighted real-pair equality additionally holds at every lower integer order, including zero.

### S26-013: Physical kinetic-plus-remainder Hamiltonian

- The physical odd Hamiltonian is exactly the squared top-derivative norm plus the actual lower-jet polynomial mean, with unit-interval physical integration.

Public declarations:

- `NLS.ZakharovShabat.sobolevOddHamiltonian_real_decomposition`
- `NLS.ZakharovShabat.sobolevOddKinetic_real`

The real Hm decomposition retains the independently defined physical Hamiltonian and its actual polynomial remainder.

### S26-014: Homogeneity and balanced monomial counts

- The fixed reduced polynomial has weight 2m+2 when differentiation and each field count once, and charge zero. Grouping conjugate factors gives nonnegative integer jet multiplicities, weighted degree 2m+2 and even total field count.

Public declarations:

- `NLS.ZakharovShabat.nlsOddReducedPolynomial_totalWeight`
- `NLS.ZakharovShabat.nlsOddReducedPolynomial_fieldCharge`
- `NLS.ZakharovShabat.nlsOddReducedPolynomial_multiplicity_constraints`
- `NLS.DifferentialPolynomial.monomial_prod_norm_lower_jets`

The finite support and conjugate norm equality preserve the exact physical polynomial and both constraints, at every m>=1.

### S26-015: Multi-index constraints

- Use nonnegative integer multiplicities of the actual polynomial monomials, with sum (i+1)*mu_i=2m+2 and even sum mu_i, as specified in the preceding source prose.

Public declarations:

- `NLS.DifferentialPolynomial.jetMultiplicity`
- `NLS.ZakharovShabat.nlsOddReducedPolynomial_multiplicity_constraints`

Normalize the displayed ambient notation (Z>=0/2)^m to the finite natural multi-index data actually used in the monomial proof. No unsupported half-integer factorization is claimed, and no new refutation is introduced.

### S26-016: Finite monomial majorant and uniform constants

- The norm of the actual physical polynomial is bounded pointwise and after integration by the finite sum of real monomial magnitudes times coefficient norms. Every supported coefficient is nonzero, so these constants are positive and independent of the potential.

Public declarations:

- `NLS.ZakharovShabat.norm_sobolevOddRemainderField_le`
- `NLS.ZakharovShabat.sobolevOddRemainderMajorant`
- `NLS.ZakharovShabat.integral_sobolevOddRemainderMajorant`
- `NLS.DifferentialPolynomial.norm_eval_le_real_monomials`

The actual finite support is used to collect the constrained monomials. The historical improvement over reference [59] is contextual and is not a separate priority claim.

### S26-017: Lemma 26.3 uniform physical remainder and Hamiltonian bounds

- For every m>=1 and epsilon>0 one nonnegative constant, chosen before all real Hm sources, bounds the absolute physical remainder integral and Hamiltonian norm by epsilon or 1+epsilon times top-derivative energy plus the exact L2-only remainder.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceSection26_remainder_bounds`
- `NLS.ZakharovShabat.SourceSection26RemainderBounds`
- `NLS.ZakharovShabat.exists_sobolevOddRemainder_derivative_absorption`
- `NLS.ZakharovShabat.exists_sobolevOddHamiltonian_energy_estimates`

Both conclusions share a common constant. The source polynomial, physical interval, arbitrary epsilon and exact power (1+scalarMass^(4m))*scalarMass^2 are retained, with the original U and T unchanged.

### S26-018: Field-count lower bound four

- Every actual supported monomial has field count D between 4 and 2m+2. The upper weight estimate 2m+2<=m*D and evenness rule out D<=2.

Public declarations:

- `NLS.ZakharovShabat.nlsOddReducedPolynomial_field_degree_bounds`

The proof follows the source argument for every m>=1, including m=1. The lower bound supplies two factors even when their indices coincide.

### S26-019: Two-factor extraction and integral estimate

- Two selected factors are extracted from the actual monomial; all residual factors use their supremum norms and the selected factors use physical L2 norms via Cauchy-Schwarz and Parseval.

Public declarations:

- `NLS.DifferentialPolynomial.exists_two_factor_split`
- `NLS.DifferentialPolynomial.prod_pow_two_factor_split`
- `NLS.ZakharovShabat.integral_sobolevRealMonomial_le_split`
- `NLS.ZakharovShabat.integral_lowerSobolevJet_norm_mul_le`

The general split includes distinct indices and repeated indices. Its multiplicities are nonnegative integers and its constants precede every source.

### S26-020: Formula (5.11) interpolation ranges

- Formula (5.11) holds in the exact physical Hm norm for i<m in the supremum estimate and i<=m in the L2 estimate, with explicit constants 4*(2*pi)^i and (2*pi)^i.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_supremum_interpolate`
- `NLS.ZakharovShabat.sourceSection26_L2_interpolate`
- `NLS.ZakharovShabat.norm_sobolev_le_sourcePiSobolevScalar`

Correct the supremum endpoint directly to the strict range used by the polynomial proof. The existing endpoint refutation is unchanged. No new counterexample construction is needed.

### S26-021: Formula (5.12) product exponents

- The finite product collects exactly the two interpolation powers in (5.12): two L2 factors lower the high-norm exponent by 1/m and increase the mass exponent by 1/m.

Public declarations:

- `NLS.ZakharovShabat.exists_sobolevRealMonomial_interpolation_bound`
- `NLS.DifferentialPolynomial.prod_interpolated_powers`
- `NLS.DifferentialPolynomial.two_factor_interpolation_exponents`

The proof first bounds with the auxiliary norm, which is dominated by the exact physical norm. The high-norm exponent is positive, so the same constant supplies the source display. Zero inputs are treated separately and introduce no negative-power assumption.

### S26-022: Repeated-index factor extraction

- When both selected factors have the same derivative order k, the residual multiplicity is mu_k-2 and the two L2 factors coincide. The same exact exponent calculation gives (5.12).

Public declarations:

- `NLS.DifferentialPolynomial.exists_two_factor_split`
- `NLS.DifferentialPolynomial.prod_pow_two_factor_split`
- `NLS.ZakharovShabat.integral_sobolevRealMonomial_le_split`
- `NLS.DifferentialPolynomial.two_factor_interpolation_exponents`

In the single-support display, remove the unused l from the residual product restriction; the repeated-index split provides the literal intended factorization. This is a direct notation correction.

### S26-023: Highest-norm exponent

- Writing D=sum mu_i, the high-norm exponent is alpha=2-(D-2)/(2m), with 0<alpha<2. Weighted degree and 4<=D<=2m+2 give exactly this range.

Public declarations:

- `NLS.ZakharovShabat.nlsOddReducedPolynomial_multiplicity_constraints`
- `NLS.ZakharovShabat.nlsOddReducedPolynomial_field_degree_bounds`
- `NLS.DifferentialPolynomial.two_factor_interpolation_exponents`
- `NLS.DifferentialPolynomial.monomial_interpolation_power_range`

The finite-sum identities retain arbitrary supported multiplicities and repeated selections. The alpha formula is valid at every m>=1.

### S26-024: Mass exponent intermediate identity

- The mass exponent is beta=(1+1/(2m))*(D-2)=D-2+(D-2)/(2m), matching the actual finite product of two L2 and residual supremum factors.

Public declarations:

- `NLS.DifferentialPolynomial.two_factor_interpolation_exponents`

Replace the intermediate numerator D-4 by D-2 directly. The final beta in the source is retained and is proved by the positive finite-sum identity; no refutation is added.

### S26-025: Combined monomial estimate

- Each supported physical monomial has integral at most C*mass^beta*Hm^alpha with exactly alpha=2-(D-2)/(2m) and beta=(1+1/(2m))*(D-2).

Public declarations:

- `NLS.ZakharovShabat.exists_sobolevRealMonomial_interpolation_bound`
- `NLS.ZakharovShabat.norm_sobolev_le_sourcePiSobolevScalar`
- `NLS.DifferentialPolynomial.monomial_interpolation_power_range`

The actual proof uses the stronger auxiliary Hm bound; monotonicity transfers it to the exact physical norm without changing C, since alpha>0. Constants depend on the fixed monomial and m, never on the source.

### S26-026: Young conjugates and exact mass power

- Young absorption with t=alpha/2, hence conjugates p=2/alpha and pprime=4m/(D-2), gives arbitrary epsilon times Hm squared and the exact mass power beta/(1-alpha/2)=4m+2.

Public declarations:

- `NLS.DifferentialPolynomial.monomial_interpolation_power_range`
- `NLS.exists_geometric_absorption`
- `NLS.ZakharovShabat.exists_sobolevRealMonomial_absorption`

Both conjugates are finite and greater than one because 0<alpha<2. The positive absorption theorem handles nonnegative norms including zero, and its constant is chosen before all sources.

### S26-027: Uniform finite sum and physical norm splitting

- Finite support permits summing the monomial estimates with a uniform constant. The exact physical norm splits with coefficient 2^(2m-1) into scalar mass and top-derivative energy.

Public declarations:

- `NLS.ZakharovShabat.exists_sobolevOddRemainder_Hm_absorption`
- `NLS.ZakharovShabat.sourcePiSobolevScalar_norm_sq`
- `NLS.ZakharovShabat.sourceSection26_physicalNorm_split`
- `NLS.ZakharovShabat.exists_sobolevOddRemainder_derivative_absorption`

Replace the printed 2^(m-1) directly. Rescale epsilon before the norm splitting and absorb constants into the L2-only error, preserving Lemma 26.3. The positive physical splitting passed the full checks and is committed and pushed; historical refutations are unchanged.

### S26-028: Original Theorem 23.2(i) consequence

- The final action inequality has exactly 2^m times the squared physical pair Hm norm plus c_m^2*(1+P)^(4m) times squared pair mass, for every m>=1 and every original real Hm source.

Public declarations:

- `NLS.ZakharovShabat.sourceSection26_action_estimate`
- `NLS.ZakharovShabat.sourcePiSobolevCoordinates_real_norm_sq`
- `NLS.ZakharovShabat.two_mul_highestJet_sq_le_sourcePiSobolev`
- `NLS.ZakharovShabat.exists_sourceSection26_action_leading_bound`

Correct the repeated alternating Hamiltonian sign. Epsilon=1 and the exact real-pair factor two retain the literal leading coefficient, including even orders; one nonnegative c_m is chosen before every source. The positive theorem passed the full checks and is committed and pushed.

## Evidence and validation

The [original Section 26 package](../NLS/ZakharovShabat/SourceSection26Original.lean)
retains the same original family and domains. The
[action estimates](../NLS/ZakharovShabat/SourceSection26Actions.lean),
[summed estimate](../NLS/ZakharovShabat/SourceSection26Sum.lean) and
[physical remainder](../NLS/ZakharovShabat/OddHamiltonianRemainderEstimate.lean)
supply the named conclusions. The positive
[norm splitting](../NLS/ZakharovShabat/SourceSection26PhysicalNormSplit.lean) and
[leading action bound](../NLS/ZakharovShabat/SourceSection26ActionLeading.lean)
retain the physical constants in the final displays.

This comparison read 34 complete module bodies and resolves 63 public declarations.
It reconciles the prior named comparison and the positive proof step. Reading
every transitive dependency again is not claimed. Existing refutations remain
unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit ad38fb1920ad267ac19c161ac7d941e8cc276cb9: 8,580 build jobs, 7,688 public examples and an axiom audit of 44,702 NLS declarations, with 21 inherited warnings and zero new. All 63 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered comparison for Section 27. The
[broader completion qualifications](COMPLETENESS.md) remain.
