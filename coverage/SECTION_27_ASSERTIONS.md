# Section 27 ordered assertion comparison

The ordered Section 27 comparison covers 18 groups on printed pp.115–116: 14 matched, three directly corrected and one contextual, with no partial or pending groups in this local ledger. Original indexed actions, independently defined physical Hamiltonians, exact pair norms and all real Hm sources are retained. The quarter-energy step keeps the complete mass remainder; the zero-index split is explicit; the final constant budget uses the refined H1 estimate and the existing unrestricted endpoint proof. The literal Lemma 27.2 constant is retained for every m>=1. The final derivative estimate has coefficient one on its highest action term and the unweighted final mass factor. This documentation step adds no Lean proof or refutation. Broader completeness, the exact cited 2014 construction and Appendix G.2 qualifications remain.

Source: printed pp. 115–116, text lines 9489–9631. Line numbers count
newline characters and preserve form feeds. Both rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S27-001 | 9491–9492 | Converse norm-estimate objective | matched |
| S27-002 | 9494–9499 | Formula (5.13): pair derivative energy and actual trace | matched |
| S27-003 | 9502–9508 | Central modes, fixed-mass spectral translation and H1 strategy | contextual |
| S27-004 | 9510–9513 | Lemma 27.1 kinetic action bound | matched |
| S27-005 | 9515–9519 | H3 and exact physical H1 consequences | matched |
| S27-006 | 9529–9537 | Exact cubic correction and moment positivity | matched |
| S27-007 | 9537–9544 | Physical Fourier weight and kinetic-plus-mass identity | matched |
| S27-008 | 9547–9553 | Quartic mass bound and final H1 estimate | matched |
| S27-009 | 9555–9556 | Theorem 23.2(ii) order-one branch | matched |
| S27-010 | 9558–9563 | Top-derivative trace identity for higher orders | matched |
| S27-011 | 9566–9573 | Quarter-energy absorption and mass remainder | corrected |
| S27-012 | 9575–9579 | Coefficient-one derivative estimate with unweighted final factor | matched |
| S27-013 | 9581–9581 | Transition to the auxiliary Hamiltonian estimate | matched |
| S27-014 | 9584–9591 | Lemma 27.2 exact all-order Hamiltonian estimate | matched |
| S27-015 | 9594–9600 | Exterior threshold and summed comparison | corrected |
| S27-016 | 9602–9603 | Mean-value comparison relative to the third action | matched |
| S27-017 | 9605–9612 | Central third-action budget and physical constants | matched |
| S27-018 | 9615–9621 | Third-action trace and final constant budget | corrected |

## Compared passages

### S27-001: Converse norm-estimate objective

- For every m>=1 the exact physical pair Hm norm is bounded by a constant times the highest weighted original action sum plus (1+S)^(4m-3)*M.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceSection27_sobolev_bound`
- `NLS.ZakharovShabat.sourceSection27_original`

Here M=S_0 and S=S_1 are the original signed-index action sums. The constant is chosen before every real Hm source. The retained original family and domains are unchanged.

### S27-002: Formula (5.13): pair derivative energy and actual trace

- Half the sum of both physical top-derivative energies equals 4^m times the original higher-action sum minus the actual lower-jet polynomial integral on [0,1].
- The scaled original series has the independently defined physical Hamiltonian as its HasSum value.

Public declarations:

- `NLS.ZakharovShabat.SourceSection26Data.section27_pair_top_jet_identity`
- `NLS.ZakharovShabat.SourceSection26Data.section27_top_jet_identity`
- `NLS.ZakharovShabat.SourceSection26Data.section27_hamiltonian_hasSum`
- `NLS.ZakharovShabat.sourceSection27_pair_jet_norm`

The identities include every real Hm source at m>=1. The implementation action index 2m denotes source level 2m+1; absolute convergence and the positive factor 4^m are retained.

### S27-003: Central modes, fixed-mass spectral translation and H1 strategy

- The source motivates H1 control of central modes using spectral translation at fixed L2 mass. The implementation supplies a positive plane-wave spectral translation identity and estimates the central modes through the physical H1 norm.

Public declarations:

- `NLS.ZakharovShabat.sourcePlaneWave_mem_spectrum_iff_constant`
- `NLS.ZakharovShabat.H1_gap_point_central_or_zero_bound`
- `NLS.ZakharovShabat.sourceSection27_H1_norm`

This is a strategy and attribution passage. The positive spectral identity and actual H1 estimates are linked; no new general impossibility theorem or refutation is claimed. The historical localization audit is unchanged.

### S27-004: Lemma 27.1 kinetic action bound

- For every real H1 source, H3-2*H1^2 is at most the absolutely convergent sum of (2*n*pi)^2 times the original indexed action.

Public declarations:

- `NLS.ZakharovShabat.sourceSection27_energy_action_bound`
- `NLS.ZakharovShabat.sourceSection27_kinetic_summable`
- `NLS.ZakharovShabat.sourceH1_energy_le_kinetic_actions`

Signed frequencies, all real H1 sources and the exact physical Hamiltonian and mass are retained. No auxiliary spectral hypothesis is introduced.

### S27-005: H3 and exact physical H1 consequences

- The physical Hamiltonian satisfies H3<=S+2*M^2 and the exact physical pair norm satisfies P^2/3<=S+M^2.

Public declarations:

- `NLS.ZakharovShabat.sourceSection27_H3_action_mass_bound`
- `NLS.ZakharovShabat.sourceSection27_H1_norm`
- `NLS.ZakharovShabat.sourceSection27_H3_bridge`

The m=1 sharp Hamiltonian is identified with the physical H1 Hamiltonian. The norm uses the literal bracket 1+|2*n*pi| and both components, keeping the printed factor 1/3.

### S27-006: Exact cubic correction and moment positivity

- The physical energy correction is exactly -(4/3) times the original cubic-moment sum, whose real terms are nonnegative and summable.

Public declarations:

- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.sobolevPhysicalHamiltonian_identity`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_renormalizedHamiltonian_eq_real_tsum`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.summable_real_cubic_moments`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_moment_nonneg`
- `NLS.ZakharovShabat.sourceSobolevPhysicalCorrection_nonpos`

The H1-to-FL4 inclusion preserves coefficients. Finite-gap identification and H1 continuity give the same physical identity for every real H1 source. An actual atlas is constructed; no supplied representation premise remains.

### S27-007: Physical Fourier weight and kinetic-plus-mass identity

- The discrete physical Fourier weight satisfies <2*n*pi>^2 <= (3/2)*(1+(2*n*pi)^2), including n=0 and both signs.
- The exact pair norm consequently obeys P^2/3 <= scalar mass plus scalar kinetic energy; the physical Hamiltonian splits into kinetic and quartic energy.

Public declarations:

- `NLS.ZakharovShabat.physical_H1_weight_sq_le`
- `NLS.ZakharovShabat.sourcePhysicalH1_fst_sq_le`
- `NLS.ZakharovShabat.sourcePhysicalH1_norm_sq_eq_twice_fst`
- `NLS.ZakharovShabat.sourcePhysicalH1_third_sq_le_mass_kinetic`
- `NLS.ZakharovShabat.periodOneSobolevQuartic_re_eq_integral_norm_four`

The factor two comes from conjugate real-source components. Physical unit-period integration is retained, so the displayed kinetic-plus-mass identity uses the same H3 and H1.

### S27-008: Quartic mass bound and final H1 estimate

- The physical quartic integral dominates squared mass by nonnegative variance on the unit interval. Combining this with the exact kinetic action estimate gives P^2/3<=S+M^2.

Public declarations:

- `NLS.ZakharovShabat.unit_interval_mean_sq_le`
- `NLS.ZakharovShabat.periodOneSobolevMass_re_eq_integral_norm_sq`
- `NLS.ZakharovShabat.periodOneSobolevMass_sq_le_quartic`
- `NLS.ZakharovShabat.sourceH1_kinetic_actions_add_mass_le`
- `NLS.ZakharovShabat.sourceH1_third_norm_sq_le_actions`

The scalar mass equals the original total action. The argument covers zero mass and all real H1 sources and keeps the literal coefficient 1/3.

### S27-009: Theorem 23.2(ii) order-one branch

- The m=1 branch of Theorem 23.2(ii) follows from the H1 norm bound and M<=S, with d=sqrt(3) and the unweighted last factor M.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceSobolev_weightedAction_lower_bound`
- `NLS.ZakharovShabat.sourceH1_action_mass_le_weighted`
- `NLS.ZakharovShabat.exists_sourceSection27_sobolev_bound`

The proof explicitly separates m=1 before the higher-order coercivity argument. Its constant is independent of the source and no small-action hypothesis is used.

### S27-010: Top-derivative trace identity for higher orders

- For m>=2 the half-pair derivative identity is the same original higher-action trace minus the actual physical polynomial remainder.

Public declarations:

- `NLS.ZakharovShabat.SourceSection26Data.section27_pair_top_jet_identity`
- `NLS.ZakharovShabat.SourceSection26Data.section27_hamiltonian_hasSum`

The stronger identity already holds at every m>=1. All sums and the physical interval integral have their original normalization.

### S27-011: Quarter-energy absorption and mass remainder

- Retain the complete remainder C*(1+M^(2m))*M from Lemma 26.3. With epsilon=1/4 it bounds quarter of the pair derivative energy by H_(2m+1) plus this remainder, uniformly for every m>=1.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceSection27_quarter_energy_bound`
- `NLS.ZakharovShabat.exists_sobolevOddHamiltonian_energy_estimates`
- `NLS.ZakharovShabat.sourceHigher_sum_actions_eq_scalar_mass`
- `NLS.ZakharovShabat.sourceSection27_pair_jet_norm`

This directly replaces the pure-power-only intermediate expression at 9566-9573. It retains zero and small mass without asserting that the stronger displayed remainder has been proved. The existing final theorem keeps its full scope. The positive quarter-energy theorem passed the full checks and is committed and pushed; no refutation is added.

### S27-012: Coefficient-one derivative estimate with unweighted final factor

- For m>=2, quarter of the pair top-derivative energy is at most S_m+C*(1+S)^(4m-3)*M, with coefficient one on S_m and a constant chosen before all sources.

Public declarations:

- `NLS.ZakharovShabat.exists_sobolevOddHamiltonian_three_halves_action_bound`
- `NLS.ZakharovShabat.section27_central_remainder_budget`
- `NLS.ZakharovShabat.exists_sobolev_highestJet_action_bound`
- `NLS.ZakharovShabat.exists_sourceSection27_derivative_bound`

An adjustable frequency cutoff first gives coefficient 3/2 on S_m; epsilon=1/4 and the exact pair normalization recover coefficient one. Both terms of the full mass remainder are bounded by 2*(1+S)^(4m-3)*M. This positive argument retains the final displayed conclusion, including zero mass.

### S27-013: Transition to the auxiliary Hamiltonian estimate

- The auxiliary all-order Hamiltonian bound used by the source has a public theorem for the original actions and the same retained family.

Public declarations:

- `NLS.ZakharovShabat.sourceSection27_hamiltonian_estimate_literal`
- `NLS.ZakharovShabat.SourceSection27Data.hamiltonian_estimate_literal`

This transition adds no independent mathematical premise. The final derivative bound additionally uses the proved adjustable-cutoff estimate to retain its exact coefficient and unweighted final factor.

### S27-014: Lemma 27.2 exact all-order Hamiltonian estimate

- For every m>=1 and every real Hm source, H_(2m+1)<=S_m+(64*pi)^(2m-2)*(1+S)^(4m-3)*S, with the original higher-action trace.

Public declarations:

- `NLS.ZakharovShabat.sourceSection27_hamiltonian_estimate_literal`
- `NLS.ZakharovShabat.sourceSection27_endpoint`
- `NLS.ZakharovShabat.SourceSection27Data.hamiltonian_estimate_literal`
- `NLS.ZakharovShabat.SourceSection26Data.section27_hamiltonian_hasSum`

The literal m=1 endpoint is unrestricted: no smallness, collapsed-gap or supplied-profile premise remains. At m>=2 the refined physical H1 budget gives exactly the printed 64*pi constant.

### S27-015: Exterior threshold and summed comparison

- For nonzero indices at the inclusive threshold 8*P^2<=1+|n|, the original higher action satisfies 4^m*J_(n,2m+1)<=<2*n*pi>^(2m)*I_n.
- A nonnegative summable majorant combines this exterior bound with the central third-action bound.

Public declarations:

- `NLS.ZakharovShabat.sourceRealHigherAction_H1_exterior_bounds`
- `NLS.ZakharovShabat.sourceRealHigherAction_H1_le_action_add_third`
- `NLS.ZakharovShabat.H1_gap_point_central_or_zero_bound`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_le_actions_add_H1_energy`

Make the zero-index split explicit: n=0 always uses the central-or-zero estimate, including small P. This directly corrects the cutoff presentation so that no exterior estimate is applied at zero. Threshold equality and signed nonzero indices remain included, and the summed conclusion keeps every real source.

### S27-016: Mean-value comparison relative to the third action

- The original higher action equals a power of an actual closed-gap sample times the third action, without dividing by the latter.

Public declarations:

- `NLS.ZakharovShabat.sourceRealHigherAction_eq_power_mul_even_level`
- `NLS.ZakharovShabat.sourceRealHigherAction_even_level_le`

Choose base level l=1 and exponent 2m-2 for m>=1. The positive weighted gap measure proves the mean-value identity even for closed gaps, vanishing third action, m=1 and gaps crossing the spectral origin.

### S27-017: Central third-action budget and physical constants

- Central-or-zero modes satisfy 4^m*J_(n,2m+1)<=(16*pi)^(2m-2)*(1+P^2)^(2m-2)*4*J_(n,3).
- The physical H1 norm has the stronger bound P^2<=(8/3)*(S+M^2), which supplies the margin needed for the displayed conversion to action-only constants.

Public declarations:

- `NLS.ZakharovShabat.sourceRealHigherAction_H1_central_le_third`
- `NLS.ZakharovShabat.H1_gap_point_central_or_zero_bound`
- `NLS.ZakharovShabat.physical_H1_weight_sq_le_four_thirds`
- `NLS.ZakharovShabat.sourceH1_norm_sq_le_eight_thirds_actions`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_le_actions_add_H1_energy`

The exponent is 2*(m-1), including zero at m=1. The refined bound is stronger than the source H1 corollary and therefore gives its intermediate 64*pi comparison. The exact final constant uses the separate budget below.

### S27-018: Third-action trace and final constant budget

- The full third-action trace equals H3, and Lemma 27.1 gives H3<=S+2*M^2.
- For m>=2, the refined H1 constant and 2*(8/3)^(2m-2)<=4^(2m-2) absorb the energy factor two and prove the exact final 64*pi remainder.
- At m=1 the established global cubic inequality supplies the unrestricted endpoint H3<=2*S+S^2.

Public declarations:

- `NLS.ZakharovShabat.sourceSection27_H3_bridge`
- `NLS.ZakharovShabat.sourceSection27_H3_action_mass_bound`
- `NLS.ZakharovShabat.two_mul_eight_thirds_pow_le_four_pow`
- `NLS.ZakharovShabat.lemma272_central_budget`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_le_weighted_actions`
- `NLS.ZakharovShabat.SourcePrimitivePowerAtlas.real_action_sq_le_cubic`
- `NLS.ZakharovShabat.sourceH1_energy_le_quadratic_budget`
- `NLS.ZakharovShabat.sourceH1_energy_le_lemma272`
- `NLS.ZakharovShabat.sourceSection27_endpoint`

The final constant calculation is supplied by these positive bounds instead of dropping the factor two. The endpoint uses the already proved actual finite-gap profile, continuity and density; it imposes no additional condition on the source. Historical arithmetic refutations remain unchanged and no new refutation or root-selection scratch is added.

## Evidence and validation

The [original Section 27 package](../NLS/ZakharovShabat/SourceSection27Original.lean)
retains the physical trace and original family. The
[action estimates](../NLS/ZakharovShabat/SourceSection27Actions.lean) and
[unrestricted endpoint](../NLS/ZakharovShabat/SourceSection27SharpEndpoint.lean)
supply the literal named conclusions. The positive
[quarter-energy bound](../NLS/ZakharovShabat/SourceSection27QuarterEnergy.lean)
retains the complete mass remainder. The
[derivative bound](../NLS/ZakharovShabat/SourceSection27DerivativeBound.lean)
keeps the exact final coefficient and unweighted mass factor.

This comparison read 31 complete module bodies and resolves 55 public declarations.
It reconciles the prior named comparison and the positive proof step. Reading
every transitive dependency again is not claimed. Existing refutations remain
unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit 053f761701e1f096332b713a8c0d951b54d3e705: 8,581 build jobs, 7,690 public examples and an axiom audit of 44,704 NLS declarations, with 21 inherited warnings and zero new. All 55 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered comparison for Section 28. The
[broader completion qualifications](COMPLETENESS.md) remain.
