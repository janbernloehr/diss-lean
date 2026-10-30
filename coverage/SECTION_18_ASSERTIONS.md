# Section 18 ordered assertion comparison

All 39 ordered Section 18 passage groups are classified: 28 matched, five corrected, one partial external-edition comparison and five contextual groups. The original Hamiltonian and frequency retain a common connected action domain, actual physical recovery, Taylor remainders, inverse and Fredholm conclusions, sign and local concavity. The corrected full Hessian is 4-2 delta_nm, H* includes both mass-square and weighted linear subtractions, and the gauge is exp(4 i mass t). The isolated S1 denotes H1. The action-image assertion uses an open source neighborhood inside the original complex domain. Wellposedness retains finite source exponents, the all-smooth-approximation solution class and compact-time uniform norms. The exact cited 2014 construction comparison remains qualified in S18-003. Literature attributions and the then-open question are historical, not independently verified results or claims about current research status. No new Lean code or refutation is added. Wider dissertation qualifications remain unresolved.

Source: printed pp. 83–87, text lines 6643–6974. Line numbers count newline characters,
preserving form-feed characters. All five rendered pages were inspected. The overview
continues onto p. 87 before the actual Section 19 heading.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S18-001 | 6643–6653 | Hamiltonian integral and complex NLS system (4.1). | matched |
| S18-002 | 6655–6659 | Real-type scalar dNLS equation (4.2). | matched |
| S18-003 | 6662–6670 | Sobolev canonical analytic Birkhoff diffeomorphism and weighted actions. | partial |
| S18-004 | 6671–6678 | Full Hamiltonian analyticity, action dependence and Taylor expansion. | matched |
| S18-005 | 6680–6682 | Full Hamiltonian origin derivatives with the mass correction. | corrected |
| S18-006 | 6684–6687 | Frequency Taylor expansion (4.3). | matched |
| S18-007 | 6697–6699 | Rectangular Birkhoff equations and rotation signs. | matched |
| S18-008 | 6701–6707 | Renormalized nonlinear frequency normalization. | matched |
| S18-009 | 6710–6715 | Hamiltonian H* including the weighted linear subtraction. | matched |
| S18-010 | 6717–6722 | Renormalized frequency expansion at zero. | matched |
| S18-011 | 6725–6735 | Original action-image domain and analytic neighborhood. | corrected |
| S18-012 | 6737–6756 | Theorem 18.1: one frequency, all target exponents and mixed remainder. | matched |
| S18-013 | 6759–6763 | Motivation for applications to perturbations. | contextual |
| S18-014 | 6765–6767 | Corollary 18.2(i): local analytic inverse at zero. | matched |
| S18-015 | 6769–6769 | Corollary 18.2(ii): compact derivative correction. | matched |
| S18-016 | 6771–6771 | Corollary 18.2(iii): Fredholm index zero. | matched |
| S18-017 | 6773–6773 | Corollary 18.2(iv): generic local analytic inverse. | matched |
| S18-018 | 6776–6785 | Corrected H* definition and local concavity claim. | corrected |
| S18-019 | 6796–6797 | Theorem 18.3(i): FL4 extension, sign and zero set. | matched |
| S18-020 | 6799–6811 | Theorem 18.3(ii): action extension, sign and local Hessian bound. | matched |
| S18-021 | 6814–6819 | Remark 18.4: no C1 extension above action exponent two. | matched |
| S18-022 | 6822–6830 | Global Sobolev solutions and analytic trajectory map (4.4). | matched |
| S18-023 | 6831–6838 | Ordinary frequency obstruction and renormalized frequency. | corrected |
| S18-024 | 6841–6851 | Renormalized Hamiltonian and Wick-ordered PDE (4.5). | matched |
| S18-025 | 6853–6856 | Conserved mass and corrected gauge conversion. | corrected |
| S18-026 | 6858–6863 | Analytic Sobolev trajectories and local higher-exponent extension. | matched |
| S18-027 | 6873–6879 | Original all-smooth-approximation solution definition. | matched |
| S18-028 | 6882–6883 | Uniqueness in the stated solution class. | matched |
| S18-029 | 6885–6894 | Definition of local analytic wellposedness. | matched |
| S18-030 | 6896–6905 | Definition of global analytic wellposedness. | matched |
| S18-031 | 6908–6909 | Transition to Fourier Lebesgue applications. | contextual |
| S18-032 | 6911–6912 | Theorem 18.5(i): global wellposedness for 1<p<=2. | matched |
| S18-033 | 6914–6915 | Theorem 18.5(ii): local wellposedness for 2<p<infinity. | matched |
| S18-034 | 6917–6919 | Theorem 18.5(iii): small-data global wellposedness above two. | matched |
| S18-035 | 6921–6926 | Theorem 18.5(iv): ordinary solution-map nonextension. | matched |
| S18-036 | 6929–6938 | Historical related wellposedness and weak-continuity results. | contextual |
| S18-037 | 6948–6953 | Historical announcements, open question and probabilistic results. | contextual |
| S18-038 | 6954–6965 | Historical Fourier Lebesgue existence and uniqueness classes. | contextual |
| S18-039 | 6966–6974 | Contributions: analyticity, small global solutions and original-class uniqueness. | matched |

## Compared passages

### S18-001: Hamiltonian integral and complex NLS system (4.1).

- The period-one H1 energy equals the literal integral of the kinetic and quartic terms. On smooth periodic complex pairs, its two directional derivatives are integration against the actual variational gradients.
- The cross-component Hamiltonian field is (-i times the second gradient, +i times the first gradient), giving the matrix convention in (4.1).

Public declarations:

- `NLS.ZakharovShabat.periodOneSobolevHamiltonian_eq_integral`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_three`
- `NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_three_fst`
- `NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian_three_snd`
- `NLS.ZakharovShabat.classicalNLSVectorField`

The integral energy is defined on H1; pointwise Hamiltonian PDE identities use smooth periodic fields. No pointwise derivative is asserted for arbitrary L2 data.

### S18-002: Real-type scalar dNLS equation (4.2).

- The Hamiltonian field preserves the conjugate-pair real form. Multiplication of its first component by i gives -u_xx + 2|u|^2 u.

Public declarations:

- `NLS.ZakharovShabat.classicalNLSVectorField_real`
- `NLS.ZakharovShabat.classicalNLSVectorField_scalar`
- `NLS.ZakharovShabat.classicalNLS_equation_of_hasDerivAt`

The subsequent rough solutions use the explicit smooth-approximation definition, rather than imposing a classical PDE on distributions.

### S18-003: Sobolev canonical analytic Birkhoff diffeomorphism and weighted actions.

- The actual weighted Birkhoff map has a global real analytic inverse at every nonnegative real Sobolev order in the range 1<p<=2, hence at p=2 and every printed integer order.
- Canonical brackets retain the physical factor -i and the rectangular sign convention. Weighted spectral actions are summable at every positive integer Sobolev order; the Hilbert case supplies summable actions at order zero.

Public declarations:

- `NLS.ZakharovShabat.NativeWeightedPeriodic.sobolevHomeomorph_analytic`
- `NLS.ZakharovShabat.NativeWeightedPeriodic.birkhoff_canonical`
- `NLS.ZakharovShabat.sourceWeightedAction_summable_on_Hm`
- `NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData.real_actions_mem`

The mathematics is proved internally. Identification with the exact cited 2014 construction [23] remains qualified as in S17-007; inspecting the earlier 2013 manuscript does not close that external comparison.

### S18-004: Full Hamiltonian analyticity, action dependence and Taylor expansion.

- The physical energy is analytic on the full complex H1 pair space and is recovered by the same action-only Hamiltonian on every real H1 source.
- In the standard weighted ell^(2,1) action norm, H equals the weighted linear sum plus 2(sum I)^2 minus sum I_n^2, with one uniform cubic remainder bound near zero.

Public declarations:

- `NLS.ZakharovShabat.analyticAt_periodOneSobolevHamiltonian`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_real_full_action_analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_physical_identity`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_expansion_bound`

The bound includes complex infinite-support inputs in one ball. The attribution to [51] is historical; this comparison checks the internal expansion, not that external proof.

### S18-005: Full Hamiltonian origin derivatives with the mass correction.

- At zero the full energy frequency is (2 pi n)^2. Restoring the mass term gives the full Hessian 4-2 delta_nm.
- The Hessian -2 delta_nm belongs to H*, whose gradient is the renormalized nonlinear frequency.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_coordinate_derivative`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.map_zero`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.restored_frequency_derivative`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.hessian_zero`

Use the positive corrected derivative formula directly. Historical refutation proofs are unchanged and no new one is added.

### S18-006: Frequency Taylor expansion (4.3).

- Literal coordinate derivatives of the full Hamiltonian equal dispersion + 4 sum I - 2 I_n + R_n.
- A single Hilbert remainder sequence satisfies ||R||<=C||I||^2 in the standard weighted action norm, with radius and constant chosen before the action and spectral index.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_frequency_expansion_bound`

This is the uniform sequence form of (4.3), retaining the corrected full-Hessian mass term.

### S18-007: Rectangular Birkhoff equations and rotation signs.

- Every global ordinary solution in the original approximation class has rectangular coordinates satisfying xdot_n=-omega_n y_n and ydot_n=omega_n x_n.
- These frequencies remain constant along that same solution.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.ordinary_original_rectangular_oscillators`
- `NLS.ZakharovShabat.SourceSection20Data.ordinary_original_frequency_conserved`

The source overview is in the Hilbert/Sobolev range, contained in the proved 1<p<=2 range. The physical Hamiltonian time orientation is used.

### S18-008: Renormalized nonlinear frequency normalization.

- The full action derivative restores exactly 4 times total action and the free dispersion to the same retained frequency F.
- On actual real finite-gap potentials, the original action map recovers the independently constructed physical frequency with those terms subtracted.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.standard_full_action_coordinate_derivative`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.physical_finiteGap`
- `NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData.physical_finiteGap`

The finite-gap physical normalization and the action-space derivative identity have their separate stated domains.

### S18-009: Hamiltonian H* including the weighted linear subtraction.

- H* equals physical H minus 2 mass squared minus the literal absolutely convergent weighted action series on every real H1 source.
- On the common connected action domain, the retained original frequency is exactly the gradient of this same H*.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.physical_identity`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.gradient_eq`

Both subtractions are retained. H-2mass^2 alone is the renormalized PDE Hamiltonian Hr.

### S18-010: Renormalized frequency expansion at zero.

- The same frequency vanishes at zero, has derivative -2Id, and has a quadratic remainder in the full action norm.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.map_zero`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.derivative_zero`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.action_quadratic_remainder_bound`

For every finite p>2 the action exponent is p/2; the neighborhood and bound are uniform over all coordinates.

### S18-011: Original action-image domain and analytic neighborhood.

- The action domain is open and connected, contains all original real-source actions and the entire nonnegative summable cone, and is an actual action image.
- More precisely U is the image of an open source neighborhood Y containing the real locus with Y contained in the original complex domain V.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.exists_connected_action_image`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.source_image`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.positive_actions_mem`

The justified image statement uses a restricted source neighborhood. It does not identify U with the image of the entire previously chosen V. The stronger target realizations below imply the prior weaker weighted-frequency regularity.

### S18-012: Theorem 18.1: one frequency, all target exponents and mixed remainder.

- One original Hilbert frequency has real and complex analytic realizations into every ell^r target with r>1, including infinity, on the same action domain.
- For each finite p>2 an original family gives one analytic F on ell^(p/2) extending those nonnegative summable-action values. Its correction F+2I has one locally uniform ell^(p/3)+ell^(1+) decomposition chosen before all projection exponents.

Public declarations:

- `NLS.ZakharovShabat.sourceSection18_original_frequencies`
- `NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData.realizations_all`
- `NLS.ZakharovShabat.SourceOriginalHilbertFrequencyData.memℓp_all`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.eq_hilbert_on_positive`
- `NLS.ZakharovShabat.SourceSection17OriginalData.exists_frequency_asymptotic`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.refined`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.mixed`
- `NLS.ZakharovShabat.exists_sourceFrequency_actionSpace_asymptotic`

The literal p/3 component is retained when it is below one. Infinity is a frequency target, not an extension to all bounded action inputs. The domain has the restriction stated in S18-011.

### S18-013: Motivation for applications to perturbations.

- The passage motivates perturbative applications of the following frequency inverse results.

Possible applications are not a separate mathematical theorem or a proved perturbation result.

### S18-014: Corollary 18.2(i): local analytic inverse at zero.

- The same frequency is a bijection between actual open neighborhoods of zero with an analytic inverse throughout its image. Its inverse derivative at zero is -1/2 Id.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.local_open_inverse`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.local_inverse`

The source neighborhood lies in the original action domain; global injectivity of the frequency is not asserted.

### S18-015: Corollary 18.2(ii): compact derivative correction.

- At every complex action in the same domain, dF+2Id is compact, by factoring the refined derivative through a stronger Banach sequence space and applying Pitt compactness.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.compact_derivative`

A finite exponent strictly between one and p/2 and at least p/3 is selected; no Banach structure is imposed on ell^(p/3) below one.

### S18-016: Corollary 18.2(iii): Fredholm index zero.

- Every derivative is Fredholm with equal finite kernel and cokernel dimensions, giving index zero.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.fredholm`

This is a statement throughout the original connected action domain, for each finite p>2.

### S18-017: Corollary 18.2(iv): generic local analytic inverse.

- There is one open subset dense in the original domain where every point has an analytic inverse branch between open sets, with the inverse derivative equal to the inverse Jacobian.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalFrequencyData.generic_open_inverse`
- `NLS.ZakharovShabat.SourceOriginalFrequencyData.generic_local_inverse`

Analytic Fredholm density uses connectedness and invertibility at zero. Inverse neighborhoods may depend on the point.

### S18-018: Corrected H* definition and local concavity claim.

- The H* preceding Theorem 18.3 includes the weighted linear action subtraction, as in the earlier displayed definition.
- The same Hamiltonian has an analytic FL4 extension and strict concavity on one neighborhood of zero in the real Hilbert action space.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.physical_identity`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.source_extension`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.strict_concavity`

The conjecture attribution is historical. The internal theorem proves local concavity; it does not assert global concavity on the entire positive Hilbert cone.

### S18-019: Theorem 18.3(i): FL4 extension, sign and zero set.

- The actual original H* is analytic on an open complex FL4 neighborhood containing the full real locus. On real sources it is real, nonpositive, and zero exactly at the zero source.

Public declarations:

- `NLS.ZakharovShabat.sourceSection18_original_hamiltonian`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.source_extension`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.source_sign`

The constructor retains the same original family, action frequency and physical H1 identity.

### S18-020: Theorem 18.3(ii): action extension, sign and local Hessian bound.

- One open connected Hilbert action domain carries the same analytic Hamiltonian, with nonpositive real values and zero only at zero on its nonnegative part.
- The Hessian at zero is -2 times the bilinear Hilbert pairing. On one positive-radius ball it obeys Re d2H*(J,J)<=-||J||^2 for every real Hilbert direction.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.analytic`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.sign`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.hessian_zero`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.concavity`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.strict_jensen`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.positive_domain`

The positive domain is relatively open and dense; it is not replaced by the whole nonnegative Hilbert cone. Closed-gap boundary points are included in the local strict Jensen conclusion.

### S18-021: Remark 18.4: no C1 extension above action exponent two.

- The same H* has no continuous, hence no C1, extension near zero relative to the nonnegative ell^q cone for any q>2, including infinity.
- The proof integrates the local Hessian bound and uses finite nonnegative blocks; the infinity endpoint follows by coefficient-preserving inclusion.

Public declarations:

- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.quadratic_bound`
- `NLS.ZakharovShabat.SourceOriginalHamiltonianData.no_continuous_extension_all`

This proves the source nonextension assertion by a stronger continuity obstruction. It is not an additional refutation of a printed constant.

### S18-022: Global Sobolev solutions and analytic trajectory map (4.4).

- Constructed ordinary and renormalized global solutions have real analytic trajectory maps in the uniform Sobolev norm on each compact time interval, for every real regularity s>=0.
- At p=2 this gives the Sobolev assertion (4.4). Uniqueness holds in the stated original all-smooth-approximation class.

Public declarations:

- `NLS.ZakharovShabat.exists_original_sobolev_analytic_solutions`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.exists_analytic_sobolevHamiltonianTrajectories`

The attribution to [7] is historical and is not an external proof comparison. Analyticity is in the initial datum with values in the trajectory space; no analyticity in time or uniqueness among arbitrary distributional solutions is inferred.

### S18-023: Ordinary frequency obstruction and renormalized frequency.

- The renormalized PDE frequency is the ordinary frequency minus four times the physical mass H1, equivalently dispersion plus omega*.
- The announced ordinary-flow continuity obstruction is proved for the actual smooth solution map in S18-035.

Public declarations:

- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.ordinaryPhaseFrequency_complex`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.phaseFrequency_complex`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all_symmetric`

Read the isolated S1 in this display as the mass H1, consistent with the preceding expansion and the following Hamiltonian. This is a notation correction; no new refutation is added.

### S18-024: Renormalized Hamiltonian and Wick-ordered PDE (4.5).

- The literal renormalized energy is H-2H1^2. Both variational gradients include the factor four in the mass term.
- Its real-type Hamiltonian field gives -v_xx+2|v|^2v-4(integral |v|^2)v, and the constructed smooth trajectories satisfy that actual Hamiltonian equation.

Public declarations:

- `NLS.ZakharovShabat.classicalRenormalizedNLSEnergy`
- `NLS.ZakharovShabat.hasDerivAt_classicalRenormalizedNLSEnergy_fst`
- `NLS.ZakharovShabat.hasDerivAt_classicalRenormalizedNLSEnergy_snd`
- `NLS.ZakharovShabat.classicalRenormalizedNLSVectorField_scalar`
- `NLS.ZakharovShabat.SmoothNLSData.renormalized_hamiltonian_equation`

Hr retains dispersion; H* subtracts it. The classical differential equation and the rough approximation solution class are distinguished.

### S18-025: Conserved mass and corrected gauge conversion.

- The positive gauge phase is exp(4 i mass t), where mass is the squared L2 norm. The inverse phase recovers the ordinary solution.
- Physical mass conservation and the gauge identity hold for the actual full source flows in 1<p<=2, hence for the Sobolev solutions.

Public declarations:

- `NLS.ZakharovShabat.SmoothNLSData.renormalized_phase`
- `NLS.ZakharovShabat.IsClassicalRenormalizedNLSTrajectory.ungauge`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.hamiltonianOrdinarySourceFlow_mass`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.hamiltonianRenormalizedSourceFlow_gauge`

The factor four and the square are retained directly. Historical constant-datum witnesses are unchanged.

### S18-026: Analytic Sobolev trajectories and local higher-exponent extension.

- Both Sobolev trajectory maps are analytic for every compact time interval. At higher finite source exponents the renormalized map has a local analytic extension at every datum.

Public declarations:

- `NLS.ZakharovShabat.exists_original_sobolev_analytic_solutions`
- `NLS.ZakharovShabat.renormalizedNLS_locallyAnalyticallyWellposed_of_two_le`

The extension sentence is interpreted with the immediately following local definition and Theorem 18.5(ii). It does not supply a global map on all higher-exponent sources for every prescribed time horizon.

### S18-027: Original all-smooth-approximation solution definition.

- A solution is continuous on its time domain, starts at the prescribed datum, and is the pointwise source-norm limit of the actual classical trajectories for every convergent sequence of smooth initial data.
- The smooth classical trajectories are constructed and satisfy the renormalized PDE with their own initial mass.

Public declarations:

- `NLS.ZakharovShabat.IsSmoothApproximationSolutionOn`
- `NLS.ZakharovShabat.IsRenormalizedNLSSolutionOn`
- `NLS.ZakharovShabat.SmoothNLSData.renormalized_isClassical`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.renormalizedImageFlow_isSolution`

The general domain formulation requires zero in the domain and includes the printed open intervals and compact intervals used for wellposedness. Convergence is quantified over all smooth approximations.

### S18-028: Uniqueness in the stated solution class.

- Smooth density and uniqueness of limits imply that two solutions with the same initial datum agree on the intersection of their time domains.

Public declarations:

- `NLS.ZakharovShabat.IsSmoothApproximationSolutionOn.eqOn_inter`
- `NLS.ZakharovShabat.SourceSection18WellposednessData.unique`

Uniqueness is precisely in the original approximation solution class.

### S18-029: Definition of local analytic wellposedness.

- Local analytic wellposedness supplies a single positive time and an open neighborhood for each datum, solutions for every datum in that neighborhood, and a real analytic map into continuous trajectories with the uniform norm.

Public declarations:

- `NLS.ZakharovShabat.IsLocallyAnalyticallyWellposed`

The neighborhood and time are chosen before the neighboring datum, exactly as required by (a) and (b).

### S18-030: Definition of global analytic wellposedness.

- Global analytic wellposedness on an open initial-data set supplies one trajectory for all real times for each datum, with analytic compact-time restriction maps for every positive horizon.

Public declarations:

- `NLS.ZakharovShabat.IsGloballyAnalyticallyWellposedOn`

The underlying global trajectories are chosen before the time horizon, as required by (a prime) and (b prime).

### S18-031: Transition to Fourier Lebesgue applications.

- The passage introduces the Fourier Lebesgue applications of the preceding frequency theorem.

This transition adds no mathematical hypothesis or separate result.

### S18-032: Theorem 18.5(i): global wellposedness for 1<p<=2.

- Renormalized NLS is globally real analytically wellposed on the whole source space for every finite 1<p<=2, in the original solution sense.

Public declarations:

- `NLS.ZakharovShabat.source_theorem18_5`
- `NLS.ZakharovShabat.SourceSection18WellposednessData.global`
- `NLS.ZakharovShabat.renormalizedNLS_globallyAnalyticallyWellposed`

The spectral families and smooth solution construction are internal to the theorem; they are not additional premises.

### S18-033: Theorem 18.5(ii): local wellposedness for 2<p<infinity.

- For every finite p>2, renormalized NLS is locally real analytically wellposed at every source, with analytic dependence in the complete compact trajectory norm.

Public declarations:

- `NLS.ZakharovShabat.SourceSection18WellposednessData.local_wellposed`
- `NLS.ZakharovShabat.renormalizedNLS_locallyAnalyticallyWellposed`

The general implementation also covers finite 1<p<=2; the printed higher-exponent range is included.

### S18-034: Theorem 18.5(iii): small-data global wellposedness above two.

- For every finite p>2 there is an open neighborhood of zero containing a positive source-norm ball where renormalized NLS is globally real analytically wellposed.

Public declarations:

- `NLS.ZakharovShabat.SourceSection18WellposednessData.small_global`
- `NLS.ZakharovShabat.exists_small_global_analytic_renormalizedNLSSolutions`

The neighborhood is constructed from the invariant coordinate-image region, and the same trajectories exist for all real times.

### S18-035: Theorem 18.5(iv): ordinary solution-map nonextension.

- At every FLp source outside L2 with finite p>2, no map agreeing with all actual smooth ordinary solutions can be continuous into compact-time FLq trajectories.
- The original package covers finite q>=p; the retained-family theorem includes infinity and even every q>=1.

Public declarations:

- `NLS.ZakharovShabat.SourceSection18WellposednessData.ordinary_nonextension`
- `NLS.ZakharovShabat.smoothClassicalNLS_theorem18_5_iv`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all_symmetric`

The input exponent remains finite. Agreement is with constructed physical classical solutions, not arbitrary coordinate rotations.

### S18-036: Historical related wellposedness and weak-continuity results.

- The passage surveys historical weak discontinuity, renormalized weak continuity, nonuniform continuity and real-line mapping results attributed to other authors.

These cited external results are recorded as historical context, not claimed as formalized or independently checked by this ordered review. The survey continues on page 87.

### S18-037: Historical announcements, open question and probabilistic results.

- The continuation records an announcement, real-line weak-solution bounds, a then-open torus question and probabilistic wellposedness results.

Open status and literature priority are reported only as statements in the 2016 dissertation, not as current research status. No independent external-source comparison is claimed.

### S18-038: Historical Fourier Lebesgue existence and uniqueness classes.

- The passage compares earlier Fourier Lebesgue constructions, continuity, solution methods and their distinct uniqueness classes.

These are historical attributions. The internal uniqueness theorem below uses the dissertation approximation class and does not subsume every external solution notion.

### S18-039: Contributions: analyticity, small global solutions and original-class uniqueness.

- The implemented conclusions supply analytic initial-data dependence, small-data global solutions and uniqueness in the original all-smooth-approximation class.
- The phase characterization uses the actual original coordinates; the ordinary solution map fails continuity at every higher-exponent source outside L2.

Public declarations:

- `NLS.ZakharovShabat.source_theorem18_5`
- `NLS.ZakharovShabat.sourceSection22_original`
- `NLS.ZakharovShabat.IsSmoothApproximationSolutionOn.eqOn_inter`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all_symmetric`

The sentence about one continuous solution is read in the solution sense defined on page 86 and characterized in Remark 22.3. It is not a claim of uniqueness among arbitrary distributional solutions; novelty is contextual.

## Evidence and validation

The [original frequency package](../NLS/ZakharovShabat/SourceFrequencyOriginalAsymptotic.lean)
and [original Hamiltonian package](../NLS/ZakharovShabat/SourceHamiltonianOriginal.lean)
retain their actual domains and spectral recovery. The
[Hamiltonian expansion](../NLS/ZakharovShabat/SourceHamiltonianActionTaylor.lean),
[frequency expansion](../NLS/ZakharovShabat/SourceFrequencyActionTaylor.lean),
[Sobolev trajectories](../NLS/ZakharovShabat/SourceSobolevAnalyticSolutions.lean) and
[wellposedness package](../NLS/ZakharovShabat/SourceSection18Wellposedness.lean)
give the uniform remainders and original solution meaning used above.

This comparison inspected 52 full module bodies and four positive formula/proof excerpts,
and resolves 91 declarations. It does not claim a fresh semantic reading of every
transitive dependency. The existing full axiom audit covers that dependency graph.
Historical refutation modules are unchanged; no new refutation was added.

This documentation-only step reuses the successful full check from commit c8cbe87 on the exact unchanged Lean and dependency-lock snapshot: 8,559 build jobs, 7,635 public examples and the transitive axiom audit of 44,604 NLS declarations, with 21 inherited warnings and no new warnings. No new full build is claimed. Current source hashes, declaration references, review integrity and local documentation links are checked separately. These integrity checks do not certify mathematical completeness.

Next: Section 19, The abelian integral F.
