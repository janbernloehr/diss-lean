# Section 17 ordered assertion comparison

All 31 ordered Section 17 passage groups are classified: 21 matched, eight corrected, one partial external-edition comparison and one contextual attribution. The actual original map is a local analytic diffeomorphism and globally injective for every finite p>1. Surjectivity, the global analytic inverse and complete isospectral images retain 1<p<=2. The Hilbert inverse is proved internally. The exact cited 2014 construction remains unverified in S17-007; this is not an unproved Hilbert-inverse premise. Corrected swapped canonical labels, selected enumeration indices, factor two, the 2N+1 cutoff and inward angle-flow signs are retained directly. The original theta flow is unique and C1 on its full pre-collapse interval, with continuous displacement in every finite exponent above one. Existing proofs supply the results; no Lean code or new refutation is added. Earlier source qualifications and the wider dissertation inventory remain unresolved.

Source: printed pp. 78–81, text lines 6353–6624. Line numbers count newline characters,
preserving form-feed characters. All four rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S17-001 | 6355–6355 | Connection to the remaining properties of Theorem 14.1. | matched |
| S17-002 | 6358–6364 | Proposition 17.1: local diffeomorphism at every finite exponent above one. | matched |
| S17-003 | 6367–6369 | Normalized Jacobian equivalence and compact-perturbation Fredholm step. | matched |
| S17-004 | 6370–6374 | Canonical images with consistent swapped x/y labels. | corrected |
| S17-005 | 6377–6384 | Dense modes and Jacobian invertibility, with the correct dual interpretation. | corrected |
| S17-006 | 6388–6394 | Proposition 17.2: global injectivity. | matched |
| S17-007 | 6397–6399 | The Hilbert base case and the cited external construction. | partial |
| S17-008 | 6400–6405 | Local inverse branches and Hilbert collision reduction. | matched |
| S17-009 | 6409–6415 | Proposition 17.3: surjectivity for 1<p<=2. | matched |
| S17-010 | 6418–6425 | Hilbert preimage and stronger-exponent membership goal. | matched |
| S17-011 | 6435–6447 | Origin inverse chart and the small target ball (3.6). | matched |
| S17-012 | 6450–6452 | Finite reduction strategy and source-space displacements. | matched |
| S17-013 | 6453–6467 | Original angle gradients, stronger-space Hamiltonian and (3.7). | matched |
| S17-014 | 6470–6477 | Actual finite reductions with the selected index m_n. | corrected |
| S17-015 | 6480–6487 | Selected action decreases while other actions are preserved. | matched |
| S17-016 | 6489–6492 | Untouched enumeration tail with the correct m_k index. | corrected |
| S17-017 | 6494–6508 | Corrected coordinate-power sum constant and action budget. | corrected |
| S17-018 | 6519–6527 | Summable action tails and the 2N+1 enumeration cutoff. | corrected |
| S17-019 | 6529–6535 | Small target estimate and identification of the reduced source (3.8). | corrected |
| S17-020 | 6536–6539 | Finite displacement recovers original p-membership. | matched |
| S17-021 | 6541–6542 | Attribution of the flow method to reference [36]. | contextual |
| S17-022 | 6544–6552 | Lemma 17.4: unique C1 flow and displacement in every finite exponent. | matched |
| S17-023 | 6554–6557 | Hilbert canonical map and the original angle differential. | matched |
| S17-024 | 6558–6560 | Equation (3.9) with inward signs in both components. | corrected |
| S17-025 | 6561–6569 | Full pre-collapse time interval, uniqueness and selected-action limit. | matched |
| S17-026 | 6571–6579 | Bochner integration in the stronger space gives continuous displacement. | matched |
| S17-027 | 6580–6590 | Original periodic isospectral sets and action tori. | matched |
| S17-028 | 6592–6594 | Compactness of the target torus for every finite exponent. | matched |
| S17-029 | 6604–6612 | Lemma 17.5: equality and compactness below two, inclusion above two. | matched |
| S17-030 | 6614–6617 | Equal periodic spectral data give equal discriminants and actions. | matched |
| S17-031 | 6618–6624 | Hilbert action rotations and transfer of torus equality below two. | matched |

## Compared passages

### S17-001: Connection to the remaining properties of Theorem 14.1.

- The original-family package supplies the remaining local inverse, injectivity and stated surjectivity properties. Its constructor proves the package fields from the actual preceding source construction.

Public declarations:

- `NLS.ZakharovShabat.sourceSection17_original`
- `NLS.ZakharovShabat.SourceSection17OriginalData.global_inverse`

The same normalized family and compatible Chapter 3 domain are retained. Global injectivity holds for every finite p>1; surjectivity is asserted only for p<=2.

### S17-002: Proposition 17.1: local diffeomorphism at every finite exponent above one.

- At every real source and every finite p>1 the actual real derivative is a bounded linear equivalence. The inverse function theorem gives an analytic local inverse with both inverse identities and the exact strict derivative of the inverse.
- The complex extension also has both local inverse identities near each real source.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.proposition17_1`
- `NLS.ZakharovShabat.SourceSection17OriginalData.complex_localInverse`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_jacobian_bijective_all_exponents`

No invertibility premise is supplied by the caller. The complex local result concerns neighborhoods of real sources, not every complex point of the full construction domain.

### S17-003: Normalized Jacobian equivalence and compact-perturbation Fredholm step.

- Composition with the exact bounded Fourier inverse identifies invertibility of the actual Jacobian with invertibility of its normalization. The normalized operator is identity plus compact.
- The compact spectral decomposition gives the needed Banach-space alternatives: dense range implies bijectivity, and injectivity implies bijectivity. This supplies the role of the printed index-zero Fredholm argument.

Public declarations:

- `NLS.ZakharovShabat.sourceBirkhoffNormalizedJacobian_bijective_iff`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_normalizedJacobian_sub_id`
- `NLS.CompactSpectrum.bijective_of_denseRange_compact_sub_id`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_bijective_all_exponents`

The implementation does not require a Hilbert adjoint on a general p-source space. The actual compact-perturbation alternatives retain the full finite exponent range.

### S17-004: Canonical images with consistent swapped x/y labels.

- For p>=2, the actual x Hamiltonian maps to a positive y output mode, and the y Hamiltonian maps to a negative x output mode.
- After exact Fourier normalization these become A K b_x=-d_y and A K b_y=-d_x, with the reflected index -m. Both labels are swapped consistently.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.jacobian_hamiltonian_coordinates`
- `NLS.ZakharovShabat.SourceSection16OriginalData.normalizedJacobian_hamiltonian_coordinates`

The unswapped printed labels are corrected directly. Hamiltonian source directions here require p>=2; the separate inclusion argument handles smaller exponents. Existing historical refutations are unchanged.

### S17-005: Dense modes and Jacobian invertibility, with the correct dual interpretation.

- The pairing argument must use the same swapped labels as the corrected canonical images. The proof instead gives actual source preimages for both output modes, then places every finite output truncation in the Jacobian range.
- For p>=2 truncation convergence gives dense range and hence bijectivity. For p<2 compatibility transports a kernel vector to the Hilbert Jacobian; its injectivity and injective coefficient inclusion kill the vector. The compact-perturbation alternative gives surjectivity.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_single_preimages`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_truncate_mem_range`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_denseRange`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_exponent`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_injective_of_le_two`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_bijective_all_exponents`

The following printed pairing display is not certified merely because it uses an opposite label. The correction is consistent in both displays, and a Holder-conjugate cotangent is not treated as an arbitrary source vector below two.

### S17-006: Proposition 17.2: global injectivity.

- The actual real map is injective throughout every finite p>1 source space. The local-homeomorphism result then makes it an open embedding.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_2`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_isOpenEmbedding`
- `NLS.ZakharovShabat.sourceSection17_original`

The constructed original package has no supplied global-injectivity premise.

### S17-007: The Hilbert base case and the cited external construction.

- The Hilbert map is internally proved globally bijective: the action-mass identity bounds sources, coefficient compactness and actual action continuity prove properness, and the trace identity gives a singleton zero fiber.
- A closed local homeomorphism with a singleton fiber over the connected target is bijective. Its inverse agrees locally with the analytic inverses.
- This proves the mathematical Hilbert base case used by the section. Equality with the exact construction in the cited 2014 edition of [23], Theorem 19.3, remains unverified.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_proper`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_eq_zero_iff`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_bijective`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertRealHomeomorph_symm_analytic`
- `NLS.FunctionalAnalysis.bijective_of_closed_localHomeomorph_singleton_fiber`

Partial denotes the retained external-edition comparison only. The internal Hilbert inverse is a proved theorem, not an assumption.

### S17-008: Local inverse branches and Hilbert collision reduction.

- Two distinct preimages of a common output give local inverse branches. One sufficiently large finite truncation of that output lies in both inverse neighborhoods and has distinct preimages in independently prescribed source neighborhoods.
- Finite output support means finitely many open spectral gaps. The finite-gap Sobolev bootstrap supplies coefficient-preserving Hilbert realizations, and exponent compatibility gives an actual Hilbert collision. Below two direct inclusion suffices.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_finiteGap_collision_mem_open`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.finiteGap_of_real_map_eq_truncatePair`
- `NLS.ZakharovShabat.sourceFiniteGap_exists_hilbert_realization`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbert_collision_of_collision`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_injective_of_hilbert`

This supplies the regularity step behind restricting inverse branches to Hilbert space. Openness of their intersections alone is not used as a proof of Hilbert preimages.

### S17-009: Proposition 17.3: surjectivity for 1<p<=2.

- Every real target in exponent 1<p<=2 has a preimage under the actual source map. The full original package combines this with injectivity and analytic local inverses.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`
- `NLS.ZakharovShabat.sourceSection17_original`
- `NLS.ZakharovShabat.SourceSection17OriginalData.global_inverse`

The upper bound p<=2 is retained in surjectivity and the global inverse.

### S17-010: Hilbert preimage and stronger-exponent membership goal.

- Include the p-target into Hilbert space and apply the internally constructed Hilbert inverse. The proof then recovers membership of this actual Hilbert preimage in the original p-space.
- The coefficient-preserving inclusions and map compatibility identify the final p-output with the prescribed target.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_bijective`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.realHomeomorph_symm_exponent`

The contradiction formulation (3.5) and the direct recovery of p-membership prove the same conclusion. The exact cited 2014 identification remains qualified in S17-007.

### S17-011: Origin inverse chart and the small target ball (3.6).

- The actual real map sends zero to zero and has an open image containing zero. Hence an actual positive-radius target ball lies in its image.
- The complex local inverse from Proposition 17.1 also supplies the ambient chart around zero; restricting its target neighborhood permits any smaller ball, including the source notation B_(4 epsilon).

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_isOpenEmbedding`
- `NLS.ZakharovShabat.SourceSection17OriginalData.complex_localInverse`

The surjectivity proof needs only the real small-ball consequence. Its radius is chosen from openness rather than fixed in advance.

### S17-012: Finite reduction strategy and source-space displacements.

- Finite lists of actual Hilbert angle-flow moves are defined in their list order. Every admissible move stops strictly before its current collapse time.
- The sum of the stronger-space displacements recovers both actual Fourier components of the total displacement in every finite exponent above one.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.AdmissibleActionReductions`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_displacement`

The initial Hilbert source need not itself belong to the stronger space. Membership is asserted for the displacement.

### S17-013: Original angle gradients, stronger-space Hamiltonian and (3.7).

- The original theta sum has real analytic local representatives modulo pi on the selected open-gap domain, with its full branch-independent differential.
- At conjugate exponents p<=2<=q, bounded recovery of the q-cotangent gives an exponent-p Hamiltonian vector analytic in the Hilbert source. Its Hilbert inclusion equals the actual theta Hamiltonian, even for independently constructed normalized families.
- The lifted curve solves the original Hamiltonian equation (3.7). Only the selected gap must be open.

Public declarations:

- `NLS.ZakharovShabat.sourceTheorem13_1_original`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.analyticAt_hilbertThetaVectorInExponent`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.hilbertThetaVectorInExponent_inclusion`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaDifferential_exponent`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hasDerivAt_hilbertActionReduction_thetaHamiltonian`

Angle values retain their period ambiguity; the vector field uses the well-defined differential. The selected open-gap condition replaces the inconsistent D_k/Z_k notation at real sources.

### S17-014: Actual finite reductions with the selected index m_n.

- Finite selected actions can be made smaller than any prescribed positive index-dependent bounds by actual admissible flows. The finite-set induction skips already small actions and preserves all earlier bounds.
- This includes the positive geometric thresholds used in the source. The selected gap and vector-field labels are m_n throughout the recursive construction.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbertActionReductionSequence_small_actions`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbertActionReduction_small_action`
- `NLS.ZakharovShabat.section17Mode_bijective`

The occurrences of Z_n and Y_n in the selected m_n step are corrected to Z_(m_n) and Y_(m_n). No new refutation is added.

### S17-015: Selected action decreases while other actions are preserved.

- Along the original theta flow, I_j(t)=I_j(0)-t when j is the selected index and I_j(t)=I_j(0) otherwise. The formula holds for all times up to collapse, including negative times.
- Consequently each later distinct selected move preserves the bounds already achieved. The finite induction proves all prescribed inequalities simultaneously.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.angleFlow_action_law`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_action_le`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbertActionReductionSequence_small_actions`

The exact action law supplies the integrated content of the canonical commutator used here. The source time derivative has the negative unit sign.

### S17-016: Untouched enumeration tail with the correct m_k index.

- Every unselected rectangular coordinate is preserved through the entire finite list. Therefore its original indexed action is preserved as well.
- In the enumerated tail the retained equality is I_(m_k)(phi_n)=I_(m_k)(phi_0).

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_coordinates_of_not_selected`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_pairAction_eq`

The printed right-hand index k is corrected to m_k. The finite-set formulation keeps the exact outside set.

### S17-017: Corrected coordinate-power sum constant and action budget.

- For 1<p<=2 the correct pointwise bound is |x|^p+|y|^p <= 2*((x^2+y^2)/2)^(p/2). It follows from concavity of the p/2 power.
- Both the coordinate-power sum and action-power sum are proved summable. The original spectral actions then satisfy the literal infinite summed bound with factor two, retaining both coordinate powers inside each summand.

Public declarations:

- `NLS.ZakharovShabat.real_pair_power_le_two_action`
- `NLS.RealCoeff.summable_pairAction_rpow`
- `NLS.RealCoeff.coordinate_power_tsum_le_two_actions`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.corrected_action_power_sum`

The factor two is used directly. The literal summed power is distinguished from the maximum product norm used by the target interfaces. No new optimality or failure witness is proved.

### S17-018: Summable action tails and the 2N+1 enumeration cutoff.

- Actual p-coordinates give summable original action powers. The one-based ordering 0,-1,1,-2,2,... is a proved bijection after shifting its natural-number index.
- Its first 2N+1 positions cover exactly the modes with absolute index at most N. The remaining enumeration sum equals the absolute-mode tail with |m|>N.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.corrected_action_power_sum`
- `NLS.ZakharovShabat.section17Mode_initial_block`
- `NLS.ZakharovShabat.section17Mode_tail_iff`
- `NLS.ZakharovShabat.section17Mode_corrected_tail_sum`

The absolute cutoff N is paired with 2N+1 enumeration positions. The actual surjectivity proof instead uses a chosen finite set and its exact complement, so both descriptions retain the same tail scope.

### S17-019: Small target estimate and identification of the reduced source (3.8).

- With factor two and an action-power budget below 2 epsilon^p, the coordinate-power sum is below 4 epsilon^p and hence below (4 epsilon)^p for p>=1. An existing general public example proves this positive arithmetic bound.
- The actual finite-action criterion gives a small p-target from small selected actions and unchanged outside coordinates, even when the candidate initially lives only in Hilbert space.
- An original p-preimage exists in the small image ball. Hilbert injectivity identifies it with the reduced Hilbert source, giving (3.8).

Public declarations:

- `NLS.RealCoeff.exists_finite_action_small_norm`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_bijective`

The corrected constant and matching cutoff preserve the original small-target argument. The implementation uses an arbitrary image-ball radius rather than depending on a norm equality for a product space.

### S17-020: Finite displacement recovers original p-membership.

- An admissible finite reduction preserves membership in every exponent p<=2: the reduced source is the original source plus a source-p displacement.
- Subtracting that displacement from the identified p-preimage recovers the original Hilbert preimage in p, finishing surjectivity.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_displacement_inclusion`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_mem_exponent_iff`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`

Both coefficient components and their real-type relation are retained; mere coordinatewise regularity is not substituted for source-space membership.

### S17-021: Attribution of the flow method to reference [36].

- The source attributes the method of the following flow lemma to reference [36], Lemma 1. The mathematical flow statement is proved internally in the next groups.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.lemma17_4`

This records the attribution in the dissertation; it does not independently compare the external paper or certify the historical attribution.

### S17-022: Lemma 17.4: unique C1 flow and displacement in every finite exponent.

- For every real Hilbert source with the selected gap open, the original theta Hamiltonian has a C1 solution on the complete interval (-infinity,I_k(phi_0)).
- Uniqueness holds against every ambient complex-source solution with the same initial value and actual derivative equation. The selected action tends to zero at the right endpoint.
- The displacement has a continuous real-type realization in every finite exponent r>1, with equality of every actual Fourier coefficient.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.lemma17_4`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_angleFlow_exists_unique_and_action_limit`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_angleFlow_continuous_real_displacement`

Only the selected gap is assumed open. No C1 extension through the collapse endpoint is asserted.

### S17-023: Hilbert canonical map and the original angle differential.

- The Hilbert map is globally bi-real-analytic and has the actual canonical rectangular brackets. Positive-root action-angle formulas identify the original theta with the polar angle modulo its period.
- On the selected open gap its full differential is (-y dx+x dy)/(2I). The identity remains valid when the map and auxiliary angle family were independently constructed.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertRealHomeomorph_symm_analytic`
- `NLS.ZakharovShabat.SourceSection14OriginalData.real_rectangular_formula`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.thetaDifferential_eq_rectangular`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.thetaDifferential_eq_map_rectangular`

The polar angle statement uses the original cosine/sine phase and local differential, not a globally single-valued analytic principal argument.

### S17-024: Equation (3.9) with inward signs in both components.

- The actual Jacobian sends the original theta Hamiltonian to the radial field with both components negative: -x_k/(x_k^2+y_k^2) and -y_k/(x_k^2+y_k^2). Every other coordinate has zero velocity.
- The coordinate radial curve scales the selected pair by sqrt(1-t/I_k(phi_0)), and its derivative is this field at the current point.

Public declarations:

- `NLS.ZakharovShabat.SourceSection16OriginalData.equation3_9`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.map_coordinates_thetaHamiltonian`
- `NLS.RealCoeff.actionReductionVector`
- `NLS.RealCoeff.hasDerivAt_actionReduction_vector`

The positive printed x sign in (3.9) is replaced directly by the inward negative sign. Existing historical witnesses are preserved without new ones.

### S17-025: Full pre-collapse time interval, uniqueness and selected-action limit.

- The positive selected action makes the radial scale smooth for every t<I_k(phi_0), including all negative times. The global analytic inverse lifts it to the actual source curve.
- The vector field is C1 near every point of the reference curve. Local Lipschitz uniqueness propagates across the connected open time interval, and the exact selected-action law gives the zero limit.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.contDiffAt_hilbertActionReduction`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReduction_thetaHamiltonian_unique`
- `NLS.FunctionalAnalysis.eqOn_of_autonomous_hasDerivAt`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.tendsto_action_hilbertActionReduction`

The explicit curve also has a continuous source-norm collapse limit, but the differentiable ODE statement remains on the open interval.

### S17-026: Bochner integration in the stronger space gives continuous displacement.

- For an exponent below two, the actual theta velocity has a continuous stronger-space realization and an actual Bochner integral on every segment from zero to t. Applying Hilbert inclusion commutes with that integral and recovers the source displacement.
- Above two, continuous Hilbert inclusion supplies the displacement directly. In both cases both actual Fourier components agree, and the resulting displacement is continuous in the claimed stronger or weaker source norm.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_angleFlow_displacement_of_conjugate`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_angleFlow_displacement_all_exponents`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_angleFlow_continuous_real_displacement`
- `NLS.FunctionalAnalysis.exists_continuous_displacement_of_hasDerivAt`

The integral proof does not infer stronger-norm convergence from Hilbert convergence alone. The additional angle families are constructed internally and identified by exponent compatibility.

### S17-027: Original periodic isospectral sets and action tori.

- The source isospectral set uses the actual periodic spectrum and algebraic multiplicities. The target torus fixes the quadratic radius at every signed index to the original spectral action.
- The action-radius identity identifies the preimage of that torus with the original source action level set.

Public declarations:

- `NLS.ZakharovShabat.sourceIsospectralSet`
- `NLS.RealCoeff.actionTorus`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_pairAction_eq`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.actionLevelSet_eq_preimage_actionTorus`

The action level set and the spectral isospectral set are distinct definitions; their equality below two is a proved later conclusion.

### S17-028: Compactness of the target torus for every finite exponent.

- Every action torus is closed. If nonempty, any one element supplies a single lp majorant for all coordinate magnitudes of every other element.
- Uniform majorant tails and closedness give compactness in the full target norm at every finite exponent. Empty tori and infinitely many nonzero actions are included.

Public declarations:

- `NLS.RealCoeff.isClosed_actionTorus`
- `NLS.RealCoeff.abs_coordinates_le_of_pairAction_eq`
- `NLS.RealCoeff.isCompact_actionTorus`
- `NLS.RealCoeff.isCompact_of_isClosed_of_majorant`

Finite exponent is required. Coordinatewise compactness alone is not used to claim norm compactness.

### S17-029: Lemma 17.5: equality and compactness below two, inclusion above two.

- For 1<p<=2 the actual isospectral image is the entire prescribed action torus and the source isospectral set is compact in its original norm.
- For every finite p>1, hence also p>2, the isospectral image is contained in the torus.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.lemma17_5`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.lemma17_5_i`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.image_isospectralSet_subset_actionTorus`

Neither complete torus images nor source isospectral compactness above exponent two are asserted.

### S17-030: Equal periodic spectral data give equal discriminants and actions.

- Equality of the actual periodic spectrum with multiplicities is equivalent to equality of the normalized discriminant. Equal endpoints also identify the canonically signed square root.
- A common smaller action contour gives equality of each original indexed action, including collapsed gaps and the finite central block. This proves the all-exponent torus inclusion.

Public declarations:

- `NLS.ZakharovShabat.mem_sourceIsospectralSet_iff_discriminant_eq`
- `NLS.ZakharovShabat.sourceCanonicalRoot_eq_of_isospectral`
- `NLS.ZakharovShabat.sourceRealAction_eq_of_isospectral`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.image_isospectralSet_subset_actionTorus`

The normalization and spectral multiplicities are retained; equality of unlabelled zero sets alone is not substituted.

### S17-031: Hilbert action rotations and transfer of torus equality below two.

- In Hilbert space the inverse map lifts every finite coordinate action rotation. Its actual source velocity is the action Hamiltonian, whose discriminant derivative is zero; every such source curve is isospectral.
- Finite rotations can match any finite block of an equal-action target, and those replacements converge in the full norm. Continuity of the inverse and closedness of the actual isospectral set yield the converse inclusion.
- Action and discriminant compatibility transfer this equality to p<=2. The global inverse maps the compact action torus to the compact source action level set, and the spectral set is closed.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionRotationSequence_mem_isospectralSet`
- `NLS.RealCoeff.closure_actionRotationSequence_range`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_actionLevelSet_subset_isospectralSet`
- `NLS.ZakharovShabat.sourceRealActionLevelSet_subset_isospectralSet`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.image_isospectralSet_eq_actionTorus`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompact_isospectralSet`

This establishes the mathematical converse internally; the exact external [23] edition comparison remains the qualification in S17-007.

## Evidence and validation

The [original Section 17 interface](../NLS/ZakharovShabat/SourceSection17Original.lean)
retains the actual map, inverse derivatives, flow and isospectral sets. The
[finite reductions](../NLS/ZakharovShabat/SourceHilbertFiniteActionReduction.lean)
and [stronger-space displacement](../NLS/ZakharovShabat/SourceHilbertAngleDisplacement.lean)
supply the regularity step in surjectivity. The
[summed factor-two bound](../NLS/ZakharovShabat/SourceActionPowerSum.lean) and
[matching enumeration cutoff](../NLS/ZakharovShabat/Section17EnumerationCutoff.lean)
give the direct positive corrections.

This comparison inspected 58 full module bodies and resolves 92 declarations.
Two additional excerpts inspect only the existing positive pointwise constant proof
and the general public example for the corrected 4 epsilon budget. Historical
counterexamples are unchanged. The full transitive dependency graph is covered by
the reused axiom audit, not a fresh semantic reading of every dependency.

The Lean and dependency-lock snapshot is identical to pushed commit c8cbe87. Its successful full check is reused, not rerun: 8,559 build jobs, 7,635 public examples and the transitive axiom audit of 44,604 NLS declarations, with 21 inherited warnings and no new warnings. Current source hashes, declaration references, review integrity and local documentation links are checked separately. These integrity checks do not certify mathematical completeness.

Next: Section 18, Overview of frequencies, convexity and wellposedness.
