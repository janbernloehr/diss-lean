# Section 24 ordered assertion comparison

The ordered Section 24 comparison covers 20 groups on printed pp. 106–107: 14 matched, two corrected and four contextual, with no partial or pending groups in this local ledger. The original higher actions retain arbitrary piecewise C1 circuits, the exact contour normalization and the chosen primitive and family. Scalar analyticity on the full Section 11 contour domain is distinguished from all-order traces on the retained Section 19/20 complex Sobolev preimages. The physical hierarchy keeps its independent Riccati definition, literal low-order integrals and one canonical lower-jet polynomial before all smooth complex sources. The trace includes absolute convergence, the mass endpoint and the sharp odd-order Hm identity with positive factor 1/4^m. The real arcosh gap integral, positivity, actual mean-value sample and two-sided asymptotic retain signed indices and closed gaps. Zero detection is restricted to the proved real odd-level equivalence; collapsed complex gaps still give zero on the retained domain. The norm-square mass interpretation is restricted to real sources, while complex sources keep bilinear mass. Historical attributions, later-use transitions and the external book-normalization footnote are contextual. No independent comparison with the exact 2014 book is asserted. Existing corrections and refutations are preserved; this documentation step adds no Lean proof or refutation. Broader completeness and Appendix G.2 qualifications remain.

Source: printed pp. 106–107, text lines 8666–8781 and footnote 8794–8795.
Line numbers count newline characters and preserve form feeds. Both rendered
pages were inspected. Lean spectral power k represents printed level k+1.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S24-001 | 8668–8669 | Original domain and introductory recall | matched |
| S24-002 | 8669–8678 | Ordinary-action contour and orientation | matched |
| S24-003 | 8678–8686 | Higher-action definition on arbitrary isolating circuits | matched |
| S24-004 | 8688–8688 | Level one equals ordinary action | matched |
| S24-005 | 8688–8689 | Analyticity on original contour domain | matched |
| S24-006 | 8689–8690 | Corrected zero-detection scope | corrected |
| S24-007 | 8690–8700 | Integration by parts and original primitive in (5.2) | matched |
| S24-008 | 8701–8709 | Mass trace and real-source squared-norm interpretation | corrected |
| S24-009 | 8720–8722 | Historical hierarchy attribution | contextual |
| S24-010 | 8723–8731 | Physical mass, momentum and energy integrals | matched |
| S24-011 | 8733–8740 | General physical hierarchy and canonical lower-jet polynomial | matched |
| S24-012 | 8742–8746 | Theorem 24.1 absolute trace on complex H^(k-1) | matched |
| S24-013 | 8748–8755 | Odd trace and physical derivative integral including m=0 | matched |
| S24-014 | 8757–8758 | Use of the trace in later estimates | contextual |
| S24-015 | 8759–8765 | Literal real gap integral and arcosh profile | matched |
| S24-016 | 8766–8766 | Reality and odd-level nonnegativity | matched |
| S24-017 | 8766–8773 | Mean-value sample in the actual periodic segment | matched |
| S24-018 | 8772–8776 | Endpoint displacement and sample-power asymptotics | matched |
| S24-019 | 8776–8778 | Transition to quantitative localization | contextual |
| S24-020 | 8794–8795 | Footnote on comparison with external Hamiltonian normalization | contextual |

## Compared passages

### S24-001: Original domain and introductory recall

- One original family and its retained source domain carry all higher actions, their analytic sequence maps and physical traces. The family is chosen before every index, action level and Sobolev order.

Public declarations:

- `NLS.ZakharovShabat.sourceSection24_original`
- `NLS.ZakharovShabat.SourceSection23Data.section24`

Scalar contour analyticity on the earlier Section11 domain and trace statements on the retained Section19/20 domain U are distinguished below. No equality of these two domains is asserted.

### S24-002: Ordinary-action contour and orientation

- The ordinary indexed action is the literal integral of z times the original discriminant derivative divided by the canonical root, with factor 1/pi. Every piecewise C1 winding-one circuit in an original isolating cut disk gives the same value.

Public declarations:

- `NLS.ZakharovShabat.sourceActionContour`
- `NLS.ZakharovShabat.SourceIsolatingNeighborhoods.indexedAction_eq_circuit`
- `NLS.ZakharovShabat.sourceActionContour_eq_of_original_circuits`

The winding-one condition represents the printed counterclockwise single traversal. Corners and different original isolating families are allowed.

### S24-003: Higher-action definition on arbitrary isolating circuits

- At Lean spectral power k, the higher action uses z^(k+1) and factor 1/((k+1)*pi), exactly printed level k+1. Every winding-one piecewise C1 circuit in the original isolating cut disk computes the original indexed higher action.

Public declarations:

- `NLS.ZakharovShabat.sourceHigherActionContour`
- `NLS.ZakharovShabat.SourceCriticalRootPeriodCircle.higherActionContour_eq`
- `NLS.ZakharovShabat.SourceCriticalRootPeriodCircle.higherActionContour_eq_mul_winding`

The stronger winding formula also handles reversed and repeated traversals. All natural powers, signed indices and finite source exponents p>1 are included.

### S24-004: Level one equals ordinary action

- The higher action at spectral power zero is exactly the original ordinary indexed action.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_zero`

Printed level one corresponds to Lean power zero; this is equality of the original definitions.

### S24-005: Analyticity on original contour domain

- Each original scalar higher action is complex analytic throughout the unchanged open Section11 contour domain, at every index and level. The retained Section24 family also provides analytic higher-action sequences on its full complex Sobolev preimages in the admissible range.

Public declarations:

- `NLS.ZakharovShabat.SourceSection11ContourData.analytic_indexedHigherAction`
- `NLS.ZakharovShabat.SourceSection24Data.higherAction_analytic`
- `NLS.ZakharovShabat.SourceSection24Data.sequence_analytic`

The scalar statement does not shrink to the trace domain or a real-chart union. Sequence analyticity is separately quantified on the retained Section19/20 domain U.

### S24-006: Corrected zero-detection scope

- The positive zero-detection equivalence holds on real-type sources at every printed odd level: the higher action vanishes exactly when the original periodic gap collapses. At every level, a collapsed complex gap gives zero on the retained Section19 domain.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_even_eq_zero_iff`
- `NLS.ZakharovShabat.SourceSection19Data.indexedHigherAction_of_collapsed`

Use this precise real odd-level equivalence and the stated complex implication in place of the unrestricted printed equivalence. The central gap and m=0 are included. Historical corrections and refutations remain; no new refutation is added.

### S24-007: Integration by parts and original primitive in (5.2)

- Formula (5.2) holds with exact factor -1/pi and integrand z^k times the original Section19 primitive. Polynomial integration by parts uses actual path integrals and telescoping endpoint terms on every finite piecewise C1 loop in the original root domain. Winding-one isolating circuits give the original indexed action.

Public declarations:

- `NLS.ComplexAnalysis.PiecewiseC1Loop.integral_pow_mul_deriv_eq_neg`
- `NLS.ZakharovShabat.sourceHigherActionContour_eq_primitive`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_eq_piecewise_primitive`
- `NLS.ZakharovShabat.SourceSection24Data.higherAction_eq_original_piecewise_primitive`

The original family, source domain and arbitrary primitive index are retained. Analyticity is needed near the circuit only; no extension through the spectral cut is assumed. Closed gaps are included.

### S24-008: Mass trace and real-source squared-norm interpretation

- The mass trace includes the H0 endpoint and the entire retained complex source preimage. Its Hamiltonian is the physical bilinear mass. On real-type sources it equals half the squared original two-component L2 norm, and the action series converges to that value. The squared physical norm is the sum of the two unit-interval component energies.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.trace_printed_level`
- `NLS.ZakharovShabat.sobolevNLSHamiltonian_one`
- `NLS.ZakharovShabat.sourceHilbertMass_eq_half_norm_sq_of_realType`
- `NLS.ZakharovShabat.sourceHilbert_sum_actions_eq_half_norm_sq`
- `NLS.ZakharovShabat.SourceSection14OriginalData.physical_hasSum_actions`
- `NLS.ZakharovShabat.norm_sourcePhysicalL2`
- `NLS.ZakharovShabat.norm_sq_intervalL2Representative`

The norm-square interpretation in (5.3) is restricted to the real form. The complex trace retains the bilinear mass instead of a norm square. This is a direct scope correction, with no new counterexample.

### S24-009: Historical hierarchy attribution

- The paragraph attributes the higher trace formulas to the cited literature; the mathematical identity is compared in S24-012.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.trace_printed_level`

No independent formal theorem about historical priority or the cited external publication is claimed.

### S24-010: Physical mass, momentum and energy integrals

- The independently defined physical hierarchy has exactly the displayed mass, symmetrized momentum with coefficient i/2, and kinetic-plus-quartic third Hamiltonian. The corresponding established Sobolev mass, momentum and sharp H3 energy agree with these physical constructions.

Public declarations:

- `NLS.ZakharovShabat.classicalNLSHamiltonian_one`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_two`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_three`
- `NLS.ZakharovShabat.sobolevNLSHamiltonian_one_eq_periodOneSobolevMass`
- `NLS.ZakharovShabat.sobolevNLSHamiltonian_two_eq_periodOneSobolevMomentum`
- `NLS.ZakharovShabat.periodOneSobolevMomentum_eq_integral`
- `NLS.ZakharovShabat.periodOneSobolevHamiltonian_eq_integral`
- `NLS.ZakharovShabat.sourceSection27_H3_bridge`

The classical integration-by-parts formulas use smooth unit-periodic complex pairs. The Sobolev bridges retain the physical derivatives and component products; the normalization is not defined through the action sum.

### S24-011: General physical hierarchy and canonical lower-jet polynomial

- For every k the physical H_(k+1) is (-i)^k times the unit-interval integral of a times the kth derivative of b plus one canonical polynomial using jets through order k-1. The polynomial is explicitly -X(false,0)*R_k and is chosen before every smooth complex pair.

Public declarations:

- `NLS.ZakharovShabat.section24HamiltonianRemainder_jetOrder`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_leading_polynomial`
- `NLS.ZakharovShabat.exists_classicalNLSHamiltonian_leading_polynomial`
- `NLS.ZakharovShabat.nlsRiccatiRemainder_hamiltonian_grades`

The statement includes even Hamiltonian orders, not just the odd reduced hierarchy. The proof also covers k=0 and does not need periodicity for this defining unit-interval identity. The positive all-order polynomial proof and its three public examples have passed the full checks and are committed and pushed.

### S24-012: Theorem 24.1 absolute trace on complex H^(k-1)

- At every printed k>=1, the sum over all integer indices converges absolutely on the full retained complex H^(k-1) preimage and equals H_k/2^(k-1). The Hamiltonian is independently defined by the physical Riccati recurrence. Connectedness and real-form analytic uniqueness give the complex extension.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.trace_printed_level`
- `NLS.ZakharovShabat.SourceSection24Data.absolute_convergence`
- `NLS.ZakharovShabat.SourceSection19Data.indexedHigherAction_hamiltonian_trace`
- `NLS.ZakharovShabat.SourceSection19Data.indexedHigherAction_trace_of_real`
- `NLS.ZakharovShabat.SourceSection19Data.isConnected_higherSobolev_domain`

The original Section19/20 source domain U is fixed before all k, and its entire Sobolev preimage is used. The mass endpoint k=1 is included. No narrower source neighborhood is chosen for each order.

### S24-013: Odd trace and physical derivative integral including m=0

- At printed odd level 2*m+1 the trace has the positive factor 1/4^m. For m>=1 the sharp complex Hm Hamiltonian agrees on real smooth sources with the integral of the squared mth derivative plus a fixed polynomial in lower jets. The mass trace supplies m=0.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.odd_trace`
- `NLS.ZakharovShabat.SourceSection24Data.trace_printed_level`
- `NLS.ZakharovShabat.exists_classicalNLSHamiltonian_odd_real_reduced_polynomial`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_real_decomposition`
- `NLS.ZakharovShabat.sobolevOddHamiltonian_eq_classical`

The real leading term is the squared derivative of one scalar component; the pair norm and its factor two remain explicit. The remainder polynomial is chosen before the source, and the Hm extension is proved independently of defining an action sum.

### S24-014: Use of the trace in later estimates

- The sentence announces the use of the odd trace in the estimates of Sections26 and27.

Public declarations:

- `NLS.ZakharovShabat.SourceSection24Data.odd_trace`

It introduces no separate bound. The quantitative constants and source norms are assessed in those later sections.

### S24-015: Literal real gap integral and arcosh profile

- Formula (5.5) is the actual endpoint-interval integral with factor 2/pi, spectral power k-1 in printed notation, and the positive discriminant arcosh profile. The original canonical upper and lower boundary values give opposite primitive signs and the required contour normalization.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_eq_gapIntegral`
- `NLS.ZakharovShabat.sourceRealHigherAction_eq_gapIntegral`
- `NLS.ZakharovShabat.sourceRealGapArcoshProfile`
- `NLS.ZakharovShabat.sourceRealGapArcoshProfile_spec`
- `NLS.ZakharovShabat.sourceRealGap_upperIntegral_eq_arcosh`
- `NLS.ZakharovShabat.sourceRealGap_lowerIntegral_eq_neg_arcosh`

Every signed index and real finite-p source with p>1 is included. Endpoint integrability and collapsed gaps are handled; the expression is not merely a formal contour-deformation argument.

### S24-016: Reality and odd-level nonnegativity

- On the real form every higher action is real, and every printed odd-level action is nonnegative.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_real`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_even_nonneg`

Lean power 2*m represents printed level 2*m+1. Both open and closed gaps, including the central gap, are covered.

### S24-017: Mean-value sample in the actual periodic segment

- Formula (5.6) uses an actual sample in the closed interval between the original periodic endpoints and gives J_(n,2*m+1)=zeta^(2*m)*I_n. The formal result covers every natural spectral power.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_eq_power_mul_action`

No division by I_n occurs, so collapsed gaps and vanishing actions are retained. The sample is real and belongs to the original gap.

### S24-018: Endpoint displacement and sample-power asymptotics

- One simultaneous choice of the mean-value samples has lp displacement from n*pi, satisfies the exact action identity for every signed index, and has normalized power tending to one along both integer tails. At p=2 this supplies the printed l2 statement and the asymptotic following (5.6), including m=0.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_exists_asymptotic_samples`
- `NLS.ZakharovShabat.sourceGapSample_ratio_tendsto`
- `NLS.ZakharovShabat.sourceGapSample_power_ratio_tendsto`
- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic`

The cofinite filter on integers expresses |n| tending to infinity. The result includes closed gaps without division by an action. Quantitative source-uniform thresholds are deferred to Section25.

### S24-019: Transition to quantitative localization

- The final paragraph motivates quantitative periodic-eigenvalue localization for subsequent estimates of high-level actions.

Public declarations:

- `NLS.ZakharovShabat.sourceIndexedHigherAction_asymptotic`

No new uniform rate is asserted here. Section25 supplies the quantitative localization statement.

### S24-020: Footnote on comparison with external Hamiltonian normalization

- The footnote states a normalization convention relative to the cited book. The implementation fixes the physical hierarchy by its Riccati integral definition and verifies the displayed low-order Hamiltonians and expansion coefficient.

Public declarations:

- `NLS.ZakharovShabat.classicalNLSHamiltonian`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_riccati_coefficient`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_two`
- `NLS.ZakharovShabat.classicalNLSHamiltonian_three`

This is an internal normalization comparison, not an independent verification against the exact external 2014 book. The wider qualification about that construction remains in COMPLETENESS.md.

## Evidence and validation

The [original Section 24 package](../NLS/ZakharovShabat/SourceSection24Original.lean)
retains the chosen family and the entire original trace domain. The
[piecewise primitive formula](../NLS/ZakharovShabat/SourceHigherActionPiecewisePrimitive.lean)
handles corners and arbitrary original winding-one circuits. The
[all-order polynomial formula](../NLS/ZakharovShabat/SourceSection24HamiltonianPolynomial.lean)
supplies the literal phase, derivative and canonical remainder before every source.

This comparison read 42 complete module bodies and resolves 60 public declarations.
It reconciles the earlier named trace comparison and both new positive proof steps.
Reading every transitive dependency again is not claimed. The historical corrections
and refutations are unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit c2bd47e6f9e8707f13b3aa9b2ac988ffebe084b5: 8,575 build jobs, 7,679 public examples and a transitive axiom audit of 44,689 NLS declarations, with 21 inherited warnings and zero new. All 60 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered comparison for Section 25. The
[broader completion qualifications](COMPLETENESS.md) remain.
