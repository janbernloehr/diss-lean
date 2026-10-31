# Section 22 ordered assertion comparison

The ordered Section 22 comparison covers 37 groups on printed pp. 98–101: 23 matched, 10 corrected and 4 contextual, with no partial or pending groups in this local ledger. It retains the original moment/root/map families, physical phase signs and factor-four mass shift, actual inverse image restrictions above two, exact component-sum continuity constants, one complex neighborhood before all horizons, full Banach trajectory analyticity, local and invariant small-data source flows, arbitrary-Hilbert frequency divergence and literal separation, and the original all-smooth approximation solution definition. Finite-gap-only finite-target and all-smooth endpoint-inclusive nonextension scopes remain separate. The local coordinate domain, coordinate-ball ambient space and common small-data source domain are normalized directly. Existing sign, time-variable, path-codomain, proof-label, index and non-Hilbert mass corrections are preserved. The exact 2014 construction, Appendix G.2 and wider dissertation-completeness qualifications remain. No new Lean proof or refutation is added.

Source: printed pp. 98–101, text lines 8124–8385. Line numbers count newline
characters and preserve form feeds. All four rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S22-001 | 8126–8137 | Renormalized frequency, analytic extension and global coordinate phases | matched |
| S22-002 | 8138–8146 | Complex coordinate convention, real conjugation and local space notation | matched |
| S22-003 | 8148–8152 | Equation 4.14 physical phase signs | corrected |
| S22-004 | 8154–8155 | Joint scalar analyticity on the actual coordinate image | matched |
| S22-005 | 8157–8171 | Equation 4.15 guarded inverse source flow | matched |
| S22-006 | 8172–8185 | Ordinary frequency, factor four mass and equation 4.16 below exponent two | matched |
| S22-007 | 8186–8187 | Transition to Theorem 18.5 coordinate properties | contextual |
| S22-008 | 8190–8194 | Theorem 22.1(i): norm continuity and compact-time trajectory analyticity | matched |
| S22-009 | 8195–8197 | Theorem 22.1(i): group and analytic diffeomorphism below exponent two | matched |
| S22-010 | 8200–8204 | Theorem 22.1(ii): ordinary trajectories, group and analytic diffeomorphism | matched |
| S22-011 | 8206–8211 | Theorem 22.1(iii): both scalar nonextensions at any signed index | matched |
| S22-012 | 8214–8214 | Historical KdV proof comparison | contextual |
| S22-013 | 8215–8224 | Global scalar phases and corrected time-difference estimate | corrected |
| S22-014 | 8224–8236 | Displayed finite-head and tail p-power estimate | matched |
| S22-015 | 8238–8246 | Small tail and finite-head time increment | matched |
| S22-016 | 8257–8260 | Norm continuity and nonlinear group property | matched |
| S22-017 | 8262–8264 | Scalar complex trajectory analyticity | corrected |
| S22-018 | 8265–8268 | One complex neighborhood and uniform refined frequency asymptotics | matched |
| S22-019 | 8270–8277 | Exponential multiplier and Banach trajectory analyticity in coordinate space | corrected |
| S22-020 | 8278–8280 | Ordinary analytic flow in the Hilbert exponent range | matched |
| S22-021 | 8282–8288 | Correct proof label, non-Hilbert data and divergent mass | corrected |
| S22-022 | 8289–8289 | Ordinary frequency divergence and arbitrary selected signed index | corrected |
| S22-023 | 8290–8294 | Oscillating subsequence and small times | matched |
| S22-024 | 8296–8306 | Coordinate separation and failure of uniform trajectory convergence | matched |
| S22-025 | 8308–8308 | Transition to Theorem 18.5 via source wellposedness | contextual |
| S22-026 | 8310–8312 | Corollary 22.2(i): both equations globally analytically wellposed | matched |
| S22-027 | 8315–8316 | Corollary 22.2(ii): local and small-data global renormalized solutions | matched |
| S22-028 | 8319–8323 | Corollary 22.2(iii): source nonextension including endpoint targets | matched |
| S22-029 | 8325–8327 | Source conjugation by the global Birkhoff diffeomorphism | matched |
| S22-030 | 8329–8334 | Local image chart and one common time-neighborhood pair | corrected |
| S22-031 | 8336–8350 | Equation 4.17 and physical compact-time analytic trajectories | matched |
| S22-032 | 8352–8357 | Invariant small coordinate ball by norm preservation | corrected |
| S22-033 | 8359–8362 | One small source domain supports all time horizons | corrected |
| S22-034 | 8364–8370 | Physical nonextension proof and finite-target composition scope | matched |
| S22-035 | 8373–8378 | Remark 22.3 exact solution characterization with corrected signs | corrected |
| S22-036 | 8380–8382 | Uniqueness in the full continuous-curve class | matched |
| S22-037 | 8382–8385 | Contextual comparison with cited restriction norm spaces | contextual |

## Compared passages

### S22-001: Renormalized frequency, analytic extension and global coordinate phases

- The original moment frequency extends analytically near all real sources. Adding the physical quadratic lattice gives the actual real renormalized frequency. Every initial source supplies a global coordinate phase at every finite p>1, using one original family before all sources, signed indices and horizons.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.bounded_phase_correction`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.phaseFrequency_complex`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_real`
- `NLS.ZakharovShabat.sourceSection22_original`

Global coordinate trajectories do not supply a global source inverse above exponent two.

### S22-002: Complex coordinate convention, real conjugation and local space notation

- The exact bounded complex linear change sends rectangular coordinates to z=(x-i*y)/sqrt(2), w=(x+i*y)/sqrt(2). Actual real sources give conjugate pairs at the same signed index. The complex source map is the original rectangular map composed with this fixed equivalence.

Public declarations:

- `NLS.Birkhoff.rectangularToComplex`
- `NLS.Birkhoff.rectangularToComplex_real`
- `NLS.ZakharovShabat.sourceComplexBirkhoffMap`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.complex_map_real`

The source Fourier real form uses reflected conjugation, whereas the Birkhoff complex real form uses same-index conjugation. These spaces are kept separate.

### S22-003: Equation 4.14 physical phase signs

- For the source coordinate convention, the physical original Hamiltonian trajectory has exp(-i*t*frequency) in the first component and exp(+i*t*frequency) in the second, with the same original amplitudes and moment frequency.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_coordinates`

Preserve the already established phase-sign correction and historical refutation modules unchanged. This comparison adds no refutation.

### S22-004: Joint scalar analyticity on the actual coordinate image

- Both scalar components are jointly real analytic in real time and initial rectangular coordinates on the actual open original Birkhoff image, for every finite p>1 and signed index.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.phase_coordinate_joint_analytic`

This is scalar analyticity; it does not claim time differentiability in the full low-regularity sequence norm.

### S22-005: Equation 4.15 guarded inverse source flow

- The original inverse lift is an actual smooth-approximation solution on a compact interval exactly when the full coordinate curve stays in the original image. The frequency, initial source and inverse all belong to the same original family.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.trajectory_domain_iff_solution`
- `NLS.ZakharovShabat.SourceSection20Data.renormalized_solution_coordinates`

The total inverse formula outside its actual image is not used as a physical solution.

### S22-006: Ordinary frequency, factor four mass and equation 4.16 below exponent two

- The ordinary coordinate frequency adds exactly four times the original physical mass. For 1<p<=2 the original map is onto, and its inverse lift is a global ordinary physical solution with the exact ordinary coordinate law.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.ordinary_coordinate_trajectory_apply`
- `NLS.ZakharovShabat.SourceSection20Data.ordinary_solution_iff_coordinates`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_solutions`

Above two the ordinary nonextension statements compare finite-gap/Hilbert dynamics; an infinite mass is not substituted into a real frequency definition.

### S22-007: Transition to Theorem 18.5 coordinate properties

- This sentence introduces the comparison with the earlier Theorem18.5 coordinate properties. The following theorem and source wellposedness assertions carry the mathematical requirements.

Organizational transition, not an additional theorem.

### S22-008: Theorem 22.1(i): norm continuity and compact-time trajectory analyticity

- The actual renormalized coordinate trajectory is continuous in the full sequence norm and has real analytic compact-time trajectory dependence on the entire actual open coordinate image. One complex source neighborhood U supports every horizon.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_joint_continuous`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_analytic`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_coordinate_analytic`

Finite p>1, actual original image, full compact-time norm. Real coordinate data produce the original conjugate-pair real form.

### S22-009: Theorem 22.1(i): group and analytic diffeomorphism below exponent two

- For 1<p<=2, the original renormalized coordinate time map is a real analytic diffeomorphism of the whole real coordinate space. Its inverse is negative time, and the original physical group laws hold for every pair of real times.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.global_physical_group`
- `NLS.ZakharovShabat.SourceSection20Data.renormalized_coordinate_time_map`

The group law is nonlinear and uses the original preserved frequencies and source flow; global surjectivity is used only in the stated range.

### S22-010: Theorem 22.1(ii): ordinary trajectories, group and analytic diffeomorphism

- In the Hilbert exponent range both continuity and full compact-time coordinate analyticity hold for ordinary NLS, with analytic coordinate diffeomorphisms, negative-time inverse and physical group law.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.ordinary_coordinate_trajectory_analytic`
- `NLS.ZakharovShabat.SourceSection20Data.ordinary_coordinate_time_map`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_group`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_joint_continuous`

The unchanged mass correction and original Birkhoff family are retained.

### S22-011: Theorem 22.1(iii): both scalar nonextensions at any signed index

- At an original coordinate image point outside ell2, each scalar component with nonzero selected amplitude has no continuous compact-time extension agreeing with the actual finite-gap dynamics. Every signed index, including zero and negative indices, is allowed.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_fst`
- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_snd`

The two components retain their separate nonvanishing hypotheses and physical time orientations. Agreement on finite-gap data suffices.

### S22-012: Historical KdV proof comparison

- The citation to the KdV proof is historical context; no result about that external cited proof is used as an unproved project axiom.

No bibliographic priority or external-proof comparison is claimed formalized.

### S22-013: Global scalar phases and corrected time-difference estimate

- The repeated second time variable is corrected to s. The exact scalar t-s identity and factor-two bound are proved for arbitrary real frequencies, amplitudes and times. The two physical signs have the same absolute increment.

Public declarations:

- `NLS.Coeff.norm_phaseFlow_sub_apply`
- `NLS.Coeff.norm_phaseFlow_sub_apply_le`
- `NLS.Birkhoff.norm_hamiltonianPhaseFlow_sub_apply`

Direct correction only; the historical Hamiltonian sign correction is retained. No new refutation.

### S22-014: Displayed finite-head and tail p-power estimate

- The p-power of the exact component-sum pair norm is bounded by the finite-head phase energy plus exactly 2^p times the complementary initial energy. This holds for arbitrary finite signed heads; the symmetric [-N,N] head is a specialization. The original trajectory and actual image inverse are retained.

Public declarations:

- `NLS.Birkhoff.norm_hamiltonianPhaseFlow_sub_rpow_le`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_increment_rpow_le`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_coordinate_increment_rpow_le`

Finite p>=1 in the generic estimate, finite p>1 in the original-family interface. No maximum-product isometry is assumed.

### S22-015: Small tail and finite-head time increment

- For every positive epsilon, one symmetric cutoff N>=1 is chosen before a positive delta. The weighted tail is at most epsilon^p. For all real time origins with |t-s|<delta the displayed finite-head scalar factors times the full initial pair norm are at most epsilon, and the full pair increment is at most 2*epsilon. The original-family cutoff and delta precede every compact horizon.

Public declarations:

- `NLS.Birkhoff.exists_symmetric_phase_tail_small`
- `NLS.Birkhoff.exists_phase_head_small`
- `NLS.Birkhoff.exists_symmetric_phase_continuity_estimate`
- `NLS.ZakharovShabat.SourceSection20Data.exists_hamiltonian_phase_continuity_cutoff`

The generic finite-head proof also bounds the finite phase energy by epsilon^p, directly supplying the next implication. This is a coordinate trajectory assertion and does not remove the source image condition.

### S22-016: Norm continuity and nonlinear group property

- The two small-energy conditions imply the printed 2*epsilon norm bound. Original coordinate curves are continuous in the full sequence norm. The actual nonlinear group law and analytic negative-time inverse hold on the whole coordinate space for 1<p<=2.

Public declarations:

- `NLS.Birkhoff.norm_hamiltonianPhaseFlow_sub_le_of_head_tail`
- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_phase_joint_continuous`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_group`
- `NLS.ZakharovShabat.SourceSection20Data.renormalized_coordinate_time_map`

The nonlinear group assertion uses the proved original source dynamics and preserved frequency, not merely the fixed-frequency algebraic phase law. Above two retain the image guard.

### S22-017: Scalar complex trajectory analyticity

- The scalar trajectory has complex values. Full Banach trajectory analyticity on the actual coordinate image is stronger than analyticity after any bounded scalar coordinate projection. Scalar coordinates are jointly real analytic in time and initial coordinates.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.hamiltonian_coordinate_analytic`
- `NLS.ZakharovShabat.SourceSection20Data.phase_coordinate_joint_analytic`
- `NLS.ZakharovShabat.SourceSection20Data.exists_complex_coordinate_phase_neighborhood`

Correct C([-T,T],R) to C([-T,T],C). Joint scalar analyticity does not assert full sequence-valued differentiability in time at rough sources.

### S22-018: One complex neighborhood and uniform refined frequency asymptotics

- At each original real source, an actual complex coordinate neighborhood contains its complex Birkhoff image. Its analytic inverse lands in the unchanged original U and has the actual right-inverse identity. On that single neighborhood the original uncorrected frequency has a fixed p/2+OnePlus decomposition, with locally uniform norms before every OnePlus projection exponent.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.exists_complex_coordinate_phase_neighborhood`
- `NLS.ZakharovShabat.SourceSection20Data.frequency_mixed_at_real`

The quadratic lattice is added separately to the original renormalized moment frequency. Use the uncorrected p/2 estimate, not the distinct gap-square-corrected p/3 remainder.

### S22-019: Exponential multiplier and Banach trajectory analyticity in coordinate space

- On the same actual complex coordinate neighborhood chosen before every horizon, the exponential error has a fixed p/2+OnePlus decomposition uniformly for times in [-R,R]. The full coordinate trajectory is complex analytic in its Banach compact-time norm and is bounded by exp(R*C)*M, with C and M chosen before R. The fixed unbounded real quadratic phase contributes modulus one.

Public declarations:

- `NLS.Coeff.exists_uniform_phase_error_sequence`
- `NLS.Coeff.exists_uniform_phase_error_onePlus_decomposition`
- `NLS.Coeff.norm_complex_phase_mul_le`
- `NLS.ZakharovShabat.SourceSection20Data.norm_hamiltonian_phase_trajectory_le`
- `NLS.ZakharovShabat.SourceSection20Data.exists_complex_coordinate_phase_neighborhood`

Correct the printed FL_c^p path codomain to the coordinate space ell_c^p. The existing Banach trajectory uses the maximum-product norm; uniform boundedness and analyticity hold in the equivalent component-sum pair norm as well. Exact continuity constants are proved separately in the component-sum norm. Both physical signs are retained.

### S22-020: Ordinary analytic flow in the Hilbert exponent range

- The established ordinary trajectory construction gives the corresponding analytic compact-time coordinate flow in the full range 1<p<=2.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.ordinary_coordinate_trajectory_analytic`
- `NLS.ZakharovShabat.SourceSection20Data.ordinary_coordinate_time_map`

The actual ordinary frequency retains the factor-four physical mass.

### S22-021: Correct proof label, non-Hilbert data and divergent mass

- The repeated proof label is (iii). At the stipulated nonsquare-summable limit, every pointwise Hilbert approximation has diverging energy, including the exact half-sum energy of pairs. For original Hilbert complex coordinates that energy equals physical mass. Every norm-convergent real coordinate approximation is eventually in the actual original image, whose inverse recovers the exact pair and stays in the original frequency domain.

Public declarations:

- `NLS.Coeff.tendsto_energy_atTop_of_nonsummable_limit`
- `NLS.Coeff.tendsto_pair_energy_atTop_of_nonsummable_limit`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_complex_map_energy_eq_mass`
- `NLS.ZakharovShabat.SourceSection20Data.eventually_conjugate_coordinate_image`
- `NLS.ZakharovShabat.mem_sourceHilbertLocus_iff`

The infinite mass is asserted only at the stipulated non-Hilbert datum. Generic complex-pair energy is identified with physical mass on the real Birkhoff form through the original Hilbert action trace. The arbitrary-Hilbert quantifier is retained; no finite-gap restriction is substituted.

### S22-022: Ordinary frequency divergence and arbitrary selected signed index

- The original renormalized frequency, pulled back through the actual image inverse, is continuous at the limiting image point. Adding four times the literal Hilbert-pair energy gives a frequency tending to positive infinity for every Hilbert coordinate approximation. This formula equals the actual ordinary frequency of any independently constructed original Hilbert family. The physical Hilbert ordinary frequencies therefore diverge along every such approximation, at every signed index.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.hilbert_coordinate_frequency_eq_ordinary`
- `NLS.ZakharovShabat.SourceSection20Data.tendsto_hilbert_coordinate_frequency_atTop`
- `NLS.ZakharovShabat.SourceSection20Data.tendsto_original_hilbert_ordinary_frequency_atTop`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.tendsto_finiteGapOrdinaryFrequency_atTop`
- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_fst`
- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_snd`

Select any signed index with the corresponding nonzero amplitude, including zero or a negative index; remove the printed positive-index restriction directly. No infinite energy is substituted as a real frequency value at the limiting non-Hilbert point.

### S22-023: Oscillating subsequence and small times

- Any frequency sequence tending to infinity has a strictly increasing subsequence with successive gaps at least pi/T. The times pi/gap are positive and at most T, with relative phase exactly minus one and thus phase difference of modulus at least one. Reflecting the times realizes the physical first-coordinate sign on [-T,T], both for the original finite-gap application and for arbitrary real Hilbert coordinate approximations.

Public declarations:

- `NLS.Dynamics.exists_frequency_gap_subsequence`
- `NLS.Dynamics.exists_phase_separating_times`
- `NLS.ZakharovShabat.SourceSection20Data.exists_finiteGap_coordinate_separation`
- `NLS.ZakharovShabat.SourceSection20Data.exists_hilbert_coordinate_separation`

The original frequencies need not be monotone. The actual original inverse identity is eventually valid along arbitrary real coordinate approximations, so its fallback outside the image is not used to interpret the limiting argument.

### S22-024: Coordinate separation and failure of uniform trajectory convergence

- The difference of successive selected scalar trajectories is bounded below by the preceding amplitude norm minus the full sequence norm of the successive amplitude difference. Convergence and a nonzero limiting amplitude give the exact eventual half-amplitude lower bound. The arbitrary-Hilbert original-coordinate application retains physical signs and all signed indices. Existing nonextension conclusions for both components remain intact.

Public declarations:

- `NLS.Dynamics.norm_phase_pair_lower`
- `NLS.Coeff.exists_phase_separated_subsequence`
- `NLS.ZakharovShabat.SourceSection20Data.exists_finiteGap_coordinate_separation`
- `NLS.ZakharovShabat.SourceSection20Data.exists_hilbert_coordinate_separation`
- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_fst`
- `NLS.ZakharovShabat.SourceSection20Data.coordinate_nonextension_snd`

The original physical nonextension theorems retain their established agreement scopes. The new literal intermediate estimates supplement their positive proofs; no new refutation is introduced.

### S22-025: Transition to Theorem 18.5 via source wellposedness

- This transition states that the following source wellposedness corollary supplies the earlier Theorem18.5 result. Its three mathematical conclusions are compared in the next groups.

No new mathematical object or independent estimate is introduced here.

### S22-026: Corollary 22.2(i): both equations globally analytically wellposed

- For every 1<p<=2, both ordinary and renormalized NLS have global analytic wellposedness in the original all-smooth-approximation solution definition, witnessed by the actual original source flows.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.global_analytic_wellposedness`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_solutions`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_trajectories`

Analyticity is in the full uniform compact-time source norm, not merely pointwise time evaluation.

### S22-027: Corollary 22.2(ii): local and small-data global renormalized solutions

- At every real source above two, one positive time and open source neighborhood give actual local renormalized solutions and analytic uniform trajectories. One invariant open neighborhood of zero containing a positive source-norm ball has global solutions for every time.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.local_physical_solutions`
- `NLS.ZakharovShabat.SourceSection20Data.local_analytic_wellposedness`
- `NLS.ZakharovShabat.SourceSection20Data.small_global_physical_solutions`

The same small-data domain is fixed before all horizons. It does not assert global source solvability for arbitrary large data above two.

### S22-028: Corollary 22.2(iii): source nonextension including endpoint targets

- At each non-Hilbert source, the ordinary physical solution map has no continuous extension agreeing with all smooth solutions into any target exponent q>=1, including infinity, for every positive horizon. Forward and symmetric intervals are covered.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.finiteGap_source_nonextension`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all_symmetric`

The separate finite-gap-only theorem keeps finite targets q>=2, which includes all finite q>=p>2. The endpoint-inclusive theorem uses agreement with every smooth classical solution.

### S22-029: Source conjugation by the global Birkhoff diffeomorphism

- The original Birkhoff map is a global real analytic diffeomorphism for 1<p<=2. Conjugation through that same map supplies the two global physical source flows and analytic source trajectories.

Public declarations:

- `NLS.ZakharovShabat.SourceSection17OriginalData.global_inverse`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_solutions`
- `NLS.ZakharovShabat.SourceSection20Data.global_physical_trajectories`

The source solutions retain the original smooth-approximation definition; they are not redefined to be coordinate lifts.

### S22-030: Local image chart and one common time-neighborhood pair

- Openness of the original image and joint continuity produce one positive time and a common neighborhood of the initial datum on which every phase curve remains in the image. The original inverse then gives the local physical flow.

Public declarations:

- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.exists_local_renormalizedImageFlow`
- `NLS.ZakharovShabat.SourceSection20Data.local_physical_solutions`

The coordinate flow has initial domain a coordinate neighborhood V, rather than the source neighborhood U printed in this sentence.

### S22-031: Equation 4.17 and physical compact-time analytic trajectories

- Equation4.17 uses the same original inverse and original phase curve. For one common source neighborhood and compact time interval, it is an actual approximation solution and is analytic as a map into continuous source-valued paths.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.local_physical_solutions`

The full image condition is retained above two, and the path agrees with the physical inverse flow at every time.

### S22-032: Invariant small coordinate ball by norm preservation

- A positive ball in the complex coordinate space, restricted to its real form, is preserved by the phase norm. Its real decoding stays in the original open image. The inverse image is an invariant open source neighborhood containing a positive source-norm ball.

Public declarations:

- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.exists_small_renormalizedImageDomain`
- `NLS.ZakharovShabat.SourceAbelianMomentAtlas.exists_invariant_small_renormalizedFlow`
- `NLS.Birkhoff.norm_phaseFlow`

Correct the printed ambient space of the ball from source space to coordinate space. The formal bound accounts for the bounded real decoder.

### S22-033: One small source domain supports all time horizons

- The same original small source neighborhood is invariant and supports actual global solutions, compact-time analytic trajectory maps, joint time/source continuity and the group law, for every real horizon.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.small_global_physical_solutions`

Use that same U, not the unrelated earlier U-prime, in the all-horizon analytic statement.

### S22-034: Physical nonextension proof and finite-target composition scope

- The finite-target composition argument uses original source, Hilbert and target families and actual finite-gap classical agreement. A separate positive physical mass-gauge argument supplies all smooth-agreeing targets, including infinity, without requiring an infinity-exponent Birkhoff map.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.finiteGap_source_nonextension`
- `NLS.ZakharovShabat.SourceSection20Data.smooth_source_nonextension_all`

Do not attribute the endpoint result to the printed finite-target Birkhoff-composition proof. Keep finite-gap-only and all-smooth agreement scopes distinct.

### S22-035: Remark 22.3 exact solution characterization with corrected signs

- Every original approximation solution satisfies the physical coordinate law. Conversely, a continuous curve with that law supplies its own original image condition, so the guarded original inverse gives the same actual approximation solution. This works for every finite p>1 and includes T=0.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.remark22_3`
- `NLS.ZakharovShabat.SourceSection20Data.renormalized_solution_coordinates`
- `NLS.ZakharovShabat.SourceSection20Data.trajectory_domain_iff_solution`

Retain the existing physical phase-sign correction. The initial condition is forced by the coordinate law at zero; no additional differentiability or restriction-space hypothesis is introduced.

### S22-036: Uniqueness in the full continuous-curve class

- Two continuous curves on the compact interval with the same initial source and corrected original coordinate law agree everywhere on that interval. Hence uniqueness holds in the whole stated continuous-curve class.

Public declarations:

- `NLS.ZakharovShabat.SourceSection20Data.coordinate_curve_unique`

The proof uses the original approximation-solution characterization and uniqueness; it does not redefine the solution concept.

### S22-037: Contextual comparison with cited restriction norm spaces

- The comparison with Grunrock and Herr restriction spaces is literature context.

The original project proves continuous-curve uniqueness; the separate cited restriction-space construction is not claimed formalized.

## Evidence and validation

The [original Section 22 construction](../NLS/ZakharovShabat/SourceSection22Original.lean)
retains the original source, moment, root and Birkhoff-map families. The
[Hilbert coordinate extension](../NLS/ZakharovShabat/SourceSection22HilbertCoordinates.lean)
also preserves the literal arbitrary-Hilbert approximation quantifier.
This comparison read 59 complete module bodies and resolved 72 declarations.
It reconciles the two earlier named comparisons and the separately indexed
Remark 22.3, together with their broad proof ranges and the subsequent positive
estimate comparisons. Historical corrections and refutation records are retained.
Reading every transitive proof dependency again is not claimed. No new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit b542c02bbaaeec246fc3bc2bf5f200c0c5088341: 8,571 build jobs, 7,668 public examples and the transitive axiom audit of 44,671 NLS declarations, with 21 inherited warnings and zero new. This step changes source-comparison documentation and its integrity record. Source hashes, all 72 declaration references, the review index and local documentation links are checked again. These checks do not certify complete formalization.

Next: the ordered assertion comparison for Section 23.
