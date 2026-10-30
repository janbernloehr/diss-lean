# Section 14 ordered assertion comparison

All eighteen Section 14 overview passage groups are classified: thirteen matched, one with an explicit common-domain restriction, one partial external comparison and three contextual remarks. The actual rectangular map retains the original root family, actions and integral-defined angles. The working Chapter 3 domain V is an open restriction containing the entire real locus, not an asserted equality with an arbitrarily fixed earlier W. All five Theorem 14.1 properties hold on this constructed compatible domain, with global surjectivity only for 1<p<=2. Native weighted results supply the positive-smoothness extension. The precise comparison with the cited 2014 edition of [23] remains unresolved; the previously inspected 2013 conventions do not settle it. Historical open-problem and minimal-decay remarks and related-equation references are contextual. The proof outline uses actual local inverses, finite-gap collision approximation, canonical mode preimages and compactness, with no new refutations. This completes classification of the overview passages, not proof of every source attribution, all later Chapter 3 arguments or the dissertation. Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, Appendix G.2 norm interpretation and the broader source inventory retain their qualifications.

Source: printed pp. 73–74, text lines 5919–6008. Line numbers count newline characters,
preserving form-feed characters. Both rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S14-001 | 5921–5928 | The common action domain and exact factorization 4I=xi^2*gamma^2. | matched |
| S14-002 | 5930–5933 | The literal theta and analytic closed-gap locus. | matched |
| S14-003 | 5934–5938 | Equation (3.1), including exact phase and positive sine orientation. | matched |
| S14-004 | 5940–5945 | Analytic extension and a full sequence map on a common neighborhood. | corrected |
| S14-005 | 5947–5950 | Theorem 14.1(i): analytic lp-valued Birkhoff map. | matched |
| S14-006 | 5954–5954 | Theorem 14.1(ii): compatibility on the entire complex exponent intersection. | matched |
| S14-007 | 5956–5956 | Theorem 14.1(iii): canonical rectangular coordinates. | matched |
| S14-008 | 5958–5961 | Theorem 14.1(iv): injectivity, local inverse and open dense image. | matched |
| S14-009 | 5963–5965 | Theorem 14.1(v): global bi-real-analytic inverse for 1<p<=2. | matched |
| S14-010 | 5968–5968 | Remark 14.2(i): identification with the cited Hilbert-space construction. | partial |
| S14-011 | 5970–5970 | Remark 14.2(ii): the stated open question above two. | contextual |
| S14-012 | 5972–5973 | Remark 14.2(iii): positive-smoothness extension. | matched |
| S14-013 | 5983–5987 | Remark 14.2(iv): isolated spectral pairs and the proposed minimal decay. | contextual |
| S14-014 | 5989–5991 | Proof outline: analytic extension of the rectangular formulas. | matched |
| S14-015 | 5992–5996 | Proof outline: sequence analyticity, canonicity and injectivity from Hilbert data. | matched |
| S14-016 | 5997–5999 | Proof outline: Fredholm argument and the local diffeomorphism. | matched |
| S14-017 | 6000–6002 | Proof outline: finite angle-flow reductions give surjectivity below two. | matched |
| S14-018 | 6003–6008 | Related-results paragraph and external equation references. | contextual |

## Compared passages

### S14-001: The common action domain and exact factorization 4I=xi^2*gamma^2.

- Intersect the retained Section 12 domain with the normalized-action domain supplied from its own preceding Section 11 data. This open intersection contains the entire real locus and retains the original indexed actions, principal roots and normalized psi family.
- The actual indexed action agrees with the constructed complex action there. Write a for the analytic normalized-action factor, equal to I/gamma^2 off the closed-gap locus. The identities I=gamma^2*a and xi^2=4*a give the displayed identity also at collapsed complex gaps, without dividing by a zero gap.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma11_1Data.normalizedActions`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.factorization`
- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_sq`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_coordinate_domain`

Matched on a common neighborhood chosen for these objects. The Section 11 root neighborhood need not equal the preceding domain; S14-004 records the subsequent common-domain restriction explicitly.

### S14-002: The literal theta and analytic closed-gap locus.

- Theta is the original eta-plus-beta sum, with local analytic representatives modulo pi on its own open-gap locus. All these data restrict to the chosen common neighborhood.
- Z_n is exactly the zero set of the actual squared canonical gap. Its defining scalar function is complex analytic and its zero set is relatively closed. This supplies the analytic-subvariety assertion in the sense of a set defined by an analytic equation.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.original_theta_common_domain`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus`
- `NLS.ZakharovShabat.sourceActionGapZeroLocus_eq_preimage`
- `NLS.ZakharovShabat.SourceLemma11_1Data.squared_gap_analytic`
- `NLS.ZakharovShabat.SourceLemma11_1Data.gapZeroLocus_isClosed`

No smooth-manifold or nonsingularity assertion about Z_n is inferred, and no theta value at its own collapsed gap is required.

### S14-003: Equation (3.1), including exact phase and positive sine orientation.

- The left-endpoint model normalization identifies gamma*exp(i*eta) exactly with the constructed terminal coordinate. The exact product identity identifies the negative phase as well.
- Multiplication by the principal xi and the beta correction gives x=(xi*gamma/sqrt(2))*cos(theta) and y=(xi*gamma/sqrt(2))*sin(theta) at every complex open gap. The actual sequence coordinates have these same evaluations.
- This uses the original 2*pi integral class to fix the phase; a local theta representative modulo pi alone would not fix the sign of the rectangular pair.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_plus`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_signed`
- `NLS.ZakharovShabat.SourceLemma12_12Data.birkhoffWeighted_original_formula`
- `NLS.ZakharovShabat.SourceLemma12_12Data.birkhoffXY_original_formula`
- `NLS.ZakharovShabat.SourceSection14OriginalData.rectangular_formula`

The formula and normalization match, with the actual integral-defined theta. The later exponential sine display is reviewed in Section 15.

### S14-004: Analytic extension and a full sequence map on a common neighborhood.

- The original gap-weighted eta coordinates extend analytically through every collapsed complex gap in the retained angular domain. Intersecting with the normalized-action neighborhood gives analytic x and y and the exact indexed-action radius.
- Uniform local spectral bounds produce the full lp pair on a union of neighborhoods of all real sources. A further union of real-centered balls provides compatible exponent domains. The final V is open, contains the entire real locus and lies inside the preceding angular W; the map functions and normalized root family remain the same.
- The precise common-domain formulation is to choose this restricted V as the working neighborhood for Chapter 3. Existing proofs do not assert extension of the full sequence map to every point of an arbitrarily fixed earlier W.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_coordinate_domain`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_map`
- `NLS.ZakharovShabat.sourceSection14`
- `NLS.ZakharovShabat.SourceSection14OriginalData.restrict`

Domain correction made explicit: the printed reuse of W is implemented by a common restriction V, not an equality with the earlier W. This is a proved neighborhood containing the full real locus. No counterexample or new refutation is added.

### S14-005: Theorem 14.1(i): analytic lp-valued Birkhoff map.

- For every finite p>1 the constructed map is complex analytic as a map into the product of two actual lp Banach spaces on the common V. Consequently it is real analytic there.
- Uniform spectral majorants prove sequence membership and exact scalar evaluations before the coordinatewise analytic criterion is applied. The total sequence constructor never uses its zero fallback on V.
- Its real restriction takes values in the two real sequence spaces and its complex inclusion equals the complex map, as full sequences.

Public declarations:

- `NLS.ZakharovShabat.sourceSection14`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.coordinates`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_complex_inclusion`
- `NLS.ZakharovShabat.sourceBirkhoffSequence_analytic_of_uniform_bound`

Matched on the constructed Chapter 3 neighborhood from S14-004, with full Banach-valued analyticity rather than only scalar analyticity.

### S14-006: Theorem 14.1(ii): compatibility on the entire complex exponent intersection.

- For p<=q, coefficient-preserving inclusions identify the entire output sequences at every point of the constructed complex overlap, even for independently chosen normalized families.
- A point in two real-centered balls has its real-type projection in their convex overlap. Full analytic germs agree at that real projection, and analytic uniqueness propagates equality across the overlap.
- There are no reality, open-gap or connected-overlap premises on the compared source. The equality also gives one full-map germ and equality of the complete Frechet derivatives after inclusion.

Public declarations:

- `NLS.ZakharovShabat.sourceRealPart_exponent`
- `NLS.ZakharovShabat.sourceRealBallCore`
- `NLS.ZakharovShabat.SourceSection14OriginalData.map_real_exponent`
- `NLS.ZakharovShabat.SourceSection14OriginalData.map_exponent_on_realBallCore`
- `NLS.ZakharovShabat.SourceSection14Data.exponent`
- `NLS.ZakharovShabat.SourceSection14Data.eventually_map_exponent`
- `NLS.ZakharovShabat.SourceSection14Data.fderiv_exponent`

The source writes q<p; the public theorem uses the reverse variable names p<=q for the same inclusion direction, and also includes equal exponents.

### S14-007: Theorem 14.1(iii): canonical rectangular coordinates.

- The actual x and y coordinate derivatives have regular Fourier representatives. Their physical pairings are xx=0, xy=-Kronecker and yy=0, with frequency reversal and factor -i in the absolutely convergent Fourier sum.
- Analytic rectangular coordinates and density of the simultaneous open-gap locus extend the brackets through every real collapsed gap. Restriction with identical regular coefficients covers 1<p<2.

Public declarations:

- `NLS.ZakharovShabat.SourceSection14OriginalData.canonical`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.lemma15_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.fderiv_coordinates`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.mixed_fourier_canonical`
- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.birkhoff_sourceBracket_canonical`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_birkhoff_regular_canonical`

Canonical has the meaning specified by Lemma 15.3: all real sources, all signed index pairs and every finite p>1. It does not assert a Poisson pairing on arbitrary nonregular cotangents below two.

### S14-008: Theorem 14.1(iv): injectivity, local inverse and open dense image.

- The real map is injective on the complete real source space. Its actual real Jacobian is a bounded equivalence at each point, and the inverse-function theorem gives analytic local inverses with both inverse identities.
- The local homeomorphism and injectivity give an open embedding. Every finite target truncation is attained: above two use its Hilbert preimage and exponent inclusion; at or below two use surjectivity. Truncations converge in the actual target norm, giving density.

Public declarations:

- `NLS.ZakharovShabat.SourceSection14OriginalData.real_geometry`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_1`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_2`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_isOpenEmbedding`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.truncatePair_mem_real_map_range`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_open_dense_range`

All four assertions match for every finite p>1. Open dense image is not promoted to surjectivity above two.

### S14-009: Theorem 14.1(v): global bi-real-analytic inverse for 1<p<=2.

- An arbitrary exponent-p target has a Hilbert preimage. Finitely many admissible angle-flow moves make the selected actions small enough that the output lies in the image of the exponent-p local inverse at zero.
- The total source displacement of these moves belongs to exponent p. Hilbert injectivity identifies the reduced source with the exponent-p preimage, and adding back the displacement recovers the original source in p.
- The resulting actual map is a homeomorphism onto the whole real target. Its global inverse agrees locally with each analytic local inverse and is therefore real analytic everywhere.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.realHomeomorph`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.realHomeomorph_symm_analytic`
- `NLS.ZakharovShabat.SourceSection14OriginalData.global_inverse`

The full onto and inverse assertions match exactly for 1<p<=2. No stronger exponent range is inferred.

### S14-010: Remark 14.2(i): identification with the cited Hilbert-space construction.

- The current implementation constructs the physical Hilbert map, analytic global inverse, exact physical norm normalization, complex extension and literal action-angle formulas from the same original family.
- The existing comparison with inspected 2013 manuscript conventions is preserved. This ordered review does not establish identity with the exact 2014 edition cited as [23].

Public declarations:

- `NLS.ZakharovShabat.sourceSection14_physicalHilbert`

The mathematical Hilbert map is constructed, but the precise external-edition comparison remains unresolved. This row is not marked proved.

### S14-011: Remark 14.2(ii): the stated open question above two.

- This is the dissertation's historical statement about surjectivity for p>2. The formalization asserts only open dense image in that range.

No current literature-status claim, proof of surjectivity or proof of failure of surjectivity is made.

### S14-012: Remark 14.2(iii): positive-smoothness extension.

- The same constructed original family supplies native weighted maps. The half-scale spectral weight gives exactly (1+abs(n))^t on the period-one Fourier lattice, for every real t>=0.
- The full weighted maps are analytic on open complex neighborhoods, retain their original raw coefficients, and agree on entire complex exponent overlaps. Their actual coordinate derivatives satisfy the canonical relations, and the maps have analytic two-sided local inverses at every weighted real source.
- For Sobolev weights the real image is open and dense at every finite p>1. Exact source-output regularity identifies its range with the preimage of the unweighted range. For 1<p<=2 the resulting native weighted homeomorphism has analytic forward and inverse maps.

Public declarations:

- `NLS.ZakharovShabat.sourceSobolevSpectralWeight_even`
- `NLS.ZakharovShabat.sourceSection14_weighted_complex_analytic`
- `NLS.ZakharovShabat.sourceSection14_weighted_complex_compatible`
- `NLS.ZakharovShabat.sourceSection14_weighted_canonical`
- `NLS.ZakharovShabat.sourceSection14_weighted_real_local_inverse`
- `NLS.ZakharovShabat.sourceSection14_sobolev_open_dense`
- `NLS.ZakharovShabat.sourceSection14_sobolev_global_analytic_inverse`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.originalWeightedRealMap_sobolev_range`

The positive-smoothness extension matches with the original coefficient and norm conventions. Density and global surjectivity here are asserted for Sobolev weights; no global onto assertion for arbitrary spectral weights or p>2 is inferred.

### S14-013: Remark 14.2(iv): isolated spectral pairs and the proposed minimal decay.

- This paragraph explains the role of isolated asymptotic eigenvalue pairs in the preceding construction and proposes Fourier decay as a minimal requirement.
- The minimality wording is heuristic. It is not an additional theorem excluding all constructions without that decay.

Retained as mathematical motivation, with no new necessity theorem or refutation requested.

### S14-014: Proof outline: analytic extension of the rectangular formulas.

- Exact original endpoint phases identify equation (3.1) off the closed-gap locus. Original annular formulas extend the weighted phases holomorphically through complex collapsed gaps, and the action-root and beta factors give the rectangular extensions.
- The sequence construction and common restriction are those recorded in S14-004. Real collapsed gaps give zero rectangular coordinates; no vanishing claim at arbitrary complex collapsed gaps is made.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_coordinate_domain`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_map`

The analytic-extension method matches on the chosen common neighborhood. The cited external proof is not independently certified.

### S14-015: Proof outline: sequence analyticity, canonicity and injectivity from Hilbert data.

- A common neighborhood bounds xi, the beta correction and both spectral displacement sequences. The actual x and y bounds use C=2*A*Cz*exp(H), giving locally bounded lp sequences and full sequence analyticity.
- The established action-angle brackets, density of open gaps and exponent restriction give the rectangular canonical identities. The implementation proves the Hilbert theorem internally rather than importing it as an axiom.
- For injectivity above two, two distinct preimages of one output have local inverse branches. Truncating the common output produces distinct finite-gap preimages with the same truncated output. Their Hilbert realizations contradict the proved Hilbert injectivity. Below two, direct exponent inclusion suffices.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_local_birkhoffSequence_analytic`
- `NLS.ZakharovShabat.sourceBirkhoffSequence_analytic_of_uniform_bound`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_finiteGap_collision_mem_open`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbert_collision_of_collision`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbert_real_map_bijective`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_2`

The outline is supported with the needed local-inverse step spelled out. Injectivity is not inferred from continuity and dense-set injectivity alone.

### S14-016: Proof outline: Fredholm argument and the local diffeomorphism.

- The actual Jacobian is the exact free Fourier equivalence plus a compact operator. Finite-gap row majorants give finite-rank approximations in operator norm; finite-gap density and continuity extend compactness to every real source.
- For p>=2 the canonical relations construct actual preimages of each output mode, giving dense range. The compact-perturbation Fredholm alternative then gives bijectivity. For p<2, exponent compatibility transfers a kernel vector to the Hilbert case, and the same compact alternative gives surjectivity.
- The real derivative is a bounded equivalence and the inverse-function theorem supplies both analytic inverse germs at every real point.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_jacobianRemainder_real`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.isCompactOperator_normalizedJacobian_sub_id`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_single_preimages`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_denseRange`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.normalizedJacobian_bijective`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_injective_of_le_two`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.jacobian_bijective_all_exponents`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_1`

The Fredholm conclusion matches. The review records the implementation's precise order: mode preimages and compactness imply invertibility; it does not attribute injectivity to the canonical relations alone.

### S14-017: Proof outline: finite angle-flow reductions give surjectivity below two.

- The moves are generated by the actual original theta Hamiltonian. They lower the selected action at unit speed and preserve every unselected rectangular coordinate.
- Each move stops strictly before its selected action vanishes. Finitely many moves achieve any prescribed positive bounds on a finite set of actions; no move is needed for an already small or collapsed action.
- The stronger-space displacement theorem and the local inverse at zero complete the surjectivity reduction without assuming the arbitrary target already has an exponent-p preimage.

Public declarations:

- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.exists_hilbertActionReductionSequence_small_actions`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.hilbertActionReductionSequence_mem_exponent_iff`
- `NLS.ZakharovShabat.SourceSection16OriginalData.equation3_9`
- `NLS.ZakharovShabat.SourceSection16OriginalData.lemma17_4`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.proposition17_3`

The method matches, with the previously corrected inward flow orientation retained. No new sign counterexample or refutation is added; the attribution to [36] is contextual.

### S14-018: Related-results paragraph and external equation references.

- The references to other dNLS constructions, KdV, modified KdV and Toda describe related literature. They are recorded as external attributions, not new dNLS implementation requirements.

This pass does not formalize those other equations or independently certify the cited results. The exact [23] comparison remains the partial row S14-010.

## Evidence and validation

The [original formula](../NLS/ZakharovShabat/SourceBirkhoffOriginalFormula.lean)
and [original sequence map](../NLS/ZakharovShabat/SourceBirkhoffOriginalMap.lean)
feed the [compatible Section 14 construction](../NLS/ZakharovShabat/SourceSection14.lean).
Its [original-family interface](../NLS/ZakharovShabat/SourceSection14Original.lean)
retains the canonical and inverse statements. The
[native weighted inverse results](../NLS/ZakharovShabat/SourceSection14WeightedRealInverse.lean)
supply the positive-smoothness extension.

This comparison freshly inspected 49 module bodies and resolved 70 public declarations.
It adds no Lean theorem, definition, example or refutation. The full transitive dependency
graph is covered by the reused axiom audit, not a fresh semantic reading of every dependency.

This documentation-only step reuses the exact Lean and dependency snapshot of commit `5e8a261`. The completed full check on that snapshot passed 8,557 build jobs, 7,631 public examples and the transitive axiom audit of 44,598 NLS declarations, with 21 inherited warnings and no new warnings. No new full build is claimed. Current source hashes, declaration references, review integrity and documentation links are checked separately.

Continue in source order with Section 15, Analyticity. The exact [23] comparison remains open.
