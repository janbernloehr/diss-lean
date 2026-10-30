# Section 15 ordered assertion comparison

All fifteen Section 15 passage groups are classified: twelve matched and three with explicit corrections or a sufficient estimate replacement. The corrected opening sine difference is retained. At a complex collapsed gap outside its midpoint exactly one signed coordinate is nonzero. The Banach-analyticity argument uses a locally uniform beta bound; fixed-potential beta decay is not promoted to a uniform little-o rate on a fixed neighborhood. Lemma 15.1 holds throughout the unchanged angular W. Equation (3.2) and Theorem 15.2 use the common Chapter 3 domain V inside W containing the full real locus. Lemma 15.3 retains the actual regular coordinate derivatives at all real sources and finite p>1. Direct annular extensions and internal analytic/canonical proofs supply the results without independently certifying the cited [23] lemmas. This completes the ordered Section 15 comparison, not the exact 2014 external-edition comparison or the dissertation. Section 7 physical NLS Dirichlet motion and unrestricted psi characterization, Appendix G.2 norm interpretation and the broader source inventory retain their qualifications. No new refutation is added.

Source: printed pp. 74–75, text lines 6012–6106. Line numbers count newline characters,
preserving form-feed characters. Both rendered pages were inspected. Line 6042 appears
in two groups because it finishes the outside-gap claim and starts the estimate.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S15-001 | 6014–6018 | Opening exponential coordinates with the corrected sine difference. | corrected |
| S15-002 | 6019–6020 | Analytic action roots and beta corrections on the common domain. | matched |
| S15-003 | 6022–6024 | The literal two gap-weighted original phases. | matched |
| S15-004 | 6026–6026 | Discontinuities of the indexed gap and original eta phase. | matched |
| S15-005 | 6027–6034 | Local analytic unordered endpoints and open-gap analyticity. | matched |
| S15-006 | 6035–6039 | Limits at complex collapsed gaps and their signed nonvanishing. | corrected |
| S15-007 | 6041–6042 | The outside-gap locus is open and has no real sources. | matched |
| S15-008 | 6042–6045 | Local uniform spectral bounds and continuity through collapse. | matched |
| S15-009 | 6055–6059 | Analytic extension across the collapsed locus. | matched |
| S15-010 | 6061–6067 | Lemma 15.1 with a common neighborhood and index-uniform estimate. | matched |
| S15-011 | 6070–6074 | Equation (3.2) for the actual sequence entries. | matched |
| S15-012 | 6076–6083 | Precise local bounds sufficient for Banach-valued analyticity. | corrected |
| S15-013 | 6085–6092 | Theorem 15.2 for the full real map and its complex extension. | matched |
| S15-014 | 6094–6101 | Lemma 15.3 for every real source, exponent and signed index pair. | matched |
| S15-015 | 6103–6106 | Canonical identities by continuity and exponent restriction. | matched |

## Compared passages

### S15-001: Opening exponential coordinates with the corrected sine difference.

- The original cosine and positive sine orientation give a sum in x and a difference in y, with denominators sqrt(8) and i*sqrt(8), respectively.
- The existing exact original-phase formula and equation (3.2) retain that difference. The opening printed plus in y is replaced directly; no new sign counterexample is added.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.birkhoffXY_original_formula`
- `NLS.ZakharovShabat.SourceSection15OriginalData.equation3_2`

This retains the established correction and the same integral-defined phase. The exponential phase formula is used off the selected collapsed-gap locus.

### S15-002: Analytic action roots and beta corrections on the common domain.

- The principal normalized-action root is analytic on the Section 11 common action domain, including its collapsed gaps. The original beta correction is analytic throughout the retained angular W.
- Their intersection supports the rectangular scalar formulas; the full sequence map uses the Chapter 3 neighborhood V inside W established in the Section 14 comparison.

Public declarations:

- `NLS.ZakharovShabat.SourceTheorem11_2Data.root_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.beta_original_series`
- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_birkhoff_coordinate_domain`

Throughout this ledger W denotes the retained angular domain and V the constructed common Birkhoff domain. Both contain the entire real locus. No equality with an arbitrarily fixed earlier W is asserted.

### S15-003: The literal two gap-weighted original phases.

- On W away from the selected closed gap, both constructed coordinates equal gamma_n*exp(plus_or_minus i*eta_n) for the actual original eta integral.
- The endpoint normalization fixes the positive phase exactly, and the product identity fixes the negative phase. This is an equality of complex values, not just agreement modulo pi.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_plus`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_signed`

At collapsed gaps the analytic coordinate formula supplies the value; no angle value or division by the gap is required there.

### S15-004: Discontinuities of the indexed gap and original eta phase.

- The existing positive source assertion gives open central-gap potentials arbitrarily close to zero where both the labeled gap and exp(i*eta) fail to be continuous within the original open-gap domain.
- Continuity of the phase modulo 2*pi would imply continuity of its exponential, so the exhibited exponential discontinuity supplies the stated phase discontinuity.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.exists_original_gap_eta_phase_discontinuity`
- `NLS.ZakharovShabat.SourceLemma12_12Data.original_gap_eta_phase_not_continuousOn`

This is an existential discontinuity statement. It asserts neither discontinuity at zero nor discontinuity at every source or every index. The existing proof is reused; no new witness or refutation is added.

### S15-005: Local analytic unordered endpoints and open-gap analyticity.

- At any complex source with nonzero selected gap, an analytic square root of the squared half-gap has the prescribed base value. Adding and subtracting it from the analytic midpoint gives analytic local endpoints with the exact unordered pair of canonical endpoints.
- The original weighted phases agree with the analytic annular coordinate formulas. These formulas prove the claimed open-gap analyticity and also extend across the collapsed locus.

Public declarations:

- `NLS.ZakharovShabat.exists_local_sourceAnalyticHalfGap`
- `NLS.ZakharovShabat.sourcePeriodicEndpoint_pair_eq_of_halfGap_sq`
- `NLS.ComplexAnalysis.exists_local_analytic_squareRoot`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`

Local analytic endpoints need not agree with one global canonical labeling. The required result is proved internally; this does not certify the exact external [23] Lemma 16.1 text.

### S15-006: Limits at complex collapsed gaps and their signed nonvanishing.

- The original phases converge to their analytic extension along every converging net eventually in W with nonzero selected gap, hence along the sequences in the source.
- At a collapsed gap, both signed values vanish exactly when the Dirichlet root equals the midpoint. If it lies outside the collapsed segment, exactly one signed value is nonzero and the other is zero.
- This is the positive replacement for the unqualified nonzero-limit wording. The exact identity z_plus*z_minus=gamma^2 remains valid through collapse.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_phase_limit`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_collapsed_pair_zero_iff`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_collapsed_pair_exactly_one_nonzero`
- `NLS.ZakharovShabat.sourceGapWeightedEtaCoordinate_mul`

The review does not select a sign globally or construct another potential witnessing the correction. The existing positive classification suffices.

### S15-007: The outside-gap locus is open and has no real sources.

- F_n is the subset of W where the actual Dirichlet root avoids its actual periodic segment. Analytic symmetric gap data and the analytic Dirichlet root make this subset open in the full complex source space.
- Real interlacing places the Dirichlet root inside the segment at every real source, so F_n is disjoint from the entire real locus.

Public declarations:

- `NLS.ZakharovShabat.sourceDirichletOutsideGap`
- `NLS.ZakharovShabat.SourceLemma12_12Data.dirichletOutsideGap_original_open`
- `NLS.ZakharovShabat.disjoint_sourceDirichletOutsideGap_realType`
- `NLS.ZakharovShabat.exists_joint_neighborhood_avoids_sourcePeriodicSegment`

Line 6042 also starts the estimate reviewed in S15-008; this is an intentional overlap of source ranges.

### S15-008: Local uniform spectral bounds and continuity through collapse.

- The annular remainder bound is 3*r*(pi*rho^2*M/(rho-r)^3). A bound B for that remainder gives |z_sigma| <= 4*exp(B)*(|gamma|+|mu-tau|) for every |sigma|<=1.
- Uniform tail charts use fixed radii r=pi/16, R=pi/8, rho=3*pi/32 and the original diagonal numerator bound. Intersecting finitely many remaining charts gives one neighborhood and one positive constant for all signed indices.
- The directly analytic formulas are continuous across every complex collapsed gap. They retain the original phase values wherever the gap is open.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularJointAnnulusChartData.norm_etaRemainder_le_of_chart_bound`
- `NLS.ZakharovShabat.norm_sourceGapWeightedEtaCoordinate_le_of_remainder_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_tail_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_uniform_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`

All estimates hold near every complex point of W, not only near real sources. The published constants are the proven sufficient constants; no optimality or new refutation is claimed.

### S15-009: Analytic extension across the collapsed locus.

- The omitted-root product is nonzero at the Dirichlet terminal. Dividing the actual anti-discriminant by twice that product gives the analytic sine numerator without a half-gap denominator.
- Together with the analytic normalized remainder this gives an analytic coordinate on the whole chart. Its restrictions to collapsed-gap analytic curves are therefore analytic as well.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularJointAnnulusChartData.analyticOnNhd_dirichletEtaSineNumerator`
- `NLS.ZakharovShabat.SourceAngularJointAnnulusChartData.analyticOnNhd_gapWeightedEtaCoordinate`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`

The implementation proves a full neighborhood extension directly. It does not reproduce the source's weak-analytic-removability route or independently certify [23] Lemma A.6.

### S15-010: Lemma 15.1 with a common neighborhood and index-uniform estimate.

- For every finite p>1 and every complex point of the original W, one open source neighborhood and one constant bound both signs for all n. The local spectral estimate includes collapsed gaps and endpoint terminals.
- The actual gap and Dirichlet-midpoint displacement sequences are in lp and locally bounded. The estimate therefore gives actual lp-valued weighted phase sequences, their exact scalar evaluations and locally uniform sequence norm bounds.
- Bounded coordinatewise analyticity proves that these sequences are Banach-valued analytic throughout the unchanged angular W.

Public declarations:

- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeightedEta_original_analytic`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_uniform_bound`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_local_sequence`
- `NLS.ZakharovShabat.SourceSection15OriginalData.gap_sequence_analytic`

The original scalar lemma is matched, and the existing sequence theorem supplies the stronger realization needed later. The norm bound is also uniform over all complex sigma with |sigma|<=1.

### S15-011: Equation (3.2) for the actual sequence entries.

- On the common V the actual Birkhoff sequence entries equal xi/sqrt(8) times the sum of z_plus*exp(i*beta) and z_minus*exp(-i*beta), and xi/(i*sqrt(8)) times their difference.
- The equality is valid at every index, including complex collapsed gaps. Sequence membership is proved, so the total sequence constructors never select their zero fallback on the stated domains.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.equation3_2`
- `NLS.ZakharovShabat.SourceLemma12_12Data.gapWeighted_original_sequence_apply`

The Chapter 3 common-domain restriction from S14-004 is retained. The z sequences themselves still exist on the larger angular W.

### S15-012: Precise local bounds sufficient for Banach-valued analyticity.

- The normalized-root error has the genuine locally uniform lp/2 plus l(1+) decomposition from Theorem 11.2. Taking the one-plus exponent equal to p and using lp/2 inclusion in lp supplies xi-1 in lp. The local root-sequence construction gives a uniform scalar root bound A near every real source.
- The original beta correction tends to zero as |n| tends to infinity at each fixed potential. The sequence-analyticity proof uses the separately proved bound |beta_n(psi)|<=B on one neighborhood for all n; it does not require a uniform little-o rate on that neighborhood.
- With the gap-coordinate constant Cz, the exact sufficient bound for each rectangular coordinate is 2*A*Cz*exp(B)*(|gamma_n|+|mu_n-tau_n|). Local lp norm bounds for the two spectral sequences give a common bound for the full rectangular pair.
- The proved bounded-coordinate analytic criterion then gives full Banach-valued analyticity. Taking the union of these complex neighborhoods of real sources gives the working V.

Public declarations:

- `NLS.ZakharovShabat.SourceTheorem11_2Data.locally_uniform`
- `NLS.ZakharovShabat.exists_local_sourceNormalizedActionRootDeviation_continuousMap`
- `NLS.ZakharovShabat.exists_local_uniform_sourceNormalizedActionRoot_bound`
- `NLS.ZakharovShabat.sourceAngularBetaCorrection_decay_of_bound`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_local_uniform_betaCorrection_bound`
- `NLS.ZakharovShabat.norm_sourceBirkhoffXY_le`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_local_birkhoffSequence_analytic`
- `NLS.ZakharovShabat.sourceBirkhoffSequence_analytic_of_uniform_bound`
- `NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise`

The estimate passage is replaced by the precise sufficient bounds. Fixed-potential beta decay is not promoted to a fixed-neighborhood uniform decay assertion, and the latter is not certified or refuted here. The needed analytic criterion is proved internally, without an external [23] Theorem A.4 axiom.

### S15-013: Theorem 15.2 for the full real map and its complex extension.

- For every finite p>1, the actual map from the complete real source space to the pair of real lp spaces is real analytic.
- It extends to the actual complex lp-pair-valued map on V, an open neighborhood of the entire real source locus. Complex inclusion of the real output equals the full complex output, not just each component after taking real parts.

Public declarations:

- `NLS.ZakharovShabat.sourceSection15_original`
- `NLS.ZakharovShabat.SourceSection15OriginalData.theorem15_2`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_analytic`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.real_map_complex_inclusion`

Matched with the established Chapter 3 domain convention V inside the earlier W. This does not assert a full Birkhoff sequence extension to every point of an arbitrarily fixed angular domain.

### S15-014: Lemma 15.3 for every real source, exponent and signed index pair.

- The actual sequence coordinate derivatives have regular Fourier representatives at every real source, including all collapsed gaps. Their pairings are xx=0, xy=-Kronecker and yy=0 for every pair of signed indices.
- The mixed bracket is the literal absolutely convergent Fourier sum with frequency reversal and factor -i. For p>=2 it equals the continuous physical source bracket on full cotangents; for 1<p<2 the regular representatives retain that same pairing.

Public declarations:

- `NLS.ZakharovShabat.SourceSection15OriginalData.lemma15_3`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.fderiv_coordinates`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.mixed_fourier_canonical`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.sourceBracket_canonical`

No unspecified closed-gap angle or bracket on arbitrary nonregular cotangents below two is assumed.

### S15-015: Canonical identities by continuity and exponent restriction.

- For p>=2 the continuous bilinear source bivector applied to the analytic coordinate derivatives gives continuous brackets. The action-angle identities on the dense simultaneous open-gap locus extend them to all real sources.
- Below two, the full coordinate derivatives restrict from the Hilbert exponent with identical regular Fourier coefficients and hence identical pairings. The resulting scalar bracket values are constant on the entire real source space, so they are real analytic.
- The implementation proves the needed canonical identities internally. It uses open-gap density directly at exponents at least two rather than taking the exact external Hilbert theorem as a premise.

Public declarations:

- `NLS.ZakharovShabat.SourceAngularThetaCommonDomainData.birkhoff_sourceBracket_canonical`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_birkhoff_regular_canonical_of_le`
- `NLS.ZakharovShabat.SourceAngularEtaLocalCommonDomainData.exists_birkhoff_regular_canonical`
- `NLS.ZakharovShabat.SourceBirkhoffMapComplexData.lemma15_3`

The mathematical conclusion and continuity/restriction mechanism are supplied. The proof route differs from the cited [23] Theorem 18.8 shortcut; the exact external edition comparison remains unresolved.

## Evidence and validation

The [original Section 15 interface](../NLS/ZakharovShabat/SourceSection15Original.lean)
combines the [uniform original bound](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalBound.lean),
[actual analytic sequences](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalSequence.lean)
and [collapsed-gap classification](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalCollapsed.lean).
The [local Birkhoff construction](../NLS/ZakharovShabat/SourceBirkhoffSequenceLocal.lean)
uses the stated sufficient bounds; the [canonical theorem](../NLS/ZakharovShabat/SourceBirkhoffLemma15_3.lean)
identifies the actual coordinate derivatives.

This comparison freshly inspected 25 module bodies and reused 13 full readings from the
ordered Section 13 and Section 14 comparisons after verifying exact module hashes.
It resolves 51 public declarations and adds no Lean theorem, definition, example or refutation.
The full transitive dependency graph is covered by the reused axiom audit, not a fresh
semantic reading of every dependency.

This documentation-only step reuses the exact Lean and dependency snapshot of commit `399faae`. The completed full check on that snapshot passed 8,557 build jobs, 7,631 public examples and the transitive axiom audit of 44,598 NLS declarations, with 21 inherited warnings and no new warnings. No new full build is claimed. Current source hashes, declaration references, review integrity and documentation links are checked separately.

Continue in source order with Section 16, Jacobian. The exact cited 2014 construction comparison remains open.
