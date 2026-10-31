# Section 28 ordered assertion comparison

The ordered Section 28 comparison covers 30 groups on printed pp.117–119: 16 matched, eight directly corrected, four partial and two contextual, with no pending groups. Original indexed actions, exact weighted norms, the common connected L2-open domain before all weights and weight-dependent estimate neighborhoods are retained. The final complex chi bound 2048, action-gap bound 4608, real action bound 2^20 and complex action bound 2^21 are proved. Four complex intermediate passages remain partial: the reflected rational spectral bound, adjacent-disc comparison, central telescoping and enclosing-root ratio. The independent final bounds do not establish these printed arguments. The small-ball step directly uses the weighted norm. This comparison adds no Lean proof or refutation. Broader completeness and Appendix G.2 qualifications remain.

Source: printed pp. 117–119, text lines 9632–9914. Line numbers count
newline characters and preserve form feeds. All three rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| S28-001 | 9634–9639 | Weighted Sobolev motivation | contextual |
| S28-002 | 9641–9648 | Formula (5.14), local and bounded-set uniformity | matched |
| S28-003 | 9649–9656 | Original contour action and deleted product | matched |
| S28-004 | 9658–9669 | Gap shrinking and critical coordinate integral | matched |
| S28-005 | 9671–9677 | Common critical-coordinate bound and formula (5.15) | matched |
| S28-006 | 9682–9686 | Lemma 28.1 and its signed ratio | partial |
| S28-007 | 9688–9697 | Inclusive cutoff and product split | matched |
| S28-008 | 9700–9707 | Exterior endpoint localization and separation | corrected |
| S28-009 | 9709–9713 | Individual gap and small ratio | corrected |
| S28-010 | 9723–9729 | Root factor and critical displacement estimate | matched |
| S28-011 | 9731–9744 | Cauchy-Schwarz exterior sum | corrected |
| S28-012 | 9746–9751 | Weighted gap-tail budget | matched |
| S28-013 | 9753–9764 | Infinite exterior product constant 128 | matched |
| S28-014 | 9767–9780 | Central isolating discs and formula (5.16) | partial |
| S28-015 | 9783–9789 | Central telescoping product | partial |
| S28-016 | 9791–9796 | Enclosing-root ratio | partial |
| S28-017 | 9798–9802 | Inclusive boundary arithmetic | corrected |
| S28-018 | 9804–9808 | Final complex chi estimate | matched |
| S28-019 | 9819–9831 | Figure 5.1 disc geometry | contextual |
| S28-020 | 9834–9836 | Proposition 28.2 action-gap estimate | matched |
| S28-021 | 9839–9844 | Factor four in the action proof | corrected |
| S28-022 | 9847–9848 | Weighted cutoff for Theorem 23.4 | corrected |
| S28-023 | 9850–9854 | Weighted action tail and its boundary | corrected |
| S28-024 | 9856–9862 | Gap tail and norm budget | matched |
| S28-025 | 9864–9870 | Weighted summability and continuity | matched |
| S28-026 | 9872–9879 | Real central action estimate | matched |
| S28-027 | 9881–9887 | Real weighted action constant 2^20 | matched |
| S28-028 | 9889–9890 | Complex extension near nonzero real sources | matched |
| S28-029 | 9890–9897 | Near-zero bound and weighted norm | corrected |
| S28-030 | 9899–9901 | Complex weighted action constant 2^21 | matched |

## Compared passages

### S28-001: Weighted Sobolev motivation

- The introduction motivates gap estimates for general M1 weighted spaces; the actual weighted estimates keep the original indexed actions.

Public declarations:

- `NLS.ZakharovShabat.sourceSection28_original`
- `NLS.ZakharovShabat.sourceM1_gap_tail`

The historical assertion that no corresponding Hamiltonian identity is known is context, not a mathematical nonexistence theorem.

### S28-002: Formula (5.14), local and bounded-set uniformity

- The filled quantity 4*I_n/gamma_n^2-1 is realized by an actual l2 sequence, with one bound on a neighborhood before all indices.
- Compact decoding gives one bound before all real sources in each exact physical H1 ball, and more generally in every real M1 weighted ball.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.normalized_locally_uniform`
- `NLS.ZakharovShabat.SourceSection28Data.normalized_uniform_H1_ball`
- `NLS.ZakharovShabat.SourceSection11OriginalEstimates.section28_uniform_weighted_ball`
- `NLS.ZakharovShabat.isCompactOperator_normalizedWeightedSource`

At a collapsed gap use the filled analytic quotient; the expression is not totalized 0/0. Local complex uniformity and real bounded-ball uniformity have distinct quantifiers.

### S28-003: Original contour action and deleted product

- The original circuit action equals i/pi times the integral of the squared critical displacement divided by the selected standard root, multiplied by the actual deleted product.
- The derivative/canonical-root quotient has the exact -i selected-factor normalization.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_18Data.circuit`
- `NLS.ZakharovShabat.SourceEquation2_18Data.factorization`

All contours retain their admissibility and winding hypotheses. The deleted product is the existing spectral object.

### S28-004: Gap shrinking and critical coordinate integral

- The original action has the straight-gap integral with the exact 2/pi coefficient and critical coordinate.
- For a nonzero gap the normalized formula is the literal quotient 4*I_n/gamma_n^2. The analytic filled extension retains collapsed gaps.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_19Data.action_integral`
- `NLS.ZakharovShabat.SourceEquation2_19Data.normalized_integral`
- `NLS.ZakharovShabat.SourceEquation2_19Data.factorization`
- `NLS.ZakharovShabat.SourceEquation2_19Data.collapsed_limit`

Division is confined to nonzero gaps; the following bounds use the filled formulation throughout the common domain.

### S28-005: Common critical-coordinate bound and formula (5.15)

- A connected open restriction containing the entire real locus controls the critical coordinate by two before all indices.
- The closed-gap integral then gives the exact factor nine, including the filled collapsed extension.

Public declarations:

- `NLS.ZakharovShabat.exists_section28_critical_coordinate_neighborhood`
- `NLS.ZakharovShabat.section28_critical_coordinate_bound`
- `NLS.ZakharovShabat.SourceSection28Data.normalized_bound`

The common L2 neighborhood precedes all weights, sources and indices; the bound is not chosen point by point on each gap.

### S28-006: Lemma 28.1 and its signed ratio

- The final Lemma 28.1 estimate holds with 2048, signed indices, the inclusive bracket threshold and the exact physical H1 norm.
- The literal signed rational expression is replaced by absolute-index arithmetic where it is used as a scalar comparison.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.physical_H1_bounds`
- `NLS.ZakharovShabat.lemma281_ratio_le_eight`
- `NLS.ZakharovShabat.lemma281_ratio_le_two_of_exterior`

The printed signed ratio is not asserted. A complex spectral bound by the reflected rational expression is not verified by these scalar theorems; the central complex-product steps S28-014 through S28-016 remain qualified. The independent final 2048 theorem is fully proved. No new refutation is added.

### S28-007: Inclusive cutoff and product split

- The actual deleted infinite product is bounded by a uniform exterior-product bound times its finite central product over -N<m<N.
- Both exterior indices use the inclusive condition |m|>=N and the omitted index n is excluded. Cutoff zero makes the central product empty.

Public declarations:

- `NLS.ZakharovShabat.sourceCriticalRootRatioExtension_le_finite_core`
- `NLS.ZakharovShabat.sourceH1_exterior_product_le_128`

The transfer keeps the existing product limit and its omitted-domain hypothesis, and avoids division by central factors. The displayed product decomposition is used through this positive finite-core inequality.

### S28-008: Exterior endpoint localization and separation

- The endpoints and every point of the target closed gap lie in their pi/5 localization discs at the quadratic cutoff.
- The proof uses the explicit separation (3/2)*|m-n|, which suffices for the stronger coefficient-one exterior factor estimate.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_endpoints_localization`
- `NLS.ZakharovShabat.sourceH1_gap_point_norm_localization`
- `NLS.ZakharovShabat.localized_endpoint_separation`

The formal proof uses the stated 3/2 separation budget instead of separately publishing the intermediate 3*pi/5 separation display. Both complex sources and signed indices are retained.

### S28-009: Individual gap and small ratio

- The original individual weighted gap estimate has the exact sqrt(12) factor at the inclusive bracket cutoff.
- Exterior factor control is obtained directly from both localized endpoints and the critical-offset hypothesis.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_gap_individual`
- `NLS.ZakharovShabat.localized_critical_root_factor_le`
- `NLS.ZakharovShabat.sourceH1_exterior_critical_factor_le`

The original scalar small-ratio chain is not needed by this direct geometric proof. The replacement retains the full complex source scope and gives a stronger final single-factor coefficient.

### S28-010: Root factor and critical displacement estimate

- The standard-root square identity bounds the midpoint distance by root norm plus half-gap.
- An actual critical offset at most the gap length yields factor norm at most 1+gap/|m-n|, stronger than the printed coefficient 4/3.

Public declarations:

- `NLS.ZakharovShabat.midpoint_dist_le_root_add_half_gap`
- `NLS.ZakharovShabat.source_exterior_critical_factor_le`
- `NLS.ZakharovShabat.sourceH1_exterior_critical_factor_le`

Complex critical-offset hypotheses are explicit. They are provided in the chosen almost-real neighborhood; the geometry does not assume the source real.

### S28-011: Cauchy-Schwarz exterior sum

- Finite Cauchy-Schwarz bounds the sum of gap lengths times reciprocal distances by the product of the two square-budget roots.
- The formal proof uses unweighted gap budget three and a translated reciprocal-square budget 7/2, uniformly in the omitted index.

Public declarations:

- `NLS.ZakharovShabat.norm_finite_product_le_exp_sqrt_budgets`
- `NLS.ReciprocalSeries.sum_shifted_reciprocal_sq_le`
- `NLS.ZakharovShabat.M1_canonicalGap_finite_exterior_sq_le_three`

These directly proved budgets replace the particular weighted intermediate expression and give the same exterior constant 128. Finite products are transferred to the existing infinite limit.

### S28-012: Weighted gap-tail budget

- The inclusive weighted gap tail is bounded by 3*(1+N)^2 at every valid cutoff.
- Removing the linear weight gives at most three for every finite subset of exterior gap squares, including N=0.

Public declarations:

- `NLS.ZakharovShabat.M1_canonicalGap_tail_cutoff_budget`
- `NLS.ZakharovShabat.M1_canonicalGap_finite_exterior_sq_le_three`
- `NLS.ZakharovShabat.sourceM1_gap_tail`

The proof keeps the 1152/(1+N) remainder before using 8*norm(a)^2<=1+N; both components and signed boundary indices are retained.

### S28-013: Infinite exterior product constant 128

- Every finite exterior product is bounded by 128 for complex H1 sources with the explicit common critical-offset condition.
- The exponential square-budget estimate fits inside 128, and uniform finite bounds transfer to the actual deleted product with its finite central part.

Public declarations:

- `NLS.ZakharovShabat.sourceH1_exterior_product_le_128`
- `NLS.ZakharovShabat.exterior_product_exponential_budget`
- `NLS.ZakharovShabat.sourceCriticalRootRatioExtension_le_finite_core`

No replacement infinite-product candidate is introduced. The root-omitted domain and complex offset condition remain hypotheses of the transfer.

### S28-014: Central isolating discs and formula (5.16)

- The reviewed central-product theorem supplies a squared-norm enclosing-interval bound for real sources and real spectral points.
- The complex final estimate instead uses comparison with the projected real source and uniformly controlled distant modes.

Public declarations:

- `NLS.ZakharovShabat.sourceReal_finite_gap_product_sq_le`
- `NLS.ZakharovShabat.exists_local_sourceM1_gapFactor_bound`

The adjacent complex-disc distance comparison (5.16) is not proved by the reviewed support. The real theorem and independent complex final bound do not establish this printed intermediate assertion.

### S28-015: Central telescoping product

- Ordered real gaps admit a direct squared-product estimate using their actual roots and critical points.

Public declarations:

- `NLS.ZakharovShabat.sourceReal_finite_gap_product_sq_le`

The printed complex adjacent-factor telescoping estimate remains unverified. The real-only supporting theorem is not promoted to a complex statement.

### S28-016: Enclosing-root ratio

- Real central products can be controlled by one enclosing-interval ratio.
- The final complex 2048 theorem is available by a separate local comparison argument.

Public declarations:

- `NLS.ZakharovShabat.sourceReal_finite_gap_product_sq_le`
- `NLS.ZakharovShabat.exists_sourceH1_lemma28_1`

The particular complex ratio of the two enclosing standard roots on the printed disc geometry has not been established in this review. It is not inferred from the independent final estimate.

### S28-017: Inclusive boundary arithmetic

- At n>=N the scalar rational expression is bounded by 8*(N+1). At n>=N+1 the factor two is valid.
- With N<=8*P^2 the scalar chains give 8192 inclusively and 2048 strictly outside, respectively.

Public declarations:

- `NLS.ZakharovShabat.lemma281_ratio_le_eight`
- `NLS.ZakharovShabat.lemma281_ratio_le_two_of_exterior`
- `NLS.ZakharovShabat.lemma281_scalar_constant_inclusive`
- `NLS.ZakharovShabat.lemma281_scalar_constant_of_exterior`

Apply the scalar formulas to |n| for signed indices. These are positive arithmetic bounds, distinct from the actual spectral 2048 theorem; no new counterexample is added.

### S28-018: Final complex chi estimate

- The original complex deleted product has bound 2048*(1+P^2) on the full closed gap at the inclusive bracket threshold.
- One connected L2-open domain contains the whole real locus and is chosen before all M1 weights.

Public declarations:

- `NLS.ZakharovShabat.exists_sourceM1_gapFactor_neighborhood`
- `NLS.ZakharovShabat.SourceSection27Data.section28_original_chi_neighborhood`
- `NLS.ZakharovShabat.SourceSection28Data.physical_H1_bounds`

The proof uses the real-source margin, compact-gap continuity, a finite intersection and uniform distant control. It does not certify the printed complex disc-ordering chain.

### S28-019: Figure 5.1 disc geometry

- Figure 5.1 illustrates the disc geometry used to motivate the central comparison.

Public declarations:

- `NLS.ZakharovShabat.sourceReal_finite_gap_product_sq_le`

The picture is contextual; the unverified complex distance and root-ratio claims are recorded explicitly in S28-014 through S28-016.

### S28-020: Proposition 28.2 action-gap estimate

- The original indexed action has the exact 4608*(1+P^2)*gap^2 estimate for |n|>=8*P^2 in the physical H1 norm.
- The weighted-coordinate API also supports the inclusive bracket threshold, on the same retained domain.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.physical_H1_bounds`
- `NLS.ZakharovShabat.SourceSection28Data.chi_action_bound`

The division-free proof includes collapsed complex gaps and keeps the original action family.

### S28-021: Factor four in the action proof

- The factor-nine estimate and chi bound give 4*|I_n|<=18432*(1+P^2)*gap^2.
- Dividing by four then gives the proposition constant 4608.

Public declarations:

- `NLS.ZakharovShabat.SourceEquation2_19Data.section28_action_bound`
- `NLS.ZakharovShabat.SourceSection27Data.section28_original_chi_neighborhood`

The coefficient before division is 9*2048=18432. The final proposition retains 4608. This directly corrects the intermediate arithmetic.

### S28-022: Weighted cutoff for Theorem 23.4

- The real weighted proof chooses N=floor(8*norm(a)^2), hence N<=8*norm(a)^2<1+N.
- The tail theorem needs only 8*norm(a)^2<=1+N and therefore includes N=0 and zero sources.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_real_weighted_actions_summable_and_le`
- `NLS.ZakharovShabat.SourceSection28Data.weighted_action_tail_corrected`

Allow equality in the lower cutoff inequality; the printed strict lower inequality cannot be imposed at every integer value. The source space and final constants remain unchanged.

### S28-023: Weighted action tail and its boundary

- The original weighted action tail is summable and bounded by 4608*(1+norm(a)^2) times the weighted gap-square tail.
- Both sums retain the same inclusive boundary |n|>=N.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.weighted_action_tail_corrected`

The factor one and the boundary indices are kept directly. The norm is the original weighted norm, exactly the physical H1 norm for the order-one pi-Sobolev weight. Historical refutations remain unchanged.

### S28-024: Gap tail and norm budget

- The source Fourier-tail budget has coefficients six and 1152/(1+N).
- At a valid cutoff its sixth-power remainder is at most 144*norm(a)^4, giving the 6*norm(a)^2+144*norm(a)^4 scalar bound used in the action estimates.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_gap_tail`
- `NLS.ZakharovShabat.M1_canonicalGap_tail_six_144`
- `NLS.ZakharovShabat.SourceSection28Data.weighted_action_tail_budget`

The exact Fourier tail is retained before taking the norm contraction. The following scalar bound by 144*(1+norm(a)^2)*norm(a)^2 uses nonnegativity; no source-dependent constant is introduced.

### S28-025: Weighted summability and continuity

- The whole original weighted absolute action series converges throughout the weighted complex part of S.
- A locally bounded l1 realization with analytic coordinates makes its norm, the actual total weighted sum, continuous there.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.weighted_summable`
- `NLS.ZakharovShabat.SourceSection28Data.weighted_continuous`
- `NLS.ZakharovShabat.SourceSection11OriginalEstimates.section28_weighted_summable_continuousAt`

Continuity and summability hold on the full weighted part of the common domain, beyond the smaller domain needed for the explicit complex estimate.

### S28-026: Real central action estimate

- Real central actions are controlled by the exact mass trace and the weight at 16*norm(a)^2.
- The central finite sum uses -N<n<N and is empty at cutoff zero.

Public declarations:

- `NLS.ZakharovShabat.sourceM1_real_central_actions_le`
- `NLS.ZakharovShabat.source_norm_sq_le_weighted_realization`

The proof bounds each central weight directly by the continuous extension at 16*norm(a)^2; it does not need a separate evaluation at 2N-2 when N=0. The exact pair mass factor is retained before taking the weighted bound.

### S28-027: Real weighted action constant 2^20

- The real bound has exactly 2^20 times w[16*norm(a)^2]^2 times norm(a)^2.
- Every M1 weight, every real weighted source and zero are included, with absolute summability of the original indexed action series.

Public declarations:

- `NLS.ZakharovShabat.section28_real_weighted_action_bound`
- `NLS.ZakharovShabat.sourceM1_real_weighted_actions_normalized`
- `NLS.ZakharovShabat.weighted_action_two_pow_twenty_budget`

The original continuous weight extension and its argument are unchanged; the proof uses the stronger real action-gap coefficient 1536 in its scalar budget.

### S28-028: Complex extension near nonzero real sources

- At every nonzero real weighted source, strict positivity of the action scale and continuity extend the real estimate with doubled constant 2^21.
- The neighborhoods retain absolute summability.

Public declarations:

- `NLS.ZakharovShabat.exists_local_sourceM1Action_bound`

Zero is handled separately. The neighborhood is allowed to depend on the weight and the real source before the final union and connected restriction.

### S28-029: Near-zero bound and weighted norm

- For every complex weighted source in the common domain with 8*norm(a)^2<=1, the full original weighted action series is summable and at most 2^20*norm(a)^2.
- The new positive estimate implies the displayed source-shaped bound with the extra factor (1+norm(a))^4 and includes the equality boundary.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.weighted_action_small_ball`
- `NLS.ZakharovShabat.SourceSection28Data.weighted_action_tail_budget`

The right-hand quadratic factor is the original weighted norm, replacing the printed H1-only factor. The positive small-ball theorem passed the full checks and is committed and pushed. No new refutation is added.

### S28-030: Complex weighted action constant 2^21

- For each M1 weight a connected weighted-open neighborhood contains the entire real weighted locus and decodes into the common S.
- The original total weighted action sum is bounded there by the exact 2^21*w[16*norm(a)^2]^2*norm(a)^2.

Public declarations:

- `NLS.ZakharovShabat.SourceSection28Data.weighted_bound`
- `NLS.ZakharovShabat.SourceSection27Data.section28_weighted_neighborhood`
- `NLS.ZakharovShabat.sourceSection28_original`

The common L2 domain precedes all weights; the smaller estimate neighborhood may depend on the weight. This distinction, the original family and the exact weight argument are retained.

## Evidence and validation

The [original Section 28 package](../NLS/ZakharovShabat/SourceSection28Original.lean)
retains the common domain and original indexed actions. The
[complex gap bounds](../NLS/ZakharovShabat/SourceSection28GapBounds.lean) and
[weighted action estimates](../NLS/ZakharovShabat/SourceSection28WeightedActions.lean)
retain the named final constants. The
[corrected tail](../NLS/ZakharovShabat/SourceSection28TailEstimate.lean) and
[positive small-ball bound](../NLS/ZakharovShabat/SourceSection28SmallBall.lean)
keep inclusive cutoffs and the original weighted norm.

This comparison read 32 complete module bodies and resolves 58 public declarations.
It reconciles the prior named comparison and the positive proof step. Four
intermediate complex claims remain explicitly partial. The review does not
claim to have read every transitive dependency again. Existing refutations
remain unchanged; no new refutation is added.

The unchanged Lean snapshot reuses the successful full check at commit a315469d3324976a247ee8c1acbd8e60a99cd798: 8,582 build jobs, 7,692 public examples and an axiom audit of 44,706 NLS declarations, with 21 inherited warnings and zero new. All 58 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: the ordered Appendix A comparison. The
[broader completion qualifications](COMPLETENESS.md) remain.
