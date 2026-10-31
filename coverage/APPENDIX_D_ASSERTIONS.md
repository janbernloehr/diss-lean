# Appendix D ordered assertion comparison

The ordered Appendix D comparison covers thirty groups on printed pp.126-130: nineteen matched, ten directly corrected and one contextual. No partial or pending group remains in this local comparison. It retains literal symmetric products, joint analyticity including p=1, exact roots and multiplicities, locally uniform exterior asymptotics, separated tail products and actual disc suprema. Direct corrections retain the signed D.3 subtraction, exterior boundaries, half-radius Fourier tail, signed-index cutoff, inequality in the D.6 display, explicit separation constants, finite-head dependence, c^p and the p norm below exponent two. D.7-D.9 retain their actual remainders, removable centers and independent samples. This documentation step adds no Lean proof or refutation; historical refutations and broader completeness qualifications remain unchanged.

Source: printed pp.126–130, text lines 10320–10674. Line numbers count
newline characters and preserve form feeds. All five rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| D-001 | 10322–10330 | Absolute versus ordinary ordered products | matched |
| D-002 | 10333–10341 | D.1 signed sum and square sum estimate | matched |
| D-003 | 10344–10350 | D.2 exponential bound | matched |
| D-004 | 10360–10366 | D.3 signed linear subtraction | corrected |
| D-005 | 10368–10372 | Sine product normalization | matched |
| D-006 | 10374–10380 | Finite exponent displaced roots and uniform simple-root separation | matched |
| D-007 | 10383–10383 | Adaptation from p=2 | contextual |
| D-008 | 10386–10391 | D.4 joint analyticity and exact roots | matched |
| D-009 | 10392–10398 | Simple roots and reciprocal poles | matched |
| D-010 | 10401–10420 | Paired perturbation sums and products | matched |
| D-011 | 10421–10424 | Local uniform product convergence and analyticity | matched |
| D-012 | 10426–10428 | Free open quarter-pi discs | matched |
| D-013 | 10440–10462 | D.5 locally uniform exterior asymptotic | matched |
| D-014 | 10465–10470 | Entire product divided by sine as a relative product | matched |
| D-015 | 10472–10477 | Nearest lattice point and reciprocal denominator estimate | corrected |
| D-016 | 10478–10490 | Exterior reciprocal sum split into far and near indices | corrected |
| D-017 | 10492–10493 | Local uniform decay gives asymptotic | matched |
| D-018 | 10497–10519 | D.6 separated tail products with uniform constants | corrected |
| D-019 | 10530–10535 | Literal ratio perturbation | matched |
| D-020 | 10537–10546 | Uniform half-unit cutoff for all retained factors | corrected |
| D-021 | 10550–10557 | Corrected product-error inequality and its three sums | corrected |
| D-022 | 10559–10563 | Holder bound for absolute reciprocal sum | corrected |
| D-023 | 10565–10572 | Finite head modification and signed-row estimate | corrected |
| D-024 | 10574–10583 | Square row at p>=2 | matched |
| D-025 | 10585–10591 | Square row at p<=2 | corrected |
| D-026 | 10595–10602 | Combined powered product estimate | corrected |
| D-027 | 10605–10608 | D.7 signed quadratic remainder | matched |
| D-028 | 10611–10621 | D.8 multiplicative and additive deleted-product estimates | matched |
| D-029 | 10635–10646 | D.9 full product at arbitrary independent samples | matched |
| D-030 | 10649–10673 | Restoring omitted factor and estimating the sine error | matched |

## Compared passages

### D-001: Absolute versus ordinary ordered products

- Absolute convergence of the ordered source products is equivalent to summability of the perturbation norms.
- Absolute convergence gives genuine complex product convergence, including products with zero factors.

Public declarations:

- `NLS.ComplexAnalysis.source_absolute_product_limit_iff`
- `NLS.ComplexAnalysis.source_complex_product_limit_and_bounds`

The source uses cutoffs from 1 through N. The public theorems retain these literal cutoffs. Historical evidence separating ordinary and absolute convergence is preserved without adding or repeating a refutation.

### D-002: D.1 signed sum and square sum estimate

- The norm of the actual complex product minus one is at most A*exp(S)+B*exp(S+S^2), with A the norm of the signed complex sum, B the sum of squared norms and S the sum of norms.
- Absolute summability and the half-unit bound are retained; the printed constants and powers are unchanged.

Public declarations:

- `NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_signed_sum`

The result holds over any index type, hence in particular over the two-sided integer lattice. The proof controls the logarithmic remainder by B.

### D-003: D.2 exponential bound

- The product error is bounded by exp(S)-1, which is at most S*exp(S).

Public declarations:

- `NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_exp_sub_one_le`

Absolute summability suffices; the weaker bound does not require the half-unit hypothesis.

### D-004: D.3 signed linear subtraction

- Subtract the signed complex sum in the linear term and retain its squared norm divided by two in the exponential bound.

Public declarations:

- `NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_sub_tsum_le_signed_square`

The symbol A in the subtraction is the complex sum, while D.1 used its norm. This is the positive corrected statement. Historical source-notation evidence is unchanged; no new refutation is added.

### D-005: Sine product normalization

- The free sine function is the limit of the literal negative symmetric root products.
- The zero-index normalization denominator is one; all nonzero denominators are pi*m.

Public declarations:

- `NLS.ZakharovShabat.singleSpectralDenominator`
- `NLS.ZakharovShabat.tendsto_appendixDProduct`
- `NLS.ZakharovShabat.appendixDProduct_zero`

The negative prefactor, two-sided symmetric cutoffs and zero-index convention are retained. The product is not replaced by an arbitrarily normalized entire function.

### D-006: Finite exponent displaced roots and uniform simple-root separation

- Every finite Banach displacement exponent, including p=1, has the prescribed perturbed lattice.
- If its roots are pairwise distinct, one strictly positive constant separates every pair of distinct roots.

Public declarations:

- `NLS.ZakharovShabat.exists_uniform_displacedRoots_separation`
- `NLS.ZakharovShabat.exists_displacedRoot_separation`

Uniform separation uses finite-exponent decay. For arbitrary bounded displacements only the individual-root isolation used later is asserted; a common global separation is not inferred from boundedness alone.

### D-007: Adaptation from p=2

- The source says its presentation extends the p=2 appendix in reference [23].

Public declarations:

- `NLS.ZakharovShabat.analyticOnNhd_jointSingleSpectralProduct_finite`
- `NLS.ZakharovShabat.analyticOnNhd_jointDeletedSingleSpectralProduct_finite`

The attribution is contextual. The finite-exponent conclusions are proved in the repository. This row does not claim comparison of the exact 2014 edition of reference [23].

### D-008: D.4 joint analyticity and exact roots

- For each omitted integer index, the literal negative deleted product converges and is jointly analytic in the spectral parameter and the displacement.
- Its zeros are exactly the retained roots, with the count of repeated retained indices as analytic multiplicity.

Public declarations:

- `NLS.ZakharovShabat.tendsto_appendixDDeletedProduct`
- `NLS.ZakharovShabat.analyticOnNhd_appendixDDeletedProduct`
- `NLS.ZakharovShabat.appendixDDeletedProduct_eq_zero_iff`
- `NLS.ZakharovShabat.analyticOrderAt_appendixDDeletedProduct`

All finite p>=1 are retained. Repeated roots are allowed in this assertion, and the omitted index is removed before counting multiplicity.

### D-009: Simple roots and reciprocal poles

- For an injective root sequence the retained zeros have analytic order one.
- The reciprocal is meromorphic, has order minus one at each retained root, and is the limit of the reciprocal symmetric products away from those roots.

Public declarations:

- `NLS.ZakharovShabat.analyticOrderAt_appendixDDeletedProduct_of_injective`
- `NLS.ZakharovShabat.meromorphicAt_inv_appendixDDeletedProduct`
- `NLS.ZakharovShabat.meromorphicOrderAt_inv_appendixDDeletedProduct_of_injective`
- `NLS.ZakharovShabat.tendsto_inv_appendixDDeletedProduct`

The zero and pole locations are the original displaced roots, with no unmentioned nonvanishing assumption at the omitted index.

### D-010: Paired perturbation sums and products

- Opposite indices cancel the spectral parameter in the linear perturbation sum and give the exact square-denominator quadratic identity.
- Both paired expressions are absolutely summable at every finite Banach exponent; the quadratic one is summable even for bounded displacements.

Public declarations:

- `NLS.ZakharovShabat.appendixDZeroDeletedPerturbation_add_neg`
- `NLS.ZakharovShabat.appendixDZeroDeletedPerturbation_mul_neg`
- `NLS.ZakharovShabat.summable_norm_appendixDZeroDeletedPerturbation_add_neg`
- `NLS.ZakharovShabat.summable_norm_appendixDZeroDeletedPerturbation_mul_neg`

The zero entry is totalized and unused. These statements are fixed-parameter summability results; local uniformity is supplied by the next separately proved product-convergence assertion.

### D-011: Local uniform product convergence and analyticity

- Full and deleted symmetric cutoffs converge uniformly on compact spectral sets and bounded displacement sets.
- Every finite cutoff is jointly analytic and its limit is jointly analytic, including p=1.

Public declarations:

- `NLS.ZakharovShabat.tendstoUniformlyOn_jointSingleSpectralProduct_finite`
- `NLS.ZakharovShabat.tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite`
- `NLS.ZakharovShabat.analyticOnNhd_jointSingleSpectralPartialProduct`
- `NLS.ZakharovShabat.analyticOnNhd_jointDeletedSingleSpectralPartialProduct`
- `NLS.ZakharovShabat.analyticOnNhd_jointDeletedSingleSpectralProduct_finite`

The proof uses uniform product estimates and exponent inclusion for the summable endpoint. It proves the required local uniform convergence without treating pointwise convergence alone as sufficient.

### D-012: Free open quarter-pi discs

- The free source discs are open balls of radius pi/4 centered at pi*n, and their exterior contains the boundaries.

Public declarations:

- `NLS.ZakharovShabat.appendixDExterior`
- `NLS.ZakharovShabat.appendixDExterior_eq_compl_iUnion_ball`

The complement is taken after the union over every signed integer index.

### D-013: D.5 locally uniform exterior asymptotic

- The normalized full product is jointly analytic and has exactly the prescribed roots with their multiplicities.
- For every displacement and epsilon>0, one positive neighborhood radius and one spectral threshold make the literal exterior error supremum smaller than epsilon for all displacements in that neighborhood.

Public declarations:

- `NLS.ZakharovShabat.analyticOnNhd_appendixDProduct`
- `NLS.ZakharovShabat.appendixDProduct_eq_zero_iff`
- `NLS.ZakharovShabat.analyticOrderAt_appendixDProduct`
- `NLS.ZakharovShabat.exists_local_appendixDProduct_div_sin_sup_lt`

This retains the strict supremum statement, the full exterior including boundaries, and every finite p>=1. The threshold is chosen before varying the displacement in the neighborhood.

### D-014: Entire product divided by sine as a relative product

- Off the free lattice the sine-normalized source product equals the actual convergent relative product.
- The product error is bounded by exp of the absolute reciprocal-sum norm minus one.

Public declarations:

- `NLS.ZakharovShabat.appendixDProduct_div_sin_eq_tprod`
- `NLS.ZakharovShabat.norm_appendixDProduct_div_sin_sub_one_le`

The factors are 1-a_m/(z-pi*m), equal to the printed root ratios. The quotient is evaluated only where its sine denominator is nonzero.

### D-015: Nearest lattice point and reciprocal denominator estimate

- Each exterior point has a real nearest lattice index with real displacement at most pi/2.
- For that index every reciprocal denominator satisfies the factor-four estimate, and one index works before all factors and complex numerators.

Public declarations:

- `NLS.ZakharovShabat.exists_appendixDExterior_nearest_lattice`
- `NLS.ZakharovShabat.appendixDExterior_denominator_le_four`
- `NLS.ZakharovShabat.norm_appendixDExterior_relativeFactor_le`

Use the non-strict lower distance pi/4 at exterior boundary points; the source discs are open. The factor four is retained. The nearest-index helper passed its full check and is committed and pushed.

### D-016: Exterior reciprocal sum split into far and near indices

- The actual scalar reciprocal sum converges and splits into a distant kernel plus the coefficient tail.
- The two printed decay denominators hold with explicit constant 8*(4*p.toReal+1), including p=1.

Public declarations:

- `NLS.Coeff.appendixDReciprocalSum_height_bound`
- `NLS.Coeff.appendixDReciprocalSum_far_near`
- `NLS.Coeff.appendixDReciprocalSum_source_bound`

Correct the tail to the half-radius tail retaining abs(m)>=floor(abs(n)/2)+1. The near split only provides this half-radius information. The constant and tail index are corrected directly without proving a counterexample.

### D-017: Local uniform decay gives asymptotic

- The absolute reciprocal-sum norm tends to zero at spectral infinity outside fixed free discs.
- One threshold works throughout a neighborhood of any fixed displacement, yielding the required locally uniform sine asymptotic.

Public declarations:

- `NLS.ZakharovShabat.tendsto_scalarResolventToL1_of_separated`
- `NLS.ZakharovShabat.exists_local_threshold_scalarResolvent_small`
- `NLS.ZakharovShabat.exists_local_appendixDProduct_div_sin_bound`

The final uniformity is proved by finite-support approximation and a common operator bound. The scalar split is also proved, but the final theorem does not depend on an unproved assertion about uniform tails over an arbitrary bounded set.

### D-018: D.6 separated tail products with uniform constants

- Two arbitrary bounded complex displacements with finite ell-p difference have genuinely convergent tail-disc relative products for finite 1<p<infinity.
- One positive constant, chosen from p,c and the two norm bounds before the inputs or cutoffs, bounds both the p-power sum and the printed linear-norm right side.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaD6_multipliable`
- `NLS.ZakharovShabat.sourceLemmaD6`
- `NLS.ZakharovShabat.exists_appendixDReciprocalTerm_half_cutoff`

The final theorem is stronger: it permits every cutoff beyond the separated tail and does not need simplicity or the printed small-tail condition. Where the proof uses small factors, use the separately proved uniform cutoff with c on both head and tail terms; do not retain the incomplete sufficient-condition constant.

### D-019: Literal ratio perturbation

- The actual quotient minus one is the off-diagonal displacement difference divided by the reference denominator.
- Reconstructing numerator roots from their literal displacement difference gives exactly the source relative product.

Public declarations:

- `NLS.ZakharovShabat.appendixDReciprocalTerm`
- `NLS.ZakharovShabat.appendixDRelativeProductError_eq`
- `NLS.ZakharovShabat.appendixDRelativeProductError_difference`

Separation gives nonzero off-diagonal denominators before the division identity is used. The omitted product entry is one and the omitted sum entry is zero.

### D-020: Uniform half-unit cutoff for all retained factors

- The head/tail factor bound retains abs(n), the head coefficient 2*c/abs(n), and c multiplying the tail norm.
- For every positive tolerance one positive cutoff works before every signed n, every point in its original disc, and every factor index; the half-unit bound follows.

Public declarations:

- `NLS.ZakharovShabat.norm_appendixDReciprocalTerm_le_head_tail`
- `NLS.ZakharovShabat.exists_appendixDReciprocalTerm_uniform_cutoff`
- `NLS.ZakharovShabat.exists_appendixDReciprocalTerm_half_cutoff`

Use signed-index magnitude and the inclusive Fourier-tail convention. The statements also hold at p=1. No source formula is disproved to establish this correction.

### D-021: Corrected product-error inequality and its three sums

- The actual product-error norm supremum is at most A*exp(S)+B*exp(S+S^2).
- Here A is the supremum of the signed sum, S is the sum of the individual factor suprema and B is the sum of their squares; both factor sums converge.

Public declarations:

- `NLS.ZakharovShabat.appendixDDiscNormSup_bounds`
- `NLS.ZakharovShabat.appendixDReciprocalTerm_discSup_summable`
- `NLS.ZakharovShabat.exists_appendixDRelativeProduct_discSup_signed_bound`

Replace the printed equality by an inequality directly. Every supremum is over the original full open disc; no maximum-attainment assumption is imposed. A common cutoff precedes all tail indices.

### D-022: Holder bound for absolute reciprocal sum

- Holder bounds the sum of factor suprema by c times the conjugate-exponent reciprocal-kernel norm times norm(a).

Public declarations:

- `NLS.ZakharovShabat.appendixDReciprocalTerm_discSup_sum_le`

Keep c explicit instead of hiding it in a symbol labeled C_p. The exact conjugate-kernel bound assumes 1<p<infinity, as in D.6. The zero kernel entry implements the omitted diagonal.

### D-023: Finite head modification and signed-row estimate

- Simplicity permits one finite modification of the head discs, leaving the original tail discs unchanged and giving a global off-diagonal separation.
- One radius and one separation constant C are chosen before all inputs. All independent samples give genuinely convergent ell-p signed rows, with a single least norm majorant over the modified discs.

Public declarations:

- `NLS.ZakharovShabat.appendixDModifiedDisk`
- `NLS.ZakharovShabat.exists_appendixDModifiedDisks_separated`
- `NLS.ZakharovShabat.appendixDModifiedDisk_displacement_le`
- `NLS.ZakharovShabat.exists_appendixDModifiedDisk_rows`
- `NLS.ZakharovShabat.exists_appendixDModifiedDisk_signed_sup_of_simple`

Retain C explicitly in the bound pi^(-1)*(HilbertBound+C*(2*norm(r)+1+pi/4)*norm(square kernel))*norm(a). Do not claim uniform finite-head control from the displacement norm alone. The original tail conclusion uses its own independently proved uniform bound.

### D-024: Square row at p>=2

- For finite p>=2, the literal sum of squared factor suprema has half-exponent membership and summable p/2 powers.
- Its total p/2 energy is at most c^p*norm(a)^p times the reciprocal-square convolution constant to power p/2.

Public declarations:

- `NLS.Fourier.exists_squaredAbsoluteRows`
- `NLS.ZakharovShabat.appendixDReciprocalTerm_discSup_square_sum_le`
- `NLS.ZakharovShabat.appendixDReciprocalTerm_discSup_square_power_bound`

Young convolution gives the half-exponent estimate. The finite head is extended by zero, so the full integer sum is exactly the selected-tail sum. The two literal-square theorems passed their full check and are committed and pushed.

### D-025: Square row at p<=2

- The same literal squared-supremum sum belongs to ell-(p/2) for 1<p<=2, allowing the target exponent to be below one.
- The powered bound retains c^p and the p norm of a; at p=3/2 these are c^(3/2), norm(a)^(3/2), and target exponent 3/4.

Public declarations:

- `NLS.Fourier.exists_squaredAbsoluteRows`
- `NLS.ZakharovShabat.appendixDReciprocalTerm_discSup_square_power_bound`

Correct c^2 to c^p in the powered energy and the inconsistent q norm label to p. Powered Young handles the quasi-normed range. The positive theorem passed its full check and is committed and pushed; no refutation is added.

### D-026: Combined powered product estimate

- Combining the signed row, square row and absolute bound gives the literal product-error supremum in ell-p.
- The p-power sum has a constant uniform before all bounded inputs and later cutoffs, and the linear-norm version is retained as well.

Public declarations:

- `NLS.ZakharovShabat.appendixDRelativeProductPowerSup_normBall`
- `NLS.ZakharovShabat.sourceLemmaD6`

The final constant retains dependence on c,p,the reference norm bound and the difference norm bound. The repository proves the final estimate by uniform majorants, without relying on the printed equality or missing constant labels in intermediate displays.

### D-027: D.7 signed quadratic remainder

- After subtracting the signed root-difference reciprocal sum, the literal tail-disc norm supremum belongs to ell-(p/2), uniformly on bounded input sets.
- This implies the printed ell-(p/2)+ell-(1+) decomposition with one common zero second component.

Public declarations:

- `NLS.ZakharovShabat.sourceRemarkD7Remainder_eq`
- `NLS.ZakharovShabat.sourceRemarkD7_uniform`
- `NLS.ZakharovShabat.sourceRemarkD7_mem`
- `NLS.ZakharovShabat.sourceRemarkD7`

The selected tail is extended by zero on the finite head. The half-exponent target includes p<2; the linear subtraction remains complex and signed.

### D-028: D.8 multiplicative and additive deleted-product estimates

- The literal positive deleted product divided by its omitted normalization denominator has both multiplicative and additive ell-p errors.
- Actual error suprema and arbitrary independent samples share one bound throughout each displacement norm ball, hence locally uniformly.

Public declarations:

- `NLS.ZakharovShabat.tendsto_appendixDNormalizedDeletedProduct`
- `NLS.ZakharovShabat.sourceLemmaD8_uniform`
- `NLS.ZakharovShabat.sourceLemmaD8_locally_uniform`
- `NLS.ZakharovShabat.sourceLemmaD8_off_center`
- `NLS.ZakharovShabat.sourceLemmaD8_center`

At free centers the sine quotient is filled by its removable value, retaining the cosine sign. Away from centers it is the literal displayed quotient. The original finite 1<p<infinity scope is retained.

### D-029: D.9 full product at arbitrary independent samples

- For every independent sampling sequence in the original discs, the full negative source product differs from sine by an actual ell-p sequence.
- One bound works throughout a displacement neighborhood and before all sampling sequences; literal symmetric-cutoff definitions give the same result.

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaD9`
- `NLS.ZakharovShabat.sourceLemmaD9_uniform`
- `NLS.ZakharovShabat.sourceLemmaD9_locally_uniform`
- `NLS.ZakharovShabat.sourceLemmaD9_of_cutoff_limits`

The negative normalization and all signed integer indices are retained. No regularity or correlation is imposed on the independent sample choices. The exponent range is the original finite 1<p<infinity.

### D-030: Restoring omitted factor and estimating the sine error

- Restoring the omitted source factor gives the exact full product, and subtracting sine yields the signed free-quotient times displacement-and-relative-error identity.
- The free sine quotient and the sampled displaced-root difference are uniformly bounded on the discs, so the resulting error belongs to ell-p.

Public declarations:

- `NLS.ZakharovShabat.appendixDProduct_eq_deleted`
- `NLS.ZakharovShabat.appendixDDeletedProduct_zero`
- `NLS.ZakharovShabat.appendixDProduct_sub_sin_eq_relative_error`
- `NLS.ZakharovShabat.sourceLemmaD8_uniform`
- `NLS.ZakharovShabat.sourceLemmaD9_mem`

The free deleted product divided by its denominator is minus the filled sine quotient, which accounts for the sign. The final membership theorem applies also at the removable centers.

## Evidence and validation

The [literal sine products](../NLS/ZakharovShabat/AppendixDSineProducts.lean)
retain symmetric cutoffs and the negative normalization. The
[scalar bound](../NLS/SequenceSpaces/AppendixDExteriorSum.lean),
[modified discs](../NLS/ZakharovShabat/AppendixDModifiedDisks.lean),
[literal supremum inequality](../NLS/ZakharovShabat/AppendixDDiscSupProduct.lean),
[squared suprema](../NLS/ZakharovShabat/AppendixDDiscSupSquare.lean) and
[nearest index](../NLS/ZakharovShabat/AppendixDNearestLattice.lean)
supply the direct proof details and explicit constants.

This comparison read fifty complete public module bodies and resolves
83 declarations. It reconciles the preceding Appendix D review and
three positive implementation steps. Historical refutations remain
unchanged. This local comparison does not claim a fresh review of
every transitive analytic or product-convergence proof.

The unchanged Lean snapshot reuses the successful full check recorded at commit 9aa445d2e925078f5f3aaabf490e728ab7fb45ce: 8,593 build jobs, 7,712 public examples and an axiom audit of 44,804 NLS declarations, with 21 inherited warnings and zero new. All 83 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix E. The
[broader completion qualifications](COMPLETENESS.md) remain.
