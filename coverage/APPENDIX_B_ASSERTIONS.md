# Appendix B ordered assertion comparison

The ordered Appendix B comparison covers 12 groups on printed pp.124–125: eight matched, two directly corrected and two contextual, with no partial or pending groups in this local comparison. B.1 retains both printed reciprocal-series bounds. B.2 retains all Banach Young triples, including infinity, genuine absolute convergence and constant one. B.3 retains the finite positive exponent formula, including inputs below one, all three convergence levels and constant one. Zero auxiliary exponents and an unstated infinity/supremum convention are not asserted. The proof outer sum is correctly the gamma-th power of the stated left side; both directions of the intermediate exponent conditions are proved. This documentation step adds no Lean proof or refutation. Historical diagnostics and broader completeness qualifications, including the four Section 28 complex intermediates, remain unchanged.

Source: printed pp.124–125, text lines 10158–10244. Line numbers count
newline characters and preserve form feeds. Both rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| B-001 | 10160–10161 | Conjugate exponent convention | contextual |
| B-002 | 10163–10169 | Lemma B.1, both reciprocal-series bounds | matched |
| B-003 | 10171–10171 | Integral comparison retaining the first summand | matched |
| B-004 | 10183–10188 | Lemma B.2, full Young inequality | matched |
| B-005 | 10191–10192 | Transition to the nested three-sequence estimate | contextual |
| B-006 | 10194–10210 | Lemma B.3, finite positive exponent formula | corrected |
| B-007 | 10213–10221 | Inner sequence and corrected outer gamma power | corrected |
| B-008 | 10222–10226 | First powered Young relation (B.2) | matched |
| B-009 | 10228–10228 | Intermediate exponent order equivalence | matched |
| B-010 | 10230–10237 | Second powered Young estimate and (B.3) | matched |
| B-011 | 10239–10239 | Intermediate exponent at least alpha | matched |
| B-012 | 10239–10244 | Equivalence of the combined and two intermediate relations | matched |

## Compared passages

### B-001: Conjugate exponent convention

- The source uses the usual reciprocal conjugate-exponent convention; B.1 uses finite conjugate exponents and B.2 admits infinity.

Public declarations:

- `NLS.sourceLemmaB1`
- `NLS.Coeff.sourceLemmaB2`

The introductory notation is interpreted separately at the stated ranges of each lemma; it does not define the zero powers in B.3.

### B-002: Lemma B.1, both reciprocal-series bounds

- For every nonnegative shift alpha and finite conjugate pair p,q>1, the actual series over m>=1 is summable.
- Its sum is at most (q+alpha)/(q-1)/(1+alpha)^q, which is at most p/(1+alpha)^(q-1).

Public declarations:

- `NLS.sourceLemmaB1`
- `NLS.ReciprocalSeries.shifted_reciprocal_series_bounds`

Both printed constants and the alpha=0 case are retained. The natural-index implementation uses m=n+1 exactly.

### B-003: Integral comparison retaining the first summand

- The decreasing reciprocal-power series is bounded by its first summand plus the exact improper integral.

Public declarations:

- `NLS.ReciprocalSeries.tsum_nat_shifted_rpow_le`
- `NLS.ReciprocalSeries.tsum_nat_succ_shifted_rpow_le`
- `NLS.ReciprocalSeries.shifted_rpow_bound_le_simple`

The first summand is retained before the algebraic simplification; no larger unspecified constant is substituted.

### B-004: Lemma B.2, full Young inequality

- Every Banach Young triple, including every infinity endpoint, gives a unique target sequence with a genuine HasSum formula at each output frequency.
- The convolution is absolutely convergent in each row and its target norm is at most the product of input norms, with exact bilinear operator norm one.

Public declarations:

- `NLS.Coeff.sourceLemmaB2`
- `NLS.Coeff.summable_norm_youngConvolution_terms`
- `NLS.Coeff.norm_youngConvolutionCLM`

The proof applies to arbitrary sequence inputs without finite-support assumptions; finite cutoffs and the lp Fatou property construct the actual limit.

### B-005: Transition to the nested three-sequence estimate

- The next result is a nested three-sequence version of the preceding Young estimate.

Public declarations:

- `NLS.Coeff.sourceLemmaB3_positive`

The prose reference to the preceding inequality is contextual. The following statement is compared using its actual nested magnitude formula.

### B-006: Lemma B.3, finite positive exponent formula

- For finite alpha,beta>0, gamma>=p1>=beta and p2,p3>=alpha with the printed reciprocal identity, all three nested sum levels converge.
- The exact displayed bound has constant one and retains the indices k-l,l-m,m and powers beta/alpha,gamma/beta,1/gamma. Input exponents below one are allowed.

Public declarations:

- `NLS.Coeff.sourceLemmaB3_positive`
- `NLS.Coeff.mixedYoung_summable_and_le`
- `NLS.Coeff.sourceLemmaB3_constant_sharp`

The divisions require strictly positive auxiliary exponents. The source supplies no zero-exponent definition or separate infinity/supremum convention; the implemented statement is explicitly finite and positive. Historical diagnostics remain unchanged and no new refutation is added.

### B-007: Inner sequence and corrected outer gamma power

- The inner sequence d_l is the positive alpha-th root of the actual sum of |b(l-m)*c(m)|^alpha, with its proved target membership and norm bound.
- The next displayed outer sum is bounded by norm(a)^gamma*norm(d)^gamma and ultimately by norm(a)^gamma*norm(b)^gamma*norm(c)^gamma. Its positive gamma-th root is the stated B.3 left side.

Public declarations:

- `NLS.Coeff.exists_powerConvolution`
- `NLS.Coeff.mixedYoung_row_identity`
- `NLS.Coeff.mixedYoung_outer_sum_le`

Correct the proof wording to the gamma-th power of the left side. Powered complex sequences mean powered magnitudes in the actual construction. The new outer-sum theorem retains summability and constant one; the positive theorem passed its full check and is committed and pushed.

### B-008: First powered Young relation (B.2)

- The first powered Young application uses the exact relation 1/beta+1/gamma=1/p1+1/q and exponents p1,q,gamma at least beta.

Public declarations:

- `NLS.MixedYoungRelation.exists_intermediate`
- `NLS.PowerYoungRelation.youngRelation`
- `NLS.Coeff.exists_powerConvolution`

The powered exponents are Banach even when original exponents are below one. The intermediate q is a positive finite real number.

### B-009: Intermediate exponent order equivalence

- Under the exact first reciprocal identity and positive finite exponents, q>=beta is equivalent to gamma>=p1.

Public declarations:

- `NLS.mixedYoung_intermediate_order_iff`

Both directions are proved by reciprocal order, not only the direction needed by the final inequality. The positive proof step passed its full check and is committed and pushed.

### B-010: Second powered Young estimate and (B.3)

- The second powered Young application uses 1/alpha+1/q=1/p2+1/p3, with p2,p3,q at least alpha.
- It bounds the norm of d by the product of the b and c norms and preserves the exact power-norm identities.

Public declarations:

- `NLS.Coeff.exists_powerConvolution`
- `NLS.Coeff.norm_normPower`
- `NLS.Coeff.mixedYoung_summable_and_le`

All inner sums are proved convergent before the positive root and the second convolution are formed.

### B-011: Intermediate exponent at least alpha

- The second reciprocal identity and p2,p3>=alpha imply that the constructed intermediate exponent q is at least alpha.

Public declarations:

- `NLS.MixedYoungRelation.exists_intermediate`

The construction uses the positive reciprocal 1/beta+1/gamma-1/p1, proves its bound by 1/alpha, and then inverts it. Its positivity is explicit.

### B-012: Equivalence of the combined and two intermediate relations

- The single mixed exponent condition is equivalent to the existence of a q satisfying both powered Young relations.
- Adding (B.2) and (B.3) and cancelling 1/q recovers the printed combined identity; the order equivalence recovers gamma>=p1.

Public declarations:

- `NLS.mixedYoungRelation_iff_exists_intermediate`
- `NLS.MixedYoungRelation.exists_intermediate`

The new theorem provides the reverse implication as well as the existing constructive direction. The positive proof step passed its full check and is committed and pushed.

## Evidence and validation

The [source inequalities](../NLS/SequenceSpaces/AppendixBSourceInequalities.lean)
retain both B.1 constants and the original B.2/B.3 norm formulas. The
[full Young construction](../NLS/SequenceSpaces/YoungInequality.lean) proves
row convergence before forming the convolution. The
[positive proof steps](../NLS/SequenceSpaces/AppendixBProofSteps.lean)
make the intermediate exponent and outer gamma power explicit.

This comparison read nine complete public module bodies and resolves
19 declarations. It reconciles the previous Appendix B review and the
new positive proof step. It does not claim to repeat every transitive
finite-convolution proof. The zero-exponent diagnostics remain unchanged;
no new refutation is added.

The unchanged Lean snapshot reuses the successful full check recorded at commit 862ad929f3588bf317eff9c659e8e63a1fef9549: 8,583 build jobs, 7,694 public examples and an axiom audit of 44,709 NLS declarations, with 21 inherited warnings and zero new. All 19 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix C. The
[broader completion qualifications](COMPLETENESS.md) remain.
