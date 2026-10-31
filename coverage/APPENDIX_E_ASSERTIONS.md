# Appendix E ordered assertion comparison

The ordered Appendix E comparison covers eleven groups on printed pp.130-131: seven matched, three directly corrected and one contextual. No partial or pending group remains in this local comparison. It retains literal symmetric interpolation sums and diagonal-omitted products, actual circle suprema, finite residue identities, at-most-simple poles, the nonempty real slice and actual unit-interval Fourier coefficients. Local derivative and series-diagonal vanishing use an alternative complex-line argument; the printed polarization derivation is not separately claimed. This documentation step adds no Lean proof or refutation; historical refutations and broader completeness qualifications remain unchanged.

Source: printed pp.130–131, text lines 10676–10763. Line numbers count
newline characters and preserve form feeds. Both rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| E-001 | 10678–10678 | Extension beyond p=2 | contextual |
| E-002 | 10680–10686 | Entire numerator, circle decay and simple displaced lattice | matched |
| E-003 | 10687–10691 | Omitted-index cardinal products and symmetric interpolation sums | corrected |
| E-004 | 10693–10700 | Entire product, roots and circle asymptotic | matched |
| E-005 | 10701–10707 | At most simple poles and quotient decay | corrected |
| E-006 | 10717–10726 | Finite residue identities, outer contour limit and interpolation | matched |
| E-007 | 10729–10731 | Identity theorem with nonempty real slice | corrected |
| E-008 | 10733–10747 | Taylor/polarization argument and local vanishing | matched |
| E-009 | 10747–10748 | Propagation over a connected domain | matched |
| E-010 | 10751–10753 | Uniform Fourier-Lebesgue exponential bound | matched |
| E-011 | 10755–10761 | Literal reciprocal coefficient estimate and uniform quantifiers | matched |

## Compared passages

### E-001: Extension beyond p=2

- The source extends the p=2 interpolation statement cited from reference [23].

Public declarations:

- `NLS.ZakharovShabat.sourceLemmaE1_literal`

The attribution is contextual. All finite Banach exponents are implemented, but this does not compare the precise 2014 edition of reference [23].

### E-002: Entire numerator, circle decay and simple displaced lattice

- The numerator is entire and its actual sine-quotient norm supremum tends to zero on circles of radius N*pi+pi/2.
- Every injective complex displaced lattice with finite ell-p displacement, including p=1, is allowed; evaluation points avoid all roots.

Public declarations:

- `NLS.ZakharovShabat.appendixESineCircleSup`
- `NLS.ZakharovShabat.norm_sineQuotient_le_appendixESineCircleSup`
- `NLS.ZakharovShabat.eventually_sineQuotient_small_of_sup_tendsto`
- `NLS.ZakharovShabat.sourceLemmaE1`

No decay rate or summability of interpolation coefficients is assumed. Analyticity supplies finiteness of the literal circle supremum.

### E-003: Omitted-index cardinal products and symmetric interpolation sums

- Each cardinal product is the literal symmetric cutoff product with its diagonal index omitted.
- The symmetric outer sums of those limits converge to the numerator value; the kernel equals g(z)/(g'(sigma_n)*(z-sigma_n)).

Public declarations:

- `NLS.ZakharovShabat.appendixEInterpolationKernel`
- `NLS.ZakharovShabat.tendsto_appendixEInterpolationKernel`
- `NLS.ZakharovShabat.appendixEInterpolationKernel_eq_deriv`
- `NLS.ZakharovShabat.sourceLemmaE1_literal`

Omit the diagonal as in the source residue calculation. The outer sum is explicitly symmetric; absolute convergence and unconditional HasSum are not claimed. Historical diagonal-index evidence is retained without extending or repeating a refutation.

### E-004: Entire product, roots and circle asymptotic

- The full negative product is entire with exactly the displaced roots and nonzero derivative at every root of a simple lattice.
- On every sufficiently large source circle its quotient by sine has norm at least one half, so it is nonzero there.

Public declarations:

- `NLS.ZakharovShabat.analyticOnNhd_appendixDProduct`
- `NLS.ZakharovShabat.appendixDProduct_eq_zero_iff`
- `NLS.ZakharovShabat.deriv_appendixDProduct_ne_zero`
- `NLS.ZakharovShabat.eventually_appendixDProduct_circle_lower`

The literal negative product normalization and finite p=1 endpoint are retained. The circle estimate follows from D.5 on the full separated exterior.

### E-005: At most simple poles and quotient decay

- At a simple denominator zero the principal part has coefficient numerator-value divided by denominator-derivative, and subtracting it leaves an analytic germ.
- The numerator/sine circle decay transfers to the quotient by the displaced product, and the outer Cauchy integrals vanish uniformly on bounded evaluation sets.

Public declarations:

- `NLS.ComplexAnalysis.exists_analytic_simpleQuotient_remainder`
- `NLS.ComplexAnalysis.analyticOnNhd_simpleQuotient_remainder`
- `NLS.ZakharovShabat.eventually_appendixEQuotient_small`
- `NLS.ZakharovShabat.eventually_appendixE_outerCauchy_small`

Read the poles as at most simple: a zero numerator may cancel a pole. The existing positive principal-part theorem permits zero residues. No counterexample is added. The contour estimate assumes no rate of decay.

### E-006: Finite residue identities, outer contour limit and interpolation

- Large half-integer circles enclose exactly the symmetric block of displaced roots.
- The finite residue identity is exact; its vanishing outer error proves the symmetric interpolation limit, uniformly for the quotient on bounded zero-free evaluation sets.

Public declarations:

- `NLS.ZakharovShabat.eventually_displacedRoots_mem_centralBall_iff`
- `NLS.ComplexAnalysis.circleIntegral_simpleQuotient_cauchy_eq_interpolation_error`
- `NLS.ZakharovShabat.eventually_appendixE_interpolation_error`
- `NLS.ZakharovShabat.tendstoUniformlyOn_appendixEQuotientInterpolation`
- `NLS.ZakharovShabat.sourceLemmaE1_of_circle_decay`

The limit of residues is interpreted through these finite symmetric sums. Root simplicity, boundary nonvanishing and the derivative normalization are established before taking the limit.

### E-007: Identity theorem with nonempty real slice

- An analytic map on a connected open subset of any continuous real-linear complexification is determined by its values on the nonempty real slice.
- A specified real base point, agreement of two maps, complete complex targets and the actual conjugate-reflected source spaces are supported.

Public declarations:

- `NLS.ComplexAnalysis.RealComplexification`
- `NLS.ComplexAnalysis.sourceLemmaE2`
- `NLS.ComplexAnalysis.sourceLemmaE2_of_real_point`
- `NLS.ComplexAnalysis.sourceLemmaE2_eq`
- `NLS.ZakharovShabat.sourceLemmaE2_realType`

The real-slice intersection must be nonempty, as used in the printed proof. There is no convexity or isometric/projection-norm assumption. Historical empty-slice evidence remains unchanged; no new refutation is added.

### E-008: Taylor/polarization argument and local vanishing

- At each real point in the domain the analytic map has a zero germ.
- All complex iterated derivatives, including mixed derivatives, vanish there. Every supplied local multilinear power series has zero diagonal coefficients in every complex direction.

Public declarations:

- `NLS.ComplexAnalysis.sourceLemmaE2_zero_germ`
- `NLS.ComplexAnalysis.sourceLemmaE2_iteratedFDeriv_eq_zero`
- `NLS.ComplexAnalysis.sourceLemmaE2_powerSeries_diagonal_zero`

These local assertions do not need connectedness. The proof uses the existing complex-line identity argument and then derivative and series uniqueness, an alternative to the printed polarization argument. It does not claim that arbitrary nonsymmetric multilinear series maps themselves are zero. The three positive helper theorems passed their full check and are committed and pushed.

### E-009: Propagation over a connected domain

- The local zero germ propagates to the entire connected open domain by the analytic identity theorem.

Public declarations:

- `NLS.ComplexAnalysis.AnalyticOnNhd.eqOn_zero_of_continuous_real_form`
- `NLS.ComplexAnalysis.sourceLemmaE2`

One real point starts the argument; the domain need not contain the whole real subspace or be convex.

### E-010: Uniform Fourier-Lebesgue exponential bound

- The actual unit-interval Fourier coefficients of exp(i*nu_n*x) are uniformly bounded whenever the frequencies eventually lie within pi/4 of pi*n.
- One tail constant precedes the frequency sequence and cutoff; any finite exceptional head is absorbed in a global bound. Every q>1, including infinity, is retained.

Public declarations:

- `NLS.Fourier.exponentialFourierCoefficients_apply`
- `NLS.Fourier.sourceLemmaE3Bound`
- `NLS.Fourier.sourceLemmaE3_tail`
- `NLS.Fourier.sourceLemmaE3`
- `NLS.Fourier.sourceLemmaE3_bigO`

Complex frequencies and the inclusive displacement boundary are allowed. The unextended exponential is not required to have matching endpoint values; the physical Fourier integrals are used.

### E-011: Literal reciprocal coefficient estimate and uniform quantifiers

- The literal Fourier coefficient of exp(i*nu*x)-exp(i*n*pi*x) is bounded by 4*(2+5*pi/4)*exp(5*pi/4)/(1+abs(n-2*m)).
- Integer modulation preserves the coefficient norm; Euclidean division handles every signed lattice index.

Public declarations:

- `NLS.Fourier.norm_intervalFourierCoefficient_exponential_difference`
- `NLS.Fourier.exponential_shift_bracket_le`
- `NLS.Fourier.norm_exponential_residual_frequency_le`
- `NLS.Fourier.norm_exponentialFourierCoefficients_modulation`
- `NLS.Fourier.norm_exponentialFourierCoefficients_near_lattice`

The coefficient constant is independent of n and m under the pi/4 displacement hypothesis. Uniformity on the finite exceptional head is handled separately, not assumed from the tail hypothesis.

## Evidence and validation

The [literal interpolation products](../NLS/ZakharovShabat/AppendixEInterpolationProducts.lean)
and [circle-decay estimates](../NLS/ZakharovShabat/AppendixEInterpolationDecay.lean)
retain symmetric cutoffs and the actual suprema. The
[continuous real complexification](../NLS/ComplexAnalysis/RealComplexification.lean)
and [local Taylor assertions](../NLS/ComplexAnalysis/AppendixELocalTaylor.lean)
retain the real slice and local vanishing. The
[physical Fourier coefficients](../NLS/Fourier/ShiftedExponentialCoefficientBound.lean)
and [uniform exponential bound](../NLS/Fourier/SourceLemmaE3.lean)
retain complex frequencies and explicit constants.

This comparison read nineteen complete public module bodies and resolves
40 declarations. It reconciles the preceding Appendix E review and
the positive local Taylor implementation step. Historical refutations
remain unchanged. This local comparison does not claim a fresh review
of every transitive analytic or product-convergence proof.

The unchanged Lean snapshot reuses the successful full check recorded at commit 241175fdd8c504f548fb5e4f98da3675ca201130: 8,594 build jobs, 7,714 public examples and an axiom audit of 44,807 NLS declarations, with 21 inherited warnings and zero new. All 40 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Appendix F. The
[broader completion qualifications](COMPLETENESS.md) remain.
