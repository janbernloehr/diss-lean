# Dissertation coverage audit

This is a focused map of the dissertation's introductory results to the
current public Lean API. It is not a completeness certificate for every
chapter or appendix. All paths below are relative to the repository root;
the introductory declarations are in `NLS.ZakharovShabat`.
The appendix audits below use `NLS.Fourier` and `NLS.ComplexAnalysis`.

| Source result | Public entry point | Scope |
| --- | --- | --- |
| Theorem 0.1; Theorems 23.1–23.2; Remark 23.3 | [`SourceSobolevCommonConstants.lean`](NLS/ZakharovShabat/SourceSobolevCommonConstants.lean), `exists_sourceBirkhoffMap_sobolev_common_constants` | One constructed map, every positive integer Sobolev order, common positive constants chosen before the potential, both Birkhoff bounds and both action bounds. |
| Theorem 0.2: analytic action Hamiltonian, sign, Hessian and local concavity | [`SourceHamiltonianActionConcavity.lean`](NLS/ZakharovShabat/SourceHamiltonianActionConcavity.lean), `exists_sourceHamiltonian_action_extension_with_concavity` | Actual source Hamiltonian on an open complex ℓ² domain containing all nonnegative summable actions; actual frequency gradient, Hessian −2 times Hilbert bilinear duality, quantitative local negativity. |
| Physical normalization of H* | [`SourceSobolevHamiltonianIdentification.lean`](NLS/ZakharovShabat/SourceSobolevHamiltonianIdentification.lean), `SourcePrimitivePowerAtlas.renormalizedHamiltonian_eq_sobolevPhysicalCorrection` | Identification with the H¹ energy correction on all real H¹ sources, beyond the finite-gap normalization. |
| Consequence after Theorem 0.2, printed p. 12: no C¹ extension for q > 2 | [`SourceHamiltonianNonextension.lean`](NLS/ZakharovShabat/SourceHamiltonianNonextension.lean), `exists_sourceHamiltonian_no_continuous_extension` | No continuous extension at zero relative to the nonnegative ℓ^q cone, hence no C¹ extension, for every finite q > 2. The same Hamiltonian retains actual source recovery and the physical H¹ identity. |
| Theorem 0.3; Theorem 18.1: frequency extensions | [`SourceFrequencyTheorem18_1Real.lean`](NLS/ZakharovShabat/SourceFrequencyTheorem18_1Real.lean), `exists_sourceFrequency_theorem18_1_real` | A common actual frequency on summable actions, real analytic values in every finite exponent above one, compatible higher-exponent complex extensions and locally uniform mixed remainders. |
| Local invertibility near zero; Corollary 18.2(i) | [`SourceFrequencyLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyLocalInverse.lean), `exists_sourceFrequency_localInverse` | Actual frequency derivative −2 times identity, both analytic local inverse identities, inverse derivative −1/2 times identity, and the Fredholm property throughout the action domain. |
| Remark after Theorem 0.3; Corollary 18.2(iv): generic local invertibility | [`SourceFrequencyGenericLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyGenericLocalInverse.lean), `exists_sourceFrequency_genericLocalInverse` | Open dense set of points with two-sided analytic local inverses on a connected action domain containing all real-source actions and all nonnegative summable actions. |
| Remark after Theorem 0.2: open dense positive Hamiltonian domain | [`SourceHamiltonianPositiveDomain.lean`](NLS/ZakharovShabat/SourceHamiltonianPositiveDomain.lean), `exists_sourceHamiltonian_open_dense_positive_domain` | The actual Hamiltonian domain restricted to the positive ℓ² cone is open and dense; source recovery, gradient, Hessian and local concavity are retained. |
| Remark after Theorem 0.3: open dense positive frequency domains | [`SourceFrequencyPositiveDomains.lean`](NLS/ZakharovShabat/SourceFrequencyPositiveDomains.lean), `exists_sourceFrequency_open_dense_positive_domains` | For every finite p > 2 the compatible action domain at exponent p/2 is open dense relative to the positive cone, retaining real analytic ranges and all locally uniform mixed remainder conclusions. |

## Nonextension proof and limits

The proof integrates the quantitative Hessian estimate along real radial
segments twice. Since H*(0) = 0 and its gradient vanishes at zero, this gives
`Re H*(I) ≤ -‖I‖₂²/2` on a small real Hilbert ball. A block of N+1 coordinates,
each equal to `c / sqrt(N+1)`, has ℓ² norm c and ℓ^q norm
`c (N+1)^(1/q-1/2)`. For finite q > 2 the latter tends to zero while the
Hamiltonian remains bounded above by `-c²/2`. Every block is nonnegative and
summable, so agreement with H* contradicts continuity at zero.

The formal statement allows an arbitrary ambient neighborhood U of zero
and requires agreement only for summable nonnegative actions lying in U.
Continuity and C¹ regularity are tested relative to the nonnegative cone.
No ℓ∞ endpoint is asserted in this milestone. Global analytic extension to
all of the nonnegative ℓ² cone, and global strict concavity, are not asserted.

## Accepted source corrections

The global replacement for Lemma 27.2 is
`sobolevOddHamiltonian_le_twice_weighted_action_remainder`. The original
unrestricted m=1 coefficient is unresolved and optional, not disproved.
The principal Sobolev estimates do not depend on recovering it. See
[`SOURCE_ERRATA.md`](SOURCE_ERRATA.md) for the precise scope of this and
other discrepancies in printed statements or proofs.

## Relative density and limits

[`NonnegativeActionDensity.lean`](NLS/SequenceSpaces/NonnegativeActionDensity.lean)
proves a reusable closure identity: for finite q ≥ 1, every set V containing
all nonnegative summable actions has
`closure (V ∩ nonnegativeLocus q) = nonnegativeLocus q`.
Finite truncations preserve nonnegativity and converge in ℓ^q. Openness of V
then gives relative openness in the positive-cone subtype. This proves the
density assertions without requiring the entire positive cone to lie in V.
It makes no claim of density in the ambient complex space, no density claim
at q=∞, and no global extension or global strict-concavity claim.

## Numbered-statement inventory and spectral overview

[`coverage/statement-candidates.json`](coverage/statement-candidates.json)
indexes 156 distinct candidate numbered labels in the cached text extraction.
It records every matching occurrence, text page and line, and the extraction's
SHA256. Labels in proof references can also match: this is a navigation aid,
not a list of certified statements or completed proofs. It does not replace
an audit of unnumbered definitions, remarks and consequences.

Regenerate with `python3 scripts/source_inventory.py PATH_TO_DISS_TEXT
--output coverage/statement-candidates.json`; add `--check` to verify the
saved inventory without editing it. The source must be the same UTF-8 text
extraction to reproduce its hash and line positions.

[`coverage/SPECTRAL_OVERVIEW.md`](coverage/SPECTRAL_OVERVIEW.md) records the
first detailed comparison. Theorem 1.1 remains partial: the new
`exists_source_periodicCounting_printed_height` recovers the exact printed
source-norm height for 1 ≤ p ≤ 2, including the central counts and moving
projections. Above two, `printed_height_neumann_bound_fails` shows a
limitation of the numerical criterion, not a spectral counterexample.
The literal bound above two still needs proof.

## Appendix C.1 audit

The full-range boundedness assertion is proved by
[`HilbertBoundedness.lean`](NLS/Fourier/HilbertBoundedness.lean), including
the finite-input formula and, through `HilbertSeries.lean`, the convergent
series on every input. The printed isomorphism assertion is refuted at p=2
by [`HilbertNotIsomorphism.lean`](NLS/Fourier/HilbertNotIsomorphism.lean).
Alternating finite blocks have squared norm N+1 and uniformly bounded
transforms. The public results rule out a lower norm estimate, a bounded
linear left inverse, and a continuous linear equivalence realizing H.

This is a proved source discrepancy, not a completed proof of the literal
statement. The correction and its precise scope are recorded in
[`SOURCE_ERRATA.md`](SOURCE_ERRATA.md). The argument makes no claim of a
nonzero kernel and leaves boundedness for all 1 < p < infinity intact.

## Appendix C.2 audit

Lemma C.2, printed page 126, is covered with its literal hypotheses by
[`ModifiedHilbertKernel.lean`](NLS/Fourier/ModifiedHilbertKernel.lean) and
[`ModifiedHilbert.lean`](NLS/Fourier/ModifiedHilbert.lean), in `NLS.Fourier`.
The displacement sequences s and r are arbitrary elements of ℓ∞. Their
nodes are sigma_n=pi*n+s_n and rho_k=pi*k+r_k. The hypothesis
`HilbertLatticeSeparated s r c` is precisely
`c^(-1)*|k-n| <= |rho_k-sigma_n|` for k != n, with c>0.

For every 1<p<infinity, `modifiedHilbert` is a continuous complex linear
operator on ℓp. `modifiedHilbert_source_apply` identifies it with
`pi * sum_{k != n} a_k/(rho_k-sigma_n)` on every input;
`summable_norm_modifiedHilbert_source_series` proves absolute convergence.
`norm_modifiedHilbert_le` gives the operator norm bound
`C_p+c*(norm(s)+norm(r))*norm(hilbertSquareCoeffs)`.
`exists_modifiedHilbert_uniform_bound` explicitly chooses the bound before
s and r, uniformly over prescribed upper bounds for their norms.

No smallness, real-valuedness, or ordering of the two displacements is
required. The diagonal is omitted even when rho_n differs from sigma_n.
A common translation of any size recovers the ordinary Hilbert operator,
checking the exact pi normalization. The square-kernel correction also
extends to p=1 and p=infinity; no such endpoint claim is made for the full
operator. Only the valid boundedness part of C.1 is used.

## Appendix D.1–D.3 audit

The declarations in this section are in `NLS.ComplexAnalysis`.
[`SignedProductEstimates.lean`](NLS/ComplexAnalysis/SignedProductEstimates.lean)
uses A=sum(u), S=sum(norm(u)), B=sum(norm(u)^2), and P=prod(1+u).

| Source statement | Public theorem | Scope |
| --- | --- | --- |
| Lemma D.1, p. 126 | `norm_tprod_one_add_sub_one_le_signed_sum` | Exactly `norm(P-1) <= norm(A)*exp(S)+B*exp(S+S^2)`, for absolutely summable complex inputs with norm(u_i)<=1/2. |
| Remark D.2, p. 126 | `norm_tprod_one_add_sub_one_le_exp_sub_one_le` | Both printed inequalities `norm(P-1) <= exp(S)-1 <= S*exp(S)`; individual coefficients need not be small. |
| Remark D.3, p. 127, signed-sum interpretation | `norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` | Exactly `norm(P-1-A) <= norm(A)^2*exp(S)/2+B*exp(S+S^2)` with A the complex sum, including the half-unit boundary. |
| Literal reuse of D.1's A in D.3 | `printed_D3_absolute_linear_term_fails` | An admissible single negative coefficient refutes subtraction of the absolute sum. See `SOURCE_ERRATA.md`; the literal notation is not marked proved. |

The results apply to arbitrary index types and therefore to the printed
integer sequences. Infinite products are unconditional and are justified
by absolute summability. The proof keeps the stronger intermediate bound
`norm(P-exp(A)) <= B*exp(S+B)` before using B<=S^2. The logarithmic remainder
is bounded by B, and the exponential Taylor estimate retains the exact
factor 1/2. Finite cancelling-pair examples check that signed cancellation
is preserved. The D.4–D.9 audit below is scoped to the statements explicitly listed.

### Lemma D.4 and the displaced-root separation assertion

D.4, printed page 127, is now proved for every finite 1 <= p < infinity:

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal deleted product and joint analyticity | `tendsto_appendixDDeletedProduct`, `analyticOnNhd_appendixDDeletedProduct` | Exact source signs and normalization, including p=1. Uniform cutoff convergence on compact spectral sets over bounded displacement sets is supplied by `tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite`. |
| Roots listed with their multiplicities | `analyticOrderAt_appendixDDeletedProduct` | At every complex point, the order equals the cardinality of `displacedRootIndices a z` after erasing the omitted index. No injectivity hypothesis. |
| Simple roots and simple reciprocal poles for a simple sequence | `analyticOrderAt_appendixDDeletedProduct_of_injective`, `meromorphicOrderAt_inv_appendixDDeletedProduct_of_injective` | Every retained root has order one, and the reciprocal has meromorphic order minus one. |
| Meromorphic reciprocal and its printed product formula | `meromorphicAt_inv_appendixDDeletedProduct`, `tendsto_inv_appendixDDeletedProduct` | Meromorphic at every point; the literal negative reciprocal cutoffs converge away from retained roots. |
| Positive separation of simple sequences (preceding D.4) | `exists_uniform_displacedRoots_separation` | A positive lower bound for every distinct pair, for arbitrary injective finite-exponent displacements. No quarter-pi localization assumption. |

`DisplacedProductOrders.lean` uses properness to obtain finite root fibers
and isolating discs, then Rouche stability to pass finite cutoff orders to
the entire limit. `AppendixDProductMultiplicities.lean` also computes exact
meromorphic orders of full and deleted reciprocals, including higher-order
poles. The collision examples at p=1 check a double root, removal of one
occurrence, removal of an unrelated root, and the resulting pole orders.

### Lemma D.5: locally uniform exterior sine asymptotic

D.5, printed page 128, is now proved for every finite 1 <= p < infinity:

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal full product and joint analyticity | `tendsto_appendixDProduct`, `analyticOnNhd_appendixDProduct` | Exact negative product normalization, free value sin(z), including p=1. |
| Prescribed roots | `appendixDProduct_eq_zero_iff`, `analyticOrderAt_appendixDProduct` | Exactly the prescribed roots, counting repeated indices. |
| Source exterior Pi | `appendixDExterior_eq_compl_iUnion_ball` | Exactly the complement of the union of open quarter-pi discs, retaining their boundaries. |
| Uniform exterior error, locally uniform threshold | `exists_local_appendixDProduct_div_sin_bound` | For every a and epsilon > 0, there are eta > 0 and R > 0 that work for every b with norm(b-a) < eta and every exterior z with R <= norm(z). |
| Literal strict supremum inequality | `exists_local_appendixDProduct_div_sin_sup_lt` | The supremum of the quotient error over Pi and norm(z) > R is strictly below epsilon, with the same R for all b in the selected neighborhood. |

`LocallyUniformExteriorResolvent.lean` upgrades strong exterior decay at a
fixed input using the common operator bound. `AppendixDExteriorAsymptotic.lean`
then uses the exponential absolute-product estimate of D.2. The neighborhood
may depend on the tolerance, as in the source's explicit threshold formulation.
There is no injectivity or localization restriction on the displaced roots.
The strict supremum is proved via a uniform half-tolerance bound, rather
than inferred from individual strict inequalities at each spectral point.

Focused examples check the disc boundary, the zero-displacement quotient,
and both neighborhood and supremum estimates at p=1, as well as the
supremum estimate at p=3. D.5 does not settle the separate printed
spectral-height bound above p=2.

### Lemma D.6: relative products for arbitrary bounded reference roots

D.6, printed pages 128-129, is proved for every 1 < p < infinity.
Unlike the earlier free-lattice and spectral-midpoint special cases,
this result allows any bounded reference displacement and any bounded
numerator displacement with ell^p difference. The hypothesis is exactly
the pointwise lower bound on the distant open quarter-pi discs.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Reference separation | `AppendixDReferenceSeparated` | Every point of each disc with abs(n) >= N, every m != n, and the source constant c > 0. |
| Convergence of the omitted ratios | `sourceLemmaD6_multipliable` | Literal ratios for both bounded sequences; vanishing numerator factors are allowed. |
| Uniform ell^p disc error | `exists_appendixDRelativeProductSup_normBall` | A least majorant in ell^p, zero off the selected tail, norm <= C times the actual difference norm. Constants fixed before inputs and cutoffs. |
| Literal powered disc suprema | `sourceLemmaD6PowerSup`, `sourceLemmaD6` | Summability and both sum <= C times norm(difference)^p and the printed sum <= L times norm(difference). |
| Uniformity and the later cutoff N1 | `sourceLemmaD6` | Constants depend only on c, p and the two norm-ball radii; every K >= N is allowed. |

The signed reciprocal row plus a global quadratic product remainder
proves a stronger conclusion than the source's small-tail argument:
no additional cutoff smallness or simplicity of the reference sequence
is needed. Therefore every cutoff satisfying the printed sufficient
condition is covered. The linear-norm displayed right side is proved
literally by absorbing a bounded power of the difference norm into the
norm-ball constant; it is not silently replaced by a p-power right side.
Independent sampling establishes control of all disc suprema at once.

Focused examples use a nonzero constant bounded reference displacement,
check zero perturbations and a vanishing retained numerator, and instantiate
the two-sequence theorem at p=3 with constants preceding both cutoffs.
The following audit treats D.7; later statements still require their own source comparisons.

### Remark D.7: the signed quadratic product remainder

D.7, printed page 129, is proved for every 1 < p < infinity under the
arbitrary-reference hypotheses of D.6. The actual disc-supremum sequence
belongs to ell^(p/2), which is stronger than the printed sum-space result.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Signed linear term | `sourceRemarkD7Remainder`, `sourceRemarkD7Remainder_eq` | Exactly the omitted product minus one minus the sum of (sigma_m-rho_m)/(rho_m-z); no absolute value replaces the signed sum. |
| Literal supremum over each source disc | `sourceRemarkD7Sup`, `sourceRemarkD7_mem` | The norm supremum on the selected open quarter-pi discs is in ell^(p/2), extended by zero on the omitted finite head. |
| Printed ell^(p/2) + ell^(1+) assertion | `sourceRemarkD7` | A half-exponent sequence plus one CoeffOnePlus sequence; the latter can be zero. |
| Uniformity inherited from D.6 | `sourceRemarkD7_uniform` | One bound for both displacement norm balls, chosen before both sequences and cutoffs, valid for every K >= N. |
| Range 1 < p < 2 | `exists_squaredAbsoluteRows`, `exists_appendixDQuadraticSup` | Powered Young and a quasi-norm addition bound avoid imposing a Banach assumption on p/2. |

The global signed product remainder is bounded by exp(S)/2 times
(norm(A)^2+B), with A the complex sum, S the absolute sum, and B the
square sum. The proof compares finite products with exp(A), then passes
to the unconditional limit. This avoids the source proof's small-factor
step and handles vanishing numerator factors. The signed-row square and
the reciprocal-square convolution both lie in ell^(p/2), so no nonzero
ell^(1+) error is needed. The formula in D.7 explicitly subtracts the
signed sum and is unaffected by the D.3 notation correction.

The tail restriction is inherited from the D.6 separation hypothesis;
unseparated head discs may contain poles and are not included in this
claim. Every later cutoff, including a source-admissible small-tail
cutoff, is covered. Focused tests exercise p=3/2 and p=3, large cancelling
factors, zero perturbations, and uniform constants preceding all inputs.
The following audit treats D.8; later source statements remain to be audited.

### Lemma D.8: the two deleted sine-product asymptotics

D.8, printed page 129, is proved for every 1 < p < infinity, for arbitrary
ell^p displacements and all open quarter-pi source discs. There is no
restriction to a distant tail or to simple or small root displacements.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal left-side product and normalization | `tendsto_appendixDNormalizedDeletedProduct` | The positive symmetric product omitting n, divided by pi_n, converges to `jointDeletedSingleSpectralProduct n`; no factor of -2 or pi_n is dropped. |
| Multiplicative sine-product form | `appendixDDeletedProduct_eq_free_mul_relative`, `sourceLemmaD8` | Exact identity with the filled sine quotient and an actual ell^p relative-error sequence, for any independent disc samples. |
| Additive sine-product form | `appendixDDeletedProduct_sub_free_eq`, `sourceLemmaD8` | The same product is the filled quotient plus an actual ell^p additive-error sequence. |
| Uniformity over whole discs and displacements | `sourceLemmaD8_uniform` | Both literal norm-supremum sequences lie in ell^p, bounded by C times the input norm with C fixed on each norm ball. |
| Local uniformity in the displacement | `sourceLemmaD8_locally_uniform` | A common constant on the unit neighborhood of every input, for all independent samples. |
| The printed quotient and its removable center | `sourceLemmaD8_off_center`, `sourceLemmaD8_center` | Exactly sin(z)/(z-pi*n) away from the center, with value cos(pi*n) at the center. |

The finite-cutoff factorization proves the identity even at the free
center. The source's sine quotient is interpreted with its usual removable
extension there; the totalized quotient 0/0 would not have the correct
value. This is an explicit analytic convention, not a claimed equality
with Lean's raw division at zero. The entire deleted product is already
normalized by D.4. D.6 at the free reference lattice supplies the common
relative-error majorant on every disc, and the uniform sine-quotient bound
supplies the additive one. Actual suprema are constructed from these
majorants, rather than inferred from bounds on fixed sample sequences.

Focused checks include the value -1 at a negative odd free center, the
value 1 at zero, invariance under moving only the omitted root, a negative
omitted-index cutoff, p=3 norm-ball bounds, and p=3/2 local uniformity.
The following audits treat D.9 and E.1-E.3; later statements still require source-level comparison.

### Lemma D.9: the full sine-product asymptotic

D.9, printed page 130, is proved for every 1 < p < infinity and arbitrary
ell^p displacements. Every open quarter-pi source disc is included,
with arbitrary independent samples and with no simplicity or smallness condition.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Literal negative-product normalization | `appendixDProduct_eq_displacedBoundaryProduct`, `sourceLemmaD9_of_cutoff_limits` | The existing negative symmetric cutoff limit is exactly the entire boundary product; the sampled assertion also accepts any function specified by those limits. |
| Restoring the omitted factor | `appendixDProduct_sub_sin_eq_relative_error` | Exact identity `f(z)-sin(z) = -Q_n(z) * (a_n + (sigma_n-z) * error_n(z))`, including the filled center value. |
| Sampled full-product asymptotic | `sourceLemmaD9`, `sourceLemmaD9_mem` | An actual ell^p error for every independent disc sample sequence, including the free centers. |
| Disc-supremum control | `sourceLemmaD9Sup`, `sourceLemmaD9_uniform` | The literal norm suprema belong to ell^p with one bound on every displacement norm ball. |
| Local uniformity in sigma | `sourceLemmaD9_locally_uniform` | One constant on the unit neighborhood of each displacement, uniformly for all independent samples. |

The proof uses the existing entire-boundary disc majorants after identifying
the normalization, then constructs the literal suprema and the sampled error.
The independent restored-factor identity checks the source proof's sign.
Moving only the root at a free center gives minus cos(pi*n) times that
root displacement; focused examples check n=0 and n=-1. Other examples
exercise literal cutoff-defined functions and p=3 and p=3/2 uniform bounds.
No source correction is needed for D.9.

The following audit treats E.1's full interpolation formula, beyond the
earlier zero-sample uniqueness result.

### Lemma E.1: interpolation at arbitrary simple displaced roots

E.1, printed pages 130-131, is proved for every 1 <= p < infinity, with
an explicit correction of the product index m in Z to m != n. The source's
own residue calculation uses the latter. See SOURCE_ERRATA.md.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Entire numerator and literal supremum decay | `appendixESineCircleSup`, `norm_sineQuotient_le_appendixESineCircleSup`, `sourceLemmaE1` | The supremum is over the whole circle of radius N*pi+pi/2; its finiteness is derived, and its limit to zero is the actual hypothesis. |
| Arbitrary simple displaced sequence | `sourceLemmaE1` | Any injective roots pi*n+a_n with a in ell^p; complex roots and p=1 are included. |
| Literal cardinal product | `tendsto_appendixEInterpolationKernel` | The symmetric product of (sigma_m-z)/(sigma_m-sigma_n), omitting n, converges to the ratio of deleted products. |
| Correct residue coefficient | `deriv_appendixDProduct_at_root`, `appendixEInterpolationKernel_eq_deriv` | The full derivative at sigma_n is minus the deleted product divided by pi_n; the coefficient is exactly g(z)/(g'(sigma_n)*(z-sigma_n)). |
| Finite residue identity | `eventually_appendixE_interpolation_error` | All sufficiently large source circles contain precisely the symmetric root block and have the exact derived outer Cauchy error. |
| Vanishing error and convergence | `eventually_appendixE_outerCauchy_small`, `tendstoUniformlyOn_appendixEQuotientInterpolation` | No rate of source decay is assumed; quotient residue sums converge uniformly on bounded zero-free evaluation sets. |
| Full interpolation formula | `sourceLemmaE1`, `sourceLemmaE1_literal` | Symmetric sums converge to f(z) at every z off the root set; the literal version specifies both product and sum cutoffs in one theorem. |

The source contour argument determines symmetric convergence, which is
explicit here. No unconditional `HasSum` or absolute convergence is claimed.
The product index typo is not silently interpreted through division by
zero: `appendixE_all_index_cutoff_eq_zero` checks the obstruction formally.
`appendixEInterpolationKernel_root` gives the cardinal values one and zero.

Focused examples include p=1 and p=3, a negative omitted index, and a
nonreal single-root displacement. The end-to-end sinc example derives
the literal supremum-decay hypothesis and reconstructs the nonzero value
one at z=0 when the zero-index root is moved to i. E.2 and E.3 are audited below.

### Lemma E.2: the identity theorem for real subspaces

E.2, printed page 131, is proved for arbitrary continuous complexifications
on connected open domains that meet the included real space. The necessary
nonempty-real-slice interpretation of "neighborhood" is explicit. The
arbitrary-open-domain reading without that condition is refuted; see
SOURCE_ERRATA.md. Both uses in the dissertation start at real-type potentials.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| An arbitrary real space and its complexification | `RealComplexification` | A continuous real-linear equivalence from R times R to E, with the imaginary axis mapped to i times the included real axis; no isometry or projection-norm restriction. |
| Local uniqueness from the real slice | `DifferentiableOn.eventually_eq_zero_of_continuous_real_form` | Real and imaginary parts need only be continuous at zero, vanish there, and give the decomposition; no contractivity assumption. |
| Connected open domain | `sourceLemmaE2` | Vanishing on the nonempty real slice implies vanishing throughout the domain; no convexity assumption. |
| A neighborhood of a real point | `sourceLemmaE2_of_real_point` | An explicit included real point in the domain supplies the required nonemptiness. |
| Identity of two analytic maps | `sourceLemmaE2_eq` | Real-slice agreement gives agreement on the domain, also for complete complex Banach targets. |
| Necessity of the real-slice hypothesis | `sourceLemmaE2_realSlice_condition_needed` | Constant one on the ball of radius 1/2 about i satisfies real-slice vanishing vacuously but does not vanish on the domain. |
| The actual Fourier source real form | `sourceLemmaE2_realType` | Every finite Banach exponent, including p=1, and a connected open domain containing just one real-type source. |

The coordinate model encodes the usual unique decomposition x+i*y through
a topological real-linear isomorphism. Continuity replaces the older local
helper's contractive projections; the analytic identity theorem replaces
convexity in the global step. The source's Taylor-series proof is thus
replaced by a complex-line uniqueness argument with the same intended scope.

Focused checks use the complex plane with i removed and formally verify
that this domain is connected but not convex. They also check a translated
real base point, a paired complex target, the real-slice obstruction, and
the actual source spaces at p=1 and p=3.

### Lemma E.3: uniform Fourier-Lebesgue bounds for shifted exponentials

E.3, printed page 131, is proved for arbitrary complex frequencies with
|nu_n-n*pi| <= pi/4 outside a finite index block. Every q>1 is covered,
including infinity. No periodic endpoint matching is assumed: the
coefficients are the actual integrals on the unit interval.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Actual Fourier coefficients of exp(i*nu*x) | `exponentialFourierCoefficients_apply` | The coefficient-space element evaluates to the literal unit-interval Fourier integral. |
| Modulation and Fourier normalization | `intervalFourierCoefficient_exponential_modulation`, `intervalFourierCoefficient_exponential_lattice` | Integer modulation shifts the Fourier index; free pi-lattice modes recover the exact overlap integral. |
| Uniformity in the lattice index | `norm_exponential_residual_frequency_le`, `norm_exponentialFourierCoefficients_modulation` | Removing n/2 leaves norm at most 5*pi/4, including negative odd n; modulation preserves the full sequence norm. |
| Reciprocal decay in the printed proof | `norm_intervalFourierCoefficient_exponential_difference` | A common explicit constant bounds the literal difference coefficient by 1/(1+abs(n-2*m)) for every near-lattice index and every Fourier mode. |
| A common tail constant | `sourceLemmaE3_tail` | Positive constant depends only on q, before the sequence and cutoff. |
| Arbitrary finite head | `sourceLemmaE3` | All-index positive norm bound absorbs the unrestricted exceptional frequencies. |
| Literal O(1) conclusion | `sourceLemmaE3_bigO` | Boundedness as the absolute integer index tends to infinity, for every q>1 including infinity. |

Focused examples check q=3/2 and infinity, negative even and odd frequency
normalizations, a complex displacement exactly on the pi/4 boundary, and
a large exceptional imaginary frequency at index zero. No correction to
E.3 is needed. F.1-F.3 are audited below.

### Lemma F.1: critical-point bounds in terms of the periodic gap

F.1, printed pages 131-132, is proved with both printed constants. Its
first part covers every collapsed complex point in a single connected
almost-real domain, and its second part gives a common neighborhood for
all signed indices around each real source. No source correction is needed.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| One complex domain for every index | `exists_local_source_allCriticalGapQuotients_analytic`, `nonempty_sourceCriticalGapAnalyticDomain` | Uniform distant-index analyticity plus finitely many head neighborhoods; the connected domain contains all real sources. |
| Compatibility with earlier choices of W_p | `exists_sourceCriticalGapAnalyticDomain_within` | The domain can be chosen inside any prescribed open set containing the real locus. |
| Continuity without continuous endpoint labels | `SourceCriticalGapAnalyticDomain.continuousAt_gap_norm`, `.analyticAt_offset` | Gap magnitude is the square root of the norm of its analytic square; the exact squared-gap identity gives analytic critical offset. |
| F.1(i): constant 1/2 at a collapsed gap | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_i` | Every complex base point in the domain with zero selected gap; an open neighborhood remains inside that domain. |
| Stronger local collapsed-gap estimate | `SourceCriticalGapAnalyticDomain.exists_collapsedGap_bound` | Any positive constant times gap magnitude is valid on a sufficiently small neighborhood; no division by the gap. |
| Uniform tail control | `exists_local_sourceCriticalOffset_small_gap_tail` | A common cutoff and source neighborhood for any positive linear gap constant, at all positive and negative tail indices. |
| F.1(ii): constant 1 for all indices | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_ii` | One complex neighborhood around each real source, including every collapsed or noncollapsed finite-head gap. |
| Both statements on the same constructed domain | `sourceLemmaF1` | Every finite exponent strictly above one, an open connected domain containing the real locus, and the two source conclusions with literal canonical spectral coordinates. |

The proof uses the already proved exact squared-gap identity instead of
repeating the source's Rouche argument. The quotient is analytic even at
complex collapsed points of the constructed domain. Part (ii) uses real
interlacing to leave a strict margin at open head gaps; collapsed head gaps
use part (i), and a common small tail supplies the remaining indices.
Focused checks include p=3/2 and p=3, a negative index with no real-base-point
hypothesis, exact zero-source values, an actual nonzero real source, and
compatibility with an earlier prescribed domain. F.2 is audited below.

### Lemma F.2: analyticity of the actual endpoint-averaged integral

F.2, printed pages 132-134, is proved for the literal half-sum of two
improper endpoint integrals of Delta′/sqrt_c(Delta^2-4). One source
neighborhood supports every signed gap and every point on its assigned
isolating boundary. Complex collapsed points are included. The statement
is unchanged; two intermediate proof formulas need correction as recorded
in SOURCE_ERRATA.md.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Genuine nonsingular path integrals | `HasPolygonalIntegral`, `exists_hasPolygonalIntegral`, `polygonalIntegral_spec` | Finite sums of actual curve integrals along integrable straight segments; connectors exist on every open connected domain. |
| Genuine improper endpoint integration | `endpointPolygonalIntegral`, `tendsto_polygonalIntegral_endpoint` | Relative limit as the start approaches a singular endpoint through the domain; primitive boundary values give convergence. |
| Actual source differential and endpoint average | `sourceAbelianDifferential`, `sourceAbelianEndpointIntegral`, `sourceAbelianEndpointAverage` | Canonical discriminant derivative and canonical root; both actual periodic endpoints and the factor 1/2 appear in the definition. |
| Nonvacuous endpoint limits | `SourceFullAbelianUniformCauchyFamily.endpoint_mem_closure_rootDomain`, `.tendsto_endpointPolygonalIntegral` | Every endpoint, including a collapsed one, is approached through the cut complement; the limit filter is nontrivial. |
| Equality with the previously constructed primitive | `.endpointIntegral_eq`, `.endpointAverage_eq` | Either endpoint integral equals the full primitive normalized at that gap, hence so does their average. |
| Agreement with conventional admissible paths | `.endpointCurveIntegral_eq` | Every integrable C1 path whose interior avoids the cuts has the same value; no artificial endpoint value of the differential is used. |
| F.2 on each whole boundary circle | `.sourceLemmaF2` | One source ball, every gap and every boundary point, without a nonzero-gap hypothesis. |
| Full almost-real source statement | `sourceLemmaF2` | Connected open domain containing all real sources; every complex point has a common neighborhood supporting all boundary functions and their literal integral identification. |
| Exact free normalization | `sourceAbelianEndpointAverage_zero` | Value -i*nu+i*pi*n at every off-lattice evaluation point, including negative indices and collapsed free endpoints. |

The proof transfers joint analyticity through equality with the canonical
primitive and avoids the problematic dominated-convergence calculation.
The common-path coefficient check and the counterexample to the printed
real majorant are in `AppendixFProofAudit.lean`. Focused examples include
a nonconvex punctured domain, its improper endpoint integral, p=3/2 and
p=3, and nonzero free values. Corollary F.3 is audited below.

### Corollary F.3: analyticity between actual spectral endpoints

F.3, printed page 134, is proved unchanged. The integral is a second relative
endpoint limit of the actual improper polygonal integrals used in F.2.
For an initial endpoint in gap n and a terminal endpoint in gap m, its value
is i*pi*(n-m), including complex collapsed gaps and either endpoint choice.

| Source requirement | Public theorem(s) | Scope |
| --- | --- | --- |
| Actual endpoint-to-endpoint integration | `sourceAbelianEndpointToEndpointIntegral`, `SourceFullAbelianUniformCauchyFamily.tendsto_endpointIntegral` | Iterated relative limits of finite sums of genuine curve integrals; terminal limit convergence is proved. |
| Exact endpoint normalization | `.endpointToEndpointIntegral_eq` | Value i*pi*(n-m) for all signed indices and either endpoint, with nontrivial endpoint filters. |
| Agreement with admissible paths | `.endpointToEndpointCurveIntegral_eq` | Every integrable C1 path with interior off the cuts agrees with the improper definition. |
| Arbitrary endpoint selections | `.endpointToEndpointIntegral_analytic` | Pointwise membership in each endpoint pair is enough; no continuity of the choices or nonzero-gap assumption. |
| Full source statement | `sourceCorollaryF3` | One connected open almost-real domain supports all gap pairs and all pointwise endpoint selections, including every complex base point. |
| Collapsed free normalization | `sourceAbelianEndpointToEndpointIntegral_zero` | Actual integral between pi*n and pi*m at zero equals i*pi*(n-m). |

Focused checks cover p=3/2 and p=3, opposite signs between gaps -3 and 2,
the vanishing same-gap integral, arbitrary predicates switching endpoint
choices, admissible C1 paths, and the common domain. The Appendix G audits
follow below; its existing implementation is not treated as automatic
coverage of every printed statement. The required unresolved p>2 spectral
height is unchanged.

### Lemma G.1: prerequisite stages

Current status: `sourceLemmaG1` now proves the estimate on the full physical
L2 domain in the Hermitian operator norm; see the final G.1 table below.
The following stages record how the earlier domain and norm gaps were closed.

The literal dependence on the potential's Hilbert L2 norm and on the
first Born term's L2 norm in time is now proved for the constructed
continuous-potential solutions. This replaces neither the full printed
L2 domain nor its matrix norm convention. Those requirements are supplied
by the subsequent stages below.

| Required ingredient | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Variable-forcing comparison | `le_forcing_add_exp_integral_mul` | Continuous scalar functions; integrating-factor proof retains terminal forcing and integral of coupling times forcing. |
| Exact L2 coefficient | `integral_mul_le_sqrt_sq_mul_sqrt_sq`, `le_forcing_add_L2_bound` | Actual square integrals give A*exp(A) on [0,T], T<=1; no supplied bound on the error. |
| Actual variable coupling | `classicalNormalizedRemainder_le_firstBorn_add_variable_integral` | Original signed Duhamel equations, with pointwise potential norm inside the integral rather than the potential supremum. |
| Actual first Born time dependence | `continuous_oscillatoryIntegral`, `continuous_classicalFirstBornVector`, `classicalNormalizedFirstBorn` | Continuity proved from the literal oscillatory integral, without differentiating the potential. |
| Hilbert L2 potential budget | `classicalPotentialL2Norm`, `sqrt_integral_potential_norm_sq_le` | Integral of the sum of both coordinate norm squares; controls every truncated pointwise-norm square integral. |
| Actual vector solution estimate | `classicalNormalizedRemainder_le_L2_firstBorn` | All continuous potentials, complex spectral parameters, initial vectors, and times in [0,1]; no nonzero-frequency or smoothness restriction. |
| Actual matrix estimate | `classicalNormalizedMatrixRemainder_le_L2_firstBorn` | Both columns of M-E and of the actual first Born matrix, explicitly using the elementwise maximum matrix norm. |
| Arbitrary L2 potentials | Completed in later stages below | L2-stable extension, original integral equation, and full estimate. |
| Matrix norm | Hermitian operator norm proved below | The convention is explicit in the related author preprint; the 2014 edition of [23] has not been checked directly. |

Checks include an actual nonzero triangular potential at zero frequency,
both-coordinate Hilbert norm sqrt(2), a variable potential (t,0) with
Hilbert L2 norm sqrt(1/3), free zero error for every complex frequency,
and a scalar exponential solution with time-dependent forcing. No source
erratum is asserted by this partial G.1 audit.

The related author preprint [Normal form theory for the NLS equation,
arXiv:0907.3938](https://arxiv.org/pdf/0907.3938), printed page 7,
explicitly uses the matrix operator norm induced by the Hermitian vector
norm. Its Lemma 2.1 (printed page 12) gives the variable-forcing estimate.
This supplies a concrete next target: use Euclidean vector/operator norms,
without multiplying the printed coefficient by a norm-equivalence constant.
The 2014 book [23] is a later publication, so its convention has not been
verified directly from that edition.

### Lemma G.1: Hermitian operator norm, continuous-potential stage

The genuine Hermitian operator-norm estimate is now proved, with the literal
Hilbert L2 coefficient A*exp(A). This closes the norm gap in the preceding
continuous-potential result. The arbitrary-L2 domain is supplied by the
subsequent extension and limit passage below.

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Genuine Hermitian vectors | `hermitianPair_norm`, `hermitianPair_norm_sq` | Euclidean norm on both complex coordinates, using WithLp 2. |
| No norm-conversion loss | `hermitianPair_norm_diagonal_le`, `norm_classicalHermitianDuhamelKernel_le` | Direct diagonal and off-diagonal bounds with coefficient one and the correct signed free exponential. |
| Exact off-diagonal operator norm | `norm_hermitianColumns_offDiagonal` | Maximum of the two scalar magnitudes. |
| Actual vector integral identity | `classicalHermitianRemainder_duhamel` | Transport of both original signed Duhamel equations, through a continuous linear equivalence used only for algebra and integration. |
| Actual vector Volterra bound | `classicalHermitianRemainder_le_firstBorn_add_integral` | Weighted Hermitian vector norm with the original pointwise potential coefficient. |
| Actual operator identification | `classicalHermitianRemainderOperator_eq_matrix`, `classicalHermitianFirstBornOperator_eq_matrix` | Operators are precisely M-E and the actual first Born matrix. |
| True induced operator norm | `classicalHermitianOperator_le_L2_firstBorn` | All initial vectors are bounded before taking the operator norm; exact A*exp(A) coefficient and actual first Born L2 time integral. |
| Exact first Born formula | `classicalNormalizedHermitianFirstBorn_eq` | The off-diagonal operator norm is the maximum of the oscillatory integral magnitudes. |
| Arbitrary L2 potentials | Proved in later stages below | Density, stability, the original equations, and passage of G.1 to the physical L2 space. |

The Hermitian convention is explicit on printed page 7 of the related
author preprint [arXiv:0907.3938](https://arxiv.org/pdf/0907.3938). The 2014
book [23] has not been read directly. Checks distinguish this operator norm
from the entrywise maximum, attain the signed kernel bounds in both
half-planes, and exercise zero time, arbitrary complex free frequency,
and a nonzero potential at zero frequency. No extra factor is accepted in
place of the printed coefficient.

### Lemma G.1: physical L2 stability and uniform extension

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Exact physical norm | `norm_continuousPotentialL2Class`, `dist_continuousPotentialL2Class` | Hilbert sum of both coordinate square integrals, with no normalization factor. |
| Full physical L2 density | `denseRange_continuousPotentialL2Class`, `exists_continuousPotential_L2_approximation` | Arbitrary a.e. L2 classes; no periodicity or endpoint condition. |
| Quantitative solution stability | `norm_classicalSolution_sub_le_L2`, `dist_classicalSolutionCurve_le_L2` | Actual classical solutions, uniformly in time and on L2-bounded potential sets. |
| Uniform extension exists | `cauchy_classicalSolutionCurve_L2`, `tendsto_classicalSolutionCurve_L2` | Convergence proved before relying on the limit; all physical L2 potentials and complex spectral parameters. |
| Approximation independence | `tendsto_solutionCurve_of_tendsto_L2` | Every approaching family, along any filter, has the same uniform limit. |
| Exact recovery and normalization | `l2SolutionCurve_of_continuous`, `l2SolutionCurve_zero`, `l2SolutionCurve_free`, `l2SolutionCurve_zero_initial` | Entire classical curves, arbitrary initial values, zero initial vector, signed free solution. |
| L2 growth bound | `norm_l2SolutionCurve_le` | Uniform curve norm bounded by ||v|| exp(||z||+||u||_2). |
| Original L2 equation and G.1 | Proved in later stages below | The original equations and the full Hermitian estimate are now proved. |

The uniform-limit construction is now supplemented by the actual integral
and a.e. differential equations in the next stage. Its defining convergence
alone was not counted as proof of those equations. Public checks include a discontinuous
step potential through `intervalL2OfFunction`, distinct approaching
sequences, both potential coordinates, and the free frequency signs.

### Lemma G.1: the original equation for arbitrary physical L2 potentials

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual scalar integral pairing | `intervalL2_integral_mul_eq_inner`, `continuous_intervalL2_integral_mul` | Ordinary representative-based integrals on [0,t]; joint continuity in L2 and uniform norms via an exact Hilbert inner-product identity. |
| Coefficient integrability | `intervalIntegrable_l2ODECoefficient` | Any physical L2 potential times any continuous vector curve. |
| Continuity of the original vector integral | `continuous_l2ODEIntegral` | Both signed coordinates; potential and curve vary together, for every fixed complex z and t in [0,1]. |
| Exact classical recovery | `classicalSolutionCurve_eq_l2ODEIntegral`, `l2ODEIntegral_of_continuous` | The actual previously constructed classical Volterra equation. |
| Original L2 Volterra equation | `l2SolutionCurve_eq_integral`, `l2SolutionCurve_eq_integral_ofFunction` | The constructed L2 limit solves the original equation at every time, for every complex z and initial vector. |
| Original differential equation | `ae_hasDerivAt_l2SolutionCurve` | Actual derivatives of the curve extension almost everywhere on the physical interval. |
| Physical spectral equation | `ae_physicalOperator_l2SolutionCurve`, `ae_physicalOperator_l2SolutionCurve_ofFunction` | L_phi y = z y with actual coordinate derivatives and any original L2 representative. |
| Full G.1 estimate | Proved in the final stage below | Actual L2 first Born operator, uniform convergence, and passage of the Hermitian bound with the literal coefficient. |

These results require neither pointwise convergence of L2 representatives
nor a continuous representative of the potential. Public checks directly
compute the signed coefficient integral for a discontinuous two-component
step and instantiate both the original integral and differential equations.
No claim of full dissertation completion follows from this milestone.

### Lemma G.1: full physical L2 domain and literal Hermitian estimate

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Uniform L2 primitive | `intervalL2PrimitiveCLM`, `norm_intervalL2_integral_mul_le` | Actual integrals of representatives; bounded complex-linear map to the uniform curve norm. |
| Actual oscillatory integrals | `l2OscillatoryCurve_apply`, `l2OscillatoryCurve_apply_ofFunction` | Exact original kernels with signed complex frequencies and arbitrary L2 inputs. |
| Actual first Born operator and matrix | `l2HermitianFirstBornOperatorCurve_apply`, `l2HermitianFirstBornOperatorCurve_eq_matrix`, `l2HermitianFirstBornOperatorCurve_ofFunction` | Signed off-diagonal entries are the original oscillatory integrals; independent of null-set changes. |
| Genuine Hermitian norm | `l2NormalizedHermitianFirstBorn_eq`, `l2NormalizedHermitianFirstBorn_ofFunction` | Exact maximum of the two scalar oscillatory integral magnitudes; no dimension factor. |
| Uniform first Born convergence | `continuous_l2HermitianFirstBornOperatorCurve`, `continuous_l2NormalizedHermitianFirstBorn` | Continuity from physical L2 potentials into operator and real curves with the uniform norm. |
| Actual square integral convergence | `continuous_curve_squareIntegral`, `integral_l2NormalizedHermitianFirstBorn_sq_of_continuous` | The literal time integral in G.1, with exact classical recovery. |
| Actual remainder M-E | `l2HermitianRemainderOperator_eq_matrix`, `tendsto_classicalNormalizedHermitianRemainder_L2` | Constructed L2 solution columns with the original integral and a.e. differential equations and identity initial matrix. |
| Printed estimate | `sourceLemmaG1`, `l2HermitianOperator_le_L2_firstBorn` | [0,1] × Complex × physical L2; exact weight exp(-|Im z|t), coefficient ||phi||_2 exp(||phi||_2), and actual first Born L2 time norm. |
| Exact classical recovery | `l2FundamentalMatrix_of_continuous`, `l2NormalizedHermitianRemainder_of_continuous`, `l2HermitianFirstBornOperatorCurve_of_continuous` | Existing actual matrices and operators are retained exactly. |

The source formula and domain were checked against printed page 135. A
noncontinuous two-component step is exercised with exact norm one, exact
terminal first Born norm one half, and the literal coefficient exp(1).
The full dissertation is still incomplete. Lemma G.2 requires a separate
comparison of its H1 norm convention, arbitrary time range, and precise
constants; the existing broader Sobolev bounds do not establish it verbatim.


### Lemma G.2: trace and derivative estimate; source norm comparison open

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Cauchy--Schwarz length factor | `integral_norm_le_sqrt_length_mul_L2` | Every t >= 0, arbitrary scalar L2 function; exact sqrt(t). |
| Integration by parts with L2 derivative | `norm_oscillatoryIntegral_weighted_le_L2` | Absolutely continuous functions; actual endpoint values and square integral of the derivative. |
| Actual Hermitian first Born operator | `intervalHermitianFirstBornOperator_weighted_le` | Any nonnegative time and any nonzero complex frequency; no matrix norm conversion factor. |
| Exact existing operator recovery | `intervalHermitianFirstBornOperator_of_continuous`, `intervalHermitianFirstBornOperator_eq_l2` | Equality with the classical operator and with the physical L2 operator of any original representative. |
| Numerical factor (2+sqrt(t))/(2\|z\|) | `intervalHermitianFirstBornOperator_weighted_le_of_trace_L2_bound` | Explicit common bound on both traces and coordinate derivative L2 norms; not an assumed Sobolev embedding. |
| Remainder consequence of G.1 | `l2HermitianRemainder_le_of_firstBorn_uniform`, `l2HermitianRemainder_le_of_firstBorn_uniform_unit` | Full physical L2; exact coefficient, with an optional sharper sqrt(t) factor. |
| Explicit size S | `classicalHermitianFirstBorn_le_traceL2Size`, `classicalHermitianRemainder_le_traceL2Size` | S is exactly max(sup norm(phi), norm(phi_-')_2, norm(phi_+')_2); constants (2+sqrt(t))/(2*abs(z)) and 3/(2*abs(z))(1+c_phi). |
| Physical H1 inputs | `classicalHermitianRemainder_sobolev_le_traceL2Size` | All physical period-two H1 Fourier pairs; regularity proved, no additional AC or derivative premises. |
| Printed interval H1 norm | **Unresolved** | Need its precise convention and a trace/derivative comparison on [0,t]. S is not declared equal to that norm. |

The source was checked at printed page 135. Printed page 103 explicitly
uses the periodic Fourier norm with weights (1+|2*pi*n|)^s; it does not
define the norm on arbitrary intervals [0,t]. A comparison with the combined
endpoint/derivative bound may be needed; a constant-one bound on each
component of S is not presumed. The related author preprint
[arXiv:0907.3938](https://arxiv.org/pdf/0907.3938), printed page 15, defines
the interval Sobolev space via distributional derivatives but does not settle
the required norm comparison in that definition. Its numbering differs from
the cited 2014 book, which has not been read directly. No source discrepancy
is asserted by this milestone. Existing coarse Fourier-norm estimates and
the explicit size S do not establish the literal printed H1 bound.


### Lemma G.2: integral H1 norm and the arbitrary-time interpretation

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Explicit scalar H1 energy | `intervalH1Norm`, `intervalH1Norm_sq` | Unnormalized integral of squared function and derivative magnitudes. |
| Existing energy compatibility | `NLS.Fourier.intervalH1Norm_eq_sqrt_energy` | Exactly the square root of the pre-existing physical squared energy on [0,t]. |
| Explicit Hilbert pair norm | `intervalPairH1Norm_eq_integral` | Exactly the square root of the sum of all four component integrals, with no norm-equivalence constant. |
| Combined trace estimate | `endpoint_variation_le_sample`, `endpoint_variation_le_integrals`, `endpoint_variation_le_three_H1` | Every t in [0,1], complex AC functions with L2 derivatives; no periodicity requirement. |
| Unit-interval Born bound | `intervalHermitianFirstBornOperator_weighted_le_unit_H1` | Actual Hermitian operator; coefficient 3/(2*abs(z)); original H1 functions. |
| Unit-interval remainder consequence | `l2HermitianRemainder_le_unit_H1` | Actual physical L2 solution; same coefficient and exact factor 1+norm(phi)_2 exp(norm(phi)_2). |
| Physical Fourier H1 inputs | `classicalHermitianRemainder_sobolev_le_unit_H1` | No extra AC/derivative premises; actual integral H1 norm retained. |
| Exact constant kernel | `oscillatoryIntegral_const`, `oscillatoryIntegral_neg_const`, `oscillatoryIntegral_const_quarter_period` | Original oscillatory integral and both frequency signs. |
| Arbitrary-time first inequality under the integral convention | `lemmaG2_firstBorn_integralNorm_counterexample`, `g2IntegralNormTestPotential_admissible` | Strict failure for smooth period-one phi=(1,0), t=1/4, z=2*pi; actual left side 1/(2*pi), right side 5/(16*pi). |
| Source's precise interval norm | **Still unresolved** | The counterexample concerns the explicit integral norm only. The unit-interval consequence is independently proved under that convention. |

The endpoint estimates are combined before integration: their variation sum
is at most 2 times the L1 function norm plus 2 times the L1 derivative norm.
Cauchy--Schwarz yields the needed constant three in H1. This avoids assuming
that individual point evaluations have norm at most one. The comparison with the source's
periodic Fourier convention on printed page 103 is proved in the next stage
below. The
arbitrary-time first inequality is not silently replaced or marked complete.


### Lemma G.2: unit-interval estimate in the exact periodic source norm

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Physical unit-period Parseval | `hasSum_sq_periodOneCoefficient`, `integral_sq_periodOneSobolevSynthesis` | Arbitrary L2 interval functions, then every original H1 Fourier input; no factor two. |
| Actual derivative energy | `integral_sq_deriv_periodOneSobolevSynthesis`, `intervalH1Norm_sq_periodOneSobolevSynthesis` | Actual classical derivative, with multiplier 2*pi*i*n at every signed frequency. |
| Original H1 source | `sourcePeriodicH1Potential_coefficients`, `periodic_sourcePeriodicH1Potential` | Both original sequences recovered, actual period-one representative; all complex H1 pairs. |
| Exact Chapter 5 norm | `sourcePeriodicH1_fourierNorm_sq` | Exactly the sum with weights (1+abs(2*pi*n))^2 and both component energies. |
| Constant-one comparison | `graphEnergy_le_sourcePiSobolev_one`, `intervalPairH1Norm_sourcePeriodic_le` | Integral H1 norm <= exact source norm, with no larger constant. |
| Physical/source L2 normalization | `norm_sourcePeriodicH1L2Class` | Original physical L2 norm equals the original source coefficient Hilbert norm. |
| Uniform Born estimate on [0,1] | `sourceLemmaG2_firstBorn_unit` | Actual Hermitian operator, coefficient 3/(2*abs(z)), exact periodic source norm. |
| Unit-interval G.2 remainder estimate | `sourceLemmaG2_remainder_unit` | Actual L2 fundamental solution; exact printed factors and Chapter 5 periodic norm. |
| Existing classical recovery | `sourcePeriodicH1Potential_eq_classical`, `sourcePeriodicH1L2Class_eq_classical`, `sourceLemmaG2_classical_remainder_unit` | Equality with the period-doubled classical curve and the same actual M-E estimate. |
| Arbitrary-time local-norm first inequality | **Still separate** | Not asserted by these unit-interval theorems. The qualified integral-norm counterexample remains valid. |

The periodic source norm is the one explicitly defined on printed page 103.
The comparison preserves its exact coefficient in G.2; equality is tested
on a constant 3-4 pair. The source space is identified through the existing
coefficient-preserving bijection `higherSobolevSourceOneEquiv`, rather than
restricted to a subset of Fourier inputs. The following milestone audits
G.3, with an explicit qualification of the singular epsilon endpoint.


### Lemma G.3: full matrices, exact source balls, and endpoint qualification

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual full matrix Fourier coefficients | `classicalHermitianRemainderFourierCoefficients_apply`, `classicalHermitianShiftedFreeFourierCoefficients_apply` | Bochner integrals of M-E_z and M-E_x; genuine Hermitian operator norm at each Fourier mode. |
| Original period-one H1 inputs | `sourceG3ClassicalCoefficients_potential`, `norm_sourceG3ClassicalCoefficients_le` | Actual source potential recovered on [0,1]; one uniform coefficient bound on each exact Chapter 5 source-norm ball. |
| Full-matrix physical H1 time norm | `sourceLemmaG3_H1` | Actual derivative and integrals; uniform O(1) under eventual bounded displacement from n*pi. |
| Near-free Fourier-Lebesgue decay | `sourceLemmaG3_fourier_decay` | Exact exponent, 0 < epsilon < 1, 1+epsilon <= q <= 2; one common cutoff for each ball and displacement tail. |
| Shifted-free comparison | `sourceLemmaG3_shiftedFree_decay` | Full M(nu_n)-E_(n*pi), with the stronger eventual O(1/abs(n)) displacement hypothesis. |
| q=2 endpoints | `sourceLemmaG3_l2_decay`, `sourceLemmaG3_shiftedFree_l2_decay` | Explicit inverse-index decay, with no epsilon parameter or singular quotient. |
| Printed epsilon=1 expression | **Qualified** | It is 0/0 at its only admissible q=2; no interpretation is assigned. See SOURCE_ERRATA.md. |

Both signed tails are covered, with unrestricted finite initial segments.
The fixed assembly factor four and coefficient-ball conversion factor two
are displayed in the bounds; neither changes the source's Big-O exponents.
A concrete off-diagonal Fourier mode checks that the sequence uses the
actual operator norm (four for entries three and four), rather than the
sum of entry norms. The source-ball domain is all complex H1 via the
existing bijective coefficient identification, not just real sources.

The full dissertation remains incomplete. The G.4 audit follows below;
G.2's arbitrary-time local norm, the required p>2 spectral height, and the
optional original m=1 sharpening retain their previously recorded status.


### Corollary G.4: full-matrix summability on exact source-norm balls

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Literal eventual pi/4 displacement | `sourceCorollaryG4` | One nonnegative lp majorant for the full matrix norms at all signed indices, uniform on each exact Chapter 5 source-norm ball. |
| Full shifted-free comparison | `sourceG4_shiftedFree_uniform_majorant` | Actual M(nu_n)-E_(n*pi), eventual O(1/abs(n)) displacement, arbitrary finite initial spectral values. |
| Uniform tails over spectral families | `sourceG4_remainder_tail_majorant`, `sourceG4_shiftedFree_tail_majorant` | The cutoff and summable majorant precede the spectral sequence and potential quantifiers; common displacement bound and initial cutoff. |
| Whole-sequence membership | `sourceG4_remainder_memlp`, `sourceG4_shiftedFree_memlp` | The actual full-matrix Fourier norms are in lp for every complex period-one H1 source. |
| Actual operator-valued membership | `sourceG4_remainder_operator_memlp`, `sourceG4_shiftedFree_operator_memlp` | The Fourier sequences themselves, with values in the Hermitian-operator coefficient space, form an lp sequence. |
| Complete exponent range | All preceding theorems | Finite real p>1, q>1+1/p, including q>2 and q=infinity; no threshold equality or excluded outer endpoints claimed. |

The source statement on printed page 137 fixes a spectral sequence before
asserting uniformity over potential balls. The whole-sequence majorant may
therefore depend on its finite initial values. The tail statements are
stronger uniform-family results, but do not impose a common bound on
unrestricted finite initial segments. This distinction is explicit in the
quantifier order. The generic near-free majorants allow any O(1) bound,
with the literal pi/4 hypothesis supplied by the source specialization.

Focused checks exercise q=3/2, q=2, q=infinity, a non-Hilbert outer p=3/2,
an arbitrary complex initial spectral value, an actual nonzero 1/abs(n)
displacement, and a common majorant chosen before the spectral family.
G.5's reference and endpoint audit is recorded below.
The dissertation remains incomplete; the previously recorded G.2 local-norm,
p>2 spectral-height, and optional original m=1 obligations remain open.


### Lemma G.5: literal-reference and infinity-endpoint audit

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Actual off-diagonal free gradients | `sourceG5_actual_i_free_upper`, `sourceG5_actual_i_free_lower` | Upper minus component and lower plus component, agreeing with the proof but opposing the printed statement. |
| Original source and both frequency hypotheses | `sourceG5_zero_admissible`, `sourceG5_printed_upper_lattice` | Zero period-one H1 potential, nu_n=n*pi, both printed references equal at every signed index. |
| Literal finite p=2 claim | `sourceG5PrintedUpperErrorCoefficients_diagonal`, `not_memlp_sourceG5PrintedUpperError_norms` | Actual scalar Fourier integral has modulus one at mode n; the norm sequence is not in l2. |
| Full-matrix implication and arbitrary finite exceptions | `not_memlp_sourceG5PrintedError_majorant`, `not_eventually_sourceG5PrintedError_majorant` | No l2 majorant of this component exists, even on any spectral tail. |
| Independent printed infinity endpoint | `sourceG5_triangular_coefficients`, `sourceG5_not_eventually_fourier_l1` | Original smooth period-one H1 source (1,0); a diagonal component fails Fourier l1 at every perturbed lattice index, independently of the off-diagonal reference correction. |

The source formula needs the two off-diagonal superscripts exchanged.
Even with this correction the printed outer p=infinity endpoint fails.
The corrected finite-p full-gradient estimate on exact source-norm balls
is now proved by the full assembly described below. This uses all eight
scalar components and the actual gradient-valued Fourier integrals.
See `SOURCE_ERRATA.md` for the literal formulas and proof discrepancy.
These findings do not change the unresolved G.2 local-norm and required
p>2 spectral-height obligations or the optional original m=1 sharpening.


### Corrected G.5: full-gradient summability on exact source-norm balls

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Full gradient and actual coefficients | `classicalHermitianGradientFourierCoefficients_apply` | Actual Bochner Fourier integral of i times the gradient error; induced norm from Hermitian potential directions to Hermitian matrix operators. |
| Corrected reference identification | `classicalHermitianGradientError_eq_correctedReference` | Exact matrix identity with the upper minus and lower plus component, for any complex source and both frequency arguments. |
| Exact signed lattice reference | `classicalHermitianCorrectedFreeGradientMatrix_lattice` | (-1)^n phase, signed +/-2n waves, and arbitrary potential directions; negative indices included. |
| First finite-p source assertion | `sourceLemmaG5_corrected` | Every finite p>=2, q=p/(p-1), eventual pi/4 displacement, one nonnegative lp majorant on each exact periodic source H1 ball. |
| Second finite-p source assertion | `sourceLemmaG5_shifted_corrected` | Exact lattice reference and eventual O(1/abs(n)) displacement, with the same source-domain and uniformity scope. |
| Generalized exponents | `sourceG5_gradient_uniform_majorant`, `sourceG5_shifted_gradient_uniform_majorant` | Every finite p>1 and q>1+1/p, including inner q=infinity; no outer p=infinity claim. |
| Whole-sequence membership | `sourceG5_gradient_memlp`, `sourceG5_shifted_gradient_memlp`, and the corresponding `norms_memlp` theorems | Actual gradient-valued Fourier sequences and their full operator Fourier norms belong to outer lp, including arbitrary finite initial spectral values. |
| Zero-source consistency | `classicalHermitianGradientError_zero`, `classicalHermitianGradientFourierCoefficients_zero` | Exact cancellation against the actual free reference, at every complex frequency and all q>1. |

A fixed factor eight assembles the scalar bounds in the full induced norm.
The source potential is reconstructed through the existing period-doubling
identification, and its classical coefficient norm is bounded by twice
the exact source norm. The majorant is chosen after fixing the spectral
sequence and before choosing a potential in the ball. No common bound on
arbitrary finite initial spectral values is silently imposed. Both G.5
assertions are proved with the explicit reference correction and finite
outer exponent restriction; the two printed failures remain documented.
G.6 is covered below. The dissertation remains incomplete, with the previously
recorded G.2 local-norm, required p>2 spectral-height, and optional original
m=1 obligations unchanged.


### Corollary G.6: exact source norms and the corrected wave reference

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Discriminant assertion | `sourceCorollaryG6_discriminant` | Unchanged assertion for every finite p>=2, conjugate q, eventual pi/4 displacement, exact H1 source ball and exact finite-q signed pair output norm. |
| Anti-discriminant assertion | `sourceCorollaryG6_antiDiscriminant_corrected` | Same exponent and norm scope, eventual O(1/abs(n)) displacement, reference wave subscripts corrected from -2*n*pi to -2*n. |
| Actual signed Fourier coefficients | `sourceG6DiscriminantCoefficients_fst`, `sourceG6DiscriminantCoefficients_snd`, and the anti-discriminant counterparts | Actual scalar Fourier integrals of i times the gradient or gradient remainder; the first physical index is -k and the second is k. |
| Exact equation (1.2) norm | `sourceG6DiscriminantCoefficients_norm_rpow`, `sourceG6AntiDiscriminantCoefficients_norm_rpow` | Combined coefficient energy for finite q, with the signed first-index reversal. |
| Uniform generalized bounds | `sourceG6_discriminant_sourceNorm_majorant`, `sourceG6_antiDiscriminant_sourceNorm_majorant` | Finite p>1 and finite q>1+1/p; one nonnegative summable majorant for all potentials in the exact source ball. |
| Coefficient-valued membership | `sourceG6_discriminant_source_memlp`, `sourceG6_antiDiscriminant_source_memlp` | The actual signed pair coefficient sequences belong to outer lp; arbitrary finite initial spectral values are included. |
| Vector Bochner integral interpretation | `classicalHermitianDiscriminantGradientCoefficients_apply`, `classicalHermitianAntiDiscriminantGradientCoefficients_apply`, `classicalHermitianAntiDiscriminantGradientCoefficients_lattice` | Separate Hermitian-vector coefficient representation and the actual corrected reference, including negative indices. |
| Printed-reference failure | `half_le_norm_sourceG6PrintedAntiErrorCoefficients`, `not_memlp_sourceG6PrintedAntiError_norms`, `not_eventually_sourceG6PrintedError_majorant` | At zero potential and exact lattice frequencies, the inner l2 norm is at least 1/2 for every nonzero n; no finite spectral head repairs outer l2 summability. |
| Failure in the exact source norm | `not_memlp_sourceG6Printed_pair_norms` | The same obstruction in the exact signed source pair norm, regardless of the second component. |

The majorant is chosen after fixing the spectral sequence and before the
potential. No uniform bound on arbitrary finite initial spectral values is
imposed. The source is the full complex period-one H1 domain, with no
smallness or reality restriction. The separate Hermitian-vector extension
allows inner q=infinity; no exact-source infinity output norm is claimed
here. The source's finite conjugate range is fully covered.

The printed second reference is refuted at p=2 under the source's own wave
definition; the first assertion remains unchanged. See `SOURCE_ERRATA.md`.
G.7's domain and printed wave indices are audited below.
The previously recorded G.2 local-norm, required p>2 spectral-height, and
optional original m=1 obligations remain open. Neither declaration counts
nor the source-label inventory certify completeness.


### Lemma G.7: actual spectral gradients and the corrected half-wave reference

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original complex H1 source | `sourceG7_periodic_representative` | Every original period-one Sobolev source supplies the required physical Sobolev representative; no separate compatibility assumption. |
| Both finite-p estimates | `sourceLemmaG7_corrected`, `sourceLemmaG7_corrected_with_coefficients` | Finite p>=2 and conjugate q; for each exponent one common open complex domain contains the entire real source locus. All signed indices and collapsed periodic gaps are retained. |
| Actual midpoint derivative | `sourceG7MidpointGradient_coefficients` | Exact signed coefficients of the Frechet derivative of the canonical periodic midpoint; first direction k and second direction -k. |
| Actual corrected Dirichlet gradient | `exists_sourceG7_dirichlet_coefficients`, `SourceG7DirichletCoefficients` | Actual Fourier integrals of the normalized squared eigenfunction gradient minus (wave(2*n),wave(-2*n))/2, on the same domain as the summability theorem. |
| Exact source norm | `norm_sourceG7SignedCoordinates`, `sourceG7DirichletGradientError_norm_rpow` | First-index reflection is an isometry; the norm power is the combined Fourier coefficient energy from equation (1.2). |
| Entire real H1 locus | `sourceLemmaG7_real_corrected` | Both estimates at every real H1 source, with no smallness assumption. |
| Correct free reference | `classicalDirichletNormalizedGradient_free_lattice`, `sourceG7_free_signed_coefficients`, `sourceG7DirichletGradientError_zero` | Exact factor one half, physical indices 2*n and -2*n, signed source index -n in both components, and exact cancellation of the actual free derivative. |
| Printed-reference failure | `quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients`, `not_eventually_sourceG7PrintedError_majorant` | Actual error norm at least 1/4 for every nonzero n at the zero H1 source; outer p=2 fails even after removing an arbitrary finite head. |
| Exact-norm obstruction | `not_memlp_sourceG7Printed_pair_norms` | Failure in the exact signed source pair norm, regardless of the second component. |

The exponent is finite, with q conjugate to p. The complex neighborhood
may depend on p, and the same neighborhood supports both estimates and
the actual corrected Fourier-integral representation. These are pointwise
H1 source estimates; no new uniform bound on all source balls in that
neighborhood is asserted. The midpoint assertion is unchanged, and the
Dirichlet reference is explicitly corrected from -2*n*pi to -2*n.
See `SOURCE_ERRATA.md` for the zero-source counterexample.

Appendix H's recurrence/homogeneity statement is covered below; its subsequent
integration-by-parts formulation is the next audit. The G.2 local-norm, required p>2 spectral-height,
and optional original m=1 obligations remain open. Neither source-label
inventories nor declaration counts certify completeness.


### Lemma H.1: the canonical weak density on the printed Sobolev source

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original H^(k-1) source | `weakSobolevRiccatiDensity`, `analyticAt_weakSobolevRiccatiDensity` | Every integer k=s+1>=1 and every complex period-one H^s pair; the next actual recurrence density belongs to H^-1 and depends analytically on the source. |
| Actual recurrence | `weakSobolevRiccatiDensity_apply`, `weakRiccatiNonlinear` | Weak derivative of the last L2 Riccati density plus actual double Fourier convolutions; all nonlinear factors retain at least H1 regularity. |
| Smooth identification | `weakSobolevRiccatiDensity_eq_classical_coefficients` | Exact Fourier integrals of the independently defined classical density u_(s+2), for every smooth periodic pair. |
| Full-source extension | `denseRange_sobolevSourceOfFinsupp`, `eq_of_continuous_of_smooth_sobolevSource`, `weakSobolevRiccatiDensity_unique` | Finite Fourier polynomials are dense in the complex H^s source; the weak density is the unique continuous extension of the actual smooth hierarchy. |
| Leading derivative and polynomial | `sourceLemmaH1`, `sourceLemmaH1_weak` | Coefficientwise and H^-1 equality: u_(k+1)=-b^(k)+q_k, with the exact multiplier 2*pi*i*j and actual lower-jet polynomial. |
| Every polynomial restriction | `sourceLemmaH1_polynomial` | Total weight k+1; after multiplication by the first field, equal field counts and total derivative count at most k-2; each remainder jet has order at most k-2. |
| Actual nonlinear Fourier integral | `sourceH1RemainderCoefficient_eq_integral`, `sourceH1RemainderL2_apply` | The remainder has the actual unit-period Fourier integrals of the continuous polynomial field, assembled in L2. |
| Distributional interpretation | `weakRiccatiDistribution_derivative`, `sourceLemmaH1_distribution`, `sourceH1RemainderDistribution_coefficient` | Faithful period-one tempered-distribution synthesis; the leading derivative is the actual distributional derivative and the remainder keeps its physical coefficients. |
| Low-order endpoints | `weakSobolevRiccatiDensity_zero_apply`, `weakSobolevRiccatiDensity_one_apply` | u2=-b' for H0 inputs; u3=-b''+a*b^2 for H1 inputs, using actual convolutions. |

The displayed kth derivative is weak at the printed H^(k-1) regularity.
The construction covers all k>=1; for k=1 the remainder polynomial is
zero, so its negative derivative-count bound is meaningful. No real-type,
smallness, or extra smoothness restriction is imposed. The polynomial is
canonical and independent of the input. The distributional realization
preserves the original period-one normalization, including negative modes.

H.2's full H^m statement is covered below. The G.2 local-norm, required p>2
spectral-height, and optional original m=1 obligations retain their status.
The source inventory and declaration count do not certify completeness.


### Corollary H.2: one polynomial and the physical integral on every real H^m source

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| One polynomial before all inputs | `sourceCorollaryH2` | For every m>=1, there exists a single polynomial giving the displayed integral for every real H^m source. |
| Jet order, homogeneity, field balance | `sourceH2Polynomial_properties` | Jets through m-1, total weight 2m+2, field charge zero; all for the same canonical chosen polynomial. |
| Highest physical derivative | `memLp_sobolevTopJetPhysical`, `periodOneCoefficient_sobolevTopJetPhysical` | Actual derivative of the penultimate H1 representative; square integrability and exact period-one coefficients on every H^m source. |
| Actual weak-derivative hierarchy | `hierarchySobolevJetL2_distribution_succ`, `hierarchySobolevJetL2_distribution_iterate` | Every available jet equals successive Mathlib tempered-distribution derivatives of the zeroth jet. |
| Exact physical square integral | `integral_sq_sobolevTopJetPhysical` | Unit-interval Parseval, including nonsmooth data, with no lost normalization factor. |
| Single real integral | `sourceCorollaryH2_integral` | Squared physical top derivative plus the continuous lower-jet polynomial, integrated over the original unit period. |
| Complex extension | `sobolevOddHamiltonian_eq_physical_integral` | Bilinear physical top-derivative integral plus the same polynomial, for every complex H^m pair. |
| Original smooth meaning | `sobolevTopJetPhysical_eq_classical`, `sobolevOddHamiltonian_unique_continuous` | Pointwise classical derivative agreement on smooth inputs; unique continuous Hamiltonian extension on complex H^m. |

The polynomial and Hamiltonian are the existing physical constructions;
no replacement by an action sum or an input-dependent polynomial occurs.
The lower jets of real inputs are pointwise conjugates by the existing
`hierarchySobolevJetContinuous_real` theorem. There is no source correction
for H.2. Appendix I's Schur-complement hypotheses are the next audit.
The G.2 local-norm, required p>2 spectral-height, and optional original
m=1 obligations remain open. Counts are not completeness certificates.


### Appendix I.1-I.2: the missing hypothesis and the original operator

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Identity terms and signs | `sourceSchur_apply`, `one_add_block` | S=Id+A-B*(Id+D)^(-1)*C; the identity shifts both diagonal blocks. |
| Corrected I.1 equivalence | `sourceLemmaI1_corrected` | Arbitrary complex Banach blocks, assuming Id+D has a bounded inverse; no finite-dimensional restriction. |
| Valid printed direction | `sourceLemmaI1_sufficient` | Invertibility of Id+D and S implies invertibility of Id+T. |
| Printed forward implication | `sourceLemmaI1_printed_false` | Refuted on C times C: Id+T is coordinate exchange while Id+D is zero. |
| I.2's lower inverse | `source_lower_isUnit_of_norm_lt_one` | The exact strict norm bound gives a bounded inverse by Neumann series. |
| I.2 determinant condition | `sourceCorollaryI2`, `sourceCorollaryI2_iff` | Finite-dimensional first block, arbitrary Banach second block; the printed sufficient condition and the equivalence under its norm bound. |
| Original Banach space | `source_operator_isUnit_iff`, `sourceLemmaI1_on_decomposition`, `sourceCorollaryI2_on_decomposition` | Any bounded direct-sum coordinate equivalence realizing T; conclusions concern Id+T on Z itself. |
| Strict-bound check | `sourceCorollaryI2_boundary_counterexample` | At norm(D)=1 a nonzero Schur determinant alone is insufficient; no refutation of the printed strict version. |

I.1's unrestricted statement is refuted, not proved by silently adding an
assumption. Its corrected form and the unchanged I.2 criterion are proved.
The polynomial and physical H.2 results above remain unchanged. Next is
I.3's full total-boundedness characterization, followed by I.4. The G.2
local-norm, required p>2 spectral-height, and optional original m=1
obligations remain open. Counts do not certify completeness.


### Lemma I.3: arbitrary sets, finite exponents, and weighted norms

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Full equivalence | `Coeff.sourceLemmaI3` | Every subset of l^p for 1<=p<infinity; pointwise coefficient bounds and one uniform N>=1 for each epsilon>0. |
| No hidden norm-bound hypothesis | `isBounded_of_pointwise_tail`, `totallyBounded_iff_pointwise_uniform_finite_tails` | The global norm bound is derived from the printed assumptions before applying finite-rank compactness. |
| Necessity uniformly over sets | `tendstoUniformlyOn_norm_tail_of_isCompact` | Decreasing continuous tail norms converge uniformly on compact sets by Dini; applies to the compact closure of any totally bounded set. |
| Exact symmetric cutoffs | `sourceI3Tail_apply`, `sourceI3Tail_eq_fourierTail` | Retains |n|<=N; complement equals the existing `fourierTail (N+1)`. Both signed boundary frequencies are tested. |
| Compactness and relative compactness | `Coeff.sourceLemmaI3_compact`, `Coeff.sourceLemmaI3_compactClosure` | Add closedness for compactness; the same printed criterion characterizes compact closure. |
| Original weighted source | `WeightedCoeff.sourceLemmaI3`, `WeightedCoeff.sourceLemmaI3_compact` | Every positive weight and every finite exponent; raw pointwise bounds and exact weighted tail norm, including all real Sobolev orders. |
| Full compact-operator output | `exists_sourceI3Tail_comp_norm_le`, `tendsto_sourceI3Tail_comp` | Arbitrary complex normed input space; entire output tails vanish in operator norm for compact operators, uniformly for all larger cutoffs. |
| Endpoint and hypothesis checks | `AppendixI3FullSetChecks` public examples | p=1, signed boundaries, weighted p=3, escaping unit vectors, and the compact constant-one singleton in l-infinity. |

The printed I.3 is proved unchanged. The operator consequence supplies the
initial tail estimate for I.4; it does not claim I.4's full real-analytic
or generic local-diffeomorphism conclusion. The relative-cone argument and Schur signs are covered below. G.2's local-norm, required p>2 spectral-height, and
optional original m=1 obligations remain open. Counts do not certify
completeness.


### Proposition I.4: relative-cone density and the Schur signs

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Boundary uniqueness | `eventuallyEq_of_nonnegative_agreement`, `eventuallyEq_of_nonnegative_restriction` | All finite Banach exponents; relative agreement on nonnegative sequences determines an ambient holomorphic germ, including at zero. |
| Relative density | `subset_closure_of_nonnegative_local_analytic_nonvanishing` | Local scalar criteria on the cone subtype; preconnected source domain, with no ambient-interior assumption. |
| Local compact Fredholm families | `open_dense_isUnit_of_nonnegative_analytic_compact_shift` | Local operator-valued extensions; compactness only at original cone parameters; one invertible point gives a relatively open dense invertible locus. |
| Intrinsic complexified derivative | `NonnegativeAnalyticAtlas.derivative_eq`, `derivative_hasLocalAnalyticExtensions` | Derivative independence and local analytic dependence follow from cone uniqueness and original-map agreement. |
| Actual local-inverse seed | `isUnit_fderiv_iff_localInverse`, `open_dense_localInversePoints_of_nonnegative_atlas` | One actual two-sided analytic local inverse implies a relatively open dense set of such points. |
| Original cone-map recovery | `open_dense_localInverse_of_nonnegative_atlas` | Both ambient extension inverse identities, inverse derivative, and the original map's left-inverse identity as a relative germ. |
| Atlas-independent locus | `NonnegativeAnalyticAtlas.localInversePoints_eq_of_atlas` | Changing local analytic extensions does not change which source points have local inverses. |
| Printed Schur signs | `sourceI4_printedSchur_false_positive`, `sourceI4_correctSchur_zero` | Finite-dimensional false positive for the displayed determinant; the corrected signs detect singularity. This does not refute I.4's conclusion. |

The source of these new theorems is the nonnegative cone in unweighted
l^p for every 1<=p<infinity. The openness and closure statements use its
relative topology, so the zero boundary and arbitrary zero coordinates
are included. The conclusion concerns inverses of local complex analytic
extensions, and agreement with the original cone map is proved. Only local
extensions are required; they need not be chosen as one global map.

Weighted complex and real transport are proved below. The bridge from
local real-analytic germs to the extension-atlas hypothesis remains pending. Accordingly I.4 is partial, not marked fully proved. The G.2 local-norm, required p>2 spectral-height,
and optional original m=1 obligations retain their status. Source-label
inventories and declaration counts do not certify completeness.


### Proposition I.4: original weighted spaces at every real order

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original positive cone | `WeightedCoeff.mem_nonnegativeLocus_iff`, `nonnegativeHomeomorph` | Positivity of raw coefficients is equivalent to positivity after weighting; the full cone, including zero, is identified homeomorphically. |
| Local extension transport | `localAnalyticExtensions_transport`, `WeightedCoeff.HasLocalAnalyticExtensions.toCoeff` | Local germs are transported by compatible continuous parameter maps and ambient complex linear coordinates; no global extension assumption. |
| Weighted Fredholm density | `WeightedCoeff.open_dense_isUnit_of_nonnegative_analytic_compact_shift` | Every positive weight and finite Banach exponent; compactness only at original parameters, on the original operator space. |
| Intrinsic weighted derivative | `WeightedCoeff.NonnegativeAnalyticAtlas.derivative_eq`, `derivative_hasLocalAnalyticExtensions` | Original weighted derivatives are independent of local extension choices and locally analytic as operators. |
| One actual inverse as seed | `WeightedCoeff.open_dense_localInversePoints_of_nonnegative_atlas` | A relatively open dense local-inverse locus from one two-sided local inverse and compact derivative minus identity. |
| Original-space inverse identities | `WeightedCoeff.open_dense_localInverse_of_nonnegative_atlas` | The inverse maps the weighted space to itself; both extension identities, original cone-map recovery, and inverse derivative are proved. |
| Arbitrary real Sobolev order | `AppendixI4WeightedChecks` public examples | Instantiation at `Weight.sobolev s` for every real s, p=1 at zero, and arbitrary finite exponent; no nonnegative-order restriction. |
| Nonconstant boundary check | `AppendixI4WeightedChecks.rawCoordinateFamily` | The raw-coordinate scalar operator family is singular at zero and has an open dense invertible locus for every positive weight. |

All weighted statements use raw coefficients and the existing weighted norm.
No comparison constants, boundedness assumption on the weight, or compactness
hypothesis off the nonnegative cone have been added. The local inverses are
currently complex ambient inverses of the original weighted extensions.
Restriction to real sequence spaces is proved below for both unweighted
and weighted spaces. The real-analytic-to-complex-atlas representation
bridge is the next obligation. I.4 is not yet marked fully proved.
The previously recorded G.2, p>2 spectral-height, and optional original m=1
obligations remain open; counts do not certify completeness.


### Proposition I.4: actual real inverses and a real seed, unweighted

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Reality from original cone values | `eventually_realLocus_of_nonnegative_analytic`, `NonnegativeAnalyticAtlas.extension_eventually_real` | Local complex extensions preserve the full nearby real locus, derived from real values on the original cone, including at zero. The reality lemma also covers the infinite exponent. |
| Real derivative and inverse | `fderiv_entries_real_of_eventually_real`, `inverse_mapsTo_realLocus_of_real_entries` | Real matrix entries and preservation of the real locus by the inverse derivative; the latter uses finite p. |
| Preservation by nonlinear inverse | `eventually_mem_closedSubmodule_of_localInverse`, `exists_real_localInverse_of_nonnegative_atlas` | The actual complex inverse preserves nearby real targets; no extra inverse-reality assumption. |
| Actual real sequence maps | `realRestriction_localInverse`, `exists_realRestriction_localInverse_of_nonnegative_atlas` | Real analytic maps between `RealCoeff p` spaces, both inverse identities, center identity, and recovery of the original cone map. |
| Real inverse seed | `isUnit_fderiv_of_real_localLeftInverse`, `NonnegativeAnalyticAtlas.realLocalInversePoints_eq` | A differentiable real left inverse plus compact derivative minus identity yields an invertible complex derivative. The real and complex local-inverse loci coincide. |
| Real open dense conclusion | `sourcePropositionI4_real_unweighted`, `sourcePropositionI4_real_of_differentiable_seed` | Relatively open dense real analytic inverse locus on a relatively open preconnected cone domain at every finite Banach exponent. |
| Nonlinear boundary example | `AppendixI4RealChecks` | A quadratic coordinate perturbation at p=1 has an actual real analytic inverse at zero with both identities; generic examples check the real analytic and merely differentiable seed APIs. |

These results use local complex extension atlases to represent analyticity
at the cone boundary. The reality required to restrict those extensions and
their inverses is proved from the original cone values. A general construction
of such an atlas from a separate real-analytic predicate is not asserted.
The real conclusion, real inverse locus, and real seed are now transported
to all positive weights below. The real-analytic-to-complex-atlas bridge is
still pending; I.4 as a whole is not yet marked fully proved. The G.2 local-norm, required
p>2 spectral-height, and optional original m=1 obligations remain unchanged.


### Proposition I.4: real inverses in every positive weighted space

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Original weighted real Banach space | `WeightedRealCoeff`, `WeightedRealCoeff.im_eq_zero`, `WeightedCoeff.mem_realSubmodule_iff` | Closed subspace with real raw coefficients and the original inherited weighted norm; complete at every Banach exponent. |
| Compatible real coordinates | `coordinateRealEquiv`, `val_coordinateReCLM`, `realRestriction_linear_conjugate` | Real inclusion and projection, recovery of real original values, and compatibility of real restriction with complex weighting. |
| Original compactness | `WeightedCoeff.NonnegativeAnalyticAtlas.toCoeff_derivative`, `toCoeff_compact` | Derivative conjugacy and compactness of derivative minus identity in normalized coordinates, from the original cone hypotheses only. |
| Actual real inverse locus | `WeightedCoeff.NonnegativeAnalyticAtlas.realLocalInversePoints_eq`, `realLocalInversePoints_eq_of_atlas` | Real and complex inverse loci coincide; the real locus is intrinsic to the original cone map. |
| Real weighted density | `WeightedCoeff.sourcePropositionI4_real_weighted` | One actual real local inverse implies a relatively open dense real inverse locus for all positive weights and finite Banach exponents. |
| Differentiable real starting inverse | `WeightedCoeff.sourcePropositionI4_real_weighted_of_differentiable_seed` | The initial real map need only be differentiable and a left inverse; the resulting inverse points have analytic two-sided real inverses. |
| Both real identities and original recovery | `WeightedCoeff.NonnegativeAnalyticAtlas.exists_real_localInverse` | Actual maps `WeightedRealCoeff w p -> WeightedRealCoeff w p`, with analyticity, center identity, both local inverse identities, and recovery of the original cone map. |
| Nonlinear check in arbitrary weights | `AppendixI4WeightedRealChecks` | A quadratic raw-coordinate perturbation has compact derivative minus identity, an inverse at the zero boundary, and an open dense real inverse locus for every positive weight. Both inverse identities are checked. |

The weight is only required to be strictly positive. All real Sobolev orders
are included, and no global upper or lower bound on the weight is assumed.
Only local complex extension atlases are used; compactness is assumed at
original cone points. The real transport obligation is now complete.
Constructing those atlases from local real-analytic germs remains pending,
so the unrestricted source formulation is not marked complete. The separate
G.2 local-norm, required p>2 spectral-height, and optional original m=1
obligations retain their status. Counts do not certify completeness.
