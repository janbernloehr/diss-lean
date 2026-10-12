# Dissertation coverage audit

This is a focused map of the dissertation's introductory results to the
current public Lean API. It is not a completeness certificate for every
chapter or appendix. All paths below are relative to the repository root;
the introductory declarations are in `NLS.ZakharovShabat`.
The appendix audits below use `NLS.Fourier` and `NLS.ComplexAnalysis`.
Later milestone entries retain their historical validation counts and
then-current limitations. The current Appendix G comparison is in
[`coverage/APPENDIX_G.md`](coverage/APPENDIX_G.md), and Appendix H is in
[`coverage/APPENDIX_H.md`](coverage/APPENDIX_H.md). The focused Section 2 convergence and scalar-pairing audit is in
[`coverage/SECTION_2.md`](coverage/SECTION_2.md). The spectral overview link below and the final
dyadic-counterexample entry record the current status of Theorem 1.1.

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
detailed comparison. Theorem 1.1's unchanged printed source-norm height
and counting conclusions are proved for 1<=p<=4. Its all-exponent claim
is now refuted by actual balanced dyadic sources for every integer
P>=100000000, in the original source norm. Theorem 1.2 and Corollary 1.3 are proved for every finite
p>1, with the actual ordered endpoints, their multiplicities, and the
full locally uniform source bounds. Corollary 1.6's density of actual real
finite-gap sources is also verified. Theorem 1.5 is covered for every
finite p>1; Theorem 1.4 is covered at p=2, but its all-p original-norm
printed height is refuted by an actual Dirichlet spectral counterexample
at p=1024 (and every natural exponent at least 1024). No replacement
height is adopted.

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
G.2's arbitrary-time local norm, the remaining p>4 spectral height, and the
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
These findings do not change the unresolved G.2 local-norm and remaining
p>4 spectral-height obligations or the optional original m=1 sharpening.


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
recorded G.2 local-norm, remaining p>4 spectral-height, and optional original
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
The previously recorded G.2 local-norm, remaining p>4 spectral-height, and
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
integration-by-parts formulation is the next audit. The G.2 local-norm, remaining p>4 spectral-height,
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
The G.2 local-norm, remaining p>4 spectral-height, and optional original
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
local-norm, remaining p>4 spectral-height, and optional original m=1
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
or generic local-diffeomorphism conclusion. The relative-cone argument and Schur signs are covered below. G.2's local-norm, remaining p>4 spectral-height, and
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

Weighted complex and real transport, and the construction of the complex
atlas from real-analytic germs, are proved in the later entries below.
The G.2 local-norm, remaining p>4 spectral-height,
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
bridge is proved in the final I.4 entry below.
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
their inverses is proved from the original cone values. The subsequent
entries transport the real conclusion, inverse locus, and seed to all
positive weights and construct the atlas from actual real-analytic germs.
The G.2 local-norm, remaining
p>4 spectral-height, and optional original m=1 obligations remain unchanged.


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
The following entry constructs those atlases from real-analytic germs and
closes this final representation obligation. The separate
G.2 local-norm, remaining p>4 spectral-height, and optional original m=1
obligations retain their status. Counts do not certify completeness.


### Proposition I.4: real-analytic germs and the original real derivative

| Source requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Complexify real coefficients | `Complexification.complexifyLinear`, `complexifyMultilinear`, `norm_complexifyMultilinear_apply_le`, `complexifyMultilinear_real` | Continuous complex multilinear extensions, agreement on real arguments, degree-n norm bound 2^n. |
| Extend real-analytic germs | `half_radius_le_complexifySeries`, `exists_complex_extension_of_analyticAt`, `exists_complex_extension_in_coordinates` | At least half the original radius; full real-neighborhood agreement at arbitrary real centers, also at p=infinity. |
| Identify the actual derivative | `complexifyRealMap_real`, `fderiv_eq_complexifyRealMap`, `realGermComplexExtension_fderiv` | Complex derivative equals complexification of the original real derivative. This is proved, not assumed. |
| Original real analyticity | `WeightedCoeff.NonnegativeRealAnalyticAtlas`, `toComplex`, `toComplex_restriction`, `toComplex_derivative` | Real analytic neighborhood extensions of the cone map yield the needed complex atlas and preserve full real germs. |
| Preserve the original inverse locus | `HasAnalyticInverse.congr`, `toComplex_realLocalInversePoints`, `complexifiedDerivative_eq`, `localInversePoints_eq_of_atlas` | The conclusion concerns the original real extensions, and the derivative and inverse locus are intrinsic. |
| Proposition I.4 | `WeightedCoeff.sourcePropositionI4_real_analytic` | Relatively open dense real inverse locus from one real local inverse, for all positive weights and finite Banach exponents; compactness only at cone points. |
| Original differentiable seed | `sourcePropositionI4_real_analytic_of_differentiable_seed` | A differentiable real left inverse suffices; analytic two-sided inverses result on the generic locus. |
| Both identities and source recovery | `NonnegativeRealAnalyticAtlas.exists_localInverse` | Actual real maps, both inverse identities on real neighborhoods, and recovery of the original cone map. |
| Nonlinear real-input checks | `AppendixI4RealAnalyticChecks` | A directly defined real quadratic map has compact complexified derivative minus identity, a real inverse at zero with both identities, and an open dense inverse locus for arbitrary positive weights. |

This completes I.4 with real-neighborhood extensions as the meaning of
real analyticity and local diffeomorphism at cone boundary points. No
ambient-interior, global complex-extension, or off-cone compactness
hypothesis is introduced. The source's path-connected domain is covered
by the weaker preconnected-domain hypothesis. All real Sobolev orders are
included. The density theorem keeps 1<=p<infinity; the separate extension
construction also permits p=infinity. The printed Schur sign error remains
recorded in `SOURCE_ERRATA.md`.

G.2's arbitrary-time local norm and the remaining p>4 spectral height remain
open; the original unrestricted m=1 sharpening remains optional and
unresolved. The dissertation is incomplete, and statement counts do not
certify completeness.


### Lemma G.2: arbitrary-length integral-norm bound and necessary scaling

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Length-dependent trace bound | `endpoint_variation_le_sample_interval`, `endpoint_variation_le_integrals_interval`, `endpoint_variation_le_length_H1` | Every T>0 and t in [0,T]; combined endpoints and variation bounded by 2*sqrt(1/T+T) times the integral H1 norm. |
| Actual all-time Born bound | `intervalHermitianFirstBornOperator_weighted_le_interval_H1`, `intervalHermitianFirstBornOperator_weighted_le_local_H1` | Original Hermitian operator, arbitrary nonzero complex frequency, all finite nonnegative times; local version uses T=t and handles zero separately. |
| Exact constant family | `g2IntegralNormTestPotential_norm_length`, `oscillatoryIntegral_const_half_phase`, `g2IntegralNormTestPotential_firstBorn_length` | Smooth period-one (1,0), every t>0, frequency pi/(2t), norm sqrt(t), actual Born norm 2t/pi. |
| Necessary length dependence | `lemmaG2_integralNorm_length_necessary`, `lemmaG2_integralNorm_no_uniform_numerator` | Any bound B(t)/(2|z|) in the integral norm requires B(t)>=2/sqrt(t); no fixed numerator suffices. |
| Sharp leading short-time coefficient | `intervalH1_length_factor_normalized`, `tendsto_intervalH1_length_factor_normalized` | Ratio of the sufficient numerator to the necessary lower bound equals sqrt(1+t^2) and tends to one from the right at zero. |
| Public checks | `AppendixG2LengthChecks` | Full interval theorem, arbitrary-length constant inputs, affine input on [0,4], zero time, exact values, the impossibility theorem, normalized limit, and the unit-length coefficient comparison. |

The integral H1 norm is exactly the previously defined integral energy,
with no length normalization. This entry supplies an explicit correction
candidate, not a proof of the printed coefficient under an unspecified
norm convention. The printed arbitrary-time G.2 interpretation remains
unresolved. The exact periodic-norm unit-interval theorem remains valid;
the remaining p>4 spectral height and optional original m=1 sharpening also
retain their status. None of these counts or examples certify completion
of the dissertation.


### Theorem 1.1 / Proposition 3.1: unchanged printed height through p=4

| Requirement | Public theorem(s) | Verified scope |
| --- | --- | --- |
| Preserve the conjugate root | `norm_punctured_reciprocal_le_of_power_bound`, `norm_reciprocal_le_conjugate_root` | All finite conjugate pairs; retain the reciprocal-envelope coefficient 2*(2/(q-1))^(1/q). |
| Constant-eight free bound | `reciprocal_power_coefficient_le_four`, `freeL1Bound_le_height_eight` | Every 1<=p<=4, with the central inverse-height term retained. |
| Printed height and its edges | `mem_resolventSet_of_printed_height_up_to_four`, `abs_im_lt_printed_height_up_to_four` | Arbitrary complex potentials and norm balls; unchanged (1+8M)^p, both horizontal edges, strict spectral exclusion outside. |
| Exact source norm | `sourceSpectrum_abs_im_lt_printed_height_up_to_four` | Original period-one source with its component-sum norm, including p=4. |
| Full common-neighborhood counting | `exists_source_periodicCounting_printed_height_of_resolvent`, `exists_source_periodicCounting_printed_height_up_to_four` | One open convex neighborhood and every sufficiently large cutoff; central count 4N+2, disk counts two, parity, exhaustion, and analytic actual projections. |
| Distinguish criterion failure from spectral failure | `PrintedHeightFourChecks` | At p=3 and norm bound one the coarse test exceeds one, while the actual resolvent exists at 729i; p=4 checks include the negative edge and source central count. |
| Remaining limitation | `reciprocal_power_coefficient_four_fails_at_five` | Constant-four power-sum test fails at p=5; no spectral counterexample or all-exponent completion follows. |

This extends the required result beyond two without changing the printed
height or source norm. The full finite-exponent statement remains unresolved
above four. The all-exponent alternative height is not substituted for it.
The detailed source-scope audit is in `coverage/SPECTRAL_OVERVIEW.md`.
G.2's interval-norm interpretation and the optional original m=1 sharpening
retain their status. The dissertation remains incomplete.


### Theorem 1.2 and Corollary 1.3: full source periodic asymptotics

| Source requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Literal full eigenvalue displacement series | `sourcePeriodicEndpointEnergy_sum`, `sourceTheorem1_2` | Summability and one positive full-series bound on an open convex source neighborhood, every finite p>1. |
| Ordered actual eigenvalues with multiplicities | `sourceTheorem1_2_ordered_labels`, `PeriodicEndpointLabeling.exhaustive`, `CentralPeriodicLabeling.count_eq` | Both global lexicographic inequalities, all central repetitions, distant disk multiplicities, and exact original spectrum. |
| Choice-independent labels | `PeriodicEndpointLabeling.eq_canonicalPeriodicEndpoints` | Any admissible cutoff and complete ordered enumeration give the same endpoints. |
| Literal midpoint and gap membership | `sourceCorollary1_3_mem` and the displacement evaluation identities | Actual midpoint minus n*pi and unsquared gap in lp, without a smaller exponent range. |
| Joint local uniformity | `sourceCorollary1_3` | One source neighborhood and positive norm bound for both sequences; arbitrarily small tails at all larger cutoffs. |
| Public scope checks | `SourcePeriodicOverviewChecks` | General finite p, p=5, original multiplicities, literal series and sequences, coincident free roots. |

Both printed statements on p. 19 are covered unchanged. The neighborhoods
use the original finite-p source norm. No global constant over all
potentials or continuity of the sorted individual endpoints is claimed.
The construction does not depend on the unresolved printed height above
four. See `coverage/SPECTRAL_OVERVIEW.md` for the requirement-by-requirement
audit. The boundary-spectrum overview comparison is recorded below.
G.2's interval norm and the remaining height ranges are still open; the
dissertation is incomplete.


### Corollary 1.6: actual real finite-gap density

The source statement on p. 21 is covered by the existing
`exists_mem_sourceFiniteGapLocus_norm_sub_lt` and
`dense_sourceFiniteGapLocus` for every finite p>1. The underlying locus
uses finitely many nonzero actual canonical periodic gaps in the real
source space. Real spectral closing approximants converge in the original
finite-p pair norm, and the singleton-strip criterion proves their actual
finite-gap property. Existing public checks cover p=3 approximants and
density at p=2 and p=3/2. The detailed audit is recorded in
`coverage/SPECTRAL_OVERVIEW.md`. The unrestricted complex regularity
sentence is refuted below. Real-type spatial real analyticity is now
proved separately in `SourceFiniteGapAnalyticRealization.lean`, as recorded
in the latest entry below.


### Theorems 1.4 and 1.5: Hilbert box, all-p asymptotics, and a height counterexample

| Source requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Actual ordinary boundary spectra | `periodOneBoundaryPotential`, `BoundaryCondition.spectrum`, `sourceBoundarySpectrum_closed_discrete` | Same reflected source potential, two boundary restrictions, closed and discrete for every finite p>1. |
| One common neighborhood and cutoff | `exists_uniform_sourceBoundaryLabels` | Both canonical sequences and every larger cutoff, original source topology, full multiplicities and displacement norm bounds. |
| Reality of every eigenvalue | `sourceBoundarySpectrum_im_eq_zero` | Every real-type source, either condition, all central and distant points. |
| Exact printed height at p=2 | `norm_periodOneBoundaryPotential_two_le`, `sourceBoundarySpectrum_abs_im_lt_printed_height_two` | Original source norm and constant eight; spectrum strictly inside both horizontal edges. |
| Printed-box counts and exhaustion at p=2 | `sourceTheorem1_4_two` | Central count 2N+1, one simple root per high disk for either condition, no other roots, one neighborhood and all larger cutoffs. |
| Full Theorem 1.5 | `sourceTheorem1_5_mem`, `sourceTheorem1_5` | Both literal lp sequences and a common full-series bound for every finite p>1 and every complex source. |
| Canonical ordering and multiplicities | `monotone_canonicalPeriodOneBoundaryRoots`, `canonicalPeriodOneBoundaryRoots_multiplicity` | Global lexicographic order and all actual repetitions, independent of initial labels. |

Theorem 1.5 is covered unchanged. Every clause of Theorem 1.4 is covered
at p=2, but its all-p printed height is now refuted. The finite potential
`triangularNormalizedCoefficients P`, for every natural P>=1024, has source
norm at most 3/32 and an actual Dirichlet eigenvalue at i*2^P. The eigenvalue
escapes the printed box and every stated disk at every cutoff.
`sourceBoundaryPrintedHeight_counterexample` proves that assertion;
`not_sourceTheorem1_4_printed_exhaustion` negates the all-source exhaustion
statement at p=1024. No substitute spectrum, extended norm, or failed
sufficient estimate is used. See `SOURCE_ERRATA.md` and
`coverage/SPECTRAL_OVERVIEW.md`. No replacement height is adopted.
Theorem 1.1's periodic height above four remains unresolved, and the
dissertation remains incomplete.

Validation: the full project check passed (6592 build jobs), including all
public examples and the axiom audit of 27502 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Proposed boundary-height correction and necessary exponent dependence

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Retain the interval-extension loss | `norm_periodOneBoundaryPotential_le` | Reflected maximum pair norm bounded by E_p times the original source norm, all finite p>1. |
| Explicit sufficient source height | `mem_boundaryResolventSet_of_sourceBoundaryExplicitHeight`, `sourceBoundarySpectrum_abs_im_lt_explicit_height` | `(1+8*p*E_p*M)^p` on every original source norm ball; both ordinary boundary conditions, including the horizontal edges. |
| Corrected counts and exhaustion | `sourceTheorem1_4_proposed_height` | One open convex neighborhood containing the source and zero; every larger cutoff; original central count 2N+1, simple high roots and no other roots. |
| Necessary growth of any height coefficient | `sourceBoundaryCountingHeightCoefficient_necessary` | C_P>=P/96 for integer P>1, even with source-dependent cutoffs. |
| No fixed replacement for eight | `not_exists_uniform_sourceBoundaryCountingHeightCoefficient` | Negates all-source exhaustion for all integer exponents for every fixed nonnegative coefficient. |

The new sufficient height is recorded as a proved proposed correction,
not an adopted replacement for Theorem 1.4. The printed p=2 theorem and
all-p Theorem 1.5 remain unchanged. The periodic height above four is a
separate unresolved obligation. No optimality or whole-source completion
is certified.

Validation: the full project check passed (6594 build jobs), including all
public examples and the axiom audit of 27521 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Unnumbered finite-gap regularity: unrestricted complex reading refuted

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Actual triangular periodic inverse | `triangularResolvent_spectralPencil`, `spectralPencil_triangularResolvent` | Original one-derivative domain; any triangular coefficient potential; every finite Banach exponent; no smallness. |
| Full free spectrum | `periodicSpectrum_triangular`, `sourcePeriodicSpectrum_triangular` | Equality with the whole free lattice, including the original period-one source embedding. |
| Literal finite-gap property | `finite_canonicalPeriodicGap_triangular`, `roughTriangularSource_finite_gap` | Finite set of nonzero actual canonical indexed gaps for every finite p>1. |
| A rough source in the original space | `roughTriangularSource` | First coefficients 1/(1+|n|), second component zero; belongs to every finite lp with p>1. |
| Failure of smooth and analytic realizations | `roughTriangularCoefficients_no_smooth_representative`, `roughTriangularCoefficients_no_analytic_representative` | No periodic physical representative with the same Fourier coefficients has the claimed regularity. |
| Scope separation | `roughTriangularSource_not_realType`, `not_every_complex_finiteGap_source_smooth` | Refutes the unrestricted complex reading; preserves the existing real-type regularity and density results. |

The statement audited is the unnumbered sentence on printed p. 21, not
Corollary 1.6's real-type density theorem. Real-type spatial real
analyticity is now proved in the later analytic-realization entry. The
complex counterexample uses no proposed
replacement definition of finite gaps or of the periodic spectrum.
The dissertation remains incomplete.

Validation: the full project check passed (6596 build jobs), including all
public examples and the axiom audit of 27550 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Spatial translation: prerequisite for real-type finite-gap analyticity

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Translation in the original norms | `Coeff.spatialTranslation`, `WeightedCoeff.spatialTranslation`, `sourceSpatialTranslation`, `continuous_sourceSpatialTranslation` | Isometric equivalences, source group law, and joint continuity at every finite exponent. |
| Actual domain-to-base operator conjugacy | `domainInclusion_spatialTranslation`, `potentialMul_spatialTranslation`, `spectralPencil_spatialTranslation` | Original one-derivative domain and convolution, including p=1. |
| Full intrinsic spectral data | `mem_periodicRootSpace_spatialTranslation`, `periodicRootSpaceTopTranslationEquiv`, `periodicAlgebraicMultiplicity_spatialTranslation`, `periodicSpectrum_spatialTranslation` | All chain lengths, actual multiplicities, and the entire periodic spectral set. |
| Source normalization and indexing | `periodOnePotential_spatialTranslation`, `sourceCanonicalPeriodicEndpoints_spatialTranslation`, `sourceCanonicalPeriodicGap_spatialTranslation` | Original period-one coefficients and both complete canonical endpoint sequences; every finite p>1, with no index shift. |
| Real finite-gap translation orbit | `sourceSpatialTranslation_realType`, `sourceSpatialTranslation_closedGapTail`, `sourceSpatialTranslation_mem_sourceFiniteGapLocus` | Real type and exactly the same closed-gap cutoff survive every real displacement. |
| Physical spatial sign and scale | `Fourier.continuousSynthesis_spatialTranslation`, `Fourier.periodOneSynthesis_spatialTranslation`, `Fourier.periodOneCoefficient_translated_synthesis` | The action is f(x+t), in both periods, for arbitrary absolutely summable coefficients. |

The translation lemmas supply the fixed-gap-tail curve used in the
analytic-realization proof below. They do not assume or conclude
exponential coefficient decay. The complex counterexample and the other
unresolved source obligations are unchanged.

Validation: the full project check passed (6601 build jobs), including all
public examples and the axiom audit of 27610 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.


### Unnumbered finite-gap regularity: real-type spatial analyticity proved

| Requirement | Public evidence | Verified scope |
| --- | --- | --- |
| Finite-dimensional analytic reconstruction | `exists_analyticAt_sourceFiniteGap_finiteReconstruction` | Local weighted lift factors through finitely many original Fourier coefficients; previous weighted-lift APIs retained. |
| Analytic target without analytic source assumption | `analyticAt_sourceTranslationFiniteTarget`, `sourceTranslationFiniteTarget_ofReal` | Entire complex-time finite target equals the exact weighted block of the real spatial translation. |
| Weighted lift of the same translated source | `exists_analyticAt_sourceFiniteGap_translationLift` | Analytic near time zero; decoding equals the actual original translation, using the unchanged canonical gap tail. |
| Bounded physical evaluation | `sourceOneDerivativeWeight_double`, `normalizedSobolevSourceL1`, `normalizedSobolevSourceEvaluation` | Exactly the original one-derivative weight after embedding; bounded l1 decoding and physical evaluation at every finite p. |
| Analyticity of the existing representative | `analyticOnNhd_sourceFiniteGapPhysicalPair` | Both original coefficient-preserving physical functions are real analytic on all of R, for every real-type finite-gap source at finite p>1. |
| Full qualified source assertion | `sourceFiniteGap_exists_analytic_representative` | Real analyticity, period one, and every original Fourier integral, without finite Fourier support or an extra regularity assumption. |

This completes the real-type reading of the regularity sentence on
printed p. 21. Its unrestricted complex reading remains refuted, while
Corollary 1.6's real-type density theorem remains proved. No claim about
p=infinity or a uniform analytic strip width is made. The unresolved
periodic-height range above four and G.2 norm interpretation remain;
the dissertation is incomplete.

Validation: the full project check passed (6605 build jobs), including all
public examples and the axiom audit of 27645 NLS declarations. There are
21 existing warnings and no new warnings. The source inventory check
passed with 156 labels. Counts do not certify completeness.

### Lemma 3.2(ii) / Theorem 1.1 proof route: exponent dependence is necessary

[`FreeResolventHeightNecessity.lean`](NLS/ZakharovShabat/FreeResolventHeightNecessity.lean)
proves bounds for the actual free operator, using finite Fourier inputs.

| Public entry point | Scope |
| --- | --- |
| `tsum_scalarResolventToL1_triangularNormalized` | Exact output coefficient sum -2 at z=-i2^P for every positive integer exponent P. |
| `freeResolventToL1_dyadic_norm_lower`, `freeResolventToL1_dyadic_norm_upper` | P/48 <= actual pair-resolvent norm <= 2P+2^(-P), from lP to l1. |
| `freeResolventHeightCoefficient_necessary` | Any height coefficient C_P in the standard decay form must obey P <= 24 C_P+48. |
| `not_exists_uniform_freeResolventHeightCoefficient` | No fixed coefficient works for all finite integer exponents and nonreal parameters. |
| `freeResolvent_eight_height_bound_fails` | Actual constant-eight norm estimate fails for every integer P>240; checked at P=256. |
| `negativeDyadicHeight_mem_free_resolvent` | Every test point belongs to the actual free periodic resolvent set at every finite exponent. |

This establishes the necessary linear order of the exponent coefficient
in Lemma 3.2(ii)'s type of bound. It does not refute Theorem 1.1: its
unchanged printed periodic height remains proved through p=4 and required
but unresolved above four. The original source norm is unchanged, and no
source correction is adopted. The next periodic argument must use more
than a free-resolvent norm estimate with a fixed coefficient.

### Squared resolvent: component product and a conditional all-p printed height

[`ComponentProductResolvent.lean`](NLS/ZakharovShabat/ComponentProductResolvent.lean)
retains both off-diagonal component norms in the actual operator square.

| Public entry point | Scope |
| --- | --- |
| `norm_potentialFreeResolvent_sq_le_component_product` | Actual square norm bounded by B(z)^2 times the component-norm product, at every finite Banach exponent. |
| `squaredNeumannCondition_of_component_product` | Supplies the existing squared inverse with both inverse identities. |
| `mem_resolventSet_of_componentMean_height` | Both horizontal edges and the entire exterior for height (1+8p sqrt(ab))^p, where a,b are the component norms. |
| `periodicSpectrum_abs_im_lt_componentMean_height` | Every actual periodic spectral point lies strictly within that strip. |
| `source_mem_resolventSet_of_printed_height_component_product` | Unchanged printed source height at every finite p, assuming p sqrt(ab) <= original source norm. |
| `source_componentMean_condition_of_imbalance` | The norm condition p^2 b <= a implies that coupling hypothesis. |
| `analyticOnNhd_resolvent_componentProductRegion` | Actual resolvent analytic on an explicit open potential region containing every triangular potential for fixed z off the free lattice. |

Public examples check arbitrary finite exponents and p=256 with both
components nonzero. One example proves invertibility at z=i while the
previous Neumann condition fails; another checks the literal printed
height under the imbalance condition. The source norm remains the p-th
root of the two component p-energies. The unrestricted printed height
above p=4 is still required and unresolved, and the geometric-mean
supplement is not adopted as a replacement source statement.

### Theorem 1.1: exact balanced-source reduction of the remaining height claim

[`PeriodicDiagonalSimilarity.lean`](NLS/ZakharovShabat/PeriodicDiagonalSimilarity.lean)
and [`SourceBalancedHeightReduction.lean`](NLS/ZakharovShabat/SourceBalancedHeightReduction.lean)
transport actual spectral data while controlling the original source norm.

| Public entry point | Scope |
| --- | --- |
| `spectralPencil_diagonalSimilarity` | Exact conjugation of z-L on the original one-derivative domain, for any nonzero complex scalar. |
| `periodicRootSpaceTopDiagonalEquiv` | Full generalized root-space equivalence; finite root-chain transport is also proved. |
| `periodicAlgebraicMultiplicity_diagonalPotential`, `periodicSpectrum_diagonalPotential` | Actual multiplicities and entire periodic spectral set unchanged. |
| `exists_source_balanced_diagonalPotential` | For two nonzero components, both new norms equal sqrt(ab), the new p-energy norm is exactly 2^(1/p) sqrt(ab), and it does not exceed the original norm. |
| `source_printedHeight_iff_balanced` | At each finite exponent, the unrestricted literal height is equivalent to its equal-component-norm case. |
| `source_printedHeight_counterexample_balances` | Any putative violation retains its spectral parameter under balancing, with no increase in the source norm; no violation is asserted to exist. |
| `exists_source_periodicCounting_printed_height_of_balanced` | An explicit balanced-height hypothesis gives full counts, exhaustion, and actual analytic rectangular projections on one common open convex neighborhood, for all sufficiently large cutoffs. |

Public examples include p=5, rescaling component norms (1,4) to (2,2) and
checking the actual spectra and multiplicities, as well as arbitrary-exponent
interfaces and the full conditional counting conclusion. Equal norms do
not imply the source's real-type conjugation condition. The unrestricted
height above p=4 remains required and unresolved; the reduction is not a
proof of its explicit balanced-case hypothesis. No source correction is
adopted.

### Theorem 1.1: exact ordered-coupling criterion and normalization

[`OrderedTriangularMonodromy.lean`](NLS/ZakharovShabat/OrderedTriangularMonodromy.lean)
and [`OrderedTriangularNormalization.lean`](NLS/ZakharovShabat/OrderedTriangularNormalization.lean)
connect separated physical couplings to actual coefficient-space spectral points.

| Public entry point | Scope |
| --- | --- |
| `classicalSolution_eq_orderedTriangular` | Exact continuous-potential solution when the upper coupling acts before the lower coupling. |
| `classicalMonodromy_orderedTriangular`, `classicalDiscriminant_orderedTriangular` | Actual monodromy and trace expressed through two integrating-factor integrals A and B. |
| `source_mem_periodicSpectrum_orderedTriangular_iff` | Both Floquet signs characterize the actual spectrum at every finite p>=2; the original Hilbert source and its physical representative must agree. |
| `source_mem_periodicSpectrum_orderedPeriodicNormalization` | Scaling the upper coupling by -(exp(-i z)-1)^2/(A B) places z in the actual spectrum, assuming A B is nonzero. |
| `norm_orderedPeriodicNormalization`, `norm_scaleUpperSource_rpow` | Exact normalization magnitude and original source p-energy cost. |
| `exists_balanced_source_orderedPeriodicNormalization` | At nonreal z with nonzero components, a balanced realization retains z and has norm exactly 2^(1/p) sqrt(abs(kappa) a b). |

Public examples check the free trace, antiperiodic sign, normalized actual
spectral membership at p=5, and the arbitrary-exponent norm identities.
No quantitative small-norm profile or periodic-height counterexample is
claimed. Theorem 1.1's unrestricted printed height above p=4 remains
required and unresolved. No source correction is adopted.

### Theorem 1.1: concrete tent sources and reflected Fourier cancellation

[`ContinuousPeriodOneRealization.lean`](NLS/Fourier/ContinuousPeriodOneRealization.lean),
[`TentProfile.lean`](NLS/Fourier/TentProfile.lean),
[`OddTentProfile.lean`](NLS/Fourier/OddTentProfile.lean), and
[`OrderedTentSources.lean`](NLS/ZakharovShabat/OrderedTentSources.lean)
supply actual continuous profiles and quantitative estimates.

| Public entry point | Scope |
| --- | --- |
| `continuousPeriodOneCoefficients_apply`, `circlePullback_continuousPeriodOneCoefficients` | Every original Fourier integral and the actual almost-everywhere physical representative agree; no finite-support assumption. |
| `norm_sq_continuousPeriodOneCoefficients` | Exact unit-interval Parseval normalization. |
| `integral_tentProfile_mul_cexp`, `periodOneCoefficient_tentProfile` | Exact second-difference exponential transform. |
| `periodOneCoefficient_tentProfile_zero`, `norm_periodOneCoefficient_tentProfile_le_area` | Exact mean (b-a)^2/4 and the same coefficient bound at every frequency. |
| `norm_periodOneCoefficient_tentProfile_mul_frequency_le` | (2 pi abs(n))^2 times the coefficient norm is at most 4. |
| `normalized_orderedTentSource_mem_periodicSpectrum` | Explicit ordered tents realize every iH after normalization, at every finite p>=2; representative and interaction hypotheses are proved. |
| `exists_balanced_orderedTentSource` | At nonzero H, a balanced actual source retains iH with its exact original norm cost. |
| `periodOneCoefficient_oddTentProfile_zero` | An early tent minus its reflected tent has zero original Fourier mean. |
| `norm_periodOneCoefficient_oddTentProfile_le_low`, `norm_periodOneCoefficient_oddTentProfile_mul_frequency_le` | Low-frequency cancellation pi abs(n) b (b-a)^2 and quadratic high-frequency bound 8. |
| `integral_oddTentProfile_mul_exp_lower`, `integral_oddTentProfile_mul_exp_pos` | Quantitative weighted-interaction lower bound and strict positivity for an early nonempty signed pair. |

Public checks include concrete width 1/4 and p=5, as well as signed
profile estimates on [1/8,1/4]. The signed profiles have not yet been
summed over dyadic scales. No periodic-height violation is asserted;
Theorem 1.1 above p=4 remains required and unresolved.

### Theorem 1.1: dyadic interaction growth with bounded original coefficient norm

[`DyadicGeometricBounds.lean`](NLS/Fourier/DyadicGeometricBounds.lean),
[`NormalizedDyadicTent.lean`](NLS/Fourier/NormalizedDyadicTent.lean),
[`DyadicTentSum.lean`](NLS/Fourier/DyadicTentSum.lean), and
[`UniformQuadraticEnvelope.lean`](NLS/SequenceSpaces/UniformQuadraticEnvelope.lean)
prove the upper half of the proposed ordered multiscale construction.

| Public entry point | Scope |
| --- | --- |
| `sum_norm_le_of_dyadic_envelopes` | A bound of 80 for any finite set of scales satisfying the two envelopes; the proof splits at the frequency's dyadic bracket. |
| `periodOneCoefficient_dyadicTentSum`, `circlePullback_dyadicTentSumCoefficients` | The actual finite physical sum, every original Fourier integral, and the Hilbert representative agree. |
| `dyadicTentSum_eq_zero_near_ends` | The full upper profile vanishes on both endpoint intervals of width 2^(-J). |
| `norm_periodOneCoefficient_dyadicTentSum_le`, `norm_periodOneCoefficient_dyadicTentSum_tail` | Uniform coefficient bound 80 and quadratic tail abs(n)^2 abs(U_hat_J(n)) <= 16*4^J, without a scale-count factor. |
| `Coeff.norm_le_of_uniform_quadratic_envelope` | Original lp norm <= C (8N)^(1/p) for a zero-mean sequence bounded by C with quadratic tail C N^2, at every finite Banach exponent. |
| `norm_exponent_dyadicTentSumCoefficients_le` | Actual upper coefficient norm <= 80 (8*2^J)^(1/p), for every finite p>=2. |
| `norm_dyadicTentSumCoefficients_twice_exponent_le` | At J=2P and p=P, the original coefficient norm is at most 640 for every integer P>=3. |
| `integral_normalizedDyadicTent_ge_quarter` | Each sufficiently fine normalized scale contributes at least 1/4. |
| `integral_dyadicTentSum_pow_height` | The upper interaction at H=2^P is at least (P-2)/4 for every integer P>=3. |

Public checks cover negative frequencies, the zero mean and endpoint
support, a concrete scale contribution, and p=5 together with the full
integer-exponent family. The normalized lower coupling and final spectral
normalization estimate remain to be combined with these results.
Theorem 1.1 above p=4 is still required and unresolved; no periodic-height
counterexample or source correction is claimed.

### Theorem 1.1: actual counterexample to the all-exponent printed height

[`LowerDyadicTent.lean`](NLS/Fourier/LowerDyadicTent.lean),
[`OrderedDyadicSource.lean`](NLS/ZakharovShabat/OrderedDyadicSource.lean),
[`DyadicNormalizationBound.lean`](NLS/ZakharovShabat/DyadicNormalizationBound.lean), and
[`SourcePeriodicHeightCounterexample.lean`](NLS/ZakharovShabat/SourcePeriodicHeightCounterexample.lean)
complete the ordered multiscale construction in the original source norm.
This supersedes the historical unresolved-height entries above: the
all-exponent assertion is refuted, while the result through p=4 is proved.

| Public entry point | Scope |
| --- | --- |
| `integral_lowerDyadicTent`, `lowerDyadicTentCoefficients_zero` | Late tent has area one and original mean coefficient one. |
| `norm_lowerDyadicTentCoefficients_le_one`, `norm_lowerDyadicTentCoefficients_tail` | Every signed Fourier coefficient is bounded by one; its quadratic tail is bounded by 4^J. |
| `norm_exponent_lowerDyadicTentCoefficients_le` | Original lp norm <= 1+(8*2^J)^(1/p), for every finite p>=2. |
| `norm_lowerDyadicTentCoefficients_twice_exponent_le` | At J=2P and p=P>=3, the lower coefficient norm is at most nine. |
| `integral_lowerDyadicTent_exp_lower` | Lower interaction at H>=0 is at least exp(2H(1-2^(-J))). |
| `physicalBase_orderedDyadicSource`, `orderedDyadicCurve_support` | Original coefficients reconstruct the combined physical pair, with the upper coupling before the lower. |
| `normalized_orderedDyadicSource_mem_periodicSpectrum` | Normalization places i*2^P in the actual spectrum at every finite target p>=2 for each integer P>=3. |
| `exists_balanced_orderedDyadicSource` | Balanced source preserves that point with its exact original pair norm; no compatibility or nonzero-component hypotheses remain. |
| `norm_orderedDyadicNormalization_le` | Normalization magnitude <=12/(P-2) for integer P>=3. |
| `exists_balanced_dyadicSource_norm_le` | At exponent P, source norm <=2 sqrt(69120/(P-2)). |
| `exists_small_dyadicSource` | For integer P>=100000000, balanced source norm <=1/16 with actual spectral point i*2^P. |
| `sourcePeriodicPrintedHeight_counterexample` | The same source and point escape the printed-height box and all high disks at every cutoff N. |
| `not_sourceTheorem1_1_printed_exhaustion` | Explicit negation of all-source printed exhaustion at p=100000000. |

Public examples check the original mean and negative frequencies, the
concrete p=5 lower norm, physical reconstruction, actual spectral membership
at 32i, the normalization bound, the full counterexample family, and the
concrete negated assertion. No claim about the optimal threshold or every
individual exponent above four is made. Real-type reality and the printed
result through four remain valid. No replacement height is adopted.

Validation: the full project check passed (6624 build jobs), including all
public examples and the axiom audit of 27956 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Theorem 1.1: necessary coefficient growth and a proposed all-p height

[`SourcePeriodicHeightNecessity.lean`](NLS/ZakharovShabat/SourcePeriodicHeightNecessity.lean)
uses the actual balanced dyadic counterexample family.
[`SourcePeriodicExplicitHeight.lean`](NLS/ZakharovShabat/SourcePeriodicExplicitHeight.lean)
packages a separate sufficient correction in the original source norm.

| Public entry point | Scope |
| --- | --- |
| `exists_sourcePeriodicHeightCoefficient_counterexample` | At integer P>=3, every nonnegative C with 276480*C^2<P-2 has an actual balanced source whose spectral point exceeds (1+C*norm)^P. |
| `sourcePeriodicHeightCoefficient_necessary` | A universal original-source strip coefficient requires P-2<=276480*C^2. |
| `sourcePeriodicCountingHeightCoefficient_necessary` | The same necessary growth survives arbitrary source-dependent cutoffs and all high disks. |
| `not_exists_uniform_sourcePeriodicHeightCoefficient`, `not_exists_uniform_sourcePeriodicCountingHeightCoefficient` | No fixed nonnegative coefficient works at all integer exponents, for either strips or box/disk exhaustion. |
| `exists_source_periodicCounting_coefficient_height_of_resolvent` | General counting transfer for any nonnegative coefficient with an exterior resolvent estimate; the printed coefficient-eight API is preserved. |
| `mem_resolventSet_of_sourcePeriodicExplicitHeight` | Both closed exterior edges and the full exterior region for (1+8pM)^p, at all finite p>=1, in the original source norm. |
| `sourcePeriodicSpectrum_abs_im_lt_explicit_height` | Strict spectral strip bound for every source in the original norm ball. |
| `sourceTheorem1_1_proposed_height` | Common open convex source neighborhood, all larger cutoffs, full counting/parity data, central count 4N+2, spectral exhaustion, actual central projection, and analytic moving rectangular integrals. |

Public checks include the cutoff-dependent necessity, a concrete
coefficient-one failure at P=300000, exclusion of every uniform coefficient,
both signs of the corrected p=5 resolvent edge, and simultaneous central
count/parity data with analytic projections on one source neighborhood.
The printed height remains refuted at large integer exponents and proved
through p=4. No correction is adopted and no optimal growth rate is claimed.

Validation: the full project check passed (6626 build jobs), including all
public examples and the axiom audit of 27977 NLS declarations. Focused
builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with
156 labels. Counts do not certify completeness.

### Appendix G introduction: full-time fundamental-solution regularity to audit

Printed p. 135 recalls joint continuity of the original fundamental matrix
on `[0,infinity) x Complex x L2_c` and analyticity in frequency and potential
for every fixed time. The current `l2FundamentalMatrix` in
`L2HermitianOperatorBound.lean` is defined on `[0,1]`; its columns come
from `l2SolutionCurve` in `L2SolutionExtension.lean`. The integral equation,
a.e. differential equation, initial data, norm bounds, and recovery of
continuous inputs are proved. They do not by themselves establish the
full parameter-regularity and all-time statement. No matching public
entry point for that exact assertion was located during this audit.
It remains a concrete obligation, separate from G.2's interval-norm issue.
The plan is to establish regularity of the actual L2 solution and a
compatible extension of periodic inputs to all nonnegative times.

### Appendix G introduction: unit-interval L2 parameter regularity proved

The preceding all-time obligation is now reduced by a proved
unit-interval regularity result. The new modules
`ClassicalVolterraL2Bound.lean`, `L2ScalarVolterra.lean`,
`L2VolterraOperator.lean`, `L2VolterraInverse.lean`, and
`L2FundamentalAnalytic.lean` work with the original physical L2 norm and
actual integral equation. They impose no continuity assumption on the
potential. The existing coordinate integral formula is now public.

| Public entry point | Scope |
| --- | --- |
| `l2Volterra_apply`, `l2Volterra_of_continuous` | Exact original integral and classical-operator recovery. |
| `l2VolterraCoefficientMap`, `norm_l2Volterra_sub_le` | Bounded complex-linear parameter map and potential difference bound. |
| `isUnit_one_sub_l2Volterra` | Invertibility for every physical L2 potential and every complex frequency. |
| `l2SolutionOperator_eq_iff` | Unique actual integral-equation solution for arbitrary continuous forcing. |
| `norm_l2SolutionOperator_le` | Full forcing inverse norm at most exp(abs(z)+norm(u)). |
| `l2SolutionCurve_eq_l2SolutionOperator`, `l2SolutionCurve_unique_integral` | Identification and uniqueness for the existing initial-value solution. |
| `analyticOnNhd_l2SolutionOperator`, `analyticOnNhd_l2SolutionCurve_joint` | Joint parameter analyticity in the operator/uniform curve norm. |
| `analyticOnNhd_l2FundamentalMatrix_joint` | Fixed-time complex analyticity of the original matrix for every t in [0,1]. |
| `continuous_l2FundamentalMatrix_time_joint` | Joint time/frequency/potential continuity including both endpoints. |
| `det_l2FundamentalMatrix` | Determinant one for every original physical L2 input on [0,1]. |

The proof uses continuous approximation with a uniform L2 forcing bound,
then analytic inversion of the actual Volterra operator. It does not
replace the existing solution by an unrelated abstract construction.
Public checks include arbitrary forcing, both inverse identities,
initial-vector additivity, classical recovery, and matrix regularity.
The full `[0,infinity)` claim still requires periodic continuation and
identification with the original equation. The G.2 norm issue is separate.

Validation: the full project check passed (6631 build jobs), including all
public examples and the axiom audit of 28075 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Appendix G introduction: full-time physical L2 regularity proved

`L2PeriodicFundamental.lean`, `L2FundamentalInitialValue.lean`,
`L2PeriodicEquation.lean`, and `L2PeriodicUniqueness.lean` close the
full-time regularity obligation recorded above. The domain is all
nonnegative times and the original physical L2 space, with no continuity
assumption on the potential.

| Public entry point | Scope |
| --- | --- |
| `l2FundamentalMatrix_mul_column` | Matrix multiplication gives the existing initial-value solution for arbitrary initial columns. |
| `l2PeriodicFundamentalMatrix_on_period` | Exact M(s)*B^n formula on each whole closed period, including both joins. |
| `l2PeriodicFundamentalMatrix_unit`, `l2PeriodicFundamentalMatrix_nat` | Recovery on [0,1] and actual monodromy powers at all natural times. |
| `l2PeriodicFundamentalMatrix_zero`, `det_l2PeriodicFundamentalMatrix` | Identity initial value and determinant one for all nonnegative times. |
| `l2PeriodicFundamentalMatrix_add_nat` | Correct multiplication order in the monodromy relation for every natural time shift. |
| `continuous_l2PeriodicFundamentalMatrix_joint`, `analyticOnNhd_l2PeriodicFundamentalMatrix_joint` | Joint continuity through integer joins and fixed-time analyticity for all nonnegative times. |
| `l2PeriodicColumn_integral_on_period` | Actual signed Volterra equation on every closed period. |
| `ae_hasDerivAt_l2PeriodicColumn`, `ae_physicalOperator_l2PeriodicColumn` | Original differential and spectral equations almost everywhere on the full positive time domain. |
| `periodicL2Representative_ofFunction_periodic`, `ae_physicalOperator_l2PeriodicColumn_ofFunction` | Full-time agreement and spectral equation for any original period-one L2 representative. |
| `l2PeriodicColumn_unique` | Uniqueness among continuous columns with the same initial value and period-by-period integral equation. |
| `sourceFundamentalSolution_regularity` | The exact full-time continuity/analyticity assertion recalled on printed p. 135. |

Public checks include integer time 5, fractional time 5/2, a whole-period
shift, the free zero-frequency solution, first-period recovery, determinant
one, the actual integral equation on period three, arbitrary original
periodic representatives, and uniqueness. The construction uses periodic
coefficients after time one. The existing endpoint-clamped classical
construction is used only through its proved unit-interval recovery.

The independent G.2 interval-norm interpretation remains unresolved.
Next audit target: the trace-of-monodromy definition of the discriminant
on printed p. 45 for arbitrary rough Hilbert source potentials. The
existing `canonicalDiscriminant_eq_classical` requires a compatible
continuous representative; its removal is not supplied by the full-time
regularity theorem alone. The dissertation is incomplete.

Validation: the full project check passed (6635 build jobs), including all
public examples and the axiom audit of 28119 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Chapter 2, printed p. 45: the actual L2 monodromy trace for rough sources

`SourcePhysicalL2.lean`, `L2Discriminant.lean`, and
`L2DiscriminantCotangent.lean` extend the physical discriminant comparison
from continuous representatives to every original Hilbert source. The
source map reuses `physicalRestrictionL2CLM` and `periodOnePotential`.
The proof uses exact finite-source recovery, source density, and joint
continuity of the actual physical L2 trace.

| Public entry point | Scope |
| --- | --- |
| `sourcePhysicalL2_representative`, `sourcePhysicalL2_ofFinsupp` | Original Fourier representative on [0,1] and exact finite-curve recovery. |
| `analyticOnNhd_l2Discriminant_joint` | Joint frequency/potential analyticity of the actual L2 monodromy trace. |
| `canonicalDiscriminant_eq_l2_source` | Trace identity for every original Hilbert source, with no continuous-representative hypothesis. |
| `canonicalDiscriminant_eq_l2` | The same identity on the full even-supported Hilbert coefficient subspace. |
| `canonicalPeriodicProduct_eq_l2Discriminant` | Original normalized full spectral product equals actual trace squared minus four. |
| `l2Discriminant_sq_eq_four_iff` | Entire original periodic spectrum is exactly the physical characteristic zero set. |
| `l2Discriminant_parity_levels` | Trace levels two/minus two correspond to positive original even/odd algebraic multiplicity. |
| `l2Discriminant_zero` | Exact original free discriminant normalization. |
| `sourceDiscriminantCotangent_eq_l2`, `sourceDiscriminantCotangent_apply_eq_l2` | Complete source cotangent and every Hilbert variation agree with the physical L2 differential under the established source map. |
| `deriv_canonicalDiscriminant_eq_l2` | Equality of spectral derivatives. |

Public checks cover the literal monodromy trace, arbitrary even-supported
potentials, original representative recovery, source linearity, normalized
spectral product, spectrum equivalence, both parity sectors, arbitrary
Hilbert directions, spectral derivatives, and free/finite-source recovery.
These are exact identities, not only shared zero sets or proportionality.
The source normalization is retained throughout.

The rough-source physical anti-discriminant and separated-characteristic
comparisons remain the next transfer. Their current classical comparison
theorems require continuous representatives. A physical integral formula
for the full rough-potential gradient is also not supplied merely by the
cotangent chain-rule identity. The dissertation remains incomplete.

Validation: the full project check passed (6638 build jobs), including all
public examples and the axiom audit of 28144 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Physical L2 anti-discriminant and separated characteristics at rough sources

`L2SeparatedCharacteristics.lean`, `L2SourceCharacteristics.lean`, and
`L2CharacteristicCotangents.lean` remove the continuous-representative
hypotheses from the physical comparisons at the Hilbert exponent. They
reuse the established source-to-physical L2 map and prove exact identities
by finite-source density.

| Public entry point | Scope |
| --- | --- |
| `analyticOnNhd_l2SeparatedCharacteristic_joint`, `analyticOnNhd_l2AntiDiscriminant_joint` | Actual monodromy-entry formulas are jointly analytic on the entire physical L2 parameter space. |
| `l2SeparatedCharacteristic_eq_zero_iff` | Literal original endpoint condition for normalized initial data, with both boundary signs. |
| `l2SeparatedCharacteristic_zero`, `l2AntiDiscriminant_zero` | Exact sine and zero free normalizations. |
| `l2Discriminant_sq_sub_four` | Delta squared minus four equals delta squared minus four times the two separated characteristics for every physical L2 input. |
| `periodOneBoundaryCharacteristic_eq_l2`, `sourceAntiDiscriminantCandidate_eq_l2` | Exact original-source comparisons for every Hilbert source, without continuous-representative assumptions. |
| `l2SeparatedCharacteristic_source_eq_zero_iff`, `sourceBoundarySpectrum_iff_l2_endpoint` | Original restricted-operator spectrum equals the physical characteristic zero set and the actual L2 endpoint condition. |
| `analyticOrderAt_l2SeparatedCharacteristic_source` | Actual physical zero orders equal original algebraic multiplicities. |
| `l2SeparatedCharacteristic_source_eq_product` | Complete original boundary labelings give the normalized physical characteristic product. |
| `sourceBoundaryCharacteristicCotangent_eq_l2`, `sourceAntiDiscriminantCotangent_eq_l2` | Full continuous cotangent identities on the Hilbert source space. |
| `sourceBoundaryCharacteristicCotangent_apply_eq_l2`, `sourceAntiDiscriminantCotangent_apply_eq_l2` | Every Hilbert source direction is included. |
| `deriv_periodOneBoundaryCharacteristic_eq_l2`, `deriv_sourceAntiDiscriminantCandidate_eq_l2` | Exact spectral derivative comparisons. |

Public checks verify the Dirichlet and Neumann endpoint signs separately,
the off-diagonal anti-discriminant sum, original boundary spectra and
multiplicities, labeled normalized products, arbitrary Hilbert variations,
spectral differentiation, the determinant identity at a characteristic
zero, and both free normalizations.

The remaining physical-gradient transfer is an explicit integral formula
for the actual potential derivative at arbitrary rough L2 inputs and
directions. `ClassicalPotentialVariation.lean` proves the corresponding
variation result for continuous input. The cotangent identities above
alone do not supply that physical formula. The dissertation is incomplete.

Validation: the full project check passed (6641 build jobs), including all
public examples and the axiom audit of 28177 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 solution variation and linearized equation

`L2SolutionVariation.lean`, `L2PotentialVariation.lean`, and
`L2VariationEquation.lean` identify the actual solution derivative with
its physical linearized Volterra solution. They supply the rough-L2
variation prerequisite for the fundamental-matrix gradient formula in
the proof of Lemma G.5 (printed p. 137).

| Public entry point | Scope |
| --- | --- |
| `fderiv_l2SolutionCurve_joint_apply` | Joint frequency/potential derivative in the uniform curve norm, at every physical L2 input. |
| `l2VariationCurve_eq_integral`, `l2VariationCurve_zero`, `l2VariationCurve_unique` | Actual signed integral equation, zero initial value, and uniqueness among its continuous solutions. |
| `fderiv_l2SolutionCurve_potential`, `fderiv_l2SolutionCurve_potential_eval` | Arbitrary L2 potential directions and evaluation at every time, including the endpoint. |
| `l2PotentialVariation_eq_integral` | Explicit off-diagonal forcing with the original plus/minus signs. |
| `norm_l2VariationCurve_le` | Global bound, linear in the frequency and L2 perturbation norms. |
| `l2PotentialVariation_of_continuous` | Exact agreement with the existing classical potential variation. |
| `ae_hasDerivAt_l2VariationCurve`, `ae_hasDerivAt_l2PotentialVariation` | Actual linearized differential equation almost everywhere on the unit interval. |
| `l2VariationCurve_eq_integral_ofFunction`, `ae_hasDerivAt_l2VariationCurve_ofFunction` | Integral and differential equations for arbitrary original square-integrable representatives. |

Public examples verify the full derivative formula, potential directions,
endpoint and initial values, explicit signed forcing integrals,
uniqueness, the norm estimate, the a.e. equation, arbitrary physical
representatives, and classical recovery. The matrix kernel and the
resulting rough-L2 endpoint gradient integrals are not yet claimed.
The dissertation remains incomplete.

Validation: the full project check passed (6644 build jobs), including all
public examples and the axiom audit of 28197 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 variation kernel and endpoint gradient integrals

The matrix-kernel prerequisite for the gradient formula in the proof of
Lemma G.5 (printed p. 137) is now established at arbitrary physical L2
inputs. This is an exact formula, not an assumed gradient or a change
of the original Fourier normalization.

| Public entry point | Scope |
| --- | --- |
| `l2KernelPairing_apply` | Integrated adjugate forcing is the ordinary unconjugated integral of the original L2 representatives. |
| `continuous_l2KernelPairing`, `l2KernelPairing_sub`, `l2KernelPairing_smul` | Joint continuity and linearity in the adjugate column. |
| `continuous_l2VariationCurve`, `continuous_l2PotentialKernelCurve` | Joint continuity needed to pass both base potentials and directions through L2 approximation. |
| `l2PotentialKernelCurve_of_continuous` | Exact recovery of the existing classical variation through its determinant-one kernel. |
| `l2PotentialKernelCurve_eq_variation`, `fderiv_l2SolutionCurve_potential_eq_kernel` | Explicit kernel equals the actual derivative as a whole continuous curve on [0,1]. |
| `l2EndpointGradient`, `continuous_l2EndpointGradient` | Explicit physical adjugate gradient for any complex-linear endpoint functional at any unit-interval time. |
| `fderiv_l2Endpoint_eq_gradient_integral` | Actual L2 Fréchet derivative equals its unconjugated physical gradient integral. |
| `fderiv_sourceL2Endpoint_eq_gradient_integral`, `fderiv_sourceL2Endpoint_eq_physical_integral` | Every Hilbert source and direction, with the original physical Fourier representative and normalization. |

Public checks cover the entire-curve kernel identity, its two column
signs, literal integral pairing, general endpoint functional, an actual
monodromy-entry derivative, original Hilbert source directions,
classical recovery, and both free off-diagonal gradient signs.
Named trace, anti-trace, and separated-characteristic gradient integral
specializations remain to be connected to the existing source
cotangents. Counts do not certify completion of the dissertation.

Validation: the full project check passed (6648 build jobs), including all
public examples and the axiom audit of 28227 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Physical spectral-characteristic gradients on the full Hilbert source space

The generic endpoint integral now supplies the actual trace,
anti-discriminant, and both separated-characteristic gradients at rough
L2 inputs. Existing source cotangents are identified with these physical
integrals in every Hilbert direction.

| Public entry point | Scope |
| --- | --- |
| `intervalIntegrable_l2EndpointGradient_pairing` | Actual L2 endpoint pairings are integrable on every unit subinterval. |
| `fderiv_l2Endpoint_add_eq_gradient_integral` | Endpoint sums differentiate and combine inside the ordinary integral. |
| `l2DiscriminantGradient`, `l2AntiDiscriminantGradient`, `l2SeparatedGradient` | Explicit physical gradients constructed from the proven endpoint kernel. |
| `l2SeparatedCharacteristic_eq_endpoint` | Exact separated endpoint identity, including the original sine normalization and signs. |
| `fderiv_l2Discriminant_eq_gradient_integral`, `fderiv_l2AntiDiscriminant_eq_gradient_integral`, `fderiv_l2SeparatedCharacteristic_eq_gradient_integral` | Actual potential derivatives for all physical L2 bases and directions. |
| `continuous_l2DiscriminantGradient`, `continuous_l2AntiDiscriminantGradient`, `continuous_l2SeparatedGradient` | Continuity in the physical variable. |
| `sourceDiscriminantCotangent_eq_physical_gradient_integral`, `sourceAntiDiscriminantCotangent_eq_physical_gradient_integral`, `sourceBoundaryCharacteristicCotangent_eq_physical_gradient_integral` | Existing source cotangents equal ordinary integrals against the original Fourier-synthesized direction at every Hilbert source. |

Public checks include all six derivative/cotangent formulas,
integrability, the free trace and anti-trace gradients, and the exact
free gradient for both boundary signs. Pointwise comparison with the
classical gradient functions and the resulting connection to existing
corrected coefficient estimates remain the next step. The previously
proved estimates and documented reference/exponent corrections are
unchanged. The dissertation remains incomplete.

Validation: the full project check passed (6651 build jobs), including all
public examples and the axiom audit of 28245 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Classical comparison and actual L2 realization of G.6 coefficient estimates

The endpoint, trace, anti-trace, and separated gradient functions now
have pointwise classical comparisons on the physical unit interval.
The established G.6 signed coefficient vectors and their source-norm
estimates consequently apply to the actual physical L2 derivatives.

| Public entry point | Scope |
| --- | --- |
| `l2EndpointGradient_of_continuous`, `l2DiscriminantGradient_of_continuous`, `l2AntiDiscriminantGradient_of_continuous`, `l2SeparatedGradient_of_continuous` | Exact pointwise agreement on [0,1]. |
| `l2AntiDiscriminantGradientRemainder_of_continuous`, `l2AntiDiscriminantGradientRemainder_lattice` | Subtraction of the actual free L2 gradient and the corrected signed lattice waves. |
| `L2GradientFourierRealizes` | Actual Fourier integrals, factor i, first index -k and second index k. |
| `L2GradientFourierRealizes.unique`, `L2GradientFourierRealizes.norm_rpow` | Unique represented coefficient vector and the exact finite-q source energy. |
| `sourceG6DiscriminantCoefficients_realizes_l2`, `sourceG6AntiDiscriminantCoefficients_realizes_l2` | Existing coefficient vectors represent the actual L2 gradient and its free-reference error. |
| `sourceG6_l2DiscriminantGradient_majorant`, `sourceG6_l2AntiDiscriminantGradient_majorant` | One nonnegative outer-lp majorant on each exact H1 source ball, with the established spectral and exponent hypotheses. |
| `sourceG6_l2DiscriminantGradient_memlp`, `sourceG6_l2AntiDiscriminantGradient_memlp` | Realized whole coefficient sequences belong to outer lp; finite initial spectral values are retained. |

Public checks include the pointwise comparisons, actual free-gradient
subtraction, all signed lattice indices, both Fourier index conventions,
uniqueness, the q=2 energy, a p=q=2 uniform source-ball majorant, and
whole-sequence anti-discriminant summability. No new rough-L2-ball
asymptotic estimate or infinity endpoint is claimed. The existing
G.5–G.7 reference corrections and exponent restrictions remain unchanged.
Physical simple-root gradient normalization remains the next step.

Validation: the full project check passed (6654 build jobs), including all
public examples and the axiom audit of 28266 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

### Actual physical L2 simple-root derivatives and Dirichlet normalization

The actual physical L2 separated characteristics now differentiate any
continuous local selection of a simple zero. The implicit-root quotient
uses the previously proved physical gradient integral for either boundary
sign, with no regularity assumption on the L2 potential or direction.

`L2SpectralVariation.lean` proves spectral differentiation of the entire
solution curve and the endpoint-dual integral identity for every L2
potential, before imposing a characteristic zero. Continuity and density
are used on this unrestricted identity; no density of smooth potentials
inside a root locus is assumed.

`L2DirichletNormalization.lean` proves that the dual curve at a Dirichlet
root is proportional to the forward eigenfunction. The spectral derivative
is -i times that factor times Q, where Q is twice the unconjugated integral
of the two eigenfunction components. Simplicity implies Q is nonzero.
`L2DirichletRootGradient.lean` then identifies the actual branch derivative
with the integral against (y2 squared / Q, y1 squared / Q). These expressions
agree with the classical ones on [0,1]; at zero potential Q=2 and the two
opposite exponential waves have exactly the factor one half.

Next is transfer of this normalized root differential to the original
Hilbert source coordinates and connection to the established corrected
G.7 coefficient estimates. No new asymptotic estimate on arbitrary rough
L2 balls is asserted. G.2's arbitrary-time interval norm remains unresolved;
neither proposed spectral-height correction is adopted. The optional
original m=1 sharpening remains under the accepted Lemma 27.2 correction.
The dissertation is incomplete.

Validation: the full project check passed (6658 build jobs), including all
public examples and the axiom audit of 28313 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `fderiv_l2SeparatedRoot_eq_gradient_quotient` | Both separated boundary signs; any continuous local simple-root branch in physical L2. |
| `hasDerivAt_l2SolutionCurve_spectral`, `deriv_l2Endpoint_eq_spectral_integral` | Actual spectral derivatives of the uniform solution curve and arbitrary linear endpoint functionals. |
| `l2DirichletDualCurve_of_root`, `l2SeparatedGradient_dirichlet_of_root` | Dual proportionality and reversed eigenfunction squares at a Dirichlet zero. |
| `deriv_l2DirichletCharacteristic_of_root`, `l2DirichletNormalization_ne_zero_of_simple` | Spectral derivative factorization; simplicity supplies the required nonzero denominator. |
| `fderiv_l2DirichletRoot_eq_normalized_integral` | Actual branch derivative paired with normalized eigenfunction squares, without complex conjugation. |
| `l2DirichletNormalization_of_continuous`, `l2DirichletNormalizedGradient_of_continuous` | Exact comparison with the established classical quantities. |
| `l2DirichletNormalization_free`, `l2DirichletNormalizedGradient_free` | Free normalization two and both opposite waves divided by two. |

Public checks cover both boundary signs, the unrestricted spectral integral,
the spectral factorization, simplicity implying nonzero normalization,
the expanded squared-eigenfunction derivative, classical comparison, and
the free normalization and waves, including their value at zero frequency.

### Original source Dirichlet differentials and actual L2 G.7 coefficients

The original canonical source Dirichlet differential now has its actual
physical L2 normalized squared-eigenfunction integral for arbitrary
Hilbert potentials and directions. `L2SourceDirichletGradient.lean`
retains the original period-one Fourier synthesis and proves compatibility
with every finite source exponent p>=2. One open complex neighborhood of
the entire real source locus supplies simplicity and nonzero normalization
at every signed index. No continuous representative or H1 assumption is
needed for this differential formula.

`L2SourceDirichletFourier.lean` identifies both unit-mode values of the
actual source cotangent with the normalized L2 Fourier integrals. Finite
directions are handled through their almost-everywhere physical
representatives; no continuity of the base potential is introduced.

`L2SourceG7Gradients.lean` identifies the existing signed G.7 Dirichlet
error vector with the actual normalized L2 gradient minus its actual free
reference. The signed coefficient convention has first index -k, second
index k, and no extra factor i. The represented vector is unique and its
finite-q norm power is exactly the combined coefficient energy. The free
reference has corrected waves at 2*n and -2*n, each divided by two.

Intersecting the physical-realization domain with the established G.7
summability domain gives one open complex domain for both results. On the
original H1 source, the realized whole sequence lies in outer lp with
finite p>=2 and conjugate exponent q, including all finite central indices.
Every real H1 source is covered without an extra smallness, simplicity,
or normalization premise. No new asymptotic estimate on rough L2 balls
or infinity endpoint is asserted.

Next is the actual physical L2 midpoint gradient and its contour formula,
connecting the other half of G.7 to the same construction. G.2's arbitrary-
time interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6661 build jobs), including all
public examples and the axiom audit of 28330 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `sourceBoundaryCharacteristicCotangent_exponent_l2_integral` | Both boundary signs, arbitrary Hilbert bases and directions, and finite source exponent inclusion. |
| `canonicalDirichletRoot_l2_normalized_integral_of_simple` | Actual normalized derivative at any differentiable simple complex canonical root. |
| `exists_global_source_dirichlet_l2_normalized_integral` | One complex neighborhood of the real locus, every signed index, and every Hilbert direction; normalization proved nonzero. |
| `exists_global_source_dirichlet_l2_fourier` | Both unit source directions have the actual normalized L2 Fourier coefficients without a continuous base representative. |
| `L2RootGradientFourierRealizes.unique`, `L2RootGradientFourierRealizes.norm_rpow` | Unique coefficient vector and exact finite-q energy. |
| `l2DirichletGradientRemainder_lattice` | Subtraction of the actual free half-waves with corrected signed indices. |
| `exists_global_sourceG7_l2_realization` | Existing G.7 Dirichlet error vector realizes the physical error at every included Hilbert source in one complex neighborhood. |
| `exists_global_sourceG7_l2_memlp`, `sourceG7_l2_memlp_real` | Whole-sequence H1 summability with physical realization on one complex domain, and the unconditional real-source corollary. |

Public checks include the Hilbert cotangent, arbitrary real Hilbert bases
and directions, complex-domain realization, the generic conjugate-exponent
real H1 result, signed lattice reference, uniqueness, and exact q=2 energy.

### Physical midpoint gradient contours and actual G.7 coefficients

The actual source midpoint differential now has a physical L2 gradient
contour. `L2GradientCurves.lean` places the endpoint and discriminant
gradients in the Banach space of continuous physical curves, proves
spectral continuity in the uniform norm, and constructs the unconjugated
pairing with any rough L2 direction as a continuous linear map.

`L2MidpointContour.lean` integrates the quotient-weighted discriminant
gradient in that uniform norm. Evaluation recovers its pointwise contour,
and the continuous pairing commutes with the contour to give the actual
directional discriminant integral. A radius-times-supremum estimate bounds
the entire physical gradient curve. Nonvanishing of the periodic
characteristic on the circle ensures integrability.

`L2SourceMidpointGradient.lean` identifies this physical integral with the
actual canonical source midpoint derivative on an isolating circle. The
original period-one realization, arbitrary Hilbert directions, and every
finite source exponent p>=2 are retained. Enclosing both indexed periodic
endpoints and avoiding the other cuts supplies denominator nonvanishing;
the two enclosed endpoints may coincide.

`L2SourceMidpointFourier.lean` constructs such circles for every signed
index on one common complex neighborhood of the real source locus. It
identifies the existing signed G.7 midpoint vector with the actual Fourier
coefficients of the physical contour gradient. On the original H1 source,
the whole realized sequence retains G.7's outer-lp summability with finite
p>=2 and conjugate q. The finite central block and collapsed gaps are
included without supplied circles or distinct-endpoint hypotheses.

Next is uniqueness of physical gradient representatives and independence
of the chosen isolating circle, followed by a choice-independent midpoint
gradient API. No new rough-L2-ball asymptotic estimate is asserted. G.2's
arbitrary-time interval norm remains unresolved; neither proposed spectral-
height correction is adopted. The optional original m=1 sharpening remains
under the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6665 build jobs), including all
public examples and the axiom audit of 28375 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `continuous_l2EndpointGradientCurve_spectral`, `continuous_l2DiscriminantGradientCurve_spectral` | Spectral continuity in the uniform norm of physical gradient curves. |
| `l2GradientPairing_apply`, `l2GradientPairing_discriminant` | Continuous unconjugated pairing with rough L2 directions; exact actual discriminant derivative. |
| `circleIntegrable_l2MidpointGradientIntegrand`, `l2MidpointGradient_apply` | Uniform curve contour and its literal pointwise values. |
| `l2MidpointGradient_pairing`, `norm_l2MidpointGradientCurve_le` | Justified pairing-contour interchange and the radius-times-supremum bound. |
| `exists_global_source_midpoint_l2_gradient_contour` | Actual source midpoint derivative from any admissible isolating circle, with finite exponent inclusion. |
| `exists_global_source_midpoint_isolating_circles`, `exists_global_source_midpoint_l2_gradient` | Constructed circles and physical gradient formulas for every signed index on a complex neighborhood. |
| `exists_global_sourceG7_l2_midpoint_realization`, `exists_global_sourceG7_l2_midpoint_memlp` | Exact signed G.7 coefficient vectors and whole-sequence H1 summability for the physical gradients. |

Public checks cover uniform continuity, the actual discriminant differential,
rough L2 pairing-contour interchange, the curve norm bound, arbitrary real
Hilbert source directions, the collapsed zero-potential case, and the generic
finite conjugate-exponent H1 summability result. Contour independence of the
pointwise physical representative is not yet asserted.

### Pointwise gradient uniqueness and contour-independent midpoint gradients

Physical midpoint gradients are now independent of the constructing
isolating circle. `IntervalContinuousUniqueness.lean` proves that equal
actual Fourier coefficients determine continuous functions on the entire
closed physical interval. The proof reconstructs their L2 classes and then
uses continuity to recover both endpoints; no endpoint-matching condition
is imposed.

`L2SourceGradientUniqueness.lean` proves pointwise uniqueness both from a
common signed Fourier vector and from the full Hilbert source cotangent.
`SourcePhysicalGradientRepresents` records the actual unconjugated source
integral, and every continuous curve representing the same cotangent is
equal. The selected representative agrees with any such constructed curve.
Its representation theorem requires existence; the total definition's
zero fallback outside that domain is not asserted to represent a cotangent.

`L2CanonicalMidpointGradient.lean` defines the physical midpoint curve from
the actual source derivative restricted to Hilbert directions. On a common
complex neighborhood of the entire real source locus, it represents that
full restriction at every signed index. Every admissible isolating circle
gives exactly the same curve, including endpoint values and collapsed gaps.
At real Hilbert sources the curve also agrees across all finite ambient
source exponents p>=2.

The signed G.7 midpoint vector now realizes this unique physical gradient
without contour parameters. The established whole-sequence H1 summability
persists on a common complex neighborhood, with finite p>=2 and conjugate q.
No new asymptotic estimate on rough L2 balls or infinity endpoint is claimed.

Next is physical-gradient realization below the Hilbert exponent, using
restriction to the original source spaces 1<p<=2 while retaining their
actual norms and established summability. G.2's arbitrary-time interval
norm remains unresolved; neither proposed spectral-height correction is
adopted. The optional original m=1 sharpening remains under the accepted
Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6668 build jobs), including all
public examples and the axiom audit of 28399 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21
existing warnings and no new warnings. The source inventory check passed
with 156 labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `eqOn_Icc_of_intervalFourierCoefficient_eq` | Fourier uniqueness on any closed positive-length interval, with no endpoint-matching condition. |
| `L2RootGradientFourierRealizes.eqOn` | A common signed coefficient vector determines the physical gradient at every point of [0,1]. |
| `SourcePhysicalGradientRepresents.unique` | The full Hilbert source cotangent determines the entire continuous physical curve. |
| `sourcePhysicalGradientCurve_eq_of_represents` | Every constructed representative equals the selected curve. |
| `exists_global_source_midpoint_physical_gradient` | Canonical physical curve represents the actual source differential and is realized by a constructed contour at every index. |
| `exists_global_source_midpoint_contour_independent` | Every admissible isolating circle produces that same curve, including collapsed gaps. |
| `sourceMidpointPhysicalGradientCurve_exponent_of_real` | Equality with the Hilbert ambient-exponent construction at real sources. |
| `exists_global_sourceG7_canonical_midpoint_realization`, `exists_global_sourceG7_canonical_midpoint_memlp` | Actual signed Fourier identity and original H1 summability without contour parameters. |

Public checks include equality at both physical endpoints, uniqueness from
source cotangents and signed Fourier coefficients, admissible-circle
independence, equality of two represented contour curves, finite-exponent
compatibility, the collapsed zero-source case, and generic conjugate-
exponent H1 summability of the canonical gradient coefficients.

### Physical G.7 gradients in original source spaces below two

The actual canonical midpoint and Dirichlet differentials now have physical
integral formulas in every original source direction for 1<p<=2.
`L2GradientsBelowTwo.lean` differentiates the spectral-coordinate identities
under inclusion into the Hilbert source. It constructs open complex
neighborhoods containing the entire real source locus where these formulas
hold at every signed index. The midpoint uses the canonical Hilbert physical
gradient; the Dirichlet formula uses normalized squared eigenfunctions with
nonzero normalization proved on the same domain.

`L2GradientRestrictionFourier.lean` identifies the signed conjugate vectors
with the actual physical Fourier coefficients in the original source norm.
Both midpoint gradients and Dirichlet errors have this realization on
complex neighborhoods. The Dirichlet error subtracts the actual zero-source
gradient, with its exact half-wave normalization. The endpoint p=2 agrees
with the Hilbert construction.

`L2SourceG7BelowTwo.lean` transfers the established derivative estimates to
both physical G.7 coefficient sequences. For real H1 sources and every
1<p<=2, both sequences belong to outer lp in the exact conjugate pair norm,
including every signed index and the finite central block. The physical
formulas and coefficient realization hold on complex neighborhoods; this
step's summability theorem is for real H1 sources. It does not assert a new
complex-neighborhood summability estimate below two.

Next is physical realization of the G.6 anti-discriminant error in the
original source spaces below two. G.2's arbitrary-time interval norm remains
unresolved; neither proposed spectral-height correction is adopted. The
optional original m=1 sharpening remains under the accepted Lemma 27.2
correction. The dissertation is incomplete.

Validation: the full project check passed (6672 build jobs), including all
public examples and the axiom audit of 28422 NLS declarations. Focused
module builds and the standalone public probe passed, including the concrete
conjugate pair p=3/2, q=3 and the endpoint p=2. There are 21 existing warnings
and no new warnings. The source inventory check passed with 156 labels.
Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `CoeffPair.exponentInclusion_refl` | Identity exponent inclusion, including the Hilbert boundary case. |
| `fderiv_midpoint_below_two_of_hilbert_differentiable`, `fderiv_dirichlet_below_two_of_hilbert_differentiable` | Actual source derivatives restricted from the Hilbert source wherever its coordinate is differentiable. |
| `exists_global_source_midpoint_below_two_integral`, `exists_global_source_dirichlet_below_two_integral` | Physical integrals in every original direction on open complex neighborhoods, with nonzero Dirichlet normalization. |
| `signedGradient_realizes_below_two_of_integral` | An actual source integral determines its signed conjugate Fourier vector. |
| `fderiv_canonicalDirichletRoot_zero_eq_free_below_two` | Exact free half-wave differential for 1<p<=2. |
| `exists_global_sourceG7_midpoint_below_two_realization`, `exists_global_sourceG7_dirichlet_below_two_realization` | Both physical G.7 Fourier realizations on complex neighborhoods, with the actual free gradient subtracted for the Dirichlet error. |
| `sourceG7_below_two_memlp_real`, `sourceG7_below_two_physical_real` | Both whole coefficient sequences have outer-lp summability in the original conjugate norm at real H1 sources. |

Public checks cover the Hilbert boundary case, full original-direction
integrals on complex neighborhoods, subtraction of continuous physical
gradients, and both physical realizations and summability at the concrete
conjugate pair p=3/2, q=3. No infinity endpoint is asserted.

### Physical G.6 errors below two for complex sources

The actual anti-discriminant cotangent now has its physical integral in
every original source direction for 1<p<=2, at every complex potential and
spectral parameter. `L2AntiDiscriminantBelowTwo.lean` restricts the entire
Hilbert cotangent and constructs its error vector in G.6's signed Fourier
convention. The factor i and first-component index reversal preserve the
exact conjugate pair norm. Subtraction uses the actual zero-potential
gradient at the reference parameter.

`L2SourceG6BelowTwo.lean` proves outer-lp summability of this physical error
at both canonical Dirichlet and Neumann sequences for complex H1 sources.
Every signed index and the finite central block are retained. The Hilbert
estimate already applies to complex sources, so restricting it requires
neither a reality assumption nor root simplicity. On the original H1
source, uniqueness of the actual Fourier coefficients identifies the new
cotangent vector exactly with the established Sobolev G.6 vector.

The standalone public checks include arbitrary complex spectral and
reference parameters, exact coefficient energy, zero-source cancellation,
the Hilbert endpoint p=2, the concrete conjugate pair p=3/2 and q=3, and
both boundary conditions. This step supplies no infinity endpoint.

Next is extending the physical G.7 summability below two from real H1
sources to a common complex neighborhood of the real source locus. G.2's
arbitrary-time interval norm remains unresolved; neither proposed spectral-
height correction is adopted. The optional original m=1 sharpening remains
under the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6674 build jobs), including all
public examples and the axiom audit of 28435 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `sourceAntiDiscriminantCotangent_below_two_integral` | Entire physical integral in every original source direction for 1<p<=2. |
| `L2RootGradientFourierRealizes.mul_I` | Exact conversion to G.6's Fourier phase convention. |
| `sourceG6AntiDiscriminantCotangentCoefficients`, `norm_sourceG6AntiDiscriminantCotangentCoefficients` | Actual signed error vector, with its exact conjugate pair norm. |
| `sourceG6AntiDiscriminantCotangentCoefficients_realizes_below_two` | Physical remainder identity for any complex potential and spectral/reference parameters. |
| `memlp_source_antiDiscriminantCotangent_error_below_two_complex` | Original operator estimate at either boundary sequence for complex H1 sources. |
| `sourceG6_below_two_physical_complex` | Whole-sequence physical Fourier realization and outer-lp summability in the original source norm. |
| `sourceG6AntiDiscriminantCotangentCoefficients_eq_sobolev` | Exact equality with the established Sobolev physical G.6 coefficient vector. |

### Complex physical G.7 summability and the full finite source range

Physical G.7 summability below two now holds on a common open complex
neighborhood containing the entire real source locus, rather than only at
real H1 sources. `SourceHilbertGradientComplexSummability.lean` constructs
Hilbert neighborhoods before choosing the outer exponent. Every real outer
exponent greater than one works on those same domains, with the original
H1 source and the finite central block retained.

`L2SourceG7ComplexBelowTwo.lean` intersects the estimate domains with the
analytic coordinate domains, then restricts both actual derivatives to
the original source space for 1<p<=2. On one common complex neighborhood,
both signed conjugate coefficient sequences have outer-lp summability and
realize the canonical midpoint gradient and normalized Dirichlet gradient
error. Dirichlet normalization is nonzero at every signed index. The exact
free derivative and corrected half-wave reference are retained.

`SourceSobolevAllExponents.lean` supplies the original H1 input directly in
every coefficient exponent through its l1 embedding. The map preserves
both Fourier sequences and agrees with the established Hilbert inclusion.
`SourceLemmaG7AllFinite.lean` uses this map to give both corrected G.7
estimates for every finite p>1 on the original complex H1 source, with no
separate physical-compatibility premise. For each exponent, a single open
complex domain contains the real source locus and supports both estimates.

The public checks include a Hilbert domain common to all outer exponents,
the concrete conjugate pair p=3/2 and q=3, the collapsed zero source,
automatic physical H1 realization, and the full finite-exponent statement.
These remain pointwise H1 summability conclusions; no new uniform bound on
all H1 source balls or infinity endpoint is asserted.

Next is auditing the remaining Appendix G physical estimates and source
interfaces against the printed assumptions. G.2's arbitrary-time interval
norm remains unresolved; neither proposed spectral-height correction is
adopted. The optional original m=1 sharpening remains under the accepted
Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6678 build jobs), including all
public examples and the axiom audit of 28454 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `exists_global_hilbert_midpoint_outer_complex`, `exists_global_hilbert_dirichlet_outer_complex` | Complex Hilbert domains chosen before every outer exponent above one, for the actual derivatives and free-reference errors. |
| `exists_global_source_gradients_below_two_complex_memlp` | Both original source operator sequences summable on a common complex neighborhood for 1<p<=2. |
| `exists_global_sourceG7_below_two_physical_complex` | Both exact conjugate-norm sequences, physical Fourier realizations, and nonzero Dirichlet normalization on the same domain. |
| `sobolevSourceExponentInclusion`, `exponentInclusion_sobolevSourceExponentInclusion` | Continuous original H1 inclusion preserving both raw Fourier sequences across source exponents. |
| `sourceG7_below_two_periodic_representative` | Automatic physical H1 representative below two, without an added compatibility premise. |
| `sourceLemmaG7_all_finite_corrected` | Both corrected G.7 estimates for every finite p>1 on the original complex H1 source. |

### G.3 derivative proof correction and consolidated Appendix G audit

The intermediate derivative line in the proof of G.3 omits the remainder
hat. The rendered PDF on printed page 136 displays a uniform bound for the
time derivative of M. `ClassicalFundamentalDerivativeAudit.lean` proves
that at zero potential and time zero the actual fundamental derivative is
diag(-i*z,i*z), with Hermitian operator norm exactly abs(z). The displayed
uniform claim therefore fails even on real spectral parameters with
abs(z)>=1 and the singleton zero-potential source set.

`SourceG3DerivativeCorrection.lean` proves the required corrected bound for
the actual remainder M-E. After the printed exponential normalization,
the full Hermitian derivative is bounded uniformly at every nonzero
complex spectral parameter and every time in [0,1]. On the exact original
periodic H1 source ball of radius M, an explicit valid constant is
4*(8+pi)*(2*M)*exp(4*(2*M)). No spectral-strip restriction is required.
The stated G.3 remainder decay conclusions retain their existing proofs.

`coverage/APPENDIX_G.md` now consolidates the current source audit, including
the actual physical L2 fundamental solution, all seven numbered results,
original H1 source interfaces, corrected references, and exponent ranges.
It distinguishes source-level refutations from intermediate proof typos
and does not treat a corrected theorem as the unchanged printed statement.

Public checks cover the exact derivative norm at an arbitrary complex
parameter and at z=3, failure of the uniform printed estimate, the corrected
bound on the exact source ball, and vanishing of the free remainder's
derivative on the entire closed unit interval.

Next is auditing Appendix H's Hamiltonian formulas and weak-source
identifications against the printed assumptions. G.2's arbitrary-time
interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: the full project check passed (6680 build jobs), including all
public examples and the axiom audit of 28468 NLS declarations. Focused
module builds and the standalone public probe passed. There are 21 existing
warnings and no new warnings. The source inventory check passed with 156
labels. Counts do not certify completeness.

| Public entry point | Scope |
| --- | --- |
| `deriv_classicalHermitianFundamental_zeroPotential_at_zero` | Actual free diagonal generator at time zero. |
| `norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero` | Exact genuine Hermitian operator norm abs(z). |
| `sourceG3_printed_full_derivative_false` | Failure of the displayed uniform full-derivative bound even at the zero potential. |
| `classicalHermitianRemainder_derivative_weighted_sobolev_ball` | Corrected full-matrix derivative bound for every nonzero complex spectral parameter. |
| `sourceLemmaG3_weighted_remainder_derivative` | The same corrected estimate on the exact original periodic H1 source balls. |

See [`coverage/APPENDIX_G.md`](coverage/APPENDIX_G.md) for the current complete
comparison of Appendix G's numbered statements, distinct from a claim that
every printed assertion holds unchanged.

### Actual Riccati and Hamiltonian field rescaling

Appendix H's identity u_k(a,c*b)=c*u_k(c*a,b) is now proved for the actual
Riccati recurrence at every order and every complex scalar, including zero.
`NLSRiccatiRescaling.lean` uses recurrence uniqueness and then proves the
corresponding identity for the physical Hamiltonian integrals. No division
by the scalar or smoothness assumption is needed for the classical identity.

`SobolevRiccatiRescaling.lean` transfers the identity to every admissible
Sobolev density in H^(s-n) and to the next weak H^-1 density for an H^s
source. Continuity and dense smooth Fourier sources preserve the original
period-one coefficients. The result includes the H^0 endpoint and does
not impose extra regularity on the highest derivative.

`SobolevHamiltonianRescaling.lean` proves the Hamiltonian identity on the
original H^(k-1) domain and on the sharper H^m domain of H_(2m+1). It also
proves reciprocal field-rescaling invariance for nonzero scalars on both
domains. These are the existing physical Hamiltonians, with their exact
normalization and original smooth integral meaning.

`coverage/APPENDIX_H.md` records the current recurrence, normalization,
weak-source, polynomial, and physical-integral coverage for H.1 and H.2.
The public checks include scalar zero, the top available Sobolev density,
the weak H^-1 endpoint, mass on H^0, and reciprocal scaling of the odd
Hamiltonian on H^1 without imposing H^2 regularity.

Next is a systematic numbered-statement coverage audit beyond the existing
spectral overview, beginning with Sections 2–3. G.2's arbitrary-time
interval norm remains unresolved; neither proposed spectral-height
correction is adopted. The optional original m=1 sharpening remains under
the accepted Lemma 27.2 correction. The dissertation is incomplete.

Validation: focused module builds, the standalone public probe, and the full
project check passed (6,683 build jobs and all public examples). The axiom
audit passed for 28,476 NLS declarations with only the permitted classical
axioms. The build retains 21 existing warnings and introduces none. The
source inventory check passed for 156 candidate statement labels; this is
not a completeness certificate.

| Public entry point | Scope |
| --- | --- |
| `nlsRiccatiDensity_field_rescaling`, `classicalNLSHamiltonian_field_rescaling` | Actual classical recurrence and physical integral identities for every complex scalar and order. |
| `sobolevRiccatiDensity_field_rescaling` | Equality in the actual lower Sobolev space at every admissible order. |
| `weakSobolevRiccatiDensity_field_rescaling` | Equality in H^-1 at the next weak density, including H^0 sources. |
| `sobolevNLSHamiltonian_field_rescaling`, `sobolevOddHamiltonian_field_rescaling` | Original Hamiltonian regularity and the sharper odd H^m extension, with scalar zero included. |
| `sobolevNLSHamiltonian_reciprocal_rescaling`, `sobolevOddHamiltonian_reciprocal_rescaling` | Nonzero reciprocal rescaling preserves the actual Hamiltonians on both domains. |

See [`coverage/APPENDIX_H.md`](coverage/APPENDIX_H.md) for the current
comparison of the printed recurrence, proof identity, and H.1–H.2 conclusions.

## Section 2 infinity convergence correction

The rendered Section 2 paragraph on printed page 21 asserts Fourier-series
norm convergence without excluding p=infinity. `InfinityTruncation.lean`
now proves the exact correction for every positive weight: universal norm
convergence holds exactly at finite Banach exponents, while an individual
infinity input converges exactly when its weighted coefficients vanish
outside finite sets.

The coefficients 1/w(n) have weighted norm one and every finite Fourier
truncation has error exactly one. `SourceSectionTwoConvergence.lean`
realizes the Sobolev case as an actual period-two tempered distribution
for every real regularity, including negative orders. The same Fourier
sums converge distributionally while failing norm convergence. The
existing finite-exponent and distributional convergence results are retained.

`coverage/SECTION_2.md` records this focused source comparison and
`SOURCE_ERRATA.md` records the missing infinity qualification. The public
checks include p=1, general real regularity, every symmetric cutoff,
the zero-order constant coefficients, and infinity convergence for
finite-p inputs, which may have infinite support.

Next: the scalar bilinear pairing and dual-gradient claims on printed
page 22, followed by the numbered statements in Section 3. This focused
audit does not establish completeness. G.2's arbitrary-time interval norm
remains unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: both focused module builds and the standalone public probe
passed without warnings. The full project check passed all 6,685 build
jobs and public examples. The axiom audit passed for 28,499 NLS declarations
with only the permitted classical axioms. The full build retains 21 existing
warnings and introduces none. The source inventory check passed for 156
candidate statement labels; that count is not a completeness certificate.

## Section 2 physical bilinear pairing

Section 2's printed same-index scalar bilinear pairing is now formally
refuted by the smooth period-one wave exp(2*pi*i*x): its coefficient sum
is one and its actual physical integral against itself is zero. The
corrected pairing reverses one Fourier index. Abstract coefficient duality
remains unchanged; its physical interpretation uses that reflection.

`ArbitraryPeriodBilinearParseval.lean` proves the corrected physical
identity for all positive periods and square-integrable inputs with the
original 1/L factor. It also proves the unchanged sesquilinear formula.
`SobolevBilinearPairing.lean` supplies a bounded bilinear map on every real
Sobolev scale with absolute convergence and the sharp Hölder constant,
including both conjugate infinity endpoints.

`SobolevDistributionPairing.lean` identifies the pairing with normalized
actual distributional action. `SmoothPeriodicTestLift.lean` constructs
an exact Schwartz lift of every smooth period-two test, and
`SmoothPeriodicDistributionPairing.lean` gives the action identity for
all such tests and arbitrary periodic distributions of the stated regularity.
No extra smooth-test growth hypothesis is imposed. The source discrepancy
and the exact scope are recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_2.md`.

Next: arbitrary-positive-period distribution transport and the full
Section 2 dual-gradient representation, including exponent endpoints,
then the numbered Section 3 statements. The dissertation remains incomplete.
G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: the focused builds and standalone public probe passed without
new warnings. The full project check passed all 6,691 build jobs and public
examples. The axiom audit passed for 28,555 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 distributional pairing on every positive period

The corrected Section 2 scalar distributional pairing now holds on every
positive period. `DistributionDilation.lean` constructs continuous linear
rescaling of actual distributions with an exact inverse and the required
inverse Jacobian. Actual translation invariance rescales with the period.

`ArbitraryPeriodDistribution.lean` defines normalized Schwartz coefficient
tests whose periodizations are exactly (1/L) times the negative Fourier
waves. The zero-mode window is therefore normalized by 1/L. Each raw
weighted coefficient is recovered unchanged; every actual periodic
distribution of the stated coefficient regularity has a unique synthesized
representative. Continuous synthesis and distributional Fourier convergence
include the infinity endpoint and all real Sobolev orders. Period two
recovers the existing tests and distributions exactly.

`ArbitraryPeriodDistributionPairing.lean` proves the original smooth-test
action identity for every positive period and both conjugate endpoints.
It also proves existence and uniqueness of the smooth test's actual
normalized Fourier coefficients at every real order and Banach exponent.
The public checks include period three's exact 1/3 normalization, arbitrary
real regularity, p=1 and p=infinity, unique physical reconstruction, and
distributional convergence for the previous norm-convergence counterexample.

The period restriction in the previous scalar-pairing milestone is resolved.
Next: the full Section 2 dual-gradient representation and reflexivity,
with exponent endpoints audited explicitly, then numbered Section 3 results.
The dissertation remains incomplete. G.2's arbitrary-time interval norm
is unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: the focused builds and standalone public probe passed without
new warnings. The full project check passed all 6,694 build jobs and public
examples. The axiom audit passed for 28,624 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 full scalar duality and reflexivity

Section 2's scalar full-dual identification is now proved for every finite
Banach exponent, including p=1 with conjugate exponent infinity.
`FullDuality.lean` constructs the representative of an arbitrary bounded
complex functional, proves exact operator-norm equality, and bundles the
pairing as a linear isometry onto the entire continuous dual.

`SobolevFullDuality.lean` transports this result to every real Sobolev order
under the corrected physical bilinear pairing. Representation is unique,
the norm remains exact, and the coefficient at n is the original functional
applied to the raw mode -n. `SobolevScalarGradient.lean` gives a bounded linear
recovery operator, analytic scalar gradients on the original analytic domain,
and the complete Hessian identity. The p=1 endpoint is included throughout.

`Reflexivity.lean` proves surjectivity of the canonical evaluation map into
the continuous double dual for every positive weight and every 1<p<infinity.
The conjugate exponent is obtained automatically; the final theorem does
not require the caller to supply a second finite exponent. Together with
the existing intrinsic periodic-distribution identification, these scalar
coefficient results apply to the source's Fourier-Lebesgue spaces.

Next: finish the two-component gradient audit with the original signed
coefficients and the distinct infinity pair norm, and audit the unrestricted
infinity-source gradient claim before moving to numbered Section 3 results.
This milestone proves scalar duality and reflexivity; it does not claim
completion of the pair-gradient or endpoint audit. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,704 build jobs and public
examples. The axiom audit passed for 28,692 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 pair gradients and the infinity obstruction

Section 2's two-component gradient representation is now proved for all
finite source exponents and every real Sobolev order. The finite-conjugate
case retains the source q-sum norm; the p=1 case returns a gradient in the
separate frequencywise sum-norm infinity space. Both representations are
unique, bounded linear in the full functional, and analytic on the original
analytic domain. The conversion from signed pair coefficients to physical
scalar Fourier coefficients reflects the first component in both factors
and preserves the corrected physical pairing.

`SobolevPairCotangent.lean` supplies the complete component representation
and uniqueness. `SobolevPairGradient.lean` packages the two original target
norms, with bounds 2^(1/q) and 2 respectively. These are proved bounds, not
claims that the pair gradient is always isometric to the dual. Recovery of
prescribed endpoint components is exact; equal components have twice the
scalar norm, including the inverse-weight infinite-support example.

`InfinityDuality.lean` proves that full coefficient-dual representation is
surjective exactly when the source exponent is finite. A Hahn-Banach
functional vanishes on every finite sequence but is nonzero on one, so it
has no l1 representative. It is itself an everywhere-analytic functional
whose derivative has no coefficient gradient at any point.
`SobolevInfinityDuality.lean` transports the obstruction to every real
Sobolev order and the original weighted infinity pair norm.

The scalar duality statement on page 21 explicitly assumes finite p and
remains valid. The gradient paragraph on page 22 must retain that source
restriction: interpreting it for arbitrary infinity-source analytic
functionals is false, even with the corrected physical pairing. In
particular, the later automatic Poisson-regularity sentence cannot use
analyticity alone to supply a gradient for an infinity-domain functional.
The exact scope is recorded in `SOURCE_ERRATA.md` and `coverage/SECTION_2.md`.

Next: audit the Section 2 Poisson bracket and its automatic regularity
claim against these full gradient APIs, then the numbered Section 3 results.
The dissertation remains incomplete. G.2's arbitrary-time interval norm
is unresolved; neither proposed spectral-height correction is adopted.
The optional original m=1 sharpening remains under the accepted Lemma 27.2
correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,708 build jobs and public
examples. The axiom audit passed for 28,770 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 Sobolev Poisson pairing on common physical states

Section 2's Poisson pairing now covers every real Sobolev order and
conjugate gradient exponents, with the printed -iJ sign and matrix.
`SobolevBivector.lean` proves boundedness, absolute convergence, the signed
Fourier formula, and antisymmetry with explicit opposite-order transport.
The cross-component sum uses equal signed indices: reflecting the first
signed component converts it to the corrected physical scalar pairing,
which still uses opposite indices.

`ConjugateSobolevBracket.lean` applies this pairing to the full differentials
on reciprocal Sobolev domains when both source exponents are finite.
`SobolevCommonState.lean` constructs their closed Banach intersection, with
the maximum of the two original source norms. Every pair of representatives
with equal raw signed coefficients belongs to this intersection, and the
two representatives synthesize the same actual distribution pair on every
positive period.

`SobolevCommonBracket.lean` evaluates both functionals at that common state.
It proves the physical formula, automatic absolute convergence, analyticity
on the entire intersection of the analytic domains, and the left product
rule. The recovered gradients represent the complete ambient differentials
on every direction. The bracket bound is twice the product of the original
operator norms; no extra Hilbert regularity hypothesis is imposed.

`SobolevEndpointBivector.lean` retains the original l1 and frequencywise
sum-norm infinity pair spaces. Given represented gradients, its pairing is
bounded and absolutely convergent; analytic gradient fields give an analytic
bracket. This does not extend full-gradient existence to arbitrary analytic
functionals on an infinity source space, which the preceding milestone
refuted.

Next: formally compare this interface with the existing physical source
bracket and finish the remaining bracket algebra and domain audit, then
continue with numbered Section 3 results. Core bivector antisymmetry and a
left product rule do not by themselves establish the full bracket algebra
or Jacobi identity on these Sobolev domains. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither
proposed spectral-height correction is adopted. The optional original m=1
sharpening remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,713 build jobs and public
examples. The axiom audit passed for 28,868 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 bracket compatibility, domain exchange, and Hilbert Jacobi

The new full-gradient Sobolev bracket now agrees with the established
physical source bracket on their order-zero overlap.
`SobolevSourceCompatibility.lean` gives the signed-to-physical coordinate
equivalence, including exact first-component frequency reversal, and the
full differential mode formula at every real Sobolev order. Its comparison
allows any finite conjugate pair p,q and an ambient exponent r>=2 with
p<=r and q<=r. The two functionals are restricted from the same ambient
source space. Equality holds for actual brackets at every common physical
base point under differentiability of those ambient functionals.

`SobolevBracketSwap.lean` proves antisymmetry on the entire common Sobolev
domain for every real order and finite conjugate source pair. It explicitly
exchanges the two ambient domains, normalizes the double negative order
without changing signed coefficients, and exchanges the representatives of
the same state. The right product rule is also proved, complementing the
previous left product rule.

`SobolevZeroBracket.lean` defines a single-domain bracket from the full
Sobolev differentials at order zero and exponent two. It agrees both with
the common-state bracket and, through the coordinate equivalence, with the
existing physical bracket. This proves Jacobi for arbitrary functionals
analytic at the base point, analytic closure on their original domain,
antisymmetry, both product rules, left additivity under differentiability,
and scalar homogeneity (including scalar zero).

These results do not assert that arbitrary reciprocal Sobolev intersections
are closed under nested brackets. The Jacobi transfer is specifically on
the order-zero Hilbert domain; the common-domain antisymmetry and product
rules hold for every real order. The legacy ambient comparison at r=infinity
uses its existing maximum pair norm and finite-exponent restrictions; it
does not imply full coefficient-gradient representation on the original
infinity source norm. The previously proved infinity obstruction remains.

Next: audit the general weighted sesquilinear product and the normalized
periodic action of locally integrable functions in Section 2, then resume
the numbered Section 3 spectral statements. The dissertation
remains incomplete. G.2's arbitrary-time interval norm is unresolved;
neither proposed spectral-height correction is adopted. The optional
original m=1 sharpening remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,716 build jobs and public
examples. The axiom audit passed for 28,936 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 sesquilinear duality and physical pairings

Section 2's sesquilinear product is now proved on the full real Sobolev
scale and at both conjugate endpoints. `SobolevSesquilinearPairing.lean`
bundles physical conjugation as a conjugate-linear isometric involution:
it conjugates coefficients and reverses their Fourier indices. Composing
the corrected bilinear product with this involution gives precisely the
printed same-index sesquilinear sum. The sum converges absolutely, has a
constant-one norm bound, is jointly continuous, and is complex linear in
the first variable and conjugate linear in the second.

`SobolevPairSesquilinear.lean` adds the two signed components. The product
has a constant-one bound in the original finite pair norms, and in both
endpoint orientations using the separate frequencywise sum-norm infinity
space. All three pair products are jointly continuous and absolutely
convergent. Reflecting both first components recovers the physical scalar
Fourier convention without changing the product. The maximum product norm
is used only as an auxiliary continuity coordinate, not as the source
infinity norm.

`SobolevSesquilinearDuality.lean` identifies the entire scalar continuous
dual at every finite source exponent, including one, with a unique
opposite-order representative of exactly the operator norm. This Riesz
map is a conjugate-linear isometry; multiplying a functional by i multiplies
its representative by -i. Its coefficient at n is the conjugate of the
functional on the raw mode n. The infinity-source analytic counterexample
persists with this convention, so no unrestricted infinity Riesz or gradient
claim is introduced.

`SobolevSesquilinearDistributionPairing.lean` identifies the product with
actual periodic distributional action on a conjugated smooth test for every
positive period. Every smooth periodic test supplies its unique coefficient
representative automatically. The original normalized physical L2 integral
formula is also proved, retaining the factor 1/L. These statements keep the
sesquilinear same-index formula distinct from the corrected opposite-index
bilinear formula.

Next: prove the normalized periodic action for locally integrable periodic
functions, then resume the numbered Section 3 audit. The dissertation remains
incomplete. G.2's arbitrary-time interval norm is unresolved; neither proposed
spectral-height correction is adopted. The optional original m=1 sharpening
remains under the accepted Lemma 27.2 correction.

Validation: focused builds and the standalone public probe passed without
warnings. The full project check passed all 6,720 build jobs and public
examples. The axiom audit passed for 29,013 NLS declarations with only the
permitted classical axioms. The full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Section 2 normalized L1 periodic action

Section 2's normalized action is now proved for locally integrable data on
any positive period. `PeriodicL1Functional.lean` constructs the bounded
functional on continuous circle tests from interval-integrable input. Its
operator norm and every actual Fourier coefficient are bounded by the
normalized L1 norm. No square-integrability or boundedness hypothesis is
needed on the input.

`PeriodicL1Pairing.lean` applies that functional to the uniformly convergent
Fourier series of a smooth periodic test. The resulting opposite-index
coefficient sum equals the physical integral with exactly the factor 1/L.
The proof handles arbitrary positive periods directly.

`PeriodicL1Distribution.lean` realizes these bounded coefficients as an
actual periodic tempered distribution. Its normalized windowed action on
every smooth periodic test equals the same integral, and its Fourier
coefficients are exactly the normalized physical coefficients. The product
series converges absolutely. The distribution is unique among periodic
tempered distributions with these coefficients and depends only on the
almost-everywhere class on the fundamental interval. Conjugating the test
gives the corresponding sesquilinear action. Local integrability supplies
the interval hypothesis; the construction also works for the periodic
extension of arbitrary interval-integrable data.

This closes the pending normalized periodic smooth-test action obligation
on printed page 21. It does not assert an additional global real-line
integral formula for arbitrary Schwartz tests. The existing infinity norm
convergence, scalar pairing, and infinity duality qualifications remain.

Next: audit Section 3's numbered statements, starting with Proposition 3.1.
Its printed height must retain the existing qualification from Theorem 1.1;
neither proposed height correction is adopted. The dissertation remains
incomplete. G.2's arbitrary-time interval norm and the optional original
m=1 sharpening remain unresolved.

Validation: focused builds and the standalone public probe passed without
warnings, including a non-unit-period normalization check. The full project
check passed all 6,723 build jobs and public examples. The axiom audit passed
for 29,053 NLS declarations with only the permitted classical axioms. The
full build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Proposition 3.1 on the full period-two source space

Proposition 3.1 (printed page 23) now has an explicit statement on the entire
period-two potential space with the original finite-exponent component-sum
norm. The earlier printed-height source theorem only covered embedded
period-one potentials. `PeriodTwoPrintedHeightCounting.lean` supplies the
full period-two neighborhood theorem, without an even-support restriction.

For 1<=p<=4, one open convex neighborhood containing the potential and zero
supports all sufficiently large cutoffs, the original norm-dependent
height, exact central and disk algebraic multiplicities, exhaustion, and
analytic moving rectangular projections. The original source norm occurs
in the height; the maximum norm is used only in the equivalent operator
coordinates. At every finite p, a separate theorem retains the established
height-N qualitative counting data on the original source space.

`Proposition3_1.lean` bundles the actual printed clauses: discreteness,
two eigenvalues per distant disk counted algebraically, the central count
4N+2, conditional parity and its central dimensions, exhaustion, and
real-type spectral reality. The conditional disk parity also implies the
actual pointwise unit-translation law of every finite-exponent eigenfunction.

The same module transfers the existing balanced dyadic counterexample to
the full period-two source space without changing its original norm. For
every integer P>=100000000, it gives a source of norm at most 1/16 and an
actual spectral point outside the printed box and high disks for every
cutoff. `not_proposition3_1_all_p` explicitly refutes the unrestricted
printed proposition at exponent 100000000. This is a source qualification,
not a replacement-height theorem; no proposed correction is adopted.

Next: audit Lemma 3.2, explicitly checking its operator norms in the source
pair norms, then continue through Section 3. The dissertation remains
incomplete. The earlier Section 2 endpoint and pairing corrections, G.2's
unresolved arbitrary-time interval norm, and the optional original m=1
sharpening remain as recorded.

Validation: focused builds and a standalone public probe passed without
warnings. The probe covers the p=4 endpoint, odd Fourier support, original
norms, central parity counts, all-finite-p qualitative counting, and the
concrete refutation. The full check passed all 6,725 build jobs and public
examples. The axiom audit passed for 29,081 NLS declarations with only the
permitted classical axioms. The build retains 21 existing warnings.
The source inventory check passed for 156 candidate statement labels; that
count is not a completeness certificate.

## Lemma 3.2 in the original pair norms

Lemma 3.2 (printed pages 23–24) is now checked in the original
component-sum pair norms. `SourceFreeResolvent.lean` transports the actual
free resolvent through the coefficient-preserving norm equivalences.
Clause (i) is compact in the original l1 space, and the same compactness
holds on every finite-exponent source space. Clause (iii)'s printed
8p/r estimate holds in the original p-to-one norms; the proof gives 4p/r.

The printed clause (ii) is false in these norms, already at p=2.
`SourceFreeResolventCounterexample.lean` uses lambda=i/10000 and a vector
with both zero-mode coefficients equal to one. The input norm is exactly
sqrt(2), the output norm is 20000, and the printed operator bound is 10800.
The output/input ratio exceeds that bound. The parameter is off the free
lattice with nonzero imaginary part, and the input is a finite, smooth
Fourier vector. `not_lemma3_2_ii_original_norms` explicitly refutes the
printed assertion in this domain.

`PairComponentHolder.lean` proves the exact two-component comparison
factor 2^(1-1/p), including p=1, and its attainment on equal components.
The original p-to-one free resolvent has a proved corrected height bound
with this factor multiplying the printed expression. A zero-mode lower
bound also proves that its pole term must account for this factor.
At p=1 the factor is one and the printed height bound remains valid.
The older maximum-product bound remains valid as stated in its own norm;
it does not certify the original component-sum operator estimate. The
corrected estimate is recorded separately, not silently substituted for
the false printed clause.

Next: audit Corollary 3.3 in the source norms and its dependence on the
maximum-product Neumann estimate, then continue Section 3. The failure
of the printed p-to-one bound alone does not refute the corollary's
resolvent region. The dissertation remains incomplete; the existing
spectral-height, Section 2, G.2, and optional m=1 qualifications remain.

Validation: focused builds and the standalone public probe passed without
warnings, covering compactness in the actual l1 norm, both endpoint and
finite-exponent factors, the pole lower bound, the concrete counterexample,
and the printed strip bound. The full check passed all 6,728 build jobs
and public examples. The axiom audit passed for 29,124 NLS declarations
with only the permitted classical axioms. The build retains 21 existing
warnings.
The source inventory check passed for 156 candidate labels; this count
is not a completeness certificate.

## Corollary 3.3 in the original source norms

Corollary 3.3 (printed page 24) is now proved for every finite Banach
exponent on the full period-two potential space in the original
component-sum norms. Its printed sufficient region remains valid:
`(4p/abs(Im(lambda))^(1/p)+1/abs(Im(lambda)))*norm(phi)<1`, with nonzero
imaginary part so both denominators are meaningful. This follows from
the valid maximum-product Neumann bound and the contractive conversion
of the original potential norm. It does not use the false original-norm
p-to-one estimate from Lemma 3.2(ii).

`SourceResolvent.lean` defines the actual operator, spectral pencil,
one-derivative inverse, base-space resolvent, and complete resolvent set
in the original norms. The source resolvent set equals the established
maximum-product resolvent set. Both inverse identities hold throughout
that set, the base-space inverse factors through the coefficient-preserving
domain inclusion, and the pencil is exactly lambda times inclusion minus
the source operator. The resolvent is compact and analytic on its full
natural set; its complement has the discrete subspace topology.
At zero potential it agrees with the original free resolvent at every
parameter off the free lattice, including real parameters.

`SourceCorollary3_3.lean` proves the numerical region is open and nonempty,
with one common height for every original-norm ball of potentials.
`sourceCorollary3_3` bundles the printed conclusion, actual resolvent-set
membership, both inverse identities, and discreteness. The p=1 endpoint
is included. No period-one support restriction is imposed.

Next: audit Lemma 3.4 in the original p-to-one pair norms, tracking the
component constants in the existing sandwich-resolvent estimate. The
dissertation remains incomplete, and all previously recorded source
qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The source inventory check passed for 156 candidate labels;
this count is not a completeness certificate. The full check passed all
6,730 build jobs and public examples. The axiom audit passed for 29,165
NLS declarations with only the permitted classical axioms. The build
retains 21 existing warnings; the new modules add none.

## Lemma 3.4 in the original pair norms

Lemma 3.4 (printed page 25) is now proved in the original component-sum
pair norms for every finite Banach exponent and every period-two
potential. `SourceDoubleResolvent.lean` constructs the actual map
R0 Phi R0 from the original p space to the original l1 space. Its
composition identity uses the original-norm free resolvent and potential
convolution, and both coefficient formulas are proved in the library's
raw scalar Fourier convention.

The explicit admissible constant is c_p=64p^2. The maximum-product
estimate has constant 32p^2; transporting its l1 output to the original
sum norm costs at most two, while the input and potential conversions
are contractive. The same comparison applies to the Fourier remainder.
The source only asks for a constant depending on p, so this verifies its
claim without asserting sharpness. The numerical discrepancy in
Lemma 3.2(ii) is not used or altered.

`SourceLemma3_4.lean` supplies `sourceLemma3_4`, with the positive constant
quantified before the potential, radius, spectral parameter, and strip
index. Membership in a permitted punctured strip proves that the free
inverse exists. The p=1 endpoint and both signs of the strip index are
included. The zero strip is controlled by the full potential remainder;
Lean's totalized division makes its frequency term zero.

The proof reuses `sourceFourierTail`, including its exact boundary cutoff,
norm monotonicity, and convergence to zero, and adds its contraction
bound. The explicit sandwich bound tends to zero, yielding uniform
smallness of the actual original-norm operator on all sufficiently high
punctured strips at every fixed admissible radius.

Next: Corollary 3.5 in the original source topology, with one neighborhood
and cutoff controlling the full stated complement of the central box
and high disks. The dissertation remains incomplete, and earlier source
qualifications remain in force.

Validation: the focused builds and standalone public probe passed without
warnings, including the original-norm composition, quantified constant,
p=1 endpoint, remainder boundary modes, and uniform smallness. The source
inventory check passed for 156 candidate labels; this is not a completeness
certificate. The full check passed all 6,732 build jobs and public
examples. The axiom audit passed for 29,183 NLS declarations with only
the permitted classical axioms. The build retains 21 existing warnings;
the new modules add none.

## Corollary 3.5 in the original source topology

Corollary 3.5 (printed page 26) is now proved on the entire period-two
source space for every finite Banach exponent, using the original
component-sum norm for both the potential topology and the resolvent's
base space. `SourceCorollary3_5.lean` gives one positive cutoff and one
open, convex, connected neighborhood containing the potential and zero.
Every potential in that neighborhood has its actual compact analytic
resolvent on the precise printed box-and-disk complement.

The geometry is unchanged: the central box has strict real-part bounds
and non-strict imaginary-part bounds; the removed high disks are open
quarter-pi disks with abs(n)>N. The proof preserves the vertical boundary
case abs(n)=N in the strip argument. The supporting height-and-strips
theorem includes equality at the horizontal height, so it also handles
horizontal contour points which lie inside the printed central box.

`sourceCorollary3_5_all_larger` proves the same conclusions for every
larger cutoff on the same neighborhood. The full source resolvent-set
inclusion is explicit, and the complement of that actual set lies in the
stated box-and-disk union. The construction pulls back the established
maximum-product neighborhood through the coefficient-preserving norm
equivalence, then uses the actual original-norm resolvent. No period-one
support restriction, p>1 restriction, or printed-height assumption is
introduced. Convexity also controls the entire line from zero to the
potential with one cutoff.

Next: equation (1.4), transporting the actual Cauchy-Riesz contour
projectors and their source analyticity to the original norms, followed
by the parity subspaces and Lemma 3.6. The dissertation remains incomplete;
all earlier source qualifications remain in force.

Validation: the focused build and standalone public probe passed without
warnings, covering the common neighborhood at all finite exponents,
the p=1 line segment, horizontal-boundary admissibility, and actual
inverse identities in the original domain. The source inventory check
passed for 156 candidate labels; this is not a completeness certificate.
The full check passed all 6,733 build jobs and public examples. The axiom
audit passed for 29,188 NLS declarations with only the permitted classical
axioms. The build retains 21 existing warnings; the new module adds none.

## Equation (1.4) in the original norms

Equation (1.4) (printed page 26) now has actual Cauchy-Riesz contour
projectors in the original component-sum norms. `SourceResolventContours.lean`
defines normalized, positively oriented circle integrals and four-edge
rectangle integrals of `sourceResolvent`. The central projector uses the
actual lower-left and upper-right corners of the height-N box.

For admissible contours, bounded linear conjugation commutes with these
operator-norm integrals. The resulting equalities identify them with the
established maximum-product contour operators. Integrability and evaluation
on vectors are proved in the original norm. The circle and central rectangle
operators are idempotent and compact, and their ranges are finite-dimensional.
The circle integral also has analytic dependence on the potential near every
source for which its circle lies in the full resolvent set.

`SourceEquation1_4.lean` proves the simultaneous statement. One positive
cutoff and one open, convex, connected original-norm neighborhood contain
the potential and zero. For every larger cutoff, the central rectangular
projector and every quarter-pi circle projector with abs(n)>N are analytic
on that same neighborhood. Every contour is in the actual source resolvent
set, and every corresponding actual integral is a compact finite-rank
projection. All finite Banach exponents, including p=1, and all period-two
potentials are covered without an even-support restriction.

The central boundary is established separately on all four edges, including
the horizontal edges inside the printed box. The integrals are defined as
integrals of the original resolvent, and their conjugation identities are
proved rather than used as replacement definitions. No quantitative claim
of isometry between the original norm and the maximum-product norm is made.

Next: the closed complementary parity subspaces and Lemma 3.6 in the original
norms, then the restricted projectors of equation (1.5). The dissertation
remains incomplete; earlier source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers the literal operator integrals, evaluation,
projection identities and finite rank, the common p=1 neighborhood, and
the full central-boundary package at every finite exponent. The source
inventory check passed for 156 candidate labels, not a completeness
certificate. The full check passed all 6,735 build jobs and public
examples. The axiom audit passed for 29,216 NLS declarations with only
the permitted classical axioms. The build retains 21 existing warnings;
the new modules add none.

## parity subspaces and Lemma 3.6 in the original norms

The closed even and odd subspaces immediately before Lemma 3.6 (printed
page 26) are now implemented in the original component-sum norms.
`SourceParity.lean` proves the exact printed coefficient conditions,
closedness, complementary bounded projections, and a topological direct
sum. The masks are contractive for every finite Banach exponent. Frequency
doubling gives a linear isometric equivalence from period-one coefficient
pairs onto the even subspace, with an explicit inverse reading index 2n.

`SourceLemma3_6.lean` proves that the actual Zakharov-Shabat operator,
with its original one-derivative domain, preserves both parities for
period-one potentials at every finite exponent, including p=1.
`sourceLemma3_6` supplies the even support automatically through the
canonical period-one embedding; a separate entry point accepts explicit
even support. The operator intertwines the domain and base parity masks.
The actual source resolvent and admissible circle integral commute with
the base parity projections.

An explicit odd potential sends an even domain vector to an output with
a nonzero odd coefficient. This verifies that the period-one assumption
cannot be dropped; it is not a correction to the source, whose proof
states this assumption explicitly. No claim identifies the infinity
endpoint's source pair norm with the maximum-product norm.

Next: equation (1.5), with actual continuous linear endomorphisms of each
parity subspace and analytic dependence on a neighborhood within the
period-one potential space. The dissertation remains incomplete; earlier
source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers both printed support conditions, negative
frequencies, the topological direct sum, finite-exponent contraction,
the isometry and inverse, domain invariance including p=1, nonconstant
mode coupling, necessity of period one, and commutation with the actual
resolvent and circle integral. The source inventory check passed for 156 candidate labels, not a
completeness certificate. The full check passed all 6,737 build jobs and
public examples. The axiom audit passed for 29,285 NLS declarations with
only the permitted classical axioms. The build retains 21 existing
warnings; the new modules add none.

## equation (1.5) in the original period-one topology

Equation (1.5) (printed page 26) now has actual bounded endomorphisms of
the original-norm parity subspaces. `SourceParityRestriction.lean` constructs
the central rectangular and circle projectors with each parity subspace
as both domain and codomain. For even-supported potentials and admissible
contours, their values agree exactly with the actual original-norm contour
integrals on those subspaces. They are idempotent and have finite-dimensional
range. The restricted range is exactly the part of the ambient range lying
in the selected parity subspace.

The construction uses bounded compression on the space of operators.
Commutation with parity proves that this compression equals restriction;
the rectangular commutation result covers all four edges. Analyticity of
compression transfers analytic dependence from the ambient projectors.

`SourceEquation1_5.lean` gives one positive cutoff and one open, convex,
connected neighborhood in the original period-one potential coordinates,
containing both the potential and zero. Simultaneously for both parities,
every larger central projector and every quarter-pi circle with abs(n)>N
is analytic on that neighborhood, agrees with the actual integral there,
and is a finite-rank projection on the parity subspace. The canonical
`periodOnePair` embedding supplies even support. Every finite Banach
exponent, including p=1, is covered.

No period-one assumption is dropped, and the neighborhood is open in the
period-one parameter space specified by the source. The fixed-norm-height
qualifications in Proposition 3.1 and Theorems 1.1 and 1.4 remain unchanged.

Next: the rank calculations following equation (1.5), then Lemma 3.7.
The dissertation remains incomplete; earlier source qualifications remain
in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe checks typed domains and codomains, equality with the
literal source resolvent integral, the exact restricted range, idempotence
and finite rank at p=1, and the common neighborhood for all finite exponents,
parities, and cutoffs. The source inventory check passed for 156 candidate
labels, not a completeness certificate. The full check passed all 6,739
build jobs and public examples. The axiom audit passed for 29,313 NLS
declarations with only the permitted classical axioms. The build retains
21 existing warnings; the new modules add none.

## original-norm ranks and periodic counts after equation (1.5)

The rank calculations and counting conclusions on printed page 27 now apply
to the actual original-norm contour projectors. The central rectangle has
rank 4N+2, and every distant quarter-pi circle has rank two. For period-one
potentials, the typed central restriction has rank 2N+2 in the parity of N
and 2N in the other parity. A distant circle has rank two in the parity of
its index and rank zero in the opposite parity, including negative indices.

`ConjugatedRanges.lean` gives linear range equivalences under continuous
linear conjugation, including intersections with transported subspaces.
`SourceContourRanks.lean` applies these to the actual source integrals and
typed parity restrictions. The norm conversion is not claimed to be an
isometry. Within the original norm, the typed restricted range is linearly
isometric to the corresponding ambient range intersection.

`SourcePeriodicCounting.lean` packages the numeric ranks together with the
established algebraic multiplicities of the coefficient operator, under
coefficient-preserving norm conversion. The disk counts are two with
algebraic multiplicity, and the central count is 4N+2. One positive cutoff
and one open, convex, connected original-norm neighborhood containing the
potential and zero support all larger cutoffs simultaneously. The actual
central and circle projectors are analytic there. A period-one version
also gives analytic typed restrictions and the same complete counting data.
All finite Banach exponents, including p=1, are covered.

Every vector in a distant contour range has the index's parity for an
even-supported potential. Eigenvectors in the actual original-norm domain
inherit that parity, and their continuous Fourier representatives satisfy
the corresponding unit-translation law. The full original-norm spectrum
is exhausted by the central cluster and unique high disks; its exterior
resolvent is analytic. Real-type potentials have real spectrum, without
an even-support restriction.

The central box here has height N, as in Corollary 3.5 and equations
(1.4–1.5). This does not resolve or adopt a correction to the separate
printed norm-dependent height in Proposition 3.1 and Theorems 1.1 and 1.4.
The positive cutoff and contour admissibility hypotheses are retained.

Next: Lemma 3.7, the analytic midpoint and squared-gap trace expressions
in the original source norms. The dissertation remains incomplete;
earlier source qualifications remain in force.

Validation: focused builds and the standalone public probe passed without
warnings. The probe covers full ranks and algebraic counts on one neighborhood,
both central parity formulas, negative odd disk indices, the p=1 segment to
zero, analytic typed restrictions, physical antiperiodicity, spectral reality,
and exhaustive source-spectrum classification. The source inventory check
passed for 156 candidate labels, not a completeness certificate. The full
check passed all 6,742 build jobs and public examples. The axiom audit passed
for 29,407 NLS declarations with only the permitted classical axioms. The
build retains 21 existing warnings; the new modules add none.

## Lemma 3.7 in the original source norms

Lemma 3.7 (printed page 27) now uses traces of the actual original-norm
operator restriction. `SourceContourTrace.lean` lifts each contour-range
vector into the original one-derivative domain and proves that inclusion
recovers that same vector. Its intrinsic endomorphism acts by `sourceOperator`
on this lift. A proved range conjugation identifies its power traces with
the established coefficient-space traces; the source functions are defined
from the intrinsic traces themselves.

The midpoint is one half of the first trace, and the squared gap is twice
the second trace minus the square of the first. At rank two, the trace of
the centered square is exactly half the squared gap, as printed. These
identities hold for coincident eigenvalues and possible nontrivial Jordan
blocks. The functions agree with the midpoint and squared difference of
the algebraically counted enclosed pair. Free-potential values are pi*n
and zero, respectively.

`SourceContourReduction.lean` constructs analytic ambient transport, inverse
transport, and the operator on a fixed reference range, on an open neighborhood.
The concrete continuous linear range isomorphism is induced by that transport.
Its domain lift represents the transported vector exactly, and the transported
operator intertwines the actual original-domain operator. All power traces,
and both displayed rank-two formulas, agree in the intrinsic and fixed-range
representations.

`SourceLemma3_7.lean` supplies one positive cutoff and one open, convex,
connected original-norm neighborhood containing the potential and zero.
The midpoint and half-squared-gap functions are analytic there for every
high disk. The same neighborhood retains the actual counting data, the
trace formulas, and the enclosed eigenvalue pair with its algebraic
multiplicities. Every finite Banach exponent, including p=1, is covered.
The explicit period-one version uses the original period-one parameter
topology. The norm conversion is not claimed to be isometric.

Next: Section 4, beginning with the classical Dirichlet/Neumann domains
in equation (1.6) and their AKNS representation. The dissertation remains
incomplete; earlier source qualifications remain in force.

Validation: `./scripts/check.sh` passed: 6,745 build jobs, public examples, and the axiom audit of 29,480 NLS declarations. The build retains 21 existing warnings; the new modules and standalone public probe are warning-free. The source inventory check passed with 156 candidate labels (not a completeness certificate).

## Section 4 classical domains and AKNS conjugation

The beginning of Section 4 (printed pages 28–29) now has the original
classical AKNS domain and operator, with exact identifications of equation
(1.6), the component system (1.7), and the normalized coordinate matrix.
`AKNSCoordinates.lean` proves both matrix inverses, both boundary conditions,
and the derivative/potential intertwining for arbitrary complex coordinates.

`IntervalH1Linear.lean` supplies linear closure of the original interval H¹
class. `AKNSClassicalDomain.lean` proves equivalence of the original Sobolev
endpoint domains, actual derivative intertwining almost everywhere, and
equivalence of the physical eigenvalue equations. No regularity outside
[0,1] or endpoint periodicity is assumed.

`AKNSPhysicalNorms.lean` constructs `aknsL2Equiv` on the actual Lebesgue
component-sum L² space and proves exact preservation of the original H¹
norm. `AKNSIntervalOperator.lean` constructs the actual closed-interval AKNS
domain, characterizes membership by original H¹ functions and the printed
endpoint conditions, and identifies its norm with the physical H¹ norm.
The inclusion is injective and dense. Both inclusion and operator are
conjugated by the L² unitary and domain H¹ isometry. Their values are proved
to be the original function and actual AKNS differential expression almost
everywhere, for arbitrary L² potentials and either boundary condition.

The page 29 assertion phi = T(q,p) has a normalization error: the potential
map is (q+i*p,q-i*p) = sqrt(2) T(q,p), while T remains the normalized vector
matrix. This agrees with page 19. Lean proves the corrected relation and
counterexamples to the printed normalization, including the actual operator
on constant smooth data. The correction is confined to the potential map.

Next: the even/odd and signed-swap extensions and Lemma 4.1, auditing the
existing physical transfer against the original source spaces. The full
dissertation remains incomplete; all earlier qualifications remain in force.

Validation: `./scripts/check.sh` passed: 6,750 build jobs, public examples, and the axiom audit of 29,625 NLS declarations. The build retains 21 existing warnings; the five new modules and standalone public probe are warning-free. The source inventory check passed with 156 candidate labels (not a completeness certificate).
