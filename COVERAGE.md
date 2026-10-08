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
The following audits treat D.9 and E.1-E.2; later statements still require source-level comparison.

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
one at z=0 when the zero-index root is moved to i. E.2 is audited below;
E.3 remains to be source-audited.

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
the actual source spaces at p=1 and p=3. E.3 remains to be audited.
