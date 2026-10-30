# Section 16 original-Jacobian audit

## Intermediate gradients, own-index products and ordered comparison

Two new positive theorems prove the intermediate estimates in Lemma 16.2:
the x derivative differs from the normalized sum of the two eta derivatives
by an lp sequence, and the y derivative differs from their normalized
difference by an lp sequence. The results hold in the full source operator
norm and for physical Holder-conjugate gradients of actual sequence entries,
at every real spectral finite-gap source and every finite p>1.

The [ordered Section 16 ledger](SECTION_16_ASSERTIONS.md) records
all 27 passage groups: 20 matched and seven corrected. It retains
the positive quotient product, corrected y formula, negative y term in
Fourier reconstruction and the bounded inverse norm in the cutoff estimate.
No new proof refuting a printed formula is added.

Two further positive theorems establish the separate own-index product
asymptotics in S16-012, for the original root family varying with n.
They hold at every real source, without a finite-gap hypothesis. A shared
majorant is chosen before both indices; real Dirichlet interlacing permits
diagonal sampling, and the signed omitted product recovers the psi estimate.
The auxiliary's complex local uniformity and Banach analyticity retain
their separate proof on the original W.

This step freshly inspected 47 module bodies, reused three full readings
at identical hashes and resolved 84 declarations.

The fresh full check passed 8,559 build jobs, all 7,635 public examples and the transitive axiom audit of 44,604 NLS declarations. It reported 21 inherited warnings and no new warnings. Four new examples exercise the gradient and product estimates at p=3/2 and p=4, including ambient interval notation. Source hashes, declaration references, review integrity and documentation links are checked separately; those checks do not certify mathematical completeness.

Next is Section 17, Diffeomorphism property. The exact 2014 [23] comparison and wider
qualifications remain in the [completion assessment](COMPLETENESS.md).

Earlier entries retain their historical scope and validation.

Source: printed pp. 75–77, the Jacobian, Lemmas 16.1–16.3, and equations
(3.3)–(3.4). `sourceSection16_original` constructs one package for every
finite p>1. D below denotes `SourceSection16OriginalData`; H denotes
`D.toSourceSection15OriginalData`. The same normalized root family,
original angular domain W, and compatible Birkhoff domain V⊆W are retained.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Analytic operator-valued Jacobian | `D.jacobian_analytic` | Actual Fréchet derivative of the sequence-valued map, complex analytic on V |
| Physical gradient representation | `D.jacobian_gradients` | Gradients of actual sequence entries in the Holder-conjugate coefficient space; exact unconjugated Fourier pairing at every complex source in V |
| Free Jacobian and normalized identity | `D.jacobian_zero`, `D.complex.normalizedJacobian_zero` | Actual derivative at zero equals the explicitly invertible free Fourier map |
| Lemma 16.1 | `H.lemma16_1` | Both original gap-sequence gradient errors have Holder-conjugate norms in outer ℓᵖ at every real finite-gap source |
| Corrected auxiliary quotient | `H.auxiliary_eq_real_quotient`, `sourceGapWeightedEtaAuxiliary_eq_quotient` | Positive literal product divided by actual psi; all real sources unconditionally, arbitrary complex points whenever the psi numerator is nonzero |
| Analytic auxiliary extension | `H.auxiliary_analytic` | Minus the inverse of twice the omitted standard-root product, analytic on all original W |
| Signed auxiliary asymptotic | `H.previous.auxiliary_remainder_analytic`, `H.previous.auxiliary_error_local_bound` | The full sequence 2φₙ+cos(nπ) is Banach analytic into ℓᵖ on original complex W, with locally bounded norm |
| Auxiliary Cauchy bound | `H.previous.auxiliary_gradient_local_bound` | One original-source neighborhood bounds all actual auxiliary derivatives and physical conjugate gradients, uniformly in n |
| Equation (3.3) | `H.equation3_3` | Every real collapsed gap, all complex sign parameters; correct shared sign on both moving-terminal terms |
| Lemma 16.2 | `H.lemma16_2` | Actual x/y sequence-coordinate gradient errors in outer ℓᵖ, at every real finite-gap source |
| Inverse Fourier series | `sourceBirkhoffFourierInverse_hasSum` | Unconditional convergence in source norm, with the corrected negative y-gradient term |
| Equation (3.4) | `H.normalizedJacobian_hasSum`, `D.jacobian_gradients` | Exact normalized Jacobian series for every complex source in V and every input vector; physical gradient interpretation through the preceding pairing identity |
| Literal finite-rank cutoff | `sourceBirkhoffNormalizedJacobianCutoff_apply`, `sourceBirkhoffNormalizedJacobianCutoff_finiteDimensional` | Finite gradient-basis sum with the corrected sign, and a proved finite-dimensional range |
| Tail bound and operator-norm convergence | `sourceBirkhoffNormalizedJacobianCutoff_error_le`, `H.normalizedCutoff_tendsto`, `H.normalizedCutoff_symmetric_tendsto` | Constructed ℓᵖ row majorants at real finite-gap sources; arbitrary finite sets and the source cutoffs [−N,N] |
| Lemma 16.3 | `D.lemma16_3` | Real analytic normalized Jacobian, compact difference from identity at every real source, and equivalence of bounded-isomorphism assertions |

## Auxiliary quotient and the closed-gap formula

Write A for the deleted single spectral product and P for the omitted
standard-root product. The existing literal-product theorem
`hasProd_sourceSingleRootQuotient_subtype` identifies the product over m≠n
of (σₘ−λ)/wₘ(λ) with Q=A/P. The actual normalized numerator is ψₙ=−2A.
Consequently Q/ψₙ=−1/(2P) whenever ψₙ is nonzero.

The corrected auxiliary uses this last expression at the Dirichlet root.
The original annulus charts prove that P is analytic and nonzero there,
throughout W. At every real source the actual psi numerator is nonzero:
its retained roots lie in other, disjoint periodic gaps. Thus the literal
quotient and the analytic extension agree at all real sources. We do not
assert that the actual psi numerator is nonzero at every complex point
of W; identification there has an explicit nonzero hypothesis.

At a real collapsed gap the terminal anti-discriminant vanishes. The
term δ(μₙ)dφₙ in (3.3) therefore vanishes exactly. Differentiating the
moving terminal retains both the fixed-source anti-discriminant derivative
and its spectral derivative times dμₙ, under the same sign. This proves
(3.3) directly without needing an index-uniform derivative bound for φₙ.
The source's separate locally uniform auxiliary asymptotic and Cauchy
bound are now proved on the same original complex domain in the follow-up below.

## Reconstruction, norms, and compactness

The inverse of a pair of single modes a,b at index −n is
`a • sourceBirkhoffFreeXGradient p n - b • sourceBirkhoffFreeYGradient p n`.
Applying the bounded inverse Fourier map to the unconditional coordinate
series proves the infinite reconstruction and its normalized-Jacobian form.
The finite cutoffs use the same reconstruction of the two truncated output
components of the actual Jacobian remainder. Their ranges lie in the span
of finitely many reconstructed coordinate vectors.

The operator-norm error is bounded by

    ‖FourierInverse‖ * max(‖truncate S b₁ − b₁‖, ‖truncate S b₂ − b₂‖).

The majorants b₁,b₂ are constructed from the actual derivative errors at
finite-gap sources. Their tails tend to zero for finite p. The estimate
uses bounded maps between the ordinary product output norm and the genuine
p-norm on source pairs; it assumes no Fourier isometry for general p.
Compactness extends from finite-gap to all real sources using their proved
density in the source norm, continuity of the Jacobian, and closedness of
the compact operators. Analytic dependence alone is not the density argument.

## Source corrections with explicit witnesses

- The free inverse series and (3.4) on p. 77 require a negative y-gradient
  term. `sourceBirkhoffFreeYGradient_ne_fourierInverse_y_mode` proves the
  printed positive term differs from the actual inverse. The theorem
  `H.freeJacobian_y_mode` transfers the check to the original map at zero.
- The leading minus in the displayed ζₙ on p. 76 conflicts with the later
  free leading value. `H.printed_auxiliary_product_free` gives −1 at every
  free center; `H.printed_auxiliary_quotient_zero` gives +1/2 at the zero
  center. The positive literal product gives the corrected auxiliary above.
- In the second error formula in the proof of Lemma 16.2, the printed
  unscripted ∂zₙ should read ∂yₙ. The numbered lemma itself is unchanged.
- The coefficient-to-source norm equality used on p. 77 is not a general
  p-isometry identity. `sourceBirkhoffFreeXGradient_norm_fourth` proves
  ‖dₙ⁺‖⁴=1/2 at p=4, whereas its one nonzero reconstruction coefficient has
  fourth-power sum 1. This checks the norm convention; it does not claim
  that this particular vector is attained by a nonlinear Jacobian tail.
  The bounded reconstruction estimate suffices for compactness.

See [the discrepancy log](../SOURCE_ERRATA.md) for the source locations.
The printed grouping in (3.3) puts both anti-discriminant terms under the
same ± sign; no discrepancy is claimed for that grouping.

## Retained results and validation

The package extends Section 15 without replacing the root family or the
map. It retains the full complex exponent compatibility from Section 14,
all canonical brackets, real local inverses, and the global inverse for
1<p≤2. Native weighted analyticity and the analytic inverse at every
nonnegative real Sobolev order are now proved in
[Section 14](SECTION_14.md). Its precise 2014 construction comparison
remains unverified. No surjectivity for p>2 is asserted.

Seven new modules and 23 new public examples cover the original derivatives,
physical gradients, quotient identification, equation (3.3), corrected
series, finite-rank estimates, all-real compactness, and the explicit free
witnesses. Independent packages at p=3/2 and p=4 are constructed and compared
on their full complex intersection. Full validation is recorded in
[the implementation status](../STATUS.md).

The detailed inverse and flow arguments for this same original family
are audited in [Section 17](SECTION_17.md).

## Locally uniform auxiliary asymptotics and the Cauchy bound, printed p. 76

The separate auxiliary estimate used in the proof of Lemma 16.1 is now
proved throughout the unchanged original complex angular domain W, at
every finite p>1. Write P_n for the omitted standard-root product sampled
at the actual Dirichlet root. The corrected auxiliary remains
phi_n = -1/(2 P_n), with the positive quotient-product convention recorded
above. No further domain restriction or Sobolev hypothesis is imposed.

[SourceDirichletOmittedSquareAnalytic.lean](../NLS/ZakharovShabat/SourceDirichletOmittedSquareAnalytic.lean)
first proves that the complete sequence P_n^2-1 is Banach analytic into
lp. Its local norm bound retains the finite head and uses the original
Dirichlet displacement and deleted-product estimates for the tail.

Controlling squares alone would not fix the signs of the roots.
[NormalizedRootBranchPropagation.lean](../NLS/SequenceSpaces/NormalizedRootBranchPropagation.lean)
proves that a normalized lp root branch propagates from one base point
across an open preconnected domain when the squared error is continuous
in lp. It also proves local norm bounds and Banach analyticity of that
normalized root error. The
[original-domain application](../NLS/ZakharovShabat/SourceDirichletOmittedNormalizedAnalytic.lean)
uses (-1)^|n| P_n, fixes its branch at the real zero source, and obtains
preconnectedness from the retained root atlas itself. It does not add a
connectedness assumption to the source package.

[NormalizedInverseAnalytic.lean](../NLS/SequenceSpaces/NormalizedInverseAnalytic.lean)
then preserves lp normalization under coordinatewise inversion. The
actual omitted products are nonzero everywhere on W. Uniformly small
tails control their inverses locally; continuity bounds the finite head.
A global lower bound on all denominators is unnecessary.

[SourceAuxiliaryUniformAsymptotics.lean](../NLS/ZakharovShabat/SourceAuxiliaryUniformAsymptotics.lean)
identifies every coefficient of `sourceGapWeightedEtaAuxiliaryRemainder`
with the literal error 2 phi_n + cos(pi n). This full lp-valued map is
Banach analytic on W. Its norm is bounded on one original-source
neighborhood of each point. The results apply to complex sources,
central and negative indices, and both open and collapsed gaps.

[SourceAuxiliaryUniformGradient.lean](../NLS/ZakharovShabat/SourceAuxiliaryUniformGradient.lean)
applies Cauchy's estimate on nested original-source balls. One
neighborhood and one constant bound all actual Frechet derivatives,
uniformly over the signed spectral index. The physical conjugate
Fourier gradients have a simultaneous bound in the original conjugate
pair norm. A `HasFDerivAt` statement and the exact reversed-frequency
pairing identify these gradients with the full actual differentials.
These results prove the separate O(1) assertion used on p. 76.

The five public examples construct an original domain at p=4, check
p=3/2 with physical l3 gradients, recover actual Hilbert differentials,
and derive uniform coordinate-tail decay and a bound on the literal
fourth-power sum. The previous proof of (3.3), the corrected positive
product convention, and all existing original-family results remain in
place. The precise 2014 construction comparison is still unverified.

## Uniform derivative bounds and finite-gap beta decay, printed pp. 76–77

The separate Cauchy estimates used in the proof of Lemma 16.2 are now
explicit in [SourceSection16UniformDerivatives.lean](../NLS/ZakharovShabat/SourceSection16UniformDerivatives.lean).
For the actual normalized action root, beta correction and gap-weighted
eta coordinates, one complex source neighborhood and constant bound
every full Frechet derivative, uniformly over all signed indices.
The same neighborhood bounds the physical Holder-conjugate gradients
in the full pair norm. The estimates hold for every finite p>1.

The root estimate is near each real-type source. The beta and eta
estimates hold at every point of their original complex domains, and
for each fixed eta parameter in the closed unit disk (in particular either
sign), the neighborhood and constant precede all signed indices.
Nested-ball Cauchy estimates are applied to the actual local scalar bounds; no uniform bound over an
arbitrary source norm ball is asserted. All central indices are retained.

[SourceFiniteGapBetaDecay.lean](../NLS/ZakharovShabat/SourceFiniteGapBetaDecay.lean)
proves the printed beta_n=O(1/n) directly at every real spectral finite-gap
source, for every finite p>1. Outside one symmetric cutoff, the actual
beta correction has norm at most K/abs(n). The constant and cutoff precede
both positive and negative indices. The proof uses the finite set of
open gaps and the original reciprocal estimate for the actual beta
terms. It assumes neither finite Fourier support nor an H1 representative.

The existing proof of Lemma 16.2 also uses the exact vanishing of the
gap-weighted coordinate at a real collapsed gap: its product rule removes
the normalization and beta derivative terms there. The new separate
bounds verify the additional estimates in the source proof narrative.
The documented Section16 sign corrections and exact2014/G2 qualifications
remain unchanged; the remaining semantic source audit is still in progress.
