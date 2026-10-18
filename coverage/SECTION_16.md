# Section 16 original-Jacobian audit

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
| Signed auxiliary asymptotic | `memlp_sourceGapWeightedEtaAuxiliary_sub_free` | The sequence 2φₙ+cos(nπ) belongs to ℓᵖ at every real source |
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
bound are not independently asserted by this audit.

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
