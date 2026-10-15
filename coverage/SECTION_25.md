# Section 25: uniform localization for the original source

This audit covers printed pp. 108–112: Theorem 25.1, Lemmas 25.2–25.4,
Proposition 25.5, and formulas (5.7)–(5.8). The public API now states
these estimates for the original period-one source, retaining the exact
physical norm, signed indices, numerical constants, and multiplicities.

## Original coordinates and exact norms

[`NormalizedWeightedSourceRange.lean`](../NLS/ZakharovShabat/NormalizedWeightedSourceRange.lean)
proves that every even weighted potential has normalized source
coordinates with exactly the same component-sum norm. This covers the
entire weighted source space. `normalizedWeightedSource w a` decodes by
dividing the original coefficient at n by w(2n), and its period-one
operator parameter is exactly the weighted realization used in the
spectral proofs.

`normalizedWeightedSource_physical_norm` identifies ‖a‖² with the
literal sum of w(2n)² times both decoded component energies.
For a : SobolevSource 1, `sourcePiSobolevCoordinates_norm_sq` gives

    P² = ∑ n∈ℤ, (1+|2nπ|)² (|a⁻ₙ|²+|a⁺ₙ|²).

The localization uses this exact P. No equivalent norm or auxiliary
realization is left as a premise. The full complex H¹ source is allowed.
Period doubling transports the inclusive source cutoff |n|≥N to the
physical cutoff |k|≥2N; the tail norm identity also preserves its two
boundary frequencies.

## Localization, coefficients, and multiplicities

[`SourceSection25Localization.lean`](../NLS/ZakharovShabat/SourceSection25Localization.lean)
puts the canonical endpoints in the exact source discs when
8P²≤1+|n|. The radius is

    P²/(1+|n|) + √2 P/(1+|2n|) < π/5.

The remaining indexed endpoints lie in the printed central box,
|Re λ|≤(8P²−1/2)π and |Im λ|≤P. The entire original periodic spectrum
is covered. Zero and negative indices are included whenever their
threshold condition holds.

The determinant has the same two canonical roots throughout the closed
strip, counted with their original algebraic multiplicities. Its analytic
order at each strip point is the count in the multiset {λ⁻ₙ,λ⁺ₙ};
coincident endpoints therefore still contribute twice. The squared-gap
bound has the printed factor six.

[`SourceSection25Coefficients.lean`](../NLS/ZakharovShabat/SourceSection25Coefficients.lean)
uses the actual weighted inverse and resonant coefficient extensions.
The square estimate holds at every index and every closed-strip point.
At the exact quadratic threshold it gives a one-half contraction.
The coefficients are analytic near every point of that strip and jointly
analytic in the original normalized source and spectral parameter.
The diagonal bound has constant one and the off-diagonal remainders
have constant eight, with the corresponding individual component norm.
The negative resonant mode reads the original first component at −n;
the positive mode reads the second component at n.

| Source assertion | Public entry point | Exact scope |
| --- | --- | --- |
| Theorem 25.1 | `sourceH1_uniform_localization`, `sourceH1_spectrum_subset` | Every original complex H¹ source; exact P, quadratic threshold, signed endpoints, radius, and central box. |
| Lemma 25.2 | `sourceM1_square_bound` | Every M₁ weight, every normalized source, every index and closed-strip point; constant 4/(1+|n|). |
| Contraction after Lemma 25.2 | `sourceM1_square_contraction` | Norm at most 1/2, including equality at the threshold 8‖a‖²=1+|n|. |
| Formula (5.7) | `weightedResonantA_parity`, `weightedResonantA_parity_zero`, `weightedResonantBPlus_remainder`, `weightedResonantBMinus_remainder` | Both diagonal representations and both literal Fourier remainders of the actual inverse, whenever its square is contractive. The source threshold supplies that condition. |
| Lemma 25.3 | `sourceM1_coefficients`, `sourceM1_coefficients_joint_analytic` | Closed-strip and joint source analyticity, exact constants one/eight, literal leading coefficients and separate component norms. |
| Lemma 25.4 | `sourceH1_canonical_pair`, `sourceH1_uniform_localization` | Exact determinant roots and analytic orders on the whole strip, original periodic multiplicities, quantitative radius, and factor-six gap bound. |
| Proposition 25.5, tail | `sourceM1_gap_tail` | Every M₁ weight and complex weighted source; inclusive N, summability, exact constants 6 and 1152, original Fourier tail norm. |
| Proposition 25.5, global | `SourceSection25Data.gap_bound` | One open T containing every real source, T⊆U, chosen before all M₁ weights and sources; constant 265π² and w[16‖a‖²]²(1+‖a‖²)‖a‖². |
| Formula (5.8) | `sourceM1_gap_individual` | Every M₁ weight, including superlinear weights; exact √12 and the original source gap. |

The inverse and convergent coefficient series used in (5.7) are in
[`ResonantParityExpansion.lean`](../NLS/ZakharovShabat/ResonantParityExpansion.lean)
and [`ResonantCoefficientSeries.lean`](../NLS/ZakharovShabat/ResonantCoefficientSeries.lean).
Their analytic extensions agree with those coefficients on the open
correction domain by
[`ResonantAnalytic.lean`](../NLS/ZakharovShabat/ResonantAnalytic.lean).

## One common domain for the global estimate

[`SourceSection25Gaps.lean`](../NLS/ZakharovShabat/SourceSection25Gaps.lean)
retains the actual source gaps throughout the tail and individual bounds.
For the global bound it chooses

    T = U ∩ sourceSpectralStripNeighborhood.

This is an open neighborhood of the entire real source locus, independent
of the weight. The existing proof controls the horizontal packing of
central gaps and their imaginary heights, whose additional contribution
fits inside the printed constant 265π². It does not need a new assumption
about the sum of diameters of chosen isolating discs. The global estimate
is asserted on T; the localization and tail estimates need no such
neighborhood restriction.

[`SourceSection25Original.lean`](../NLS/ZakharovShabat/SourceSection25Original.lean)
packages this as `SourceSection25Data D A B U T`. It extends the same
Section 24 family and keeps its original domain U. The additional T is
chosen once, before all weights and potentials.
`SourceSection24Data.section25` augments any retained family, and
`sourceSection25_original` constructs the family and T unconditionally.

## Validation and next work

Twenty public checks cover non-Hilbert realization, exact physical norms,
both tail boundary frequencies, the cutoff N=0, zero and negative spectral
indices, equality at the contraction threshold, joint analyticity,
both diagonal formulas, coincident-root multiplicity, superlinear
weights, the full global bound, and the unconditional common-family
constructor. Full validation is recorded in [implementation status](../STATUS.md).

Next: the original Section 26 action estimates, including the printed
alternating sign in Lemma 26.2. The separate
[Section 14 qualifications](SECTION_14.md) remain. The dissertation is
incomplete.
