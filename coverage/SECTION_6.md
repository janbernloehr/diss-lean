# Section 6: asymptotic behavior of the eigenvalues

This audit starts with Proposition 6.1 on printed page 35. Its source domain
is the full period-two coefficient space, with the original component-sum
norm. The existing period-one embeddings do not by themselves establish this
statement for arbitrary period-two input.

## Proposition 6.1: original norm and actual spectrum

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Coefficient-preserving unit weighting | `unitWeightedPairEquiv_fst`, `unitWeightedPairEquiv_snd` | Every integer frequency, both original components; the existing map is a linear isometry. |
| Same periodic operator input | `weightedBaseToPair_unitWeightedPairEquiv` | Equals `CoeffPair.toMax p φ`; no frequency doubling. |
| Same Fourier tail | `weightedPairFourierTail_unitWeightedPairEquiv` | Same cutoff, retaining its boundary frequencies, with exact norm equality. |
| Actual original spectrum | `sourcePeriodTwoSpectrum_iff` | Noninvertibility of `sourceSpectralPencil`, equivalently complement of `sourceResolventSet`. |
| Corrected quantitative bound | `exists_uniform_sourcePeriodTwoDisplacement` | Every finite p>1; one open convex neighborhood containing the input and zero; all larger cutoffs. |
| Multiplicities and complete distant strips | `PeriodicResonantPair`, together with `sourcePeriodTwoSpectrum_iff` | The two selected values exhaust each sufficiently distant strip; repetitions record algebraic multiplicity. |
| Locally small corrected budget | `exists_uniform_small_sourcePeriodTwoDisplacementBudget` | The neighborhood and cutoff may depend on the positive tolerance. |
| Qualitative ℓᵖ asymptotics | `sourceProposition6_1_asymptotics` | Actual high pairs, ℓᵖ displacement sequences, convergent full signed tails, and locally uniform small power sums. |

The new entry points are in `SourcePeriodTwoDisplacement` and
`SourcePeriodTwoAsymptotics`. Their quantitative input is the existing proved
weighted periodic-pair theorem. They identify its coefficients, exact norms,
and spectral pencil with those of the original period-two input.

Write B=‖φ‖, T=‖R_floor(N/2) φ‖, and δ=min(1,p−1). The proved bound is

```
C_p [ T^p + (B^p/N^δ + T^p)(1+B^p)B^p ].
```

`C_p = rootDisplacementSummationConstant p` depends only on p. In Lean,
`N/2` is natural-number division. This cutoff convention is explicit: a
sharper corrected formula using ceiling(N/2) is not established here.
The tails sum both root displacements over all integer indices with |n|≥N.

The qualitative theorem selects actual pairs at sufficiently distant
indices. Its finitely many remaining entries are unspecified. Their values
do not affect ℓᵖ membership; the theorem does not assert a new global central
labeling or continuity of individual eigenvalue labels.

## Proposition 6.1: refutation of the printed quantitative bound

The formula on printed page 35 and the corresponding Lemma 6.9 display on
page 43 omit the additive leading-tail term. Their overall potential-norm
factor makes the printed p=2 budget quartic at zero, whereas a single
resonant input has quadratic displacement energy.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Literal Hilbert budget | `sourcePrintedHilbertDisplacementBudget` | Original pair norm and ceiling(N/2) tail. |
| Rounding-independent comparison | `sourcePrintedHilbertDisplacementBudget_le` | Ceiling budget is no larger than the existing floor-cutoff budget for every nonnegative constant. |
| Actual weighted periodic witness | `exists_periodicRoot_exceeding_printed_budget` | Upgrades the earlier reduced determinant witness to actual periodic spectral membership. |
| Actual original-pencil witness | `exists_sourcePeriodTwoRoot_exceeding_printed_budget` | Every open neighborhood of zero, every proposed uniform cutoff, and every nonnegative constant. |
| Refuted single-root consequence | `not_exists_locally_uniform_sourcePrintedDisplacementBudget` | No locally uniform printed estimate at zero. |
| A root is controlled by its pair tail | `sourcePeriodTwoRoot_sq_le_pair_tail` | Uses summability and nonnegativity; no assumption that the two labels are distinct. |
| Refuted pair-sum assertion | `not_sourceProposition6_1_printed_pair_sum` | Rules out any choice of labels exhausting the actual distant disk spectra and satisfying the printed sum bound. |

These statements are in `SourcePeriodTwoDisplacementCounterexample`.
The construction inherited from `RootDisplacementSourceAudit` places small
single coefficients at the two resonant frequencies. Its roots are nπ±t,
its squared original norm is 2t², and its printed budget is at most 24C t⁴.
The resonance can be chosen beyond any proposed uniform cutoff.

This refutes the source's **locally uniform quantitative** claim at zero.
It does not refute the qualitative ℓᵖ assertion, nor does it assert that a
separate cutoff chosen individually for each fixed input must fail. The
counterexample covers both natural rounding conventions at N/2.

## Corollary 6.2: arbitrary period-two input

The paragraph preceding the corollary discusses one-periodic input, but the
corollary itself states the period-two space. This scope is now realized
constructively by bounded restriction to [0,1] and re-expansion with unit
frequencies. No typo or change of the displayed input space is needed.
Merely keeping the even input coefficients would discard physical odd modes.

For raw period-two coefficients a, the unit-period sequence is

```
b_n = a_(2n) + i H(oddSamples(a))_(n−1),
```

where H is the established shifted discrete Hilbert transform. On one odd
input mode at 2k+1 with amplitude c, the output is
`c · 2i / (π(2k−2n+1))`. In particular, input mode 1 has nonzero output
`2i/π` at unit frequency zero. The public checks cover this value and its
nonvanishing at p=3. The map recovers embedded period-one input exactly.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Bounded scalar restriction | `periodTwoToUnit`, `norm_periodTwoToUnit_le` | Every 1<p<∞; even samples plus odd shifted Hilbert transform. |
| Exact finite physical coefficients | `periodTwoToUnit_finite_integral` | Every finitely supported period-two Fourier polynomial; both frequency signs and parities. |
| Arbitrary physical L² restriction | `periodTwoToUnit_two_ofFunction`, `periodTwoToUnit_two_reconstruct` | Actual unit-interval coefficients and almost-everywhere reconstruction, without period-one or endpoint-matching assumptions. |
| Original pair norm and phase | `norm_sourcePeriodTwoRestriction_le`, `sourcePeriodTwoRestriction_sourcePhase` | Same scalar bound in the source component-sum norm; commutes with the auxiliary potential phase. |
| Physical pair reflection | `sourcePeriodTwoRestriction_ofFunction`, `sourcePeriodTwoRestriction_reflection` | Restriction then completed extension equals literal physical reflection for arbitrary L² pairs. |
| Actual full boundary spectra | `sourcePeriodTwoBoundaryRoots_exhaustive`, `sourcePeriodTwoAuxiliaryRoots_exhaustive` | Both ordinary and both auxiliary spectra after restriction and their respective reflections. |
| Full Jordan multiplicities | `sourcePeriodTwoBoundaryRoots_multiplicity`, `sourcePeriodTwoAuxiliaryRoots_multiplicity` | Repeated canonical labels count actual original-domain full root-space dimensions. |
| Locally uniform full power sums | `sourceCorollary6_2` | One open convex neighborhood containing the input and zero; one positive bound for all four complete displacement power sums. |
| Full ℓᵖ membership | `sourceCorollary6_2_mem` | All integer indices, including central labels, for every finite p>1. |

The physical integral identification is proved for finite inputs at every
1<p<∞ and arbitrary L² input. On general ℓᵖ input, the bounded coefficient
map defines the completion; no pointwise representative of a general
Fourier–Lebesgue distribution is assumed. This step does not assert
continuity of individual canonical eigenvalue labels.

## Midpoint and gap consequences on page 35

`SourcePeriodTwoMidpointGap` works on the original raw period-two input.
It does not use `periodOnePotential`, which would double the input frequencies.
For every 1<p<∞, the actual distant counted pairs give
`(ξ_n+η_n)/2 − nπ ∈ ℓᵖ` and `ξ_n−η_n ∈ ℓᵖ` on one open convex
neighborhood containing the input and zero. The finitely many unspecified
entries of those selected sequences do not affect membership.

The contour midpoint and squared gap agree with these pairs at high indices.
`exists_uniform_small_sourcePeriodTwoMidpointGapTail` proves arbitrarily small
full signed tails of the sum of midpoint-displacement p-powers and squared-gap
p/2-powers, locally uniformly. `sourcePeriodTwoMidpointGap_summable` proves
both complete power sums converge; `sourcePeriodTwoMidpoint_mem` gives the
midpoint's actual ℓᵖ membership. This does not assign individual central pairs
to the fixed low-index contours or assert continuity of eigenvalue labels.

## Proposition 6.3: exact weighted input and corrected bound

The displayed source weight assumptions are exactly those of `SpectralWeight`:
`w_n≥1`, symmetry, submultiplicativity, and monotonicity on nonnegative indices.
They do not require the extra normalization `w_0=1`. The public checks use
`WeightedCoeffPair.norm_rpow_eq_tsum` to verify the printed component-sum norm.
`sourceWeightedPeriodTwoInput` forgets the weight while retaining both raw
Fourier components at every integer frequency, without period doubling.
`sourceWeightedPeriodTwoSpectrum_iff` identifies the actual source pencil's
noninvertibility with the existing weighted spectral realization.

Write B=‖φ‖_(w,p), T=‖R_floor(N/2) φ‖_(w,p), and δ=min(1,p−1).
The corrected estimate in `sourceProposition6_3_corrected` is

```
Σ_(|n|≥N) w_(2n)^p |γ_n|^p
  ≤ C_p [ T^p + D_p B^p (B^(2p)/N^δ + T^(2p)) ].
```

Here `C_p=rootGapSummationConstant p` and
`D_p=offDiagonalSummationConstant p` depend only on p. The theorem uses the
actual contour squared gap through `‖γ_n²‖^(p/2)=|γ_n|^p`. It supplies actual
counted spectral pairs, their source spectral equivalence, and the sum bound
on one open convex neighborhood for every larger cutoff.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Small corrected budget | `exists_uniform_small_rootGapBudget` | Every source weight and 1<p<∞; one neighborhood and cutoff for each positive tolerance. |
| Small actual weighted gap tails | `sourceProposition6_3_small_tails` | All signed indices beyond every larger cutoff; actual intrinsic squared gap. |
| Full weighted gap-power convergence | `sourceProposition6_3_summable` | Includes the finitely many central contour values. |
| Weighted ℓᵖ gap membership | `sourceProposition6_3_gap_mem` | Any choice of square roots of the intrinsic squared gaps, weighted at 2n. |

## Proposition 6.3: printed quantitative estimate is false locally at zero

The printed page-36 p=2 estimate with unit weight has the same quartic budget
as the earlier root-displacement display. `SourceWeightedGapCounterexample`
now proves the failure for the actual gap, rather than inferring it from a
single displaced root. In every open weighted-input neighborhood of zero and
beyond every proposed cutoff, the two finite resonant modes produce actual
roots `nπ±t`. The full counted pair and spectral equivalence identify the
intrinsic squared gap with `4t²`. The printed budget is at most `24C t⁴`.

`exists_periodicGap_exceeding_printed_budget` exceeds the floor-cutoff budget.
`sourcePrintedHilbertGapBudget` records the ceiling-cutoff version for general
weights, and `exists_periodicGap_exceeding_printed_ceiling_budget` exceeds that
smaller budget too. The final negations
`not_sourceProposition6_3_printed_gap_sum` and
`not_sourceProposition6_3_printed_pair_sum` exclude the printed locally uniform
claim for both the intrinsic gap and any actual counted pair labels, already
at unit weight and p=2. Thus the assertion for all source weights is false.

This is a failure of the uniform cutoff on neighborhoods of zero. It does not
claim that every separately chosen cutoff for a fixed potential fails. The
qualitative weighted ℓᵖ asymptotics and the corrected budget remain proved.

## Equation (1.13), the P/Q equations, and the original derivative domain

`SourceWeightedPencil` adds the derivative-domain counterpart of the existing
coefficient-preserving weighted source inclusion. The two maps are injective,
and including the derivative domain into the base commutes with forgetting
the weight. The exact identity `sourceWeightedPencil_eq` identifies the original
source pencil with `weightedFreePencil − weightedDomainPotential`.
`sourceWeightedDomainPotential_eq` identifies the weighted potential with the
original operator at φ minus the original operator at zero. Thus the projected
equations concern the actual original operator on the weighted derivative
domain, rather than a separately stipulated coefficient equation.

`SourcePQSplitting` proves unique decomposition into the two raw resonant
amplitudes and a complementary vector. The synthesis uses physical frequencies
−n in the first component and n in the second. The theorem applies to every
positive weight, including the one-derivative weight, and every finite Banach
exponent. It realizes the direct decomposition in (1.13) on both domains.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original and weighted pencil equality | `sourceWeightedPencil_eq`, `sourceWeightedPencil_zero_iff` | Every weighted domain vector; exact source base/domain conventions. |
| Original eigenvalue equation | `sourceWeighted_eigenvalue_iff` | `sourceOperator f = λ • sourceDomainInclusion f` iff the actual weighted free/potential equation. |
| Unique resonant/complementary decomposition | `exists_unique_sourcePQDecomposition` | Exactly two resonant amplitudes and one complementary remainder; both base and derivative weights. |
| The projected equations | `sourceWeightedPencil_zero_iff_PQ`, `sourceWeightedPencil_add_zero_iff_PQ` | Equivalent to the original pencil at every frequency; no smallness assumption. |
| Actual complementary inverse | `sourceComplementaryFreeInverse_equation`, `sourceComplementaryFreeInverse_unique` | Solves the original zero-potential source equation with Q_n right-hand side, uniquely on the complementary weighted domain. |
| Removed resonant modes | `sourceComplementaryFreeInverse_resonant`, `sourceLemma6_4_resonant_zero` | Both modes vanish under the complementary inverse and its potential composition, also at λ=nπ. |

## Lemma 6.4: exact shifts, operator, and endpoints

For physical coefficients f₋ and f₊, the exact source norm is

```
‖f‖_(w,p;i)^p = Σ_k w_(k+i)^p (|f₋(-k)|^p + |f₊(k)|^p).
```

`sourceShiftedNorm_formula` proves this identity. The first component has the
opposite physical modulation, as required by the signed Fourier convention.
`sourceLemma6_4_operator` identifies the bounded weighted map T_n with the
actual potential part of the original operator applied to A_λ⁻¹ Q_n in the
weighted derivative domain.

`sourceLemma6_4` proves the unchanged displayed estimate

```
‖T_n f‖_(w,p;i) ≤ c_p ‖φ‖_(w,p) ‖f‖_(w,p;−i)
```

for every 1≤p<∞. The constant depends only on p; there is no weight-, shift-,
or strip-index-dependent factor. The parameter may lie anywhere in the entire
closed strip U_n, including λ=nπ. `sourceLemma6_4_two` retains the printed
constant two. `sourceLemma6_4_one` proves that the endpoint admits constant one,
using reciprocal-symbol contraction and the exact component-sum norm. This
is a sufficient constant, not a claim of optimality.

The focused public checks cover the original eigenvalue/PQ equivalences,
complementary inverse equation and uniqueness, raw domain coefficients,
shifted coefficient formula, both endpoints, and the resonant free center.
The p=1 check with constant weight two also verifies that no extra w_0=1
hypothesis was introduced. No correction to Lemma 6.4 is required.

## Lemma 6.5: the exact induced norm and common contraction threshold

`sourceSquareNorm_le_iff` characterizes the norm of the conjugated square
by its bound on every input measured in the source's n-shifted pair norm.
`sourceLemma6_5` proves the displayed estimate

```
‖T_n²‖_(w,p;n) ≤ C_p ‖φ‖_(w,p)
  [ ‖φ‖_(w,p)/(1+|n|)^(1/p) + ‖R_n φ‖_(w,p)/w_n ].
```

The range is every 1≤p<∞. The tail retains |k|≥|n|, including equality;
there is no half-cutoff in this lemma. The estimate applies to every signed
n and the entire closed U_n, including λ=nπ, for the original source weight
class. It requires no w_0=1 normalization. No source correction is needed.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Exact induced shifted norm | `sourceSquareNorm_le_iff` | Equivalent to the input-wise estimate for every nonnegative proposed bound. |
| Original unweighted operator | `sourcePotentialInverse_operator` | Exactly the actual source potential part applied to the complementary domain inverse, for arbitrary original input. |
| Constant-free norm identification | `sourceSquareNorm_one`, `sourcePotentialInverse_square_norm` | Unit shifts and unit weighting preserve the squared operator norm. |
| Same weighted and original operator | `sourcePotentialInverse_weightedInput` | Every weighted input, preserving all raw coefficients. |
| Common local half-contraction | `sourceLemma6_5_uniform_half` | One open convex neighborhood containing φ and zero, one positive cutoff, both norms, all sufficiently large signed n and all of U_n. |

## Following paragraph: compatible squared Neumann inverses

`sourceComplementaryCorrection` constructs (Id−T_n)⁻¹ on the original
unweighted pair space from smallness of its square. The formula theorem
identifies (Id+T_n)(Id−T_n²)⁻¹; the even inverse has a proved convergent
operator-norm series. The left and right inverse identities and uniqueness
hold for every right-hand side. `sourceComplementaryCorrection_weightedInput`
shows that the weighted inverse restricts to the same original solution.
`exists_uniform_sourceComplementaryCorrection` constructs both compatible
bounded inverses on one neighborhood and every sufficiently distant closed
strip. It does not assume that the norm of T_n itself is less than one.

The public API checks include p=1, constant weight two, index −3 and its
free center, exact boundary retention in both Fourier components, and
weighted/unweighted compatibility. The actual Q-solution and resonant
determinant reduction are the next source-level audit step.

## Q-equation: actual original-domain solution and uniqueness

`sourceUnitDomainEquiv` is a coefficient-preserving continuous linear
equivalence onto the entire original derivative domain. Thus the source
Q-solution covers every original-domain input, not merely a specified range.
The base and domain complementary projections commute with the coefficient
inclusions. `sourceQEquation_iff` identifies the actual original equation
with the weighted equation.

`sourceQSolution` constructs v=A_λ⁻¹ Q_n T̂_n Φu in the original derivative
domain. It belongs to Q_n, satisfies A_λ v=Q_n Φ(u+v), and is the unique
complementary solution for every u. `sourceQSolution_potential` proves
Φv=T̂_n T_n Φu with the actual original-source operators. Its weighted and
original small-square assumptions are equivalent by
`sourcePotentialInverse_square_norm`; no new smallness restriction is added.

## Lemma 6.6: actual determinant and eigenfunction reconstruction

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual two-mode matrix | `sourceResonantMatrix` | Matrix of the corrected resonant map in the physical first-component −n and second-component n basis. |
| Full domain reconstruction | `sourceResonantReconstruction`, `sourceResonantReconstruction_eq` | Resonant domain lift plus the actual unique Q-solution. |
| Original amplitudes retained | `sourceResonantReconstruction_coordinates` | Its first coefficient at −n and second coefficient at n are exactly the specified amplitudes. |
| Full differential residual | `sourceResonantReconstruction_residual` | The actual source pencil applied to reconstruction equals the synthesized matrix residual, with matching sign. |
| Exact kernel correspondence | `sourceResonantReconstruction_kernel_iff`, `sourceResonantReconstruction_ne_zero_iff` | Exactly matrix-kernel vectors reconstruct pencil-kernel vectors; nonzeroness is preserved. |
| Converse reconstruction | `sourceResonantReconstruction_of_eigenvector` | Every original-domain eigenvector is recovered from its own resonant coefficients. |
| Actual spectrum | `sourceLemma6_6` | Original source spectral-pencil noninvertibility iff the matrix determinant is zero. |
| Full-domain eigenvectors | `sourceLemma6_6_eigenvector` | Nonzero original derivative-domain pencil kernel iff determinant zero. |
| Local uniform threshold | `sourceLemma6_6_uniform` | One open convex neighborhood containing φ and zero, one positive cutoff, all sufficiently large signed n and the entire closed U_n. |

Every statement allows 1≤p<∞. The strip includes the free center λ=nπ;
no puncture, p>1 hypothesis, or max-norm threshold loss is introduced.
The public free-potential check derives spectral membership at every lattice
center, including n=0 and negative n, at p=1 directly from the matrix criterion.
The high-frequency uniform statement itself retains the source's N≥1.
No source correction is required for Lemma 6.6.

## Resonant matrix coefficients and the printed basis order

The source prints the basis in (plus, minus) order; the library uses the
physical first-component −n and second-component n modes in (minus, plus)
order. `sourceCorrectionMatrix_entry` identifies the entries with actual
original-source corrected potential coefficients, evaluated on actual
resonant domain vectors. The common diagonal is `sourceResonantA`;
`sourceResonantBPlus` and `sourceResonantBMinus` are the physical-order
entries (1,0) and (0,1).

`sourcePrintedResonantMatrix_form` restores the printed order:

```
S_n = [[ λ−nπ−a_n, −b_n⁺ ], [ −b_n⁻, λ−nπ−a_n ]].
```

Reversing both rows and columns preserves the determinant.
`sourceSpectrum_iff_resonantScalarEquation` identifies the actual original
periodic spectrum with (λ−nπ−a_n)²=b_n⁺b_n⁻.

## Lemma 6.7: valid symmetries and the missing hypothesis

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Equal correction diagonals | `sourceLemma6_7_i` | Every complex potential; no reality hypothesis. |
| Original physical star | `sourcePotentialStar_fst`, `sourcePotentialStar_snd` | Component exchange, complex conjugation, and reversal k↦−k. |
| Exact reality condition | `sourceHasRealitySign_iff`, `sourceHasRealitySign_one_iff` | Original φ*=εφ matches the weighted condition; ε=1 matches the existing real-type predicate. |
| Corrected conjugation identities | `sourceLemma6_7_ii` | Under ε²=1 and φ*=εφ, both a_n and b_n⁺ obey their printed conjugation formulas. |
| Real diagonal on the real axis | `sourceResonantA_im_eq_zero` | Both real and imaginary type. |
| Local uniformity | `sourceLemma6_7_uniform` | One open convex neighborhood containing φ and zero, one positive cutoff, both conjugate parameters, the full closed strips, and all 1≤p<∞. |
| Constant-potential calculation | `sourceResonantA_constant_center` | Actual original coefficient ab/(2πn) at every nonzero center under the small-square condition. |
| Arbitrarily distant counterexample | `exists_large_nonreal_sourceResonantA` | Same fixed original potential (1,i), positive n beyond every proposed cutoff, squared norm ≤1/2, nonreal diagonal. |
| Printed claim refuted | `not_sourceLemma6_7_printed_diagonal` | No individual frequency cutoff makes unconditional diagonal reality true for that fixed potential. |

The displayed Lemma 6.7(ii) on printed page 40 states diagonal reality before
introducing φ*=±φ for the off-diagonal claim. Its proof starts with that
hypothesis and uses it for both conclusions. The counterexample verifies
that the unrestricted diagonal clause is false. The corrected sufficient
hypothesis is exactly the one used in the source's proof; no characterization
of all potentials with real diagonal is claimed. See `SOURCE_ERRATA.md`.

## Equations (1.14)–(1.15): original parity expansions

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original operator powers | `sourcePotentialInverse_pow_unitInput` | Every natural power agrees under the coefficient-preserving unit-weight inclusion. |
| Actual potential input | `sourceResonantPotentialVector_eq` | Difference of the actual source operator at φ and zero, applied to the original resonant domain vector. |
| Even Neumann vector | `sourceResonantEvenVector_hasSum` | Convergence of actual original even powers under the small-square hypothesis. |
| Diagonal formula | `sourceEquation1_14` | Original T applied to the even vector, evaluated in the second component at n. |
| Off-diagonal formulas | `sourceEquation1_15_plus`, `sourceEquation1_15_minus` | Original T² applied to the even vectors; leading physical coefficients φ.snd(2n), φ.fst(−2n). |
| Convergent coefficient series | `sourceResonantA_hasSum`, `sourceResonantBPlus_remainder_hasSum`, `sourceResonantBMinus_remainder_hasSum` | Odd diagonal series and strictly positive even remainder series. |
| Vanishing discarded terms | `sourceResonantA_even_term_zero`, `sourceResonantBPlus_odd_term_zero`, `sourceResonantBMinus_odd_term_zero` | No small-square assumption is needed for the individual cancellations. |

## Lemma 6.8: original joint analytic functions

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual coefficient agreement | `sourceResonantFunctions_eq` | Total extensions recover all three original coefficients on the small-square domain. |
| Joint analyticity | `analyticAt_sourceCorrectionEntryFunction` | Analytic in the original potential and spectral parameter together. |
| Uniform full-strip analyticity | `sourceLemma6_8_analytic` | One open convex neighborhood containing φ and zero, N≥1, every signed index with |n|≥N, entire closed strips, and actual coefficient agreement. |
| Weight compatibility | `sourceCorrectionEntryFunction_weightedInput` | Exact entry equality with arbitrary spectral weights on the common correction domain. |
| Uniform weight compatibility | `exists_uniform_sourceResonantFunctions_weightedInput` | All three coefficient functions agree on every distant closed strip on one weighted neighborhood. |

These analytic and parity statements hold for all 1≤p<∞, including p=1.
They make no global analyticity claim for the total extensions outside the
correction domain. The public checks also recover the actual original scalar
spectral equation using the analytic functions and check both signed Fourier
remainders under weighted inclusion.

## Lemma 6.8: quantitative original full-strip tails

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual original suprema | `sourceResonantDiagonalSup`, `sourceResonantBMinusSup`, `sourceResonantBPlusSup` | Full closed strips; weighted off-diagonal remainders retain physical frequencies −2n and 2n. |
| Exact weighted agreement | `sourceResonantSup_eq_weighted`, `exists_uniform_sourceResonantSup_eq` | Equality of full strip images; no majorant substituted for the supremum. |
| Boundedness and domination | `exists_uniform_sourceCoefficientStripBounds` | All three images bounded above, suprema nonnegative, and every actual strip value dominated by its supremum. |
| Exact diagonal budget | `sourceDiagonalTailBudget_weightedInput` | Original unweighted component-sum norm and original Fourier tail, with no comparison constant. |
| Exact unit-weight budgets | `sourceOffDiagonalTailBudget_unit`, `sourceUnitWeighted_component_norms` | Both pair and distinguished component norms are the original norms. |
| All three signed tails | `sourceLemma6_8_summability` | Summable p-power tails with explicit diagonal and off-diagonal budgets, for every larger cutoff. |
| Common neighborhood | `sourceLemma6_8_quantitative` | Bounded-image assertions and all tail estimates on one open convex neighborhood containing φ and zero, N₀≥2. |
| Original unweighted neighborhood | `sourceLemma6_8_unweighted` | Neighborhood in the original `CoeffPair p` space, preserving the full period-two input. |

For the diagonal let B=‖φ‖_p and T=‖R_floor(N/2) φ‖_p. Its budget is

```
C_p B^p (B^p/N^δ + T^p),     δ=min(1,p−1).
```

For each weighted off-diagonal remainder, let W=‖φ‖_{w,p},
T_w=‖R_floor(N/2) φ‖_{w,p}, and B_±=‖φ_±‖_{w,p}. Its budget is

```
D_p B_±^p (W^(2p)/N^δ + T_w^(2p)).
```

The left-hand sides sum the p-th powers of the actual suprema over all
integer n with |n|≥N. The off-diagonal supremum already includes w(2n),
so the weight is raised to p along with the remainder norm. The proof uses
strict 1<p<∞, not the analytic endpoint p=1. The floor-half cutoff includes
its boundary; no sharper ceiling-half result is claimed.

The page-41 printed off-diagonal display has neither these left-hand powers
nor the same inner norm. The formal result follows the p-power and full-pair
form of the concluding source proof. The literal display is not yet formally
refuted; see `SOURCE_ERRATA.md` for the precise distinction.

## Remaining source assertions

Continue with the formal audit of the literal Lemma 6.8(ii) display, including
its omitted powers and positive-component norm factor. Sharper ceiling-cutoff
versions of the corrected Propositions 6.1/6.3 estimates remain unproved.
Existing later results and the candidate-label inventory do not certify this
section or the dissertation complete.
