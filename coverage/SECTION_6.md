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

## Remaining source assertions

Continue with the midpoint and gap consequences and Proposition 6.3,
matching their exact source norms and weighted assumptions. The sharper
ceiling-cutoff version of the corrected Proposition 6.1 quantitative estimate
remains unproved. Existing later results and the candidate-label inventory
do not certify this section or the dissertation complete.
