# Section 6: ordered assertion ledger

This ledger follows the 47 passage groups located in the cached extraction of
[the dissertation](https://janbernloehr.de/Download/fs16/diss.pdf). It is a
navigation inventory with a partial assertion-level review, not a completion
percentage. A **pending** row can already have proved results in earlier
reviews; its whole passage has not yet been reconciled in this ledger.

The current review covers S6-024 through S6-032 (printed pp.39–41).
**Matched** records the mathematical assertions and their exact scope.
**Corrected** retains a refuted printed claim alongside its valid replacement.
**Interpreted** makes an operator-domain interpretation explicit rather than
claiming a literal formalization of the source's adjoint notation.

The extraction positions are newline-based and tied to SHA-256
`64640083a811e0e05710297d056d23d7e1f2aadad7fb1f1a1271819b90978619`.
The source PDF and inspected page hashes, module snapshots and declaration
references are recorded in Section6TransposeSourceComparison-2026-10-28 in
the [source-review index](source-review-index.json). The
[completion qualifications](COMPLETENESS.md) remain in force.

| ID | Extraction lines | Passage | Status |
| --- | --- | --- | --- |
| S6-001 | 2280–2285 | Initial spectral sequence and O(1) statement | pending |
| S6-002 | 2287–2292 | Proposition 6.1 qualitative local asymptotics | pending |
| S6-003 | 2294–2309 | Proposition 6.1 literal positive-index quantitative budget | pending |
| S6-004 | 2312–2316 | Reflection argument for interval eigenvalues | pending |
| S6-005 | 2318–2328 | Corollary 6.2 on arbitrary period-two input | pending |
| S6-006 | 2331–2336 | Canonical midpoint and gap asymptotics | pending |
| S6-007 | 2339–2368 | Source weights, original weighted norm and Sobolev examples | pending |
| S6-008 | 2370–2384 | Proposition 6.3 literal positive-index gap budget | pending |
| S6-009 | 2387–2398 | Lyapunov-Schmidt attribution and free modes | pending |
| S6-010 | 2399–2409 | Closed strips and P/Q topological decomposition | pending |
| S6-011 | 2410–2421 | Free multiplier, actual potential and projected equations | pending |
| S6-012 | 2422–2432 | Complementary inverse geometry and transformed Q equation | pending |
| S6-013 | 2442–2448 | Id-T formulation | pending |
| S6-014 | 2449–2474 | Exact opposite component shifts | pending |
| S6-015 | 2476–2486 | Lemma 6.4 all finite Banach exponents | pending |
| S6-016 | 2488–2525 | Full reciprocal series, shifted Holder and Young proof | pending |
| S6-017 | 2528–2534 | Square decay and Neumann inversion | pending |
| S6-018 | 2544–2555 | Lemma 6.5 and exact retained-boundary tail | pending |
| S6-019 | 2558–2578 | Actual double inverse and full double coefficients | pending |
| S6-020 | 2580–2584 | Near/far partition | pending |
| S6-021 | 2586–2605 | Far weighted Holder estimate | pending |
| S6-022 | 2606–2629 | Near geometry, weight gain and tail estimate | pending |
| S6-023 | 2631–2661 | Component recombination and printed final equality | pending |
| S6-024 | 2663–2684 | Common half-contraction and compatible Neumann inverses | matched |
| S6-025 | 2686–2694 | Reduced map and Lemma 6.6 | matched |
| S6-026 | 2696–2715 | Full original-domain reconstruction and converse | matched |
| S6-027 | 2725–2754 | Actual matrix entries and printed basis order | matched |
| S6-028 | 2755–2764 | Lemma 6.7 and required reality hypothesis | corrected |
| S6-029 | 2766–2796 | Equal diagonals via transposition/conjugation | interpreted |
| S6-030 | 2799–2853 | Reality identities using the stated type assumption | matched |
| S6-031 | 2856–2880 | Matrix form and full parity series (1.14)-(1.15) | matched |
| S6-032 | 2883–2888 | Actual suprema on closed unbounded strips | matched |
| S6-033 | 2891–2915 | Lemma 6.8 analytic scope and printed bounds | pending |
| S6-034 | 2917–2933 | Uniform series and corrected potential vector | pending |
| S6-035 | 2935–2941 | Actual diagonal coefficient sum | pending |
| S6-036 | 2952–2970 | Diagonal Holder estimate | pending |
| S6-037 | 2972–3036 | Diagonal near/far power sums in both exponent ranges | pending |
| S6-038 | 3037–3058 | Off-diagonal double sum and inserted weight factor | pending |
| S6-039 | 3060–3096 | Three index regions and (1.16) | pending |
| S6-040 | 3097–3147 | High-exponent off-diagonal sum estimates | pending |
| S6-041 | 3149–3174 | Low-exponent off-diagonal sum estimates | pending |
| S6-042 | 3176–3183 | Actual determinant and Rouche preparation | pending |
| S6-043 | 3185–3207 | Lemma 6.9 roots, gap and literal duplicated positive sum | pending |
| S6-044 | 3217–3232 | Uniform strip bounds, Rouche counts and no exterior roots | pending |
| S6-045 | 3233–3259 | Branch-free root estimate, Cauchy derivative and gap | pending |
| S6-046 | 3261–3270 | Identification with actual periodic pairs | pending |
| S6-047 | 3272–3293 | Final weighted gap estimate and source constants | pending |

## Reviewed assertions

### S6-024: Common half-contraction and compatible Neumann inverses

- One open convex potential neighborhood and one cutoff N>=1 give both printed half-contractions on every distant closed strip. The proof controls one Fourier tail on the neighborhood, uses tail monotonicity, and transports the unit-weight norm isometrically to the original component-sum space.
- The squared Neumann factorization is a two-sided inverse; its even series converges in the original operator norm. The weighted and original inverses agree on every weighted input.
- The actual derivative-domain Q solution is unique and satisfies Phi v=T_hat T Phi u. The inverse expansion and commutation give both product orders in Id+T_hat T=T_hat.
- Substitution of weightedQSolution_total_potential into sourceWeightedPencil_add_zero_iff_PQ gives the displayed P equation A u=P T_hat Phi u. This is a composition of the cited identities, with the original resonant/complementary conditions retained.

Public evidence: `sourceLemma6_5_uniform_half`, `sourcePotentialInverse_square_norm`, `exists_uniform_weightedFrequencyNeighborhood`, `sourceComplementaryCorrection_formula`, `sourceComplementaryCorrection_even_hasSum`, `sourceComplementaryCorrection_left`, `sourceComplementaryCorrection_right`, `sourceComplementaryCorrection_weightedInput`, `exists_uniform_sourceComplementaryCorrection`, `sourceQSolution_potential`, `sourceQSolution_unique`, `weightedCorrection_expand`, `weightedCorrection_commute`, `weightedQSolution_total_potential`, `sourceWeightedPencil_add_zero_iff_PQ`.

### S6-025: Reduced map and Lemma 6.6

- The resonant map is the free diagonal minus the corrected potential, with actual synthesis and coefficient extraction.
- Its matrix determinant vanishes exactly at a noninvertible original source pencil, equivalently at an original periodic eigenvalue. The source domain is covered by an equivalence, not only an inclusion.
- One neighborhood and cutoff make the criterion uniform on all distant closed strips, including p=1.

Public evidence: `weightedResonantMap`, `weightedResonantMatrix`, `sourceUnitDomainEquiv`, `sourceLemma6_6`, `sourceLemma6_6_eigenvector`, `sourceLemma6_6_uniform`.

### S6-026: Full original-domain reconstruction and converse

- The constructed v is the actual domain-valued complementary free inverse of the corrected potential. It belongs to the complementary derivative domain and solves the Q equation.
- The full reconstruction has the prescribed two resonant amplitudes. Its differential residual is exactly the synthesized matrix residual.
- Nonzero resonant data reconstruct a nonzero vector; every original eigenvector is recovered. Thus both directions of the source proof retain the nonzero requirement.

Public evidence: `weightedQSolution`, `complementaryFreeDomainInverse_nonresonant`, `weightedQSolution_potential`, `weightedQSolution_equation`, `sourceResonantReconstruction_eq`, `sourceResonantReconstruction_coordinates`, `sourceResonantReconstruction_ne_zero_iff`, `sourceResonantReconstruction_residual`, `sourceResonantReconstruction_kernel_iff`, `sourceResonantReconstruction_of_eigenvector`.

### S6-027: Actual matrix entries and printed basis order

- Matrix entries are evaluations of the actual original corrected potential on the two resonant domain modes.
- The printed (plus,minus) basis reverses the library physical (minus,plus) order. Reversing both indices gives exactly the displayed off-diagonal signs and leaves the determinant unchanged.
- The scalar determinant formula and its connection to the original periodic spectrum use these same entries.

Public evidence: `sourceCorrectionMatrix_entry`, `sourcePrintedResonantMatrix_form`, `sourcePrintedResonantMatrix_det`, `sourceResonantMatrix_det_formula`, `sourceSpectrum_iff_resonantScalarEquation`.

The mathematical matrix assertions are compared. The historical attribution to references [37,18] is not independently checked here.

### S6-028: Lemma 6.7 and required reality hypothesis

- The two diagonal entries agree for arbitrary complex potentials at every finite Banach exponent.
- The printed unconditional parameter-conjugation identity for a_n is false. The single fixed original potential (1,i) gives a_n(n*pi)=i/(2*pi*n) and violates it beyond every proposed cutoff, while satisfying half-contraction.
- The corrected statement assumes phi*=epsilon*phi, epsilon^2=1, for both the diagonal and signed off-diagonal conjugation conclusions. One common local cutoff supplies the conditions at z and conjugate(z).

Public evidence: `sourceLemma6_7_i`, `sourceResonantA_constant_center`, `exists_large_nonreal_sourceResonantA`, `not_sourceLemma6_7_printed_diagonal`, `sourceHasRealitySign_iff_coeff`, `sourceLemma6_7_ii`, `sourceLemma6_7_uniform`.

Corrected means a formal refutation and a separately scoped valid replacement; the printed unconditional statement is not marked proved.

### S6-029: Equal diagonals via transposition/conjugation

- The original cross-component unconjugated Fourier pairing is defined on a base coefficient vector and a derivative-domain test; its formula preserves the actual raw coefficients.
- Q transfers to the derivative-domain test. The actual punctured complementary inverse R=A^-1 Q is transpose symmetric, including at the free center. Potential multiplication is symmetric on two derivative-domain tests.
- Transposing T=Phi R reverses the two factors. Induction gives the full identity for every T^j Phi before any small-square assumption.
- When the shifted square is small, the full corrected potential is transpose symmetric on arbitrary derivative-domain tests. The proof cancels the equal R terms in the potential symmetry identity for f+R Hf and g+R Hg, where H=T_hat Phi.
- The original-source theorem uses the actual source correction and potential difference. The p=3 negative-strip integration example derives equality of the actual matrix diagonals directly from this full identity.

Public evidence: `sourceGreenPairing`, `sourceGreenPairing_apply`, `sourceGreenPairing_unitInput`, `weightedGreenPairing_complementaryProjection`, `weightedGreenPairing_complementaryInverse_symm`, `weightedGreenPairing_potential_symm`, `weightedGreenPairing_potentialInverse_transfer`, `weightedGreenPairing_powerPotential_symm`, `weightedGreenPairing_add_right`, `weightedGreenPairing_correctedPotential_symm`, `sourceCorrectedPotential_transpose`.

The source adjoint notation is implemented as its bilinear transpose identity on stated domains. No Hilbert adjoint on a general l^p space, bounded potential on the entire base space, or full free inverse at a resonant center is asserted. This domain interpretation remains explicit, rather than being counted as a literal formalization of every adjoint symbol.

### S6-030: Reality identities using the stated type assumption

- The proof explicitly assumes phi*=epsilon*phi. Physical conjugation reverses Fourier indices and exchanges components with the stated sign.
- The potential, domain-valued complementary inverse and T intertwine at conjugate spectral parameters. Uniqueness of the inverse transfers this to the full correction.
- Extraction on the two resonant modes gives the diagonal and signed off-diagonal parameter-conjugation identities. Both signs are covered; the type condition is retained throughout.

Public evidence: `sourcePotentialStar_fst`, `sourcePotentialStar_snd`, `sourceHasRealitySign_iff_coeff`, `weightedConjugation_domainPotential`, `weightedConjugation_domainInverse`, `weightedConjugation_potentialInverse`, `weightedConjugation_correction`, `weightedConjugation_correctedSynthesis`, `weightedResonantA_conj`, `weightedResonantBPlus_conj`, `sourceLemma6_7_ii`.

The formal proof uses signed conjugation and inverse uniqueness in place of manipulating Hilbert adjoints. It proves the displayed coefficient identities under the hypothesis used in the source proof.

### S6-031: Matrix form and full parity series (1.14)-(1.15)

- The displayed common-diagonal matrix has the printed basis order.
- Even terms of the diagonal and odd terms of each off-diagonal vanish individually, before any contraction condition.
- The even vector is the convergent sum of actual original operator powers. Continuous extraction yields the odd diagonal series and strictly positive even remainder series.
- Equations (1.14) and (1.15) retain the actual original T and the leading raw coefficients: second component at 2n, first component at -2n.

Public evidence: `sourcePrintedResonantMatrix_form`, `sourceResonantEvenVector_hasSum`, `sourceResonantA_even_term_zero`, `sourceResonantBPlus_odd_term_zero`, `sourceResonantBMinus_odd_term_zero`, `sourceResonantA_hasSum`, `sourceResonantBPlus_remainder_hasSum`, `sourceResonantBMinus_remainder_hasSum`, `sourceEquation1_14`, `sourceEquation1_15_plus`, `sourceEquation1_15_minus`.

### S6-032: Actual suprema on closed unbounded strips

- The source coefficient suprema are suprema of their actual images on the full closed unbounded strip, not only bounds for sampled values.
- Uniform bounds establish bounded-above images, nonnegative suprema and pointwise domination. The quantitative uniform theorem uses 1<p<infinity, as in the following Lemma 6.8.
- Equality of the original and weighted coefficient functions on the whole common correction strip gives equality of the actual supremum sets and values.

Public evidence: `sourceResonantDiagonalSup`, `sourceResonantBMinusSup`, `sourceResonantBPlusSup`, `sourceCoefficientStripBounds_of_bound`, `exists_uniform_sourceCoefficientStripBounds`, `sourceResonantSup_eq_weighted`, `exists_uniform_sourceResonantSup_eq`.

A real-valued sSup alone is not evidence of boundedness. The cited bounded-image theorem supplies that evidence for the actual coefficient functions.

## Remaining work

Reconcile the other 38 passage groups, including the earlier groups already
covered by focused reviews. Next in this forward pass are the analytic and
power-sum proof assertions of Lemma 6.8. The final p.44 inequality with
1/2^p on its left side remains unresolved; the corrected larger-constant
bound and the refuted preceding middle comparison are separate results.
This ledger does not replace the source-wide inventory or the remaining
Birkhoff-construction and Appendix G.2 checks.
