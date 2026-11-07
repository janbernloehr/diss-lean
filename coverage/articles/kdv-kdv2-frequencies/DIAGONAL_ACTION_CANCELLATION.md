# Exact diagonal action cancellation for Theorem 1.2

The exact original +6I counterterm now cancels the free DIAGONAL physical second-moment term near EVERY original real Hill source. One actual physical Miura frequency chart, one Cauchy normalization family and one complex source ball serve ALL signed moment indices. The normalized second moments and both diagonal error factors are complex analytic through arbitrary closed gaps. The article-level theorem retains the original contour actions, physical -12 frequency normalization and BOTH opposite own Dirac labels. A reusable theorem also proves compact corrected derivatives from a finite-exponent analytic diagonal symbol and a compact remainder, in the SAME original weighted ell1 norm. The required finite-exponent estimates for the ACTUAL diagonal symbol are not yet established.

## Actual normalization through closed gaps

The actual Cauchy integral `C.normalizedSecondMoment s n k` is defined before any division by the selected squared gap. Its verified identity is `M_nk = gamma_k^2 * N_nk`. The new analytic theorem proves complex analyticity of N_nk on a COMMON ball near every real source for ALL n,k. It uses the actual normalized psi root branch, actual filled primitive quotient, analytic symmetric midpoint and squared gap. Individual endpoint selections need not be analytic. Every closed gap is included.

The same ball supports the actual first weighted Dirac action `A_n1 = gamma_n^2 * W_n1`, with W_n1 complex analytic. Define regular errors

`E_n = 4*N_nn - pi`,

`F_n = 4*W_n1 - pi*n`.

Both errors are scalar analytic on this common ball, including collapsed gaps. They are regular integrals, not totalized quotients by gamma_n^2. The exact complex identity is

`-12*n*(M_nn-M_n,-n) + 12*A_n1 = 3*gamma_n^2*(F_n-n*E_n) + 12*n*gamma_-n^2*N_n,-n`.

The free pi*n terms cancel algebraically at EVERY complex source in this ball. This is not merely a Taylor coefficient at zero. Neither opposite own label may be discarded. No sign convention for the opposite gap is needed in this identity; its own squared gap is retained explicitly.

## Original physical +6I identification

`exists_physicalMiuraFrequencyChart_with_original_estimates` constructs an actual physical chart near EVERY real rough Hill source, with any requested lower bound on its positive energy shift and its verified original psi estimates retained. No Miura inverse, root branch, period condition or error estimate is supplied by the caller.

`theorem_1_2_local_diagonal_cancellation` applies at EVERY original real Hill potential. One such physical chart, one Cauchy family and one radius work simultaneously for ALL signed moment indices and all original real potentials whose Miura sources lie in that ball and in the physical domain. The exact original action is twice the first weighted Dirac action: I_n=2*A_n1. The original quadratic contour pullback, zero-period shift cancellation and exact 2*z Jacobian establish this identification. Thus the actual physical frequency correction satisfies

`correction_n + 6*I_n = offDiagonalCorrection_n + 3*gamma_n^2*(F_n-n*E_n) + 12*n*gamma_-n^2*N_n,-n`.

The physical correction retains the original -12 factor and original contour actions. All selected gaps may be closed and arbitrary infinite support is included. The analytic error domains are common complex SOURCE neighborhoods; no action-space regularity of the diagonal error is asserted here.

## Compactness mechanism and unresolved estimate

The reusable `WeightedCoeff.isCompactOperator_corrected_fderiv_of_finiteSymbol` works in the SAME original weighted coefficient source and target, in particular weighted ell1 at order 2s+1. If an analytic correction has an exact decomposition into a compact-derivative remainder and a product of the raw action with a finite-exponent analytic symbol, its corrected derivative is compact. The fixed-symbol derivative term is compact because a finite-exponent symbol vanishes at infinity. The symbol-variation term is compact because multiplication from bounded symbols into a fixed finite-exponent coefficient sequence is compact. Both terms are transported by the original weight isometry without changing raw coefficients. The theorem holds for any scalar counterterm, including 6.

This is a fully abstract criterion. It does NOT provide the finite-exponent analytic symbol for the actual diagonal physical remainder. Proving the required locally uniform sequence estimates, recovering a suitable nonvanishing normalized original action factor, descending the actual spectral remainder to original actions and identifying it with the full global frequency map remain necessary. The already proved off-diagonal action compactness supplies only the other contribution.

## Canonical reuse and scope

`CANONICAL_DIAGONAL_ACTION_NORMALIZATION_REUSE.json` records seven source files at canonical main c5bcf6344cd2e2628ae537e98b85bb9ec1849dec. They were already tracked in the article branch, remain byte-identical to canonical main and the previous article HEAD, and were newly selected and strictly rebuilt privately for this milestone. These give the original regular moment integral, sine-square mean and exact free psi factors. All prior provenance records, canonical main and shared build caches remain unchanged.

All regularity-dependent target clauses of Theorem 1.2(i), and the previously proved local off-diagonal ACTION compactness near every original intermediate nonnegative action, remain verified. COMPLETE Theorem 1.1 remains verified; the other ten COMPLETE main rows remain OPEN. Theorem 1.2(ii) still needs locally uniform sequence estimates for the actual normalized DIAGONAL error, its descent and identification with the full global frequency map. The scalar 6I cancellation is now proved, but compactness of the full corrected derivative is not. Sharp locally uniform asymptotics, Hilbert derivative compactness, strict concavity, local inverses, PDE conclusions and the KdV2 weighted moment sums and mass-renormalized physical frequency identification remain open.

## Modules

- `NLS/ComplexAnalysis/ParametricSineSquareMean.lean`: Unchanged canonical sine-square weighted means at a collapsed gap, with exact pi/2 central value and regularity of the actual integral.
- `NLS/ZakharovShabat/SourcePsiFreeSequence.lean`: Unchanged canonical actual free psi sequence needed by the verified free regular factors.
- `NLS/ZakharovShabat/SourcePsiFreeFrechet.lean`: Unchanged canonical free psi Frechet derivatives needed by the verified free regular factors.
- `NLS/ZakharovShabat/SourcePsiFreeOperator.lean`: Unchanged canonical actual free psi operator needed by the verified free regular factors.
- `NLS/ZakharovShabat/SourcePsiFreeEquationFactorization.lean`: Unchanged canonical free psi equations and exact factorization needed for the calibrated free moment numerator.
- `NLS/ZakharovShabat/SourceMomentFreeFactors.lean`: Unchanged canonical exact free regular psi numerator factors, including the diagonal and off-diagonal values at the original free spectral centers.
- `NLS/ZakharovShabat/SourceNormalizedSecondMoment.lean`: Unchanged canonical regular second-moment integral after extracting the squared gap, exact all-gap factorization, exact free pi/4 diagonal value and free-source continuity.
- `NLS/ZakharovShabat/SourceNormalizedSecondMomentAnalytic.lean`: The ACTUAL regular normalized second moment is complex analytic on one common source ball for ALL signed numerator and contour indices, including every closed gap. Only the analytic midpoint and squared gap are differentiated; no analytic choice of individual endpoints or nonzero-gap assumption is made.
- `NLS/ZakharovShabat/SourceRegularDiagonalActionCancellation.lean`: Analytic regular diagonal moment and first weighted action errors expose exact cancellation of the original free pi*n term. On one common complex source ball, the actual diagonal moment pair plus twelve times the actual first weighted Dirac action equals the explicit squared-gap error remainder, including closed gaps and all integer indices. No sequence estimate is asserted.
- `NLS/SequenceSpaces/CompactFiniteSymbolPacket.lean`: For any original weight and finite target exponent, BOTH derivative terms of a finite-exponent analytic symbol times a weighted analytic sequence packet are compact. A compact remainder plus this exact diagonal factorization gives compactness of the full corrected derivative for any scalar counterterm, including 6. The factorization is an independent hypothesis; it is not assumed to hold spectrally.
- `NLS/KdV/PhysicalDiagonalActionCancellation.lean`: At EVERY real rough source, an actual physical Miura frequency chart is constructed with its verified original psi estimates and arbitrary requested lower energy shift. Near any original real Hill source in such a chart, the original +6I counterterm has the exact regular diagonal cancellation on a common complex normalization ball, simultaneously at all original real sources in that ball, with both signed own labels retained.
- `NLS/Articles/KdVKdV2Frequencies/Theorem12DiagonalCancellation.lean`: The exact original +6I counterterm now cancels the free DIAGONAL physical second-moment term near EVERY original real Hill source. One actual physical Miura frequency chart, one Cauchy normalization family and one complex source ball serve ALL signed moment indices. The normalized second moments and both diagonal error factors are complex analytic through arbitrary closed gaps. The article-level theorem retains the original contour actions, physical -12 frequency normalization and BOTH opposite own Dirac labels. A reusable theorem also proves compact corrected derivatives from a finite-exponent analytic diagonal symbol and a compact remainder, in the SAME original weighted ell1 norm. The required finite-exponent estimates for the ACTUAL diagonal symbol are not yet established.

## Validation

All 3312 prior selected sources and all 51 prior provenance records remain byte-identical. Five new own modules and seven newly selected canonical normalization/free-factor modules were strictly rebuilt in dependency order AFTER freezing 3379 selected-source/checker/provenance/pinned-Mathlib-source hashes. The seven canonical source files were already tracked, remain byte-identical to canonical main c5bcf6344cd2e2628ae537e98b85bb9ec1849dec and the previous article HEAD, and have one new reuse record, bringing provenance to 52 records. The exact new import closure is these twelve modules. The fresh combined transitive axiom audit covers all 3324 selected modules and EVERY imported NLS declaration: 25722 selected and 47789 imported declarations. The entire audit loop, collectAxioms traversal, allowed axioms and imported NLS scope remain byte-identical to baseline. Exact ordered selection, dependencies, reachability and 26 private selection chunks of at most 128 names were verified. The actual 3324-name bidirectional NameSet probe rejects insertion/deletion mismatches. Private output freshness, overlay targets, unchanged canonical main and pinned Mathlib are checked. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a twelve-module incremental rebuild retaining all prior strict evidence, not a full 3324-module rebuild.

Five own modules contain 10 explicit theorems. No sorry, new axiom, raised limit or linter exception. Complete main theorem status remains one verified, ten open.
