# COMPLETE Theorem 1.2(ii): compact corrected global derivative

The COMPLETE Theorem 1.2(ii) compact derivative clause is now proved for the ACTUAL global physical KdV frequency: for EVERY -1<s<-1/2 and EVERY nonnegative original action, d(omega-star)+6*Id is compact in the SAME original positive-frequency weighted ell(2s+1,1) source and target norm. One actual weak scalar frequency family is fixed BEFORE all regularities and all actions, with exact independently defined native Hamiltonian frequency recovery. Each regularity has ONE genuine complex analytic map near the ENTIRE original positive action cone, with literal raw frequency calibration to that same family. The diagonal and off-diagonal compact ACTION germs are combined on the SAME actual physical chart and native inverse, identified with the FULL global intermediate frequency, then extended from the nonnegative cone by holomorphic uniqueness in the proper normalized positive-frequency model. Exact norm-isometric conjugation gives the literal original weighted action space and the unchanged coefficient +6.

## Exact source clause and Lean declaration

The source Theorem 1.2(ii), PDF page 4, requires that for every -1<s<-1/2 and every I in the nonnegative quadrant of the ORIGINAL positive-frequency weighted ell(2s+1,1) space, `d_I omega-star+6*Id` is compact on that SAME space.

The declaration is

`NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData.theorem_1_2_ii`

in `NLS/Articles/KdVKdV2Frequencies/Theorem12CompactDerivative.lean`. One globally analytic actual weak scalar frequency family G is fixed BEFORE every regularity and action. It has exact recovery of the independently defined native H1 Hamiltonian frequencies after subtracting `(2*n*pi)^3`. For each -1<s<-1/2, there is ONE complex analytic map F on an OPEN neighborhood of the ENTIRE original nonnegative weighted action cone. At every nonnegative action its raw positive coefficients agree with that same G through the coefficient-preserving original weak inclusion. At EVERY such action, including zero, closed actions and arbitrary infinite support, its complex Frechet derivative plus the literal `6*Id` is compact.

## The literal original action Banach space

The source article indexes actions and frequencies by positive physical labels. `WeightedCoeff.positiveSupportedSubmodule w` realizes precisely this space as the CLOSED subspace of the raw integer weighted ell1 space whose nonpositive slots vanish. Its inherited norm is the ORIGINAL weighted ell1 norm, with no contribution from the fixed zero slots. Completeness is proved from closedness.

`WeightedCoeff.positiveActionModelEquiv w actionIndexEquiv` is a genuine linear ISOMETRIC equivalence from enumerated ell1 onto that exact space. Its raw positive coordinate is `b_k/w(actionIndexEquiv k)`. Its inverse samples `w_n*a_n` over ALL positive labels; both inverse identities are proved. It preserves and reflects the original raw nonnegative cone. Consequently the normalized coefficient model is only a proved exact Banach coordinate change. The final theorem is stated on the ORIGINAL supported weighted space, with literal raw original frequency values.

The full raw weighted space over integers contains extra nonpositive directions ignored by older raw frequency extensions. Its positive action cone is not spanning. No holomorphic uniqueness or full-raw +6Id compactness is inferred there. Complex uniqueness is used only in the normalized positive-frequency model, which parametrizes ALL original action directions.

## Combining actual compact contributions

The off-diagonal construction now retains the original SourceLemma12_12 estimates for the SAME actual physical chart and root family that builds its strictly smoothing packet. Pulling through the actual global native inverse retains those estimates and all signed coordinate identities. They construct the actual diagonal Hilbert symbol on a shrink of that SAME off-diagonal pair chart, with literal equality of the physical chart and native inverse.

The previously verified off-diagonal compact action germ and diagonal compact action germ are therefore compatible. Their real realizations may differ in phase, but have exactly the same normalized actions and belong to the same fixed physical chart. The proved whole-discriminant invariance of the actual off-diagonal correction identifies their values. The exact original rough Arnold factorization then gives

`correction_n+6*a_n=offDiagonalContribution_n+diagonalContribution_n`.

Both contributions are genuine complex analytic maps into the SAME original weighted ell1 target and have compact action derivatives at every complex point of a common germ. Their sum therefore has compact derivative. No source derivative is substituted for an action derivative, and the physical coefficient -12 and both signed own labels are retained.

## Identifying the FULL global frequency

`NegativeWeightedFrequencyPairChart.correction_eq_of_diagonal_pair` compares independently chosen full-frequency and diagonal physical charts on every real equal-action fiber. Exact original finite physical recovery identifies both scalar corrections with the independently defined physical Hamiltonian frequency. Simultaneous finite truncation extends this equality to every rough infinite-support real pair, including boundary actions.

`global_negativeWeighted_packet_diagonal_recovery` identifies the actual full global intermediate frequency with the diagonal chart correction. Thus the sum of the actual compact germs is calibrated to the FULL global frequency plus 6I on every nonnegative action in the local germ, in the exact output weight.

The proved positive-frequency linear isometry transports this equality into the normalized ell1 model. Holomorphic uniqueness from its full nonnegative action cone identifies the ENTIRE complex germ, even at boundary actions. Differentiating proves compactness of the FULL corrected global derivative. Exact linear isometric conjugation transports it back to the original supported weighted Banach space; the identity term remains the literal `6*Id`.

## Scope and remaining main obligations

COMPLETE Theorem 1.1 remains verified; the other ten COMPLETE main theorem rows remain OPEN. Theorem 1.2(ii) is VERIFIED and all regularity-dependent target clauses of Theorem 1.2(i) remain verified. COMPLETE Theorem 1.2 still needs the sharp locally uniform high-index asymptotics of (iii), and the Hilbert target/compact derivative assertions of (iv), together with a consolidated precise full statement. Strict concavity, local inverses, PDE conclusions, and KdV2 actual weighted moments, mass-renormalized frequency identification and global conclusions remain open.

This milestone proves a complete numbered SOURCE CLAUSE, not the complete Theorem 1.2 row. No sharp asymptotics, Hilbert target or other main row is marked verified by inference.

## Modules

- `NLS/KdV/PhysicalOffDiagonalFrequencyEstimates.lean`: Construct the actual strictly smoothing off-diagonal physical packet while retaining SourceLemma12_12Data for the SAME physical chart and its original root family. No Miura inverse, branch or estimates are assumed by the caller.
- `NLS/Articles/KdVKdV2Frequencies/OffDiagonalPairOriginalEstimates.lean`: Pull that actual smoothing packet through the global native inverse while retaining its SAME physical chart original estimates and exact original signed coordinates.
- `NLS/SequenceSpaces/WeightedPositiveActionModel.lean`: An exact linear isometric lift from enumerated ell1 to original positive-supported weighted ell1, a bounded restriction, both inverse identities on the original positive support, and preservation of the complete nonnegative action cone.
- `NLS/Articles/KdVKdV2Frequencies/CompatibleDiagonalPairCharts.lean`: The actual diagonal Hilbert symbol and original rough Arnold factorization are constructed on a shrink of the SAME off-diagonal pair chart, with literal equality of physical chart and native rough inverse. This removes any assumption of arbitrary off-diagonal cross-chart agreement.
- `NLS/SequenceSpaces/CompactAnalyticLinearTransport.lean`: Compact derivatives survive bounded linear pre/postcomposition, with genuine analytic transported germs. Agreement of a corrected map and a compact analytic germ on the full normalized nonnegative cone identifies the actual corrected Frechet derivative even at boundary actions.
- `NLS/Articles/KdVKdV2Frequencies/DiagonalGlobalFrequencyAgreement.lean`: The FULL correction of the actual diagonal pair chart agrees with the existing global intermediate frequency. Independently chosen physical charts are compared by exact original finite physical calibration and simultaneous finite truncation, retaining every rough infinite-support real action.
- `NLS/Articles/KdVKdV2Frequencies/DiagonalActionRealizationNormalization.lean`: Exact original Arnold actions of a real diagonal realization recover its normalized weighted quadratic actions, in the original weight and with no finite support or open-gap assumption.
- `NLS/Articles/KdVKdV2Frequencies/CorrectedFrequencyCompactGerms.lean`: The actual diagonal and off-diagonal compact ACTION contributions combine on one common physical chart and native inverse. On EVERY nonnegative action in the original weighted ell1 germ their sum equals the FULL global frequency plus the literal 6I term, after the exact output weight.
- `NLS/Articles/KdVKdV2Frequencies/GlobalCorrectedFrequencyCompact.lean`: The FULL corrected global intermediate frequency derivative is compact at EVERY normalized nonnegative action, including boundary and infinite support. A true positive-frequency norm model and the complex cone identity theorem identify the entire derivative, with no inference from the non-spanning full-raw positive support cone.
- `NLS/SequenceSpaces/WeightedPositiveActionSpace.lean`: The ORIGINAL positive-frequency weighted ell1 action space is a CLOSED supported submodule of the raw integer model, is complete, and is exactly linearly isometric to enumerated ell1. The inverse preserves and reflects original raw nonnegativity, and every raw positive coordinate retains its literal weight.
- `NLS/SequenceSpaces/CompactCorrectedDerivativeConjugate.lean`: An exact Banach linear equivalence preserves compactness of the FULL corrected derivative under conjugation, including the literal scalar identity term and both domain/codomain norms.
- `NLS/Articles/KdVKdV2Frequencies/OriginalPositiveFrequencyCompact.lean`: Transport the ACTUAL global frequency and compact corrected derivative back to the ORIGINAL supported positive-frequency weighted ell1 space. One complex neighborhood contains the entire nonnegative cone, raw original frequency calibration holds at every action, and dF+6Id is compact at every such action.
- `NLS/Articles/KdVKdV2Frequencies/Theorem12CompactDerivative.lean`: The COMPLETE Theorem 1.2(ii) compact derivative clause is now proved for the ACTUAL global physical KdV frequency: for EVERY -1<s<-1/2 and EVERY nonnegative original action, d(omega-star)+6*Id is compact in the SAME original positive-frequency weighted ell(2s+1,1) source and target norm. One actual weak scalar frequency family is fixed BEFORE all regularities and all actions, with exact independently defined native Hamiltonian frequency recovery. Each regularity has ONE genuine complex analytic map near the ENTIRE original positive action cone, with literal raw frequency calibration to that same family. The diagonal and off-diagonal compact ACTION germs are combined on the SAME actual physical chart and native inverse, identified with the FULL global intermediate frequency, then extended from the nonnegative cone by holomorphic uniqueness in the proper normalized positive-frequency model. Exact norm-isometric conjugation gives the literal original weighted action space and the unchanged coefficient +6.

## Validation

All 3351 prior selected sources and all 53 provenance records remain byte-identical. Thirteen new own modules containing 22 explicit theorems were strictly rebuilt in dependency order AFTER freezing 3420 selected-source/checker/provenance/pinned-Mathlib-source hashes. The exact new import closure is these thirteen modules; no new canonical source or provenance record was needed. The fresh full transitive axiom audit covers all 3364 selected modules and EVERY imported NLS declaration: 25902 selected and 47969 imported declarations. The entire audit loop, collectAxioms traversal, allowed axioms and imported NLS scope remain byte-identical to baseline. Exact ordered selection, dependencies, reachability and 27 private chunks of at most 128 names were verified. The actual 3364-name bidirectional NameSet probe rejects insertion/deletion mismatches. Private output freshness, overlay targets, unchanged canonical main and pinned Mathlib are checked. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a thirteen-module incremental rebuild retaining all prior strict evidence, not a full 3364-module rebuild.

No sorry, new axiom, raised limit or linter exception. Complete main theorem status remains one verified, ten open; Theorem 1.2(ii) is now a verified complete source clause.
