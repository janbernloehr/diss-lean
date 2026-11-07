# Sharp actual off-diagonal decay: Theorem 1.2(iii) dependency

A sharp OFF-DIAGONAL dependency of Theorem 1.2(iii) is proved for the ACTUAL physical KdV correction, at EVERY original native real H^s base for -1<=s<=-1/3. ONE full complex native neighborhood has a uniform bound of exact order (1+n)^(-3s-2), including the O(1/n) endpoint s=-1/3. At EVERY complex source in that neighborhood the off-diagonal correction is pointwise o((1+n)^(-3s-2)) for -1<=s<-1/3. Original positive physical indices, the actual moment branch, the exact -12 normalization, all closed gaps and infinite support are retained. This is an off-diagonal dependency with pointwise little-o; it does NOT assert locally uniform little-o or the full corrected-frequency asymptotics.

## Source obligation and exact scope

The source Theorem 1.2(iii), PDF page 4, and Theorem 3.6(iii), PDF pages 32-34, require sharp locally uniform asymptotics of the COMPLETE corrected frequency in the ORIGINAL action spaces. The source proof separates a diagonal action-gap expansion from the off-diagonal moment sum.

`NLS.Articles.KdVKdV2Frequencies.theorem_1_2_iii_offDiagonal_sharp_dependency`

in `NLS/Articles/KdVKdV2Frequencies/Theorem12OffDiagonalSharpDecay.lean` proves the actual ORIGINAL NATIVE-SOURCE off-diagonal dependency. The full Theorem1.2(iii) is still OPEN.

For EVERY -1<=s<=-1/3 and EVERY real original native H^s base, it constructs one actual physical Miura frequency chart B and one full COMPLEX native H^s neighborhood T of that base. One K>=0 is chosen BEFORE all sources in T and all physical positive indices, with

`(1+n)^(3s+2) * norm(B.offDiagonalCorrection_n(q)) <= K`.

For EVERY complex q in that SAME T, the normalized off-diagonal tail tends to zero as n tends to infinity whenever -1<=s<-1/3. The endpoint s=-1/3 gives a locally uniform O(1/n) bound. The asymptotic order is exact, with no epsilon loss. This milestone proves POINTWISE little-o at every complex source and a LOCALLY UNIFORM big-O bound. It does not substitute those for the complete source locally uniform little-o assertion.

## Exact kernel and cubic estimate

Let `K_r(n,k)=(1+abs(n))^(-r)*(1+abs(k))^r/abs(n-k)`, with the diagonal value totalized to zero. Submultiplicativity of the Sobolev weight gives `0<=K_r(n,k)<=2` at EVERY signed pair for -1<=r<=1. Each fixed k has `K_r(n,k)->0` at positive infinity for r>-1. This follows from an explicit inverse-bracket column bound, with all constants and endpoint hypotheses retained.

A genuine ell1 majorant g therefore gives absolutely summable rows and `sum_k K_r(n,k)*g_k<=2*sum_k g_k`. Dominated convergence proves a vanishing normalized tail for r>-1. This is an exact-order result, improving the earlier summable-column argument that required an arbitrarily small loss.

The actual weighted squared-gap sequence h obeys `norm(h_k)=(1+abs(k))^(2t)*norm(gamma_k)^2`, and the same verified factory bounds `(1+abs(k))^t*norm(gamma_k)<=S`. Thus

`abs(k)*norm(gamma_k)^3 <= S*(1+abs(k))^(1-3t)*norm(h_k)`.

The refined ACTUAL off-diagonal moment bound has a punctured reciprocal factor times this cubic gap factor. Taking r=1-3t gives the sharp off-diagonal order, including t=0 and the endpoint t=2/3. Both own labels n and -n are removed by the literal paired off-diagonal row, with its exact absolutely convergent sum identity.

## Actual spectral and physical data

The source theorem applies to the actual SourceAbelianMomentAtlas and its SAME SourcePsiSquaredGapComplexExtension, with the verified refined cubic moment estimates and weighted squared-gap bounds. All closed gaps and arbitrary infinite support are retained. The open complex source domain contains the ENTIRE real normalized weighted-source locus.

The physical construction chooses an actual native analytic Miura lift of the SAME rough physical chart. The original source norm is the native weighted H^s norm; its inclusion into H-minus-one keeps all raw coefficients unchanged. Exact normalization through the actual Miura diagonal identifies the weighted-source moment expression with B.offDiagonalCorrection. The scalar factor is the original -12, with no change of physical labels or frequency scaling.

An opaque common pullback-domain lemma and an abstract positive-frequency normalization lemma keep the parameterizations out of repeated kernel reduction. All files compile at the DEFAULT limits; no heartbeat, recursion or kernel budget is raised.

## Modules

- `NLS/SequenceSpaces/SharpReciprocalKernel.lean`: The exact weighted punctured reciprocal kernel is bounded by TWO for every order -1<=r<=1, at ALL signed indices. At every order r>-1, each fixed summation column vanishes at positive infinity. The inverse-index endpoint and all constants are explicit.
- `NLS/SequenceSpaces/SharpReciprocalSums.lean`: A genuine summable majorant gives absolute convergence and a uniform bound at the exact polynomial order. Dominated convergence proves pointwise little-o for every -1<r<=1, with no epsilon loss.
- `NLS/SequenceSpaces/SharpCubicOffDiagonalDecay.lean`: The literal original weighted squared-gap ell1 majorant and its one-gap pointwise bound give exact cubic order r=1-3t. Off-diagonal signed weighted sums retain that exponent without the previous epsilon loss; t=2/3 gives a uniform inverse-index bound.
- `NLS/ZakharovShabat/SourceSharpOffDiagonalDecay.lean`: For the ACTUAL moment atlas, the ENTIRE real normalized weighted-source locus has a complex neighborhood with locally uniform exact off-diagonal big-O bounds at every 0<=t<=2/3, and pointwise little-o at EVERY complex source for t<2/3. Closed gaps and arbitrary infinite support are included. Uniform little-o on entire neighborhoods is not asserted.
- `NLS/SequenceSpaces/PositiveFrequencyDecayNormalization.lean`: The original positive-frequency enumeration and an exact arbitrary scalar calibration preserve weighted uniform bounds and pointwise vanishing tails. In application the scalar is the literal physical -12.
- `NLS/ComplexAnalysis/CommonPullbackDomain.lean`: A reusable opaque common open domain retains the native parameterization and original rough inclusion, keeping all default kernel limits.
- `NLS/KdV/PhysicalSharpOffDiagonalTransport.lean`: The SAME actual physical chart transports the sharp moment bounds through an analytic native Miura parameterization, retaining the exact -12 constant and original positive labels in the native source norm.
- `NLS/KdV/PhysicalSharpOffDiagonalDecay.lean`: At EVERY real original native H^(t-1) base for 0<=t<=2/3, constructs an ACTUAL physical frequency chart and a full complex native neighborhood with uniform off-diagonal order 1-3t and pointwise little-o when t<2/3. All parameterizations and original spectral estimates are supplied by verified factories.
- `NLS/Articles/KdVKdV2Frequencies/Theorem12OffDiagonalSharpDecay.lean`: A sharp OFF-DIAGONAL dependency of Theorem 1.2(iii) is proved for the ACTUAL physical KdV correction, at EVERY original native real H^s base for -1<=s<=-1/3. ONE full complex native neighborhood has a uniform bound of exact order (1+n)^(-3s-2), including the O(1/n) endpoint s=-1/3. At EVERY complex source in that neighborhood the off-diagonal correction is pointwise o((1+n)^(-3s-2)) for -1<=s<-1/3. Original positive physical indices, the actual moment branch, the exact -12 normalization, all closed gaps and infinite support are retained. This is an off-diagonal dependency with pointwise little-o; it does NOT assert locally uniform little-o or the full corrected-frequency asymptotics.

## Validation

All 3392 prior selected sources and all 54 provenance records remain byte-identical. Nine new own modules containing twenty explicit public theorems were strictly rebuilt in dependency order AFTER freezing 3458 selected-source/checker/provenance/pinned-Mathlib-source hashes. The exact new import closure is those nine modules; no new canonical reuse or provenance record is needed. The fresh full transitive audit covers all 3401 selections and EVERY imported NLS declaration: 26024 selected and 48094 imported declarations. The ENTIRE audit loop, collectAxioms traversal, allowed axioms and imported-NLS scope remain byte-identical to baseline. The 3401-name bidirectional NameSet probe rejects insertion/deletion mismatches. Exact ordered selections, dependency order, reachability, 27 private chunks of at most 128 names, private fresh outputs, overlay targets, unchanged canonical main and pinned Mathlib are verified. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a nine-module incremental rebuild retaining all prior strict evidence, not a full 3401-module rebuild.

No sorry, new axiom, raised limit or linter exception.

## Remaining main obligations

Complete Theorem 1.1 and Corollary 1.4 remain VERIFIED; the other nine complete main rows remain OPEN. Complete source clauses Theorem 1.2(ii) and (iv), and the regularity-dependent target clauses of (i), remain verified. COMPLETE Theorem 1.2(iii) still requires the sharp diagonal action-gap expansion, the required locally uniform little-o, the transfer to the ORIGINAL action topology and calibration with the SAME actual global frequency, and the higher-regularity O(1/n) statement. Then assemble the complete Theorem 1.2. Global Hessian nonpositivity/generic uniform strict concavity, physical asymptotic sharpness, smoothing, actual PDE conclusions and KdV2 moments/renormalization/global conclusions remain essential.
