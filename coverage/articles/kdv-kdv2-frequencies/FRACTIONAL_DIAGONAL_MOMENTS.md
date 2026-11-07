# Actual fractional raw diagonal moments

A raw diagonal-moment dependency of Theorem 1.2(iii) is proved in the ORIGINAL native H^(t-1) source norm. For EVERY t>=0 and EVERY real native base, ONE actual physical frequency chart is fixed BEFORE all 0<=u<=min(1,t). For EACH such u, ONE full COMPLEX native neighborhood, ONE tail cutoff and ONE M>=0 precede ALL sources a there and ALL signed selected labels k. With the SAME actual Miura source psi and literal gap gamma_k, the ACTUAL raw diagonal moment satisfies (1+abs(k))^u*norm(M_kk^(2)(psi)-pi*gamma_k^2/4)<=norm(gamma_k)^2*M. The two literal gap factors remain on the right, including closed gaps and infinite support. No division by a selected gap or density argument in a stronger source topology is required.

## Source obligation and exact scope

Theorem 1.2(iii), PDF page 4, requires sharp locally uniform asymptotics for the FULL corrected KdV frequency in the ORIGINAL action topology. Its spectral proof uses the primitive, normalization quotients, diagonal moments and weighted action cancellation. This milestone proves the raw diagonal-moment dependency, with the exact leading constant pi/4 and full complex source neighborhoods.

`NLS.Articles.KdVKdV2Frequencies.theorem_1_2_iii_diagonal_moment_dependency`

in `NLS/Articles/KdVKdV2Frequencies/Theorem12DiagonalMomentDecay.lean` constructs one ACTUAL physical chart A at every real native H^(t-1) base for every t>=0. This SAME chart precedes EVERY auxiliary exponent 0<=u<=min(1,t). For each u, `A.HasFractionalDiagonalMomentBounds u q` supplies a full complex native open neighborhood T containing q and contained in A.domain, one integer cutoff and one constant before every source in T and every large signed index.

Its raw moment is exactly `A.physical.atlas.moment k k 2 psi`, and psi is exactly `hillMiuraDiagonal (A.physical.psi.miura.lift (originalRoughInclusion a))`. The gap is the actual periodic gap of this SAME psi. The source topology is the original native weighted coefficient norm, without a replacement norm or an open-gap premise. Arbitrary infinite support and all collapsed gaps are included.

## Proof through the actual primitive and quotient

The previously verified critical-root quotient error has fractional decay. The actual primitive comparison also contains the product of the selected gap length with the actual critical-gap quotient coefficient. The actual weighted source factory bounds `(1+abs(k))^t*norm(gamma_k)`, and the genuine local critical-quotient norm bounds its coordinate. Therefore, for u<=t and u<=1, the ACTUAL primitive minus its free root primitive has error at most `norm(gamma_k)*M*(1+abs(k))^(-u)`, uniformly in the entire boundary parameter interval and both boundary sides.

The already verified squared-primitive comparison turns this into an error at most `norm(gamma_k)^2*M*(1+abs(k))^(-u)` on the entire actual complex segment. It holds for every compatible actual primitive family. Independence of the primitive square from its ambient source neighborhood transfers this estimate to the SAME actual moment atlas.

The filled-psi quotient is the actual normalized psi root family with its omitted label filled by its moving midpoint. Its fractional error, with omitted label equal to the selected label, combines with the squared-primitive error in the exact diagonal-moment coefficient estimate. The scalar weight inequalities use only `(1+abs(k))^u>=1`; they lose no requested u exponent.

Finally the exact actual moment factorization `M_kk^(2)=gamma_k^2/4*(pi+c_k)` gives the raw error. This identity and its coefficient bound already include collapsed gaps. The transfer to the raw estimate divides only by the positive Sobolev weight and the constant four. It NEVER divides by a selected gap and NEVER assumes density in a stronger weighted topology.

## Exact physical and native transfer

The existing actual native parameterization supplies both a genuinely complex analytic normalized source map and the exact full-complex source identity to the physical Miura lift. Pulling back the source neighborhood along this analytic map gives a full complex open neighborhood in the ORIGINAL native norm. One actual physical chart is fixed before every u. No abstract substitute sequence, assumed asymptotic, caller-supplied chart or stronger-topology density premise occurs in the article theorem.

## Modules

- `NLS/SequenceSpaces/WeightedGapErrorAlgebra.lean`: Three scalar weight inequalities for actual primitive, square and diagonal-coefficient errors, retaining literal gap factors without dividing by a gap.
- `NLS/ZakharovShabat/SourcePrimitiveFractionalGapBound.lean`: The ACTUAL Abelian primitive has a weighted fractional relative-gap error on full complex normalized Sobolev-source neighborhoods, uniformly before every compatible Cauchy family, signed selected label, gap parameter and boundary side. All closed gaps remain included.
- `NLS/ComplexAnalysis/WeightedQuadraticRemainder.lean`: An exact quadratic factorization transfers weighted coefficient error to raw moment remainder, retaining the squared factor at zero as well as nonzero values.
- `NLS/ZakharovShabat/SourceSquareFractionalGapBound.lean`: The ACTUAL filled squared primitive plus its selected polynomial has weighted error bounded by the SQUARED actual gap times one constant, on every entire complex gap and on one full complex weighted-source neighborhood.
- `NLS/ZakharovShabat/SourceDiagonalMomentFractionalBound.lean`: The ACTUAL raw diagonal second moment differs from pi*gamma_k^2/4 by a fractionally decaying error bounded by TWO literal gap factors. The estimate uses the actual filled-psi quotient and squared primitive, independent of the ambient primitive neighborhood, and includes collapsed gaps without a density argument.
- `NLS/KdV/PhysicalFractionalDiagonalMomentBounds.lean`: For ONE actual physical frequency parameterization, its ACTUAL raw diagonal moments satisfy the same weighted gap-squared remainder on one full complex parameter neighborhood in the ORIGINAL norm. Exact native-to-physical compatibility is proved, and every chart and gap is the actual one.
- `NLS/Articles/KdVKdV2Frequencies/Theorem12DiagonalMomentDecay.lean`: A raw diagonal-moment dependency of Theorem 1.2(iii) is proved in the ORIGINAL native H^(t-1) source norm. For EVERY t>=0 and EVERY real native base, ONE actual physical frequency chart is fixed BEFORE all 0<=u<=min(1,t). For EACH such u, ONE full COMPLEX native neighborhood, ONE tail cutoff and ONE M>=0 precede ALL sources a there and ALL signed selected labels k. With the SAME actual Miura source psi and literal gap gamma_k, the ACTUAL raw diagonal moment satisfies (1+abs(k))^u*norm(M_kk^(2)(psi)-pi*gamma_k^2/4)<=norm(gamma_k)^2*M. The two literal gap factors remain on the right, including closed gaps and infinite support. No division by a selected gap or density argument in a stronger source topology is required.

## Validation

All 3414 prior selected sources and all 55 prior provenance records remain byte-identical. The exact new import closure is seven own modules containing nine explicit public theorems; there are NO newly imported or reused canonical modules and NO new provenance records. All seven new selections were strictly rebuilt in dependency order AFTER freezing 3479 selected-source/checker/provenance/pinned-Mathlib-source hashes. The fresh full transitive audit covers all 3421 selections and EVERY imported NLS declaration: 26131 selected and 48201 imported declarations. The ENTIRE audit loop, collectAxioms traversal, allowed axioms and imported-NLS scope remain byte-identical to baseline. The 3421-name bidirectional NameSet probe rejects insertion/deletion mismatches. Exact ordered selections, dependency order, reachability, 27 private chunks of at most 128 names, private fresh outputs, overlay targets, unchanged canonical main and pinned Mathlib are verified. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a seven-module incremental rebuild retaining all prior strict evidence, not a full 3421-module rebuild.

No sorry, added axiom, raised limit or linter exception. All 55 existing exact provenance records are unchanged.

## Remaining main obligations

Complete Theorem 1.1 and Corollary 1.4 remain VERIFIED; the other nine complete main rows remain OPEN. Complete source clauses Theorem 1.2(ii) and (iv), and all regularity-dependent target clauses of (i), remain verified. Previous sharp actual off-diagonal and fractional normalization-quotient dependencies are retained. Full Theorem 1.2(iii) still requires the first weighted action and opposite-index moment cancellation, the sharp locally uniform FULL corrected-frequency remainder, transfer to the ORIGINAL action topology with the SAME global weak frequency calibration, and the high-regularity O(1/n) conclusion. The consolidated complete Theorem1.2 remains essential. Global Hessian nonpositivity/generic uniform strict concavity, physical asymptotic sharpness, smoothing, actual PDE conclusions and KdV2 moments/renormalization/global conclusions also remain open.
