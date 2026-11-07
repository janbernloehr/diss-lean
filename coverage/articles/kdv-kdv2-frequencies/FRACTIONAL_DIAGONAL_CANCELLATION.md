# Actual fractional diagonal moment/action cancellation

The ACTUAL diagonal moment/action cancellation required for Theorem 1.2(iii) is proved in the ORIGINAL native H^(t-1) source norm. For EVERY t>=0 and EVERY real native base, ONE actual physical frequency chart is fixed BEFORE all 0<=u<=min(1,t). For EACH such u, ONE full COMPLEX native neighborhood, ONE tail cutoff and ONE M>=0 precede ALL sources a there and ALL positive selected labels n. The ACTUAL corrected diagonal contribution obeys (1+n)^(u-1)*norm(correction_n+12*J_n1-offDiagonalCorrection_n)<=norm(gamma_n)^2*M. Here J_n1 is the literal actual first weighted Dirac action and gamma_n is the SAME physical Miura gap. On EVERY original real physical source represented in that neighborhood, the SAME bound is proved with the exact original counterterm +6I_n, using the proved identity I_n=2*J_n1. The first weighted action, diagonal moment and opposite-index moment are all actual quantities; both gap factors remain at every collapsed gap and for infinite support.

## Source obligation and exact scope

Theorem 1.2(iii), PDF page 4, requires sharp locally uniform asymptotics of the FULL corrected KdV frequency in the ORIGINAL action topology. This milestone proves the ACTUAL diagonal cancellation required in that argument, retaining the literal selected gap squared and the source normalization +6I.

`NLS.Articles.KdVKdV2Frequencies.theorem_1_2_iii_diagonal_cancellation_dependency`

in `NLS/Articles/KdVKdV2Frequencies/Theorem12DiagonalCancellationDecay.lean` constructs one ACTUAL physical chart A at every real native H^(t-1) base for every t>=0. This SAME chart precedes EVERY auxiliary exponent 0<=u<=min(1,t). For each u, `A.HasFractionalDiagonalCancellationBounds u q` supplies a full complex native open neighborhood containing q and contained in A.domain, one integer cutoff and one constant before every source there and every large positive index.

The predicate explicitly proves TWO forms of the SAME bound on that SAME neighborhood. On the full complex neighborhood the counterterm is +12 times the actual first weighted Dirac action. At EVERY represented original real Hill potential, the counterterm is literally +6 times its original real gap action. The coefficient identification I_n=2*J_n1 is proved with the SAME physical Miura lift, normalization family and energy shift. It is not a caller-supplied compatibility hypothesis.

## Raw action proof at all gaps

The exact normalized-action boundary formula gives `gamma_n^2*NWA0=(2/pi)*integral(delta_n*sin(theta)*boundary_n(theta))`. The corresponding free boundary integral is exactly `gamma_n^2/4`. Subtracting under the integral and applying the ACTUAL primitive error gives `norm(gamma_n^2*NWA0-gamma_n^2/4)<=norm(gamma_n)^2*E` with exact constant one. The argument includes gamma_n=0 and never divides by a selected gap.

The exact affine normalized-action identity writes NWA1 as its midpoint times NWA0 plus a regular boundary integral. Subtracting `n*pi*gamma_n^2/4` at the RAW level separates the affine remainder, the raw zeroth-action error, and the midpoint displacement. The boundary, gap and midpoint factories give ONE bound on a full complex source neighborhood. The exact weight loss is one: w_(u-1)=w_u/w_1. Hence `w_(u-1)*norm(J_n1-n*pi*gamma_n^2/4)<=norm(gamma_n)^2*M` for every large signed index, on one full complex normalized Sobolev-source neighborhood.

## Actual moment/action cancellation

Write eA=J_n1-n*pi*gamma_n^2/4 and eD=M_nn-pi*gamma_n^2/4. Then the exact raw identity is

`-12*n*(M_nn-M_n,-n)+12*J_n1=12*(eA-n*eD+n*M_n,-n)`.

The actual diagonal-moment estimate supplies the bound for eD at weight w_u, and w_(u-1)*abs(n)<=w_u transfers the original index factor. The actual off-diagonal cubic moment formula at the opposite label has the exact reciprocal kernel factor `abs(n)*abs(1/(n-(-n)))=1/2`. Physical Miura reflection proves gamma_-n=gamma_n at every COMPLEX source. Thus the opposite raw moment contributes at most a bounded third gap factor. The common local gap bound retains two gap factors in the final estimate.

All three terms use actual moments and actions from their verified atlases. The proof covers every collapsed gap and infinite support. No normalized quotient across a selected gap, finite-open-gap density argument in a stronger topology, or substitute action sequence is used.

## Original native and physical calibration

The native source parameterization is genuinely complex analytic in the ORIGINAL H^(t-1) norm and agrees EXACTLY with the SAME physical Miura lift under the literal original coefficient inclusion. Pulling back the common source neighborhood gives a full complex native open set. The actual physical correction minus its actual off-diagonal part is algebraically the same raw diagonal expression. The proved original-action matching calibrates its counterterm to +6I at every represented original real physical source. ONE chart precedes all u.

## Modules

- `NLS/ZakharovShabat/SourceRawActionGapError.lean`: A generic ACTUAL raw zeroth action error follows from the primitive boundary error, with TWO literal gap factors and exact constant one. The boundary-integral proof includes collapsed gaps and never divides by the selected gap.
- `NLS/ComplexAnalysis/WeightedAffineQuadraticRemainder.lean`: Two generic weighted complex inequalities retain quadratic gap factors through affine first-action subtraction and through the exact -12 moment / +12 weighted-action cancellation. The selected factor may vanish.
- `NLS/ZakharovShabat/SourceFirstWeightedActionFractionalBound.lean`: The ACTUAL first weighted action minus pi*n*gamma_n^2/4 has weighted bound (1+abs(n))^(u-1)*norm(error)<=norm(gamma_n)^2*M for every signed large label. One full complex normalized weighted-source neighborhood supports the same bound, including collapsed gaps.
- `NLS/ZakharovShabat/SourceDiagonalCancellationFractionalBound.lean`: The ACTUAL combined -12*n*(M_nn-M_n,-n)+12*J_n1 has the same fractional weighted gap-squared bound whenever the opposite selected gap equals the own gap. The proof uses the actual first action and diagonal moment and the exact reciprocal opposite-index kernel 1/2. The proved physical Miura reflection supplies the equality downstream.
- `NLS/KdV/PhysicalFractionalDiagonalCancellation.lean`: The ACTUAL physical corrected diagonal contribution has this bound on one full complex parameter neighborhood in the ORIGINAL norm. An exact algebraic identity identifies the diagonal contribution and a separate proved original-action identity calibrates +12*J_n1 to the literal +6I_n at EVERY represented original real source. Both forms and all quantifiers are explicit in HasFractionalDiagonalCancellationBounds.
- `NLS/Articles/KdVKdV2Frequencies/Theorem12DiagonalCancellationDecay.lean`: The ACTUAL diagonal moment/action cancellation required for Theorem 1.2(iii) is proved in the ORIGINAL native H^(t-1) source norm. For EVERY t>=0 and EVERY real native base, ONE actual physical frequency chart is fixed BEFORE all 0<=u<=min(1,t). For EACH such u, ONE full COMPLEX native neighborhood, ONE tail cutoff and ONE M>=0 precede ALL sources a there and ALL positive selected labels n. The ACTUAL corrected diagonal contribution obeys (1+n)^(u-1)*norm(correction_n+12*J_n1-offDiagonalCorrection_n)<=norm(gamma_n)^2*M. Here J_n1 is the literal actual first weighted Dirac action and gamma_n is the SAME physical Miura gap. On EVERY original real physical source represented in that neighborhood, the SAME bound is proved with the exact original counterterm +6I_n, using the proved identity I_n=2*J_n1. The first weighted action, diagonal moment and opposite-index moment are all actual quantities; both gap factors remain at every collapsed gap and for infinite support.

## Validation

All 3421 prior selected sources and all 55 prior provenance records remain byte-identical. The exact new import closure is six own modules containing nine explicit public theorems; there are NO newly imported or reused canonical modules and NO new provenance records. All six new selections were strictly rebuilt in dependency order AFTER freezing 3485 selected-source/checker/provenance/pinned-Mathlib-source hashes. The fresh full transitive audit covers all 3427 selections and EVERY imported NLS declaration: 26167 selected and 48237 imported declarations. The ENTIRE audit loop, collectAxioms traversal, allowed axioms and imported-NLS scope remain byte-identical to baseline. The 3427-name bidirectional NameSet probe rejects insertion/deletion mismatches. Exact ordered selections, dependency order, reachability, 27 private chunks of at most 128 names, private fresh outputs, overlay targets, unchanged canonical main and pinned Mathlib are verified. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a six-module incremental rebuild retaining all prior strict evidence, not a full 3427-module rebuild.

No sorry, added axiom, raised limit or linter exception. All 55 existing exact provenance records are unchanged.

## Remaining main obligations

Complete Theorem 1.1 and Corollary 1.4 remain VERIFIED; the other nine complete main rows remain OPEN. Complete source clauses Theorem 1.2(ii) and (iv), and all regularity-dependent target clauses of (i), remain verified. Previous sharp actual off-diagonal, normalization-quotient and raw diagonal-moment dependencies are retained. The actual raw first weighted action and opposite-index diagonal cancellation are now proved. Full Theorem 1.2(iii) still requires combining this corrected diagonal bound with the off-diagonal estimate and weighted squared-gap sequence to obtain the sharp locally uniform FULL frequency remainder, transferring that result to the ORIGINAL action topology with the SAME global weak frequency calibration, and the full high-regularity O(1/n) conclusion. The consolidated complete Theorem1.2 remains essential. Global Hessian nonpositivity/generic uniform strict concavity, physical asymptotic sharpness, smoothing, actual PDE conclusions and KdV2 moments/renormalization/global conclusions also remain open.
