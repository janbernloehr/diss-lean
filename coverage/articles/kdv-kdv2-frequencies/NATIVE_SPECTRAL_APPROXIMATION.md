# Actual finite-gap approximation and original physical moment limits

Actual spectral finite-gap sources are now proved dense in EVERY original native real mean-zero H^m space, using the SAME global inverse of genuine signed-target truncations. Every actual physical intrinsic moment is continuous through closed gaps. The exact finite physical moment formulas along these approximants converge to the TRUE KdV/KdV2 frequency corrections at EVERY native H1/H2 source. Separately, the convergent analytic rough second-moment series near zero now has its entire numerator identified with the ORIGINAL normalized physical numerator, including its removable zero-energy value.

## Exact scope of the limits

For every original native real mean-zero H^m source q, the SAME fixed global native inverse of its symmetric signed-target truncation produces q_N. Every actual original spectral gap with index greater than N is closed, q_N converges to q in the ENTIRE original native norm, and the associated actual physical L2 sources and intrinsic frequencies converge. This proves genuine spectral finite-gap density, rather than only density of an auxiliary coordinate subset.

At every q and all positive n, k and nonnegative moment orders, each actual intrinsic physical moment and every fixed finite moment head converges to its value at q. Continuity includes arbitrary closed own or integration gaps, all endpoints of the moving contour, and infinite-gap sources.

For native H1, the actual finite formula is

`omega1_n(q_N) - (2*pi*n)^3 = -12 * sum_{k=1}^N k*Omega2_nk(q_N)`.

Its right hand side converges to the TRUE independent physical Hamiltonian frequency correction at q. For native H2, the analogous diagonal limit is

`-160*pi^2*sum_{k=1}^N k^3*Omega2_nk(q_N) + 80*sum_{k=1}^N k*Omega4_nk(q_N)`

converging to

`omega2_n(q) - 20*(2*pi*n)*H0(q) - (2*pi*n)^5`.

The moments, contours, canonical roots, action derivatives, mass and factors are the ORIGINAL definitions. The diagonal sums evaluate the moments at q_N. Neither individual moment convergence nor the diagonal formula alone justifies exchanging the source limit and the infinite sum at q. No such interchange or fixed-q physical infinite-series identity is claimed.

## Convergent rough series and physical numerator matching

The existing absolutely convergent second-moment series on a complex H-minus-one ball is retained with analytic moments, analytic correction and locally uniform convergence. Its actual normalized Dirac root factory agrees on every real input with any independently verified global numerator factory. The filled odd divided-difference definition proves equality even at zero translated energy, without cancelling zero. Actual diagonal reality gives reality of the literal Miura lift. A smaller common rough ball excludes the negative chart shift from the spectrum: at zero the exact free spectral labels and positive energy shift prove exclusion, which persists by joint radicand continuity. The known complete physical numerator uniqueness then identifies the series numerator with the ORIGINAL physical numerator at every energy and positive index on that same ball. No numerator-identification or summability premise is assumed in the final existence theorem.

The rough moments still integrate over fixed frequency circles, while the intrinsic physical moments use moving gap circles in energy. The contour deformation, continued primitive/root branches and exact Jacobian comparison remain obligations before using this rough series as the actual infinite-gap physical frequency formula. This milestone identifies the entire numerator only.

## New verified modules

- `NLS/SequenceSpaces/PhysicalRealMeanZeroWeightedTruncation.lean`: Literal symmetric raw truncations preserve real Fourier coefficients and central zero and converge in the entire original weighted Hilbert norm. No weight-symmetry premise is needed.
- `NLS/Articles/KdVKdV2Frequencies/NativeFiniteGapApproximation.lean`: The SAME actual global native inverse of literal symmetric signed-target truncations yields genuine original spectral finite-gap sources. Every actual gap beyond the cutoff is closed. The approximants converge in the entire native real mean-zero H^m norm for every integer m, in physical L2, and in every actual intrinsic hierarchy frequency. Consequently actual spectral finite-gap sources are dense in the entire native source space.
- `NLS/KdV/HillIntrinsicMomentContinuity.lean`: Every original contour-defined intrinsic moment is continuous on the entire physical real L2 source, including closed selected and integration gaps. A local recentered primitive, canonical root/numerator joint continuity and a proved nonreal circle-integral comparison control the whole moving contour. Every finite weighted moment head is continuous. One private generic moving-section continuity lemma is included.
- `NLS/Articles/KdVKdV2Frequencies/NativeSpectralMomentApproximation.lean`: Every fixed actual physical moment and fixed finite head converges along the genuine finite-gap approximants at every native source. At each approximant the actual KdV/KdV2 frequency corrections equal the original finite moment formulas with exactly the same cutoff. These diagonal finite formulas converge to the TRUE intrinsic corrections at all native H1/H2 sources, retaining -12, -160*pi^2, 80 and the actual mass subtraction. The source in these sums is the approximant q_N; this does not exchange the source limit with the fixed-q infinite sum.
- `NLS/KdV/HillHminusMiuraPhysicalNumerators.lean`: Two independently verified Dirac root factories give exactly the same filled energy numerator at every real input, including zero translated energy. Actual diagonal reality implies reality of the literal Miura lift. The rough series numerator equals the ORIGINAL physical normalized numerator on a valid real chart, with chart membership, reality and outside-shift conditions explicit; these conditions are discharged on the common ball in the next module.
- `NLS/KdV/HillHminusPhysicalMiuraFrequencySeries.lean`: One genuinely constructed complex H-minus-one ball and one actual root factory retain analytic moments of every order, absolute weighted second-moment summability, an analytic correction and locally uniform series convergence. On EVERY original real physical source in that SAME ball, the series numerator is exactly the original normalized numerator at every energy and positive index. The outside-shift exclusion is proved by free spectral labels and openness; no numerator agreement or summability is assumed. The series moments still use rough frequency circles, whose comparison with the intrinsic moving physical gap contours remains separate.

## Validation and remaining main obligations

All 2941 prior selected sources remain byte-identical and retain their strict build evidence. All SIX new own modules were strictly rebuilt in dependency order AFTER freezing 2997 selected-source/checker/provenance/pinned-Mathlib-source hashes. A fresh combined transitive axiom audit covers all 2947 selected modules and every imported NLS declaration. Exact ordered selection, reachability and the exact six-module import-closure increase were checked. The entire transitive audit loop, collectAxioms traversal, permitted axioms and imported NLS scope are byte-identical to the published baseline. The selection now has 24 private chunks, each at most 128 names; the actual 2947-name bidirectional NameSet probe rejects insertion/deletion mismatches. All 47 prior provenance records remain unchanged and verified against their source commits; there is no new canonical reuse. All outputs are private and fresh through the article overlay. Canonical main and pinned Mathlib are unchanged. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are permitted. This is a SIX-module incremental rebuild retaining baseline strict evidence, not a full 2947-module rebuild.

Fresh audit: 23111 selected declarations and 45181 imported NLS declarations. Six own modules contain 24 explicit theorems, including one private generic moving-section lemma. No sorry, new axiom, option or linter exception.

COMPLETE Theorem 1.1 remains VERIFIED and byte-identical; the other ten COMPLETE main theorem rows remain OPEN. The diagonal approximation identities do not establish convergence of the infinite moment sum evaluated at the fixed original source. The rough series numerator match does not yet identify the rough frequency-circle moments with the intrinsic moving physical gap-contour moments. Prove those contour/branch comparisons and the required uniform tails or analytic limit identification next. Sharp infinite-gap summability and locally uniform asymptotics, full low-regularity sequence-valued analytic target bounds, compact derivative corrections, concavity/local inverses, fixed-mass bounds and actual PDE solution conclusions remain essential.
