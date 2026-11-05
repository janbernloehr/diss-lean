# Actual native regular gap numerators with the own period removed

There exist a positive complex period-one L2 source radius eta, one native jointly complex analytic entire numerator family G, a positive constant M and one cutoff N. On that same ball, for every gap index k>=N, the literal regular numerator

    H_k(E,u) = (-i / U_k(E,periodDouble(u))) • G(E,u) - e_k

is jointly complex analytic in the complete output Hilbert norm on the closed energy disc centered at (k*pi)^2 with radius k, times the common source ball. Here U_k is the existing actual filled complex deflated root and e_k is the k-th unit vector. The full Hilbert norm of H_k is at most M throughout every such disc. All nonpositive output components vanish.

The actual quadratic-root density Q_k^(-1) • H_k is genuinely Bochner circle integrable and its complete vector period is zero on every radius-k boundary. In particular the own output k is included in the subtraction and zero-period statement. No nonzero-gap hypothesis is used.

For every real physical period-one L2 source in the same ball, every high gap k, every positive output n and every energy in its filled disc, the n-th component is exactly

    -i * physicalPsi_n(E) / physicalDeflatedRoot_k(E) - delta_kn.

The positive G components still equal the existing globally selected physical normalized numerators at every energy. G retains full Hilbert numerator and boundary-density C/k estimates and genuine Bochner Kronecker energy periods on every positive radius-k contour, including the finite head. The common ball and cutoff for H precede all complex sources, high gap indices, energies and output indices. Means, high own modes and collapsed pairs are included.

The main declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_regular_gap_numerators`. The literal regularizer and its shared constructor are in `NLS/KdV/HillNativeRegularGapNumerator.lean`.

## Actual quadratic data and root sheet

The old intrinsic free collar has radius `(2*k-1)*pi^2/4`, which differs from k. `HillScaledComplexGapRoot` extends the existing literal normalized quadratic-root chart to any prescribed positive fraction of that collar, uniformly over bounded complex sources before all high k. Fraction 1/16 covers the new energy annuli, because the old radius lies between k and 8k.

`CenteredTwoRootPeriod` extracts an inverse-frequency Taylor coefficient. For arbitrary complex endpoints within radius/16 of the center, including a collapsed pair, it proves the exact reciprocal-root period `-2*pi*i` for the existing negative-leading normalized quadratic formula. It does not assume analytic individual endpoint labels.

`HillRadiusQuadraticData` applies actual two-root localization and the symmetric local gap polynomial, giving joint analyticity, nonvanishing and two-sided norm estimates outside half the radius-k disc, and the exact scalar negative unit period. `HillRadiusRootProduct` then proves that the normalized quadratic root times the actual filled root equals the actual rough/L2 continued root on each radius-k boundary. The square factorization and joint continuity on a connected complex source ball fix the sheet by its already proved free value.

## Native own-period cancellation

`NativeOwnPeriodSubtraction` is a reusable complex Banach-space result. The normalized energy density has raw vector period `2*pi*e_k`; multiplying by `-i` and subtracting the quadratic-root reference density cancels exactly against its scalar period `-2*pi*i`. All integrals are genuine Bochner integrals. The same module uses the Banach maximum modulus principle to bound the full regular numerator norm on the filled disc.

`HillNativeRegularGapNumerator` applies these facts to the actual native family and filled roots, obtaining one source ball, bound and high cutoff before every output. `NativeRegularGapNumerators` instantiates the already identified physical family and the verified whole-disc physical filled-root matching. This gives the literal deflated physical differential minus its own Kronecker term, including at collapsed gaps. The result is not a candidate family conditional on an unproved physical normalization.

## Scope and remaining main obligations

This is a common native analytic, uniformly bounded regular numerator on filled high energy discs, with zero Bochner period. It is not yet the regular primitive or the physical Abelian coordinate map. The high regular family still requires a finite-head completion for an all-gap construction.

Next construct the native Banach-valued quadratic solution/regular primitive with uniform estimates and physical terminal matching. Then prove genuine complex divisor/amplitude sequence bounds and summable phase control, and realize the physical Abelian coordinate family in the weighted half-shift Hilbert norm. Full Sobolev-scale canonicality, the global Birkhoff inverse, Hamiltonian action frequencies, rough-W sharp estimates and infinite-gap/action/PDE-flow conclusions remain essential. All eleven main theorem rows remain OPEN.

## Validation

Prior strict evidence for all 1151 unchanged selected baseline sources; strict dependency-order compilation of six unchanged explicitly selected canonical helpers and seven new proof modules; then a fresh combined transitive axiom audit of all 1164 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1196 frozen source/checker/provenance hashes, 29 unchanged verified provenance records plus one new verified six-file canonical reuse record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1164-module rebuild is claimed.

Fresh audit: 10548 selected and 32679 imported NLS declarations. Seven new proof modules, 12 explicit theorems including private helpers and 1 definition; six byte-identical canonical helpers explicitly selected and strictly compiled with recorded hashes. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
