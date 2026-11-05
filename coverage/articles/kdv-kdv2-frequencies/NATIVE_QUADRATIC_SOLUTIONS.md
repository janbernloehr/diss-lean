# Native filled-gap quadratic solutions for actual regular differentials

There are one positive complex period-one L2 radius eta, one actual entire native normalized numerator family G, one family of native output Hilbert functions V_k, a positive constant M and one high cutoff N. These choices precede all complex sources, high gap indices, energies and output coordinates. For every k >= N, V_k is jointly complex analytic in the complete Hilbert norm on

    |E - (k*pi)^2| < 3*k/4,    ||u|| < eta.

It solves the actual symmetric gap equation

    P_k(E,u) • d_E V_k(E,u) + (E - tau_k(u)) • V_k(E,u)
      = (-i / U_k(E,periodDouble(u))) • G(E,u) - e_k,

where P_k and tau_k are the existing actual local gap polynomial and midpoint, and U_k is the existing filled complex deflated root. On the complete closed inner disc |E-(k*pi)^2| <= k/4, the full Hilbert norm satisfies

    ||V_k(E,u)|| <= 18*pi*M/k.

No nonzero-gap or off-diagonal output assumption is made. The own unit term is retained. At every real physical source in the same ball, every positive G component is the globally selected physical normalized numerator. Every positive component of the right side is exactly `-i*physicalPsi_n/physicalDeflatedRoot_k - delta_kn` throughout the original filled radius-k disc, including collapsed pairs and means.

The main declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_regular_gap_solutions`. It applies the actual regular-numerator theorem, rather than assuming an unproved physical normalization or period hypothesis. `HillNativeQuadraticSolution` supplies the actual root geometry and shrinks the already vanishing outer Bochner period to radius k/2. It uses the proven root lower bound and chooses the Cauchy radius 3*k/4. The generic estimate pi*rho^2*D/(delta*(rho-a)), with D=4*M/k, delta=k/4 and a=k/4, gives exactly 18*pi*M/k.

## Banach-valued construction

`NativeConvexPrimitive` constructs the actual vector segment integral and proves joint Banach analyticity before identifying its derivative using bounded complex-linear observations. `NativeCircleTransforms` constructs genuine Bochner Cauchy and exterior logarithmic transforms, proves their joint analyticity and compatibility with scalar observation, and derives the vector annular Cauchy decomposition. A zero vector period cancels the logarithm's extra constant term.

`NativeAnnularPrimitive` combines these transforms into a jointly analytic vector primitive on the entire annulus, normalized at a fixed anchor. Its spectral derivative is the original vector density. `NativeCirclePrimitiveBounds` proves full Banach norm bounds directly by the circle arc derivative estimate and Bochner Cauchy kernel estimate. These are full norm estimates, rather than bounds inferred from coordinatewise analyticity.

`NativeQuadraticCauchyEquation` identifies the vector quadratic equation of a strongly analytic Cauchy projection using the previously proved scalar equation and separating bounded linear functionals. `NativeBoundedQuadraticSolution` applies this to the native normalized annular primitive divided by its nonvanishing scalar root. It produces a strongly jointly analytic solution on the filled disc, with the full norm bound used above.

## Remaining main obligations

This proves actual native high-gap quadratic solutions with a uniform full Hilbert bound. Physical terminal-value matching, finite-head regular completion, genuine complex divisor/amplitude sequence bounds and summable phase estimates remain open. The estimate M/k alone, paired with a coarse terminal factor of order k, does not prove summability. It does not yet identify a native analytic physical Abelian-coordinate map or a global Birkhoff inverse.

All eleven main theorem inventory rows remain OPEN. The full s>=-1 Sobolev scale, arbitrary-base/global neighborhoods, canonicality, action Hamiltonian frequency identities, rough-W sharp estimates and infinite-gap/action/PDE-flow conclusions remain essential.

## Validation

Prior strict evidence for all 1164 unchanged selected baseline sources; strict dependency-order compilation of eight new proof modules; then a fresh combined transitive axiom audit of all 1172 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1204 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1172-module rebuild is claimed.

Fresh audit: 10601 selected and 32732 imported NLS declarations. Eight new proof modules, 26 explicit theorems including private helpers and 5 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
