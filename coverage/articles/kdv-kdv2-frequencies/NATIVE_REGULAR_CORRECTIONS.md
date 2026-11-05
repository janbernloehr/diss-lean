# Actual physical regular corrections on one native Hilbert neighborhood

There exist one positive complex period-one L2 source radius eta, one family beta_k of native output Hilbert functions, one high cutoff N and one positive bound M. These choices precede all complex sources, high gap indices and output coordinates. For every k >= N, beta_k is complex analytic in the full Hilbert norm throughout ||u|| < eta, and ||beta_k(u)|| <= M. All nonpositive output components vanish.

At every real physical period-one L2 source in the same ball, every high gap k and every positive output n, the n-th component is exactly the existing physical regular Abelian correction. The own output n=k is included, with its linear Kronecker term subtracted. Collapsed gaps, means and all positive output indices are included. The cutoff does not depend on the output index; no k>=2*n restriction or countable intersection of output neighborhoods occurs.

The main declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_regular_corrections`. It applies the already identified actual normalized family and its native quadratic solutions, with no unproved physical normalization or terminal-matching condition.

## Moving Dirichlet evaluation

The construction uses the actual scaled Dirichlet root mu_k, selected by the existing logarithmic moment on a contour of radius 1/128 of the old free collar. The old radius lies between k and 8*k, so this root lies within k/16 of the free energy center. It therefore lies inside the new closed radius-k/4 energy disc where the native quadratic solution V_k has full norm at most18*pi*C/k.

The actual scalar terminal factor is

    Xi_k(p) = DirichletSheetRoot(p,mu_k(p)) / filledRoot_k(mu_k(p),p).

`HillScaledComplexDirichletTerminal` proves its joint source analyticity, exact squared local-gap-polynomial identity and bound2*rho*R_old for any prescribed fraction0<rho<=1, uniformly over bounded complex sources before high k. At rho=1/128, this gives ||Xi_k|| <= k/8. The source map p=periodDouble(u), analytic moving mu_k and native vector solution produce the genuine Hilbert vector `i*Xi_k • V_k(mu_k,u)`. Its norm is at most9*pi*C/4. A contractive positive-coordinate projection removes all nonpositive outputs and preserves every positive coordinate.

`HillNativeRegularTerminal` proves this moving evaluation is strongly Banach analytic, with the full vector bound. `PositiveDeletedProjectionBounds` proves the projection is contractive on every supported Banach coefficient space. These are full norm and strong analyticity conclusions, not coordinatewise substitutes.

## Exact physical terminal comparison

`HillPhysicalRegularQuadraticTerminal` extends the existing terminal comparison to every pair of positive indices. The scalar gap equation includes the literal minus-delta_kn term. The existing all-mode cosine-primitive identity gives a linear delta_kn*(theta-pi) term, which cancels against the definition of the physical regular primitive. The endpoint formula retains its exact i*DirichletSheetRoot/physicalDeflatedRoot sign. The proof also handles collapsed gaps.

`HillNativeTerminalPhysical` uses the actual common high-gap real symmetric data, small midpoint/half-gap localization, physical Dirichlet root identification and whole-disc physical filled-root matching. Continuous coordinate evaluation of the native vector differential equation gives every scalar physical equation. One cutoff works before all positive outputs, including n=k, and all bounded real physical sources. The article module applies this matching to the actual family on the same complex source ball.

## Scope and remaining main obligations

This proves common-neighborhood native Hilbert analyticity of the actual HIGH regular corrections, with a uniform coarse full norm bound and exact physical matching. It does not assert decay or summability in the gap index. The estimate ||V_k||<=C/k together with ||Xi_k||<=k/8 gives a bounded correction vector, which alone cannot justify an infinite phase sum.

Still needed are finite-head regular completion on one source neighborhood, genuine complex spectral/divisor/amplitude sequence estimates and summable phase control, followed by actual native Abelian-coordinate analyticity in the weighted half-shift Hilbert norm. Full s>=-1 Sobolev-scale and arbitrary-base/global results, canonicality, the global Birkhoff inverse, Hamiltonian action-frequency identities, rough-W sharp estimates and infinite-gap/action/PDE-flow conclusions remain essential. All eleven main theorem inventory rows remain OPEN.

Read-only shared inspection: estimates434c608 proves native analyticity of indexed Hamiltonian sources; convexityba0cf42 proves a global unweighted ell2 logarithmic Dirichlet norming family over real Hminus-one space with analytic complex neighborhoods. Neither inspected statement supplies the missing k-weighted norming or unscaled energy-gap/terminal sequence estimate. No source was imported from these branches in this milestone.

## Validation

Prior strict evidence for all 1172 unchanged selected baseline sources; strict dependency-order compilation of six new proof modules; then a fresh combined transitive axiom audit of all 1178 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1210 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1178-module rebuild is claimed.

Fresh audit: 10645 selected and 32776 imported NLS declarations. Six new proof modules, 9 explicit theorems including private helpers and 2 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
