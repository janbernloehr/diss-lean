# Uniform full Hilbert density bounds on inner contours

There exist eta>0, K>0 and one native Hilbert-valued map G, jointly complex analytic on all complex energies times the complex period-one L2 ball of radius eta, such that

    || root(z^2, inclusion(u))^(-1) • G(z^2,u) ||_ell2 <= K/k
    whenever ||u||_L2 < eta and |z-k*pi| = pi/8, for every k>=1.

The same ball and constant precede all complex sources, contour indices, contour points and output indices. The norm is the complete output-index Hilbert norm. The actual source-continued root is defined and nonzero on every one of these inner contours. Its L2 restriction is the already verified actual L2 sheet by source functoriality.

For every real physical period-one L2 source p in this ball, every positive n and every energy E, G(E,u)_n is exactly the existing globally selected physical normalized numerator. The positive free components, nonpositive zero extension and genuine Bochner Kronecker vector periods on the original pi/4 frequency contours all hold on this same complex ball. Means, the first mode, closed gaps and the own output/contour index are included.

The main declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_normalized_numerators_uniform_density`. The rough-space constructor is `exists_hillHminus_actual_native_normalized_density` in the same namespace.

## Proof dependencies

`HillHminusOneUniformSmallTrace` combines actual high-disc asymptotics at zero with a compact finite head. It gives arbitrarily small trace error uniformly over every positive closed pi/4 frequency disc on one complex H^-1 neighborhood.

`HillUniformFrequencySine` obtains a common positive free-sine lower bound on any circle of radius 0<r<pi, and proves explicit radicand perturbation bounds. `HillHminusOneInnerRootBound` chooses a radial source ball inside that trace neighborhood. Every straight source segment remains there, so the inner circles belong to the actual continuation domain. The root square identity supplies a positive lower bound for the actual root, independently of the contour index.

`HillHminusOneInnerDifferentialBound` applies the existing canonical `DiscBounds` Cauchy estimate on outer pi/4 discs and inner pi/8 discs. The exact frequency/energy derivative chain rule and |z|>=pi*k/2 then give actual energy-trace-derivative/root decay C/k.

`InnerFrequencyCircleResolvent` separates the own critical energy by pi^2*k/16. The existing quadratic separation handles different critical indices. A diagonal unit vector and a translated punctured reciprocal lattice bound the full Hilbert norm with constant 48/pi^2.

`HillHminusOneUniformNormalizedDensity` uses the literal filled critical-numerator factor identity and the actual period-inverse transpose with operator norm at most two. Its explicit pointwise bound is 192/pi times the norm of the trace-derivative/root quotient. Existing arbitrarily small common critical localization supplies one neighborhood before every critical index.

`NativeNormalizedDensity` retains the actual period inverse when constructing the complex Miura-normalized family. `PhysicalNormalizedDensity` uses the already proved physical intrinsic-period transfer and exterior uniqueness, so physical matching has no additional period hypothesis.

## Scope and next obligations

This proves a quantitative dependency for the actual normalized differential family near the zero L2 source. The bound concerns squared inner frequency circles and the full output-index norm. It does not assert decay on every energy exterior circle, arbitrary-base or global source analyticity, or physical Abelian-coordinate analyticity.

Next construct uniform regular-phase estimates, including subtraction of the own unit period and analytic filling through its gap. Establish genuine complex gap-width/terminal-divisor sequence bounds and a uniform square-root-action amplitude bound, then realize the physical Abelian coordinate family in its weighted half-shift Hilbert norm. Full Sobolev-scale canonicality, global inverse/Birkhoff realization, Hamiltonian action frequencies, rough-W sharp estimates and infinite-gap/action/PDE-flow conclusions remain essential. All eleven main theorem rows remain OPEN.

## Validation

Prior strict evidence for all 1133 unchanged selected baseline sources; strict dependency-order compilation of eight new proof modules and one unchanged explicitly selected canonical Cauchy helper; then a fresh combined transitive axiom audit of all 1142 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1173 frozen source/checker/provenance hashes, 28 unchanged provenance records and one new verified canonical reuse record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1142-module rebuild is claimed.

Fresh audit: 10465 selected and 32629 imported NLS declarations. Eight new modules, 19 explicit theorems including private helpers and 0 definitions; one byte-identical canonical Cauchy helper explicitly selected, strictly compiled and recorded. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
