# Native physical gap midpoints and Dirichlet displacements

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_gap_midpoint_remainder` constructs one common complex period-one L2 ball, a positive constant K and a native Hilbert-valued analytic map R. At every real physical source in that same ball and every positive gap k,

`R(u)(k) = physicalGapMidpoint_k - freeHillEnergy_k - u(0)`.

The map vanishes at zero, has zero Frechet derivative there and satisfies the full Hilbert bound `||R(u)|| <= K*||u||^2`. Every nonpositive complex output coefficient vanishes. This includes the first and collapsed gaps and sources with nonzero mean.

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_dirichlet_midpoint_coordinates` gives a native Hilbert-valued analytic map A whose positive components at every physical source in one common ball are exactly

`A(u)(k) = physicalDirichletEnergy_k - physicalGapMidpoint_k`.

It vanishes at zero, has the bounded Fourier derivative `L(u)(k)=-(u(k)+u(-k))/2` at positive indices and zero otherwise, and satisfies `||A(u)|| <= ||u||+K*||u||^2` and `||A(u)-L(u)|| <= K*||u||^2`. No individual analytic endpoint labels or gap division are used.

## Complex estimate and exact midpoint identification

The actual trace Duhamel equation has first Born term `(sin(z)/z)*mean(q)` and remainder at most `4*exp(H)^3*mass(q)^2/||z||^2`. Finite Fourier approximation gives a genuine complex L2 remainder bound `16*exp(H)^3*||u||^2/||z||^2`. For equal-mean u,v with `||v||<=||u||`, the linear mean term cancels and the actual trace difference is bounded by `32*exp(H)^3*||u||^2/||z||^2`.

On the complete complex energy annulus `k/2 <= ||E-freeHillEnergy_k|| <= 2*k`, the square-root frequency has imaginary part at most one, norm at least k, distance at most pi/4 and at least `1/(6*pi)` from k*pi. The actual L2 radicands consequently have a quadratic equal-mean difference bounded by `C*||u||^2/k^2`. Cauchy estimates on circles of radius k/4 give a derivative difference of order `||u||^2/k^3`. The actual continued-root separation supplies a uniform positive radicand lower bound on all these annuli on one source ball, including the finite head. Stable logarithmic division therefore bounds the difference of logarithmic derivatives by `C*||u||^2/k^3`.

The actual two-root multiset remains inside the radius-k/16 disc. Its existing multiplicity description restricts to the radius-k disc, identifying zeroth logarithmic moment with two and first moment with twice the existing literal `hillLocalGapMidpoint`. Centering the first-moment difference at the free energy cancels the common zeroth moment. The resulting norm bound has a factor k^2, giving the required inverse-index error.

The comparison potential is the constant potential with the same complex mean, `v=single_0(u(0))`. Exact constant trace translation and free zero uniqueness identify its actual midpoint with `freeHillEnergy_k+u(0)`. Thus, before all positive k and complex sources in one ball,

`||literalMidpoint_k(periodDouble(u))-freeHillEnergy_k-u(0)|| <= C*||u||^2/k`.

The positive inverse-index Hilbert majorant realizes this literal family as R. Bounded coordinate assembly gives native Hilbert analyticity, and the quadratic norm bound gives its zero derivative. Subtracting R from the already proved native mean-subtracted Dirichlet energies gives A. The existing all-gap physical terminal packet identifies both native maps with the actual physical midpoint and Dirichlet displacement, with no remaining matching assumption.

## Remaining main-theorem obligations

The native unscaled terminal sequence, summed regular phase, Dirichlet energies, symmetric midpoint remainder and Dirichlet displacement are now proved near zero in L2. The actual weighted half-shift Abelian coordinate map still needs uniform analytic action/amplitude prefactors, their physical matching and weighted coordinate assembly. Individual scalar prefactor germs and real action summability do not establish uniform complex weighted norm bounds.

The full s>=-1 scale, arbitrary-base/global neighborhoods, canonicality/global Birkhoff inverse, Hamiltonian action frequencies, rough-W/sharp/infinite-gap results and PDE-flow conclusions remain essential. All eleven main theorem inventory rows remain OPEN.

## Validation

Prior strict evidence for all 1221 unchanged selected baseline sources; strict dependency-order compilation of sixteen new proof modules; then a fresh combined transitive axiom audit of all 1237 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1269 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. Complete imported NLS source closure adds exactly the sixteen new modules. No repeated full 1237-module rebuild is claimed.

Fresh audit: 10894 selected and 33027 imported NLS declarations. Sixteen new proof modules, 29 explicit theorems including private helpers and 2 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
