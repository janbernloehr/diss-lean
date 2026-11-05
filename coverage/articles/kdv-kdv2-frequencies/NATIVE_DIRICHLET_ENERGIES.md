# Native physical Dirichlet energy coordinates with quadratic Fourier remainder

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_dirichlet_energy_coordinates` constructs one common complex period-one L2 ball, one positive bound K and a native Hilbert-valued analytic map D. At every real physical source in that same ball and every positive gap k,

`D(u)(k) = physicalDirichletEnergy_k - freeHillEnergy_k - u(0)`.

All nonpositive complex output coefficients vanish. The ball precedes all source and gap indices, including the first gap and collapsed gaps. The actual mean potential is retained and subtracted exactly; the source itself need not have mean zero.

The map vanishes at zero and has the exact bounded Fourier derivative

`L(u)(k) = -(u(k)+u(-k))/2` for positive k, and zero otherwise.

Its full Hilbert norm satisfies `||D(u)|| <= ||u||+K*||u||^2`, and its actual nonlinear remainder satisfies `||D(u)-L(u)|| <= K*||u||^2`. The remainder is itself a native Hilbert-analytic map with zero derivative at the origin. This is a sequence statement in the actual energy normalization, beyond individual scalar root analyticity.

## Proof of the complex estimate

The actual sine-column Duhamel equation gives a Dirichlet characteristic Born term with remainder at most

`2*exp(H)^3*mass(q)^2/||z||^3`.

After multiplication by twice the energy, its leading term is the cosine Fourier integral minus the potential mean times cos(z). The exact original Fourier integral and a frequency comparison give, for complex period-one L2 sources,

`||2*z^2*S(periodDouble(u),z^2)-2*z*sin(z)`

`- [(-1)^k*(u(-k)+u(k))/2-cos(z)*u(0)]||`

`<=16*exp(1)^3*||u||^2/||z||+2*exp(1)*||z-k*pi||*||u||`.

Finite Fourier approximation transports the actual continuous-potential estimates to L2, with exact coefficient and physical characteristic comparison lemmas. The previously proved complex Dirichlet frequency displacement, together with the sine and cosine Taylor bounds, then gives at the actual Dirichlet zero E in the small energy disc

`||E-freeHillEnergy_k-u(0)+(u(-k)+u(k))/2||`

`<=1024*exp(1)^4*||u||^2/k`.

The positive inverse-index Hilbert majorant realizes the literal remainder as a native ell2 sequence with full norm at most `2048*exp(1)^4*||u||^2`. Uniform scalar coordinate analyticity assembles native Hilbert analyticity, and the quadratic bound proves its zero derivative. Adding the bounded cosine Fourier projection gives D. The existing all-gap physical Dirichlet matching identifies every positive component with the actual physical energy on one common source ball.

## Scope and next obligations

The near-zero native summed regular phase and unscaled terminal sequence from the preceding milestone remain proved. The mean-subtracted Dirichlet energy sequence is now also proved; no further proof of its Fourier leading term or native quadratic remainder is needed.

The actual weighted half-shift Abelian coordinate map still needs genuine complex symmetric gap midpoint estimates after mean subtraction, uniform analytic action/amplitude prefactors, and their physical matching. The coarse radius-k midpoint bounds do not give the missing ell2 estimate. Individual scalar amplitude analyticity and real weighted action summability alone do not supply uniform complex weighted norm bounds.

The full s>=-1 scale, arbitrary-base/global neighborhoods, canonicality/global Birkhoff inverse, Hamiltonian action frequencies, rough-W/sharp/infinite-gap results and PDE-flow conclusions remain essential. All eleven main theorem inventory rows remain OPEN.

## Validation

Prior strict evidence for all 1211 unchanged selected baseline sources; strict dependency-order compilation of ten new proof modules; then a fresh combined transitive axiom audit of all 1221 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1253 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1221-module rebuild is claimed.

Fresh audit: 10834 selected and 32967 imported NLS declarations. Ten new proof modules, 23 explicit theorems including private helpers and 4 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
