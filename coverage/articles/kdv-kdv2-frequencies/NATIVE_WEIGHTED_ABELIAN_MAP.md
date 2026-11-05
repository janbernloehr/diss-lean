# Native weighted physical Abelian map and Fourier derivative

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_fourier_abelian_map` constructs one common complex period-one L2 ball, a positive bound K and one native holomorphic map Z into the actual target `WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2`.

The target weight is exactly `sqrt(1+|j|)`. The map vanishes at zero, its zero output coefficient vanishes throughout the ball, and its full weighted Hilbert norm satisfies

`||Z(u)|| <= K*(||u||+||u||^2)`.

For every real physical period-one L2 source in that same ball, Z equals the existing full signed physical sequence `hillPhysicalAbelianMap`, as a value in the weighted Hilbert space. This is equality of the complete native maps, including all positive and negative indices, first and collapsed gaps and nonzero source means.

For every complex zero-mean direction h and every integer index j, its actual native Frechet derivative satisfies

`((fderiv Z 0)(h))(j) = h(j)/sqrt(2*|j|*pi)`.

The zero-index convention is the existing total inverse convention; h(0)=0. Thus the source Fourier normalization is retained. This is the derivative of the native weighted map, beyond a collection of unrelated scalar germs.

## Uniform amplitudes

The actual filled trace numerator is `T_k(E,u)=D'_u(E)/U_k(E,u)`. Complete complex annular trace estimates and maximum modulus give an energy-disc trace bound. Cauchy then gives `||D'_u||<=C/k` on the radius-k disc. The already proved filled inverse bound `||U_k^-1||<=C*k` bounds T uniformly, and local Cauchy estimates bound its energy derivative by `C/k` on the half-radius disc.

The symmetric midpoint and squared-gap data are analytic for all gaps on one source ball. Their actual root localization controls the complete cosine paths. The sine-squared cosine integral consequently defines native action-to-gap ratios analytic on one complex ball before all positive gaps, with `||ratio_k(u)||<=C/k`.

The existing physical terminal packet identifies the filled trace numerator, its derivatives and every ratio with the actual physical quantities on one common real neighborhood. The exact free ratio is `1/(2*k*pi)`. The normalized analytic family `k*ratio_k` is uniformly bounded, so a uniform Banach Cauchy estimate bounds its variation from the common positive free value. A single smaller complex ball keeps every ratio in the open right half-plane. No infinite intersection of scalar square-root neighborhoods is used.

The native Abelian amplitude is exactly `sqrt(2*ratio_k)/sqrt(2)`. It is analytic for all k on one ball, has the original physical normalization at every real source there, equals `1/sqrt(2*k*pi)` at zero, and satisfies the actual half-shift bound

`sqrt(1+k)*||amplitude_k(u)|| <= C`.

## Weighted assembly and actual map identification

The positive coordinates use the exact gap-division-free factorization

`amplitude_k * (Xi_k-(mu_k-tau_k)) * exp(i*Phi_k)`.

The native unscaled Xi sequence, native Dirichlet-minus-midpoint sequence and actual summed regular phase were proved in preceding milestones. The weighted multiplier bound and the uniform phase exponential bound now realize their product as a genuine weighted Hilbert sequence. Uniform scalar analyticity and the full Hilbert bound give native holomorphic analyticity. Every positive component at every real source in one ball equals the actual physical coordinate; all nonpositive components of this intermediate map vanish.

For the full signed map, source conjugate reflection and target conjugate reflection are applied together. Their two conjugations preserve complex analyticity, including on the infinite-dimensional source. The source involution fixes actual real period-one potentials; the completed sequence therefore agrees exactly with the original signed physical sequence. A uniform bound controls its full weighted norm.

Finally, nearby agreement on genuine unit-period real potentials determines the complete complex L2 derivative. Real scalar curves in the actual weighted physical source and conjugate Fourier real/imaginary directions prove this uniqueness. Applying it to the already proved signed scalar Fourier germs identifies every coefficient of the derivative of Z in the native target.

## Remaining main-theorem obligations

Near zero in L2, the actual signed weighted Abelian coordinate map is now natively holomorphic and has the exact Fourier derivative on mean-zero directions. The uniform analytic amplitudes, actual weighted assembly and full signed physical identification are proved.

This does not establish the global Birkhoff theorem. Local invertibility on the correct mean-zero source and target, canonicality, the full s>=-1 regularity scale and arbitrary-base/global neighborhoods remain to be proved. Hamiltonian action-frequency identities, rough-W/sharp/infinite-gap estimates and actual PDE-flow conclusions also remain essential. All eleven main theorem inventory rows remain OPEN.

## Validation

Prior strict evidence for all 1237 unchanged selected baseline sources; strict dependency-order compilation of twenty-one new proof modules; then a fresh combined transitive axiom audit of all 1258 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1290 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. Complete imported NLS source closure adds exactly the twenty-one new modules. No repeated full 1258-module rebuild is claimed.

Fresh audit: 10998 selected and 33131 imported NLS declarations. Twenty-one new proof modules, 39 explicit theorems including private helpers and 8 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
