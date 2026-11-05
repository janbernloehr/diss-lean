# Native Hilbert analyticity of the actual summed regular phase

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_summed_regular_corrections` constructs one common complex period-one L2 ball and a bounded native Hilbert-valued analytic map. At every real physical source in the same ball, every positive component equals the existing `hillSummedRegularAbelianCorrection`. All nonpositive complex components vanish. The source ball precedes all gap and output indices, including first gaps, own modes, collapsed gaps and means.

The proof sums the actual regular correction vectors as an absolutely convergent Bochner series. It uses the newly proved complex Hilbert estimate for the unscaled Dirichlet terminals, rather than the former coarse indexwise terminal bound. This supplies the previously missing sequence control for the regular phase near zero.

## Actual complex sequence estimates

The literal terminal sequence `hillNativeDirichletGapTerminals` is native Hilbert analytic on one complex source ball, agrees with every existing unscaled `hillScaledComplexDirichletGapTerminal` at the positive gap indices and vanishes at nonpositive indices. Its full norm is bounded by K*(||u||+||u||^2). This estimate is proved for complex sources; real pointwise summability and continuity are not used to infer it.

The proof derives the actual diagonal monodromy difference from sine and cosine Duhamel formulas. Its first Born term is a sine Fourier integral; the remainder is bounded by 4*exp(H)^3*mass(q)^2/||z||^2. Frequency comparison, the exact Fourier integral and finite Fourier approximation give the L2 bound

`||z*sheetRoot(periodDouble(u),z^2)-(-1)^k*(u(-k)-u(k))/(2*i)||`

`<=16*exp(1)^3*||u||^2/||z||+2*exp(1)*||z-k*pi||*||u||`.

For the actual complex Dirichlet zero in the proved small energy disc, the actual characteristic equation gives `||sqrt(mu_k)-pi*k|| <=8*exp(1)^2*||u||/k` and `k<=||sqrt(mu_k)||`. Consequently,

`k*||sheetRoot(periodDouble(u),mu_k)||`

`<= (||u(-k)||+||u(k)||)/2+32*exp(1)^3*||u||^2/k`.

Actual continued-root separation, the genuine quadratic/root product and maximum modulus give `||filledRoot_k(E,periodDouble(u))^(-1)||<=C*k` on complete closed radius-k energy discs, uniformly before all positive k. These estimates produce the unscaled terminal ell2 bound with a Fourier majorant and a positive inverse-index Hilbert sequence. No analytic individual periodic endpoint labels are assumed.

## From terminals to the actual summed phase

`exists_hillPhysical_native_regular_correction_hilbert_control` constructs the actual regular correction family beta and one native analytic Hilbert majorant a on a common source ball. The full output norm satisfies

`||beta_k(u)|| <= A*||a(u)(k)||/k`, with `||a(u)||<=B`.

Every positive beta component retains exact physical correction matching. Cauchy-Schwarz against the positive inverse-index Hilbert sequence proves absolute Bochner summability. The reusable `Coeff.analytic_tsum_of_hilbert_control` also proves native Hilbert analyticity of the sum: scalar coordinate sums have locally bounded actual ell1 realizations; the full Hilbert norm bound then assembles the analytic map. No common pointwise summable majorant or output-dependent source intersection is required.

Evaluation through bounded coordinate maps and exact positive-index reindexing identify the sum with the existing physical summed correction. The native phase norm is bounded by 2*A*B. This is the correction phase before exponentiation, in the output Hilbert norm.

## Remaining main theorem obligations

Native physical Abelian coordinates in weighted half-shift Hilbert norm still require genuine complex amplitude/Dirichlet/symmetric spectral sequence estimates. The summed regular phase is now proved near zero; do not repeat the finite-head, terminal, physical correction or phase work.

The full s>=-1 scale, arbitrary-base and global neighborhoods, canonicality/global Birkhoff inverse, Hamiltonian action frequencies, rough-W/sharp/infinite-gap results and PDE-flow conclusions remain essential. All eleven main theorem inventory rows remain OPEN.

## Validation

Prior strict evidence for all 1197 unchanged selected baseline sources; strict dependency-order compilation of fourteen new proof modules; then a fresh combined transitive axiom audit of all 1211 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1243 frozen source/checker/provenance hashes, all 30 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1211-module rebuild is claimed.

Fresh audit: 10778 selected and 32909 imported NLS declarations. Fourteen new proof modules, 23 explicit theorems including private helpers and 4 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
