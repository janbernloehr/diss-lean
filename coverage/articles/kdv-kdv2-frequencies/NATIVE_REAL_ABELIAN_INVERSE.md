# Native local inverse of the actual real Abelian map at zero

This is supporting progress toward Theorem 1.1, not a proof of any complete main theorem. All eleven main theorem rows remain OPEN.

## Exact local result

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_real_abelian_inverse` constructs one native map `Z` on a complex period-one L2 ball and open neighborhoods `V`, `W` of zero in `DeletedCoeff 2 0`. The deleted-coordinate space is the closed kernel of evaluation at zero, with its inherited Hilbert norm. The source represents mean-zero period-one Fourier coefficients. The target chart is exactly the mean-zero part of `WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2`, whose weight is `sqrt (1 + |j|)`.

The projected map `F` is analytic, maps `V` bijectively onto `W`, and has an analytic two-sided inverse `G`. Lifting the target chart gives the original weighted value `Z a.val`, and `Z (G b).val` is exactly the weighted lift of `b`. Every actual real physical source in `V` is mapped by the existing `hillPhysicalAbelianMap`, and the inverse recovers its original Fourier coefficients.

For EVERY target in `W` fixed by physical conjugate Fourier reflection, `G` is fixed by that reflection. The theorem constructs an actual `RealHillWeightedPotential SpectralWeight.one`, with zero mean and Fourier coefficients `(G b).val`, whose existing physical Abelian map is precisely the weighted lift of `b`. These are real source/target neighborhoods inherited from the stated complex Hilbert neighborhoods; the inverse is the restriction of the complex analytic inverse.

## Proof and normalization

The exact native Frechet derivative already proved for the physical Abelian map is `h(j) / sqrt (2 * |j| * pi)` on all complex mean-zero directions. In the weighted target chart this is a diagonal multiplier `sqrt (1 + |j|) / sqrt (2 * |j| * pi)` off zero. Its norm lies between `1/4` and `1`, uniformly in the nonzero integer index, so the derivative is an actual continuous linear equivalence of the deleted-coordinate Hilbert spaces. No invertibility hypothesis is supplied by the caller.

Four unchanged canonical helper files provide deleted-coordinate spaces, invertible diagonal multipliers, and analytic local inverse branches on explicit open sets. Their exact canonical provenance is recorded in `CANONICAL_LOCAL_INVERSE_REUSE.json`.

The reality argument uses a new reusable continuous real-form identity theorem on period-one L2. Agreement with the existing physical map on the physical real slice implies conjugation equivariance of its native holomorphic germ throughout a common complex ball. Local injectivity, together with a smaller inverse neighborhood whose conjugate preimages remain in the injectivity domain, then forces the inverse to preserve the physical real form. This does not assume that an arbitrary inverse branch preserves reality.

## Boundaries and next obligations

The result is local at the zero potential, on the L2 source and half-shift target. It does not establish global bijectivity, canonical Poisson identities, analytic inverses at arbitrary real base points, or the full source/target regularity scale for s >= -1. It does not prove the KdV/KdV2 Hamiltonian action representations, frequency formulas or asymptotics, rough action-domain statements, or the PDE flow conclusions.

Next: connect the actual physical coordinate differentials to the shared Gardner/cotangent calculus, prove canonicality and arbitrary-base derivative invertibility, and use the shared spectral/isospectral geometry for global inverse and regularity results. Each precise main statement remains to be discharged with its original domain, quantifiers, topology and normalization.

## Validation

Prior strict evidence for all 1258 unchanged selected baseline sources; strict dependency-order compilation of ten new proof modules and four unchanged canonical helpers; then a fresh combined transitive axiom audit of all 1272 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1305 frozen source/checker/provenance hashes, 30 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. The old selected ordering is retained as an ordered subsequence. The imported NLS source closure adds exactly the ten new proof modules; the four canonical helpers were already in the imported closure. No repeated full 1272-module rebuild is claimed.

Fresh audit: 11104 selected and 33199 imported NLS declarations. Ten new proof modules, 30 explicit theorems including private helpers and 10 definitions; four canonical helper selections unchanged. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
