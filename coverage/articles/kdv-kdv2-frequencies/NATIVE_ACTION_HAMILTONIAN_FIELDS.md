# Native analytic physical action Hamiltonian fields

This is supporting progress toward Theorem 1.1 and its canonical Birkhoff realization. All eleven complete main theorem rows remain OPEN.

## Exact result

`NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_action_hamiltonian_fields` chooses ONE complex L2 ball, the actual native weighted Abelian map `Z`, and a pair of complex open mean-zero source/target neighborhoods `V`, `W` with analytic two-sided inverse `G`, BEFORE every positive action index. The target remains exactly `hillAbelianTargetWeight SpectralWeight.one`, with weight `sqrt (1 + |j|)`; the mean-zero target chart is obtained from its actual weight isometry.

For every positive index `m`, the theorem constructs a vector field `X m` analytic on the SAME complex neighborhood `V`. With `F` the actual mean-zero weighted Abelian chart, its formula is

```text
X_m(a) = dG(F(a)) [A_m F(a)],
dF(a) [X_m(a)] = A_m F(a),
```

where `A_m` is the literal signed coordinate rotation: `+i` on index `m`, `-i` on index `-m`, and zero at all other indices. The weighted generator, mean-zero projection and inverse lift are proved explicitly; no replacement by a norm-equivalent target is used.

At EVERY actual mean-zero real physical source in `V`, `X_m` equals the original physical action Hamiltonian direction, expressed in unit-period Fourier coefficients. This is the even-index sample of `hillL2TracePeriodDirection`, whose weak Hamiltonian identity and uniqueness are already proved in the shared library. The native derivative identity holds as an equality of weighted Hilbert-space values, not just as an assumed scalar coordinate law. All positive and negative indices and all collapsed gaps are included. No separate neighborhood is chosen for individual actions or output modes.

## Proof

An exact continuous inverse to the original physical source embedding identifies genuine unit-period real source neighborhoods with the original period-two even real source space. Raw weighted evaluation and canonical parity sampling transport the already proved scalar physical coordinate variation laws to the actual native Frechet derivative. The positive and negative laws give the exact opposite signs. A continuous real-form identity forces the native zero output mode to vanish on the entire complex ball from actual physical matching.

The complete signed component identities assemble into the native weighted vector equality. Restriction to the closed mean-zero source and the exact weighted target chart gives the projected derivative identity. The analytic inverse and chain rule then prove both the global-in-the-chart pushforward law and equality of the pulled-back analytic vector field with the physical Hamiltonian vector at every real source.

Two unchanged canonical files, parity sampling and raw weighted coefficient evaluation, are newly selected and recorded in `CANONICAL_ACTION_ROTATION_REUSE.json`. Reusable source adapters, weighted rotation operators and analytic inverse vector-field transport lemmas are in the shared library; the unconditional physical existence statement is in the article directory.

## Remaining main obligations

This proves analytic action vector fields and their exact diagonalization in a local near-zero L2 chart. It does not prove every coordinate-coordinate Gardner bracket, global canonicality, global bijectivity, arbitrary-base inverse charts, or the full s >= -1 regularity scale. No KdV/KdV2 Hamiltonian frequency formula, action-domain extension, sharp frequency asymptotic, compact derivative, generic concavity or PDE main conclusion is marked complete.

Next: establish actual rough coordinate/cotangent extensions and the full canonical bracket identities, use the shared Gardner and endpoint/isospectral geometry to obtain arbitrary-base and global Birkhoff conclusions, and then discharge the Hamiltonian action-frequency and spectral/PDE main theorem clauses.

## Validation

Prior strict evidence for all 1272 unchanged selected baseline sources; strict dependency-order compilation of eight new proof modules and two unchanged canonical helpers; then a fresh combined transitive axiom audit of all 1282 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1316 frozen source/checker/provenance hashes, 31 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. The old selected ordering is retained as an ordered subsequence. The imported NLS source closure adds exactly the eight new proof modules; both canonical helpers were already in the imported closure. No repeated full 1282-module rebuild is claimed.

Fresh audit: 11197 selected and 33265 imported NLS declarations. Eight new proof modules, 32 explicit theorems including private helpers and 7 definitions; two canonical helper selections unchanged. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
