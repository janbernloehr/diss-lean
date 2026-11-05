# Actual common native rough Abelian packet

This is a dependency milestone toward Theorem 1.1. All eleven complete main theorem rows remain OPEN.

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_normalized_abelian_packet` constructs eta>0, C>0 and Z:Hminus-one->ell-two, choosing ONE complex rough ball before EVERY positive index:

```text
Z is complex Banach analytic on ball(0,eta),
Z(0)=0,
norm(Z(q)) <= C*norm(q),
Z(q)_j=0 for j<=0.
```

For EVERY original real L2 potential p whose literal rough inclusion lies in the WHOLE ball and EVERY positive n,

```text
Z(embed(p))_n = hillDirichletAbelianCoordinate(p,n) / sqrt(1+n).
```

The coordinate is defined from the ORIGINAL nonnegative action with sqrt(action) normalization and the ORIGINAL complete infinite Abelian phase. This is the positive Sobolev-minus-one-half weighted Hilbert packet. First/closed gaps, zero endpoint Dirichlet sheets and nonzero means are included. The physical L2 norm need not be small. No caller-provided spectral family, inverse-root bound, physical matching or phase factory is assumed.

## Actual construction and normalization

The same actual Miura/Dirac chart and normalized numerator data supply the native gap-weighted eta sequence E, the bounded analytic midpoint symbol R and the bounded analytic noncentral beta exponential B. The already constructed actual weighted action amplitude symbol M supplies the amplitude. Their native Banach product has positive components

```text
M_n * R_n * E_n * B_n,
M_n = sqrt(1+n) * actual Hill amplitude,
R_n = actual frequency midpoint / (1+n),
E_n = FULL frequency gap * exp(i * own eta),
B_n = exp(i * (COMPLETE signed beta correction - central beta)).
```

The exact labelled spectral transport proves frequency midpoint times FULL frequency gap equals HALF the original Hill ENERGY gap. The central beta subtraction and factor of two are retained. Original prescribed-sheet path integrals prove the full physical phase square, including all own/off-index terms and negative-angle anchor periods.

## Removing the sheet restriction and fixing the original sign

The native complex L2 detector is terminal plus Dirichlet-minus-midpoint. On physical germs it equals the actual sheet divided by the deflated root, so it vanishes when the sheet does. Its free Fourier differential on a positive singleton is 1/2; its analytic germ is therefore nontrivial, even though it vanishes at zero. Physical real-form identity and analytic cancellation remove the nonzero-sheet restriction from the squared-coordinate comparison.

Scalar analytic germs with equal squares agree or differ by one constant minus sign. Actual scalar rough Abelian germs fix a sign for EACH index. These fixed signs form a bounded multiplier, preserving common-ball native analyticity. The resulting sequence vanishes at zero and has a linear norm bound. Original full Abelian coordinates are real analytic along every real scaling line, including closed gaps; analytic continuation then gives physical recovery at EVERY original source in the WHOLE rough ball.

## Scope and remaining work

The proof supplies a genuine native positive negative-half weighted extension of the original physical map near zero. Signed target completion, its actual Fourier derivative and local rough inverse remain next steps. The global/arbitrary-base rough inverse, full canonicality, full s>=-1 scale, actual Hamiltonian frequency identification and frequency/PDE main conclusions remain open. This milestone does not verify a complete main theorem.

## Source reuse and validation

`SHARED_ROUGH_ABELIAN_IMPORT.json` pins shared estimates commit 25e906bba4584c1c1ffbf0d13cd15ce0dfeee814. Its 11 incoming sources and 17 newly reached canonical helpers are unchanged; all previous selected source bytes and provenance records are preserved.

Prior strict evidence retained for all 1767 unchanged selected baseline sources; all 39 new selections strictly rebuilt in dependency order, followed by a fresh combined transitive axiom audit of all 1806 selected modules. New selections: 11 unchanged incoming sources, 17 unchanged canonical helpers and 11 own proof modules. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1847 frozen source/checker/provenance/Mathlib-source hashes, 37 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these 39 selections. No full 1806-module rebuild is claimed.

Fresh audit: 15117 selected and 37183 imported NLS declarations. Eleven own modules contain 26 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
