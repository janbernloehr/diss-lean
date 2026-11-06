# Actual all-order rough Hill Miura Sobolev regularity

All eleven complete main theorem rows remain OPEN. This proves the exact source/lift/Dirac-gap Sobolev bridge needed for the actual article domains; the full native Hill Birkhoff target regularity, its topology, global rough inversion and frequency/PDE conclusions remain separate obligations.

## Literal product and exact derivative

`weighted_miura_product_uniform_bound` proves the tame bound for the ACTUAL distributional two-L2 Miura product at EVERY nonnegative real order t:

```text
W_t(k)*|product(u,v)_k|
  <= 2^t*(norm(W_t*u)*norm(v) + norm(u)*norm(W_t*v)).
```

The product is the original absolutely convergent coefficient sum, not a caller-supplied replacement. The proof uses the exact additive Sobolev weight bound, genuine summability of every L2 convolution row, the actual positive magnitude convolution and Young's norm bound. The mode k is arbitrary.

`periodOneMiuraProduct_mem_sobolev_sub` proves that two H^t inputs have actual product in H^(t-d), for EVERY d>1/2 and t>=0. The exact identity W_(t-d)=W_d^(-1)*W_t and genuine L2 summability of the reciprocal weight transfer the uniform coefficient bound. At d=1 an explicit native Hilbert product and its norm estimate are supplied. No nonsummable totalized tsum is used.

## Every actual lift gains exactly one derivative

`periodOneMiura_sobolev_iff` quantifies over EVERY original complex H-minus-one source q, EVERY actual L2 lift u and EVERY constant energy shift c solving

```text
periodOneMiura u = q + periodOneL2Inclusion(single_0 c).
```

For EVERY real s>=-1 it proves exactly

```text
q in native H^s  iff  u in native H^(s+1).
```

The sufficient direction needs only the SINGLE finite Sobolev order s+1 of u. The derivative is the literal unit-period 2*pi*i*n multiplier; the product loses one order and the constant shift has finite support.

The necessary direction begins with the GIVEN L2 lift. The fractional product estimate with d=3/4 gives a quarter-order gain from the coefficient equation. At any currently known order t, it recovers every r<=s+1 and r<=t+1/4. Finite induction, starting at order zero and bounded by the requested s+1, reaches that EXACT order. No greater image regularity, lift smallness, reality, finite-gap hypothesis or all-orders premise is assumed. This includes the full negative source interval -1<=s<0 and every higher real order.

## Actual signed canonical gaps

`HillHminusMiuraChart.sobolev_iff_lift_mem` applies the equivalence to EVERY actual complex Hill chart and EVERY source in its ENTIRE domain.

For ANY real L2 lift of the original rough datum, `hillHminus_sobolev_iff_real_miuraDirac_gap_mem` proves

```text
q in H^s  iff  (W_(s+1)(n)*(DiracRight(u,n)-DiracLeft(u,n)))_n in L2.
```

These are the ACTUAL fixed canonical Dirac endpoints of the real diagonal source (u,u), over the FULL signed integer lattice, including zero, negative, low and collapsed indices. The existing proved real-source gap bootstrap supplies the converse. Weighted native source realizations give the forward direction. No initial L2 membership of q is used.

## One chart before every source and order

`exists_hillHminus_real_Miura_all_sobolev_chart` constructs at EVERY real H-minus-one base q0 ONE actual complex analytic Miura chart C and ONE positive shift c^2. The chart and shift are selected BEFORE sources q and orders s. Its entire complex domain satisfies the exact source/lift criterion for ALL s>=-1. On its entire real slice the lift is physical-real, the signed actual Dirac-gap criterion holds for ALL s>=-1, and EVERY positive original Hill endpoint label is retained exactly:

```text
HillLabel(q,2*n-1) = Re(DiracLeft(C.lift q,n))^2 - c^2
HillLabel(q,2*n)   = Re(DiracRight(C.lift q,n))^2 - c^2.
```

The chart's already proved zero-free translated energy and complete ordered spectral enumerations give these identities even at first and collapsed gaps. There is no restriction to a small chart about zero or to original L2 sources.

## Fidelity and remaining work

This is a pointwise native Sobolev membership equivalence for the actual Miura source and its actual signed Dirac gaps. It does NOT yet identify every original Hill Birkhoff target weight, nor prove stronger-topology analytic dependence from membership alone. The original weighted Hill action/gap amplitude estimates, native inverse topology and arbitrary-base/global rough Birkhoff inversion still must be joined to this bridge. Actual full-frequency identification, the KdV2 renormalized correction and physical PDE main conclusions remain open. No complete main theorem is marked verified.

## Shared provenance and validation

The actual gap criterion brings 35 canonical dependency modules into the selected closure. 34 are byte-identical to canonical main at c5bcf6344cd2e2628ae537e98b85bb9ec1849dec. In SourceResonantCenterGapBound the existing global maxHeartbeats 500000 override is removed; its unchanged proof body is validated at the default 200000 budget. Exact source/local hashes and this adaptation are recorded in CANONICAL_MIURA_SOBOLEV_REUSE.json. Canonical main is untouched. All 2376 old selected source bytes and all 39 old provenance records remain unchanged.

Prior strict evidence retained for all 2376 unchanged selected baseline sources. ALL 38 new selections strictly rebuilt in dependency order: 34 byte-identical canonical sources, one canonical proof with its global heartbeat override removed, and three new own proof modules. A fresh combined transitive axiom audit covers all 2414 selected modules. Exact checker/audit/coverage/evidence selections, transitive selected order and reachability, 2457 frozen source/checker/provenance/Mathlib-source hashes, 39 unchanged and one new verified provenance records, private fresh outputs and unchanged clean canonical main verified. The new reachable NLS import closure is EXACTLY these 38 selections. No full 2414-module rebuild is claimed.

Fresh audit: 19159 selected and 41228 imported NLS declarations. Three new own modules contain 15 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no new axioms or proof-checking exceptions. All eleven main theorem rows remain OPEN.
