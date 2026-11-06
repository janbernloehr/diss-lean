# Every exact native Sobolev endpoint of the SAME actual rough inverse

All eleven complete main theorem rows remain OPEN. This proves the ALL-order membership part of the actual local rough Birkhoff source/target regularity. Stronger Sobolev topology and analyticity, arbitrary-base/global rough inversion and frequency/PDE main conclusions remain separate obligations.

## Global ORIGINAL Hill-gap Sobolev criterion

`NLS.KdV.hillHminus_sobolev_mem_iff_original_energy_gap_mem` proves, for EVERY real original H-minus-one source q and EVERY real s>=-1:

```text
q in native H^s  iff  (W_s(n)*Gamma_n(q))_(n>0) belongs to L2,
Gamma_n(q) = ORIGINAL HillLabel(q,2*n) - ORIGINAL HillLabel(q,2*n-1).
```

The positive gap sequence is zero extended to nonpositive signed indices. No initial L2 membership of q, finite-gap hypothesis, support restriction or small source norm is assumed. The bottom label is not mistaken for a positive gap.

The proof chooses an actual real L2 Miura lift with an outside-spectrum energy translation. Complete original Hill labels give the exact factorization Gamma_n=(Re DiracRight_n+Re DiracLeft_n)*(DiracRight_n-DiracLeft_n). The actual canonical endpoint displacements are genuinely L2, hence bounded. Their norms control the high-mode endpoint sums. Every positive left endpoint is strictly positive; a finite positive head bound includes EVERY low and first gap. One pair of positive constants therefore compares endpoint sums with 1+n before ALL Sobolev orders and positive indices.

The previously proved all-order actual Miura criterion identifies H^s of q with H^(s+1) of its full signed Dirac gaps. Exact negative endpoint reflection, symmetric weights and a genuine finite central correction identify full signed membership with the zero-extended positive half. The endpoint-sum comparison then transfers the criterion to ORIGINAL Hill energy gaps with EXACT order s. This is a native membership equivalence, not a conclusion from an unrestricted totalized tsum.

## Actual rough Abelian coordinates and uniform inverse amplitudes

`exists_hillHminus_native_action_amplitude_symbol_bounds` retains ONE actual native ell-infinity analytic amplitude M on ONE complex rough ball before every source and positive index. It proves a common upper bound and the UNIFORM lower bound norm(M_n)>=1/8. Native ell-infinity continuity and the actual free Fourier-symbol lower bound supply this estimate. Individual nonvanishing alone would not give the required inverse bound.

Actual physical recovery and real mean-zero rough density identify the existing original action/gap norm formula on the whole real mean-zero rough ball, including non-L2 sources:

```text
4*(1+n)*|z_n|^2 = |Gamma_n|^2*|M_n|^2.
```

The squared-gap symbol is the actual normalized original energy gap square; its normalization n^2 cancels exactly, with no modeled or caller-supplied replacement for the physical data. The literal half-weight identity gives, for EVERY real order s,

```text
|W_(s+1/2)(n)*z_n| = (|M_n|/2)*|W_s(n)*Gamma_n|.
```

The uniform two-sided amplitude bounds and the global original Hill-gap criterion give `exists_hillHminus_native_signed_abelian_all_sobolev_criterion`: ONE ACTUAL signed rough Abelian map, with original physical recovery and complex H-minus-one analyticity, has q in H^s IFF Z(q) in native h^(s+1/2), for ALL s>=-1 and EVERY real mean-zero q in ONE common rough ball. The ball precedes every source and every order. Genuine conjugate reflection covers the negative coordinates, including the central finite correction. No q-in-L2 premise appears.

A reusable version applies to any SAME actual rough map with proved physical recovery and pointwise norm reflection. The final signed-map theorem instantiates both conditions with the existing actual native construction. The inverse theorem below supplies norm reflection from its literal real target, so no independent choice of another inverse or coordinate family is substituted.

## ONE actual inverse for ALL real targets and orders

`exists_hillHminus_native_real_target_all_sobolev_inverse` starts from the ALREADY proved actual physical L2 endpoint family (eta,Z,W,R). The SAME functions Z and R are retained. The target is shrunk to the explicit open set

```text
W_new = W intersect R^(-1)(ball(0,rho)).
```

Its openness uses the existing analytic R on its original open domain; R(0)=0 keeps zero in W_new. The radius rho comes from the Sobolev criterion for this SAME Z. Thus ONE source ball and ONE open target neighborhood precede ALL complex targets for the exact right-inverse identity, and ALL real targets and orders for the Sobolev criterion:

```text
Z(R(b)) = literal meanZeroWeightedLift(sobolev(-1/2), b)
R(b) in native H^s  iff  that SAME literal signed target lies in h^(s+1/2),
for EVERY real b in W_new and EVERY real s>=-1.
```

Every real target may have arbitrary infinite support. Reality and the zero mean of the SAME inverse are retained. Target reality gives exact norm reflection of Z(R(b)) via the literal right-inverse identity; it is not assumed from an unrelated existential map.

The ORIGINAL physical L2 endpoint is retained in addition to all the new Sobolev criteria. Half-regular real targets still have an ORIGINAL real mean-zero L2 representative p whose literal H-minus-one inclusion equals R(b), EVERY fixed GLOBAL original L2 Birkhoff coordinate equals the SAME prescribed target, and

```text
norm(p)^2 = sum_(n>=1) 4*pi*n*|target_n|^2.
```

The physical H_0 convention is one half of this squared L2 norm. Genuine endpoint summability is preserved by the earlier verified theorem.

## Remaining main obligations

These are exact native membership results for the actual local rough chart and inverse. R remains complex analytic with values in H-minus-one. Membership in a stronger Sobolev space by itself does NOT prove continuity or analyticity into that stronger topology. The stronger source/target Sobolev restrictions, arbitrary-base and global H-minus-one Birkhoff inverse, full-frequency identification, renormalized KdV2 correction estimates and the actual physical PDE main conclusions remain open. No complete main theorem is marked verified.

## Validation

All 2414 previously selected source bytes and all 40 provenance records remain unchanged. Six new own modules reuse the already reachable verified library; there is no new shared-source import or adaptation.

Prior strict evidence retained for all 2414 unchanged selected baseline sources. All six new own proof modules strictly rebuilt in dependency order, followed by a fresh combined transitive axiom audit of all 2420 selected modules. Exact checker/audit/coverage/evidence selections, transitive selected order and reachability, 2463 frozen source/checker/provenance/Mathlib-source hashes, all 40 unchanged verified provenance records, private fresh outputs and unchanged clean canonical main verified. The NLS import closure adds EXACTLY these six selections; no new shared-source import or adaptation is needed. No full 2420-module rebuild is claimed.

Fresh audit: 19192 selected and 41262 imported NLS declarations. Six new own modules contain 13 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no new axioms or proof-checking exceptions. All eleven main theorem rows remain OPEN.
