# The actual normalized rough Dirichlet terminal

This proves a necessary native Hilbert-analytic dependency toward the Hminus-one endpoint of Theorem 1.1. All eleven complete main theorem rows remain OPEN.

## Article statement and exact physical normalization

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_normalized_terminal_packet` constructs eta>0, C>0 and Z:Hminus-one->ell2, with ONE complex rough ball before every positive index:

```text
Z is complex analytic on ball(0,eta),
Z(0)=0,
norm(Z(q)) <= C*norm(q),
Z(q)_j=0 for j<=0.
```

At EVERY original real L2 potential p whose literal unit-period Hminus-one inclusion lies in this whole ball, and EVERY positive n,

```text
Z(embed(p))_n = Terminal_n(p)/n,
Terminal_n(p) = sheet_n(mu_n)/deflatedRoot_n(mu_n) - (mu_n-tau_n).
```

Here mu_n is the ORIGINAL physical labelled Dirichlet energy, tau_n is the ORIGINAL physical symmetric gap midpoint, and both sheet and canonical deflated root are their ORIGINAL physical definitions. The first gap, all closed gaps and nonzero means are included. The L2 norm of p need not be small.

The theorem supplies native Banach analyticity and a full ell2 norm bound. It does not merely provide separately analytic scalar components or leave a caller-provided spectral factory. It does not yet assemble the full rough Abelian map or prove an intrinsic terminal identity at every rough real source.

## Actual roots on a common rough domain

The verified actual squared-primitive family K and normalized gap root J construct

```text
U_n = (2*i*(-1)^n/pi)*J_n*deriv(squaredCosh)(K_n),
roughRadicand = actualGapPolynomial_n * (U_n/n)^2.
```

This is jointly analytic in energy and rough source. A common squared-primitive bound places K_n in the closed unit disc, where the squaredCosh derivative never vanishes. Compactness bounds its inverse, while J_n stays within 1/2 of one. Consequently one constant bounds every inverse U_n on the common high-index domain.

At the free potential the actual gap polynomial is (E-(pi*n)^2)^2. Continuous cancellation at the collapsed center compares squared roots without dividing by a closed gap. A constant correction of square one and norm one fixes the ORIGINAL free root value without changing the bound. Exact physical endpoint labels, continuous quadratic cancellation and source/energy continuation then identify the physical root germ, including its sign.

The actual native divisor displacement D=A+T makes the moving energy (pi*n)^2+n*D_n. The native ell2 bound controls every displacement on one rough ball, placing ALL high moving energies inside their energy domains. This gives H_n=1/U_n at the moving divisor and one common inverse bound. The already constructed finite-index local roots supply the head. The combined positive family is realized as a genuine native ell-infinity analytic H with zero nonpositive components and exact ORIGINAL physical inverse-root germs.

## Native terminal assembly and whole-ball recovery

The already verified actual native divisor packet supplies A_n=(mu_n-tau_n)/n and S_n=sinh(log multiplier_n). The exact physical sheet identity is 2*(-1)^n*S_n, with the positive sign. Thus the constructed native terminal is

```text
Z_n = 2*(-1)^n*H_n*S_n - A_n.
```

Bounded multiplication ell-infinity times ell2 into ell2 proves its native analyticity. The vanishing of A and S at zero gives Z(0)=0 and hence a local linear norm bound. Physical matching initially holds on an original L2 germ for each n. The actual physical terminal is real analytic along EVERY scaling line at EVERY point. Analytic continuation on the convex preimage of the rough ball therefore proves the stated identity for every original real L2 source in the WHOLE rough ball. This removes the L2 smallness restriction from the final statement.

## Remaining main-theorem work

The common all-index weighted amplitudes and this native normalized terminal are proved. The common rough regular phase and negative-half target Abelian map still require construction. Complete coordinate-coordinate canonicality, global and arbitrary-base inverse results, the entire s>=-1 scale, and the actual action-frequency/PDE conclusions remain open. This dependency milestone verifies no complete main theorem.

## Validation

Prior strict evidence retained for all 1504 unchanged selected baseline sources; all eleven new own proof modules strictly compiled in dependency order, followed by a fresh combined transitive axiom audit of all 1515 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1554 frozen source/checker/provenance/Mathlib-source hashes, all 36 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these eleven proof modules. No full 1515-module rebuild is claimed.

Fresh audit: 13014 selected and 35084 imported NLS declarations. Eleven own modules contain 32 explicit theorems and 3 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
