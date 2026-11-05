# Native rough symmetric midpoints and Dirichlet divisors

This is actual spectral progress toward the Hminus-one endpoint of Theorem 1.1. All eleven complete main theorem rows remain OPEN.

## Common neighborhoods at every real rough base

`NLS.KdV.exists_hillHminus_native_gap_midpoint_sequence` constructs, at EVERY actual real unit-period Hminus-one source, ONE common complex-open neighborhood and a native ell2 analytic map T BEFORE all positive indices. At EVERY real source in that neighborhood,

```text
T_n = (actual_symmetric_energy_midpoint_n - (pi*n)^2) / n.
```

Nonpositive components vanish. First gaps, collapsed gaps and nonzero means are included. No root labels, matching hypotheses or source-index-dependent neighborhoods are supplied by the caller.

The actual symmetric midpoint is `(hillHminusRealLabels_(2n-1)+hillHminusRealLabels_(2n))/2`. A constructed real-preserving analytic Miura chart has a fixed positive shift c squared, chosen AFTER the proved rough spectral lower bound. The actual characteristic is nonzero at minus that shift on the ENTIRE complex chart. Full algebraic multiplicities identify every ordered positive Dirac endpoint pair with the corresponding squared and translated actual Hill labels, including repeated low and collapsed endpoints.

The original NLS frequency midpoint displacement d is native ell2 analytic. A new shared theorem assembles the actual signed squared frequency gaps g as a native ell1 analytic map on a common neighborhood of the entire real-type source slice. The exact normalized energy midpoint is assembled by the Banach-analytic formula

```text
((pi*n+d_n)^2 + g_n/4 - c^2 - (pi*n)^2) / n.
```

The g_n/4 term is necessary: squaring only the frequency midpoint would give the wrong energy midpoint for an open gap. The construction uses the actual symmetric scalar data and genuine sequence norm bounds.

## One native rough divisor packet near zero

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_divisor_packet` constructs ONE eta>0,C>0 and T,A,K,S from the complex original Hminus-one space to ell2 BEFORE every positive index. All maps are analytic on the SAME ball, vanish at zero and satisfy

```text
norm(T q) + norm(A q) + norm(K q) + norm(S q) <= C * norm(q).
```

At EVERY real rough source in that ball,

```text
T_n = (actual_midpoint_n - (pi*n)^2) / n,
A_n = (actual_Dirichlet_energy_n - actual_midpoint_n) / n,
K_n = actual_log_norming_n,
S_n = sinh(actual_log_norming_n).
```

At EVERY complex source in the same ball, the actual entire derivative-one Dirichlet characteristic vanishes at `(pi*n)^2+n*(A_n+T_n)`. Every nonpositive component vanishes and `S_j=sinh(K_j)` holds throughout that same complex ball.

## Exact original physical normalization

`NLS.KdV.hillHminusRealLabels_eq_physical` identifies EVERY rough periodic characteristic label with the ORIGINAL physical L2 label at EVERY original real L2 source, from the bottom onwards and with all multiplicities. Literal entire radicand equality and finite global multiplicities fix the full ordered enumeration; no tail agreement is assumed. `NLS.KdV.hillHminusGapMidpoint_eq_physical` gives the exact original physical symmetric midpoint. Previously proved global Dirichlet label/norming matching remains unchanged. Thus the divisor data have the existing physical normalization.

This is necessary input for rough Abelian coordinates. Actual rough filled-root bounds, analytic action/gap amplitude ratios and the full regular phase still require proof and assembly. The full negative-half weighted Abelian map, coordinate-coordinate canonicality, global inverse, full regularity scale and actual frequency/PDE main conclusions are not asserted.

## Reuse and integration

`SHARED_MIURA_PERIODIC_LABELS_IMPORT.json` records shared source `articles/kdv-estimates` at `52ac67de59a28aee862bf8fe4903d15b246457b2`: ten unchanged incoming sources, two adapted incoming sources, fifteen retained local variants and two byte-identical canonical helper selections. Two endpoint reality/order declarations are extracted from one additional shared source into a separate compatibility module.

The full squared-Miura label theorems use the retained `hillHminusRealLabels` API and its already verified multiplicities. The real source imports only the extracted endpoint facts, avoiding the unnecessary incoming high-tail adapter. All 1418 prior selected sources and 34 prior provenance records remain unchanged. No incoming canonical-label replacement is loaded.

## Validation

Prior strict evidence retained for all 1418 unchanged selected baseline sources; all 21 new selections strictly compiled in dependency order, followed by a fresh combined transitive axiom audit of all 1439 selected modules. The new selections are twelve incoming sources, seven new/extracted proof modules and two unchanged canonical helpers. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1477 frozen source/checker/provenance/Mathlib-source hashes, 34 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these 21 selections. No full 1439-module rebuild is claimed.

Fresh audit: 12485 selected and 34552 imported NLS declarations. Seven new/extracted modules contain 15 explicit theorems and 3 definitions; twelve incoming sources and two unchanged canonical helper selections are also strictly checked. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
