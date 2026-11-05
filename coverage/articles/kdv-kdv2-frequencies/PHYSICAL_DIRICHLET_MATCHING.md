# Exact physical matching of the rough Dirichlet packet

This proves necessary physical matching for the Hminus-one endpoint of Theorem 1.1. All eleven complete main theorem rows remain OPEN.

## Global shared comparisons

`NLS.KdV.hillPhysicalHminusEmbedding` samples the original physical even Fourier indices and includes those raw unit-period coefficients into Hminus-one. It is continuous and preserves physical reality. The actual derivative-one characteristic agrees at EVERY complex energy with the existing original L2 characteristic.

`NLS.KdV.hillHminusDirichletEnergy_eq_physical` identifies EVERY positive intrinsic rough labelled energy with the original physical L2 labelled energy at EVERY real L2 source. There is no source-size, mean-zero, high-index or open-gap hypothesis. Both actual label families are continuous. Local uniqueness of the original physical Dirichlet zero makes their equality locus open along the straight real source segment; continuity makes it closed, and the exact free labels identify its zero endpoint. Connectedness then gives the original source.

`NLS.KdV.HillHminusMiuraChart.physicalMomentum_terminal_eq_physical_of_root` identifies the actual terminal quasi-derivative with the independently normalized physical L2 derivative at EVERY complex L2 Dirichlet root. The shift is exact and the Miura gauge term vanishes at the root. The coefficient and physical rough IVP curves agree as actual solutions.

`NLS.KdV.hillHminusDirichletNorming_eq_physical` and `NLS.KdV.hillHminusDirichletLogNorming_eq_physical` consequently identify the endpoint factor and its signed real logarithm with the original physical slope and log multiplier, globally at every real L2 source and positive index. Collapsed gaps and nonzero means are included.

## One common native rough ball

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_physical_dirichlet_packet` constructs ONE eta>0,C>0 and D,K,S from the actual complex period-one Hminus-one space to ell2 BEFORE all positive indices. All three are analytic on the SAME ball, vanish at zero, satisfy

```text
norm(D q) + norm(K q) + norm(S q) <= C * norm(q),
```

and have zero nonpositive components. At every complex source in the ball the actual Dirichlet characteristic vanishes at `(pi*n)^2+n*D_n`; `S_j=sinh(K_j)` holds throughout that ball.

For EVERY original physical real L2 source whose literal Hminus-one inclusion belongs to that SAME ball, EVERY positive component equals

```text
D_n = (original_physical_Dirichlet_energy_n - (pi*n)^2) / n,
K_n = original_physical_Dirichlet_log_multiplier_n,
S_n = sinh(original_physical_Dirichlet_log_multiplier_n).
```

The previously proved intrinsic rough packet remains available with recovery at all real Hminus-one sources. This result supplies its exact original physical normalization. Rough symmetric midpoints, filled roots, analytic action/gap amplitudes, full regular phase and the full negative-half weighted Abelian map still require assembly and bounds. Full canonicality, global inverse, full regularity and the actual frequency/PDE main conclusions are not asserted.

## Shared reuse and validation

`SHARED_DIRICHLET_TERMINAL_IMPORT.json` records eight byte-identical sources from `articles/kdv-estimates` at `91e0789978eb013d13e9c974ba362eef29eac4dd`, and thirteen retained local variants. The retained original characteristic/Miura APIs already supply the shared dependencies; importing duplicate extracted modules is unnecessary. All 1407 prior selected sources and 33 prior provenance records remain unchanged.

Prior strict evidence retained for all 1407 unchanged selected baseline sources; all 11 new modules strictly compiled in dependency order, followed by a fresh combined transitive axiom audit of all 1418 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1455 frozen source/checker/provenance/Mathlib-source hashes, 33 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these 11 selections. Eight shared sources are byte-identical imports and thirteen local API variants are retained unchanged. No full 1418-module rebuild is claimed.

Fresh audit: 12321 selected and 34391 imported NLS declarations. Three new proof modules contain 9 explicit theorems and 1 definition; eight imported sources are also strictly checked. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
