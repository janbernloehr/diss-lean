# Actual rough Dirichlet data on one native Hilbert analytic ball

This is necessary spectral progress toward Theorem 1.1 at its Hminus-one endpoint. All eleven complete main theorem rows remain OPEN.

## Exact result

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_dirichlet_packet` constructs ONE radius `eta > 0`, constant `C > 0`, and three maps `D`, `K`, `S` from the original complex period-one `PeriodOneHminusOne` space to `Coeff 2`, BEFORE every Dirichlet index. All three maps are analytic on the same complex ball, vanish at zero, and satisfy the genuine joint Hilbert norm bound

```text
norm(D q) + norm(K q) + norm(S q) <= C * norm(q).
```

Every nonpositive output is zero. For every complex source in that same ball and every positive integer `n`, the actual entire derivative-one Dirichlet characteristic vanishes at

```text
(pi*n)^2 + n * (D q)_n.
```

At every REAL Hminus-one source in the ball, without a mean-zero or open-gap assumption, the positive components are EXACTLY

```text
(D q)_n = (actual_Dirichlet_energy_n(q) - (pi*n)^2) / n,
(K q)_n = actual_log_Dirichlet_norming_n(q),
(S q)_n = sinh(actual_log_Dirichlet_norming_n(q)).
```

In addition, `(S q)_j = Complex.sinh ((K q)_j)` holds for every integer `j` throughout the same complex ball. It is proved by physical real-form uniqueness; no separate output-dependent neighborhood is used. First modes, collapsed gaps, infinite spectral data and nonzero source means are included.

## Construction and reused geometry

The shared rough spectral development constructs the actual normalized IVP, intrinsic weak equation and form, real Dirichlet spectrum, ordered labels, positive signed endpoint norming multipliers and their logarithms. Its Miura-to-NLS comparison supplies common analytic Dirichlet frequency branches and anti-discriminant samples. The imported geometry is proved, including reality, simplicity and label exhaustiveness, rather than supplied as caller hypotheses.

A reusable native Hilbert quadratic map converts a frequency displacement `d_n` into the normalized energy `((pi*n+d_n)^2-c^2-(pi*n)^2)/n`. Its quadratic product is formed in ell1 and continuously included in ell2. The signed half anti-discriminant samples are assembled directly in the positive output Hilbert space; analytic inverse-sinh superposition recovers the actual real logarithmic norming sequence. These constructions work on common complex neighborhoods at EVERY real Hminus-one base point. The article packet uses the zero base point and a common smaller ball, then a reusable analytic-zero estimate supplies the linear norm bound.

The actual rough characteristic now restricts to the existing ORIGINAL L2 characteristic through the adapted shared API `hillL2Dirichlet_eq_characteristic`. This reuses the original frequency family and normalization rather than loading a duplicate family. Identification of every intrinsic rough labelled energy/norming with all older physical weighted Abelian components is a further assembly obligation; no such Abelian identification is silently inferred.

## Integration provenance

`SHARED_ROUGH_DIRICHLET_IMPORT.json` records 114 incoming source files from `articles/kdv-convexity` at `ba0cf42ee4f2e37acfc7a239af566e11b9e583f2`: 107 byte-identical imports and 7 integration adaptations. Fourteen existing local variants are retained byte-for-byte. Three unchanged canonical norming helpers are newly strictly selected. Two needed chart/action-normalization compatibility modules are extracted separately, preserving all prior selected source and provenance hashes.

The adaptations make the L2 Dirichlet API reuse the original characteristic, reuse the existing free IVP proofs, name the different-radius pair-swap theorem separately from the retained same-radius API, update its incoming consumer, and add imports of the extracted compatibility lemmas. The combined old/new import check passes. No full branch merge or canonical source/cache modification is used.

The pinned Mathlib4.33.1 inverse-sinh module was missing from the read-only compiled reference. It is compiled from its pinned source into private article output. Its module artifacts and read-only dependency links are prepared privately, and the public checker builds it before its NLS consumers.

## Remaining main obligations

The packet supplies actual rough spectral coordinates and estimates, not the negative-half-weight Abelian/Birkhoff map. Remaining work includes compatible rough symmetric midpoints, filled roots, amplitude and regular-phase estimates, complete coordinate assembly and physical matching, all canonical coordinate brackets, arbitrary-base/global inverse and full regularity. KdV/KdV2 Hamiltonian action dependence, frequency extensions/asymptotics, compactness/concavity and PDE main conclusions remain unproved.

## Validation

Prior strict evidence for all 1282 unchanged selected baseline sources; 125 new selections strictly checked: 114 incoming source files, eight new or extracted compatibility/proof modules, and three unchanged canonical helpers. A retained 112-module integrated source-check prefix is completed by 13 strict selections after the needed private canonical helper outputs are prepared, followed by a fresh combined transitive axiom audit of all 1407 selected modules. The original interrupted prefix log is retained: its sole error is a missing private SourceLemma9_2.olean; the final log contains the successful helper and consumer builds and no error or warning. Exact checker/audit/coverage/evidence selections, transitive selected order and reachability, 1443 frozen source/checker/provenance/Mathlib-source hashes, 32 unchanged and one new verified provenance records, private fresh outputs and unchanged clean canonical main verified. The NLS imported source closure adds exactly the 125 new selections. Pinned Mathlib Arsinh is compiled privately with warningAsError at default heartbeats. No full 1407-module rebuild is claimed.

Fresh audit: 12222 selected and 34293 imported NLS declarations. Eight new or extracted compatibility/proof modules contain 17 explicit theorems and 3 definitions; 114 incoming source files and three unchanged canonical helper selections are also strictly checked. NLS candidates use Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. The pinned Mathlib dependency uses its standard source settings with warningAsError and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception in the NLS candidates. All eleven main theorem rows remain OPEN.
