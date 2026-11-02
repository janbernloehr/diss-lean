# KdV/KdV2 frequency maps — source and proof map

Status: **main theorems not yet verified**. The initial private candidates
were integrated into the dedicated `articles/kdv-kdv2-frequencies` worktree
from canonical base `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. See
[branch progress](PROGRESS.md) for the actual workspace and subsequent proofs.
Nothing in this record reopens the completed dissertation verification.

## Source identity

The author's [publication list](https://janbernloehr.de/academia/publications)
lists the journal article **On the wellposedness of the KdV/KdV2 equations and
their frequency maps**, with T. Kappeler, Ann. Inst. Henri Poincaré 35(1),
101–160 (2018). The assigned [arXiv v1](https://arxiv.org/abs/1605.06690v1)
is titled **On the extension of the frequency maps of the KdV and the KdV2
equations**, by Thomas Kappeler and Jan-Cornelius Molnar. This record verifies
neither equivalence of journal and preprint formulations nor the journal PDF.

Downloaded URL: `https://arxiv.org/pdf/1605.06690v1` on 2026-11-02.
SHA-256: `b123dcf540ecca2f844e9e8337738b2cbaf402013410e8315ad53e445eb5dd7c`.
Size: 1,067,594 bytes; 76 PDF pages. The PDF margin reads
`arXiv:1605.06690v1 [math.AP] 21 May 2016`, but the title page/footer reads
June 14, 2022 and PDF creation metadata reads June 14, 2022 23:35:35 UTC.
The hash, rather than the URL alone, identifies the exact bytes inspected.
PDF and extracted text are private scratch files in `work/source/` and are
excluded from the integration patch. PDF page numbers agree with printed
page numbers in this file.

## Conventions that the final interfaces must retain

- Period is one: `T = R/Z`. Fourier coefficients pair against `exp(i 2πnx)`.
  The sequence weight is `⟨n⟩ = 1 + |n|`; the norm is
  `(Σ ⟨n⟩^(sp) |z_n|^p)^(1/p)`. Sequence action indices are positive integers;
  signed coordinate indices are all integers, with `z_0 = 0` and
  `z_(-n) = conjugate(z_n)`. Positive action quadrant means **nonnegative**,
  so closed gaps and zero actions are included.
- `H^s` consists of real periodic distributions; `H^s_0` is the mean-zero
  leaf. `Fℓ^{s,p}_0` uses the same real symmetry and zero mode. `h^s_0` means
  `ℓ^{s,2}_0`. Topologies are the native strong norms except where analyticity
  explicitly uses an open neighborhood in the complexified Banach space.
  Analyticity on a nonnegative quadrant means extension to a complex open
  neighborhood; it does not assert that this quadrant has ambient interior.
- Gardner bracket is `∫_0^1 (∂_u F) ∂_x(∂_u G) dx` (3).
  `H_1 = (1/2)∫(u_x² + 2u³)` and
  `H_2 = (1/2)∫(u_xx² + 10u u_x² + 5u⁴)`.
  The actual PDEs are `u_t = -u_xxx + 6u u_x` (1) and
  `u_t = u_xxxxx - 10u u_xxx - 20u_x u_xx + 30u² u_x` (2).
- The Birkhoff map has regularity shift `H^s_0 → h^{s+1/2}_0`, for all
  `s ≥ -1`, and derivative at zero `(2|n|π)^(-1/2) u_n` (Theorem 1.1, p. 3).
  `I_n = z_n z_(-n) = |z_n|²`, with no extra factor of two.
  The source action integral (19), p. 11, is counterclockwise with factor
  `1/π`; the bracket is `{z_n,z_(-n)} = i` for `n ≥ 1`.
- `H_0 = (1/2)∫u² = Σ_(n≥1) (2nπ) I_n`.
  `ω_1* = ω_1 - (2nπ)³`,
  `ω_2* = ω_2 - (2nπ)⁵ - 20(2nπ)H_0` (8)–(9).
  `H_1* = H_1 - Σ(2nπ)³ I_n`,
  `H_2* = H_2 - Σ(2nπ)⁵ I_n - 10H_0²` (10).
  Derivatives at zero have leading diagonals `-6 Id` and
  `diag(-20(2nπ)²) = diag(-80n²π²)` respectively.
- Page 3 gives the Hamiltonian velocities `z_n' = -i ω_n z_n`,
  `z_(-n)' = +i ω_n z_(-n)`. Equations (80) and (91) later print a positive
  exponential with an odd frequency extension. The candidate uses the page-3
  Hamiltonian time orientation: negative exponential at positive modes.
  The final PDE identification must check this convention explicitly.
- A low-regularity solution is defined on p. 7 by convergence of solutions
  from **every** smooth approximating sequence, pointwise in time in the
  native norm, together with a continuous limiting curve attaining its data.
  `C^0` wellposedness additionally requires continuity into
  `C([-T,T], H)` in the uniform norm for **every** `T > 0`.
  An arbitrary phase curve is not by itself a solution of the physical PDE.
- Admissible Fourier–Lebesgue pairs: `p=2, s≥-1`, or
  `2<p<∞, -1/2≤s≤0`. `ℓ^{1+}` denotes simultaneous membership in every
  `ℓ^r`, `r>1`; it is not a single fixed exponent.

## Main and advertised statements

Every row below remains open at the equation-specific level. The candidate
dependencies are described in the next section; no row is promoted to
verified merely because it has a generic analogue.

| Label / PDF page | Statement, domains and quantifiers | Outstanding proof obligations |
| --- | --- | --- |
| Theorem 1.1 / 3 | Cited background: one complex-analytic Birkhoff map on a neighborhood of real `H^-1_0`; all `s≥-1` restrictions are real analytic diffeomorphisms, canonical and action-Hamiltonian, with the Fourier derivative above. | Consume the `kdv-estimates` Hill/Birkhoff construction, including low and real regularities and exact normalization. No dNLS map substitution. |
| Theorem 1.2(i) / 4 | One extension of `ω_1*` on `ℓ^{-1,1}_+` has values in `⋂_(r>1) ℓ^{-1,r}`. Restrictions from `ℓ^{2s+1,1}_+` are analytic into `ℓ^{-1,r}` at `s=-1`, every `r>1`; into `ℓ^{2s+1,1}` for `-1<s<-1/2`; into `ℓ^r` for `s≥-1/2`, every `r>1`. | Spectral moment formula, locally uniform convergence and analytic assembly; one map with compatible realizations, not unrelated choices for each exponent. |
| Theorem 1.2(ii),(iv) / 4 | For each `-1<s<-1/2` and each nonnegative `I` in the indicated space, `d_I ω_1* + 6Id` is compact on `ℓ^{2s+1,1}`. Also analytic `ω_1*:ℓ²_+→ℓ²` with compact remainder at every `I∈ℓ²_+`. | Establish KdV remainder bounds and derivative compactness; reuse generic compact embeddings and analytic coordinate bounds. |
| Theorem 1.2(iii) / 4 | For `I∈ℓ^{2s+1,1}_+`, `ω_1*,n+6I_n=o(n^{3|s|-2})` for `-1≤s<-1/3`; `O(n^-1)` for `s≥-1/3`, locally uniformly on a complex neighborhood. | Uniform spectral estimates with these exact exponents and endpoint split. |
| Theorem 1.3 / 5 | An open dense subset `O⊂ℓ²_+`, containing zero, on which `∀I∈O, ∃c>0, ∀J∈ℓ²`, `d²_I H_1*(J,J)≤-c‖J‖²`; `c` can be chosen locally uniformly in `I`. Openness and density are relative to the cone. | Consume `kdv-convexity` action Hamiltonian and concavity; prove compact Hessian perturbation, analytic Fredholm density, and coercivity with quantifiers in this order. |
| Theorem 1.9 / 6 | One analytic extension of `ω_2*`: `ℓ^{2s+1,1}_+→ℓ^{2s-1,1}` for `-1<s<1/2`, and into every `ℓ^r`, `r>1`, for `s≥1/2`. Remainder `ω_2*,n+20(2nπ)²I_n` belongs to `n^{-3s}ℓ¹` for `-1<s<0`, or `ℓ^{1+}` for `s≥0`, locally uniformly on a complex neighborhood. | Prove KdV2 moment identities, action descent, analytic extensions and weighted summable remainders; the exact coefficient is 80π²n². |
| Theorem 1.12(i) / 7 | For every `s≥0`, the actual KdV2 equation is globally `C^0` wellposed on all real `H^s`, with continuity into the uniform trajectory norm for every `T>0`, group law at all real times and homeomorphic time slices. | Prove actual frequency continuity, identify Birkhoff evolution with smooth PDE solutions, show every smooth approximating sequence converges, and extend the mean-zero leaf to all means. |
| Theorem 1.12(ii) / 7 | For every `s≥1/2`, every `d>0`, globally real analytic and uniformly `C^0` wellposed on `M^s_(0,d)={u∈H^s_0:H_0(u)=d}`. The supporting Theorem 4.14(ii) specifies uniform continuity on bounded subsets, while the introduction uses unqualified uniform-continuity language; retain the bounded-set qualification explicitly when matching the proof. | Fixed-mass correction analytic into bounded sequences; bounds uniform on bounded subsets; analytic trajectory transfer and level-set identification. |
| Theorem 1.12(iii) / 7 | For every `s≥1/2` and fixed `t>0`, the time-slice map on `H^s_0` is nowhere locally uniformly continuous. Consequently not `C^1` or uniformly `C^0` wellposed there. | Explicit pairs of physical initial data in every nonempty open subset, tending together while images separate at that fixed time. |
| Theorem 1.12(iv) / 7–8 | For every `0≤s<1/2`, `d>0`, `t>0`, the time slice on `M^s_(0,d)` is nowhere locally uniformly continuous, with the corresponding failure of `C^1` and uniform `C^0` wellposedness. | Preserve the fixed mass exactly in the separating pairs. Use the main statement's `d>0`; later Theorem 4.14(iv) prints `d≥0`. |
| Theorem 1.12(v) / 8 | For each `-1<s<0`, the solution map has no continuous extension to any datum of `H^s_0\L²_0`. The correction extends analytically but `ω_2,n=(2nπ)^5+20(2nπ)H_0+ω_2*,n` has a diverging mass contribution at every positive mode. | Physical smooth approximation with diverging mass and a nonzero limiting mode, actual frequency formula, and transfer of nonextension to the physical trajectory map. The compact-time and fixed-time coordinate obstruction cores are now proved; actual spectral correction and physical transfer remain open. |
| Theorem 3.10(i) / 36 | For every finite `p≥2` and `-1/2≤s≤0`, KdV is globally real analytically wellposed on `Fℓ^{s,p}_0`. | Actual KdV frequencies with bounded analytic correction; Fourier–Lebesgue Birkhoff diffeomorphism and physical identification. |
| Theorem 3.10(ii)–(iii) / 36–37 | For `-2/3≤s<-1/2`, each fixed `t>0` time slice on `H^s_0` is nowhere locally uniformly continuous. For `-1<s<-2/3`, each `T>0` trajectory map to `C([-T,T],H^s_0)` has that property. Not `C^k` wellposed for any `k≥1`. | Retain this fixed-time/trajectory distinction and the `-2/3` endpoint; prove spectral remainder and explicit separation constructions. |
| Theorem 4.12 / 49–50 | KdV2 renormalized Hamiltonian extends analytically to the nonnegative action space `h^1_+`. Its gradient is the actual `ω_2*`, naturally paired in `h^-1,h^1`. Near zero it is strictly concave, bounded by `(1/2)⟨ΛJ,J⟩` with `Λ=diag(-80n²π²)`. | Source formula has a derivative notation ambiguity in the displayed quadratic inequality; implement the well-typed Hessian/frequency-derivative form and prove its identification. Consume shared action Hamiltonians, not the dNLS Hamiltonian. |

The introduction's corollaries are also retained for later verification:

| Label / PDF page | Required content |
| --- | --- |
| Corollary 1.4 / 5 | For every `-1<s<-1/2`, `ω_1*` is a local diffeomorphism on an open dense subset of `ℓ^{2s+1,1}_+` containing zero. |
| Corollary 1.5 / 5 | Physical KdV frequencies on `H^s_0`: leading `8n³π³`, remainder `o(n^{-2s-1})` for `-1≤s<0`, `O(n^-1)` for `s=0`; locally uniform in potentials and uniform over positive indices. Sharpness for each `-1<s<0`: no smaller exponent `α<-2s-1` works in general. At `s=0` the estimate is uniform on bounded `L²_0` sets. |
| Corollary 1.7 / 6 | For every `q∈L²_0`, the actual KdV solution satisfies `‖u(t)-exp(tL)q‖_(H¹)≤C(1+|t|)` for all real `t`, with `L=-∂³_x` and `C>0` locally uniform in `q`. |
| Corollary 1.11 / 6 | For every `-1<s<1/2`, `ω_2*:ℓ^{2s+1,1}_+→ℓ^{2s-1,1}` is a local diffeomorphism on an open dense subset containing zero. |

## Existing reuse and new candidates

Search base: canonical `NLS/SequenceSpaces`, `NLS/Dynamics`,
`NLS/FunctionalAnalysis` and source flow modules. Only the `main` branch and
`origin/main` were locally available during this initial phase.

- Existing `NLS.SequenceSpaces.PhaseRotation` already proves coordinatewise
  frequency continuity plus norm-continuous amplitudes gives full `ℓ^p`
  continuity, using finite tails; reuse it directly.
- Existing `NLS.SequenceSpaces.WeightedPhaseFlow` already constructs the
  weighted linear isometric phase group for arbitrary real frequencies.
- New `NLS.Dynamics.ActionDependentWeightedPhaseFlow` adds weighted frequency
  families and nonlinear action dependence, compact-time continuous
  trajectories and time-slice homeomorphisms. It establishes the
  action-dependent application of Appendix E.1(i)–(ii) (pp. 72–73), indexed
  by `ℤ` instead of the appendix's positive indices. Its group law is proved
  using amplitude conservation. No general group law for arbitrary
  state-dependent frequencies is asserted.
- New article `SignedPhaseFlow` restricts to the actual signed real locus,
  proves zero-mode/reality preservation, identifies `z_n z_(-n)=|z_n|²`,
  and supplies the negative-positive Hamiltonian phase signs. Its `Ω` is an
  explicitly supplied generic function. Constructing actual spectral
  `ω_1,ω_2` and proving their analytic estimates remain open.
- Existing `NLS.Dynamics.HamiltonianPhaseObstruction` already proves the
  compact-time nonconvergence obstruction for a nonzero limiting amplitude
  and frequencies tending to positive infinity. New article
  `MassPhaseObstruction` derives that hypothesis from the correctly normalized
  KdV2 mass term and a convergent correction. It does not construct physical
  smooth approximations or identify their frequencies.
- Existing analytic trajectory modules (`AnalyticPhaseTrajectory`,
  `AnalyticComplexPhaseTrajectory`, `WeightedPhaseTrajectoryAnalytic`) and
  compact derivative/local inverse modules are reuse candidates. Their
  assumptions must be verified for actual KdV data before use.
- New article `SmoothKdVIdentities` proves the Euler-Lagrange polynomial
  formulas, their actual smooth spatial derivatives, the nonzero-mean
  vector-field identities, and the periodic mean/quadratic-mass spatial
  balances. This advances the physical side of Theorem 1.12 without
  presupposing a spectral identification; details are in `PROGRESS.md`.
- Shared Hill/Birkhoff foundations belong to `kdv-estimates`; action
  Hamiltonians/concavity belong to `kdv-convexity`. This candidate introduces
  no competing spectral or action-Hamiltonian construction.

The endpoint-mass and compact-time coordinate nonextension dependencies
have since been proved in `SignedMassDivergence.lean`; see
[MASS_NONEXTENSION.md](MASS_NONEXTENSION.md). The coordinate mass-divergence
and approximation obligations are discharged there. Actual spectral
correction and physical Birkhoff-flow obligations in the main-theorem rows
remain open.

The separate fixed-time coordinate argument of Theorem 4.14(v) has since
been proved with constructed mass-shifted finite approximants and explicit
correction/phase-agreement inputs; see
[FIXED_TIME_NONEXTENSION.md](FIXED_TIME_NONEXTENSION.md). This does not
mark the actual spectral or PDE main theorems verified.

The frequency-moment analytic and contour-decomposition steps of Lemmas
3.1, 3.2 and 4.1 have since been proved in the shared `NLS/KdV` layer;
see [FREQUENCY_MOMENTS.md](FREQUENCY_MOMENTS.md). The actual spectral
factors, zeroth periods, physical frequency identification, sharp estimates
and infinite-series convergence remain open.

## Integration boundary

The following describes the initial private stage; the subsequent user-approved
worktree and publishing step is recorded in [PROGRESS.md](PROGRESS.md).

Canonical sources and build products were read only. New sources, object
files, audit artifacts and downloaded source material stay in this chat's
private directory. No worktree, branch switch, commit, push or other-chat
message was made. Once the pending workspace arrangement is resolved, use
the intended branch `articles/kdv-kdv2-frequencies` and integrate generic
dependencies once before the article adapters. Expensive combined validation
must use `/tmp/diss-lean-article-build.lock` and a separate mutable build tree.
