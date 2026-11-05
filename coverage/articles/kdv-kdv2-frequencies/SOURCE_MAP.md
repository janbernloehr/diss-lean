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
  exponential with an odd frequency extension. The actual PDE linearizations
  and the stated Fourier transform prove the positive-mode physical sign is
  positive: `+i omega_n`, with negative sign at negative modes. The p.3
  evolution display has the opposite time orientation and is corrected in
  the candidate and nonextension adapters. See `TimeOrientation.lean` and
  `ABELIAN_PHASE_PERIODS.md`; actual Birkhoff/PDE identification remains open.
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
  and supplies the positive-negative physical Fourier phase signs after the
  proved time-orientation correction. Its `Ω` is an
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
remain open. The fixed-mode infinite-series summation implication from
local spectral remainder bounds is now proved; see
[FREQUENCY_SERIES.md](FREQUENCY_SERIES.md). No actual spectral estimate
or main theorem is thereby marked verified.

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


The actual continuous-potential discriminant and local primitive charts
have now been imported from `articles/kdv-convexity` through `2135a68`.
The local continuation of the squared primitive and primitive/root quotient,
its exact endpoint value, odd-moment cancellation, and local positive-moment
bounds are proved in `FrequencyPrimitiveContinuation.lean`; see
[PRIMITIVE_CONTINUATION.md](PRIMITIVE_CONTINUATION.md). This covers local
continuous-potential dependencies of Lemmas 2.6 and 3.1, not their full rough
potential and globally normalized gap statements. Main-theorem rows above
remain open.


The free normalized differential basis is now constructed from the actual
Hill discriminant. Its entire numerator, nonzero omitted-mode value,
critical-point nondegeneracy, actual isolating circles, exact positive
`2*pi*delta_nk` periods, and all positive free frequency moments are proved;
see [FREE_FREQUENCY_PSI.md](FREE_FREQUENCY_PSI.md). This is a base construction
for equations (52)–(53) and Lemma 3.1, not a proof of the product identity or
the normalized psi family at nonzero/rough potentials.


The actual normalization problem is now constructed near the free potential:
analytic simple critical branches, entire moving numerators, actual
analytic period entries and simultaneous normalization on any finite set
of distinct positive modes. See [FINITE_NORMALIZATION.md](FINITE_NORMALIZATION.md).
The neighborhood depends on that finite set. The infinite family, global
canonical product identification and all main-theorem rows remain open.


One common complex continuous-potential neighborhood now supports every
positive actual critical branch and entire numerator basis element.
The high critical displacement tail is Banach analytic in ℓ² and uniformly
small near zero. See [UNIFORM_CRITICAL_BASIS.md](UNIFORM_CRITICAL_BASIS.md).
The infinite normalized period operator, source canonical products, rough
scale and physical frequency statements remain open; no main row is closed.

The actual infinite scalar period matrix is now defined on compatible
finite-head energy circles and fixed high frequency circles. One open
neighborhood supports every analytic entry, with the whole free matrix
equal to the identity. On one uniform off-diagonal tail, the actual
quadratic energy separation and the exact squared-denominator primitive
formula are proved. A quantitative scalar estimate retains an explicit
shifted-primitive bound. See [UNIFORM_PERIOD_ENTRIES.md](UNIFORM_PERIOD_ENTRIES.md).
Bounded operator realization, its inverse and the source's fully normalized
infinite family remain open. This closes no main-theorem row.

The uniform primitive estimates are now proved for the actual continued
sheet: one ball supports every positive contour, a common root lower
bound, and primitive error O(norm q) relative to the exact free slice.
The actual off-diagonal period tail has a uniform reciprocal-square bound.
Every selected critical frequency can be localized within pi/8 of its
free center, retaining the critical equation and simplicity. See
[UNIFORM_PRIMITIVE_BOUNDS.md](UNIFORM_PRIMITIVE_BOUNDS.md). Full matrix
operator realization, normalization and the main-theorem rows remain open.

The actual full all-frequency-circle period operator is now constructed
on ℓ², with a uniform matrix majorant, operator-norm analyticity and the
exact free identity. An analytic two-sided inverse of norm at most two
is constructed on a smaller common neighborhood, retaining the identical
selected critical/numerator data. See
[ANALYTIC_PERIOD_INVERSE.md](ANALYTIC_PERIOD_INVERSE.md). The convergent
entire normalized family, canonical products, rough/global compatibility
and all main-theorem rows remain open.

The infinite normalized entire family is now constructed near zero in
the complex continuous-potential norm. The actual numerator basis has a
jointly analytic ℓ² realization; inverse-column pairings converge
absolutely over positive indices and give entire numerators with the
exact free slice. Every literal period on the constructed squared
frequency contours equals delta_nk, including the mapped energy-path
formula with exact 1/(2*pi). See
[INFINITE_NORMALIZED_DIFFERENTIALS.md](INFINITE_NORMALIZED_DIFFERENTIALS.md).
This proves the local normalization step underlying (53); canonical
products (52), global/rough compatibility and all main rows remain open.

The actual selected critical family now gives equation (15) near zero in
that same continuous-potential setting: exact minus sign, m²*pi²
normalization and locally uniform convergence throughout the energy plane.
The critical basis has its omitted nth factor product, including the filled
own critical energy. A complete central multiplicity argument justifies
the selected labeling; no real-type assumption on the Hill pair is used.
See [CRITICAL_PRODUCTS.md](CRITICAL_PRODUCTS.md). These are critical basis
products; the distinct normalized Psi_n products (52), the source's full
rough/global domain and all main-theorem rows remain open.

The normalized entire construction now has actual one-weight l2 inverse
column errors, with Banach analyticity and all-index uniform smallness
near zero. A constructed weighted period operator and inverse, together
with bounded reciprocal-diagonal intertwining, prove literal coefficient
identities for the same R used by the normalized entire functions. See
[WEIGHTED_NORMALIZED_COEFFICIENTS.md](WEIGHTED_NORMALIZED_COEFFICIENTS.md).
This is a decay step toward the normalized product (52); a second weight,
actual normalized zeros, global/rough compatibility and every main row
remain open.

Two-weight actual normalized coefficient errors are now in l2 and Banach
analytic, with a common neighborhood and exact n² smallness scaling.
The proof constructs the twice-weighted period operator using both a
convolution kernel and an outer-product Hilbert bound; compatible actual
inverses recover the literal coefficient identities. The positive residue
coefficients are analytic in l1 and give an absolutely convergent critical
resolvent expansion of the actual normalized entire functions. See
[TWO_WEIGHTED_NORMALIZED_COEFFICIENTS.md](TWO_WEIGHTED_NORMALIZED_COEFFICIENTS.md).
Normalized zeros and their canonical product (52), the rough/global
version and all main-theorem rows remain open.

Actual normalized numerator zeros are now constructed simultaneously over
all positive gap labels other than a fixed omitted n. One analytic l2
displacement branch, on a potential neighborhood U_n, gives distinct
analytic energy zeros with exact free values. The sequence equation's
partial derivative is the actual bounded identity at zero, and the
verified analytic Banach implicit function theorem constructs the branch.
The result is connected to the literal normalized entire numerator,
including at a filled own critical energy. See
[NORMALIZED_ZEROS.md](NORMALIZED_ZEROS.md). U_n may depend on n; complete
zeros, simplicity, exact canonical product/prefactor (52), all-n common
source uniformity, the rough/global domain and all main rows remain open.

The selected actual normalized zeros are now proved simple on one source
subneighborhood for each fixed omitted n. An exact filled factor identity
and an actually invertible, operator-norm analytic Hilbert partial map
prove the literal energy derivatives nonzero for every k!=n. The selected
signed frequencies have l2 free-lattice displacement and their full
signed product has exactly those simple roots, with locally uniform
literal cutoffs. See [SIMPLE_NORMALIZED_ZEROS.md](SIMPLE_NORMALIZED_ZEROS.md).
The product still includes zero and omitted-mode placeholders; it has not
yet been identified with the canonical Psi_n product. Completeness for
Psi_n, the exact prefactor, full omitted-index uniformity, rough/global
compatibility and every main row remain open.

The selected signed root product has now been paired into an entire
positive energy product, and its omitted cutoffs have the literal source
2/(n*pi) prefactor with locally uniform convergence on the whole energy
plane. That candidate has exactly the selected retained simple roots.
The actual normalized Psi_n factors as that product times an entire
quotient, which is nonzero at the selected roots and equals one on the
whole free slice. Constructed local families retain all original periods.
See [NORMALIZED_ENERGY_PRODUCTS.md](NORMALIZED_ENERGY_PRODUCTS.md) and
`exists_classicalHill_local_normalized_product_factorizations`.

The candidate prefactor does not yet identify the Psi_n prefactor at
nonzero potentials: the entire quotient has not been proved constant or
one. Completeness for Psi_n, exact (52), common omitted-index uniformity,
real gap/sharp root estimates (54), rough/global source domains and every
main inventory row remain open.

The actual entire quotient in the normalized energy product factorization
is now constant in energy, equal to the actual analytic residue scalar
L_n=(1/n)*sum_m m*(R e_n)_m. It is nonzero on the constructed U_n and
exactly one at the free source. The selected retained roots are now the
complete actual Psi_n zero set, all simple. Literal energy products
multiplied by L_n converge locally uniformly to Psi_n on the whole energy
plane, and every original normalization period is retained. See
[NORMALIZED_PRODUCT_CONSTANT.md](NORMALIZED_PRODUCT_CONSTANT.md) and
`exists_classicalHill_local_complete_normalized_products`.

The scalar's exact value at nonzero potentials is not proved. Therefore
this local nonzero scalar product identity does not close exact source
(52), nor its full W domain or common omitted-index uniformity. Real gap
placement, sharp root estimates (54), rough/global source compatibility
and every main inventory row remain open.

The actual normalized moment family now proves the local near-zero
continuous-potential versions of Lemma 3.1(i)–(iii): exact zeroth periods,
all moment analyticity, and every odd cancellation on one common complex
neighborhood before all positive n,k and moment orders. The exact mapped
energy contour/Jacobian is retained. Shared whole-gap squares yield
actual filled primitive/root quotients through complete high gaps;
constructed low-contour source tubes and a finite intersection remove
the finite-head exception. No numerator root at a branch point is assumed.
See [NORMALIZED_ODD_MOMENTS.md](NORMALIZED_ODD_MOMENTS.md) and
`exists_classicalHill_normalized_all_odd_moments`. Imported source
provenance is recorded in `SHARED_WHOLE_GAP_IMPORT.json`.

The full W domain/rough topology of Lemma 3.1, its collapsed even-moment
clause (iv), sharp moment/root estimates, exact leading scalar at nonzero
potentials, physical frequency/flow identifications and every main
inventory row remain open.

The local actual normalized family now also satisfies the high-tail
part of Lemma 3.1(iv): if the actual analytic squared gap vanishes and
k is above one common cutoff, every positive moment vanishes for every
output n, including n=k. The actual double-root quotient and its disc
square root are constructed from shared verified results. All previous
moment analyticity, zeroth periods and all-mode odd cancellations remain
on the same source neighborhood. See
[NORMALIZED_COLLAPSED_MOMENTS.md](NORMALIZED_COLLAPSED_MOMENTS.md),
`exists_classicalHill_normalized_moments_with_collapsed_tail` and
`SHARED_COLLAPSED_GAP_IMPORT.json`.

The low even collapsed contours and full W/rough-topology version of
Lemma 3.1 remain open. No main inventory row is closed. Sharp normalized
moment/root bounds, exact canonical leading scalar, physical frequency/
Hamiltonian/action identities and the source main flow statements still
require their actual proofs.


### Exact normalized squared-resolvent moment representation

`ClassicalCriticalResolvent.lean`, `CirclePowerIntegrationByParts.lean`
and `ClassicalNormalizedMomentResolvent.lean` prove an actual all-order
representation useful for the estimates after Lemma 3.2 and in Lemma 3.3
(PDF pages 27–30). On one constructed local continuous-potential family,
Omega_nk^m equals 2*pi/(m+1) times the absolutely convergent positive sum
of j*(R e_n)_j times the literal F_k^(m+1)/(lambda-mu_j)^2 contour
integrals. All original modes and the exact Jacobian are retained; mu_j
here is the critical energy, not the source Dirichlet label. The series
outside the integral is justified by an actual Hilbert Bochner integral.

This is not the physical frequency identity (69), a sharp moment estimate
or a global/rough W extension. The canonical leading scalar remains
unfixed at nonzero potentials. See `NORMALIZED_MOMENT_RESOLVENT.md` for
precise scope and remaining obligations. Every main theorem stays open.


### Actual critical gap localization for moment contour shrinking

`ClassicalCriticalGapLocalization.lean` proves actual high critical
energies lie within one quarter gap length of the actual midpoint on a
common complex neighborhood of any continuous source. It also proves an
arbitrarily small coefficient in the bound |lambda-dot_k-tau_k| <=
eta*|gamma_k^2|/k, with one neighborhood and cutoff before all retained
indices, and exact equality at an actual collapsed high gap. It also
proves the continuous-potential version of (37), the relative bound
|lambda-dot_k-tau_k|<=eta*|gamma_k| for every eta>0, using actual counted
endpoint geometry. The energy/midpoint/squared-gap families retain their analyticity. The
result supplies the critical-pole separation on gap-length circles
needed after the exact normalized squared-resolvent moment formula.

This advances the local continuous-potential form of source (37) and
Lemma 2.11(i), PDF pages 16 and 18–19. It does not establish its lp
remainder sequence, the full rough/global W scope, a normalized numerator
zero estimate or a physical frequency identity. Details and selected
source provenance are in `CRITICAL_GAP_LOCALIZATION.md` and
`SHARED_CRITICAL_GAP_IMPORT.json`. All main theorem rows remain open.


### Actual high-gap bounds for normalized second moments

`exists_classicalHill_normalized_second_gap_bounds` constructs one actual
local complex continuous-potential normalized family. With
x_k=norm(classicalHillHighSquaredGap q k)/k², its diagonal second moments
are bounded by B*x_k and distinct-index second moments by B*x_k², for one
B and high cutoff before all q,n,k. All-mode moment analyticity, exact
zeroth periods, odd cancellation and positive high collapsed-gap
cancellation hold on the same neighborhood. Weighted cut-period
homotopies, critical-pole gap-circle separation, all-order actual
critical-kernel bounds and a Hilbert remainder estimate provide the proof.

This is progress toward Lemma 3.3 (PDF pages 27–30), without its full
sharp index dependence or diagonal leading term. It does not identify
physical frequencies through (69), prove the rough/global W statement,
or close a main theorem. See `NORMALIZED_SECOND_GAP_BOUNDS.md` and
`SHARED_CRITICAL_PERIOD_GAP_IMPORT.json` for exact scope and provenance.


### Analytic actual normalized second-moment series

`exists_classicalHill_analytic_normalized_frequency_series` constructs
one local complex continuous-potential actual normalized family before
every n. For each n, the literal positive series sum_k k*Omega_nk^2 is
absolutely convergent, has locally uniform positive partial sums, and
its sum times -12 is analytic. The actual original zeroth periods and
all-mode moment analyticity/odd cancellation are retained.

This advances the summation assertion in Theorem 3.4, (73), PDF page 31.
The physical identity (69) and the finite-gap/density continuation
identifying this candidate with the physical frequency are still open,
as are the full rough/global W domain and action descent. The new tail
estimate uses the actual compatible twice-weighted inverse and a locally
bounded l1 frequency-scale squared-gap sequence; it does not infer
unscaled energy-gap summability. See `NORMALIZED_FREQUENCY_SERIES.md`.
All main theorem inventory rows remain unverified.


### Actual Hminus1 critical basis and original period entries

`exists_analytic_hillHminus_high_critical_points` constructs the actual
simple high energy critical family near any complex Hminus1 potential.
`exists_hillHminus_high_critical_points_free` proves its exact unshifted
free labels despite the auxiliary chart energy shift. The generic
analytic critical-branch theorem and a finite intersection yield
`exists_hillHminus_uniform_numerator_basis`: an entire actual critical
basis with its exact factor and free identities before all indices.

`exists_hillHminus_all_contour_period_data` then constructs one common
Hminus1-open neighborhood of zero covering every original frequency
circle. Every literal 1/(2*pi) period entry is analytic there, and the
full free matrix is exactly the identity. This supplies rough ingredients
for the differential/period construction before Lemma 3.1 (PDF26–27)
and the rough extension in Theorem 3.4 (PDF31). These are basis periods;
the nonzero-potential infinite normalization equations have not yet been
inverted in Hminus1. Full W continuation, rough normalized moments and
physical frequency identities remain open. No main row is closed.
See `HMINUS_PERIOD_DATA.md` and `SHARED_HMINUS_NORMALIZATION_IMPORT.json`.


## Current actual rough second-moment series

Theorem3.4's actual series (73), PDF31, is now constructed near zero on
one Hminus1-open neighborhood before all output indices by
`exists_hillHminus_analytic_normalized_frequency_series` in
`NLS/KdV/HillHminusOneNormalizedFrequencySeries.lean`. It retains the same
weighted normalized moment family, absolute convergence, locally uniform
ordinary positive partial sums and scalar analyticity of the exact -12
correction candidate. The actual Miura L2 source provides a genuine rough
locally bounded l1 majorant; the fixed energy shift and actual canonical
counted pair membership are proved in
`HillHminusOneCanonicalFrequencyGaps.lean` and
`HillHminusOneFrequencyGapMajorant.lean`. See `HMINUS_FREQUENCY_SERIES.md`.

Physical identity(69), Lemma3.2, PDF26-27, full W, action descent, weighted
target-space/asymptotic/compact-derivative assertions and actual physical
Birkhoff/PDE flows remain separate open obligations. No main row above is
closed by this local scalar series construction.


## Current real rough Miura and energy-psi adapter

The psi family (52)-(53), PDF21, used by the frequency extensions in
Theorems1.2 and1.9, PDF4/6, now has a proved real-preserving rough Miura
adapter to the verified NLS normalized psi theorem. See
`exists_hillHminus_real_sourcePsi_data` and
`exists_hillHminus_real_entire_energyPsi`: at every physically real rough
base potential they construct a common rough-open all-index neighborhood,
actual normalized NLS roots/periods and jointly analytic entire-energy
candidates with the exact shifted-square 2z factor identity. Definitions
and qualifications are detailed in `REAL_MIURA_ENERGY_PSI.md`.

The retained exact periods are still the original NLS frequency periods.
Hill root sign/parity, mapped positive/negative energy contours, lowest-cut
analysis, Hill energy normalization, overlap compatibility and agreement
with the earlier local rough normalized family are separate open steps.
Neither (52)-(54) in full W nor any main theorem is closed by this adapter.


## Current actual root parity and energy-pullback normalization

Toward (52)-(53), PDF21, `EvenDiscriminantPeriodicEndpoints.lean` and
`EvenDiscriminantCanonicalRoot.lean` now prove complete actual endpoint
reflection and oddness of the actual canonical root from the even trace,
including central and collapsed pairs without a real-type restriction.
`EvenPsiAntisymmetricPeriods.lean` uses the verified original-circle
periods of the same NLS family and the literal negated-circle substitution
to prove the signed difference of Kronecker periods.

`exists_hillHminus_real_normalized_energy_pullbacks` constructs one
complex Hminus1-open neighborhood at every real rough base potential,
before all numerator and circle indices, retaining actual analytic
energy candidates, actual isolating-circle families and exact positive
2pi Kronecker periods under z->z^2-C.energyShift with the Jacobian 2z.
The actual NLS root remains evaluated at the lifted frequency. A global
Hill energy-root function, chart independence, lowest-cut continuation,
overlap identification and agreement with the earlier local rough
normalized family are not yet asserted. See `MIURA_ROOT_PULLBACK_PERIODS.md`.
No main theorem row is closed by this normalization adapter.


## Current actual energy roots and root chart agreement

Toward the actual normalized psi family (52)-(53), PDF21, the theorem
`exists_hillHminus_real_normalized_mapped_energy_periods` now constructs
one common complex rough-open neighborhood at every real Hminus1 base
potential, with actual jointly analytic Hill energy root, entire
numerators and actual smooth shifted-square contours of winding one and
exact raw 2pi Kronecker energy periods. Mapped endpoint energies satisfy
the actual independent Hill characteristic equation.

`HillHminusMiuraChart.energyRoot_eq_on_real_input` proves root agreement
on the full common energy domain of two real-shift actual charts at a
real input, using proved high-band placement and the actual canonical-root
sign. `energyRoot_germ_eq_on_real_input` proves equality of the full
complex energy/rough-input germs. Details are in
`ENERGY_ROOT_CHART_AGREEMENT.md`. Entire-numerator chart agreement,
canonical leading scalar one, the earlier local weighted-family
identification and the full source main theorems are separate open steps.
No main inventory row is closed.


## Current actual continued-root compatibility

Toward the actual normalized psi family (52)-(53), PDF21, and the moment
identities leading to frequency(69), the new root comparison retains the
old independent rough Hill trace and original source continuation root.
`hillHminusRadicand_ne_zero_of_real_of_im_ne_zero` excludes nonreal zeros
at every physically real Hminus1 input. `nonreal_mem_hillHminusContinuationDomain`
places every nonreal energy in the original radial source domain.
`HillHminusMiuraChart.energyRoot_eq_continuedRoot_at_zero` proves the free
normalization from actual high-band signs. The theorem
`exists_hillHminus_energyRoot_continuation_agreement` chooses one norm
ball before all real inputs and all energies, proving equality on full
common energy domains and equality of full complex energy/source germs.
See `CONTINUATION_ROOT_AGREEMENT.md` for exact scope. A uniform complex
rough neighborhood for all contours and actual entire-numerator
identification are still separate open steps. No main inventory row closes.


## Current complete rough critical energies and genuine principal coefficients

Toward the entire numerator in (52)-(53), PDF21, and the physical moment
formula(69), PDF26, `hillHminus_critical_real_and_simple` proves reality and
simplicity of every actual rough Hill critical point at every physically
real Hminus1 input. `exists_hillHminus_complete_real_critical_energies`
constructs one chart before every real input, energy and positive critical
index, with a complete strictly increasing real energy sequence and full
complex rough-input analytic germs. The shifted central energy is not a
critical point.

`hillHminusMiuraEnergyCriticalResidue_eq_signed` proves the exact transfer
2 beta_j (r_j-r_-j) between the actual energy and canonical signed NLS
principal coefficients. `_principal_limit` proves its punctured-limit
meaning. `exists_hillHminus_real_energy_critical_residues` constructs one
actual normalized NLS data set and one common complex rough-open
neighborhood before all indices, retaining analytic coefficient germs,
genuine principal limits and joint central filling. Details and precise
qualifications are in `CRITICAL_ENERGY_RESIDUES.md`. A Hilbert coefficient
sequence, exterior remainder estimate and numerator representation are
still required. All source main-theorem inventory rows remain OPEN.


## Current full entire canonical Hilbert realization

Toward (52)-(53), PDF21, and the moment/frequency formula(69), PDF26,
`sourcePsiCriticalInterpolation_tsum_eq_quotient` identifies the actual
ordinary absolute critical interpolation with the NLS numerator divided
by its actual discriminant derivative. `memℓp_sourcePsiCriticalResidue_two`
is derived from proved 4/|j| small-circle residue bounds. The actual energy
coefficient vector has exact normalization A_j/(2pi*j).

`hillHminusMiura_energy_principal_series` proves the absolute positive
energy principal series off its poles and central ramification point.
`hillHminusMiuraEnergyPsi_eq_canonicalHilbert` fills the canonical critical
basis and proves the entire numerator identity at every energy, including
critical and central points. The theorem
`exists_hillHminus_real_canonical_numerator_representation` constructs
actual normalized NLS data and one complex rough-open neighborhood before
all real inputs, numerator indices and energies. The basis and coefficient
vector have proved genuine Hilbert membership; source joint Banach
analyticity of these vectors and identification with the older weighted
normalized family are separate steps. Details and remaining obligations
are in `CANONICAL_NUMERATOR_REPRESENTATION.md`. All main rows remain OPEN.


## Intrinsic critical labels and compatible complex germs

`HillHminusOneCriticalChartIndependence.lean` identifies actual complete strictly ordered energy labels on every real chart overlap. `SimpleRootGermUniqueness.lean` proves continuous simple-root germ uniqueness from an actual moving divided difference. `HillHminusOneCriticalChartGerms.lean` proves nearby complex criticality and equality of the actual canonical chart germs. These support coherent spectral charts but do not identify the old weighted normalized family or verify any main theorem. See `CRITICAL_CHART_GERMS.md`.


## Canonical and earlier critical-basis identification

`FreeHillCriticalEnergies.lean` proves the exact complete actual free critical energy set. `HillHminusOneCanonicalCriticalCompatibility.lean` fixes canonical free labels, propagates actual branch/germ agreement along real radial paths, identifies all filled scalar/Hilbert bases and represents the actual Miura numerator in the earlier verified period-data Hilbert class on a single common ball. This supplies a necessary dependency for coherent spectral charts and normalized-family identification; actual original contour normalization and all main theorem conclusions remain open. See `CANONICAL_CRITICAL_COMPATIBILITY.md`.


## Canonical roots on original contours

`HillHminusOneRealContinuationBands.lean` proves actual real trace and negative radicand signs on the original continued domain. `HillHminusOneOriginalContourRoots.lean` uses the closed canonical gap discriminant bound to prove canonical root-domain membership of all original frequency circles, including real crossings, and constructs a common-ball exact root/full complex germ agreement. Actual period transfer and every main theorem remain open. See `ORIGINAL_CONTOUR_ROOTS.md`.


## Indexed band geometry for contour period transfer

`SourceContourAdjacentBands.lean` identifies bands between actual critical frequencies and at actual period-circle crossings. `HillHminusOneOriginalContourBands.lean` proves actual uniform critical energy separation, shifted-square order and a common-neighborhood identification of all original crossings with bands k-1/k. This supplies the band hypotheses for contour homotopy; actual integral equality and all main theorem conclusions remain open. See `ORIGINAL_CONTOUR_BANDS.md`.


## Actual normalized periods on the original contours

`ShiftedSquaredCircleBandHomotopy.lean` proves actual integral equality through a domain-preserving homotopy. `HillHminusOneEnergyBands.lean` proves its real energy-band hypotheses inside the actual canonical root domain. `HillHminusOneOriginalNormalizedPeriods.lean` transfers the actual mapped NLS normalization to the literal original contour Kronecker periods, with one data set and ball before all real rough inputs and positive mode pairs. This proves the necessary original period normalization; weighted inverse-column identification and all main theorem conclusions remain open. See `ORIGINAL_NORMALIZED_PERIODS.md`.


## Actual candidate and weighted normalized-family identification

`HillHminusOneMiuraNormalizedIdentification.lean` uses the actual Kronecker periods and genuine Hilbert coefficients to determine the inverse column and identify the entire Miura numerator with the earlier weighted normalized family on one physical-real ball. Its existence theorem supplies the analytic two-weighted inverse families, their free values, norm bounds and exact compatibility from the verified construction. Global and complex-source extensions and every main theorem conclusion remain open. See `MIURA_NORMALIZED_IDENTIFICATION.md`.


## Actual complex-source normalized-family identification

`PeriodOneRealFormIdentity.lean` proves the physical real-form hypotheses and reuses the canonical connected identity principle. `HillHminusOneComplexNormalizedIdentification.lean` identifies the actual Miura family with the constructed weighted normalized family on the whole common complex ball, retaining the actual weighted analytic inverse data. The three canonical real-line/real-form helper modules are source-base identical and newly selected for explicit validation. This is a local complex-source result; global and all main physical frequency conclusions remain open. See `COMPLEX_NORMALIZED_IDENTIFICATION.md`.


## Actual Miura moments and analytic correction series

`HillHminusOneMiuraFrequencySeries.lean` defines literal original-circle actual numerator moments, their signed second-moment terms and correction. Full complex numerator identification transfers all-order analytic moments, exact zeroth periods, odd cancellation, absolute convergence, analytic correction and locally uniform positive partial sums on one common rough ball around zero. This advances Lemma 3.1 and the spectral-series part of Theorem 3.4 (73), PDF pages 23–26 and 31. Physical identity (69), global W, action descent and every main theorem remain open. See `MIURA_FREQUENCY_SERIES.md`.


## Actual spectral invariance toward action descent

`HillHminusOneMiuraSpectralInvariance.lean` transports intrinsic Hill discriminant equality to actual normalized numerator and canonical-root invariance on a fixed real-type chart at any real rough base. `HillHminusOneIsospectralSheets.lean` fixes continued-root signs and logarithmic phases on all original contours in one common near-zero ball. `HillHminusOneSpectralMiuraFrequencySeries.lean` constructs ONE actual analytic convergent moment/series family that is spectrally invariant on the SAME ball. The two canonical NLS isospectral modules are reused unchanged. This advances the spectral-invariance ingredient following Theorem 3.4 (73), Remark 3.5, PDF pages 31–32; physical frequency identity (69), action-coordinate realization/descent, global W and every main theorem remain open. See `SPECTRAL_INVARIANCE.md`.


## Actual physical quartic coefficient preceding frequency (69)

`HillSmoothQuarticEnergyCoefficient.lean` proves the physical smooth real period-one mean-zero full-circle quartic remainder, literal normalized contour error, limit -H1/4 and physical Hamiltonian recovery by multiplication by -4. `QuarticContourCoefficient.lean` proves the weighted scalar and residue extraction, and `UpperReflectionCircleIntegrability.lean` supplies integrability without continuation through real cuts. The final physical corollaries derive Fourier parity/reality rather than assume independent spectral hypotheses. The source input is selectively imported from the verified estimates snapshot with six local compatible sources retained, one new compatibility proof adapted and exact eighth-record provenance. This advances the physical coefficient input on PDF page 26 in the proof of Lemma 3.2 (69); exact finite-gap contour independence, the stronger source remainder, actual angle bracket, action/frequency/PDE identification and all main theorems remain open. See `PHYSICAL_QUARTIC_COEFFICIENT.md`.


## Exact physical finite-gap quartic identity

`HillFiniteGapExterior.lean` defines actual finite-gap spectral data by finitely many noncollapsed positive characteristic gaps, proves a collapsed-tail equivalent, derives a filled-square exterior from genuine high-label localization and finite band coverage, and proves analyticity and centered-circle radius independence for every even primitive power. `HillFiniteGapQuarticEnergy.lean` identifies each sufficiently large centered quartic contour exactly with -H1/4 at actual smooth real period-one mean-zero finite-gap potentials, using the already proved physical contour limit. Ten shared dependencies are unchanged and seven local variants retained, with ninth-record provenance. This proves the actual real L2 finite-gap exterior consequence of Lemma 2.6(i), PDF15, and the physical centered-circle energy input at the start of Lemma 3.2, PDF26; it does not prove angle brackets/frequency69, rough finite-gap regularity, general noncentered-loop identities or main theorems. See `FINITE_GAP_QUARTIC_IDENTITY.md`.


## Actual Dirichlet / monodromy-kernel boundary input

`ClassicalHillDirichletBoundaryPairing.lean` proves squared and mixed actual scalar Hill boundary pairings at arbitrary second energies, without dividing by the energy difference. `ClassicalHillTracePairingKernel.lean` proves endpoint determinant one, constructs the actual fundamental-state quadratic kernel, proves its spatial derivative and exact Dirichlet pairing, and solves that pairing off the energy diagonal. This is necessary input toward the angle-discriminant bracket preceding source Lemma 3.2 (69), PDF26, not that bracket itself. Actual potential-derivative identification, angle interpolation and physical frequency remain open. See `DIRICHLET_TRACE_KERNEL_PAIRING.md`.


## Actual gradient and scalar Gardner trace involution

`ClassicalHillDiscriminantGradient.lean` identifies the literal scalar kernel with the actual complex potential Frechet derivative of the Hill discriminant through the actual IVP basis bridge and affine source chain rule, at all complex energies including zero. It also proves mean-zero Dirichlet squared-state directions and exact source variation. `ClassicalHillGardnerTraceInvolution.lean` proves a closed differential system, matching endpoints and an explicit concomitant, giving zero actual scalar Gardner trace pairings at all energy pairs and zero potential derivative of every discriminant along every trace direction. Two existing canonical IVP helpers are explicitly selected, with only their old heartbeat overrides removed and their mathematical content unchanged. This is physical variational input toward the angle-discriminant identity preceding Lemma 3.2 (69), PDF26, not the angle identity or a main theorem. See `ACTUAL_GARDNER_TRACE_INVOLUTION.md` and `CANONICAL_TRACE_GRADIENT_REUSE.json`.


## Actual normalized Dirichlet / discriminant bracket

`HillL2TraceGradients.lean` identifies actual complex L2 discriminant source derivatives and almost-everywhere spatial derivatives with literal rough scalar trace-gradient curves. `HillDirichletDiscriminantBrackets.lean` uses actual real Fourier truncations, labelled simple Dirichlet energies and positive physical mass to prove the normalized scalar Gardner bracket: exact cross-multiplied actual sheet-root identity at every energy, exact off-diagonal source quotient, and exact filled diagonal value -r_D/2, including zero energy. `QuadraticDividedDifference.lean` justifies the ramified punctured-square limit. Thirty-nine shared files are unchanged; seven compatible local variants remain unchanged, with tenth-record provenance. This supplies the actual normalized Dirichlet bracket toward the angle-discriminant identity preceding Lemma 3.2 (69), PDF26, not that angle identity or a main theorem. See `NORMALIZED_DIRICHLET_TRACE_BRACKET.md`.


## Actual Gardner source tangents and spectral stationarity

`HillL2GardnerTraceInvolution.lean` proves actual complex rough scalar trace involution, matching spatial-gradient endpoints and zero physical mean by norm continuity and finite Fourier synthesis. `HillL2GardnerDirections.lean` constructs actual coefficient-space tangents with the exact physical Fourier representative, zero mean and even support; every trace source derivative vanishes and actual normalized Dirichlet branch source derivatives reproduce the bracket. `HillL2GardnerSpectralStationarity.lean` proves mixed source/spectral trace stationarity by analytic second-derivative symmetry, and source stationarity of the actual continued primitive and root on precisely the actual continuation domain. This advances the variational input toward normalized spectral differentials and the angle-discriminant identity preceding Lemma 3.2 (69), PDF26; it does not yet prove those normalization/angle identities, actual isospectral integral curves, physical frequency69 or any main theorem. See `ACTUAL_GARDNER_SOURCE_TANGENTS.md`.


## Latest actual normalized differential stationarity

See `NORMALIZED_GARDNER_STATIONARITY.md`. Prior strict validation of 572 unchanged selected sources; strict default-limit dependency-order compilation of 239 byte-identical shared normalization dependencies; strict compilation of six new stationarity modules; then a fresh combined transitive axiom audit of all 817 selected modules. Twelve compatible local shared variants are retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 817-module rebuild is claimed.

Fresh audit: 8045 selected declarations; 30623 imported NLS declarations, permitted standard axioms only. The actual implicit normalized differential germ is stationary along every constructed Gardner direction. Abelian-angle variation, physical frequencies and all main theorem rows remain open.

The six new proof modules are `HillGardnerLocalRootVariation`, `ParametricCircleStationarity`, `HillAbelianGardnerPeriods`, `HillMixedGardnerVariation`, `ImplicitRootStationarity` and `HillNormalizedGardnerStationarity`. The existence theorem constructs a genuine analytic local family at every real period-one L2 base and n>0, retains all actual mixed normalization periods, agrees with the global normalized differential at the base, and proves all complex Gardner source variations vanish. It does not yet identify actual Abelian angles or prove the physical frequency identities (69)/(84). All main source statements remain open.


## Latest canonical normalized differential stationarity

Every differentiable extension agreeing with the genuine normalized differential at nearby real period-one L2 potentials is stationary along every actual complex Gardner direction. The same constructed analytic family now has exact nearby-real canonical agreement; actual real affine curves and complex Fourier decomposition prove extension independence. See `CANONICAL_GARDNER_STATIONARITY.md`.

Prior strict validation of 817 selected sources, of which 816 are unchanged; strict dependency-order compilation of eight byte-identical shared nearby-matching sources; strict final compilation of the extended stationary-branch module and three new proof modules; then a fresh combined transitive axiom audit of all 828 selected modules. Twelve compatible local variants are retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 828-module rebuild is claimed.

Fresh audit: 8090 selected and 30674 imported NLS declarations, permitted axioms only. Abelian-angle variation, physical frequency identities and all main theorem conclusions remain open.


## Latest actual Abelian source stationarity

Actual symmetric gap data, filled Cauchy unit/root, normalized deflated differential and normalized cosine primitive are stationary along every complex Gardner direction. Actual analytic sheeted Dirichlet integral branches now satisfy the exact remaining terminal-phase chain rule, including terminal bandedges without dividing by a vanishing sine. See `ABELIAN_SOURCE_STATIONARITY.md`.

Prior strict validation of all 828 unchanged selected sources; strict dependency-order validation of 27 shared sources (26 byte-identical imports and one compatibility import reusing an already proved local spectral-derivative theorem); strict final compilation of seven new proof modules; then a fresh combined transitive axiom audit of all 862 selected modules. Twelve compatible local variants retained unchanged. Exact selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 862-module rebuild is claimed.

Fresh audit: 8254 selected and 30841 imported NLS declarations, permitted axioms only. Terminal-phase evaluation, canonical orientation, full angle variation and the physical frequencies/main theorem conclusions remain open.


## Latest actual moving Dirichlet sheet variation

Actual Dirichlet slope and moving sheet-root Gardner derivatives are proved, including filled spectral-diagonal values, zero energy and terminal bandedges. The moving-sheet formula uses the genuine source chain rule and actual differentiated monodromy determinant; it does not divide by the sheet value. See `DIRICHLET_SHEET_VARIATION.md`. Terminal-phase evaluation and the final angle/frequency identities remain open.

Prior strict validation of all 862 unchanged selected sources; strict dependency-order compilation of four new proof modules; then a fresh combined transitive axiom audit of all 866 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 866-module rebuild is claimed.

Fresh audit: 8299 selected and 30885 imported NLS declarations, permitted axioms only. All main theorem inventory rows remain OPEN.


## Latest actual terminal and Abelian integral variation

The actual sheeted Dirichlet terminal phase now has Gardner derivative I*U(mu)*K_k(b), and genuine analytic single-gap Abelian integrals have derivative psi_n(mu)*K_k(b), with filled diagonal K_k(mu)=-1/2. Both formulas retain terminal bandedges and zero energy at open selected gaps. Nearby-real agreement determines the required complex source jets; no division by sine or cosine is used. See `TERMINAL_ANGLE_VARIATION.md`.

Prior strict validation of all 866 unchanged selected sources; strict dependency-order compilation of one byte-identical canonical algebra helper and three new proof modules; then a fresh combined transitive axiom audit of all 870 selected modules. The reused helper precedes every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 870-module rebuild is claimed.

Fresh audit: 8332 selected and 30916 imported NLS declarations, permitted axioms only. Infinite/closed-gap summation, canonical angle orientation and the physical frequency/main theorem conclusions remain open. All main inventory rows remain OPEN.


## Latest actual Dirichlet interpolation exterior

The actual filled Dirichlet kernel is entire and has a jointly analytic physical source chart. A weighted scalar IVP argument gives the actual full-plane rough Dirichlet free-error estimate and a zero-free exterior lower bound, uniformly on bounded complex L2 potential families. The actual normalized numerator/characteristic quotient now has inverse-energy decay; its literal outer Cauchy errors vanish uniformly for bounded evaluations. See `DIRICHLET_INTERPOLATION_EXTERIOR.md`.

Prior strict validation of all 870 unchanged selected sources; strict dependency-order compilation of one byte-identical canonical sine-exterior helper and five new proof modules; then a fresh combined transitive axiom audit of all 876 selected modules. The reused helper precedes every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 876-module rebuild is claimed.

Fresh audit: 8376 selected and 30953 imported NLS declarations, permitted axioms only. The residue expansion and gap-label interpolation, infinite/closed-gap angle summation, canonical orientation and physical frequency/main theorem conclusions remain open. All main inventory rows remain OPEN.


## Latest actual Dirichlet spectral exhaustion and interpolation

The actual Dirichlet characteristic has no root at or below the periodic ground, and all its complex zeros are exactly the positive closed-gap Dirichlet labels. High energy circles select exactly the first N roots. The genuine filled positive-index interpolation sums now converge to -psi_n(w)/2 uniformly on every bounded complex energy disc, including all Dirichlet diagonals and collapsed physical gaps. See `DIRICHLET_INTERPOLATION.md`.

Prior strict validation of all 876 unchanged selected sources; strict dependency-order compilation of four byte-identical canonical pole/Cauchy helpers and four new proof modules; then a fresh combined transitive axiom audit of all 884 selected modules. The reused helpers precede every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 884-module rebuild is claimed.

Fresh audit: 8483 selected and 31027 imported NLS declarations, permitted axioms only. Absolute summability and the actual infinite Abelian source/angle sum, canonical orientation and physical frequency/main theorem conclusions remain open. All main inventory rows remain OPEN.


## Latest actual infinite Abelian angle variation

The actual regular correction sum is absolutely convergent and locally complex analytic, with its Gardner derivative now evaluated using a justified common-neighborhood derivative limit. Open and closed other gaps are included. Adding the actual own-gap terminal angle gives a local real physical Abelian angle A with D A[X_b] = -psi_n(b)/2 at every complex b, including filled spectral diagonals and terminal bandedges. See `SUMMED_ABELIAN_ANGLE.md`.

Prior strict validation of all 884 unchanged selected sources; strict dependency-order compilation of 75 byte-identical shared analytic correction dependencies; strict compilation of one byte-identical canonical holomorphic-limit helper and five new proof modules; then a fresh combined transitive axiom audit of all 965 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, all source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 965-module rebuild is claimed.

Fresh audit: 8939 selected and 31478 imported NLS declarations, permitted axioms only. Canonical Birkhoff angle orientation/identification, physical Hamiltonian frequency identities and the main theorem conclusions remain open. All eleven main inventory rows remain OPEN.


## Latest physical Abelian phase, period duality and corrected time sign

A branch-independent actual Abelian phase is constructed on every open selected gap, with unit norm on real data, local complex L2 analyticity, continuity across terminal angle cuts and exact trace/normalized-contour derivative formulas. The actual Fourier contour tangents have proved L2 norm integrability and exact period duality. See `ABELIAN_PHASE_PERIODS.md`.

The physical PDE linearizations prove positive imaginary cubic/fifth-order Fourier frequencies. The signed coordinate flow and both nonextension adapters are corrected to the positive exponent at positive modes, consistent with (80)/(91); the negative p.3 evolution sign is recorded as a source inconsistency. Actual Birkhoff/PDE identification remains open.

Prior strict evidence for the 965-module baseline; all 960 unaffected source files and nineteen provenance records remain unchanged. Strict dependency-order rebuild of all six affected prior selected modules, including five changed source files, and all five new modules; then a fresh combined transitive axiom audit of all 970 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, frozen source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No full 970-module rebuild is claimed.

Fresh audit: 8988 selected and 31527 imported NLS declarations, permitted axioms only. Physical action-gradient/canonical angle/Birkhoff identification and all eleven main theorem rows remain OPEN.


## Latest actual Abelian coordinates through closed gaps and weighted continuity

The literal physical coordinates `z_n = sqrt(I_n) P_n` now have genuine complex L2 analytic scalar extensions at every real source, including where their own gap is closed. Their exact normalization is `abs(z_n)^2 = I_n`; they vanish precisely at closed gaps. The signed sequence lies in the actual weighted target `w(2n)*(1+abs(n))^(1/2)`, has zero mode and signed conjugation, and satisfies `z_n*z_-n=I_n`.

`hillPhysicalAbelianMap` is constructed on the entire real weighted L2 source and is continuous in the full native weighted norm. The proof uses actual locally uniform action tails, continuous summed squared amplitudes and exact signed Parseval. See `ABELIAN_COORDINATES.md`. Full Banach analyticity, canonicality, the exact Fourier differential at zero, global inverse and rough negative-regularity realization remain open.

Prior strict evidence for all 970 unchanged selected baseline sources; strict dependency-order compilation of eleven byte-identical shared action-prefactor sources, one byte-identical canonical continuity criterion and six new proof modules; then a fresh combined transitive axiom audit of all 988 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1011 frozen source/checker/provenance hashes, 21 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 988-module rebuild is claimed.

Fresh audit: 9180 selected and 31737 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest actual action derivatives and all-gap coordinate variation

The actual action has a genuine local complex L2 analytic fixed-contour extension at every real source, including a closed selected gap. Every differentiable physical matching extension has the same derivative on period-one directions: `D I_n[h] = -1/pi contour_n D Delta[h]/R`. Compact-contour differentiation, the actual root equation, mixed derivative symmetry and integration by parts prove the formula; it is not a supplied action-gradient hypothesis.

Every actual coordinate now satisfies `D z_n[X_b] = -i psi_n(b) z_n/2` at all real sources, and `D z_n[Y_m] = i delta_mn z_n` for the actual normalized contour tangents. Closed selected gaps are included, and the formulas are independent of the differentiable nearby-real matching extension. The actions are stationary along both families of directions. See `ACTION_COORDINATE_VARIATION.md`.

Prior strict evidence for all 988 unchanged selected baseline sources; strict dependency-order compilation of three byte-identical canonical calculus helpers and five new proof modules; then a fresh combined transitive axiom audit of all 996 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1020 frozen source/checker/provenance hashes, 22 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 996-module rebuild is claimed.

Fresh audit: 9210 selected and 31761 imported NLS declarations, permitted axioms only. Physical Gardner action-gradient identification of `Y_m`, canonical brackets, full Banach analyticity, inverse/rough realization and all eleven main theorem rows remain OPEN.


## Latest unique physical action Hamiltonians and mixed coordinate identities

The actual normalized contour tangent `Y_m` now satisfies the physical Gardner weak identity against every periodic AC test with continuous periodic derivative. Its bounded test pairing uses the actual source-to-physical L2 map. Verified unit Fourier waves and their actual derivatives separate the physical tangent space, so `Y_m` is the unique period-one mean-zero weak Hamiltonian vector of the actual action, including at a closed selected gap.

Consequently, actual actions commute and `D z_n[X_(I_m)] = i delta_mn z_n` holds for every actual physical coordinate and every matching differentiable extension, including closed gaps. On an open selected gap, a genuine local analytic real angle has phase `exp(-i theta_n)` and `D theta_n[X_(I_m)] = -delta_mn`. This verifies the mixed action orientation; full angle-angle and coordinate-coordinate canonicality is not asserted. See `PHYSICAL_ACTION_HAMILTONIANS.md`.

Prior strict evidence for all 996 unchanged selected baseline sources; strict dependency-order compilation of one byte-identical canonical wave calculus helper and five new proof modules; then a fresh combined transitive axiom audit of all 1002 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1027 frozen source/checker/provenance hashes, 23 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1002-module rebuild is claimed.

Fresh audit: 9274 selected and 31820 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest real action fields and negative-mode physical variation

The actual physical action Hamiltonian vector is now proved real in the conjugate Fourier sense, with no gap-opening assumption. The proof uses actual real-source action differentials, physical Fourier conjugation, verified wave tests and the physical weak Hamiltonian identity. Every weak Hamiltonian vector matching the actual action has that real symmetry; no vector reality is supplied as a hypothesis.

The negative physical coordinates have genuine complex differentiable matching germs through every closed selected gap, and every differentiable matching extension obeys `D z_-n[X_(I_m)] = -i delta_mn z_-n`. Together with the proved positive-mode law, the actual infinitesimal action dynamics has the full signed physical orientation. No full power-series analyticity of the negative germs or Banach-valued map is asserted by this step. See `REAL_SIGNED_ACTION_FIELDS.md`.

Prior strict evidence for all 1002 unchanged selected baseline sources; strict dependency-order compilation of one byte-identical canonical real-axis calculus helper and five new proof modules; then a fresh combined transitive axiom audit of all 1008 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1034 frozen source/checker/provenance hashes, 24 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1008-module rebuild is claimed.

Fresh audit: 9295 selected and 31840 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest signed scalar analyticity and action critical locus

The actual negative scalar coordinate now has a genuine complex L2 analytic matching extension through every closed selected gap. The previously recorded power-series gap for this scalar coordinate is closed: conjugating source and target preserves analyticity on a genuine complex neighborhood, using the verified canonical Banach holomorphic calculus. Full Banach-valued coordinate-map analyticity remains open.

The actual action product `I_n=z_n*z_-n` determines its differential on every complexified physical period-one tangent, for every differentiable matching extension. At a closed selected gap that entire differential vanishes, so the physical weak action Hamiltonian vector vanishes. Conversely, the proved mixed coordinate identity forces the actual normalized contour vector to be nonzero at an open selected gap. Both the actual action critical locus and the actual action Hamiltonian-vector zero locus are exactly the closed-gap locus. See `SIGNED_ANALYTIC_ACTION_CRITICAL_LOCUS.md`.

Prior strict evidence for all 1008 unchanged selected baseline sources; strict dependency-order compilation of sixteen byte-identical canonical holomorphic calculus dependencies and three new proof modules; then a fresh combined transitive axiom audit of all 1027 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1054 frozen source/checker/provenance hashes, 25 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1027-module rebuild is claimed.

Fresh audit: 9402 selected and 31847 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest physical KdV and KdV2 spectral/action stationarity

Both actual smooth PDE fields now have explicit Fourier velocities that reconstruct their literal physical right sides, are real on real sources and have zero mean. A reusable actual trace-kernel concomitant proves each actual L2 Hill discriminant has zero source differential along these fields, at every complex energy and smooth complex period-one source. For real sources, every differentiable matching actual action extension has zero derivative along either PDE field, at open or closed selected gaps. Source mean zero is not required.

The proof computes the two exact Lenard seeds and uses actual scalar fundamental solutions, bounded physical Fourier analysis, the actual trace gradient and the previously proved universal action contour derivative. No isospectral evolution or frequency formula is assumed. See `PHYSICAL_PDE_STATIONARITY.md`. Coordinate phase velocities, actual Hamiltonian frequency identities and flow existence remain open.

Prior strict evidence for all 1027 unchanged selected baseline sources; strict dependency-order compilation of three new proof modules; then a fresh combined transitive axiom audit of all 1030 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1057 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1030-module rebuild is claimed.

Fresh audit: 9454 selected and 31899 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest actual Dirichlet and moving-sheet PDE velocities

The actual KdV and KdV2 Fourier fields now have their exact Dirichlet velocities `D mu=r_D*K` and moving signed-sheet velocities `D r_D=Delta*Delta_E*K`. The coefficients are computed from the literal PDE fields and actual characteristic derivative, with the physical mass normalization proved. Every analytic actual Dirichlet branch is covered, including terminal band edges and closed selected gaps. Source mean zero is not required.

The mixed-state boundary pairing gives the actual slope derivative directly; the moving-sheet proof uses the actual Wronskian energy identity and never divides by the sheet value. These are the two endpoint velocities needed by the actual Abelian angle calculation. Full coordinate phase/frequency identification and solution-flow existence remain open. See `PHYSICAL_DIRICHLET_MOTION.md`.

Prior strict evidence for all 1030 unchanged selected baseline sources; strict dependency-order compilation of four new proof modules; then a fresh combined transitive axiom audit of all 1034 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1061 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1034-module rebuild is claimed.

Fresh audit: 9483 selected and 31928 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest actual normalized differential stationarity for both PDEs

Every fixed tangent annihilating all actual Hill traces now has proved stationarity of the actual continued primitive, local roots, gap data and deflation, intrinsic and free-tail periods, and the full Hilbert-valued normalization equation. Its invertible implicit derivative constructs ONE analytic normalized root branch stationary in every such tangent. ONE genuinely analytic canonical numerator germ matches the physical family near the real base, at all energies, with the same stationarity.

The actual physical KdV and KdV2 directions discharge the trace condition. The article adapter constructs ONE genuine normalized numerator germ stationary in both fields, through closed selected gaps as well. Filled-gap normalized differential charts and actual Abelian primitives inherit the source stationarity. At an open selected gap only the moving terminal phase contributes to the actual Abelian integral derivative, including terminal band edges. See `TRACE_STATIONARY_NORMALIZATION.md`.

Prior strict evidence for all 1034 unchanged selected baseline sources; strict dependency-order compilation of nine new proof modules; then a fresh combined transitive axiom audit of all 1043 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1070 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1043-module rebuild is claimed.

Fresh audit: 9523 selected and 31968 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest actual PDE derivatives of the physical Abelian angle

The checked terminal-angle patch is promoted. Both actual physical PDE fields now have proved terminal-angle velocities, including terminal bandedges. The same actual first-variation data compute genuine Abelian integral derivatives and every matching regular correction derivative at both open and closed terminal gaps.

Normal analytic convergence justifies differentiation of the infinite physical correction sum. Adding the own terminal angle cancels its single subtraction. For ONE genuinely complex-L2-analytic raw physical angle germ A=epsilon-pi+S, partial sums of psi_n(mu_k)*K_k converge to DA[V] for BOTH literal physical KdV/KdV2 fields. The own selected angle gap must be open; arbitrary other gaps may be closed. No source mean-zero assumption. See `ACTUAL_ABELIAN_PDE_MOTION.md`.

Prior strict evidence for all 1043 unchanged selected baseline sources; strict dependency-order compilation of eleven new modules; then a fresh combined transitive axiom audit of all 1054 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1081 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1054-module rebuild is claimed.

Fresh audit: 9590 selected and 32035 imported NLS declarations, permitted axioms only. The actual spectral sums still need evaluation as the Hamiltonian frequencies (69)/(84). All eleven main theorem rows remain OPEN.


## Latest actual PDE coordinate derivatives at every gap

Both literal physical PDE fields now have proved scalar coordinate derivatives at EVERY own and other gap. Closed own-gap velocities are zero by actual terminal-factor first variations. Open own-gap velocities combine the genuine physical phase derivative with stationarity of the actual action amplitude. The result applies to every differentiable nearby-real physical matching coordinate extension.

ONE actual complex-L2-analytic scalar coordinate germ has BOTH physical PDE derivative limits and one physical matching neighborhood. Every closed-gap term in the coordinate series vanishes. At a finite-gap source with all gaps above N closed, both actual derivatives equal the finite spectral sum through N multiplied by i*z_n. No mean-zero or own-gap opening hypothesis in the all-gap coordinate statements. See `ACTUAL_ALL_GAP_PDE_COORDINATES.md`.

Prior strict evidence for all 1054 unchanged selected baseline sources; strict dependency-order compilation of six new modules; then a fresh combined transitive axiom audit of all 1060 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1087 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1060-module rebuild is claimed.

Fresh audit: 9613 selected and 32058 imported NLS declarations, permitted axioms only. The finite spectral sums still need evaluation as the Hamiltonian frequencies (69)/(84). All eleven main theorem rows remain OPEN.


## Latest actual finite-gap Dirichlet frequency contours

The actual normalized numerator divided by the actual Dirichlet characteristic now has a proved finite principal-part representation. Its own index is retained even at a closed gap. Analytic test functions give exact residue contour coefficients on common actual zero-free energy circles; all polynomial residue moments are independent of a valid cutoff containing that index.

The two actual physical PDE velocity sums have exact expressions in those moments and exact Dirichlet polynomial contour formulas. Both actual coordinate derivatives equal the resulting contour coefficients times i*z_n. The actual quotient also has its first three Laurent coefficients with uniform complex large-energy remainder bounds. See `FINITE_GAP_DIRICHLET_FREQUENCY_CONTOURS.md`.

Prior strict evidence for all 1060 unchanged selected baseline sources; strict dependency-order compilation of four new modules; then a fresh combined transitive axiom audit of all 1064 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1091 frozen source/checker/provenance hashes, all 25 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1064-module rebuild is claimed.

Fresh audit: 9678 selected and 32123 imported NLS declarations, permitted axioms only. Comparison with the article F^3/F^5 contours and actual Hamiltonian frequency identities (69)/(84) remains open. All eleven main theorem rows remain OPEN.


## Latest actual local resolvent and cubic frequency kernel

Both actual WKB columns now have proved all-order errors on the entire complex frequency plane, with exact reciprocal physical phase multipliers and controlled initial basis. Their actual monodromy entry is the scalar Hill Dirichlet characteristic with its verified factor i. Independently proved actual primitive bounds give actual root separation and all-order root comparison on upper energy arcs.

Combining those actual estimates with the genuine local Riccati jet proves D/R=i/(2z)+iQ(0)/(4z^3)+O(r^-4). For mean-zero sources the actual primitive then gives F^3*D/R=-z^2/2-Q(0)/4+O(r^-1). These are quantitative actual spectral estimates, with no supplied resolvent expansion or fixed leading scalar. See `LOCAL_DIAGONAL_RESOLVENT.md`.

Prior strict evidence for all 1064 unchanged selected baseline sources; strict dependency-order compilation of ten additions (two unchanged canonical symmetry/phase helpers and eight new proof modules); then a fresh combined transitive axiom audit of all 1074 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1102 frozen source/checker/provenance hashes, all 25 unchanged provenance records plus one new verified two-file canonical WKB reuse record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1074-module rebuild is claimed.

Fresh audit: 9731 selected and 32167 imported NLS declarations, permitted axioms only. Full-circle and exterior contour comparison to identify the actual Hamiltonian frequencies (69)/(84) remains open. All eleven main theorem rows remain OPEN.


## Latest actual cubic velocity contour limit

The actual primitive, root and scalar Dirichlet characteristic now have the proved conjugation identities needed for full-circle estimates. Upper-arc continuity and off-real reflection give genuine circle integrability without assuming continuity through spectral cuts or matching values at the two real crossings. The actual root is nonzero on every sufficiently large selected energy circle.

The actual cubic kernel estimate and actual normalized numerator quotient bound give an O(1/r) difference between the actual cubic spectral contour and the actual polynomial Dirichlet contour, where r is the frequency radius. Thus their difference tends to zero even without a finite-gap assumption. At a finite-gap source the exact Dirichlet contour identity identifies the cubic contour LIMIT, with factor 4/(i*pi), with the actual KdV Dirichlet velocity sum. The selected closed-gap index is retained. See `CUBIC_VELOCITY_CONTOUR_LIMIT.md`.

Prior strict evidence for all 1074 unchanged selected baseline sources; strict dependency-order compilation of five new proof modules; then a fresh combined transitive axiom audit of all 1079 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1107 frozen source/checker/provenance hashes, all 26 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1079-module rebuild is claimed.

Fresh audit: 9760 selected and 32197 imported NLS declarations, permitted axioms only. Exact exterior/finite-hole contour filling and gap-moment decomposition, actual Hamiltonian frequency identity (69), and the quintic route (84) remain open. All eleven main theorem rows remain OPEN.


## Latest exact actual cubic frequency contours

The actual cubic kernel now has genuine local analytic charts through the ground cut and every nonselected closed gap. A byte-identical canonical dense-limit helper joins those charts into ONE analytic filled kernel. The selected own gap remains a hole even if closed. Codiscrete circle congruence proves that filling the real cuts changes neither the genuine circle integral nor integrability.

Every actual finite-gap real period-one L2 source supplies an analytic exterior for this kernel, genuine cubic integrability at EVERY sufficiently large radius, and exact contour independence. For real smooth mean-zero physical sources, the independently proved contour limit therefore gives the actual KdV velocity coefficient as the exact cubic contour with factor 4/(i*pi). The literal physical scalar coordinate derivative has this contour coefficient at every gap, including a closed own gap, for any nearby-real matching germ. The radius precedes the choice of germ. See `ACTUAL_CUBIC_FREQUENCY_CONTOURS.md`.

Prior strict evidence for all 1079 unchanged selected baseline sources; strict dependency-order compilation of six additions (one unchanged canonical dense-extension helper and five new proof modules); then a fresh combined transitive axiom audit of all 1085 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1114 frozen source/checker/provenance hashes, all 26 unchanged provenance records plus one new verified canonical dense-extension record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1085-module rebuild is claimed.

Fresh audit: 9798 selected and 32228 imported NLS declarations, permitted axioms only. The source record now separates current dependencies from historical snapshots, so fulfilled contour obligations are no longer listed as current blockers. Actual finite-hole gap-moment deformation, Hamiltonian frequency identity (69), quintic route (84) and all other complete main conclusions remain open. All eleven main theorem rows remain OPEN.


## Latest actual finite-gap KdV moment identity

Every actual real period-one L2 source now has genuine filled shifted differentials on every intrinsic gap disc. The literal normalized moments have zeroth value 2*pi*delta_nk, every odd moment vanishes, and every positive moment vanishes at a collapsed gap, including the own index. Filled analytic circle extensions handle branch points; no false analyticity of literal total-division values is assumed.

Actual band geometry gives disjoint enlarged intrinsic discs and complete finite-hole coverage. Cauchy's theorem now deforms the actual cubic outer contour into the actual gap contours, retaining every first-N index, including a closed selected index. Exact cubic algebra gives the leading cube and -12 weighted second moments. At physical real smooth mean-zero finite-gap sources, the actual KdV velocity coefficient and coordinate derivative have this formula, with a genuine finite-support HasSum for the countable source sum. See `FINITE_GAP_KDV_MOMENT_IDENTITY.md`.

Prior strict evidence for all 1085 unchanged selected baseline sources; strict dependency-order compilation of six new proof modules; then a fresh combined transitive axiom audit of all 1091 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1120 frozen source/checker/provenance hashes, all 27 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1091-module rebuild is claimed.

Fresh audit: 9857 selected and 32287 imported NLS declarations, permitted axioms only. The actual Hamiltonian/action-frequency realization of (69), full complex rough-W moment scope and sharp bounds, quintic route (84) and complete main conclusions remain open. All eleven main theorem rows remain OPEN.


## Latest odd periods and actual Dirichlet normalization

The actual filled kernel F^(2*m+1)*psi_n/R now has exterior analyticity, genuine circle integrability, radius independence and finite-hole deformation for every nonnegative m at actual real period-one L2 finite-gap sources. The own index remains a hole even when closed. The exact linear outer period is -2*i*n*pi^2. The fifth outer source factor -16/(i*pi), minus (2*n*pi)^5, equals -160*pi^2*sum(k^3*Omega_nk^2)+80*sum(k*Omega_nk^4).

At actual real smooth period-one mean-zero physical sources, the proved quantitative comparison F*(D/R)=1/2+O(r^-2) and its genuine contour limit establish the actual zeroth Dirichlet residue moment S0=-2*n*pi, including a closed selected gap. No fixed leading product scalar or prescribed translation law is assumed. See `ODD_PERIOD_DIRICHLET_NORMALIZATION.md`.

Prior strict evidence for all 1091 unchanged selected baseline sources; strict dependency-order compilation of six new proof modules; then a fresh combined transitive axiom audit of all 1097 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1126 frozen source/checker/provenance hashes, all 27 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1097-module rebuild is claimed.

Fresh audit: 9920 selected and 32351 imported NLS declarations; permitted axioms only. The quintic local jet, physical mass-renormalized KdV2 contour comparison, full Hamiltonian/action-frequency identification and remaining main conclusions are open. All eleven main theorem rows remain OPEN.


## Latest actual finite-gap KdV2 moment identity

The actual sixth-order Riccati calculation gives D/R=i/(2z)+i*Q(0)/(4z^3)+i*(3Q(0)^2-Qsecond(0))/(16z^5)+O(r^-6). Combining it with the actual primitive yields the whole-circle quintic kernel polynomial with constant mass term -5H0/8 and an O(r^-1) remainder. Genuine contour comparison, the proved actual S0=-2*n*pi and exterior radius independence identify the source-factor fifth contour exactly with V2_n-20*(2*n*pi)*H0.

Consequently, at real smooth period-one mean-zero actual finite-gap physical sources, the actual KdV2 velocity sum satisfies V2_n-20*(2*n*pi)*H0-(2*n*pi)^5=-160*pi^2*sum(k^3*Omega_nk^2)+80*sum(k*Omega_nk^4). Both countable sums are genuine finite-support sums. The literal physical scalar coordinate derivative has this exact coefficient times i*z_n, including a closed selected gap. See `FINITE_GAP_KDV2_MOMENT_IDENTITY.md`.

Prior strict evidence for all 1097 unchanged selected baseline sources; strict dependency-order compilation of five new proof modules; then a fresh combined transitive axiom audit of all 1102 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1131 frozen source/checker/provenance hashes, all 27 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1102-module rebuild is claimed.

Fresh audit: 9981 selected and 32412 imported NLS declarations, permitted axioms only. Full Hamiltonian/action-frequency identification, rough-space compatibility and sharp bounds, native Banach Birkhoff realization and complete main conclusions remain open. All eleven main theorem rows remain OPEN.


## Latest actual scalar Fourier differentials at zero

The actual free critical/root products, action-gap ratio, positive amplitude and regular phase now fix the coordinate normalization. The deflated canonical root at the selected free energy is i*(-1)^n/(n*pi). Actual free state/trace calculations and Dirichlet first variations give the terminal derivative h(2*n); multiplication by the actual amplitude gives h(2*n)/sqrt(2*n*pi). Conjugating source and target gives the negative component on every complex tangent as well.

After explicit period-one transport, EVERY signed scalar coefficient of the existing actual physical Abelian map has a complex L2 analytic matching germ at zero with value zero and derivative h_k/sqrt(2*abs(k)*pi) on every mean-zero complex L2 tangent. The zero component is included. See `FREE_FOURIER_DIFFERENTIAL.md`. This proves the scalar L2 normalization toward Theorem1.1; native sequence-valued Frechet differentiability/analyticity and the full s>=-1 theorem remain separate obligations.

Prior strict evidence for all 1102 unchanged selected baseline sources; strict dependency-order compilation of six new proof modules; then a fresh combined transitive axiom audit of all 1108 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1137 frozen source/checker/provenance hashes, all 27 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1108-module rebuild is claimed.

Fresh audit: 10067 selected and 32498 imported NLS declarations, permitted axioms only. Full Hamiltonian/action-frequency identification, canonicality, native Banach map and global inverse, rough-space compatibility and sharp estimates remain open. All eleven main theorem rows remain OPEN.


## Latest native normalized differential numerator family

The actual Miura-normalized entire differential numerators now admit one jointly complex analytic realization in the full output-index Hilbert norm on a common complex Hminus-one source ball. All positive components equal the existing actual Miura family at every complex source, all nonpositive components vanish, and the entire free slice is retained. A single local neighborhood and constant control the full norm and every positive component together. The literal Hilbert-valued Bochner contour integral equals the exact Kronecker basis vector for every contour and source in that ball.

See `NATIVE_NORMALIZED_NUMERATORS.md`. This is a normalized differential dependency. The globally selected physical differential matching and moving-contour/regular-phase bounds, native physical Abelian-coordinate analyticity, full weighted Sobolev scale, canonicality, global inverse and Hamiltonian/action-frequency identification remain open.

Prior strict evidence for all 1108 unchanged selected baseline sources; strict dependency-order compilation of twelve byte-identical canonical Hilbert-transpose dependencies and four new proof modules; then a fresh combined transitive axiom audit of all 1124 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1154 frozen source/checker/provenance hashes, 27 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1124-module rebuild is claimed.

Fresh audit: 10386 selected and 32558 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest physical gap-product decay of actual normalized numerators

The actual Miura energy numerator/discriminant-derivative quotient now has a32/R_k bound over every sufficiently large complete energy circle, retaining the fixed complex energy translation and both square-root signs. The actual physical derivative/full-gap-product quotient is bounded by4. Consequently the actual common-ball native Hilbert numerator family satisfies the full physical gap-product exterior decay at every physical L2 source in that ball. The globally selected physical numerator has the same decay, and equality of these actual numerators is now equivalent to physical intrinsic Kronecker periods.

See `PHYSICAL_NUMERATOR_PRODUCT_DECAY.md`. Physical intrinsic period transfer is still required; no full physical differential identification or native physical Abelian-coordinate analyticity is inferred.

Prior strict evidence for all 1124 unchanged selected baseline sources; strict dependency-order compilation of four new proof modules; then a fresh combined transitive axiom audit of all 1128 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1158 frozen source/checker/provenance hashes, all 28 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1128-module rebuild is claimed.

Fresh audit: 10409 selected and 32577 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.


## Latest common native physical normalized differential family

There is now one jointly complex analytic native output-index Hilbert numerator family on all energies times a common complex period-one L2 source ball. At EVERY real physical source in that ball, EVERY positive index and EVERY energy, the literal component equals the existing globally selected physical normalized numerator. Exact free components, nonpositive zero extension and native Bochner Kronecker periods remain on the same complex ball. Actual rough frequency periods transfer to physical intrinsic gap periods with their exact sheet, orientation and2z Jacobian, including own/closed gaps and the first mode. The proved exterior uniqueness criterion gives physical identification with no remaining period assumption for this family near zero.

See `PHYSICAL_NORMALIZED_FAMILY.md`. This is the physical differential NUMERATOR family. Uniform moving-contour/regular-phase bounds and the native physical Abelian COORDINATE map, full Sobolev scale, canonicality/global inverse and Hamiltonian/action-frequency conclusions remain open.

Prior strict evidence for all 1128 unchanged selected baseline sources; strict dependency-order compilation of five new proof modules; then a fresh combined transitive axiom audit of all 1133 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1163 frozen source/checker/provenance hashes, all 28 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1133-module rebuild is claimed.

Fresh audit: 10429 selected and 32597 imported NLS declarations, permitted axioms only. All eleven main theorem rows remain OPEN.
