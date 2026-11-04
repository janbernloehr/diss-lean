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
