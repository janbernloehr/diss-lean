# KdV/KdV2 frequencies — branch progress

**Main-theorem status: not yet verified.**

The user authorized separate worktrees and publishing validated article
progress on 2026-11-02. The actual worktree is:

```text
/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-kdv-kdv2-frequencies/outputs/dnls
```

Branch: `articles/kdv-kdv2-frequencies`; base:
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. The app's managed-worktree API
rejects the canonical repository as an unregistered source workspace, so this
is an ordinary Git worktree, as subsequently authorized. The canonical main
checkout's files and branch remain unchanged. The path is also saved in the
private chat's `work/worktree.json` for future turns. Commands must explicitly
use this worktree directory.

## Latest continuous/rough agreement and odd moments

The actual continuous interval Fourier realization is now a bounded linear,
dense inclusion into Hminus1. Exact trace, continuation-domain, root and
primitive agreement is proved without endpoint matching. One common
continuous neighborhood identifies every selected critical energy, filled
numerator, period matrix, bounded operator, inverse, normalized entire
numerator and moment. Analytic uniqueness through the dense linear
pullback extends every odd cancellation to one full rough-open ball,
retaining all moment analyticity, free values and exact zeroth periods.
See `HMINUS_NORMALIZED_ODD_MOMENTS.md`. Full W and physical frequency
identification remain open; no main theorem is marked verified.

## Earlier rough normalization milestone

The actual infinite period operator and its analytic two-sided inverse
are now constructed on an Hminus1-open neighborhood of zero. Hilbert
realization of the critical basis and genuine Bochner contour duality
construct normalized entire numerators, their absolutely convergent
series, exact free values and every original contour normalization.
All literal normalized moments are analytic on one common rough-open
neighborhood before all positive indices and moment orders; their
zeroth periods are exactly normalized. This is a local rough result,
with full W continuation and physical frequency identification still
open. See `HMINUS_NORMALIZED_MOMENTS.md` for exact declarations, estimates,
source correspondence and remaining obligations. No main theorem is
marked verified.

## Checked mathematical progress

The initial validated patch has been applied and checked again in this
worktree. Its generic and signed-locus flow results are dependencies of
Appendix E.1(i)-(ii) and Theorem 4.14(i). Its mass-phase adapter is a
dependency of Theorem 1.12(v). These remain generic or explicitly conditional
adapters; they do not establish actual spectral KdV/KdV2 frequencies.

The new `NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities.lean` proves
identities concerning the actual equations:

| Source correspondence | Proved content |
| --- | --- |
| Hamiltonians and Gardner bracket, PDF p. 2, equations (1)-(3), pp. 1-2 | The finite Euler-Lagrange expressions of the doubled densities are twice the explicit gradient polynomials. Applying the spatial jet derivation to these gradients gives exactly `-u_xxx+6u u_x` and `u_xxxxx-10u u_xxx-20u_x u_xx+30u² u_x`. The source factor `1/2` is retained by doubling both sides of the Euler-Lagrange identity. |
| Same equations, evaluated on smooth fields | The previously proved generic jet-evaluation derivative theorem yields genuine `HasDerivAt` statements for the evaluated gradients, with the literal PDE right sides as derivatives. Smoothness is an explicit hypothesis, not an assumption of spectral identities. |
| Nonzero-mean reductions in Remarks 3.7(ii) and 4.6(ii), pp. 32 and 44 | For every scalar field and constant `c`, `V1(c+u)=V1(u)+6c u_x` and `V2(c+u)=V2(u)+10c V1(u)+30c² u_x`. These are the physical vector-field identities needed before transferring the mean-zero result to other leaves. They are not assertions that the spectral frequency formulas have already been proved. |
| Mean preservation and mass level sets in Theorem 1.12, pp. 7-8 | For every smooth period-one field, `∫ V1(u)=∫ V2(u)=0` and `∫ u V1(u)=∫ u V2(u)=0`. Explicit total-derivative fluxes establish the quadratic mass balances using the existing periodic integration theorem. This is the spatial balance needed for conservation along smooth solutions; differentiating a time-dependent solution integral remains a separate analytic obligation. |

The smooth differential identities are proved over complex scalar fields,
so they cover real fields viewed in the complexification. The later physical
solution construction must still retain the real subspace and its native
Sobolev norms. No low-regularity multiplication of distributions is asserted.

## Validation and build isolation

Run from this article worktree:

```bash
bash scripts/check-kdv-kdv2-frequencies.sh
```

The checker uses pinned Lean 4.33.1/mathlib v4.33.1 and rejects warnings.
It compiles the article modules and required shared sequence modules, and runs
`scripts/CheckKdVKdV2FrequencyCandidates.lean`, auditing their declarations
and all imported `NLS` declarations transitively. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. See `VALIDATION.md` for the
exact result and scope.

Mutable outputs live in this worktree's `.lake/build/lib/lean`. A separate
`.lake/article-imports` overlay points to read-only canonical compiled imports
and this worktree's own output files. The checker writes only to this
worktree's build directory. It does not run Lake against the overlay, copy the
21 GB cache or overwrite canonical build products. The explicit toolchain
paths are necessary because the existing `scripts/lake.sh` fallback is
relative to the original checkout. Expensive full validations still require
`/tmp/diss-lean-article-build.lock`.

## Next main-theorem requirements

The original inspection found no foundation commits beyond the shared plan.
A subsequent inspection found the Hill line through `0b58631` and the action
contour analytic-summation line through `be9eba0`. These do not yet supply
the physical Birkhoff map and actual spectral frequency identities needed
by the main theorems. No cross-chat message was sent.

1. Consume the shared physical Hill/Birkhoff construction from
   `kdv-estimates` and action Hamiltonians from `kdv-convexity` when published.
2. Construct the actual KdV and KdV2 frequency moment formulas and establish
   their locally uniform analytic estimates. The action-frequency parameter
   in the generic flow theorem must be instantiated with these constructed
   functions, with compatibility across all stated regularities.
3. Prove the actual smooth PDE/Birkhoff flow identification with the source's
   Hamiltonian time orientation, then approximation by every smooth initial
   sequence in the native Sobolev norm. The polynomial identities here
   resolve the local differential algebra, not the spectral identification.
4. For Theorem 1.12(ii), establish analytic bounded frequency corrections on
   fixed-mass leaves and the stated bounded-set uniform estimates. For
   (iii)-(iv), construct physical separating pairs in every nonempty open
   set, preserving fixed mass where required.
5. For (v), transfer the now-proved signed endpoint mass-divergence and
   finite-truncation obstruction to actual physical smooth approximants
   through the constructed Birkhoff map. Preserve the distinction
   between compact-time and fixed-time nonextension claims.

The detailed endpoint and quantifier inventory remains in `SOURCE_MAP.md`.
All actual article main theorems remain open; no unproved spectral or physical
assumption is counted as a verified main theorem.


## Endpoint-mass milestone

`SignedMassDivergence.lean` now proves the exact positive-index mass/endpoint
regularity equivalence, mass divergence for every coefficientwise
endpoint-regular approximation, and signed finite-truncation construction
and native norm convergence. Its compact-time nonextension theorem no longer
assumes mass divergence or the existence of approximants: both are proved.
The remaining frequency-correction and physical phase identity inputs stay
explicit. See [the detailed source correspondence](MASS_NONEXTENSION.md).

The finite-partial-sum argument was generalized to
`NLS/SequenceSpaces/NonnegativeEnergyDivergence.lean`, and the existing
Hilbert energy-divergence theorem now calls it with its statement unchanged.
The seven-module focused checker passes with warnings rejected; the
transitive audit covers 139 candidate declarations and 1343 declarations
including imported NLS dependencies. No article main theorem is yet marked
verified.


## Fixed-time nonextension milestone

The fixed-time sequence-space obstruction of Theorem 4.14(v) is now proved,
with the actual spectral correction and phase agreement still explicit
requirements. The proof constructs two finite endpoint-regular families
converging to the same datum, with a fixed positive mass difference and
relative phase tending to pi at the specified positive time. It does not
infer a fixed-time result from the earlier compact-time obstruction.
See [the detailed theorem map](FIXED_TIME_NONEXTENSION.md).

All ten selected modules pass with `-DwarningAsError=true`; the transitive
axiom audit covers 191 selected-module declarations and 1489 declarations
including imported NLS dependencies. The earlier `-E warning` option was
replaced because it did not enforce the intended warning policy. No
main theorem for the actual equation is yet marked verified.


## Frequency-moment contour milestone

`NLS/KdV/FrequencyMoments.lean` now defines the literal source moments and
proves Banach analyticity on fixed-contour neighborhoods, odd-moment
cancellation and the analytic-removal criterion for positive moments.
`FrequencyContourDecomposition.lean` proves the cubic and fifth-power
single-gap calculations and finite-gap exterior-period decompositions
with the exact source coefficients. It uses the existing finite-hole
Cauchy theorem rather than assuming a deformation identity. See
[FREQUENCY_MOMENTS.md](FREQUENCY_MOMENTS.md) for the theorem-by-theorem map.

These are reusable KdV contour proofs. Actual spectral factors, zeroth
period normalization and physical Hamiltonian-frequency identities remain
unconstructed, as do the sharp estimates and infinite-series convergence
required by the main theorems. All twelve selected modules pass strict
checks; the transitive audit covers 218 selected-module declarations and
1593 declarations including imported NLS dependencies. Main-theorem
completion remains unset.


## Infinite frequency-series milestone

The summation step of Theorems 3.4 and 4.3 is now proved with explicit
spectral remainder estimates as inputs. It retains the exact quadratic
denominator geometry, handles the diagonal separately, and concludes
absolute summability, analytic sums and locally uniform convergence of
ordinary positive partial sums. The general ℓ¹ analytic realization and
summation proof reuses existing Banach sequence and Dini theory.
See [FREQUENCY_SERIES.md](FREQUENCY_SERIES.md) for the declaration map,
constants, exponent qualifications and remaining spectral obligations.

All fifteen selected modules pass strict compilation. The transitive
axiom audit covers 244 selected declarations and 1658 declarations including
imported NLS dependencies. Actual main theorems remain open.

The shared branches were inspected through Hill commit `1806362` and
action/discriminant commit `2135a68`. The latter newly constructs an actual
continuous-potential discriminant and local primitive charts; it provides
a concrete dependency for the next construction step, while rough-potential
identification, global gap normalization and psi functions remain open.
These commits were not imported by this summation milestone.


## Actual Hill primitive-continuation milestone

The shared action/discriminant branch through `2135a68` is now merged with
its ancestry preserved. The five classical Hill modules actually used by
the frequency construction are compiled by this article's checker. A public
derivative identity was extracted from the shared squared-cosh proof and
reused to construct the analytic quotient at branch points.

`FrequencyPrimitiveContinuation.lean` constructs jointly analytic K,H from
the actual continuous-potential discriminant, with `K=H²(Delta²-4)`, H
nonvanishing and endpoint H=sigma/2. It proves the relative endpoint limit,
a locally uniform quotient bound, positive-moment estimates, and local
odd-moment cancellation with analyticity derived from the actual charts.
No assumption of a simple spectral zero or analytically chosen root is
introduced. See [PRIMITIVE_CONTINUATION.md](PRIMITIVE_CONTINUATION.md).

The imported shared checker was rerun after the public-lemma extraction:
all fifteen shared modules, the positive-index example and the transitive
audit of 199 shared declarations pass. The final 21-module frequency
checker and its complete transitive NLS audit are recorded in `VALIDATION.md`.
The source's global normalized primitive/root, psi functions, rough domains,
sharp moment estimates and physical frequency identification remain open.
Actual main-theorem completion remains unset.

Final strict validation passes for all 21 selected frequency modules. The
transitive audit passes for 334 selected-module declarations and 1918
declarations including imported NLS dependencies, with only the three
standard axioms allowed. The canonical checkout remains clean on main.


## Free normalized spectral-differential milestone

The shared free-normalized continuation through `ecd0109` is now merged
with ancestry preserved. `FreeFrequencyPsi.lean` constructs an entire
numerator from the actual free discriminant derivative. It proves the
exact omitted-mode value and critical-point nondegeneracy, constructs
isolating circles rather than assuming them, normalizes all periods
simultaneously to `2*pi*delta_nk`, and proves every positive weighted free
moment vanishes, including the diagonal pole case. Actual free moments
are defined with proved choices of isolating contours.
See [FREE_FREQUENCY_PSI.md](FREE_FREQUENCY_PSI.md).

The source product representation, infinite normalized family at nonzero
potentials, rough-space compatibility, sharp bounds and physical frequency
identification remain open. The free normalization does not substitute
for any actual main theorem. Final checker counts are in `VALIDATION.md`.

Final validation passes: 23 selected frequency modules, 404 selected-module
declarations and 2002 declarations including imported NLS dependencies.
The updated shared integration checker also passes its 20 modules, example
and 269-declaration transitive audit. The canonical checkout remains clean.
No main theorem is marked verified by the free-basis milestone.


## Actual critical-branch and finite-normalization milestone

Actual zeros of the continuous-potential discriminant derivative are now
constructed analytically near each positive free mode, retaining nonzero
second derivative. A reusable joint moving divided-difference construction
fills the omitted point and produces entire actual numerator bases that
agree with the normalized free basis on the whole free slice.

The actual period entries, using the constructed continued root and proved
free contours, are analytic near zero and equal the identity there. The
new finite normalization theorem solves all coefficients simultaneously
for any finite set of distinct positive modes, producing actual entire
numerators with the exact `1/(2*pi)` normalization on one common complex
neighborhood. See [FINITE_NORMALIZATION.md](FINITE_NORMALIZATION.md).

This is progress beyond the free case. No infinite-mode uniformity, period
normalization on unselected contours, global product identity or rough-space
extension is inferred. The full main-theorem inventory remains open.
The final 33-module strict build and transitive audit are recorded in
`VALIDATION.md` and `source.json`.

The final strict run passes all 33 selected modules. The transitive audit
passes for 497 selected declarations and 2148 declarations including
imported NLS dependencies, allowing only the three standard axioms.
Canonical sources and build products were not modified. All main-theorem
statuses remain open.


## Actual uniform critical basis and analytic infinite tail milestone

The shared actual high spectral embedding/coverage through `963d5bb` is now
merged with ancestry preserved. A generic complex-source distant-critical
analyticity theorem removes the real-type restriction for distant roots.
The actual Hill energy critical family is analytic, simple and uniquely
labeled in each high mapped disc, on one neighborhood at every complex
continuous potential.

Combining that uniform tail with a finite head yields an actual infinite
critical and entire numerator basis on one common neighborhood of zero.
The positive high critical displacement is also an actual Banach analytic
ℓ² map; its whole norm can be made uniformly small near zero. See
[UNIFORM_CRITICAL_BASIS.md](UNIFORM_CRITICAL_BASIS.md).

This removes the previous mode-by-mode neighborhood limitation for the
basis, but does not solve infinite period normalization. The full main
inventory remains open. The 40-module strict build, complete transitive
audit and shared integration recheck are recorded in `VALIDATION.md`.

The final 40-module strict frequency run passes. Its complete transitive
audit passes for 570 selected declarations and 12091 declarations including
imported NLS dependencies. The common-neighborhood infinite numerator
family and actual ℓ² tail norm assertions are verified; infinite period
normalization and all main-theorem completion statuses remain open.

The shared integration recheck passes all 26 modules, the positive-index
example and its 337-declaration transitive shared-namespace audit. This
milestone preserves the upstream spectral commit ancestry and keeps the
canonical checkout unchanged.

## Actual infinite period entries and uniform tail milestone

The actual common-neighborhood numerator basis now has a compatible
infinite contour period matrix. Every scalar entry is analytic on one
complex neighborhood chosen before either index, and the complete free
matrix is the identity. The high contours have the exact mapped energy
path interpretation, orientation and Jacobian.

A new actual energy separation estimate and a reusable contour integration
by parts theorem give the exact primitive formula on one uniform
off-diagonal tail. The scalar norm estimate has coefficient 20/pi and
quadratic energy denominator squared. It explicitly retains the necessary
shifted-primitive bound; no small operator norm or infinite inverse is
assumed. See [UNIFORM_PERIOD_ENTRIES.md](UNIFORM_PERIOD_ENTRIES.md).

The full main inventory remains open. All 49 selected modules and their
complete transitive audit are checked by the focused frequency command;
the final output and counts are recorded in `VALIDATION.md` and `source.json`.

## Actual uniform primitive-error and period-tail milestone

The actual IVP horizontal-strip bound and Banach Cauchy estimate now give
uniform potential derivatives of the Hill discriminant. A compact free
circle lower bound and source variation control every continued root
simultaneously on all positive contours, including low modes. The actual
primitive error is O(norm q) and its shifted value is uniformly bounded.

Consequently the actual period tail has a reciprocal-square off-diagonal
bound on one neighborhood, with no primitive estimate supplied as an
assumption. All selected critical frequencies can also be localized
inside half the contour radius, and diagonal energy separation is proved.
See [UNIFORM_PRIMITIVE_BOUNDS.md](UNIFORM_PRIMITIVE_BOUNDS.md).

The full period operator and inverse remain to be constructed; no main
theorem is marked verified. The 57-module strict check and full transitive
audit are recorded in `VALIDATION.md` and `source.json`.

## Actual bounded period operator and analytic inverse milestone

The same selected critical and numerator family now supports all positive
frequency circles, including the low modes. The full matrix has proved
diagonal and reciprocal-square off-diagonal bounds. A reusable shifted
diagonal series constructs its bounded action, and a bounded ℓ-infinity
symbol assembly proves actual operator-norm analyticity.

The exact free identity and the Neumann criterion construct an analytic
two-sided inverse on a smaller common neighborhood, with inverse norm at
most two. The actual matrix entries and all selected numerator/critical
data are retained there. See [ANALYTIC_PERIOD_INVERSE.md](ANALYTIC_PERIOD_INVERSE.md).

Convergence and contour normalization of the resulting entire differentials
are the next obligation. Canonical products, rough/global compatibility
and the full main-theorem inventory remain open. The strict 70-module
check and complete transitive audit are recorded in `VALIDATION.md` and
`source.json`.

## Actual infinite normalized entire-family milestone

The actual numerator basis is now a jointly analytic ℓ²-valued entire
map, with membership proved by quadratic critical growth and locally
uniform reciprocal numerator tails. Pairing it with the actual inverse
columns constructs absolutely convergent positive-index normalized sums.

The literal Bochner contour functional is identified with the actual
period-operator row on every coefficient vector. The inverse identity
therefore proves every positive normalization period, both in frequency
coordinates and on the mapped energy paths, with exact source constants.
The entire free slice and positive support of inverse columns are proved.
See [INFINITE_NORMALIZED_DIFFERENTIALS.md](INFINITE_NORMALIZED_DIFFERENTIALS.md).

This constructs the local continuous-potential infinite family. Canonical
products, global/rough compatibility and all main-theorem rows remain
open. The strict 78-module build and complete transitive audit are recorded
in `VALIDATION.md` and `source.json`.

## Exact selected critical products

The complete signed critical labeling now agrees with the selected actual
Hill family, including central multiplicities. Pairing the signed factors
proves the source derivative product (15), locally uniformly on the full
energy plane. The omitted nth factor gives the actual filled critical
basis B_n, including its own removable critical energy. Reusable entire
convergence descent and linear-factor cancellation are proved separately.
See [CRITICAL_PRODUCTS.md](CRITICAL_PRODUCTS.md).

The normalized Psi_n have different zeros at nonzero potentials; their
canonical products (52), the full rough/global version and all main
theorems remain open. The 90-module strict build and complete transitive
axiom audit are recorded in `VALIDATION.md` and `source.json`.

## Actual weighted normalized coefficients

The sharper actual period estimate constructs a bounded analytic period
operator after multiplication of each positive matrix entry by row/column
index. Its analytic inverse is constructed on one common neighborhood.
A bounded reciprocal diagonal intertwines it with the unweighted operator
and proves exact compatibility of the actual inverse columns.

The resulting literal one-weight coefficient error is in l2, Banach
analytic, zero at the free potential and uniformly small near zero with
its exact column-index scaling. The same inverse defines the normalized
entire functions and retains all their actual periods. See
[WEIGHTED_NORMALIZED_COEFFICIENTS.md](WEIGHTED_NORMALIZED_COEFFICIENTS.md).

A second weight and actual normalized zero/product identification remain
open, as do global/rough compatibility and all main theorems. The strict
96-module build and transitive axiom audit are recorded in `VALIDATION.md`
and `source.json`.

## Two-weight coefficients and actual critical resolvents

The twice-weighted actual period matrix is now bounded and analytic.
Its proof retains both the reciprocal-square near-diagonal kernel and
the necessary far outer-product Hilbert bound. Constructed inverses and
a bounded reciprocal-square diagonal give exact compatibility with the
unweighted inverse used by the normalized entire functions.

The literal two-weight inverse-column error is a genuine analytic l2
vector, uniformly small near zero with exact n² scaling. Its positive
residue coefficients m*(R e_n)_m form an actual analytic l1 sequence.
The normalized functions have an absolutely convergent critical resolvent
expansion off the selected critical energies. See
[TWO_WEIGHTED_NORMALIZED_COEFFICIENTS.md](TWO_WEIGHTED_NORMALIZED_COEFFICIENTS.md).

Actual normalized zero equations, complete zero/product identification,
rough/global compatibility and every main theorem remain open. The
103-module strict build and complete transitive audit are recorded in
`VALIDATION.md` and `source.json`.

## Constructed actual simultaneous normalized zeros

For each omitted n, a genuine jointly analytic l2 sequence equation now
constructs all other positive normalized zeros on one potential
neighborhood. The actual free partial derivative is proved to be the
bounded identity; the verified analytic Banach implicit function theorem
supplies the infinite displacement branch. The selected energy zeros are
analytic, distinct and exact at the free potential.

A separate identity connects every solved coordinate to the literal
normalized entire numerator defined by the same inverse R. Filled own
critical energies are treated directly using the entire numerator factors
and the actual convergent series. All original normalization periods
remain unchanged. See [NORMALIZED_ZEROS.md](NORMALIZED_ZEROS.md).

The neighborhood still depends on the omitted n. Completeness, simplicity,
canonical products/prefactors, full omitted-index uniformity, rough/global
compatibility and every main theorem remain open. The strict 116-module
build and transitive axiom audit are recorded in `VALIDATION.md` and
`source.json`.

## Simple actual normalized zeros and selected signed products

The normalized zero equation now has an exact filled factor identity
with the literal Psi_n. The critical basis factor is proved nonzero on
the full candidate domain, including its filled own critical energy.
The partial Hilbert derivative is operator-norm analytic, equals Id at
the free source and has a constructed inverse along the root graph on
one source subneighborhood. Its exact diagonal structure proves every
retained scalar derivative nonzero.

Thus every selected actual normalized energy zero is simple, simultaneously
for all k!=n on one neighborhood for the chosen omitted n. The analytic
l2 branch, distinctness, free values and original periods are retained.
The reflected selected root sequence also has genuine l2 free-lattice
displacement; its full signed product converges locally uniformly and has
exactly those simple roots. See
[SIMPLE_NORMALIZED_ZEROS.md](SIMPLE_NORMALIZED_ZEROS.md).

The signed product still includes zero and the omitted-mode placeholders.
Completeness and canonical products of Psi_n, exact prefactors, omitted-
index uniformity, rough/global compatibility and every main theorem remain
open. The strict 123-module check and full transitive audit are recorded
in `VALIDATION.md` and `source.json`.

## Selected energy products and actual entire normalized quotients

The signed candidate product now descends to the entire energy plane.
Literal positive energy products converge locally uniformly everywhere;
deleting the omitted mode gives the literal prefactor 2/(n*pi), including
the filled omitted energy. The candidate product has exactly the selected
retained roots and all are simple. At zero displacement it agrees with
the actual critical basis.

The actual normalized Psi_n divided by this product has an entire filled
quotient, nonzero at every selected root. Its multiplication identity
holds at every energy, and its free-potential value is exactly one,
including at the free zeros. Constructed local families retain every
original normalization period and the actual analytic zero branch. See
[NORMALIZED_ENERGY_PRODUCTS.md](NORMALIZED_ENERGY_PRODUCTS.md).

Constancy and the exact value of the entire quotient at nonzero potentials
remain open, so this does not yet prove completeness or source (52) for
Psi_n. Omitted-index uniformity, rough/global compatibility and every main
theorem also remain open.

Strict validation: all 132 selected modules pass; the complete transitive
axiom audit covers 1495 selected declarations and 13635 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.

## Constant actual normalized quotient and complete simple zero set

The entire normalized quotient is now proved constant in energy, equal
to the analytic scalar L_n=(1/n)*sum_m m*(R e_n)_m. A bounded positive
multiplier of the actual two-weight inverse vector constructs an odd
Hilbert direction; its paired frequency resolvent is the exact energy
remainder. Existing arbitrary-complex exterior estimates and the common
free sine normalization give the quotient limit. Entire circle decay
then proves constancy on the whole energy plane.

Simplicity at one retained actual root proves L_n nonzero. Hence the
selected retained roots are the complete Psi_n zero set, all simple,
and the literal products multiplied by L_n converge locally uniformly
to the actual normalized entire function. Constructed local families
retain every original normalization period, analytic root branches,
free energies and exact free scalar one. See
[NORMALIZED_PRODUCT_CONSTANT.md](NORMALIZED_PRODUCT_CONSTANT.md).

The exact nonzero-potential scalar value L_n=1 remains open, so source
(52) with its precise Psi_n prefactor is not yet verified. Common omitted-
index uniformity, real gap/sharp root estimates, rough/global compatibility,
physical frequency/flow identification and every main theorem remain open.

Strict validation: all 141 selected modules pass; the complete transitive
axiom audit covers 1582 selected declarations and 13743 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.

## Actual all-mode normalized odd moments near zero

The literal normalized moment family now has exact mapped energy-contour
identities, the original zeroth normalization and analyticity on one
common complex source neighborhood. Every odd moment vanishes on that
same neighborhood, before all positive numerator and contour indices.
There is no finite-head or omitted-mode exception, and diagonal and
collapsed gaps are included.

Shared whole-gap squares and annulus coverage are imported from the
convexity branch, with provenance and preserved local derivative lemmas.
Nonzero analytic filled primitive/root quotients extend through complete
high gaps. Fixed low contours use constructed compact source tubes at
the free gap; a finite intersection joins them to the uniform tail.
The proof applies first to every entire numerator and then to the actual
normalized Psi_n defined by R. See
[NORMALIZED_ODD_MOMENTS.md](NORMALIZED_ODD_MOMENTS.md).

This is a local continuous-potential version of Lemma 3.1(i)–(iii), not
its full rough/global source statement. The collapsed even-moment clause,
sharp moment/root bounds, exact canonical leading scalar, physical
frequency/flow identities and every main theorem remain open.

Strict validation: all 164 selected modules pass; the complete transitive
axiom audit covers 1778 selected declarations and 13953 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.

## Positive moments at actual collapsed high gaps

Every positive normalized moment now vanishes on a collapsed actual high
gap, including the diagonal numerator. The hypothesis is the literal
analytic squared-gap function being zero. Shared actual endpoint
deflation constructs a nonzero analytic quotient even at a double zero;
a disc square root and one fixed circle sign extend the actual shifted
primitive. The existing filled primitive/root quotient then gives an
analytic positive-order integrand and Cauchy cancellation.

The constructed local normalized family keeps all-mode analyticity,
zeroth periods and every odd cancellation on the same neighborhood,
with one cutoff only for the new collapsed positive-moment clause. See
[NORMALIZED_COLLAPSED_MOMENTS.md](NORMALIZED_COLLAPSED_MOMENTS.md) and
`SHARED_COLLAPSED_GAP_IMPORT.json` for selected shared source provenance.

The low even collapsed contours, full rough/global scope, sharp moment/
root estimates, exact canonical scalar, physical frequency/flow identities
and every article main theorem remain open.

Strict validation: all 171 selected modules pass; the complete transitive
axiom audit covers 1811 selected declarations and 13976 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.


## Exact all-order normalized moment resolvents

Constructed the jointly analytic actual Hilbert critical resolvent and
its negative energy derivative, with literal j/(lambda-mu_j)^2 positive
coordinates. Complete selected critical labeling and all-mode separation
prove the original contours avoid every critical pole, including the
finite head. Closed-circle power integration by parts gives the exact
2*pi/(m+1) coefficient for all actual normalized moments. A genuine
Hilbert-valued Bochner integral and Holder summability prove the literal
absolutely convergent positive-index series outside the contour integral.
The constructed family retains moment analyticity, exact zeroth periods,
all-mode odd cancellation and the actual analytic inverse of norm at most
two on one near-zero continuous-potential neighborhood.

Read `NORMALIZED_MOMENT_RESOLVENT.md`. The order-two formula prepares the
sharp cubic-primitive/gap estimates; those sharp estimates are not yet
proved. Physical frequency identities, full rough/global W scope and all
article main theorems remain open. No canonical scalar L_n=1 is assumed.

Strict validation: all 174 selected modules pass. The complete transitive
axiom audit covers 1858 selected declarations and 14023 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.


## Actual critical energies at quadratic gap scale

Extended the actual analytic Hilbert critical tail to uniform arbitrarily
small high-frequency confinement near any continuous complex source.
Selected proved normalized endpoint-quotient comparisons give an actual
quadratic gap localization on one common tail neighborhood. A fixed energy
radius precedes every tolerance epsilon; the critical displacement is at
most 2*epsilon*|gamma_k^2|/(pi*r*k). The simpler public consequence allows
any prescribed coefficient eta in front of |gamma_k^2|/k.
Actual endpoint geometry also yields |gamma_k|<=2*pi^2*k. Combined
with the quadratic estimate, this proves the continuous-potential form
of (37), |lambda-dot_k-tau_k|<=eta*|gamma_k|, for every eta>0 on one
common complex tail neighborhood, including collapsed gaps.

The actual critical energy lies within one quarter of the actual gap
length from its midpoint and is at least half a gap length from the
gap-length circle. At a collapsed actual high gap it equals the midpoint.
The proof constructs stationarity of the squared primitive from its actual
trace identity and squaredCosh noncriticality, then uses a whole-disc
Cauchy bound on the normalized endpoint-deflated unit. Complex and double
endpoints are included; no nonzero Delta-prime or RealType assumption is
imposed at a branch point.

Read `CRITICAL_GAP_LOCALIZATION.md` and the exact selected import record
`SHARED_CRITICAL_GAP_IMPORT.json`. This prepares the diagonal pole control
for normalized cubic-resolvent contour estimates. The weighted lp part of
source Lemma 2.11(i), sharp normalized moment/root estimates, full rough/
global W compatibility, physical frequency/action identification and all
main theorems remain open.

Strict validation: all 183 selected modules pass; the complete transitive
axiom audit covers 1935 selected declarations and 14088 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.


## Actual normalized second moments at high-gap scale

The constructed normalized family now has quadratic diagonal and quartic
off-diagonal second-moment bounds at every sufficiently high actual gap.
Writing x_k=norm(actual squared gap)/k², one constant B gives
norm(Omega_kk^2)<=B*x_k and norm(Omega_nk^2)<=B*x_k² for n!=k.
One neighborhood, cutoff and constant precede all numerator/contour
indices. Exact zeroth periods, all-mode analyticity and odd cancellation,
and every positive high collapsed-gap cancellation remain on that family.

Actual weighted primitive powers are deformed to gap circles without
crossing critical poles; the previously proved quarter-gap localization
handles the diagonal. All-order critical-kernel bounds and quadratic
basis-period row bounds are proved first. The exact Hilbert resolvent
formula and zeroth normalization then preserve the extra gap factor
for distinct numerator/contour indices. The diagonal zeroth-period lower
bound is constructed from actual operator continuity at the free identity.

Read `NORMALIZED_SECOND_GAP_BOUNDS.md` and the selected shared-source
record `SHARED_CRITICAL_PERIOD_GAP_IMPORT.json`. Full sharp n,k dependence,
diagonal asymptotics, rough/global W compatibility, the canonical scalar
and physical frequency/action/Birkhoff identification remain open. Every
main theorem remains unverified.

Strict validation: all 195 selected modules pass; the complete transitive
axiom audit covers 2095 selected declarations and 14239 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.


## An analytic actual normalized frequency series near zero

For every fixed positive output index n, the literal series
sum_k k*Omega_nk^2 now converges absolutely and locally uniformly on
one constructed complex continuous-potential neighborhood of zero.
Its sum times -12 is analytic. The same family retains the actual
analytic inverse R, free identity, norm at most two, all-mode moment
analyticity, original zeroth periods and every odd cancellation.

The compatible twice-weighted inverse moves a reciprocal square index
weight onto the actual Hilbert period vector. The resulting bound is
norm(Omega_nk^2)<=1376*pi²*C³*n²*x_k/k² for high k, where
x_k=norm(actual energy squared gap)/k². An actual locally bounded l1
frequency squared-gap sequence g gives x_k<=16*pi²*norm(g_k).
Analytic scalar head coordinates then fill the finite head. No unscaled
energy-gap l2 bound, continuous individual root ordering, RealType
assumption or canonical leading scalar identity is presumed.

Read `NORMALIZED_FREQUENCY_SERIES.md`. This proves a local summation
step toward Theorem 3.4, with the source coefficient -12. Physical
frequency identity (69), continuation to full rough/global W, action
dependence, sharp two-index/diagonal asymptotics, KdV2 series and all
main theorem inventory rows remain open.

Strict validation: all 201 selected modules pass; the complete transitive
axiom audit covers 2167 selected declarations and 14311 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.


## Actual rough critical basis and all-mode period entries

Constructed actual analytic high critical energies on one Hminus1-open
neighborhood of every complex rough source using the proved shifted
Miura trace identity and general complex canonical ZS critical labels.
Exact first/second derivative formulas retain the fixed chart energy
shift. High critical energies are simple and uniquely labeled on shifted
discs; at zero they have the exact unshifted free energy values.

A generic analytic simple-critical-branch theorem constructs the finite
head. One finite intersection joins it to the high tail before every
positive index. Filled division supplies an entire actual critical
numerator basis, its exact factor identity/nonzero center, and its exact
free normalized slice on one complex Hminus1-open neighborhood. Actual
rough annulus coverage and compact source tubes cover every original
frequency contour, including the finite head. All scalar period entries
are analytic on that same neighborhood; their whole free matrix is the
identity with the exact original 1/(2*pi) normalization and Jacobian 2*z.

Read `HMINUS_PERIOD_DATA.md` and `SHARED_HMINUS_NORMALIZATION_IMPORT.json`.
The selected dependency closure imports the proved physical Miura/L2
comparisons, analytic rough charts, actual jointly entire Hminus1 trace,
source sheets and contour coverage from convexity `08db7a5`. Six local
interfaces/extensions remain intact; the new Euler-Lagrange module adds
one explicit import to retain the proved periodic integration lemmas.
Two inherited heartbeat overrides are removed; both unchanged proofs
pass at the default budget. The 201 prior selected sources remain byte-identical.

The rough basis has not yet been normalized by an operator inverse.
Rough operator bounds/inversion, continuous/rough normalized agreement,
rough moments/summation, full source-domain continuation and physical
frequency/action/Birkhoff identification remain open. No main theorem
inventory row is verified.

Strict validation: all 318 selected modules pass; the complete transitive
axiom audit covers 3895 selected declarations and 25200 declarations
including imported NLS dependencies. See `VALIDATION.md` and `source.json`.

Current strict validation: all 334 selected modules pass, with 4052
selected declarations and 25355 imported NLS declarations in the
transitive axiom audit. See `HMINUS_NORMALIZED_MOMENTS.md`, `VALIDATION.md`
and `source.json`. All main theorems remain open.

Current strict validation: all 341 selected modules pass, with 4102
selected declarations and 25405 imported NLS declarations in the
transitive axiom audit. See `HMINUS_NORMALIZED_ODD_MOMENTS.md`, `VALIDATION.md`
and `source.json`. Every main theorem remains open.
