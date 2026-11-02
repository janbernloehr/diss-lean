# Progress on 2026-11-02

The first checkpoint below left all main theorems open. The third checkpoint
implements Theorem 1.2; Theorems 1.1 and 1.3 remain open. Validation status is
recorded in the current README and theorem-1.2.json.

## Physical Birkhoff adapter — Theorem 1.2 dependencies

`PhysicalBirkhoff.lean` defines the input as pairs of original period-one
Fourier–Lebesgue distributions. `physicalCoefficients_apply` proves exactly
which physical test mode is evaluated. Transport through the existing
spectral construction and the established rectangular-to-complex linear
change gives a holomorphic map on an open physical domain, and
`physicalBirkhoff_action` proves its coordinate product equals the actual
spectral action of the transported potential.

On the physical NLS real form, `physicalRealCoefficients` is a homeomorphism
to the established real source. The real rectangular Birkhoff map is an
open embedding with dense image, and is onto at p=2 (indeed at all 1<p≤2).
Its complex output is a same-index conjugate pair. Both complex analyticity
and real geometry have existence theorems constructing their source data.

Still required for the full article theorem: one compatible family across
exponents on complex domains, a Banach real-analytic physical-input
interface, canonical bracket transport, exact accepted Hilbert-map
identification, and all normalization identifications. The physical mKdV
real diagonal is smaller than this NLS real form. Its reflection symmetry
and hierarchy restriction remain assigned to the hierarchy task.

## H₄ candidate convergence — Theorem 1.3 dependencies

`FourthMomentSummability.lean` constructs the moment atlas and a connected
open neighborhood of the whole real source on which every weighted row
∑ k |k Ω⁽²⁾ₙₖ| converges, for 1<p≤3. In particular, it includes the p=2
base case needed by the article. The proof uses the existing refined
moment factorization, cubic gap summability (with norm bound ||γ³||₁≤||γ||ₚ³),
and the estimate |k/(n-k)|≤|n|+1 for k≠n. It handles the diagonal separately
without dividing by n, and works at collapsed gaps.

`exists_fourthFrequencyCandidate` constructs the candidate -12∑k kΩ⁽²⁾ₙₖ
and proves a HasSum statement without assuming moment convergence or a
moment atlas from the caller. `fourthFrequencyCandidate_eq_of_coefficients`
proves cross-exponent agreement from the established physical coefficient
compatibility of the moments.

Still required: local uniform convergence, analyticity of the weighted
sum, the ℓ^(-1,r)/ℓ^(-1,p/2) sequence-map bounds, and the refined remainder
ω*ₙ+12πnIₙ. The currently reused off-diagonal coefficient estimate lies in
ℓ^(p/2)+ℓ^(1+); the article's Lemma 5.3 has the sharper ℓ^(1+) row needed
for its all-finite-p weighted sum argument. The present p≤3 proof does not
supply that sharper estimate. Physical identification with the H₄ action
Hamiltonian derivative is also outstanding; the symbol “candidate” is
intentional.

## Validation and checkout

The four proof modules passed direct Lean 4.33.1 checks without diagnostics.
All 30 new declarations passed a transitive axiom audit permitting only
propext, Classical.choice and Quot.sound. There are no new axioms, sorry
proofs or disabled linters. The reproducible focused check script is
`check.sh`; `validation.txt` records the output.

The ordinary Git worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-mkdv-below-l2/work/checkouts/mkdv-below-l2`,
on branch `articles/mkdv-below-l2`. The app's managed creation tool rejected
the unregistered canonical source folder, so the approved ordinary Git
worktree fallback was used. Commands explicitly target this path. The
canonical main checkout and its build products were not edited. All compiler
outputs remain separate; no full build or aggregate NLS import was added.


## Third checkpoint — Theorem 1.2 and consumed physical fourth-flow bridge

Theorem 1.2 now has direct article statements in `Theorem12.lean`:
`theorem1_2_at_exponent`, `theorem1_2_compatible`, `theorem1_2_hilbert` and
`theorem1_2_hilbert_globalInverse`. The fixed family is constructed from
original spectral charts, then pulled back to original period-one
distributions. Domain shrinking to real-centered ball cores makes the
cross-exponent compatibility true on full complex intersections. The real
source and conjugate-pair target have explicit complete real Banach structures.
The statement includes actual analytic local inverse maps and a global
bi-real-analytic Hilbert inverse for the same family.

The canonical clause is proved on the entire complex domain by analytic
continuation of the verified real canonical identities. Full coordinate
differentials have regular Hilbert Fourier witnesses. The complex mixed
bracket is exactly -i delta; `physicalFLBracket_eq_integral_bracket` proves
that the physical Fourier bracket is the existing integral bracket in the
Hilbert case. `compatibleBirkhoff_eq_intrinsic` identifies the p=2 family
member with the accepted intrinsic action-angle map.
`physicalHilbertRealization_coefficients` verifies each input distribution's
actual unit-period Fourier coefficients in that comparison.

Reusable scalar restriction, complex coordinate inclusion, conjugate-pair
coordinates, canonical cotangent algebra and real-core uniqueness proofs
live in FunctionalAnalysis, Dynamics, Poisson and ZakharovShabat modules.
They are imported by the article rather than redefined inside a main theorem.

The shared hierarchy commits `9b664f9` and `09fa657` were merged intact,
preserving their ownership and proof provenance. The new
`ClassicalRenormalizedFourthFlow.lean` consumes their physical Hamiltonian
first-variation/field construction. Subtracting the common 6M translation
generator yields exactly the smooth renormalized mKdV velocity, while
retaining the physical Gardner energy-gradient identity. This does not
identify the low-regularity sequence flow with physical solutions.

Theorems 1.1 and 1.3 remain open. The H₄ candidate still has only the earlier
1<p≤3 absolute-convergence proof; its physical frequency identification,
all-finite-p estimates and analytic sequence bounds remain outstanding.
Theorem 1.1 additionally needs the diagonal Birkhoff invariance,
smooth-approximation identification, and fixed-time nonextension proof.

Strict validation for the third checkpoint passed: all 22 modules compiled with
warnings treated as errors, and all 120 audited declarations used only the
three permitted standard axioms. Theorem 1.2 is marked verified under the
accepted manuscript reference in `theorem-1.2.json`; Theorems 1.1 and 1.3 are
explicitly unverified. `validation.json` stores every audited declaration.


## Fourth checkpoint — actual root comparison and physical H₄ candidate

The exact cancellation identity (38), pp. 17–18, is now checked for the
actual spectral roots and actual deleted products. The theorem
`exists_sourcePsi_critical_comparison` constructs its open domain, zero
periods, isolating contours and separation. One comparison constant works
for all n,k at each source, and the product bound holds on each full closed
comparison disc, including collapsed gaps.

Reusable complex product estimates use absolute relative perturbations:
if a_m=b_m(1+u_m), then the actual products satisfy
`‖A−B‖ ≤ ‖B‖ exp(∑‖u_m‖) ∑‖u_m‖`. For the actual spectral quotients,
`u_m=(a_m−b_m)/(λdot_m−z)` away from the omitted index. The denominator
separation is proved from isolating discs, and Hölder supplies the finite
uniform reciprocal-row bound. The proof uses convergent products directly.

The original root period of an analytic numerator close to one on the gap
is within ε of -i after division by 2π. Thus its norm is at least 1−ε and is
nonzero when ε<1. The cancellation identity and the two analytic gap-error
bounds then imply `‖σ−ρ‖ ≤ (e+q)/(1−ε)`. The smallness condition is explicit;
its required locally uniform tail verification for the actual numerator has
not yet been proved. Proposition 4.1's all-p sequence bootstrap also remains
open. These intermediate lemmas do not claim that proposition.

The new physical adapter constructs a fixed actual moment atlas and an open
physical domain containing the entire real-type space for 1<p≤3. It shares
the established physical Birkhoff domain and the same original Fourier
coefficients. It proves individual-moment holomorphy, the actual absolutely
convergent -12 weighted sum, spectral-action coordinate products, and
cross-exponent agreement for equal real physical distributions. The infinite
sum is still a candidate: its analytic sequence estimates and identification
with the physical H₄ Hamiltonian derivative are outstanding.

Theorems 1.1 and 1.3 remain unverified; Theorem 1.2 remains verified. The next
mathematical steps are uniform smallness of the actual normalizing numerator,
the root-difference exponent bootstrap, the sharper Lemma 5.3 moment rows,
and physical H₄ frequency identification using the consumed hierarchy bridge.

Strict validation for the fourth checkpoint passed: all 30 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. All 155 named
declarations passed transitive axiom checks, using only `propext`,
`Classical.choice` and `Quot.sound`. The recorded declaration set was matched
exactly against `AxiomAudit.lean`; no warnings or sorry axioms occurred.


## Fifth checkpoint — uniform comparison-period invertibility

The previous checkpoint's explicit normalizer smallness criterion is now
verified for the actual roots and products. `SourcePsiCriticalFilledTail`
proves that filling the original deleted root with the actual critical root
preserves a graph radius uniform in the deleted index. At each real source
the resulting full root vectors lie in the compact product of periodic gaps.
The existing uniform-small quotient-tail theorem near that compact set then
applies to the entire actual family on one complex source neighborhood.
A separate local bound controls the full filled-root-minus-critical norm,
which supplies the uniform exponential constant in product comparison.

`SourceCriticalTailSeparation` handles all omitted indices at once. Small
critical displacement tails give the distant omitted case; one larger
selected-index cutoff handles the finite omitted head. The denominator is
at least `(π/2)|n−k|` throughout each selected free eighth-π disc.

`SourcePsiCriticalNormalizer` combines these bounds with uniformly small
periodic gaps and the existing critical-point-to-gap distance bound. Its
actual numerator ξ satisfies `‖ξ−1‖ ≤ 1/2` on every sufficiently distant
gap, uniformly in n on one complex neighborhood. `SourcePsiCriticalPeriodLowerBound`
places ξ analytically on original closed isolating discs and obtains a
normalized period norm at least 1/2. Its global existence theorem constructs
an open neighborhood of the entire real locus and establishes the estimate
locally uniformly at every complex source. It retains the exact equation
(38), actual numerator analyticity, denominator avoidance and relative
product control on the same chosen circles.

`SourceCriticalRelativeRowBound` bounds the product difference by its actual
absolute reciprocal row, with a displacement norm bound used only inside
the exponential. The reusable Fourier module `AbsoluteReciprocalYoungRows`
provides summability, an exact majorant row identity and a norm bound at any
admissible Young triple with kernel exponent strictly above one.
`SourcePsiCriticalRootBound` derives the actual inequality
`‖σ−ρ‖ ≤ 2(gD+g²M/d)` from the constructed invertible period and explicit
pointwise gap/product/denominator bounds. These lemmas supply the quantitative
inputs for the exponent iteration; they do not yet prove Proposition 4.1.

Theorem 1.3 remains open: the next steps are to assemble the root exponent
bootstrap, prove the sharper Lemma 5.3 moment estimates, and identify the
resulting all-p analytic frequency map with the physical H₄ action derivative.
The physical candidate convergence range remains 1<p≤3. Theorem 1.1 remains
open, and Theorem 1.2 remains verified.

Strict validation for the fifth checkpoint passed: all 37 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. All 175 named
declarations passed transitive axiom checks, using only `propext`,
`Classical.choice` and `Quot.sound`. The audited declaration set matched
`AxiomAudit.lean` exactly. There were no holes, new axioms or disabled linters
in the seven new modules.


## Sixth checkpoint — Proposition 4.1 at every finite p>2

`sourceProposition4_1` now proves the actual psi-critical root refinement
`σⁿₖ−λdotₖ = γₖ αⁿₖ` in every finite ℓq, q>1, on a constructed open
neighborhood of the entire real source locus. The norm bound is uniform in
the deleted index n and locally uniform at every complex source. The source
neighborhood precedes the q quantifier. One fixed scalar sequence is retained:
`sourcePsiCriticalGapNormalized`, the actual critical-filled displacement
difference divided by the actual gap. Its value is zero at collapsed gaps,
and its deleted coordinate is zero. The theorem retains explicit equality
of every ℓq representative with that same scalar sequence.

The initial squared-gap factorization is built from the original normalized
psi offsets and the actual critical squared-gap quotient, with uniform norm
bounds. A Hölder product gives the initial half-exponent estimate. The new
actual reciprocal inequality uses the checked comparison periods, quantitative
separation, actual quotient bounds, and critical-point-to-gap distance bounds.
Its constants and selected-index cutoff are independent of n on a common
complex source neighborhood. The quadratic remainder uses the exact π/2
separation and the corresponding coefficient 8B²/π in its common constant.

The reusable sequence-space bootstrap has three parts. A strict reciprocal
gain is realized by a quasi-Hölder product, an optional contractive embedding
into ℓ¹, and a Young kernel with exponent strictly above one. A quantitative
one-step theorem retains the original coefficients, the finite central part,
and the translated ℓ¹ error uniformly in n. A finite clipped arithmetic
progression of reciprocal exponents reaches every prescribed finite q>1.
The parameter neighborhood is unchanged during the iteration, and the norm
constants remain uniform over the entire parameter and row family.

This completes Proposition 4.1, rather than a restricted exponent variant.
Theorem 1.3 still requires the sharper Lemma 5.3 moment rows, the all-p weighted
sum and analytic sequence estimates, and identification with the physical H₄
action derivative using the consumed hierarchy bridge. The current physical
candidate convergence remains at 1<p≤3. Theorem 1.1 remains open; Theorem 1.2
remains verified.

Strict validation for the sixth checkpoint passed: all 43 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. All 189 named
declarations passed transitive axiom checks, including `sourceProposition4_1`,
using only `propext`, `Classical.choice` and `Quot.sound`. The audited set
matched `AxiomAudit.lean` exactly. No holes, new axioms, disabled linters or
increased heartbeat limits were introduced in the six new modules.


## Seventh checkpoint: sharp moment rows and all-p physical convergence

The off-diagonal part of Lemma 5.3 is now checked for every finite p>2.
`SourceAbelianMomentOnePlusDomain.exists_sourceAbelianMoment_onePlusAtlas`
constructs the original psi roots, their squared-gap extension and the actual
moment atlas together. On one connected open neighborhood of the entire real
locus, the canonical cubic coefficient belongs to every finite ℓq, q>1.
The local source neighborhood precedes q and the constants are uniform in n.
Collapsed gaps and the finite central part retain the same actual coefficient.

The proof uses actual critical-weighted cancellation of the squared Abelian
primitive. The contour proof differentiates F³/3; the cosine proof differentiates
the corresponding cubic primitive and includes both endpoints without division
by a zero sine or gap. The three numerator terms use Proposition 4.1, summable
actual root differences and their reciprocal Young rows, the actual relative
product estimate, and critical-root denominator separation.

`FourthMomentSharpSummability.exists_fourthMoment_summableAtlas` proves
absolute convergence of the weighted H₄ candidate at every finite p>1.
For p>3 it pairs the cubic gap sequence in ℓ^(p/3) with the sharp actual row
in its conjugate exponent. The existing 1<p≤3 proof supplies the other case.
`PhysicalFourthFrequencyCandidate` now fixes this all-p chart and transports
it to the same physical distributions and Birkhoff domain as Theorem 1.2.
Its actual sum converges absolutely, its individual moments are analytic,
and its values agree across all finite physical exponents above one.

Theorem 1.2 remains verified. Theorems 1.1 and 1.3 remain open. The full
candidate's analyticity, its weighted target estimates and refined remainder,
and its identification with the physical H₄ action derivative are not inferred
from pointwise absolute convergence. The p=2 endpoint and diagonal clause are assembled below on the sharp
common domain.


`sourceLemma5_3` now assembles the full Lemma 5.3 at every finite p≥2.
The Hilbert endpoint is supplied by the refined original moment estimate,
whose half-exponent lower bound is one. The diagonal has a fixed
ℓ^(p/2)+ℓ^(1+) decomposition from the shared verified moment library.
Both diagonal and sharp rows hold on one connected open domain and on
one local source neighborhood chosen before q. The actual row coefficient
is retained, and `SourceLemma5_3Data.row_power_sum` proves the literal
positive uniform q-power bound printed in the article. The exact clause
mapping is recorded in `lemma-5.3.json`.


Strict validation for the seventh checkpoint passed: 54 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`; 216 named
declarations passed transitive audits using only `propext`, `Classical.choice`
and `Quot.sound`. The audited declarations exactly match `AxiomAudit.lean`.
The final assembly was checked after the initial 53-module build, followed
by the expanded full audit. No holes, new axioms, disabled linters or higher
heartbeat limits were added. This is focused validation using the canonical
compiled dependencies read-only, not a fresh whole-repository rebuild.


## Eighth checkpoint: analytic scalar and weighted physical candidates

The full weighted moment row is now an actual analytic ℓ¹-valued map for
every finite p>1. `WeightedReciprocalRows` proves the cubic dual-product bound
and the bounded index-ratio realization, including the selected coordinate.
`SourceAbelianMomentWeightedRows` combines these with the established actual
diagonal formula and scalar moment analyticity. It obtains locally uniform
bounds of the form (1+|n|)C on one neighborhood before n.
`FourthMomentAnalytic` then composes the ℓ¹ row with continuous summation.
It does not assume uniform coordinate tails of bounded ℓp row families.

`FourthMomentSequence` proves the exact normalized comparison
‖candidate_n − (6π)n·unweightedCandidate_n‖ ≤ 12‖gap‖³‖a_n‖.
The actual row is the canonical cubic coefficient, and both sums are proved
absolutely convergent. The shared unweighted frequency bounds and this
uniformly bounded difference yield actual weighted ℓr realizations.
`WeightedIndexRealization` uses the literal weight (1+|n|)^(-1) and retains
the raw coordinate at n=0. No division by n or zero-mode vanishing is used.

The resulting candidate sequence is complex analytic into ℓ^(-1,r) for each
finite r>1 with r≥p/2, on one connected real-containing complex domain
selected before r. `exists_fourthMoment_sequenceAtlas` constructs the roots,
actual atlas, domain, scalar candidate and all target maps together.
The physical adapter now uses this chart, shares its domain with the fixed
Theorem 1.2 Birkhoff family, and is real analytic on the entire physical real
Banach source. Its weighted sequences agree for equal real distributions at
every common target exponent. In particular it supplies the candidate target
r=p/2 for p>2 and every finite r>1 for p=2.

Theorem 1.2 remains verified. Main Theorems 1.1 and 1.3 remain open. The
remaining Theorem 1.3 obligations are physical normalized H₄ derivative
identification and the refined actual-action remainder. Candidate analyticity
is now established, but it is not used to claim the unproved identification.
The printed n-times-remainder asymptotic must be stated at nonzero indices
(or with an explicit finite-coordinate convention); it must not silently
force the general complex zero frequency to vanish.


Strict validation for the eighth checkpoint passed: all 59 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. The transitive
audit of 238 named declarations exactly matched `AxiomAudit.lean` and used
only `propext`, `Classical.choice` and `Quot.sound`. No holes, new axioms,
disabled linters or increased heartbeat limits were introduced. Validation
uses the canonical compiled dependencies read-only and is not a fresh
whole-repository rebuild.


## Ninth checkpoint: refined physical remainder and the H₄ contour value

The refined candidate action remainder is now verified on the same physical
chart as all weighted analytic targets. `exists_fourthActionRemainder` uses
the checked unweighted correction ν_n+2I_n and the bounded difference from
6πnν_n. The shared index-quotient realization gives simultaneous bounds in
every finite ℓr with r>1 and r≥p/3. A fixed mixed decomposition then provides
one ℓ^(p/3) component and one genuine ℓ^(1+) component, including p/3<1.
The local source neighborhood and both component maps precede q.

`exists_fourthMoment_refinedAtlas` constructs all domains, roots, moments,
analytic maps and remainder bounds together. The chosen physical chart now
uses this construction. `physicalFourthFrequencyCandidate_asymptotic`
proves the exact nonzero-index formula with the actual actions represented
by products of the same Theorem 1.2 Birkhoff coordinates. The all-index
reconstruction in `physicalFourthFrequencyCandidate_remainder` explicitly
retains the actual zero-coordinate singleton. No zero-frequency vanishing
is imposed on a general complex source.

The physical H₄ identification has also advanced. The quartic inversion
phase has Laurent part
z⁴ − 2H₁z² − H₂z − (H₃−3H₁²)/2 − (H₄−6H₁H₂)/(4z).
The first four Taylor coefficients come from the independently defined
physical finite-gap hierarchy. The remainder factors as z^(-2) times an
analytic inverse-frequency germ, with a uniform exterior bound.
The exact quartic contour is −(πi/2)(H₄−6H₁H₂); hence the physical
Hamiltonian combination is (2i/π) times that contour. This is verified
for every actual ambient spectral chart at any real finite-gap source.
It does not yet identify the H₄ action derivative with the candidate.

Theorem 1.2 remains verified. Theorems 1.1 and 1.3 remain open. For Theorem
1.3 the remaining gap is the independently defined physical H₄ derivative
identity, including the closed-action endpoint. The quartic contour value,
all candidate analytic targets and the refined actual-action remainder are
now available for that identification.


Strict validation for the ninth checkpoint passed: all 64 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. The transitive
audit of 254 named declarations exactly matched `AxiomAudit.lean` and used
only `propext`, `Classical.choice` and `Quot.sound`. No holes, new axioms,
disabled linters or increased heartbeat limits were introduced. Validation
uses the canonical compiled dependencies read-only and is not a fresh
whole-repository rebuild.


## Tenth checkpoint: physical H₄ action derivatives and Lemma 5.2

Lemma 5.2 is now verified for independently defined physical H₄ finite-gap
frequencies, including every closed selected action. The open frequency is
minus the derivative of physical H₄ along the actual Birkhoff action-reduction
curve. Differentiating the fixed quartic contour uses the already calibrated
physical H₁ and H₂ derivatives and gives exactly 6H₂+12πnH₁. The actual cubic
psi contour expands into the weighted second moments and the cubic free
frequency, with coefficient −12 and dispersion (2πn)³.

The closed frequency is the second physical amplitude derivative, with the
exact opening action t²/2. The new curve lemmas prove analyticity of physical
H₂ and H₄ on any analytic real source curve with fixed finite gap support.
The weighted moment sum passes to the opening limit on that same finite
support. The amplitude derivative limit then gives the closed moment formula,
without defining the frequency through that formula or assuming H₄ continuity
in the rough source norm. The resulting frequency is independent of the
chosen compatible Birkhoff realization.

The unique coefficient-preserving Hilbert model transports the physical
frequency to every finite p>1 and preserves the original smooth physical
pair and every hierarchy Hamiltonian. The chosen article adapter now identifies
its candidate with this actual normalized physical H₄ frequency at every real
finite-gap physical input, with the same fixed Hilbert Birkhoff member used
in Theorem 1.2. The clause map is recorded in `lemma-5.2.json`.

Theorem 1.2 remains verified. Theorems 1.1 and 1.3 remain open. The remaining
Theorem 1.3 obligations are identification throughout the original full
H^(3/2) classical frequency domain, and a real-coefficient realization in the
Hilbert weighted targets. The complex candidate analytic maps, refined
actual-action remainder and finite-gap physical derivative identity are all
verified; they are not used to claim the still-unproved full-domain bridge.


Strict validation for the tenth checkpoint passed: all 75 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. The transitive
audit of 286 named declarations exactly matched `AxiomAudit.lean` and used
only `propext`, `Classical.choice` and `Quot.sound`. No holes, new axioms,
disabled linters or increased heartbeat limits were introduced. Validation
uses the canonical compiled dependencies read-only and is not a fresh
whole-repository rebuild.


## Eleventh checkpoint: actual real weighted H₄ targets

The candidate now takes values in the real-coefficient weighted target, not
merely in a complex target with a real-analytic parametrization. The shared
positive even-moment reality theorem proves coefficient reality before the
weighted summation. It applies at every real source, including collapsed
gaps and the zero frequency, without a finite-gap approximation argument.

`physicalRealFourthFrequencySequence` maps the original real distributions
into the closed real subspace of the actual weighted sequence space. Its
inclusion equals the already verified complex sequence exactly, and each
raw coordinate equals the same literal −12 weighted moment sum. The map is
real analytic for every finite p>1 and every finite r>1 with p/2≤r. In
particular the Hilbert source has every finite real target r>1, as specified
in Theorem 1.3. Exponent compatibility and the independent finite-gap
physical action-derivative identity are preserved in these real targets.

Theorem 1.2 remains verified. Theorems 1.1 and 1.3 remain open. The remaining
Theorem 1.3 obligation is the identification with the independently defined
physical H₄ frequency on the full original H^(3/2) domain, in its own
topology. Neither the real target construction nor finite-gap agreement
alone is used to claim that bridge.

Strict validation for the eleventh checkpoint passed: all 77 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. The transitive
audit of 295 named declarations exactly matched `AxiomAudit.lean` and used
only `propext`, `Classical.choice` and `Quot.sound`. No holes, new axioms,
disabled linters or increased heartbeat limits were introduced. Validation
uses the canonical compiled dependencies read-only and is not a fresh
whole-repository rebuild.


## Twelfth checkpoint: physical H₄ on the full H^(3/2) domain

The independent physical Hamiltonian is now constructed at the original
fractional regularity. The leading term pairs the H^(3/2) field with the
H^(-3/2) third derivative, retaining the exact unit-period multiplier 2πin.
The nonlinear term pairs the actual H¹ cubic product a²b with the L² first
derivative b'. The result is the entire analytic polynomial i(mean(a D³b)
−3mean(a²bb')). Its smooth periodic values equal the original Riccati H₄,
with no spectral or action hypotheses.

The native source uses the half-scale spectral weight that gives exactly
(1+|n|)^(3/2) on the original physical lattice. Its bounded real linear
transport preserves every raw coefficient. The full native Hamiltonian is
real analytic and agrees with the independently defined physical finite-gap
Hamiltonian. The all-order finite-gap higher-action trace proves physical
reality. Explicit finite-gap approximants converge in the full weighted norm,
so their real scalar values have the native physical Hamiltonian as their
limit. This also realizes the Hamiltonian in its genuine real scalar codomain.
The sequence proof avoids the kernel normalization cost of a direct closed-set
argument; heartbeat limits and linters remain unchanged.

The actual global weighted Birkhoff inverse transports this H₄ to the entire
native rectangular H^(3/2) target, with real analytic dependence. On a native
one-mode opening line the complete Hamiltonian function equals the original
physical finite-gap Riccati H₄ at every amplitude. At a collapsed selected
finite-gap action its second native derivative therefore equals the already
independently defined physical closed frequency.

Theorem 1.2 remains verified. Theorems 1.1 and 1.3 remain open. For Theorem
1.3 the physical fractional Hamiltonian is now available on its original
full domain. The remaining bridge is action dependence and identification
of its action derivatives throughout that domain with the chosen normalized
frequency candidate. Full-domain Hamiltonian analyticity, even combined with
finite-gap derivative agreement, is not counted as that frequency identity.

Strict validation for the twelfth checkpoint passed: all 82 focused modules
compiled with `autoImplicit=false` and `warningAsError=true`. After repairing
the last modules, the affected suffix was rechecked and the full transitive
audit was run. The 345 named declarations exactly matched `AxiomAudit.lean`
and used only `propext`, `Classical.choice` and `Quot.sound`. No holes, new
axioms, disabled linters or increased heartbeat limits were introduced.
Canonical compiled dependencies were imported read-only; this is not a fresh
whole-repository rebuild.


## Thirteenth checkpoint: full H₄ action dependence and independent frequencies

Physical finite-gap Hamiltonians of every order now have verified action
dependence. Equal actual actions determine the isospectral primitive. The
all-order physical exterior trace then identifies the independently defined
Riccati Hamiltonians on one common admissible circle, avoiding all periodic
segments, including collapsed gaps. This works at every finite p>1.

The full fractional H₄ is now constant on action level sets in both the
native rectangular Birkhoff target and the original H^(3/2) real source.
The proof uses simultaneous native weighted real truncations. They retain
each selected raw coefficient and action, converge in the original weighted
norm, and have actual finite-gap inverse sources. The independent physical
Hamiltonians agree at those approximants and pass to the full-source limit.
The genuine real scalar H₄ has the same action dependence.

Native weighted action reduction is now a bounded raw-mode projection and
an exact radial rescaling. Forgetting the weight gives the existing original
curve without rescaling its time parameter. The selected physical action
decreases at unit speed before collapse, and every other action is unchanged.
The global weighted inverse lifts that curve in every nonnegative real
Sobolev order. Its derivative is certified in the stronger source norm.

The new `sobolevFourthFrequency` is defined on the full original real
H^(3/2) source independently of Abelian moments. Open selected actions use
the negative physical H₄ action-reduction derivative. Closed selected actions
use the second physical amplitude derivative, with the original action
exactly t²/2. The reduction derivative is the actual H₄ Birkhoff differential
on the native radial vector. At every finite-gap source the entire reduction
function is the original physical Riccati H₄ function, so both frequency
branches retain their previously calibrated finite-gap values.

Theorem 1.2 remains verified; Theorems 1.1 and 1.3 remain open. For Theorem
1.3, equality of the independent full-domain frequencies with the chosen
normalized moment candidate remains to be proved, including closed actions.
The original local analytic action-factor derivative interpretation also
remains to be verified. Full action dependence alone is not counted as an
analytic action factorization or a full frequency identification.

Incremental strict validation passed for all 6 new modules with
`autoImplicit=false` and `warningAsError=true`. The 82 parent modules were
reused after checking their sources are unchanged from `4a0d0a4`. The full
transitive audit was rerun: all 392 named declarations exactly matched
`AxiomAudit.lean` and used only `propext`, `Classical.choice` and `Quot.sound`.
No holes, new axioms, disabled linters or increased heartbeat limits were
introduced. The focused checker now lists all 88 modules; this checkpoint
is incremental validation, not a fresh whole-repository rebuild.

## Fourteenth checkpoint: full physical action derivatives and Theorem 1.3

The physical H₄ now has genuine local complex analytic factors in its original
ell^(3,1) action space. Actual holomorphic inverse germs agree with the global
native Sobolev inverse on complete real neighborhoods. A reusable real-germ
scalar descent handles closed tail actions and arbitrary infinite zero sets.
Exact complex and real coordinate normalization transports the factors to the
original weighted action norm. The action map's raw coordinates are exactly
the original source actions and remain in the nonnegative weighted cone.

The independent full-domain physical frequencies now equal the factor
partials in raw unit action directions. Open modes use the original unit-speed
reduction curve; closed modes use the second derivative of the amplitude line,
whose action is precisely t²/2. Both curve identities are proved in the full
weighted Banach norm. The frequency is therefore real analytic on every
original H^(3/2) source, including across collapsed gaps.

The lower renormalization terms are independent physical H¹ mass and momentum,
transported coefficient-for-coefficient from the fractional source. Their
finite-gap values agree with the original Riccati hierarchy. Actual spectral
finite-gap approximation in the native weighted topology, full frequency
continuity, and analytic moment sums extend Lemma 5.2 to every original source
and every signed index. No moment candidate enters the physical frequency's
definition or its derivative interpretation.

The physical adapter uses the fixed accepted Hilbert Birkhoff family from
Theorem 1.2 and preserves both original period-one distributions. The chosen
moment candidate and every finite real weighted realization now equal the
independent physical action derivatives throughout the original domain.
Compatibility transports these same values to every source exponent.

Theorem 1.3 is now assembled and verified. Its Hilbert clause covers every
real ell^(-1,r) target, 1<r≤infinity. Its extension clause has the literal
complex ell^(-1,p/2) target at every finite p>2 and agrees on equal physical
distributions. Its locally uniform refined asymptotic uses the fixed
ell^(p/3) and OnePlus components with actual products of the chosen Birkhoff
coordinates. The quasi-norm p/3<1 is retained; the asymptotic is stated at
n≠0 and the exact all-index formula retains the zero-coordinate singleton.

Theorems 1.2 and 1.3 are verified under the accepted intrinsic Birkhoff
reference. Theorem 1.1 remains open: the smaller mKdV diagonal, physical
renormalized rotations and trajectory continuity, smooth-approximation
agreement, and fixed-time nonextension outside L² still require proof.

All 16 final new modules pass strict Lean 4.33.1 checks. The 88 parent modules
reuse the validation at `896298fd1ab33359c906eeea93d922c78fe909a0` after verifying
that their sources are unchanged. The full transitive audit was rerun: all
460 declarations exactly match `AxiomAudit.lean` and use only `propext`,
`Classical.choice` and `Quot.sound`. There are no holes, new axioms, disabled
linters or increased heartbeat limits. The focused checker now lists 104
modules. The canonical checkout and compiled dependencies remain read-only.

## Fifteenth checkpoint: actual fourth-frequency rotations and a nonzero signed mode

A reusable source action-frequency family now lifts real Hamiltonian rotations
through the actual open Birkhoff image at every finite p>1. Coordinatewise
frequency continuity suffices for full norm continuity of the phase path.
The first Hamiltonian component has the negative phase sign. Every original
spectral action is preserved, frequencies remain constant, time parameters
add, and every admissible step has an admissible negative-time inverse.
All source inverse statements retain the actual image-domain condition.

The article's constructed cubic-plus-normalized fourth-frequency family
supplies all generic data: both continuity and original action invariance are
proved. On the original H^(3/2) domain its frequency equals the independently
defined physical H4 derivative minus the exact 6H2 and 12*pi*n*H1 shifts.
No identification with the H3 frequency is used.

The fixed Theorem 1.2 map now provides actual physical distribution-pair
trajectories. Their coordinates are exactly the prescribed rotations of the
same Birkhoff family. A common positive time interval and open neighborhood
exist at every source. A single invariant open neighborhood of zero works
before every real time interval. The complete compact-time source trajectory
maps are continuous in the uniform norm. Convergent sequences or filtered
families give uniformly convergent actual source paths; openness supplies
eventual admissibility on the common interval.

The nonzero-index requirement in the fixed-time nonextension argument is now
proved on the actual physical inputs. Finite support of just the first complex
Birkhoff component forces actual spectral finite-gap regularity. Its unique
Hilbert model has the same original Fourier coefficients. Fourier uniqueness
then gives exactly the same two original period-one distributions. Hence an
input outside the physical Hilbert domain has a nonzero first Birkhoff mode
at n!=0. The mass-dependent phase therefore cannot be confined to its
degenerate zero index. Controlled divergent-mass approximations and the full
fixed-time separation argument are still required.

Theorem 1.1 remains open. These results concern actual fourth-frequency
rotation lifts on real-type pairs, not yet solutions on the smaller real
mKdV diagonal. The diagonal Birkhoff correspondence and odd frequency symmetry,
smooth PDE agreement, scalar diagonal restriction and the exact solution
notion, and the tunable-mass fixed-time obstruction remain to be proved.
The existing spatial-reflection-fixed source slice is distinct from the
mKdV diagonal; its symmetry results have not been substituted for that gap.
Theorems 1.2 and 1.3 remain verified.

All 8 final new modules pass strict Lean 4.33.1 checks. The 104 parent modules
reuse validation at `020ba7305cbfaabc0ac2be0c8398c16ec1995cd6` after verifying
that their sources are unchanged. The fresh full transitive audit checks all
522 declarations, exactly matching `AxiomAudit.lean`; only `propext`,
`Classical.choice` and `Quot.sound` occur. No holes, new axioms, disabled
linters or increased heartbeat limits were introduced. The focused checker
now lists 112 modules. The canonical checkout remains untouched.

## Sixteenth checkpoint: the actual mKdV swap, indexed roots and even actions

The unsigned physical component exchange is now treated directly. The
classical first-order equation is intertwined by the signed solution-vector
exchange (y2,-y1), with spectral parameter reflected by z -> -z. ODE uniqueness
proves the complete solution and monodromy covariance. Dirichlet and Neumann
boundary conditions exchange, with the exact minus sign in their sine-normalized
characteristics. The discriminant is unchanged under the combined transformation;
the anti-discriminant changes sign. Finite Fourier agreement and continuity
extend these actual physical identities to every finite source exponent p>1.

Original algebraic spectral multiplicities are preserved, by the analytic
vanishing order of the original discriminant square minus four. Central root
counts, distant quarter-pi discs and strips, lp displacements, and complete
lexicographic endpoint ordering give the exact signed endpoint reflection:
the swapped left endpoint at n is the negative original right endpoint at -n,
and conversely. Every repeated endpoint and closed gap is included. This is
stronger than equality of the unordered spectral sets.

The exact standard-root branch now transforms under this same reflection.
Actual midpoints change sign, oriented gaps do not, and the principal-root
radicand is unchanged. Nonzero-index factors exchange in pairs; the central
factor supplies the minus sign of the full canonical root. These identities
hold at every complex source and spectral parameter, with no division by a gap.
On the actual mKdV diagonal the canonical root is odd and the indexed gaps
are even.

The positive real gap profile reflects by theta -> pi-theta. Every original
real higher action has the corresponding spectral-power parity. At level zero
the proved positive-gap representation equals the original contour-defined
action, so ordinary actions reflect exactly by n -> -n, including closed gaps.
The actual products of the fixed Theorem 1.2 physical Birkhoff coordinates are
therefore even on every physical mKdV datum. This does not infer equality of
the Birkhoff phases from even actions alone.

The actual physical mKdV diagonal is now a named closed complete Banach
subspace: the two original period-one distribution fields are equal. Fourier
uniqueness identifies it precisely with the unsigned-swap fixed source slice.
Symmetric Fourier cutoffs preserve this same diagonal, retain finite actual
Fourier support, and converge in the original physical norm at every finite
exponent. No spectral finite-gap claim is made for these Fourier cutoffs.

The independently defined physical H2 momentum is antisymmetric under
component exchange on the whole H1 pair space. It vanishes on the true H1
diagonal. The bounded original H^(3/2) inclusion preserves equal fields, hence
H2 vanishes on the full original fractional physical diagonal. Its fourth-flow
rotation frequency is exactly the independent physical H4 action derivative
minus the physical 12*pi*n*H1 translation shift.

Theorem 1.1 remains open. The Birkhoff phase-angle part of equation (50), the
necessary odd normalized-frequency identity and actual source-flow diagonal
preservation have not yet been proved. A complete proof of preservation via
Hamiltonian swap covariance would also need to establish the same source-flow
statement. Smooth PDE agreement, the exact scalar smooth-approximation solution
notion, and the controlled divergent-mass fixed-time obstruction remain open.
Theorems 1.2 and 1.3 remain verified.

All 10 final new modules pass strict Lean 4.33.1 checks. The 112 parent modules
reuse the validation at `7558905e3dd119f6cd09294d54a21ebf522fd09d` after verifying
that their sources are unchanged. The fresh full transitive audit checks all
600 declarations, exactly matching `AxiomAudit.lean`; only `propext`,
`Classical.choice` and `Quot.sound` occur. No holes, new axioms, disabled
linters or increased heartbeat or recursion limits were introduced. The
focused checker now lists 122 modules. The canonical checkout remains untouched.


## Seventeenth checkpoint: full physical diagonal frequency parity

The physical hierarchy has its exact unsigned-swap parity at every positive
order on actual finite-gap sources, by the all-order trace and higher-action
reflection. The original weighted component swap is bounded in every native
weighted real source norm and preserves raw coefficients. Native weighted
finite-gap density extends physical H4 antisymmetry to the full H^(3/2) domain;
H4 therefore vanishes on its actual equal-field diagonal.

Full native H4 action dependence compares the actual reflected action-reduction
Hamiltonians near zero and the closed-gap opening Hamiltonians at every
amplitude. Their original unit-speed and I=t²/2 normalizations give the exact
odd reflected physical derivative, including every closed action. With the
already verified H2 vanishing, the normalized original physical frequency is
odd on the full fractional diagonal.

Every finite Fourier source has coefficient-preserving representatives at
all weighted Banach exponents. In the physical adapter, diagonal-preserving
Fourier cutoffs therefore have native H^(3/2) representatives of exactly the
same two distribution functionals. The fixed Birkhoff-family physical
frequency adapter and exponent compatibility identify their frequencies.
Continuity passes the odd normalized identity to every actual mKdV datum at
every finite p>1. The zero-index value vanishes. Both actual real and complex
weighted sequence realizations and the exact cubic-plus-normalized rotation
frequency retain this odd indexing. No angle identity is assumed.

This discharges the frequency-parity obligation of Corollary 6.1. Actual
source-flow diagonal preservation, smooth physical PDE agreement, the scalar
smooth-approximation solution and uniqueness requirements, and the tunable
divergent-mass fixed-time obstruction remain open. Theorem 1.1 remains
incomplete; Theorems 1.2 and 1.3 remain verified.

All eight final new modules pass strict Lean 4.33.1 checks. The 122 parent
modules reuse the validation at 40d1959bf83cadfd29557cf1a3035bec7db6028c after
checking that their sources are unchanged. The fresh full transitive audit
checks 634 declarations, with only propext, Classical.choice and Quot.sound.
No holes, new axioms, disabled linters or increased heartbeat or recursion
limits were introduced. The checker now lists 130 modules. Canonical compiled
dependencies remain read-only; this is incremental focused validation.


## Eighteenth checkpoint: actual physical mKdV diagonal flow preservation

The full complex action germ at every real source is now proved to reflect
under unsigned component exchange. Differentiation gives the entire complex
cotangent transformation, including every closed gap. The original bounded
source Poisson operator has the anti-Poisson sign under this swap, so each
actual action Hamiltonian field transforms to minus the reflected-index field.
For reflected frequencies the two minus signs cancel in a finite action sum.
The original complex coordinate support reflects using actual actions and
closed-gap vanishing, without an angle formula.

The independently defined native physical mass is invariant under exchange,
and momentum is antisymmetric, so normalized H4 frequencies have full
OFF-diagonal reflected covariance. Native original-coefficient Fourier
representatives, the physical derivative adapter and source-norm approximation
extend the identity to every finite p>1 real source. Frequencies also agree
coefficient-for-coefficient across exponents.

For an arbitrary action-invariant frequency family, the actual global Hilbert
image lift now has its original finite-action Hamiltonian ODE in the full
source norm. Scalar integrating-factor uniqueness works in both time directions
and identifies all actual Birkhoff coordinates from this ODE and finite support.
Applying this to the swapped finite-support trajectory proves actual source-flow
covariance. Spectral finite-gap density extends it to the full original real
Hilbert source; the equal-field Hilbert diagonal is therefore preserved.

The source phase trajectories and actual image lifts are now proved compatible
under exponent inclusion, retaining explicit image conditions. Finite Fourier
inputs have native Hilbert representatives with exactly the same original
coefficients. Hilbert diagonal preservation therefore transfers to all such
inputs at every finite p>1. Diagonal-preserving original Fourier approximants
converge in the actual source norm, and the open image domain gives eventual
admissibility at each admissible time. Continuity and the closed equal-field
source slice prove preservation for every rough diagonal datum.

The final physical adapter states that the actual fixed-family fourth image
flow remains in the closed equal-DISTRIBUTION mKdV subspace at every admissible
time, throughout the finite-p domain. This is actual source-flow preservation,
not an inference from even actions and odd frequencies alone. The auxiliary
angle identity of equation (50) is not assumed in this alternative proof.

Theorem 1.1 remains incomplete: smooth physical PDE agreement, packaging the
scalar real trajectory and its exact smooth-approximation/uniqueness notion,
and controlled divergent-mass fixed-time nonextension are still required.
Theorems 1.2 and 1.3 remain verified.

All 13 final new modules pass strict Lean 4.33.1 checks. The 130 unchanged
parent modules reuse fa047be0b6caacf63c5f7f67d447bee7cf83c434 after source
comparison. The full fresh transitive audit checks 671 named declarations,
with only propext, Classical.choice and Quot.sound. The checker lists 143
modules. No holes, added axioms, disabled linters or increased heartbeat or
recursion limits were introduced. Canonical compiled dependencies are read-only.


## Nineteenth checkpoint: full physical H4 cotangent and actual corrected ODE

The original weighted real form now determines full complex analytic germs
and cotangents for every spectral weight and finite Banach source exponent.
An abstract coordinate transport isolates the analytic identity argument;
explicit normalized real membership and inverse lemmas keep the concrete
weighted proof within the default kernel limits.

The actual native physical action map into ell^(3,1) is differentiated in
its full norm. Coordinate derivatives are the original complex action
cotangents on unchanged raw source directions. A single finite cutoff
supporting the original action cotangents supports this entire weighted
sequence derivative, including arbitrary directions opening closed gaps.
The genuine local H4 action factor gives the physical native derivative as
the finite sum weighted by the independent physical H4 frequencies. Real-form
determination upgrades the equality to the entire complex native derivative.
It is the restriction of a bounded original Hilbert cotangent at finite gaps.

The native polynomial along every represented smooth complex perturbation
line agrees with the independent physical Riccati H4. Its derivatives are
therefore the previously certified physical gradient integrals. Testing all
signed Fourier modes identifies both Hilbert cotangent components with the
reflected physical gradient. Applying the original source Poisson operator
gives exactly both Fourier integrals of the certified physical third-order
fourth vector field. Actual finite-gap smooth representatives have native
fractional lifts, and the field's total Hilbert constructor recovers every
physical Fourier integral. The finite original action Hamiltonian sum with
independent H4 frequencies is exactly this physical source field.

Reality of the independent H4 frequency is also proved directly throughout
the full native domain from its real physical Hamiltonian curves, including
the closed-action second amplitude derivative. It does not depend on the
article's normalized moment candidate.

Actual action-invariant image lifts preserve finite-gap regularity at all
admissible times, retaining one fixed original cutoff for every full action
cotangent. For the fixed article fourth family, the actual finite-gap
source-norm time derivative is now the original Poisson direction of
L4 - 6H2*dH1 - 6H1*LP. L4 is calibrated on the full physical fractional H4
derivative and dH1 is the actual physical mass cotangent. LP remains the
explicit finite signed sum of 2*pi*n times original action cotangents.
Identifying LP with the physical momentum cotangent is still necessary.
The corresponding physical correction is H4 - 6H1*H2; H2=0 on the diagonal
does not make dH2 vanish.

Theorem 1.1 remains incomplete. Physical momentum calibration, pointwise
smooth PDE agreement, the scalar trajectory and exact smooth-approximation
solution/uniqueness requirements, and fixed-time divergent-mass nonextension
remain open. Theorems 1.2 and 1.3 remain verified.

All nine final new modules pass strict Lean 4.33.1 checks; 143 unchanged
parent modules reuse 1da0001479d89ea2584a38f20d59187041ebca0f after source
comparison. A fresh full transitive audit checks 702 declarations, only
propext, Classical.choice and Quot.sound. The checker now lists 152 modules.
No holes, added axioms, disabled linters or increased heartbeat or recursion
limits were introduced. Canonical compiled dependencies remain read-only.
