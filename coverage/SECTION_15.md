# Section 15 original-coordinate audit

Source: printed pp. 74–75, the gap-weighted coordinates, Lemma 15.1,
equation (3.2), Theorem 15.2, and Lemma 15.3. The root family is the same
family retained from Lemma 12.12 and the original Section 13 integrals.
`sourceSection15_original` constructs this package for every finite p>1.
In the table, D denotes `SourceSection15OriginalData` and H denotes
`D.previous : SourceLemma12_12Data`.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| zₙ± = γₙ exp(±iηₙ) on open gaps | `H.gapWeightedEta_original_signed`, `H.gapWeighted_original_sequence_apply` | Exact original eta phase, both signs, actual sequence entries |
| Analytic extension through complex collapsed gaps | `H.gapWeightedEta_original_analytic` | Every complex source in the unchanged original angular domain W |
| Limits along open-gap sequences | `H.gapWeighted_original_phase_limit` | Any converging net eventually in W with the selected gap open; terminal source may have a collapsed gap |
| Fₙ = {ψ ∈ W : μₙ ∉ Gₙ} is open and disjoint from the real locus | `H.dirichletOutsideGap_original_open`, `disjoint_sourceDirichletOutsideGap_realType` | Full complex topology; follows from analytic symmetric endpoints, analytic Dirichlet roots, and real interlacing |
| Behavior of signed limits at collapsed gaps | `H.gapWeighted_original_collapsed_pair_zero_iff`, `H.gapWeighted_original_collapsed_pair_exactly_one_nonzero` | Both vanish iff μₙ=τₙ; otherwise exactly one sign is nonzero |
| Lemma 15.1: analyticity and index-uniform local estimate | `H.gapWeightedEta_original_analytic`, `D.gap_bound` | At every complex point of W, one open neighborhood and positive C work for all n and all complex σ with norm at most one |
| Locally uniform ℓᵖ membership of z± | `D.sequence_local`, `D.gap_sequence_analytic` | Actual ℓᵖ sequence values and one local norm bound; full Banach-valued analyticity on W |
| Equation (3.2) | `D.equation3_2` | Actual sequence coordinates on V, including collapsed gaps, with the difference in the y-coordinate |
| Theorem 15.2 | `D.theorem15_2` | Real analytic map on the entire real space, complex analytic extension on V, and exact complex inclusion of the real map |
| Lemma 15.3 | `D.lemma15_3`, `D.complex.mixed_fourier_canonical` | All three brackets at every real source; actual complex derivatives and absolutely convergent Fourier bracket, also for p<2 |

## Uniformity on the original domain

The original quotient estimate bounds each diagonal eta numerator minus i
on its isolating disk, with one local constant for all indices. Filling
the deleted root with the midpoint leaves the deleted product unchanged.
Fixed tail annuli convert this estimate into one eta-remainder bound for
all sufficiently distant indices. Finitely many annulus charts cover the
remaining indices. Their neighborhoods are intersected and their constants
combined, giving the bound C(|γₙ|+|μₙ−τₙ|) uniformly in n.

The gap and Dirichlet-minus-midpoint sequences have locally bounded ℓᵖ
norms. Their majorant proves that the actual z coordinates belong to ℓᵖ,
with a common local norm bound. The `Coeff.ofFunctionOrZero` realization
therefore evaluates to the actual coordinates throughout W. Coordinate
analyticity and local boundedness give sequence-valued analyticity.
No real-type hypothesis is used in these bounds or in the sequence result.

## Domains and retained results

W is exactly the original angular domain. Its new z estimates and sequence
analyticity require no further restriction. V is the compatible complex
Birkhoff domain constructed in Section 14: an open subset of W containing
the entire real locus. Normalized-action roots, the Birkhoff sequence map,
and equation (3.2) are asserted on V. The construction does not assert
V=W or extend the normalized-action root to every point of the larger W.
On V all assertions of Theorem 15.2 hold, and the z estimates restrict there.

The package extends `SourceSection14Data`, preserving the same root family
and map, full complex exponent compatibility, indexed-action radii, real
local inverses, and the global real inverse for 1<p≤2. Its construction
supplies the bounds and sequence membership; callers need not assume them.

## Collapsed-gap and sign qualifications

The source's sentence about a nonzero collapsed limit on Fₙ must distinguish
the two signs. The exact identity zₙ+ zₙ− = γₙ² implies that at a collapsed
gap at least one sign vanishes. The formal algebra shows that both vanish
exactly when μₙ=τₙ; outside that midpoint exactly one is nonzero. The net
limit theorem identifies these values with the limits of the original
open-gap expressions. No existence of a potential in Fₙ with γₙ=0 is
claimed here, so this is not a constructed physical counterexample.

The opening exponential rewrite for y on p. 74 has a plus where the sine
formula requires a minus. Equation (3.2) on p. 75 has the correct difference,
which is used in Lean. The visual source check and algebraic explanation
are recorded in [source discrepancies](../SOURCE_ERRATA.md).

## Validation and next step

Fifteen new public checks cover complex-domain uniformity, actual sequence
values and original phases, the outside-gap geometry, net limits, collapsed
classification, equation (3.2), real and complex analyticity, all canonical
brackets, and unconditional constructions at p=3/2 and p=4 with retained
complex exponent compatibility.

Validation: `./scripts/check.sh` passes: the full build completes 7,113
jobs, all public examples pass, and the transitive axiom audit checks 33,743
NLS declarations. The five new modules and fifteen new checks introduce
no warnings; the 21 existing warnings remain. The source inventory
verifies all 156 candidate labels, all 235 checked local Markdown file
links resolve, and `git diff --check` passes.

Next: audit Section 16's Jacobian, finite-gap estimates, and operator
arguments against the same original map, followed by Section 17. The
external-map and fractional-smoothness qualifications in the
[Section 14 audit](SECTION_14.md) remain. This is not a completeness
certificate for Chapter 3 or the dissertation.

## Modules

- [Original diagonal numerator estimate](../NLS/ZakharovShabat/SourceAngularOriginalDiagonalBound.lean)
- [Original-domain index-uniform bound](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalBound.lean)
- [Actual analytic gap-weighted sequences](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalSequence.lean)
- [Outside-gap geometry and collapsed limits](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginalCollapsed.lean)
- [Section 15 original-family package](../NLS/ZakharovShabat/SourceSection15Original.lean)
