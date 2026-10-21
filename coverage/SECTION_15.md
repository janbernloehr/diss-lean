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


## Physical Hilbert form of Lemma 15.3

[`PhysicalBirkhoffCanonical.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffCanonical.lean)
now proves the same three identities using literal physical L2 integrals,
with the unique physical gradients of the full complex differentials.
The map is the intrinsic physical action-angle map constructed in the
[Section 14 audit](SECTION_14.md). The mixed bracket retains the source
sign -delta_nm. All real Hilbert inputs, including collapsed gaps, are
covered, and a canonical complex extension is constructed without a
supplied original family. The general finite-exponent Fourier statements
above remain unchanged.

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
open-gap expressions. The follow-up below now constructs actual complex
potentials in F_0 with a collapsed central gap, together with open-gap
sequences realizing both original signed limits. Exactly one limit is zero.

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

## Physical action differentials and Hamiltonian signs

[`PhysicalHamiltonianDirection.lean`](../NLS/ZakharovShabat/PhysicalHamiltonianDirection.lean)
realizes the Hamiltonian direction in the native physical Hilbert pair by
the actual cross-gradients (-i grad_2, i grad_1). Every differential evaluates
on it to the literal physical bracket. Together with the full physical
identity dI_n=x_n dx_n+y_n dy_n, Lemma 15.3's mixed bracket -delta_nm
therefore gives velocity (-y_n,x_n) in the selected coordinate pair.

[`PhysicalActionHamiltonian.lean`](../NLS/ZakharovShabat/PhysicalActionHamiltonian.lean)
proves this for every real physical input, including closed gaps and signed
indices, and for a constructed extension of the intrinsic map. At closed
gaps, the entire action differential and physical field vanish, which is
stronger than zero coordinate velocities alone. Real tangency is proved
independently through the physical cross-gradient formula. Flow existence
is outside this step's claims.

## Complete physical evolution of the action fields

The later modules
[`PhysicalActionFlow.lean`](../NLS/ZakharovShabat/PhysicalActionFlow.lean) and
[`PhysicalActionFlowProperties.lean`](../NLS/ZakharovShabat/PhysicalActionFlowProperties.lean)
now construct complete trajectories of the fields above and prove uniqueness
against arbitrary complex physical L2 solutions from the same real initial
state. A closed selected gap is stationary for all times. The full
discriminant, every action, and the original physical norm are preserved.
[`PhysicalActionFlowGroup.lean`](../NLS/ZakharovShabat/PhysicalActionFlowGroup.lean)
proves the exact signed rotation, commutation, period 2*pi, joint continuity,
and homeomorphism group properties.

## The gap and original eta modulo 2*pi are discontinuous, printed p. 74

The unnumbered paragraph before Lemma 15.1 says that the ordered gap and
eta modulo 2*pi can have discontinuities.
[SourceOriginalGapEtaDiscontinuity.lean](../NLS/ZakharovShabat/SourceOriginalGapEtaDiscontinuity.lean)
proves this for the actual central gap and the literal original-integral
phase exp(i eta), on the unchanged original angular domain. It uses the
constant-source endpoint witnesses from the [Section 8 audit](SECTION_8.md).

For every finite p>1, every retained original normalized psi family, and
every source neighborhood V of zero, a positive r gives a source (r,-r)
in W intersect V. Its central gap is open. Both that gap and exp(i eta)
fail continuity within the same original central open-gap domain at
this source. Neither function is continuous on that domain.

The midpoint and squared gap are analytic. At a collapsed gap,
continuity of the squared gap forces continuity of the gap itself,
because its norm is the square root of the squared gap's norm. Thus the
endpoint-discontinuity witness must have an open gap. Continuity of the
gap there would make the left endpoint continuous through
left=midpoint-gap/2, a contradiction.

The exact original integral formula identifies the analytic weighted
coordinate z+ with gap*exp(i eta). The exponential never vanishes.
Continuity of exp(i eta) would therefore make the gap continuous by
division. This proves discontinuity of the actual phase modulo 2*pi,
independently of the integral representative, while the already proved
phase modulo pi and weighted-coordinate analyticity remain valid.

Two public examples construct an original family at p=4 with an
analytic weighted coordinate and both failures of continuity, and give
a witness in every prescribed source ball at p=3/2. The result concerns
existence of central-index discontinuities, not discontinuity at every
source or every signed index, and does not assert a discontinuity at zero.

## Actual complex collapsed-gap witnesses for the printed p. 74 limits

The conditional sign classification above is now realized by actual original
potentials. For every finite p>1, every retained normalized psi family and
angular domain W, and every original-source neighborhood of zero, there is
a nonzero constant triangular source (a,0) in W and that neighborhood with
both central periodic endpoints zero and its central Dirichlet root nonzero.
It therefore lies in the source's F_0 and has a collapsed central gap.

[SourceTriangularCollapsedWitness.lean](../NLS/ZakharovShabat/SourceTriangularCollapsedWitness.lean)
first uses the exact free spectrum of triangular operators. Continuity of
the canonical endpoints at the zero source forces the nearby central pair
to remain at the isolated free spectral point zero. In contrast, the actual
Dirichlet root along the original bounded linear curve a ↦ (a,0) has
complex derivative 1/2 at zero, for every finite p>1. It cannot vanish
throughout any parameter neighborhood. This constructs witnesses rather
than assuming that a collapsed gap with an exterior Dirichlet root exists.

[SourceCollapsedOriginalEtaWitness.lean](../NLS/ZakharovShabat/SourceCollapsedOriginalEtaWitness.lean)
chooses the witness within the same original angular domain. It then
constructs a sequence of constant potentials

`(a, (1/(k+1))^2/a)`

approaching (a,0). After shifting the sequence by a finite number of terms,
every term lies in W and has an open central gap. The exact canonical-pair
identification gives roots 1/(k+1) and its negative before that shift.

For each sign, the original expression gamma_0*exp(±i*eta_0) converges along
this sequence to the corresponding analytic extension at the witness.
Exactly one limit is zero and the other is nonzero. The formal theorem
`original_collapsed_both_signed_values_nonzero_false` consequently refutes
simultaneous nonvanishing on F_0. The proof retains the original integral
signs and normalized psi family; it does not choose which sign is nonzero.

These are complex sources. The existing disjointness of F_0 from the real
locus excludes real witnesses, and the real interlacing result is unchanged.
This strengthens the earlier conditional classification to a constructed
source counterexample, recorded in [source discrepancies](../SOURCE_ERRATA.md).
