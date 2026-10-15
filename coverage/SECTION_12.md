# Section 12: psi-functions

This audit begins with printed p. 63 of the dissertation. Theorem 12.1,
including the entire product (2.20) and the normalized periods (2.21), is
proved on one common neighborhood inside the original Section 11 source
domain. The scalar formulation (2.22)–(2.23) is proved. Lemmas 12.2–12.3
now have explicit admissibility versions on original filled disks and
contours constructed in arbitrary analytic gap neighborhoods, including
complex open and collapsed gaps. Lemma 12.4 now holds on the full original
source domain for arbitrary root inputs, with actual ℓᵖ-valued complex
and real analyticity and bounds locally uniform in every deleted index.
The literal auxiliary products (2.24)–(2.25), the full original-disk
asymptotic (2.26), and the actual equation-index supremum sequence in
Lemma 12.4's proof are now also certified. Lemma 12.5 now holds for the
actual original-domain Jacobian, with nonzero diagonals and the full
locally uniform diagonal/off-diagonal estimates. Lemma 12.6 now gives an
invertible diagonal plus a compact remainder for that same actual
Jacobian, with explicit reciprocal inverse and finite-rank norm
approximations. Lemma 12.7 now proves injectivity of the actual Jacobian
on the original domain, including the complex kernel reduction, original
gap interpolation, and literal outer-circle product and decay formulas.
Corollary 12.8 now gives continuous inverses on the actual complex and real
deleted spaces, including identification with the real equation's derivative.
The first proof steps of Lemma 12.10 now establish literal (2.28), the
bounded intrinsic Q*, equation (2.29), compactness of Q*−2I, and continuity
on the original domain. Full original-domain operator-norm convergence
and compact-set uniformity are now proved. Tolerance-dependent local
uniformity holds, while uniform convergence on any fixed neighborhood
of the free point is disproved. Full-domain invertibility and common
complex inverse bounds are now proved. The common analytic solution
extension on the original domains is still outstanding.

Proposition 12.9 now gives the unique global real analytic solution of the
original equation on the projected original domain, with exact gap placement,
local implicit branches, and norm convergence along source sequences.
Existing later psi modules are ingredients, not a completeness claim for
every subsequent statement or proof assertion in this section.

## One family on one common neighborhood

For every finite p>1, `sourceTheorem12_1` supplies an open connected W₀
containing the entire real-type source locus, the complete
`SourceSection11OriginalEstimates` on W₀, and an open simply connected
W⊆W₀ also containing that locus. One family
`s : (n : ℤ) → CoeffPair p → DeletedCoeff p n` works on W for all n.

`SourceSection11OriginalEstimates.psiFunctions` performs the same
construction inside any supplied open W₀ containing the real-type locus.
The package's `.previous` field retains all preceding results on that
unchanged W₀. The new W is allowed to be smaller, as in the source's
Theorem 12.1. No intersection of separately chosen root families occurs:
one squared-gap root atlas supplies the analytic maps, estimates and
periods together.

Define σₘⁿ(ψ)=`displacedRoots (s n ψ : Coeff p) m` and
ψₙ(z,ψ)=`sourcePsiCandidate n (z,(s n ψ : Coeff p))`.
Each displacement vector is an actual ℓᵖ vector with its unused nth
coordinate zero, so σₘⁿ=πm+ℓᵖ holds with the source's signed indexing.

| Source assertion | Public API | Scope |
| --- | --- | --- |
| One neighborhood for all n | `sourceTheorem12_1`, `SourceSection11OriginalEstimates.psiFunctions` | Every finite p>1; all real sources belong to W⊆W₀; original results retained on W₀. |
| Literal product (2.20) | `tendsto_sourcePsiCandidate_literalProduct` | Symmetric cutoffs over `[-N,N]` with n deleted, prefactor −2/πₙ, and `singleSpectralDenominator 0 = 1`. |
| Entire ψₙ | `SourceTheorem12_1Data.entire` | Every complex source in W, all n; the stronger `.numerator_joint` gives joint spectral/source analyticity. |
| Actual roots of ψₙ | `sourcePsiCandidate_other_root` | Every retained m≠n is a zero, including collisions. |
| Analytic root dependence | `.root_analytic`, `.root_real_analytic` | Complex and real analyticity of the actual root coordinates on W. |
| σₘⁿ=τₘ+γₘ²ℓᵖ | `.locally_uniform_offsets` | One neighborhood and one bound before all n, at every complex point of W; actual ℓᵖ coefficients with omitted coordinate zero. |
| Real gap placement | `.root_mem_gap`, `.root_real_bounds` | Retained roots have zero imaginary part and lie between the actual ordered periodic endpoints. |
| Free specialization | `.displacement_zero`, `.root_zero`, `.numerator_zero` | Exact zero displacement, signed free lattice roots, and the correctly normalized filled sine quotient. |
| Normalized period (2.21) | `.period`, `.circuit` | Every original period circle or admissible piecewise C¹ circuit of winding one, including collapsed complex gaps. |
| General winding | `.circuit_winding` | Period δₘₙ times the circuit's winding around the actual midpoint. |

The products are limits of symmetric finite cutoffs. No unordered infinite
product is substituted for the source's normalization. Likewise, the
estimate retains the literal γₘ² coefficient: it does not divide by a
possibly vanishing gap. At a collapsed complex gap the retained root is
therefore exactly τₘ.

## Original circuits and normalization

`sourcePsiCircuit` is the literal integral of ψₙ divided by the canonical
root, multiplied by 1/(2π). Its circle specialization equals the
existing `sourcePsiContour` exactly; there is no extra factor of i.

`SourceCriticalRootPeriodCircle.psiContour_eq` compares two original
circles enclosing the same actual gap, even when they are not nested.
The affine circle homotopy avoids every gap by their real-center
projection separation. The atlas's disjoint real-centered disks provide
this geometry through
`SourcePsiIsolatingComplexRootAtlas.assignedPeriodCircle`.
`.periodCircle_orthogonality` transfers the existing assigned-circle
normalization to every original circle on the same atlas.

For an arbitrary original isolating family `D` near ψ, the loop may be
any finite piecewise C¹ loop inside Dₘ minus the actual gap Gₘ(ψ).
`SourceCriticalRootPeriodCircle.psiCircuit_eq_mul_winding` uses the
analyticity of the actual psi/root integrand and the compact, star-convex
gap segment to identify its period with the original outer-circle
period times its winding. A winding-one loop gives (2.21); no separate
homotopy supplied by the caller, nonzero-gap assumption, or real-source
restriction is needed. Winding is measured at the actual midpoint,
which lies in the segment even when the segment collapses.

The existing Section 11 contour families provide simultaneous fixed
circuits and collars locally. The integrand's joint analyticity on W₀
follows directly from the retained canonical-root data through
`SourceSection11OriginalEstimates.psiIntegrand_joint`.

## Implementation and validation

The four new modules are `SourcePsiPiecewiseContour`,
`SourcePsiOriginalPeriods`, `SourceTheorem12_1`, and
`SourceTheorem12_1Functions`, all exported by `NLS.lean`.
Twenty focused public checks exercise the exact source-domain and
uniformity quantifiers, literal product, zero-mode denominator, root
zeros, entireness, joint and real analyticity, complex collapse, ordered
real bounds, original circles and circuits, winding two, both signed
free roots, a nonzero free center value of −2, and p=3/2 and p=4.

The full `./scripts/check.sh` gate passed: 6,966 build jobs, the complete
public example suite, and the axiom audit of 32,621 NLS declarations.
There are 21 existing build warnings; the four new modules and twenty
focused checks are warning-free. No admitted proofs, additional axioms,
or heartbeat overrides were introduced. The 156-label source inventory,
repository documentation links and `git diff --check` also passed.

## Scalar equations (2.22)–(2.23) and local numerator domains

`sourceGapFunctional hp hp1 n m ψ Γ f` is exactly
(n−m)∫_Γ f/canonicalRoot. Its actual finite piecewise C¹ integral has no
normalizing factor. `sourceGapFunctional_candidate_circle` identifies it
with `sourcePsiEquationCoordinate` when f is the arbitrary entire product
in (2.23). The existing literal symmetric-product limit applies to every
ℓᵖ displacement vector; no root placement or equation-solving hypothesis
is imposed. The unused deleted coordinate remains irrelevant.

`SourceCriticalRootPeriodCircle.psiEquation_eq` proves independence of
original circle families. `.psiEquation_circuit` gives the coordinate
times winding on every original cut disk. `SourceTheorem12_1Data.equation_zero`
shows that the same simultaneous root family solves all these scalar
equations, without requiring a new choice of roots or source domain.
The full sequence-valued range and uniform mapping statement belong to
Lemma 12.4 and are not asserted by these scalar identities.

The general `.localNumerator_circuit_eq` and
`.gapFunctional_eq_mul_winding` allow any numerator analytic on a
neighborhood of the filled original disk. At real sources,
`.localNumerator_zero_of_circle` combines open and collapsed gaps.
`.localNumerator_zero_of_functional` assumes m≠n and any nonzero winding,
and concludes a genuine numerator zero in the actual gap. The numerator
need only be real on that gap. The collapsed Cauchy argument itself
needs no numerator reality. `.localNumerator_zero_of_functional_on`
accepts an explicitly supplied larger analytic domain containing the
filled disk. The entire-numerator APIs keep their original signatures
and now specialize these local proofs.

The hypotheses about the analytic region are substantive. The verified
`sourceLocalContourPole_counterexample` shows that merely containing the
gap and curve in an open analytic domain does not imply either conclusion
of Lemma 12.3. At the free collapsed gap, f(z)=z/(z−1/2) gives zero on the
gap but normalized period −1 and normalized norm 1 on the unit circle.
The circle avoids all free gaps. See the
[domain clarification](../SOURCE_ERRATA.md) for the precise interpretation.

This is the disk version of the local zero-contour implication. The audit
does not yet claim the complete arbitrary-neighborhood version of Lemma
12.2, the complex open-gap estimate of Lemma 12.3, or its full admissible
local-contour formulation. Those remain ahead of Lemma 12.4.

Five new modules supply this continuation: `SourceLocalGapContourZeros`,
`SourceGapFunctional`, `SourceGapFunctionalZeros`, `SourceEquation2_22`,
and `SourceLocalContourDomain`. `SourceEntireGapContourZeros` now wraps
the local proofs while preserving its public signatures. Seventeen
focused public checks cover the unnormalized signed factor, arbitrary
products and circle choices, original circuits, the simultaneous
solutions, local numerators, reversed winding, collapsed gaps without
numerator reality, an exterior pole, the necessity of m≠n and nonzero
winding, the actual winding and gap avoidance of the counterexample,
both refuted conclusions, and p=3/2 and p=4.

Validation: `./scripts/check.sh` passed (6,971 build jobs, the complete
public example suite, and the axiom audit of 32,661 NLS declarations).
The build retains 21 existing warnings; all new and refactored modules
and the seventeen focused checks are warning-free. The 156-label source
inventory and `git diff --check` passed. No admitted proofs, additional
axioms, or heartbeat overrides were introduced.

## Lemmas 12.2–12.3: arbitrary analytic gap neighborhoods

The contour-domain clarification above is now supported by a positive
local construction. No enclosing midpoint disk is assumed to lie in the
numerator's analytic domain. For midpoint τ and nonzero complex half-gap
δ, put J(u)=τ+δ(u+u⁻¹)/2. For |u|>1 the verified branch identity is

    normalizedStandardRoot(τ,(2δ)²,J(u)) = δ(u⁻¹−u)/2,
    J′(u)/normalizedStandardRoot(τ,(2δ)²,J(u)) = −1/u.

The image of a circle |u|=r>1 is an actual smooth closed ellipse avoiding
the gap. Compactness of the unit circle gives a closed annulus 1≤|u|≤R
whose image lies inside any supplied open gap neighborhood. Holomorphy
of f(J(u))/u makes the ellipse periods independent of r by the annular
Cauchy theorem. Uniform continuity on [1,R]×[0,1] gives the limit at r=1,
where the image is τ+δ cos(2πt). Thus the literal ellipse integral is
−2πi times the ordinary gap average. At collapse an arbitrarily small
Cauchy circle gives the same formula.

| Source assertion | Public API | Explicit scope |
| --- | --- | --- |
| Local adapted standard-root period | `exists_sourceStandardRoot_local_period` | Every finite p>1, every complex source, any open analytic gap neighborhood; an actual winding-one contour stays inside that region and avoids the gap; collapse included. |
| Local estimates in Lemma 12.3 | `sourceLemma12_3_local`, `SourceLemma12_3Estimates` | An attained maximum of |f| bounds the 1/(2π)-normalized absolute period; gap reality gives the exact negative mean value with 1/(2πi). |
| Entire family of small ellipses | `exists_sourceStandardRoot_local_ellipse_estimates` | One R>1 and one maximum point work for all 1<r≤R at each noncollapsed complex gap. |
| Original outer circle | `SourceCriticalRootPeriodCircle.standardRoot_local_circle_period`, `.lemma12_3_circle` | Local numerator analytic near the filled original disk; all complex open and collapsed gaps. |
| Original piecewise circuits | `.standardRoot_local_circuit_period`, `.lemma12_3_circuit` | Exact period multiplied by arbitrary winding; the estimates specialize to winding one. |
| Lemma 12.2 on an adapted local contour | `.lemma12_2_local` | Real source, m≠n, numerator analytic on any open gap neighborhood and real only on the gap; the constructed contour lies in its intersection with the original disk and avoids all periodic gaps. |
| Lemma 12.2 on original circuits | `.localNumerator_zero_of_functional` | The earlier filled-disk result, with any nonzero winding, remains available. |

The local construction does not assert the estimates for every loop
merely lying in a multiply connected analytic domain. It supplies the
contour needed for the local interpretation, while the original-disk
version proves the formula on every original circuit under its explicit
sufficient condition. The interior-pole counterexample remains valid.
The audit does not substitute an unspecified contour-integral axiom for
these geometric conditions.

Ten modules implement this step: `SourceStandardRootJoukowski`,
`SourceStandardRootEllipseGeometry`, `SourceStandardRootEllipsePath`,
`SourceStandardRootEllipsePeriod`, `SourceStandardRootLocalEllipseEstimates`,
`SourceStandardRootLocalEllipses`, `SourceStandardRootOriginalLocalPeriod`,
`SourceStandardRootLocalContours`, `SourceLemma12_3`, and
`SourceLemma12_2LocalContours`. All are exported by `NLS.lean`.

Nineteen focused checks cover complex branch directions and parameters,
closed paths, limiting midpoint values, normalization, actual winding,
arbitrary complex sources, reversed repeated circuits, negative indices,
collapsed gaps without numerator reality, the local zero implication,
and p=3/2 and p=4. The numerator (z²+1/16)⁻¹ proves the local mean-value
theorem even though every enclosing midpoint disk contains a pole.
The earlier z/(z−1/2) example has a new admissible contour of period zero,
while a separate check refutes Lemma 12.3's conclusions on its unit circle.

Validation: `./scripts/check.sh` passed (6,981 build jobs, the complete
public example suite, and the axiom audit of 32,768 NLS declarations).
The build retains 21 existing warnings; the ten new modules and nineteen
focused checks are warning-free. The source inventory verified 156
candidate labels, and diff checks passed. No admitted proofs, additional
axioms, or heartbeat overrides were introduced.

Next: audit Lemma 12.4 on the full original source domain, with an actual
ℓᵖ-valued map and local bounds uniform in all deleted indices. Existing
selected-equation analyticity alone does not establish that statement.

## Lemma 12.4: the actual sequence map on the original W

`SourceSection11OriginalEstimates.lemma12_4` upgrades the supplied package
on exactly the same W. Its `SourceLemma12_4Data.previous` field retains
that package. `sourceLemma12_4` constructs the open connected W containing
the entire real-type source locus with the full new statement.

| Assertion | Public API |
| --- | --- |
| Literal coordinates form a deleted ℓᵖ sequence on W | `SourceCorollary10_6Data.originalEquation_exists` |
| Every original circle gives the same actual coordinate | `.originalEquation_apply`, `SourceLemma12_4Data.equation` |
| Complex and real analyticity in (source, roots) | `SourceLemma12_4Data.analytic`, `.real_analytic` |
| One local bound before choosing n | `.locally_uniform` |
| Positive strict bound for the literal p-power sum | `.power_sum` |
| Real source and real displacement inputs give real outputs | `.real` |
| Every original circuit, with actual winding | `.circuit` |
| Theorem 12.1 family solves the Banach-valued map | `SourceTheorem12_1Data.originalEquation_zero` |

The bound does not require numerator roots to belong to the isolating
disks. For the unused index n, fill its root with the base source midpoint
ξₙ in the original disk Dₙ. The added single-coordinate displacements lie
in a compact subset of ℓᵖ, by a fixed coefficient majorant. Local quotient
bounds on the original disks, combined over a finite subcover of this
compact set, yield one bound for all n and all selected m. Disk separation
bounds |n−m|/|ξₙ−z|. The exact complex-gap estimate from Lemma 12.3 gives

    |Fₘⁿ| ≤ 2π C (|aₘ| + |τₘ−mπ| + |γₘ|).

The three sequences are in ℓᵖ and their norms are locally bounded around
every complex source. This proves membership and a bound for the literal
coordinates simultaneously. Analytic scalar contours and the bounded
coordinate analyticity theorem assemble the actual Banach-valued map.
Contour independence identifies all local constructions on overlaps.

`sourcePsiOriginalEquation` is a total choice definition, with a fallback
if its coordinate characterization has no witness. Existence is proved
for every source in W and every deleted ℓᵖ input, so its values on W are
always the actual contour equation. The omitted coordinate is zero; the
sum over all integers in `.power_sum` is therefore the printed deleted sum.

Seventeen focused checks include a large imaginary root displacement
outside its disk and exact response 200i, a retained-root collision and
analyticity there, an explicitly nonreal source in every open W containing
zero, winding −2, unchanged-domain transfer, the simultaneous solution,
and p=3/2 and p=4.

Validation: `./scripts/check.sh` passed (6,989 build jobs, the complete
public example suite, and the axiom audit of 32,817 NLS declarations).
The build retains 21 existing warnings; the eight new modules and seventeen
focused public checks are warning-free. The source inventory verified
156 candidate labels, and diff checks passed. No admitted proofs,
additional axioms, or heartbeat overrides were introduced.

The initial mapping proof established Lemma 12.4 directly, without
assuming (2.26). The following milestone now certifies that intermediate
asymptotic and the stronger supremum statement used by the printed proof.

## Literal auxiliary products and uniform suprema, (2.24)–(2.26)

For arbitrary full ℓᵖ root input a and complex source ψ, define

    ζₘⁿ(z) = (i/wₙ(z)) ∏_{k≠m,n} (σₖ−z)/wₖ(z).

The deviations of the individual factors from one are absolutely
summable. The product is unconditional, with an exact subtype-indexed
`HasProd` statement. Its cross-multiplied relation to the single-omitted
quotient permits vanishing numerator factors. The actual contour
integrand equals ((σₘ−z)/wₘ(z))ζₘⁿ(z) everywhere off the periodic gaps,
without assuming σₙ≠z or excluding retained-root collisions.

The expression iQₘ/(σₙ−z) equals this product when σₙ≠z. At σₙ=z it
may have a removable division point. The example n=0, m=1, a₀=i,
ψ=0, z=i has literal ζ₁⁰=−1 and actual integrand −1, while the old
totalized quotient equals zero. The new public checks verify these
values and membership of z=i in the full gap complement.

Fix any original isolating family D near any complex base φ∈W, and
let ξₙ=τₙ(φ). Define the reciprocal-distance term by

    Rₘⁿ(z) = i ((n−m)/(ξₙ−z) − 1/π).

The sequence term S is the exact remainder in

    (n−m)ζₘⁿ(z) = i/π + Rₘⁿ(z) + Sₘⁿ(z).

One neighborhood of every full input/source pair and constants K,C
precede all choices of n. For m≠n and every z∈Dₘ, |Rₘⁿ(z)|≤K/|n−m|.
The sequence Eₘⁿ=sup_{z∈Dₘ}|Sₘⁿ(z)|, with Eₙⁿ=0, is an actual ℓᵖ
sequence and has norm at most C. This includes the original finite
head, complex gaps and collapse. W is not replaced by a root-input
dependent domain, and no retained root-location restriction is imposed.

The quotient error on all original disks first has a local ℓᵖ bound
from its exact ℓᵖ+l^(p/2) decomposition. The second summand embeds
contractively into ℓᵖ, also for p<2. Compact base insertions and
contractive deletion of nearby perturbations give one bound for every
replacement of coordinate n by the fixed midpoint displacement.
Original disk separation then supplies the reciprocal estimate.

For the stronger assertion in the proof of Lemma 12.4, a common
ℓᵖ majorant controls Fₘⁿ(ψ,deleteₙ a) for all n simultaneously.
The actual sequence Bₘ=sup_{n≠m}|Fₘⁿ(ψ,deleteₙ a)| is locally bounded
in ℓᵖ. This conclusion uses a common coordinate majorant, rather than
inferring membership of a supremum from separate sequence norm bounds.

| Assertion | Public API |
| --- | --- |
| Absolute convergence and literal double-omitted product | `summable_norm_sourcePsiDoubleOmittedFactor_sub_one`, `hasProd_sourcePsiDoubleOmitted_subtype` |
| (2.24) including numerator collisions | `sourcePsiContourIntegrandJoint_eq_zeta` |
| (2.25), with its exact minus sign | `sourcePsi_zetaSingle_eq_product` |
| Exact decomposition into i/π, R, and S | `sourcePsi_zeta_decomposition` |
| Uniform estimates on every supplied original disk family | `SourceCorollary10_6Data.zeta_originalAsymptotic_sup` |
| (2.26) throughout the unchanged original source domain | `SourceLemma12_4Data.equation2_26` |
| Common sequence majorant for all omitted equations | `SourceCorollary10_6Data.originalEquation_commonMajorant` |
| Actual supremum over all omitted equations | `SourceLemma12_4Data.originalEquation_indexSup` |

Next: Lemma 12.5's actual Jacobian on the original real domain Ωᵖ,
including nonzero diagonal entries and the full diagonal/off-diagonal
asymptotics. Existing restricted tail results do not certify all of this.

Validation: `./scripts/check.sh` passed (6,996 build jobs, the complete
public example suite, and the axiom audit of 32,893 NLS declarations).
The build retains 21 existing warnings. The seven new modules, extended
compact-slice helper, and eighteen focused public checks are warning-free.
The source inventory verified 156 candidate labels, and diff checks
passed. No admitted proofs, additional axioms, or heartbeat overrides
were introduced.

## Lemma 12.5 on the original real domain

`SourceLemma12_4Data.lemma12_5` proves Lemma 12.5 for the actual bounded
root derivative of the original equation, retaining the preceding source
domain W. `sourcePsiOriginalOmega` uses the full real source and full real
ℓᵖ root input, with every root in its assigned original disk before any
omitted index is chosen. This domain is open, including its infinite tail
placement condition.

Every matrix entry is real on real data, and every retained diagonal is
nonzero. The exact contour formulas use the literal double-omitted product.
The diagonal mean-value point belongs to the selected gap Gₘ, including
collapsed gaps. Analyticity is proved on a neighborhood of the closed
original disk, and root placement supplies every required separation.
The unused root fill does not change the actual derivative.

One neighborhood and constants K,C work for every omitted index n.
The diagonal is exactly 2+Rₘ+Sₘ, with |Rₘ|≤K/|n−m| and an actual ℓᵖ
sequence S of norm at most C; both errors vanish at the omitted coordinate.
A common ℓᵖ row majorant controls |m−r||Qₘᵣⁿ| for every n and column r.
The literal supremum over all off-diagonal columns and omitted equations
is itself an ℓᵖ sequence with the same local norm bound. All central rows
and columns are included, for every finite 1<p<∞.

Twenty focused public examples check the free matrix (diagonal 2 and
zero off-diagonal), negative and central indices, arbitrary unused-root
fills, deleted rows and columns, bounded differentiation without reality
or placement restrictions, original-domain openness and separation,
collapsed-gap evaluation, local uniformity, actual supremum sequences,
and exponents 3/2 and 4. A consequence verifies simultaneous vanishing
of every weighted off-diagonal row at infinity at a fixed point.
See the [Section 12 audit](SECTION_12.md).

Printed p. 66 names Gₙ in its final nonvanishing sentence; the required
interval is Gₘ. This index typo is recorded in [SOURCE_ERRATA.md](../SOURCE_ERRATA.md).
No additional mathematical assumption is imposed.

Next: Lemma 12.6 for this actual original-domain Jacobian: an invertible
diagonal plus a compact remainder. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (7,004 build jobs, the complete
public example suite, and the axiom audit of 32,972 NLS declarations).
The build retains 21 existing warnings. The eight new modules and twenty
new public checks are warning-free. The source inventory verified 156
candidate labels; all 100 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

| Assertion | Public API |
| --- | --- |
| Actual bounded derivative and directional entries | `SourceLemma12_4Data.originalRootJacobian_hasFDerivAt`, `.originalJacobianEntry_hasDerivAt` |
| Full original Ωᵖ is open | `SourceIsolatingNeighborhoods.isOpen_originalOmega` |
| Actual entries agree with original contour integrals | `SourceLemma12_4Data.originalJacobianEntry_contour`, `.originalJacobianEntry_diagonal_contour` |
| Literal ζ is analytic near the closed selected disk | `SourceCorollary10_6Data.originalZeta_analyticOnNhd` |
| Nonzero product on the selected gap | `SourceIsolatingNeighborhoods.originalZeta_ne_zero_on_gap` |
| Diagonal mean value and nonvanishing | `SourceLemma12_4Data.originalJacobianEntry_diagonal_meanValue`, `.originalJacobianEntry_diagonal_ne_zero` |
| Exact 2+R+S diagonal with uniform bounds | `SourceLemma12_4Data.originalJacobian_diagonal_decomposition` |
| Common off-diagonal row majorant | `SourceLemma12_4Data.originalJacobian_offDiagonal_commonMajorant` |
| Literal weighted row supremum in ℓᵖ | `SourceLemma12_4Data.originalJacobian_offDiagonal_rowSup` |
| Source statement on the retained W | `SourceLemma12_4Data.lemma12_5`, `sourceLemma12_5` |

The eight new modules are `SourcePsiOriginalJacobian`,
`SourcePsiOriginalOmega`, `SourcePsiOriginalJacobianContour`,
`SourcePsiOriginalZetaRegular`, `SourcePsiOriginalJacobianNonzero`,
`SourcePsiOriginalJacobianDiagonal`, `SourcePsiOriginalJacobianOffDiagonal`,
and `SourceLemma12_5`, under `NLS/ZakharovShabat/`.

## Lemma 12.6 on the original real domain

`SourceLemma12_5Data.lemma12_6` proves that the actual bounded root
Jacobian is a diagonal continuous linear equivalence plus a compact
operator at every original Ωᵖ point, for every finite 1<p<∞ and every
omitted index. The preceding open connected source domain W and all
Lemma 12.5 data are retained.

For each fixed omitted index n, the diagonal entries tend to 2 as
|m| tends to infinity. Their nonvanishing on the finite head gives a
positive lower bound on all retained entries. The diagonal inverse
is explicit coordinatewise multiplication by the reciprocal entries;
both inverse identities hold on the complex deleted Banach space.

The canonical off-diagonal remainder has an actual ℓᵖ row majorant,
obtained from the reciprocal matrix bounds and conjugate-exponent
Hölder duality. Its finite output cutoffs have finite-dimensional range
and converge in operator norm. The cutoff error is bounded by the
ℓᵖ tail of that majorant. All central rows and columns are included.


Eighteen new public checks cover signed diagonal limits, the finite-head
lower bound, reciprocal inverse formulas, both inverse identities,
compactness, finite-rank ranges and norm convergence, cutoff behavior at
and away from the omitted index, the unchanged source domain, original
Ωᵖ points, and exponents 3/2 and 4.

Next: Lemma 12.7, injectivity of this actual original-domain Jacobian.
The dissertation remains incomplete. No new source correction is needed
for Lemma 12.6.

Validation: `./scripts/check.sh` passed (7,008 build jobs, the complete
public example suite, and the axiom audit of 33,006 NLS declarations).
The build retains 21 existing warnings. The four new modules and eighteen
new public checks are warning-free. The source inventory verified 156
candidate labels; all 115 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

### Proof assertions and public API

| Source assertion (printed p. 66) | Lean implementation |
| --- | --- |
| Actual diagonal tends to 2 for fixed n | `SourcePsiOriginalJacobianBounds.diagonal_tail`, `.diagonal_tendsto_two` |
| Uniform positive lower bound on all retained diagonal entries | `.diagonal_lowerBound` |
| Actual Jacobian equals an invertible diagonal plus a compact operator | `.diagonal_plus_compact` |
| Bounded inverse with reciprocal coordinates | `.diagonal_plus_compact_with_inverse` |
| Hölder row estimate for the canonical remainder | `.offDiagonal_rowMajorant` |
| Finite-dimensional ranges and convergence in operator norm | `.offDiagonal_finiteRankApproximation` |
| Actual output cutoff and its tail error bound | `Coeff.deletedOutputCutoff`, `Coeff.norm_deletedOutputCutoff_sub_le` |
| Source statement on the retained W | `SourceLemma12_5Data.lemma12_6`, `sourceLemma12_6` |
| Finite-rank approximation at original Ωᵖ points | `SourceLemma12_6Data.finiteRankApproximation` |

Implementation: `SourcePsiOriginalJacobianDecomposition`,
`SourcePsiOriginalJacobianFiniteRank`, and `SourceLemma12_6`, under
`NLS/ZakharovShabat/`, together with
`NLS/SequenceSpaces/DeletedFiniteRankApproximation.lean`.

The diagonal limit is asserted for each fixed n, as in the source's
proof. No uniform-in-n diagonal limit or invertibility of the entire
Jacobian is asserted here; injectivity is the next lemma.

## Lemma 12.7 on the original real domain

`SourceLemma12_6Data.lemma12_7` proves injectivity of the actual bounded
root Jacobian at every original Ωᵖ point, for every finite 1<p<∞ and
every omitted index. It retains the same open connected source domain W,
the preceding diagonal-plus-compact decomposition, and all earlier data.
Injectivity holds on the complex deleted Banach space.

Every actual matrix row sums to the bounded derivative applied to an
arbitrary direction, and every coordinate equals the contour integral of
its entire numerator variation. For real kernel directions, the original
contours supply a zero in each retained gap, including collapsed gaps.
The selected zeros have ℓᵖ displacements and are distinct. Together with
the original omitted root they define a simple entire interpolation
product. Interpolation forces the variation to vanish identically;
evaluation at the distinct original roots then recovers the zero direction.
Real matrix entries reduce a complex kernel vector to its real and
imaginary parts, proving the full complex result.

The source's outer-circle proof assertions are also certified: all large
half-integer-radius circles avoid the entire original disk family; the
literal root product has its exact sine normalization and tends uniformly
to one; and φ=(σₙ−z)φₙ/2 satisfies φ/sin(z)→0 uniformly. The exact
root-resolvent/product factorization is retained. No selected local chart
or replacement disk family is imposed.

Twenty-two new public checks cover matrix row sums, arbitrary complex
directions, collapsed gaps, kernel splitting, injectivity, unused root
fills, simple interpolation zeros, original disk avoidance, literal
product identities and decay, the retained source domain and preceding
decomposition, and exponents 3/2 and 4.

Next: Corollary 12.8, invertibility of the actual Jacobian using the
Fredholm alternative. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (7,013 build jobs, the complete
public example suite, and the axiom audit of 33,040 NLS declarations).
The build retains 21 existing warnings. The five new modules and twenty-two
new public checks are warning-free. The source inventory verified 156
candidate labels; all 117 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

### Proof assertions and public API

| Source assertion (printed pp. 66–67) | Lean implementation |
| --- | --- |
| Matrix row sums to the actual bounded derivative | `hasSum_sourcePsiOriginalJacobianRow` |
| Arbitrary direction equals the variation contour | `SourceLemma12_4Data.originalRootJacobian_apply_variation_contour` |
| Kernel vector gives zero variation period | `.originalKernel_variation_contour_zero` |
| Real variation has a zero in every retained gap | `.originalRealKernel_gapZero` |
| Complex kernel splits into two real kernels | `.originalKernel_realImag` |
| Original roots are distinct | `SourceIsolatingNeighborhoods.originalRootPlacement_injective` |
| Gap zeros give a simple ℓᵖ interpolation product | `.originalGapInterpolationProduct` |
| All outer circles eventually avoid all original disks | `.eventually_centralCircle_avoids_originalDiscs` |
| Exact sine-normalized product | `sourcePsiCandidate_mul_omitted_div_sin` |
| Literal product tends uniformly to one | `eventually_centralCircle_sourcePsiRelativeProduct_close` |
| Exact root-resolvent/product formula | `sourcePsiVariation_div_sin_eq_resolvent_mul_product` |
| Literal φ/sin quotient tends uniformly to zero | `eventually_centralCircle_sourcePsiVariation_div_sin_small` |
| Entire variation vanishes | `SourceLemma12_4Data.originalRealKernel_variation_eq_zero` |
| Complex kernel is trivial; actual Jacobian is injective | `.originalKernel_eq_zero`, `.originalRootJacobian_injective` |
| Source statement on the retained W | `SourceLemma12_6Data.lemma12_7`, `sourceLemma12_7` |

Implementation: `SourcePsiOriginalKernelContour`,
`SourcePsiOriginalGapInterpolation`, `SourcePsiOriginalOuterCircles`,
`SourcePsiOriginalJacobianInjective`, and `SourceLemma12_7`, under
`NLS/ZakharovShabat/`.

The reality premise in the gap-zero argument is applied to real directions.
The complex statement follows by splitting the kernel using the already
proved real matrix entries. No extra hypothesis is imposed on a complex
kernel vector. Surjectivity is the next source statement, Corollary 12.8.

## Corollary 12.8 on the original real domain

`SourceLemma12_7Data.corollary12_8` proves that the actual root Jacobian
is a continuous linear isomorphism at every original Ωᵖ point, for every
finite 1<p<∞ and every omitted index. The Fredholm alternative combines
the preceding diagonal-plus-compact decomposition with injectivity. Both
the complex and real deleted Banach spaces have continuous inverses.
The same open connected source domain W and all preceding data are retained.

`RealDeletedCoeff` is the closed subspace of real ℓᵖ sequences whose omitted
coordinate is zero. Complex inclusion and real-part projection connect it
to the complex deleted space. Real matrix entries imply that the complex
inverse preserves real inputs, giving the real linear equivalence.
Its underlying operator is exactly the real Fréchet derivative of
`sourcePsiOriginalRealEquation` at the original root input. At real-type
sources this equation agrees, under inclusion, with the original equation.

Twenty-three new public checks cover both inverse identities on both
spaces, the actual real derivative, compatibility of the two inverses,
unique real preimages, nonreal right-hand sides, omitted and negative
indices, unused root fills, fixed-point inverse norm bounds, the unchanged
source domain, and exponents 3/2 and 4. The norm bounds here are for a fixed
source and omitted index; uniform inverse bounds are a later obligation.

Next: Proposition 12.9, the unique global real analytic solution map with
roots in the actual gaps. The dissertation remains incomplete. No new
source correction is needed for Corollary 12.8.

Validation: `./scripts/check.sh` passed (7,018 build jobs, the complete
public example suite, and the axiom audit of 33,111 NLS declarations).
The build retains 21 existing warnings. The five new modules and twenty-three
new public checks are warning-free. The source inventory verified 156
candidate labels; all 120 local Markdown links and diff checks passed.
No admitted proofs, additional axioms, or heartbeat overrides were added.

### Isomorphisms and exact derivative identification

| Source assertion (printed p. 67) | Lean implementation |
| --- | --- |
| Fredholm bijectivity at every original Ωᵖ point | `SourceLemma12_7Data.originalJacobian_bijective` |
| Continuous complex inverse of the actual Jacobian | `.originalJacobianEquiv`, `.originalJacobianEquiv_toCLM` |
| Complex inverse preserves real inputs | `.originalJacobianEquiv_symm_real` |
| Unique real solution for a real right-hand side | `.originalJacobian_real_existsUnique` |
| Continuous real inverse | `.originalJacobianRealEquiv` |
| Real and complex operators agree under inclusion | `.originalJacobianRealEquiv_complex` |
| Real operator is the actual real Fréchet derivative | `.originalJacobianRealEquiv_toCLM` |
| Fixed-source, fixed-index inverse norm bounds | `.originalJacobian_inverse_bound`, `.originalJacobianReal_inverse_bound` |
| Source corollary on the unchanged W | `.corollary12_8`, `sourceCorollary12_8` |

Implementation: `DeletedRealEquiv` and `DeletedRealInverse` in
`NLS/SequenceSpaces/`, and `SourcePsiOriginalRealEquation`,
`SourcePsiOriginalJacobianInverse`, and `SourceCorollary12_8` in
`NLS/ZakharovShabat/`.

The real equation takes real parts after complex inclusion. At every real-type
source in W, inclusion recovers the original complex equation exactly, by
`SourceLemma12_4Data.originalRealEquation_complex`. Its root derivative is
proved directly by the chain rule. Real coordinate deletion commutes with
complex inclusion, so the real equivalence acts at the same full root input
as the original complex Jacobian. No smaller source neighborhood, different
root-placement domain, or stronger summability exponent is introduced.

## Proposition 12.9 on the original real domain

`SourceCorollary12_8Data.proposition12_9` proves the unique global real
analytic solution map for the original psi equation, for every finite
1<p<∞ and every omitted index. Its values are actual real deleted ℓᵖ
vectors. Complex inclusion recovers the canonical gap-root map exactly.
The same open connected source domain W and all preceding data are retained.

The deleted placement domain is open and is exactly the projection of
original Ωᵖ under coordinate deletion. The solution graph lies in every
supplied original disk family over its real sources. Any real zero with
retained roots in those disks has its roots in the actual gaps, including
collapsed gaps, and equals the canonical solution. Uniqueness requires
no prior gap-placement assumption and holds across different disk families.

The earlier gap-solution construction supplies global existence,
continuation, and uniqueness. Exact original-circle coordinates now
transfer those results to the original equation and domain. The analytic
implicit theorem is also applied directly to the original complex
equation using Corollary 12.8's actual Jacobian. The real equation is
jointly analytic, and a local real branch through any placed zero stays
in the same original domain. Solutions converge in the full real ℓᵖ norm
along converging source sequences. At the free source the unique solution
has zero displacement.

Twenty-seven new public checks cover the actual equation and real codomain,
original-domain projection and graph lifting, uniqueness across disk
families, collapsed and free gaps, local real and complex analytic
branches, full sequence convergence, unchanged preceding data, and
exponents 3/2 and 4.

Next: Lemma 12.10, original-domain uniform inverse bounds and a common
complex extension for all omitted indices. The dissertation remains
incomplete. No new source correction is needed for Proposition 12.9.

Validation: the full build (7024 jobs), public example suite, and axiom
audit (33156 NLS declarations) pass. The six new modules and 27 new
checks are warning-free; the build reports 21 pre-existing warnings.
All 156 source inventory labels and 123 local Markdown links verify.

### Original domains, solution identity, and continuation

| Source assertion (printed p. 67) | Lean implementation |
| --- | --- |
| The original deleted placement domain | `sourcePsiOriginalDeletedOmega` |
| It is exactly the projection of Ωᵖ | `SourceIsolatingNeighborhoods.mem_originalDeletedOmega_iff` |
| It is open in the real product space | `.isOpen_originalDeletedOmega` |
| The real root map and exact complex inclusion | `sourcePsiOriginalRootReal`, `sourcePsiOriginalRootReal_complex` |
| Global real analyticity and the actual equation | `analyticOnNhd_sourcePsiOriginalRootReal`, `SourceLemma12_4Data.originalRootReal_solves` |
| Placed equation zeros have their roots in gaps | `.originalRealEquation_zero_mem_gap` |
| Original circles yield a valid gap solution | `.originalRealEquation_zero_gapSolution` |
| Pointwise uniqueness on any original disk family | `.originalRealEquation_zero_unique`, `.originalRealSolution_unique` |
| Unique global analytic solution | `.existsUnique_originalRealSolution` |
| Graph membership for every admissible original family | `SourceIsolatingNeighborhoods.originalRootReal_graph` |
| Direct analytic implicit theorem for the original equation | `SourceLemma12_7Data.originalEquation_local_analytic_branch` |
| Joint real analyticity and local real branches | `SourceLemma12_4Data.originalRealEquation_joint_analytic`, `.originalRealEquation_local_real_branch` |
| Full norm convergence along converging sources | `.originalRealSolution_tendsto` |
| Free normalization | `sourcePsiOriginalRootReal_zero` |
| Source package retaining Corollary 12.8 on W | `SourceCorollary12_8Data.proposition12_9`, `sourceProposition12_9` |

Implementation: `SourcePsiOriginalDeletedOmega`, `SourcePsiOriginalRealRoot`,
`SourcePsiOriginalSolutionGap`, `SourcePsiOriginalRealSolution`,
`SourcePsiOriginalImplicit`, and `SourceProposition12_9`, under
`NLS/ZakharovShabat/`.

The original-to-gap transfer uses the actual original equation as the
coordinate witness for the selected equation on the original circles.
This certifies each contour value before invoking the existing uniqueness
result. The earlier `SourcePsiGapGlobalExistence` and
`SourcePsiGapMultiplicity` prove global existence and uniqueness by
openness, compactness at convergent sources, and connectedness. Their
compactness input supplies convergence in ℓᵖ using uniform gap-root tail
bounds, strengthening the source's coordinatewise subsequence argument.
The resulting original solutions satisfy the full-sequence norm limit.

The source's domain Ω with the nth coordinate deleted is realized in
source-first order. An omitted root can be filled at the real center of
its original disk; its free location need not belong to that disk. The
canonical graph lies in every original family wherever that family is
admissible, and the same canonical solution works for all such families.

## Lemma 12.10, first proof steps: equations (2.28) and (2.29) on the original domain

The first operator-construction steps of Lemma 12.10 now hold on the
original isolating disks. Equation (2.28) uses the literal ratio
(nπ−mπ)/(σₙ−λ), with a uniform reciprocal-distance bound over every placed
complex root input and every point of the selected disk. At each fixed
row, one cutoff works in both index directions for all those inputs.

Actual original Jacobian entries converge to the literal Q* contour
entries. An eventual common operator bound makes these entries a bounded
operator, with coordinatewise convergence on every ℓᵖ input. Uniqueness
identifies one intrinsic Q*, independently of the original disk family
or circle. Its total definition's default branch is excluded throughout
the original placed-root domain at real-type sources. Roots may be
complex and need not lie in their spectral gaps for these results.

`sourceEquation2_29` retains Proposition 12.9 and its unchanged W. On every
original real Ωᵖ it proves the actual Q* diagonal is nonzero and equals
2 plus an ℓᵖ sequence, and its off-diagonal entries have one ℓᵖ row
majorant divided by index distance. Both sequence bounds are locally
bounded in the original parameters. The diagonal mean-value formula
uses an actual gap point and includes collapsed gaps. These estimates
make Q*−2I compact; bijectivity is reduced to a separate injectivity proof.

One joint root/source Lipschitz estimate controls every original full
Jacobian near a real-type source, with all omitted indices included.
Passing that estimate through coordinatewise limits proves operator-norm
continuity of Q* on the full original domain. On the smaller compact gap
product, Q* agrees with the prior bijective limit; the proved uniform
norm convergence and actual deleted inverse bounds transfer there.

Thirty new public checks cover complex root inputs, original circle and
family independence, the omitted diagonal convention, signed and central
indices, collapsed gaps, joint topology, compactness, the exact weighted
equation identity, and exponents 3/2 and 4. See the
[source coverage](../COVERAGE.md).

Lemma 12.10 remains incomplete. Next: full-domain operator-norm convergence,
Q* injectivity, and the original common complex extension. The printed
local-uniformity claim is also being audited. Gap-product norm convergence
and inverses are not asserted on the larger domain. No new source
correction is claimed in this milestone.

Validation: the full build passed (7033 jobs), the complete public example
suite passed, and the transitive axiom audit passed for 33238 NLS
declarations. The nine new modules and thirty new checks are warning-free;
the 21 existing warnings remain. The source inventory still verifies all
156 candidate labels, and all 134 checked local Markdown file links resolve.

| Module | Verified scope |
| --- | --- |
| [SourcePsiOriginalIndexRatio](../NLS/ZakharovShabat/SourcePsiOriginalIndexRatio.lean) | Literal (2.28), uniform all-disk bound and signed-index tail |
| [SourcePsiOriginalJacobianComparison](../NLS/ZakharovShabat/SourcePsiOriginalJacobianComparison.lean) | Exact original/selected equation and derivative identities; explicit gap-product bridges |
| [SourcePsiOriginalJacobianScalarLimit](../NLS/ZakharovShabat/SourcePsiOriginalJacobianScalarLimit.lean) | Actual scalar Jacobian limits for all original placed roots |
| [SourcePsiOriginalLimitOperator](../NLS/ZakharovShabat/SourcePsiOriginalLimitOperator.lean) | Bounded Q* construction and convergence on every input coordinate |
| [SourcePsiOriginalLimitCanonical](../NLS/ZakharovShabat/SourcePsiOriginalLimitCanonical.lean) | Intrinsic choice, uniqueness, every-circle formula, and gap-limit agreement |
| [SourcePsiOriginalLimitContinuity](../NLS/ZakharovShabat/SourcePsiOriginalLimitContinuity.lean) | Common joint Lipschitz control and continuity on the full original domain |
| [SourcePsiOriginalLimitEntries](../NLS/ZakharovShabat/SourcePsiOriginalLimitEntries.lean) | Twice-period formula, exact weighted original equation identity, off-diagonal lp majorant |
| [SourcePsiOriginalLimitDiagonal](../NLS/ZakharovShabat/SourcePsiOriginalLimitDiagonal.lean) | Nonzero diagonal, actual-gap mean value, locally bounded lp correction |
| [SourceEquation2_29](../NLS/ZakharovShabat/SourceEquation2_29.lean) | Original real-domain package, compact correction, Fredholm reduction, and retained Proposition 12.9 |

## Lemma 12.10: norm convergence and its uniformity quantifiers

The full original Jacobians now converge in operator norm to the intrinsic
Q* at every fixed real placed-root input, for every finite 1<p<∞ and as
the omitted index escapes in either direction. Roots need not lie in
their spectral gaps. The existing diagonal proof is generalized to
arbitrary real root inputs; its former gap-domain API remains available.
A single fixed ℓᵖ majorant controls all off-diagonal matrices and gives
uniform finite-block approximation. The off-diagonal norm limit even
allows complex placed-root inputs.

`sourceLemma12_10_normLimit` retains Proposition 12.9 and its unchanged
open connected W. Convergence on each original real Ωᵖ is locally
uniform in mathlib's sense: for each error tolerance and each base point,
one neighborhood and one index cutoff work for every input there.
Consequently convergence is uniform on every compact subset of Ωᵖ,
with both roots and sources allowed to vary.

A verified free-source counterexample resolves the stronger interpretation
of printed p. 69. For a real displacement δ at the omitted index n,
the adjacent diagonal of Qⁿ−Q* is exactly 2δ/π. Fixed small spikes can
move arbitrarily far out while staying in any given ball inside Ωᵖ.
Thus no fixed neighborhood of the free point supports uniform norm
convergence. This does not contradict the tolerance-dependent local
uniformity proved above. The counterexample includes existence of an
original isolating family and uses the actual original operators.
See [the source clarification](../SOURCE_ERRATA.md).

Seventeen public checks cover unrestricted real diagonal inputs, complex
off-diagonal inputs, full-domain norm convergence, signed-index cutoffs,
strong convergence on every input vector, joint local and compact-set
uniformity, the actual free-spike identity and lower bound, failure on
all fixed neighborhoods, and exponents 3/2 and 4.

Lemma 12.10 remains incomplete: full original-domain Q* injectivity and
the common original complex extension are next. The printed source-only
Lipschitz bound remains under audit; the proved bound controls both roots
and source parameters.

Validation: the full build passed 7037 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33286 NLS
declarations. The four new modules, two generalized modules, and seventeen
new checks are warning-free; the 21 existing warnings remain. The source
inventory verifies all 156 candidate labels, and all 145 checked local
Markdown file links resolve.

| Module | Verified scope |
| --- | --- |
| [ReciprocalMatrixConvergence](../NLS/SequenceSpaces/ReciprocalMatrixConvergence.lean) | Fixed reciprocal majorant and coordinatewise limits imply off-diagonal norm convergence |
| [SourcePsiJacobianEscapingDiagonalTail](../NLS/ZakharovShabat/SourcePsiJacobianEscapingDiagonalTail.lean) | Scalar diagonal tail for arbitrary real root inputs |
| [SourcePsiJacobianDiagonalNormLimit](../NLS/ZakharovShabat/SourcePsiJacobianDiagonalNormLimit.lean) | Uniform diagonal tail with reality alone; previous gap-domain APIs retained |
| [SourcePsiOriginalNormLimit](../NLS/ZakharovShabat/SourcePsiOriginalNormLimit.lean) | Actual full-domain pointwise operator-norm limit |
| [SourcePsiOriginalNormUniformity](../NLS/ZakharovShabat/SourcePsiOriginalNormUniformity.lean) | Tolerance-dependent local uniformity and uniformity on all compact subsets of original Ωᵖ |
| [SourcePsiOriginalUniformityCounterexample](../NLS/ZakharovShabat/SourcePsiOriginalUniformityCounterexample.lean) | Moving real spikes disprove convergence uniformly on a fixed original neighborhood |

## Lemma 12.10: full original-domain invertibility and complex inverse bounds

The intrinsic Q* is now bijective throughout the original real Ωᵖ for
every finite 1<p<∞. Its actual original contour action turns a real
kernel direction into a full product variation with a zero in every
spectral gap. Entire-function uniqueness, original-disk separation,
and reality of the matrix give complex injectivity; the Fredholm
alternative gives surjectivity. The input roots need only be real and
lie in the original disks.

The full original inverses converge in operator norm to (Q*)⁻¹ as the
omitted index escapes in either direction. One bound controls every
signed index at each base point, including the genuine deleted-space
inverse from Corollary 12.8.

Direct use of Lemma 12.4 gives one joint complex equation bound at all
deleted centers. Coordinate decay handles the tail and finitely many
local bounds handle the remaining indices. Cauchy's estimate gives a
common Lipschitz bound in both roots and sources. The Neumann estimate
then supplies actual two-sided inverses on one joint complex ball,
with radius and norm bound independent of the deleted index. This is
proved for both the full operators and the actual deleted Banach spaces.
An open neighborhood can also be kept inside the original source
neighborhoods and every original isolating disk.

`sourceLemma12_10_inverseBounds` packages the limit's bijectivity and
the common deleted-space complex inverse bounds, retaining Proposition
12.9 and the unchanged open connected W. Eighteen public checks cover
complex kernel directions, unique inhomogeneous solutions, signed-index
inverse limits, the actual Corollary 12.8 inverse, unrestricted complex
chart inputs, preservation of original domains, solution norm bounds,
and exponents 3/2 and 4.

Lemma 12.10 remains incomplete: the common analytic solution extension
must still be connected to the original isolating disks and global
domain requirements. The printed source-only Lipschitz estimate remains
under audit; the proved complex estimate controls both roots and sources.

Validation: the full build passed 7043 jobs, the complete public example
suite passed, and the transitive axiom audit passed for 33317 NLS
declarations. The six new modules and eighteen new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, and all 151 checked local Markdown file links resolve.

| Module | Verified scope |
| --- | --- |
| [DeletedOperatorNormDifference](../NLS/SequenceSpaces/DeletedOperatorNormDifference.lean) | Full block extension contracts operator differences |
| [SourcePsiOriginalLimitInjectivity](../NLS/ZakharovShabat/SourcePsiOriginalLimitInjectivity.lean) | Full original-domain Q* kernel triviality and bijectivity |
| [SourcePsiOriginalInverseLimit](../NLS/ZakharovShabat/SourcePsiOriginalInverseLimit.lean) | Norm convergence and all-index bounds for actual inverses |
| [SourcePsiOriginalComplexJacobianCharts](../NLS/ZakharovShabat/SourcePsiOriginalComplexJacobianCharts.lean) | Common complex equation and Jacobian bounds from Lemma 12.4 |
| [SourcePsiOriginalComplexInverseBounds](../NLS/ZakharovShabat/SourcePsiOriginalComplexInverseBounds.lean) | Full and deleted complex inverse balls, preserving original disks |
| [SourceLemma12_10InverseBounds](../NLS/ZakharovShabat/SourceLemma12_10InverseBounds.lean) | Inverse-bound package retaining Proposition 12.9 and unchanged W |
