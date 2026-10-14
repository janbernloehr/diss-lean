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
Lemma 12.4's proof are now also certified.
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
