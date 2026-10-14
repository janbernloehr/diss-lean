# Section 12: psi-functions

This audit begins with printed p. 63 of the dissertation. Theorem 12.1,
including the entire product (2.20) and the normalized periods (2.21), is
proved on one common neighborhood inside the original Section 11 source
domain. The scalar formulation (2.22)–(2.23) and the zero-contour implication for
local numerators on filled original disks are now proved. The complete
arbitrary-neighborhood and complex-gap assertions in Lemmas 12.2–12.3
remain the next audit.
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
