# Section 14 original Birkhoff map audit

Source: printed pp. 73–75 of the dissertation, equation (3.1), Theorem
14.1, Remark 14.2, and the meaning of canonical in Lemma 15.3. This audit
retains the original Lemma 12.12 root family and Section 13 integral-defined
angles. It does not certify all of Chapter 3 or its cited external results.
The current `sourceSection14` construction establishes all five assertions
of Theorem 14.1 on compatible complex neighborhoods. In the table below,
D denotes `SourceSection14Data`; the original-family formulas and real
geometry are inherited through `D.toSourceSection14OriginalData`.

| Source assertion | Public evidence | Scope and remaining work |
| --- | --- | --- |
| Equation (3.1) on open gaps | `SourceSection14OriginalData.rectangular_formula` | Exact cosine/sine formula for the full sequence coordinates and the original theta; positive sine orientation |
| Extension through collapsed gaps | `gapWeightedEta_original_analytic`, `exists_original_birkhoff_coordinate_domain` | Analytic at complex collapsed gaps; both coordinates vanish at real collapsed gaps |
| Theorem 14.1(i): analytic sequence map | `sourceSection14`, `D.complex.analytic`, `D.complex.coordinates` | Complex analytic ℓᵖ × ℓᵖ map on one open neighborhood of the entire real locus, constructed for every finite p>1; actual coordinate evaluations are proved |
| Theorem 14.1(ii): exponent compatibility | `SourceSection14Data.exponent` | Full sequence equality on the entire complex intersection after exponent inclusion; arbitrary complex sources and collapsed gaps included |
| Theorem 14.1(iii): canonical | `D.toSourceSection14OriginalData.canonical`, `D.complex.mixed_fourier_canonical` | All three brackets on the real locus, as in Lemma 15.3; actual coordinate derivatives and absolutely convergent Fourier pairings, including p<2 |
| Theorem 14.1(iv): injective, local diffeomorphism, open dense image | `D.toSourceSection14OriginalData.real_geometry` | Actual real map; analytic local inverse at every point with both inverse identities |
| Theorem 14.1(v): onto for 1<p≤2 | `D.toSourceSection14OriginalData.global_inverse` | Homeomorphism equal to the actual real map; forward and inverse maps analytic on their entire spaces |
| Remark 14.2(i): agreement with the external Hilbert-space map | Existing historical Hilbert compatibility interfaces | Identification with the precise external construction in [23] is not separately certified by this audit |
| Remark 14.2(ii): p>2 surjectivity | No such claim | The source states this as an open question |
| Remark 14.2(iii): positive smoothness | Existing later Sobolev interfaces | A full fractional Fourier–Lebesgue comparison is outside this milestone |

## Original definitions and exact phase

The new endpoint-remainder theorem identifies every admissible improper
eta remainder with `sourceAngularEtaRemainder` itself. At periodic terminals
it is zero. The model's left-endpoint normalization then proves
`gapWeightedEta_original_plus`; the exact product identity supplies the
negative sign in `gapWeightedEta_original_signed`.

This step matters because equality of exp(2i eta) alone would leave the
sign of exp(i eta) unresolved. The resulting weighted coordinates use
`sourceAngularOriginalTheta`, the literal eta integral plus the beta series.
Its 2π ambiguity leaves both rectangular coordinates unchanged.
The opening exponential display in Section 15 prints a plus for y where
its sine formula requires a minus. The Lean definition uses the difference;
this visually verified discrepancy is recorded in `SOURCE_ERRATA.md`.

## Domains, actions, and sequence membership

`exists_original_birkhoff_coordinate_domain` intersects the original W
with the normalized-action neighborhood furnished by its retained Section
11 data. It preserves the root family s and proves the exact identity
xₙ²+yₙ² = 2 `sourceIndexedAction` at every complex source in that domain.
No open-gap assumption is used for this identity.

`exists_original_birkhoff_map` combines uniform bounds for all indices
with these analytic coordinates, and takes a union of neighborhoods of
real sources. The resulting V is open, contains the whole real locus,
and lies in W. Its `SourceBirkhoffMapComplexData` proves full sequence
analyticity and actual scalar evaluations. Sequence membership, local
bounds, and invertibility are proved, not requested as extra hypotheses
from the caller of `sourceSection14_original`.

The canonical and real inverse proofs already in the library therefore
apply to this original family. Their reuse is explicit in
`SourceSection14OriginalData`; the construction does not replace s with a
separately chosen family to obtain the inverse properties.

## Full complex exponent intersections

`sourceRealBallCore` takes the union of all balls centered at real sources
and contained in an existing domain. This operation produces an open
subset, preserves the whole real locus of an open neighborhood, and is
idempotent. `sourceSection14` restricts the preceding original-family
package to this domain without changing its root family or map functions.

`map_exponent_on_realBallCore` compares two independently chosen original
packages at exponents p≤q. For a point in the intersection, select one
ball in each domain. The first ball intersected with the inclusion
preimage of the second is convex. It contains both the given point and
its real-type projection: projection contracts distance from real centers
and commutes with exponent inclusion. The full sequence maps have equal
complex germs at that real projection, so the analytic identity principle
identifies them throughout the convex overlap.

The public `SourceSection14Data.exponent` applies this proof throughout
the entire complex intersection of the constructed domains. It requires
no real-type, open-gap, common-root-family, or connected-intersection
hypothesis. `eventually_map_exponent` then gives one common germ for the
entire sequence at every complex overlap point, and `fderiv_exponent`
identifies the full complex Fréchet derivatives after both inclusions.

## Current validation and next step

Twelve new checks exercise the domain restriction, projection compatibility,
full complex intersections, sequence germs, complex derivatives,
independence of families at a fixed exponent, original formulas and action
radii, and retained real inverses. Independent constructions at p=3/2 and
p=4 agree throughout their complex intersection. The p=3/2 construction
retains both global inverse identities on the entire real target.

Validation: `./scripts/check.sh` passes: the full build completes 7,108
jobs, all public examples pass, and the transitive axiom audit checks 33,710
NLS declarations. The three new modules and twelve new checks introduce
no warnings; the 21 existing warnings remain. The source inventory
verifies all 156 candidate labels, all 223 checked local Markdown file
links resolve, and `git diff --check` passes.

The detailed source audits of Sections 15–17 are next. The qualifications
for the external-map and positive-smoothness remarks in the table remain.

## Previous validation: original map and real geometry

Thirteen public checks exercise the exact signed phase, equation (3.1),
complex sequence analyticity and evaluations, indexed-action radii, real
closed-gap zeros, the actual real restriction, canonical derivatives and
their Fourier sum, real geometry, and real exponent compatibility.
Unconditional constructions at p=4 and p=3/2 check the claimed exponent
ranges, including both global inverse identities at p=3/2.

Validation: `./scripts/check.sh` passes: the full build completes 7,105
jobs, all public examples pass, and the transitive axiom audit checks 33,689
NLS declarations. The six new modules and thirteen new checks introduce
no warnings; the 21 existing warnings remain. The source inventory
verifies all 156 candidate labels, all 220 checked local Markdown file
links resolve, and `git diff --check` passes.

## Modules

- [Improper eta remainder value](../NLS/ZakharovShabat/SourceAngularOriginalEtaRemainderValue.lean)
- [Exact original signed eta phases](../NLS/ZakharovShabat/SourceGapWeightedEtaOriginal.lean)
- [Original rectangular formula](../NLS/ZakharovShabat/SourceBirkhoffOriginalFormula.lean)
- [Original coordinate domain and action radius](../NLS/ZakharovShabat/SourceBirkhoffOriginalDomain.lean)
- [Original analytic sequence map](../NLS/ZakharovShabat/SourceBirkhoffOriginalMap.lean)
- [Section 14 original-family interface](../NLS/ZakharovShabat/SourceSection14Original.lean)
- [Real-centered ball domains](../NLS/ZakharovShabat/SourceRealBallCore.lean)
- [Original maps on complex intersections](../NLS/ZakharovShabat/SourceBirkhoffOriginalExponent.lean)
- [Compatible Section 14 construction](../NLS/ZakharovShabat/SourceSection14.lean)
