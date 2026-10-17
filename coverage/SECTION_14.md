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
| Remark 14.2(iii): positive smoothness | `sourceSection14_sobolev_characterization`, `sourceSection14_sobolev_open_dense`, `sourceSection14_sobolev_continuous_bijective` | Exact original source/gap/output regularity at every real t>=0; continuous injection with open dense image for every finite p>1, bijective for 1<p<=2. Both weighted inverse identities and inverse exponent compatibility hold. Weighted complex analyticity and compatibility, canonicality, analytic local inverses, and weighted inverse continuity and analyticity remain. |

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

## Weighted extension: membership and original coefficients

[`SourceBirkhoffWeightedMembership.lean`](../NLS/ZakharovShabat/SourceBirkhoffWeightedMembership.lean)
proves full weighted summability of the actual periodic gaps, adding the
finite central set to the existing tail estimate. On real sources, the
original identity x_n^2+y_n^2=2 I_n and a uniform-in-index normalized-action
root bound give one constant times the gap length for each coordinate.
Thus both original real coordinate sequences retain the source weight.
This works for every finite p>1 and every Section 6 spectral weight.

[`SourceWeightedRealSpaces.lean`](../NLS/ZakharovShabat/SourceWeightedRealSpaces.lean)
defines the closed real subspace of original weighted coefficient pairs,
with the raw relation a_2(n)=conj(a_1(-n)). Its real coordinate equivalence
preserves the weighted pair norm, proves completeness, and has both
inverse identities. Including the weighted source into the unweighted
source preserves every raw Fourier coefficient.

[`SourceBirkhoffWeightedMap.lean`](../NLS/ZakharovShabat/SourceBirkhoffWeightedMap.lean)
first expresses the weighted output in normalized lp coordinates.
[`SourceBirkhoffOriginalWeightedMap.lean`](../NLS/ZakharovShabat/SourceBirkhoffOriginalWeightedMap.lean)
then gives a map between the original weighted source and target spaces.
Its raw output is exactly the existing original real Birkhoff map, with
both coordinate identities proved. Positive weighting and the original
injectivity imply injectivity in the weighted spaces. The target's p-th
norm power equals the sum of the p-th powers of both weighted coordinate
magnitudes, with no change from the source's component-sum convention.

[`SourceSection14WeightedMembership.lean`](../NLS/ZakharovShabat/SourceSection14WeightedMembership.lean)
obtains an actual `SourceSection14Data` package from `sourceSection14` and
proves that this single construction works for every spectral weight.
Its half-scale spectral weight w(k)=(1+|k|/2)^s gives exactly the original
period-one weight w(2n)=(1+|n|)^s. All nonnegative real s are included, so
the result covers fractional positive smoothness and the zero endpoint.

This establishes weighted membership and injectivity for the original
map. The following extension adds continuity and Sobolev dense image.
A pointwise real gap bound alone does not prove analyticity in the stronger
norm. Surjectivity for p>2 remains the separate open question recorded by
the source.

Twenty-four new checks cover p=3/2 and p=4, fractional s=1/3, zero regularity,
negative frequencies, exact raw input and output coefficients, real-space
completeness and inverse coordinate identities, injectivity, and exact
weighted norm identities. The p=3/2 and p=4 constructions are obtained
without assuming a Section 14 package. The current full-gate result is
recorded in [STATUS.md](../STATUS.md).

## Weighted continuity and Sobolev dense image

[`SourceWeightedGapSequence.lean`](../NLS/ZakharovShabat/SourceWeightedGapSequence.lean)
constructs the full actual weighted gap sequence for compatible continuous
complex linear source maps. The corrected gap budget becomes uniformly
small on one weighted complex neighborhood. Adding a fixed finite head
gives a uniform lp norm bound; choosing cutoff M+1 matches the complement
of the finite interval [-M,M] and proves small tails for all later cutoffs.
No continuity of a complex ordered endpoint choice is assumed.

The normalized-action bound and factor identity hold on a common
neighborhood. The existing real action-radius argument therefore yields
one constant for all nearby real sources and all coordinate indices.
[`LocallyDominatedContinuity.lean`](../NLS/SequenceSpaces/LocallyDominatedContinuity.lean)
transfers uniform tails through this coordinate bound. Together with
continuity of the original scalar coordinates, this proves norm continuity
of the entire weighted real map. The majorizing sequence need not itself
be continuous.

[`SourceBirkhoffWeightedContinuity.lean`](../NLS/ZakharovShabat/SourceBirkhoffWeightedContinuity.lean)
proves continuity both in normalized coordinates and on the actual
original weighted source and target. One unconditional `sourceSection14`
construction gives continuous injections for every Section 6 spectral
weight. This is continuity in the stronger weighted norms.

[`SourceBirkhoffSobolevDenseRange.lean`](../NLS/ZakharovShabat/SourceBirkhoffSobolevDenseRange.lean)
proves dense image for every nonnegative real Sobolev order at every finite
p>1. The unweighted map already attains each finite target truncation.
Its preimage is spectrally finite-gap, so the original Fourier coefficients
have every Sobolev order at that same p. The resulting weighted source
lift preserves all raw coefficients. Dividing the finite target values
by their positive weights, taking this preimage, and restoring the weights
attains every finite normalized weighted target. Truncations converge in
the weighted target norm, and the target coordinate homeomorphism gives
density for the actual original map.

The finite-gap argument establishes Sobolev density, not density for
arbitrary spectral weights such as exponential weights. Dense image does
not establish open image or surjectivity. The remaining Remark 14.2(iii)
requirements are weighted complex analyticity and complex exponent compatibility,
canonicality, open image and local inverse, and the global inverse for
1<p<=2. The complex-coordinate argument still needs a weighted estimate
of the actual Dirichlet-minus-periodic-midpoint displacement; the weighted
gap bound alone does not supply it.

Twenty-two public checks exercise fractional p=3/2, p=4, s=1/3 and s=0;
negative indices; complex weighted gap bounds and tails; exact real target
coordinate inverses; continuity in the weighted norms; finite-gap lifts
and finite target attainment; unconditional continuous dense injections;
and approximation of arbitrary original weighted targets. The full gate
result is recorded in [STATUS.md](../STATUS.md).

## Weighted real exponents and gap characterization

[`WeightedRealExponent.lean`](../NLS/SequenceSpaces/WeightedRealExponent.lean)
and [`SourceWeightedRealExponent.lean`](../NLS/ZakharovShabat/SourceWeightedRealExponent.lean)
construct continuous real linear inclusions in the original weighted spaces.
They preserve raw coefficients, the source conjugate-reflection relation,
and the target reality condition. Injectivity, reflexivity and composition
are proved; the single-coordinate-space inclusion is contractive. The pair
maps use the respective WithLp p and WithLp q topologies.

[`SourceBirkhoffWeightedExponent.lean`](../NLS/ZakharovShabat/SourceBirkhoffWeightedExponent.lean)
proves the exact commuting identity for the full original weighted real
Birkhoff map. It applies for every spectral weight and finite 1<p<=q,
with independent normalized families at the two exponents. The public
`sourceSection14_weighted_real_compatible` obtains both packages from
`sourceSection14`, with no map-existence or compatibility premise. At equal
exponents this also gives independence of the original weighted real map
from the selected family. Weighted complex-domain compatibility still
requires constructing the weighted complex map.

[`SourceBirkhoffGapNormEquivalence.lean`](../NLS/ZakharovShabat/SourceBirkhoffGapNormEquivalence.lean)
uses the locally uniform positive real part of four times the normalized
action, exact action factorization, and x_n^2+y_n^2=2 I_n. It proves one
positive lower bound for the squared coordinate radius relative to the
squared gap at every nearby real source and every signed index. Taking
square roots gives gap <= A (abs(x_n)+abs(y_n)) on the same neighborhood,
including collapsed gaps. Combining this with the existing forward bound
proves `weighted_gap_mem_iff_real_map_mem` for every positive `Weight`.
No monotonicity, symmetry or submultiplicativity of that weight is needed.
The construction `sourceSection14_weighted_gap_characterization` makes
the result unconditional for the original Section 14 map.

This is equivalence between weighted spectral gaps and Birkhoff outputs.
It does not establish the converse from weighted gaps to weighted Fourier
coefficients of the source, nor weighted surjectivity or an inverse. The
23 public checks include p=3/2 to p=4, infinite-exponent sequence inclusions,
negative and zero indices, fractional Sobolev orders, decreasing positive
weights, both membership implications, and independent actual constructions.
Validation is recorded in [the current implementation status](../STATUS.md).

## Actual gap forcing and weighted source regularity

The source-regularity route now includes quantitative estimates for nonzero
gaps. The following modules prove intermediate statements used by the
weighted extension; they do not yet prove its full inverse assertion.

| Module | Proved result |
| --- | --- |
| [Real diagonal-center estimate](../NLS/ZakharovShabat/ResonantRealGapCenter.lean) | Analytic diagonal and off-diagonal bounds, two real counted roots, and the actual diagonal fixed point imply both center coefficients have norm at most twice the root gap. |
| [Actual source center bound](../NLS/ZakharovShabat/SourceResonantCenterGapBound.lean) | Actual canonical counted endpoints discharge the root hypotheses uniformly for nearby real sources, including repeated roots. |
| [Weighted adapted membership](../NLS/ZakharovShabat/SourceAdaptedGapWeightedMembership.lean) | Weighted gaps or weighted real Birkhoff outputs imply weighted adapted coordinates for every positive even weight, with one cutoff before choosing the weight. |
| [Weighted center transfer](../NLS/ZakharovShabat/SourceWeightedCenterGapBound.lean) | Every compatible weighted realization has the same actual centers and inherits the factor-two bound. |
| [Forced quadratic summability](../NLS/SequenceSpaces/ForcedQuadraticTailSummability.lean) | A vanishing nonnegative tail inherits exactly the geometric summability of its forcing; the quadratic coefficient may be any real number. |
| [Actual forced Fourier tails](../NLS/ZakharovShabat/SourceGapWeightedTail.lean) | Explicit recurrence with actual weighted gap forcing, followed by geometric summability transfer below the algebraic remainder rate. |

Let P=||psi||, C_p=2^p, alpha=min(1,p-1), and C be
`offDiagonalSummationConstant p`. Let v(N) be the p-power of the actual
weighted Fourier tail at physical cutoff 2N and G(N) be
`sourceWeightedGapPowerTail` at source cutoff N, weighted by w(2n).
For all sufficiently large N, the proved recurrence is

```
v(4N) <= C_p * (2*C_p*G(4N) + C*P^p*(P^(2p)/(4N)^alpha + v(N)^2)).
```

For one M>=2, every r>0 with r*4^(-alpha)<1 transfers summability of
r^k G(4^(k+1)M) to summability of r^k v(4^k M). This conclusion is at
the same rate r, and the polynomial forcing has already been discharged.
The source is only assumed to have the displayed weighted realization;
it need not be finite-gap. The adapted-coordinate result needs no initial
weighted realization, but it concerns the adapted map rather than the
original Fourier coefficients.

Still to prove: the exact Sobolev coefficient/tail summability bridge,
iteration of positive regularity gains for arbitrary gaps, and the full
weighted inverse assertions. The 16 public checks exercise fractional
and Hilbert exponents, negative frequencies, collapsed gaps, arbitrary
real Sobolev orders for adapted coordinates, and exact-rate summability.
Validation is recorded in [the implementation status](../STATUS.md).

## Exact Sobolev regularity and original weighted range

The converse regularity statement is now proved for the actual original
real source at every finite p>1 and every real t>=0. It is combined with
the forward gap estimate and the original Birkhoff gap characterization:

```
source Fourier components in lp_t
  iff actual periodic gaps in lp_t
  iff both original real Birkhoff coordinates in lp_t.
```

No finite-gap hypothesis or prior positive source order is required.
For positive t, a nonnegative summable sequence has a finite t-weighted
coefficient sum exactly when its tails at 4^k M are summable with weight
4^(t k). The forced recurrence transfers that exact summability. The proof
then chooses a finite K and delta=t/K below the one-step threshold and
iterates only up to K, reaching t without assuming gap regularity above t.
The zero-order case uses original lp membership directly.

| Module | Public evidence |
| --- | --- |
| [Exact summable tails](../NLS/SequenceSpaces/SummableGeometricTails.lean) | Both coefficient/tail implications and the lp Fourier-tail bridge at the same requested order. |
| [Weighted real inclusion](../NLS/SequenceSpaces/WeightedRealInclusion.lean) | Continuous, injective forgetting of weights bounded below by one; exact raw real coefficients, including the infinite Banach exponent. |
| [Physical weighted gain](../NLS/ZakharovShabat/SourceGapWeightedRegularity.lean) | The actual gap forcing gives a further Sobolev weight on any available weighted realization. |
| [Original source converse](../NLS/ZakharovShabat/SourceSobolevGapRegularity.lean) | Half-scale weights, exact original coefficient recovery, finite iteration, and the full nonnegative-order converse. |
| [Native weighted membership](../NLS/ZakharovShabat/SourceWeightedRealMembership.lean) | Original weighted representatives iff raw membership; continuous target inclusion preserving every coefficient. |
| [Source/gap/output equivalence](../NLS/ZakharovShabat/SourceBirkhoffSobolevRegularity.lean) | Exact Sobolev equivalences and one actual Section 14 construction for all nonnegative real orders. |
| [Original weighted range](../NLS/ZakharovShabat/SourceBirkhoffSobolevRange.lean) | Exact range equality, open dense image, surjectivity for 1<p<=2, native bijections, both inverse identities, and inverse compatibility across exponents. |

Let J_t denote `originalWeightedRealTarget` and F_t the original weighted
real Birkhoff map, with F the original unweighted map.
`originalWeightedRealMap_sobolev_range` proves
`range F_t = J_t ⁻¹' range F`. The forward implication is the exact
coefficient compatibility diagram. Conversely, every unweighted preimage
of a weighted target has the required source Sobolev regularity and thus
a native weighted representative. Since J_t is continuous and the
unweighted range is open, the weighted range is open. Existing density
holds in the weighted target norm.

For 1<p<=2, unweighted surjectivity makes the weighted range the whole
target. `originalWeightedRealSobolevEquiv` packages the original map as a
bijection of the native weighted spaces. Its inverse has both identities,
agrees with the original unweighted inverse after inclusion, and commutes
with p<=q<=2 inclusions even for independently constructed families.
No continuity or analyticity of this inverse in the stronger topology is
asserted. Open range alone does not prove that the map is open on every
open subset or is a local homeomorphism.

Remaining clauses: weighted complex analyticity and complex compatibility,
weighted canonicality, analytic local inverses, and weighted inverse
continuity and analyticity. The actual complex Dirichlet-minus-periodic-
midpoint estimate remains missing. Surjectivity at p>2 is still the source's
open question. The 28 public checks include p=3/2 at the one-step threshold,
p=4 at order 7/3, zero order, both inverse identities, and actual Section
14 constructions. Validation is recorded in [the implementation status](../STATUS.md).

## Previous validation: complex exponent compatibility

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

The separate source audits of Sections 15–17 are recorded in their audit
files. The external-map qualification and the remaining weighted-extension
requirements are listed above.

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
