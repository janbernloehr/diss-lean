# Section 14 original Birkhoff map audit

Source: printed pp. 73–75 of the dissertation, equation (3.1), Theorem
14.1, Remark 14.2, and the meaning of canonical in Lemma 15.3. This audit
retains the original Lemma 12.12 root family and Section 13 integral-defined
angles. It does not certify all of Chapter 3 or its cited external results.
The current `sourceSection14` construction establishes all five assertions
of Theorem 14.1 on compatible complex neighborhoods. In the table below,
D denotes `SourceSection14Data`; the original-family formulas and real
geometry are inherited through `D.toSourceSection14OriginalData`.

The detailed sections also preserve earlier proof milestones. Their
then-open inverse and compatibility tasks are superseded by the current
table and the later completion sections. The later terminal-coordinate
construction also proves local complex weighted bounds for the actual
Dirichlet-minus-periodic-midpoint displacement, as recorded below. The exact
2014 edition comparison remains unverified.

| Source assertion | Public evidence | Scope and remaining work |
| --- | --- | --- |
| Equation (3.1) on open gaps | `SourceSection14OriginalData.rectangular_formula` | Exact cosine/sine formula for the full sequence coordinates and the original theta; positive sine orientation |
| Extension through collapsed gaps | `gapWeightedEta_original_analytic`, `exists_original_birkhoff_coordinate_domain` | Analytic at complex collapsed gaps; both coordinates vanish at real collapsed gaps |
| Theorem 14.1(i): analytic sequence map | `sourceSection14`, `D.complex.analytic`, `D.complex.coordinates` | Complex analytic ℓᵖ × ℓᵖ map on one open neighborhood of the entire real locus, constructed for every finite p>1; actual coordinate evaluations are proved |
| Theorem 14.1(ii): exponent compatibility | `SourceSection14Data.exponent` | Full sequence equality on the entire complex intersection after exponent inclusion; arbitrary complex sources and collapsed gaps included |
| Theorem 14.1(iii): canonical | `D.toSourceSection14OriginalData.canonical`, `D.complex.mixed_fourier_canonical` | All three brackets on the real locus, as in Lemma 15.3; actual coordinate derivatives and absolutely convergent Fourier pairings, including p<2 |
| Theorem 14.1(iv): injective, local diffeomorphism, open dense image | `D.toSourceSection14OriginalData.real_geometry` | Actual real map; analytic local inverse at every point with both inverse identities |
| Theorem 14.1(v): onto for 1<p≤2 | `D.toSourceSection14OriginalData.global_inverse` | Homeomorphism equal to the actual real map; forward and inverse maps analytic on their entire spaces |
| Remark 14.2(i): agreement with the external Hilbert-space map | `sourceSection14_physicalHilbert`, `realSourcePhysicalL2Equiv`; 2013 manuscript audit below | Exact physical source and target Hilbert norms, global analytic real inverse, complex extension, and physical action contour integrals are proved. Independent physical spectral labels, canonical product, psi-functions, terminal-sheet angles, and the full integral-defined physical map are identified below for the inspected 2013 conventions. The literal physical canonical brackets and the exact Fourier derivatives of the intrinsic physical map and inverse at zero are now proved as well. The precise 2014 construction comparison remains unproved. |
| Remark 14.2(ii): p>2 surjectivity | No such claim | The source states this as an open question |
| Remark 14.2(iii): positive smoothness | `sourceSection14_sobolev_characterization`, `sourceSection14_sobolev_open_dense`, `sourceSection14_sobolev_continuous_bijective` | Exact original source/gap/output regularity at every real t>=0; continuous injection with open dense image for every finite p>1, bijective for 1<p<=2. Both weighted inverse identities and inverse exponent compatibility hold. Canonical coordinate identities and full native weighted complex analyticity are proved, with exact raw coefficients and compatibility of the full bounded Jacobian with unweighted inclusions. Full weighted complex exponent compatibility, native real analyticity, and native complex Jacobian bijectivity are proved. Actual complex analytic local inverses have both inverse germs. Real analytic local inverses and the analytic inverse on the actual open image are now constructed for every spectral weight. For 1<p<=2 the native Sobolev bijection is a homeomorphism with analytic inverse and the exact strict inverse derivative. These positive-smoothness inverse properties are supplied by `sourceSection14_sobolev_global_analytic_inverse`. |

## Literal real formulas and the external Hilbert comparison

[`SourceBirkhoffRealActionAngle.lean`](../NLS/ZakharovShabat/SourceBirkhoffRealActionAngle.lean)
proves that the complex amplitude xi_n gamma_n / sqrt(2) equals the
nonnegative real sqrt(2 I_n). The proof uses the positive normalized action,
ordered real periodic endpoints, and the exact action factorization.
`real_rectangular_formula` then applies at every real gap. At a collapsed
gap the action and both coordinates vanish. `real_rectangular_formula_of_eta`
allows any admissible eta integral at open gaps and any value at closed gaps.
The 2*pi integral period preserves both cosine and sine.

[`SourceBirkhoffActionAngleMap.lean`](../NLS/ZakharovShabat/SourceBirkhoffActionAngleMap.lean)
defines the two sequences directly by these formulas, proves their lp
membership, and identifies the resulting full map with `sourceRealBirkhoffMap`.
The equality supplies analyticity through collapsed gaps. For 1<p<=2,
`realActionAngleHomeomorph` has the same global analytic inverse as the
existing map. Forward maps are independent of the normalized root family;
both directions commute with exponent inclusion.
[`SourceSection14ActionAngle.lean`](../NLS/ZakharovShabat/SourceSection14ActionAngle.lean)
constructs the data and gives a Hilbert homeomorphism with these formulas
for every admissible eta choice.

The public [University of Zurich 2013 preprint listing](https://www.math.uzh.ch/preprint?key1=2013)
contains entry 07-2013, B. Grébert and T. Kappeler, *The defocusing NLS
equation and its normal form*. The retrieved manuscript has 142 PDF pages,
a July 2013 preface, and SHA-256
`81fc3df686ed112f4a724860d88d83479563836d93238baf2000ba17203f4d83`.
This records the inspected version without relying on its expiring download
URL. It is not silently identified with the dissertation's
[2014 reference [23]](https://ems.press/books/elm/205).

The inspected manuscript uses the following normalizations:

| Manuscript location | Normalization | Internal counterpart |
| --- | --- | --- |
| Section 13, actions | 1/pi contour integral of lambda times the discriminant derivative over the canonical square root | `sourceIndexedAction` and its original integral identifications |
| Theorem 13.3 | Positive principal root xi_n of 4 I_n / gamma_n^2; xi_n=1 at zero | `sourceNormalizedActionRoot`; the positive real amplitude theorem above |
| Section 15, angles | Left periodic endpoint to Dirichlet endpoint, terminal sheet fixed by delta; theta=eta+beta and eta has 2*pi ambiguity | Original eta integral values, beta series, and `real_rectangular_formula_of_eta` |
| Chapter IV opening and Section 16, printed p. 88 (PDF p. 94) | x_n=sqrt(2 I_n) cos(theta_n), y_n=sqrt(2 I_n) sin(theta_n); positive sine orientation | `real_rectangular_formula`, `realActionAngleMap_eq` |

The independent physical spectral, normalized-function, action, and angle
equalities proved below now give formal identifications for these inspected
2013 specifications. The existing `sourcePhysicalL2` in
[`SourcePhysicalL2.lean`](../NLS/ZakharovShabat/SourcePhysicalL2.lean) already
maps every Hilbert coefficient source to its physical class.
[`L2SourceCharacteristics.lean`](../NLS/ZakharovShabat/L2SourceCharacteristics.lean)
and [`L2SourceMidpointGradient.lean`](../NLS/ZakharovShabat/L2SourceMidpointGradient.lean)
identify the physical separated characteristics, anti-discriminant, and
discriminant, including arbitrary L2 inputs. These established identities
should be reused.

The physical source identification is now completed by the exact
`sourcePhysicalL2Equiv` and `realSourcePhysicalL2Equiv` described below.
The independent physical spectral labels, canonical root, normalized
functions, terminal-sheet angle integrals, and full physical map are now
identified under this equivalence. The literal formulas and eta-choice
independence supply the full coordinate equality. Agreement of the
relevant 2013 and 2014 source conventions also remains to be established.
No p>2 surjectivity assertion is added.

The publisher's public [2014 contents](https://ems.press/content/book-chapter-files/23100)
locate the separated spectra in Section 5 (p. 26), psi-functions in Section
14 (p. 84), angles in Section 15 (p. 97), and Birkhoff coordinates in Chapter
IV (p. 105). Its [preface](https://ems.press/content/book-chapter-files/23099)
still bears the July 2013 date. Its public
[overview](https://ems.press/content/book-chapter-files/23102) states the
global bi-analytic map and its Fourier derivative at zero. These checks
confirm the publication context and broad theorem, but do not establish
identity of the construction formulas in the chapters requiring a subscription.

## The original physical Hilbert spaces and map

[`UnitIntervalL2Equiv.lean`](../NLS/Fourier/UnitIntervalL2Equiv.lean)
constructs a complex linear isometry equivalence from l2 coefficients to
ordinary Lebesgue L2 classes on (0,1]. Its inverse is the normalized unit
Fourier integral; arbitrary square-integrable representatives are
reconstructed, without matching endpoint values or continuity. Pairing
this equivalence gives `sourcePhysicalL2Equiv` in
[`SourcePhysicalL2Equiv.lean`](../NLS/ZakharovShabat/SourcePhysicalL2Equiv.lean).
A density proof identifies it with the existing `sourcePhysicalL2`, so the
established physical characteristic and gradient identities still apply.
The old bound by twice the source norm is sharpened to exact norm equality.

[`SourcePhysicalRealL2.lean`](../NLS/ZakharovShabat/SourcePhysicalRealL2.lean)
proves that physical a.e. conjugation is exactly the source's conjugate
Fourier reflection. The resulting real physical submodule is complete and
isometrically equivalent to `realTypeSourceSubmodule 2`.

[`SourcePhysicalActions.lean`](../NLS/ZakharovShabat/SourcePhysicalActions.lean)
transports the original indexed labels and canonical product through this
equivalence. Its action is a literal contour integral of
lambda*deriv(l2Discriminant u)/physicalCanonicalRoot u. The canonical
product squares to (l2Discriminant u)^2-4 and at zero equals -2*i*sin(lambda),
fixing the sign. Every real physical source supplies an actual nonsingular
isolating circle, including collapsed gaps. Every admissible winding-one
circuit gives the same action. The independent physical specifications below now identify these
transported labels and the canonical root.

[`SourcePhysicalActionAngle.lean`](../NLS/ZakharovShabat/SourcePhysicalActionAngle.lean)
uses `PhysicalRealBirkhoffTarget = WithLp 2 (RealCoeff 2 × RealCoeff 2)`.
This retains the Hilbert sum of the component energies on the target as
well as the source; the comparison with the product maximum norm is an
explicit continuous linear equivalence. The physical homeomorphism has
analytic forward and inverse maps, literal action–angle coordinates for
all admissible eta choices, family independence, and agreement at every
larger finite exponent. `physical_hasSum_actions` gives convergence to
half the physical norm squared. Consequently the nonlinear map and its
inverse preserve the norm exactly; no distance-preserving claim is made.

[`SourcePhysicalBirkhoffComplex.lean`](../NLS/ZakharovShabat/SourcePhysicalBirkhoffComplex.lean)
extends the full map analytically to an open physical L2 neighborhood of
the entire real form. The complex target also carries its Hilbert pair
norm. Complex inclusion of the real homeomorphism equals this extension,
and the indexed-action radius holds throughout its complex domain.
[`SourceSection14PhysicalHilbert.lean`](../NLS/ZakharovShabat/SourceSection14PhysicalHilbert.lean)
constructs one family, its global real map, inverse, and complex extension
together. Neither inverse existence nor the physical/source equivalence
is requested as an additional premise.

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
arbitrary spectral weights such as exponential weights. Dense image alone
does not establish open image or surjectivity. Subsequent steps below prove
Sobolev open image and bijectivity, canonicality, and full weighted complex
analyticity. The closing-coordinate argument below establishes analyticity
without the then-missing complex midpoint bound. The later terminal
construction now supplies that bound, as recorded below.

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
from the selected family. Weighted complex-domain compatibility was not
part of that milestone; the weighted complex map is now constructed below.

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

At that milestone, remaining clauses included weighted complex analyticity,
complex compatibility, weighted canonicality, analytic local inverses, and weighted inverse
continuity and analyticity. The complex Dirichlet-minus-periodic-midpoint
bound was also then missing; the later terminal construction below supplies
it. Surjectivity at p>2 is still the source's open question. The 28 public checks include p=3/2 at the one-step threshold,
p=4 at order 7/3, zero order, both inverse identities, and actual Section
14 constructions. Validation is recorded in [the implementation status](../STATUS.md).

## Canonical coordinate identities on original weighted sources

For every Section 6 spectral weight and every finite p>1, the actual
original weighted real coordinates have regular full scalar complex
derivatives. Their physical Fourier brackets satisfy

```
{x_n,x_m} = 0,    {x_n,y_m} = -delta_nm,    {y_n,y_m} = 0.
```

These statements include closed gaps and exponents below two. No
finite-gap hypothesis, supplied coordinate derivative, or canonicality
assumption is required. The mixed identity is also stated as the literal
absolutely convergent sum with frequency reversal and factor -i.

| Module | Public evidence |
| --- | --- |
| [Raw weighted directions](../NLS/SequenceSpaces/WeightedSingle.lean) | A single raw coefficient c at n; its norm is exactly w(n) times norm(c), including the infinite Banach exponent. |
| [Original complex inclusion](../NLS/ZakharovShabat/SourceWeightedInclusion.lean) | Bounded injective inclusion preserves both raw components, agrees with the real inclusion, and preserves both single-direction families. |
| [Weighted regular cotangents](../NLS/Poisson/WeightedRegularSourceCotangent.lean) | Verified square-summable values on raw Fourier directions, witness independence, antisymmetry, norm bound, absolute convergence, and the physical Fourier formula. |
| [Actual cotangent restriction](../NLS/ZakharovShabat/SourceWeightedCotangent.lean) | Pullback along the original complex source inclusion retains all Fourier coefficient witnesses and physical brackets. |
| [Actual canonical coordinates](../NLS/ZakharovShabat/SourceBirkhoffWeightedCanonical.lean) | Exact agreement with original weighted real outputs, actual full scalar derivatives, all three canonical relations, and the literal mixed Fourier sum. |
| [Common scalar domain](../NLS/ZakharovShabat/SourceBirkhoffWeightedScalarAnalytic.lean) | Scalar complex power-series analyticity at every point of the common open weighted domain, which contains all weighted real sources. |
| [Actual Section 14 construction](../NLS/ZakharovShabat/SourceSection14WeightedCanonical.lean) | One constructed family supplies all canonical identities for every spectral weight and finite p>1. |

The raw unit directions have coefficient one and weighted norm w(n). Their image under the original source
inclusion is therefore the same unweighted Fourier direction. Pullback
preserves the coefficient witnesses of the previously constructed regular
cotangents, so the absolutely convergent physical brackets are identical.
The chain rule identifies these pullbacks with the full scalar derivatives
of the actual coordinate extensions.

The common weighted complex domain is the preimage of the original
unweighted domain under the continuous complex source inclusion. Each
scalar extension equals the corresponding raw coordinate of the original
weighted real map. This establishes scalar power-series analyticity and
the canonical coordinate identities; it does not give weighted local norm
bounds for the entire sequence map or a bounded weighted Jacobian.

At that milestone, full sequence analyticity and the weighted Jacobian
were still missing. These are established in the following extension;
complex exponent compatibility and analytic inverse properties were also
still missing. The later sections establish them, and the terminal
construction below supplies the complex midpoint bound. The p>2
surjectivity question and the precise 2014 comparison are unchanged.
The 18 new public checks cover raw amplitudes, zero/infinite sequence
endpoints, signed indices, collapsed gaps at the zero source, fractional
weights at p=3/2 and p=4, and the actual canonical construction.
Validation is recorded in [the implementation status](../STATUS.md).

## Full weighted complex analyticity and the actual Jacobian

For every spectral weight and finite p>1, the full original sequence map
is complex analytic on one open native weighted domain containing all
weighted real sources. Both raw components agree with the original
unweighted complex map. The restriction to real sources equals the actual
original weighted real map, including at closed gaps.

| Module | Role |
| --- | --- |
| [Signed resonance deletion](../NLS/ZakharovShabat/SourceDeleteResonance.lean) | Complex linear real-preserving projection; norm contraction and uniform control of distant deleted pairs on a common ball. |
| [Singleton spectral strips](../NLS/ZakharovShabat/SourceBirkhoffSingletonStrip.lean) | Actual real singleton strips force both original coordinates to vanish uniformly in the tail. |
| [Real-form analytic observations](../NLS/ZakharovShabat/SourceRealTypeAnalyticSlice.lean) | Analytic observations zero on the real slice are zero on the complex ball. |
| [Deleted complex slices](../NLS/ZakharovShabat/SourceBirkhoffDeletedSlice.lean) | Applies the identity principle to the two actual coordinate observations. |
| [Actual closing inverse](../NLS/ZakharovShabat/SourceBirkhoffComplexClosingInverse.lean) | Constructs a real-preserving analytic adapted inverse and complex coordinate zeros after deletion. |
| [Complex coordinate bound](../NLS/ZakharovShabat/SourceBirkhoffComplexClosingBound.lean) | Uniform distant-coordinate bound by the two signed adapted coefficients, for all later cutoffs. |
| [Uniform center compatibility](../NLS/ZakharovShabat/WeightedResonantCenterForget.lean) | Extends weight forgetting from a fixed source to a common complex neighborhood. |
| [Adapted map compatibility](../NLS/ZakharovShabat/NormalizedWeightedClosingCompatibility.lean) | Weighted decoding commutes with the actual adapted maps on that neighborhood. |
| [Finite head and tail bound](../NLS/SequenceSpaces/FiniteHeadTailBound.lean) | Actual sequence membership and norm bound from a finite head and two tail majorants, including the infinite Banach exponent. |
| [Normalized complex sequence](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexSequence.lean) | Defines the weighted sequence map and derives Banach analyticity from verified local bounds and coordinate analyticity. |
| [Constructed weighted bound](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexBound.lean) | Full weighted membership and uniform local norm control at arbitrary nearby complex inputs. |
| [Native analytic extension](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexAnalytic.lean) | Common domain, full weighted analyticity, original raw coefficients, and exact agreement with the weighted real map. |
| [Full derivative compatibility](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexDerivative.lean) | The bounded weighted Fréchet derivative commutes with both original unweighted inclusions. |
| [Actual Section 14 construction](../NLS/ZakharovShabat/SourceSection14WeightedComplex.lean) | Constructs one family with these properties simultaneously for every spectral weight. |

The complex coordinate estimate uses the actual adapted inverse. On real
sources, deleting a resonance closes the corresponding gap and kills both
coordinates. The real-form identity principle extends those zeros to a
complex ball. The adapted map's lower distance estimate and the original
Birkhoff map's local Lipschitz bound control each coordinate by the deleted
pair. Compatibility transfers this estimate to the weighted adapted map.
A finite head and the two weighted tail sequences give full local norm
bounds. Bounded-coordinate analyticity and weight isometries then yield
the native sequence-valued analytic map. Differentiating its exact
unweighted compatibility proves the full Jacobian identity.

The 22 public checks include complex closing zeros, actual membership and
norm bounds, p=3/2 and p=4 at fractional Sobolev orders, the zero source with
closed gaps, exact original real coefficients, and derivatives on raw unit
Fourier directions. The Section 14 wrapper supplies the family and all
weighted analytic maps without extra analyticity or inverse assumptions.
Validation is recorded in [the implementation status](../STATUS.md).

The next extension below establishes complex exponent compatibility,
native weighted real analyticity, and Jacobian injectivity. Weighted
Jacobian surjectivity, analytic local inverses, and weighted Sobolev global
inverse continuity and analyticity were still pending at that milestone.
The subsequent completion sections establish them. The terminal
construction below now supplies the complex midpoint bound, without making
it a premise of the earlier weighted analyticity proof. No p>2 surjectivity
or comparison with the precise 2014 construction in [23] is inferred.

## Complex weighted compatibility and native real analyticity

For each original family and spectral weight, a fixed open weighted domain
contains every weighted real source. The full complex weighted sequence
maps agree throughout the intersection of two such domains after exponent
inclusion, for every finite 1<p<=q. The root families are independent.
The equality has one common complex germ for all coordinates. The full
bounded weighted derivatives obey the same identity. At equal exponents,
this proves that the map is independent of the family on the overlap.

| Module | Public evidence |
| --- | --- |
| [Native weighted pair inclusions](../NLS/SequenceSpaces/WeightedPairExponent.lean) | Complex linear coefficient-preserving inclusion, injectivity, identity, and composition at all Banach exponents, including one and infinity. |
| [Real pair projection](../NLS/SequenceSpaces/WeightedRealPairProjection.lean) | Bounded projection onto the original weighted real target, with exact identification by raw coefficients. |
| [Source and target exponent inclusions](../NLS/ZakharovShabat/SourceWeightedComplexExponent.lean) | Both unweighted inclusions commute with exponent change; the native complex inclusion restricts to the existing real one. |
| [Fixed complex domains](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexDomain.lean) | One chosen open domain per family and weight retains all real sources, full analyticity, and map/derivative inclusion identities. |
| [Full complex exponent overlaps](../NLS/ZakharovShabat/SourceBirkhoffWeightedComplexExponent.lean) | Whole-sequence equality, common germs, full derivative compatibility, and family independence, without a real-type or open-gap premise on the overlap point. |
| [Native real analytic map](../NLS/ZakharovShabat/SourceBirkhoffWeightedRealAnalytic.lean) | Full real power-series analyticity of the actual original map on its entire weighted real source. |
| [Injective weighted Jacobian](../NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianInjective.lean) | Every weighted kernel vector vanishes, by inclusion into the original unweighted bijective derivative. |
| [Actual compatible constructions](../NLS/ZakharovShabat/SourceSection14WeightedCompatibility.lean) | Constructs both families and their domains, simultaneously for all spectral weights, and supplies native real analyticity and injective derivatives. |

The compatibility proof includes each weighted output in the unweighted
target, applies the existing full complex exponent theorem, and uses the
injectivity of that inclusion. The derivative proof applies the same
argument to actual bounded derivatives. Real analyticity uses restriction
of scalars and the bounded real-part projection; equality of the raw
coefficients identifies the result with the original weighted real map.

The 24 public checks cover signed complex single coefficients, inclusion
from one to infinity, composition through exponent two, real projection,
full common germs, independent families at equal exponents, derivatives
on arbitrary complex directions, fractional Sobolev weights, and the actual
p=3/2 to p=4 construction. Zero and collapsed-gap sources are included.
Validation is recorded in [the implementation status](../STATUS.md).

Remaining: weighted Jacobian surjectivity, analytic weighted local inverses,
and continuity and analyticity of the weighted Sobolev global inverse for
1<p<=2. Injectivity does not imply surjectivity in these infinite-dimensional
spaces. The direct complex Dirichlet-minus-periodic-midpoint estimate,
external map comparison, and p>2 surjectivity question are unchanged.

## Compact adapted derivatives and finite-gap Fourier blocks

The next part of the weighted inverse argument now has actual compact
operators and exact finite-gap derivative rows. For every spectral weight
and finite p>1, the normalized adapted map has derivative equal to identity
plus compact on a common complex neighborhood, uniformly over all late
cutoffs. The difference of two cutoffs has finite output support. After
differentiation, the remaining error is the derivative remainder at the
later cutoff and tends to zero in operator norm.

| Module | Public evidence |
| --- | --- |
| [Symmetric source projections](../NLS/ZakharovShabat/SourceSymmetricTruncate.lean) | Compact bounded projections in the native pair norm, including one and infinity. |
| [Adapted derivative compactness](../NLS/ZakharovShabat/NormalizedWeightedClosingCompact.lean) | Exact cutoff identity, compact weighted derivative remainder, and original unit-weight specialization. |
| [Compact inverse derivative algebra](../NLS/FunctionalAnalysis/CompactInverseDerivative.lean) | Right-inverse and chain-rule transfer of compact remainders through actual analytic germs. |
| [Compact diagonal observations](../NLS/SequenceSpaces/CompactDiagonalEntries.lean) | Matching output coordinates vanish uniformly for any bounded input family at finite exponents; weak convergence of the family is not assumed. |
| [Signed compact entries](../NLS/ZakharovShabat/SourceCompactSignedEntries.lean) | All four entries on the two raw signed unit directions vanish in the tail. |
| [Deleted-slice derivative rows](../NLS/ZakharovShabat/SourceDeletedSliceDerivative.lean) | Actual complex slice zeros imply both rows depend on exactly the matching signed source pair. |
| [Actual compact inverse charts](../NLS/ZakharovShabat/SourceBirkhoffClosingInverseCompact.lean) | Constructs an analytic inverse with its exact base point, right-inverse identity, complex slice zeros, and compact Birkhoff derivative remainder at every real source. |
| [Finite-gap Fourier blocks](../NLS/ZakharovShabat/SourceBirkhoffFiniteGapAdaptedDerivative.lean) | One actual chart supplies exact two-mode rows and uniformly small differences from all four free Fourier entries. |

At finite-gap sources, the adapted base is a finite Fourier truncation.
Deleting a sufficiently distant resonant pair therefore fixes the base.
Differentiating the established complex slice zeros kills every other input
mode. Compactness in the same chart makes the four remainder entries tend
to zero. This uses uniform tails of a compact image; it does not infer a
summable sequence of row norms from arbitrary compactness.

The 18 public checks include signed boundary projections, zero resonance,
complex amplitudes on nonmatching modes, fractional Sobolev weights at
p=3/2 and p=4, and construction of the actual Section 14 family and inverse
without supplied compactness or inverse assumptions. Validation is recorded
in [the implementation status](../STATUS.md).

The weighted transfer, weighted Jacobian surjectivity, and complex analytic
local inverses are now proved by the next step.

## Weighted Jacobian bijectivity and actual complex local inverses

For every spectral weight and finite p>1, the actual native complex weighted
Jacobian is bijective at every weighted real source. The analytic inverse
function theorem supplies an inverse of the actual map, both inverse germs,
and the strict derivative equal to the bounded inverse Jacobian. Closed
gaps require no separate exclusion. The inverse Jacobian commutes with
forgetting the weight, using the same original unweighted family.

| Module | Public evidence |
| --- | --- |
| [Diagonal tail compactness](../NLS/SequenceSpaces/TailDiagonalCompact.lean) | Exact diagonal tail rows and vanishing entries imply compactness, including p=infinity. |
| [Signed block compactness](../NLS/ZakharovShabat/SourceSignedBlockCompact.lean) | Two signed source modes per output row and four vanishing block entries imply compactness. |
| [Weighted signed blocks](../NLS/ZakharovShabat/WeightedSignedBlockLift.lean) | Even weights cancel in each exact block, transferring compactness to the stronger weighted norm. |
| [Adapted derivative equivalences](../NLS/ZakharovShabat/NormalizedWeightedClosingDerivativeEquiv.lean) | Constructs both weighted and unweighted equivalences at a common cutoff; their inverses commute with decoding and have norm at most two. |
| [Normalized weighted Jacobian](../NLS/ZakharovShabat/NormalizedWeightedBirkhoffJacobian.lean) | Represents the actual native derivative in normalized coordinates and proves exact decoding. |
| [Finite-gap weighted compactness](../NLS/ZakharovShabat/SourceBirkhoffWeightedFiniteGapJacobianCompact.lean) | Transfers the compact Fourier remainder through one actual adapted inverse chart and back to the original weighted derivative. |
| [Weighted finite-gap density](../NLS/ZakharovShabat/SourceWeightedFiniteGapDensity.lean) | Actual finite-gap sources approximate in every native weighted real norm. |
| [All-real weighted compactness](../NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianCompact.lean) | Continuity and weighted finite-gap density extend the compact Fourier remainder to every weighted real source. |
| [Native Jacobian bijectivity](../NLS/ZakharovShabat/SourceBirkhoffWeightedJacobianInvertible.lean) | The Fredholm alternative and the proved trivial kernel give native weighted surjectivity. |
| [Actual complex local inverse](../NLS/ZakharovShabat/SourceBirkhoffWeightedLocalInverse.lean) | Bounded inverse Jacobian, compatibility with forgetting the weight, both nonlinear inverse germs, and strict inverse derivative. |
| [Constructed Section 14 family](../NLS/ZakharovShabat/SourceSection14WeightedLocalInverse.lean) | Constructs the family before choosing the weight or real source; no inverse, derivative equivalence, or compactness premise is supplied. |

The proof of weighted compactness uses exact tail rows. It does not infer
compactness in a stronger norm merely by restricting a compact unweighted
operator. Its density argument is also in the actual weighted norm.

Twenty-one public checks cover signed complex inputs, exceptional finite
rows at infinity, native weighted density, both derivative inverse identities,
both nonlinear inverse germs, local injectivity and local surjectivity,
and fractional Sobolev weights on both sides of p=2. Validation is recorded
in [the implementation status](../STATUS.md).

The real-form restriction and Sobolev global analytic inverse are now
proved by the following step.

## Real weighted inverses and global Sobolev analyticity

The actual complex inverse Jacobian preserves the native weighted real
forms: forgetting the weight identifies it with the unweighted inverse,
whose real restriction is already known. The source inclusion reflects
the exact raw conjugate-reflection condition, so this proves reality in
the original weighted source. Differentiating the actual complex inclusion
then constructs the bounded real derivative equivalence.

For every spectral weight and finite p>1, the real map has analytic local
inverses with both inverse germs and the exact strict inverse derivative.
Its complex inverse preserves the real form locally. Global injectivity
makes the real map an open embedding, with an analytic inverse on its
actual open image. All image regularity statements retain the image
condition; the total inverse extension is set to zero outside that image.

For 1<p<=2 and every nonnegative real Sobolev order, the already constructed
native weighted bijection is a homeomorphism with both analytic directions.
Local uniqueness identifies its inverse with the actual analytic local
inverse. Its strict derivative is the bounded inverse weighted real
Jacobian at the recovered source. This retains the previous exact raw
agreement with the unweighted inverse and inverse exponent compatibility,
including independently chosen original families.

| Module | Public evidence |
| --- | --- |
| [Weighted real pair inclusion](../NLS/SequenceSpaces/WeightedRealPairInclusion.lean) | Bounded, injective complex inclusion preserving every raw coefficient, including Banach endpoints. |
| [Original real inclusions](../NLS/ZakharovShabat/SourceWeightedRealInclusion.lean) | Source inclusion reflects reality; real and complex target inclusions commute with forgetting the weight. |
| [Actual weighted real Jacobian](../NLS/ZakharovShabat/SourceBirkhoffWeightedRealJacobian.lean) | Actual derivative compatibility, complex inverse preservation of reality, native real bijectivity, and a bounded real inverse equal to the complex restriction. |
| [Real analytic local inverses](../NLS/ZakharovShabat/SourceBirkhoffWeightedRealLocalInverse.lean) | Both inverse germs, strict inverse derivative, local real-form preservation of complex inverses, and open embedding for all spectral weights. |
| [Inverse on the actual image](../NLS/ZakharovShabat/SourceBirkhoffWeightedImageInverse.lean) | Image homeomorphism, both inverse identities, analyticity, and exact strict derivative on the open image for every finite p>1. |
| [Global Sobolev inverse](../NLS/ZakharovShabat/SourceBirkhoffSobolevGlobalInverse.lean) | Native Sobolev homeomorphism with both analytic directions and the exact inverse Jacobian, for 1<p<=2 and every real t>=0. |
| [Constructed original families](../NLS/ZakharovShabat/SourceSection14WeightedRealInverse.lean) | Constructs the original family before choosing any spectral weight or nonnegative Sobolev order. |

Twenty-two public checks cover both inverse Jacobian identities, actual
complex real-form preservation, open images, inverse regularity on the
image, both Sobolev inverse identities, compatibility with the unweighted
inverse and exponent inclusions, p=4 closed gaps, p=3/2 with Sobolev order
1/3, and p=2 at order zero. Validation is recorded in
[the implementation status](../STATUS.md).

The positive-smoothness inverse properties in Remark 14.2(iii) are now
proved in the original weighted norms. The external [23] comparison in
Remark 14.2(i) remains separately uncertified. No p>2 global surjectivity
or global surjectivity for arbitrary spectral weights is asserted.

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

## Independent physical spectral and normalized-function specifications

The inspected 2013 manuscript specifies separated roots in printed
pp. 24–26 by zeros of the actual monodromy characteristics, analytic
multiplicities, lexicographic ordering, and l2 free-lattice displacements.
[`PhysicalBoundaryRoots.lean`](../NLS/ZakharovShabat/PhysicalBoundaryRoots.lean)
uses exactly these conditions, without source labels in the specification.
Existence is witnessed by the source construction. To prove uniqueness,
l2 decay and the distant simple-root count fix both tails; equal global
multiplicities then fix the finite ordered central block.
[`OrderedEnumerationFiniteException.lean`](../NLS/SequenceSpaces/OrderedEnumerationFiniteException.lean)
proves that last step with repeated entries allowed. The selected roots
satisfy the actual Dirichlet and Neumann endpoint equations and the
normalized product for the physical characteristic. Their analytic orders
are proved as ENat equalities, not merely natural-number truncations.

[`PeriodicEndpointGlobalMultiplicity.lean`](../NLS/ZakharovShabat/PeriodicEndpointGlobalMultiplicity.lean)
upgrades finite-box counts to global multiplicities for the original
periodic labels. In
[`OrderedPairedL2Enumeration.lean`](../NLS/SequenceSpaces/OrderedPairedL2Enumeration.lean),
common real strips isolate arbitrarily large finite blocks of two ordered
paired sequences. Global multiplicities and l2 displacements determine
both sequences, including repeated roots and collapsed pairs.
[`PhysicalPeriodicEndpoints.lean`](../NLS/ZakharovShabat/PhysicalPeriodicEndpoints.lean)
therefore selects unique labels using only the physical discriminant
squared minus four, its analytic zero orders, ordering, and asymptotics.

Printed pp. 59–61, formulas (12.4)–(12.5), fix the principal standard root
and the canonical product with prefactor 2i and denominator pi_0=1.
[`PhysicalCanonicalRoot.lean`](../NLS/ZakharovShabat/PhysicalCanonicalRoot.lean)
forms these expressions directly from the physical endpoints. Every
symmetric finite cutoff converges to the paired infinite product. Its
identity with the established source root retains the exact free sign,
the square identity on the cut complement, and the physical action
contour formula.
[`PhysicalSpectralCircles.lean`](../NLS/ZakharovShabat/PhysicalSpectralCircles.lean)
specifies circle geometry in physical gaps alone and constructs a
nonsingular isolating circle for every real source and index.

Printed pp. 70–71 specify the entire psi numerator by the normalized
deleted root product, real gap placement, and the 1/(2*pi) Kronecker
periods. In
[`PhysicalPsiComparison.lean`](../NLS/ZakharovShabat/PhysicalPsiComparison.lean),
`PhysicalPsiGapData` contains only the deleted l2 vector, physical gap
placement, and literal vanishing off-diagonal periods against the intrinsic
product root. Existence and uniqueness are proved before selecting
`physicalPsiGapRoot`. The entire `physicalPsiFunction` then has every
normalized period, including the diagonal value one. The uniqueness claim
is within this gap-contained product class; it is not uniqueness among
arbitrary entire functions.

[`PhysicalPsiFamily.lean`](../NLS/ZakharovShabat/PhysicalPsiFamily.lean)
identifies this independent selection with every original Section 14
family. It proves global real analyticity of the root map in the physical
Hilbert norm, complex analytic extension on the physical Birkhoff domain,
and exact periods for complex inputs on every supplied isolating circle.
At zero potential all deleted displacements vanish, with diagonal periods
still normalized at the collapsed gaps. These results complete the physical
spectral and normalized-function specification comparison for the inspected
2013 conventions. The physical terminal-sheet eta/beta comparison is completed below;
the cited 2014 edition comparison remains open.

## The intrinsic physical action-angle map

[`PhysicalAngularPaths.lean`](../NLS/ZakharovShabat/PhysicalAngularPaths.lean)
specifies a scalar root continued continuously along a physical spectral
path. Its square is the actual L2 discriminant squared minus four; its
path interior lies in the isolating disk minus the physical gap. The
continued root has a fixed sign relative to the canonical product on that
interior. The omitted product is formed directly from physical standard
roots and retains the original normalization.

[`PhysicalDirichletPaths.lean`](../NLS/ZakharovShabat/PhysicalDirichletPaths.lean)
uses physical left periodic and Dirichlet endpoints. At regular terminals,
the physical anti-discriminant fixes the continued root. At a periodic
terminal no nonzero sign is prescribed. The actual integral-value set
requires a C1 path and curve integrability; its diagonal also requires
integrability of the omitted-product model. These are explicit hypotheses
on candidate values, not assumed existence statements.

[`PhysicalAngularComparison.lean`](../NLS/ZakharovShabat/PhysicalAngularComparison.lean)
constructs one such path at every real source and gap, making every
off-diagonal integrand integrable. The diagonal and model are integrable
at open gaps. It identifies every physical off-diagonal value with the
original beta and every physical diagonal value with an original eta
integral. Thus beta is unique across paths, circles, and continued roots;
eta is independent modulo 2*pi. The existence and uniqueness statements
are also available without a supplied normalized family.

[`PhysicalAngularValues.lean`](../NLS/ZakharovShabat/PhysicalAngularValues.lean)
selects beta from these physical integral values, omits its diagonal,
and defines the correction by its actual sum. Eta is selected from its
physical values at open gaps; the angle is eta plus the correction.
The resulting theta differs from the original theta by an integer multiple
of 2*pi. At closed gaps the coordinate formulas tolerate arbitrary eta.
[`PhysicalAngularReality.lean`](../NLS/ZakharovShabat/PhysicalAngularReality.lean)
proves absolute convergence, reality of every beta term, vanishing terms
at collapsed real gaps, and reality of eta choices and theta at open gaps.

[`PhysicalBirkhoffIntrinsic.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsic.lean)
defines the action by a physical isolating-circle integral. It defines the
real coordinates by the nonnegative action square root and positive sine
orientation. Both sequences are proved to lie in l2, giving a full map
whose definition contains the intrinsic physical integrals. Equality with
every original physical Section 14 map is then proved. It is not used as
the definition of the map.

[`PhysicalBirkhoffIntrinsicProperties.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsicProperties.lean)
constructs `intrinsicPhysicalBirkhoffHomeomorph`, analytic in both directions
with both inverse identities and exact Hilbert norm preservation. Its
inverse equals every original physical inverse. Every admissible eta
choice gives the same coordinates, the zero input gives zero, and one
constructed complex analytic extension is defined on an open physical
neighborhood containing every real input.

This proves the full-map identity for the intrinsic physical formulas and
path class matching the inspected 2013 manuscript. It does not equate the
2013 manuscript with the cited 2014 edition. The physical Poisson bracket
comparison is now established separately by the cotangent results below.


## Literal physical canonical brackets

The dissertation defines the physical bracket by -i times the integral of
cross-gradient products (introduction, p. 10; gradient convention, p. 22).
Lemma 15.3 uses {x_n,y_m}=-delta_nm. The positive sine convention of the
intrinsic map is retained.

[`PhysicalL2BilinearPairing.lean`](../NLS/ZakharovShabat/PhysicalL2BilinearPairing.lean)
proves integrability for products of arbitrary physical L2 representatives
and identifies the literal bilinear integral with reflected Fourier
duality. The pairing separates all L2 pairs.
[`PhysicalCotangentGradient.lean`](../NLS/ZakharovShabat/PhysicalCotangentGradient.lean)
constructs the unique physical gradient of every continuous complex
cotangent. Its integral against every physical L2 direction is the full
cotangent evaluation. Reflection is essential because this pairing is
unconjugated. The literal cross-gradient integral equals `sourceBivector`.

[`PhysicalPoissonBracket.lean`](../NLS/ZakharovShabat/PhysicalPoissonBracket.lean)
defines the bracket from the actual complex differentials. The chain rule
identifies it with the source bracket under `sourcePhysicalL2Equiv`.
Actual unit-interval Fourier integral functionals verify the opposite
frequency pairing and the factor -i. The bracket is antisymmetric and
vanishes on equal functionals.

[`PhysicalBirkhoffCanonical.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffCanonical.lean)
proves all three canonical bracket identities for every original physical
complex extension at every real input, including collapsed gaps. The
unconditional `intrinsicPhysicalBirkhoffMap_canonical_extension` constructs
an open physical neighborhood, an analytic complex extension of the
integral-defined real map, and its canonical identities together.

These are literal integral statements about unique physical L2 gradients,
with no canonical-bracket premise. The exact 2014 edition comparison remains
open; this result does not assert global surjectivity at p>2.

## Physical action Hamiltonian fields

[`PhysicalSpectralPoisson.lean`](../NLS/ZakharovShabat/PhysicalSpectralPoisson.lean)
proves analyticity of each indexed physical action on the full complex
physical Birkhoff domain and the cotangent identity dI_n=x_n dx_n+y_n dy_n.
The actions commute on the physical real form. This uses the actual
physical indexed integrals and the literal physical gradient bracket.

[`PhysicalActionHamiltonian.lean`](../NLS/ZakharovShabat/PhysicalActionHamiltonian.lean)
then proves that the native action field is tangent to the real form and
has coordinate velocities (-y_n,x_n) in its selected pair, zero in every
other pair. A closed physical gap makes both the full complex cotangent
and the whole native field zero. The constructed extension theorem supplies
these identities for the intrinsic physical map without caller-supplied
family data. This step establishes the vector fields and their coordinate
velocities; it does not assert a physical flow-existence theorem.

## Exact physical Fourier derivative at zero

[`PhysicalBirkhoffFourier.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffFourier.lean)
constructs the bounded complex transform directly through the exact physical
Fourier equivalence. At index n its components are
-(hat(h1)(-n)+hat(h2)(n))/sqrt(2) and
(hat(h1)(-n)-hat(h2)(n))/(sqrt(2)*i). The coefficients are actual
unit-interval Fourier integrals. The transform is a complex linear isometry
equivalence of the native Hilbert pair spaces; both inverse identities and
the inverse norm equality hold on the entire spaces.

[`PhysicalBirkhoffLinearization.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffLinearization.lean)
proves that every original physical complex extension has exactly this
full bounded derivative at zero. At every real physical input its complex
differential restricts to the native real differential of the intrinsic
integral-defined map. At zero this supplies both literal coordinate formulas.
Differentiating the actual global inverse identity proves that the inverse's
native real derivative at zero is exactly the inverse physical Fourier
operator on the complex inclusion of the real target.

This verifies the physical Fourier linearization and its normalization.
It does not identify the unavailable construction text of the cited 2014
edition with the inspected 2013 manuscript.

## Complete intrinsic physical action flows

[`PhysicalActionFlow.lean`](../NLS/ZakharovShabat/PhysicalActionFlow.lean)
uses the actual intrinsic homeomorphism to lift a one-coordinate rotation
to a trajectory in the native physical real L2 space. The construction is
defined for every real time and agrees with each original source family.
Its derivative equals the literal physical action Hamiltonian vector field,
with cross-gradient components (-i grad_2, i grad_1).

[`PhysicalActionFlowProperties.lean`](../NLS/ZakharovShabat/PhysicalActionFlowProperties.lean)
proves uniqueness even among complex L2 trajectories sharing the real initial
value. The field is analytic near the constructed trajectory by
[`PhysicalHamiltonianAnalytic.lean`](../NLS/ZakharovShabat/PhysicalHamiltonianAnalytic.lean),
so local ODE uniqueness propagates over all real times. Every physical
indexed action, the entire actual monodromy discriminant, and the exact
physical Hilbert norm remain constant. A closed selected gap gives a
constant trajectory.

[`PhysicalActionFlowGroup.lean`](../NLS/ZakharovShabat/PhysicalActionFlowGroup.lean)
identifies the exact positive-sine coordinate rotation. All other coordinates
are fixed. The time maps compose by addition, have negative-time inverses,
commute across arbitrary indices, and depend jointly continuously on time
and the initial physical state. Each is a homeomorphism. All trajectories
have period 2*pi; this does not claim a least period for stationary inputs.
The required coordinate commutation and joint continuity are also proved for
arbitrary Banach lp spaces, including infinity, in
[`RealActionRotationProperties.lean`](../NLS/SequenceSpaces/RealActionRotationProperties.lean).

These results establish complete flows of individual actions. They retain
the precise 2014 edition comparison qualification recorded above.

## Later completion of the complex weighted spectral-term bounds

[SourceWeightedTerminalComplexBound.lean](../NLS/ZakharovShabat/SourceWeightedTerminalComplexBound.lean)
removes the exact eta-remainder phase from the constructed weighted eta
coordinates. For every spectral weight and finite p>1, both signed literal
terminals have bounded weighted lp realizations on one complex neighborhood
of each real source in the normalized weighted chart.

[SourceWeightedSpectralTermsComplex.lean](../NLS/ZakharovShabat/SourceWeightedSpectralTermsComplex.lean)
then proves the exact identities

```
mu_n - tau_n = -(terminal_n(1) + terminal_n(-1))/4,
sine_n = i*(terminal_n(1) - terminal_n(-1))/4.
```

`SourceBirkhoffMapComplexData.exists_local_normalizedWeightedSpectralTerms_bound`
constructs two lp sequences whose coefficients are exactly w(2n) times
these original spectral terms, with a common uniform norm bound and a
common complex neighborhood. All indices are included. The theorem applies
to the complex data in the existing `sourceSection14` construction; its
proof uses the established Birkhoff and eta maps.

This closes the earlier missing local weighted membership and bound for
the complex Dirichlet-minus-midpoint term. It is not an interlacing estimate
for arbitrary complex sources, nor a new claim that the term is pointwise
bounded by half the gap. The same completed construction is documented in
[Section 23](SECTION_23.md). The exact 2014 edition comparison remains separate.
