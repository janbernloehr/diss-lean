# Implementation plan

## Latest progress: full interior regularity and Cauchy normalization

`SourceFullAbelianJointAnalytic.lean` proves joint analyticity of the
canonical full primitive throughout the complex cut complement on one
open connected neighborhood of the real-source locus. The same function
retains spectral analyticity on the larger domain with collapsed gaps
filled. Joint analyticity here is asserted off all moving cuts; no joint
regularity at a filled collapsed endpoint is claimed.

The generic `ParametricPrimitivePropagation.lean` supplies the missing
parameter argument. On a convex product chart, a spectral primitive is
the sum of its anchor value and the explicit parametric integral of its
derivative. An analytic anchor value therefore propagates across the
chart without assuming source continuity of the primitive. An open-and-
closed argument propagates this regularity along any connected spectral
slice. The common exterior supplies the initial anchor.

`SourceFullAbelianDifferential.lean` propagates the exact Floquet
exponential identity to the full spectral cut complement. Joint
analyticity identifies the normalized logarithm germ and proves the full
differential `canonicalRoot⁻¹ • d Delta` everywhere off the cuts,
including the potential gradient in arbitrary complex directions.

`SourceFullAbelianCauchyCompatibility.lean` identifies the full function
with every overlapping normalized Cauchy disc chart. The real projection
path fixes the value at a common collar anchor; uniqueness on the
connected cut disc identifies all remaining values. The canonical full
primitive consequently inherits the exact limit `i pi (n-j)` at both
endpoints of gap `j`, including a collapsed selected gap. An existence
theorem supplies such a complex source neighborhood around every real
source and every selected gap.

Public checks verify full joint and filled-slice analyticity together
with the exact differential at exponent 3/2, the full interior potential
gradient, and the exact endpoint limit `-5 i pi` for index -3 at gap 2.

This removes the interior parameter-regularity gap and transfers the
previous local endpoint normalization to the canonical function. The
endpoint-neighborhood radius may still depend on the selected gap;
uniform endpoint control across all gaps on a common almost-real
neighborhood remains next. The estimates in Lemma 19.1(iii), later
frequency results, and the full dissertation remain unfinished.

## Previous milestone: one compatible full spectral primitive

`SourceFullAbelianPrimitive.lean` now defines one spectral abelian
primitive whose values are independent of the supporting source ball,
selected spectral chart, and ambient root neighborhood. The equality
holds on the whole complement of noncollapsed gaps, including every
filled collapsed gap. The function retains the exact spectral
derivative, all signed-index shifts, the actual real-source values,
and the free formula at every spectral point.

`RealCenteredDiscExterior.lean` proves path connectedness of the exterior
of uniformly bounded discs with real centers and a real exterior point.
`SourceAbelianComplexDomainConnected.lean` applies this geometry to the
common disc family and proves connectedness of the full cut complement
at complex potentials. Any two constructions have a nonempty open
exterior intersection. The identity theorem identifies their primitives
off the cuts; density and continuity identify their collapsed fillings.
`SourceAbelianSpectralChart.lean` packages these compatible constructions.

`SourceFullAbelianExterior.lean` proves that this same defined function
agrees with the projected primitive on every supported exterior product.
It is jointly analytic there, with full differential
`canonicalRoot⁻¹ • d Delta`. One open connected neighborhood of the whole
real-source locus supports both full spectral analyticity and uniform
joint exterior regularity for this function.

Public checks use exponent 3/2 to verify both forms of analyticity and
the exact differential simultaneously. They also check independence
between different ambient neighborhoods with a negative index shift,
the canonical free formula including collapsed lattice gaps, and the
spectral derivative throughout the cut complement.

This closes the choice-compatibility gap left by the previous milestone
and combines the spectral and exterior regularity toward Lemma 19.1(i).
Joint regularity in the interior and agreement there with the earlier
normalized Cauchy charts remain to be established for this full function.
That agreement should propagate the exact complex endpoint constants
uniformly. The estimates in (iii), later frequency results, and the full
dissertation remain unfinished.

## Previous milestone: common-neighborhood full spectral continuation

`SourceAbelianAlmostRealSpectralContinuation.lean` now constructs an
open connected neighborhood of the real-source locus covered by source
balls that control every gap simultaneously. For every complex source
in each ball, the actual projected exterior primitive has a spectral
continuation to the whole complement of noncollapsed gaps, with its
exact spectral derivative off the cuts and all signed-index shifts.
Collapsed gaps are included in the analytic domain.

`SourceAbelianUniformDiscFamily.lean` builds the common source ball
from the existing uniform tail and finite central contour family. Each
assigned disc has a smaller concentric radius enclosing its moving
segment uniformly on that ball. The larger discs are pairwise disjoint
and their closures avoid every unselected cut. Only finitely many
assigned discs differ from the free lattice discs; the new generic
`LocallyFiniteLatticeDiscs.lean` proves local finiteness and provides a
compact-set radius lemma. Thus the complement of all smaller closed
discs is one open exterior, and its product with the entire source ball
lies in the projected joint domain.

`SourceAbelianUniformSpectralContinuation.lean` extends that exterior
function into every cut disc at once and glues the spectral extensions.
The exterior and the cut discs are proved to cover the entire canonical
cut complement. This replaces per-gap source neighborhoods with one
source ball for the full infinite family.

`SourceAbelianUniformCollapsedFilling.lean` proves density of the cut
complement for arbitrary complex sources and uses dense limits to join
all analytic collapsed-gap fillings. The construction retains every
value off the cuts and the prescribed exterior values.
`SourceAbelianUniformRealNormalization.lean` proves that the exterior
is nonempty and that its real-source normalization determines the
filled primitive on the whole real spectral domain.

Public checks construct a single positive source radius at exponent
3/2 with full spectral analyticity, the actual derivative, and all index
shifts. They check arbitrary complex-source density, literal all-disc
coverage, and the complete free formula at every spectral point,
including all collapsed lattice gaps.

This supplies full spectral continuation on common almost-real source
neighborhoods, including collapsed-gap removal, toward Lemma 19.1(i).
The current theorem constructs spectral functions separately for each
complex source and supporting source ball, with fixed exterior values.
It does not yet identify all choices between different source balls or
with the earlier jointly analytic continued function throughout their
interior overlaps. Those compatibility and parameter-regularity steps
are next, together with uniform propagation of the exact complex
endpoint constants. The estimates in (iii), later frequency results,
and the full dissertation remain unfinished.

## Previous milestone: gluing interior discs and the exact potential gradient

The new `SourceAbelianContinuedPrimitive` joins the existing enlarged
exterior function to every normalized interior disc chart on one open
joint domain. Agreement holds on complete overlaps, including charts
for different selected gaps and different real-source centers. Every
previous exterior value and every established exterior product
neighborhood are retained.

`SourceFloquetJointDerivative.lean` derives the exact multiplier
differential at complex sources from the canonical-root identity.
`SourceAbelianCauchyDifferential.lean` propagates the Floquet exponential
identity from the normalized collar over the connected cut disc. The
zero-index continuation is then locally the exact normalized Floquet
logarithm. This proves its full joint differential `d Delta / canonicalRoot`,
including the potential gradient on the new interior domain.

`SourceAbelianDiscJointChart.lean` supplies normalized interior charts
on real-centered source balls inside one fixed analytic root neighborhood.
Such a chart exists for every selected gap at every real source in that
neighborhood, including collapsed gaps. Within each isolating disc its
only excluded spectral set is its own moving selected cut.
`SourceAbelianDiscCompatibility.lean` proves agreement with other disc
charts, old product charts, and the projected exterior function. For
distinct gaps, the two isolating discs jointly exclude all cuts along
the source projection path; continuous logarithm uniqueness fixes the
common value from the real-source normalization.

`SourceAbelianContinuedPrimitive.lean` glues this compatible family.
`SourceAbelianContinuedProperties.lean` proves joint analyticity, both
coordinate derivative formulas, the Floquet exponential identity,
signed-index shifts, the complete real-source normalization, and exact
endpoint limits `i (n-j) pi`. The selected-index square agrees with the
previous analytic filling across each entire local complex gap.

Public checks construct local coverage and the potential derivative
at exponent 3/2 for every real source and selected gap. They also check
negative-index endpoint normalization after gluing, free normalization,
and agreement between arbitrary overlapping disc charts.

This closes the local interior potential-gradient and chart-gluing
steps toward Lemma 19.1(i). The union is proved open, and the whole cut
disc is covered at every source in each chart's source ball. A single
almost-real source neighborhood giving full spectral coverage for all
gaps simultaneously still requires uniform tail and finite-core
arguments. The locally source-uniform and index-uniform estimates in
(iii), subsequent frequency results, and the full dissertation remain
unfinished.

## Previous milestone: exact complex endpoint normalization and filled squares

`SourceAbelianCauchyContinuation.lean` identifies the exact endpoint
values of the complex-source continuation: the normalized primitive
`F_n` tends to `i (n-j) pi` at both endpoints of the selected gap `j`.
The result includes collapsed gaps. Around every real source and
selected gap, one open complex-source neighborhood and one fixed
spectral collar work for every normalization index. The explicit
continued function agrees with the actual old joint primitive, and
with the enlarged primitive, on that entire collar.

`SourceAbelianCauchyPrimitive.lean` constructs the interior Cauchy
transform of the actual zero-index collar primitive divided by the
selected standard root. Its quadratic differential equation holds
throughout the disc. Multiplication by the root gives the exact
spectral derivative `Delta' / canonicalRoot` and zero limits at both
endpoints, even when they coincide.

`SourceAbelianCauchyChart.lean` supplies uniform charts at every real
source, including collapsed real gaps. The Cauchy quotient is jointly
analytic on the full disc times the source neighborhood. The additive
offset from the old collar function is therefore analytic in the source.
`SourceAbelianCauchyNormalization.lean` identifies its actual real-source
value as `-i j pi`; uniqueness from the real-source locus propagates that
value to complex potentials. This determines the constant without
assuming continuity or analyticity of the ordered complex endpoints.

The continued primitive is jointly analytic off the moving selected
cut, retains the exact spectral derivative and signed-index shift, and
agrees with the actual real-source primitive throughout each real slice.
`SourceAbelianCauchySquare.lean` proves that different charts for the same
gap agree on their complete cut-disc overlaps. It also constructs the
selected-index square explicitly as the endpoint polynomial times the
square of the Cauchy quotient. This square is spectrally analytic across
the entire complex gap, vanishes at both endpoints, and is independent
of the chart even at points on the filled cut.

Public checks cover constructed complex-source normalization at exponent
3/2, joint analyticity inside the disc, the relative sign for index -3
at gap 2, the full free quadratic formula through a collapsed gap, and
chart independence of the filled square.

This proves the exact local complex endpoint normalization and local
square continuation required in Lemma 19.1(ii) and (vi). The next step
is to glue the normalized local charts with the existing exterior
function across all isolating discs and obtain a common almost-real
source neighborhood. The full global complex-source spectral clause
of (i), the potential gradient on the new interior domain, locally
source-uniform and index-uniform estimates in (iii), subsequent
frequency results, and the full dissertation remain unfinished.

## Previous milestone: complex cut-disc continuation and endpoint limits

`SourceAbelianComplexDiscContinuation.lean` continues the actual
normalized joint primitive into a whole isolating disc minus its moving
complex spectral segment. Around each real source and selected gap,
one fixed annular collar, disc, and open complex-source neighborhood
work for every normalization index. A compact collar lies in the
existing joint domain; radial continuation preserves every value on
that collar and has the exact spectral derivative `Delta' / canonicalRoot`
throughout the cut disc. No open-gap assumption is required at the base
source or at its complex perturbations.

The continuation is uniquely determined by its derivative and one value.
Consequently it retains the signed index relation and the actual
real-source values throughout its cut disc. On the collar it also agrees
with the enlarged primitive from the preceding milestone.

`SourceAbelianComplexEndpointLimits.lean` proves a common weighted bound
at both endpoints of a nondegenerate complex gap. Its weight uses the
norm of the complex gap displacement, so tilted and vertical gaps are
included. Boundedness of the regular numerator and the standard-root
lower bound give finite limits along every approach in the full cut
disc, without a real-source or real-ordering hypothesis.

`SourceAbelianComplexCollapsedExtension.lean` fills a collapsed cut
analytically while preserving every previously defined cut-disc value.
The filled derivative is the regular deleted quotient. A single open
neighborhood of all real sources supports this removability and full
finite endpoint limits for all gaps. The combined local theorem gives
continued primitives with endpoint limits and collapsed-gap removal on
the same source neighborhood, simultaneously for all normalization indices.

Public checks cover the combined continuation at exponent 3/2, nonreal
gap displacements, the full free formula at an odd negative index, and
analytic filling of arbitrary complex-source collapsed-gap primitives.

The source neighborhood for the continuation still depends on the
selected gap. The next steps are to identify the complex endpoint
constants as the prescribed `i (n-j) pi`, and glue the local spectral
continuations consistently across all isolating discs. This does not
yet establish the full complex-source spectral clause of Lemma 19.1(i),
complex-source square continuation, the locally source-uniform and
index-uniform estimates in (iii), later frequency results, or the full
dissertation.

## Previous milestone: one enlarged domain over an almost-real source neighborhood

`SourceAbelianEnlargedExterior.lean` places all exterior continuations
in one open joint domain. There is an open connected neighborhood `V`
of the entire real-source locus such that every complex source in `V`
has a positive source radius and a fixed family of pairwise disjoint
isolating discs. The full unbounded exterior, including its boundary,
times that source ball lies in the same enlarged domain. The radius
works for every signed index, and all nearby spectral clusters stay
inside their assigned discs.

`SourceAbelianProjectedPrimitive.lean` normalizes each complex source
at its contractive real projection, then integrates the Floquet
logarithmic derivative along the straight source segment. The domain
where that entire segment avoids the canonical cuts is open.
`MovingSourceLogarithm.lean` proves joint analytic dependence of the
logarithmic integral on its moving anchor, spectral point, and terminal
source. Combined with real-source continuity, this gives a continuous
logarithm; local logarithm uniqueness then proves complex analyticity
even though the defining projection is only real linear.

`SourceAbelianProjectedCompatibility.lean` proves agreement with every
previous chart on its entire overlap, by following the projection path.
`SourceAbelianEnlargedPrimitive.lean` therefore unites the projected and
previously glued domains into one analytic function. It preserves all
previous complex-source values, the actual real-source normalization,
the signed index shifts, and the exact Floquet exponential identity.
Its full differential is `d Delta / canonicalRoot`; both the potential
gradient and the spectral derivative are proved explicitly. Every real
slice still contains exactly its full canonical-cut complement.

Public checks cover one common function over a connected source
neighborhood at exponent 3/2, uniform exterior analyticity and the
potential gradient at arbitrary complex base sources, preservation of
the entire old domain and function, the exact exponential and spectral
derivative, complete real-source slices, and free normalization at a
nonreal spectral point with an odd negative index.

This establishes the joint exterior-domain and gradient part of
Lemma 19.1(i) on one almost-real source neighborhood. The next step is
complex-source spectral continuation inside the isolating discs,
including removal at collapsed gaps and endpoint normalization.
The full complex-source spectral clause of (i), complex-source endpoint
and square continuation, the locally source-uniform and index-uniform
estimates in (iii), subsequent frequency results, and the full
dissertation remain unfinished.

## Previous milestone: uniform continuation over the full spectral exterior

`SourceAbelianExteriorProduct.lean` proves uniform exterior continuation
around every real source. One positive potential radius and one fixed
family of pairwise disjoint isolating discs work for every signed index
and the full unbounded spectral exterior, including its boundary.
The continued abelian integral is jointly complex analytic there, has
full differential `d Delta / canonicalRoot`, and retains the actual
normalization at every nearby real source. Every nearby spectral
cluster stays inside its assigned disc.

`SourceAbelianRadialPrimitive.lean` constructs this continuation by
integrating the Floquet logarithmic derivative along a straight source
segment, starting at the actual real-source primitive. Exponentiation
recovers the multiplier exactly; differentiating that identity gives
the full joint differential and the potential gradient. Continuous
logarithm uniqueness fixes the normalization throughout a convex
neighborhood of real sources.

`ParametricSourceLogarithm.lean` and `ParametricSourceLogDomain.lean`
supply the reusable Banach-parameter construction. The set of points
whose entire straight source segment stays inside an open analytic
domain is open, by compactness of the path parameter. This proves
analyticity at exterior boundary points without assuming that the
spectral exterior itself is open or bounded. All-index isolation keeps
the source paths away from every canonical cut at once.

`SourceAbelianRadialCompatibility.lean` identifies the continuation
with the previously glued joint primitive at every common complex-source
point in the exterior product. The proof uses
`ContinuousLogarithmUnique.lean` and
`SourceRealTypeLogarithmUnique.lean`: projection to real sources stays
inside both source balls, and the common exponential and real-source
normalization determine the logarithm throughout their overlap.

Public checks cover unrestricted exponential source transport, a common
radius over the unbounded exterior at exponent 3/2, the exact potential
gradient for arbitrary nearby complex sources and all indices,
compatibility with the glued primitive, nearby real-source values at
an odd negative index, and the complete free base-source formula.

This establishes the uniform exterior-domain continuation and gradient
around every real anchor in Lemma 19.1(i). The next step is to place these
extensions in one enlarged open joint domain over an almost-real source
neighborhood; the previously defined `sourceAbelianJointDomain` has not
yet been proved to contain these entire exterior products. Complex-source
endpoint and square continuation, locally source-uniform and index-uniform
estimates in (iii), subsequent frequency results, and the full dissertation
remain unfinished.

## Previous milestone: a single joint analytic abelian primitive

`SourceAbelianJointPrimitive.lean` constructs one chart-independent,
jointly complex-analytic normalized abelian primitive on an open union
of product neighborhoods. Its intersection with every real-source slice
is exactly that source's full spectral cut complement, and its values
there are the actual `F_0 + i n pi`. At every complex-source point of the
joint domain, its full differential is `d Delta / canonicalRoot`.
Changing the signed index adds exactly `i n pi`, and exponentiation
recovers the Floquet multiplier with its prescribed index factor.

`SourceAbelianJointChart.lean` proves compatibility for charts with both
different spectral anchors and different real-source anchors, on their
entire complex-source overlap. The real-part projection contracts
distances and fixes real sources, so projecting an overlap point stays
inside both chart balls. The actual real-source values agree there;
equality of joint derivatives extends this equality over the convex
overlap. The existing holomorphic-chart gluing construction then gives
the single primitive, independent of every local chart choice.

`SourceAbelianJointProperties.lean` proves the spectral derivative and
the potential derivative `partial Delta / canonicalRoot` for this glued
function. Every compact spectral subset off the cuts has an open
spectral neighborhood and one common complex-source ball contained in
the joint domain. This is uniform over the entire compact set and all
signed indices. The exact free-source formula is also retained.

Public checks cover complex-source overlaps between independently
anchored charts, inclusion and exact values on all real-source slices,
common product neighborhoods over arbitrary compact sets at exponent
3/2, complex-source derivatives and exponentiation, and an odd negative
free normalization at a nonreal spectral point.

This resolves complex-source chart compatibility and constructs the
joint primitive needed for Lemma 19.1(i). The remaining domain assertion
is a single source neighborhood over the full unbounded spectral
exterior of an isolating-disc family; compact-set uniformity alone does
not prove it. Complex-source endpoint and square continuation, locally
source-uniform and index-uniform estimates in (iii), subsequent frequency
results, and the full dissertation remain unfinished.

## Previous milestone: actual joint charts at every off-cut anchor

`SourceAbelianJointExtension.lean` removes the band-anchor restriction:
at every spectral point off the cuts of a real potential, one positive
product neighborhood supports jointly complex-analytic logarithm charts
for all signed indices. On every nearby real-source slice, each chart
equals the actual `F_0 + i n pi` throughout the complex spectral ball.
The full differential remains `d Delta / canonicalRoot`, including the
potential derivative at nearby complex sources. The actual primitive is
jointly continuous in complex spectral coordinate and real source at
every such point.

`SourceRootDomainConnected.lean` proves connectedness of the entire
real-source cut complement. Each nonempty vertical band strip joins the
two half-planes, and these regions cover the domain even when gaps have
collapsed. `ParameterContinuityPropagation.lean` gives a reusable
connected-set argument: continuity in a parameter at one anchor
propagates if differences at nearby spectral points are continuous.

`SourceAbelianSourceContinuity.lean` verifies that hypothesis for the
actual primitive. On a small spectral ball, actual increments equal
increments of a joint analytic chart because the additive constants
cancel. Starting from the exact band normalization, this proves source
continuity at arbitrary off-cut points. Normalized-log uniqueness then
fixes each chart at its anchor, and equality of spectral derivatives
extends the agreement over the whole ball. The previous band-chart
results are now specializations of the general theorems.

Public checks cover connectedness with all gaps collapsed, nonreal
anchors at exponent 3/2, a common product neighborhood for all indices,
exact potential derivatives at nearby complex sources, and agreement
of independently anchored charts on common real-source slices.

This advances Lemma 19.1(i) from band anchors to every off-cut spectral
anchor. Gluing the charts on complex-source overlaps and constructing
the stated product domain with one source neighborhood over the full
spectral exterior remain next. Complex-source endpoint and square
continuation, locally source-uniform and index-uniform estimates in
(iii), subsequent frequency results, and the full dissertation remain
unfinished.

## Previous milestone: normalized band charts for nearby real sources

`SourceAbelianBandChart.lean` proves that a local joint logarithm chart
is an actual extension of the normalized abelian integral for every
nearby real potential. At any real spectral band anchor there is a
positive-radius product of spectral and complex-source balls on which
all signed-index charts are analytic and have differential
`d Delta / canonicalRoot`. On every real-source slice they equal
`F_0 + i n pi` throughout the complex spectral ball.

`SourceAbelianRealBandValue.lean` fixes the exact band formula
`F_0(x) = P_n(x) - i pi/2 - i n pi`, where `P_n` is the existing
arcsine primitive. Its constant is determined by the actual endpoint
limit. `SourceAbelianBandSourceContinuity.lean` uses continuity of the
periodic endpoints to keep nearby points in the same band and proves
joint continuity of these actual values as real sources vary.
Normalized-log uniqueness fixes the chart at the real anchor for all
nearby real sources; equality of spectral derivatives then extends
this agreement across the spectral ball. The actual primitive is
therefore jointly continuous in complex spectral coordinate and real
source at every real band anchor.

Public checks cover an odd negative band index, joint continuity with
complex spectral coordinates, and a common product neighborhood at
exponent 3/2. The latter checks agreement for every nearby real source
and every index, together with the exact potential derivative at
arbitrary nearby complex sources.

This advances Lemma 19.1(i) by establishing normalization compatibility
as real sources vary near band anchors. Continuing these compatible
charts to arbitrary spectral anchors and assembling the full
complex-source product-domain primitive remain next. Complex-source
endpoint and square continuation, locally source-uniform and
index-uniform estimates in (iii), subsequent frequency results, and
the full dissertation remain unfinished.

## Previous milestone: local joint logarithm charts and exact differential

`SourceAbelianLogChart.lean` constructs local logarithm charts anchored
at the exact value of the real-source normalized abelian primitive.
For every spectral point off the cuts, an open neighborhood in the
joint spectral/complex-source space supports all signed indices at
once. Each chart is jointly complex analytic there, and its full
Fréchet differential is `d Delta / canonicalRoot`.

Restricting this differential gives both the spectral quotient and the
potential derivative `partial Delta / canonicalRoot` at every complex
source in the neighborhood. The chart agrees exactly with the existing
normalized primitive on the anchor real source's spectral germ.
Changing the index adds precisely `i n pi`, and exponentiation recovers
the Floquet multiplier with the exact corresponding exponential factor.

`NormalizedLogChart.lean` supplies a reusable local logarithm
`A + log(M/M(anchor))`, fixing the additive value even when the original
multiplier lies outside the principal slit plane. `SourceFloquetJointLog.lean`
proves joint analyticity of the actual multiplier and derives the
logarithmic differential from the canonical root's square identity.
The derivative formula applies throughout the complex-source analytic
domain whenever the normalized logarithm is on its slit plane.

Public checks use exponent 3/2, one neighborhood for all signed indices,
arbitrary nearby complex potentials in the potential and spectral
derivative formulas, an exact negative-index free-source germ, and
recovery of the multiplier by exponentiation.

This supplies local charts and the differential needed for Lemma 19.1(i).
It does not yet identify charts anchored at different sources with one
globally normalized complex-source primitive. That compatibility and
the full product-domain joint-analyticity assertion remain next.
Complex-source endpoint and square continuation, locally source-uniform
and index-uniform estimates in (iii), subsequent frequency results,
and the full dissertation remain unfinished.

## Previous milestone: analytic square across the selected gap

`SourceAbelianSquare.lean` constructs a chart-independent continuation
of `(F_0 + i n pi)^2`. It agrees with the actual normalized square on
the plane with only noncollapsed cuts removed, and is analytic after
adjoining the entire selected isolating disc. In particular, every
point of the selected closed gap is an analytic point, with no
open-gap or finite-gap assumption.

The generic `GapPrimitiveSquare.lean` theorem continues local
endpoint-normalized primitives onto regular square-root sheets.
Squaring cancels their root-ratio signs, so the local squares agree
on a dense subset and hence on overlaps. Zero endpoint limits and
the removable-singularity theorem fill the two remaining points.
`DenseAnalyticExtension.lean` supplies the reusable dense-limit and
finite-boundary extension results. The argument includes a collapsed
segment without dividing by its length.

`SourceAbelianDiscSquare.lean` applies this to the actual discriminant
quotient and its analytic regular numerator. The resulting global
square has zero values at both selected endpoints and equals the
squared real arcosh profile on the whole closed gap. At zero potential,
it is exactly the entire quadratic `-(lambda - n pi)^2`.

Public checks cover analyticity on the cut at exponent 3/2 and index
-3, positivity of the continued square in a real gap interior,
agreement of distinct isolating charts even on the cut, and the
shifted free quadratic at arbitrary complex spectral parameters.

This proves the real-source continuation assertion of Lemma 19.1(iv).
Extending the construction to the complex-source neighborhoods and
proving joint analyticity and the potential gradient in (i) remain
next. The locally source-uniform and index-uniform estimates in (iii),
subsequent frequency results, and the full dissertation are unfinished.

## Previous milestone: exact half-plane gap boundary values

`SourceAbelianGapBoundary.lean` proves the exact boundary formula
`F_n(x + i0) = arcosh((-1)^n Delta(x)/2)` and
`F_n(x - i0) = -arcosh((-1)^n Delta(x)/2)` for real sources.
The limits allow arbitrary approaches within the corresponding
half-plane. They hold on the entire closed gap, at every signed index
and every finite exponent `1 < p`, including collapsed gaps.

The proof first converts the transverse quotient estimate into an
integrable real endpoint weight. Dominated convergence then passes
partial displaced horizontal integrals to their exact arcosh values.
The fundamental theorem identifies these integrals with differences
of actual half-plane primitive values; endpoint normalization fixes
the additive constant. A local quotient bound at each interior gap
point upgrades the vertical limits to full half-plane limits.

The same formula is proved for the filled global primitive after
adding `i n pi`. Public checks exercise an odd negative index at
exponent 3/2, the negative lower-side value with the global index
correction, and the collapsed-gap limit from either half-plane.

This completes the real-source boundary assertion of Lemma 19.1(v).
The next step is continuation of the squared normalized primitive
across the selected gap, as in (iv). The complex-source construction,
joint analyticity and potential gradient in (i), locally source-uniform
and index-uniform gap estimates in (iii), subsequent frequency results,
and the full dissertation remain unfinished.

## Previous milestone: exact partial gap-side arcosh integrals

`SourceRealGapArcoshPrimitive.lean` defines the real arcosh profile
`arcosh((-1)^n Delta(x)/2)` on each canonical gap. It proves that the
actual upper canonical-root quotient is its derivative, with the
parity signs canceled exactly for every signed index. The profile is
continuous on the closed gap, zero at both endpoints, and strictly
positive in the interior.

Both actual side quotients are integrable across the endpoints.
Integrating from the left endpoint to any point of the closed gap gives
exactly the arcosh profile on the upper side and its negative on the
lower side. No integrability or open-gap hypothesis is required from
the caller; collapsed gaps are included.

`SourceRealGapArcoshBound.lean` proves that the profile is nonnegative
and bounded by `sqrt(g^2-1)`, where `g` is the signed half-discriminant.
The exact deleted-product factorization gives the quantitative bound
`profile(x) <= (gap length)/2 * sqrt(K)` whenever the real deleted
periodic product at `x` is bounded by `K >= 0`. Compactness supplies
one such finite `K` on every fixed closed gap.

Public checks cover an odd negative index at exponent 3/2, the strict
negative sign of the lower partial integral, a numerical deleted-product
bound yielding a full-gap-length norm bound, and the zero full-gap
integral without an open-gap assumption.

This proves the exact real side integrals used in Lemma 19.1(v) and a
quantitative ingredient for (iii). Identifying these side integrals
with the half-plane boundary limits of `F_n` remains next. The bound
proved here is for a fixed source and gap; local uniformity in the
source and uniformity in the index remain to be established. The
complex-source and joint-analyticity assertions, potential gradient,
square continuation, subsequent frequency results, and the full
dissertation remain unfinished.

## Previous progress: analytic extension through collapsed gaps

`SourceCollapsedGapNeighborhood.lean` proves that a collapsed gap is
an isolated missing point of the canonical cut complement. Its whole
isolating neighborhood belongs to the complement of the noncollapsed
cuts. This enlarged domain is open for every real source, without a
finite-gap assumption.

`SourceAbelianPrimitive.lean` inserts the limits of the global primitive
at the missing points. It agrees with the original function off all
cuts and has value `-i n pi` at either endpoint of gap `n`. Riemann's
removable singularity theorem proves complex analyticity through every
collapsed gap. The resulting primitive is analytic throughout the
plane with only the noncollapsed cuts removed.

`SourceAbelianPrimitiveProperties.lean` extends the exact Floquet
identity to this enlarged domain and identifies the derivative as
`sourceFloquetLogDerivative`, the regular multiplier logarithmic
derivative. It agrees with the literal `Delta'/canonicalRoot` away
from all cuts. Endpoint limits hold along all approaches in the
enlarged domain, and every smooth path there integrates the regular
one-form to the difference of primitive values. Such paths may pass
directly through collapsed endpoints.

At the free source, the enlarged domain is the whole plane and the
filled primitive is exactly the entire function `-i lambda`. Its
regular derivative is `-i` even at periodic lattice points, where the
literal quotient has zero denominator.

Public checks cover a collapsed negative-index gap at exponent 3/2,
the distinction between the regular derivative and literal quotient at
the free origin, a real path passing through three collapsed periodic
points, and endpoint limits without any gap-width assumptions.

This completes the collapsed-point extension for real sources. The
complex-source and joint-analyticity assertions of Lemma 19.1, its
potential gradient, gap-side formulas and estimates, and square
continuation remain to be proved. Subsequent frequency results and
the full dissertation remain unfinished.

## Previous progress: global real-source abelian primitive off the cuts

`SourceAbelianBandGluing.lean` constructs a quotient primitive on each
full vertical real-band strip which matches the zero-index primitive
on both half-planes. An existing corrected disc chart fixes the common
real value and hence removes the lower-half-plane constant ambiguity.

`SourceRealBandCoverage.lean` uses the bounded endpoint displacements
from `pi n` to find the greatest gap to the left of every real point
off the cuts. Thus the half-planes and band strips cover the entire
canonical cut complement, including both infinite spectral tails.

`SourceAbelianGlobalPrimitive.lean` glues these pieces into one function
for every real source at every finite exponent `1 < p`. It has the
actual derivative `Delta'/canonicalRoot` and is complex analytic on
the full cut complement. It agrees with every corrected isolating-disc
chart, independently of all local primitive and band choices.

`SourceAbelianGlobalProperties.lean` proves the full-domain endpoint
limits `F(lambda_n^±) = -i n pi` for all signed indices, including
collapsed gaps as boundary points. Every smooth path off the cuts
integrates the actual quotient to `F(b)-F(a)`; in particular, every
smooth closed path has zero period without a supplied homotopy.
The exact identity `exp(F) = (Delta + canonicalRoot)/2` holds everywhere
on this domain. At the free source the global function is `-i lambda`,
including its real band values.

Public checks cover the complex derivative at real band points for
exponent 3/2, an actual vertical path crossing from the lower to the
upper half-plane, a negative-index full-domain endpoint limit, and a
free real band value between collapsed gaps.

This constructs the global real-source abelian primitive off all cuts.
Analytically filling collapsed points is next; they are currently
excluded from this primitive's analytic domain. Joint source
analyticity, the remaining assertions of Lemma 19.1, the frequency
results, and the full dissertation remain unfinished.

## Previous progress: exact signed-index abelian normalization

`ContinuousBoundaryTransfer.lean` transfers a relative boundary limit to
closure points of a domain wherever a continuous extension is available.
`SourceAbelianBandTransfer.lean` extends each half-plane primitive across
an adjacent real-band strip and compares it with the actual arcsine
primitive. This fixes the boundary increment across every band at
exactly `-i pi`, on both sides of the real axis.

`SourceAbelianHalfPlaneNormalization.lean` proves the exact formulas
`F_n = F_0 + i n pi` and `F_n - F_m = i (n-m) pi` on both complete
half-planes, for arbitrary signed indices. At either endpoint of gap
`m`, the half-plane boundary limit of `F_n` is `i (n-m) pi`.
In particular, the zero-index primitive has value `-i m pi` there,
including when the gap is collapsed.

`SourceAbelianNormalizedCharts.lean` subtracts `i n pi` from each local
gap-normalized chart. The corrected charts retain the actual quotient
derivative and analyticity and agree with `F_0` on both half-planes.
Charts selected at different gap indices agree everywhere on their
common domain, including real overlap points. Their full chart-relative
endpoint limits have the prescribed value `-i n pi`.

Public checks exercise opposite signed indices at exponent 3/2,
negative-index lower-half-plane endpoint values, boundary limits for
both half-planes, and agreement of charts at different indices on the
real axis.

This establishes Lemma 19.1(ii)'s indexed half-plane constants for real
sources. Gluing across the entire real axis and filling collapsed
points remain next. Joint source analyticity, the remaining assertions
of Lemma 19.1, the frequency results, and the full dissertation remain
unfinished.

## Previous progress: exact adjacent-band improper integrals

`SourceRealBandGeometry.lean` identifies the nonempty real band between
consecutive canonical gaps and proves that it avoids every spectral cut.
The interval including its left endpoint still avoids all other gaps,
which permits continuation of the selected omitted root product.

`SourceCanonicalRootRealBand.lean` proves reality of the omitted product
at every real point of its domain. Continuity and nonvanishing carry its
known gap parity sign into the adjacent band. Thus the canonical root
is purely imaginary there, with sign `-(-1)^n`, and is exactly the
correspondingly signed positive square root of `4 - Delta^2`. The
actual real discriminant lies strictly between `-2` and `2` on the band.
These assertions include bands adjacent to collapsed gaps.

`SourceRealBandArcsin.lean` constructs the continuous arcsine expression
`i (-1)^n arcsin(Delta(x)/2)` and proves that its interior derivative
is the actual canonical quotient. Its left and right endpoint values
are `i pi/2` and `-i pi/2` for every signed index.

`SourceRealBandIntegral.lean` evaluates the actual quotient integral on
any compact subinterval, in either direction, with integrability derived
from continuity. Taking both endpoints independently to their adjacent
periodic endpoints gives the improper integral exactly `-i pi`.
An explicit positive cutoff realizes the same limit. No open-gap or
endpoint integrability hypothesis is imposed on the caller.

Public checks cover the actual improper integral at exponent 3/2, the
root orientation at an odd negative gap index, cancellation under
reversal of the integration direction, and the explicit free band
between `-3 pi` and `-2 pi`, where both neighboring gaps are collapsed.

This proves the real adjacent-band improper integral calculation used
in Lemma 19.1(ii). Transferring it to the half-plane primitives' boundary
constants, summing the increments to obtain `-i n pi`, and completing
global continuation remain next. Joint source analyticity and the other
remaining assertions of Lemma 19.1, the frequency results, and the full
dissertation remain unfinished.

## Previous progress: exact abelian logarithm and Floquet identities

`NormalizedLogarithmicPrimitive.lean` proves that an actual primitive
of a multiplier's logarithmic derivative exponentiates to that multiplier,
with its multiplicative constant determined by a boundary limit. No
principal-logarithm domain assumption is imposed.

`SourceFloquetEndpointLimit.lean` proves that the canonical root tends to
zero at either periodic endpoint along every approach off the cuts,
including at collapsed gaps. The actual Floquet multiplier consequently
tends to the signed index value `(-1)^n`.

`SourceAbelianFloquetIdentity.lean` identifies the exact exponential of
the normalized primitive on both complete half-planes and their joined
isolating-disc domain:

`exp(F_n) = (-1)^n (Delta + canonicalRoot) / 2`.

The opposite exponential equals the signed companion multiplier. Thus
`cosh(F_n) = (-1)^n Delta / 2` and
`sinh(F_n) = (-1)^n canonicalRoot / 2`, preserving the canonical sheet
orientation. The real part is exactly the logarithm of the multiplier's
modulus, independent of the chosen normalization index on common domains.
Near either endpoint the full continued primitive equals the principal
logarithm of the signed multiplier, because its zero boundary limit
selects the principal imaginary strip.

Public checks construct the local logarithm representation at exponent
3/2 without an open-gap assumption, verify both spectral signs at a
negative odd index on the real axis, compare real parts across different
normalization indices, and check the exact exponential at a free spectral
point far outside the local principal-logarithm chart.

This supplies the logarithm identity used in the proof of Lemma 19.1.
It does not yet construct the continuation across the rest of the real
axis or determine the full indexed `-i n pi` additive constants. Joint
source analyticity, the gap-side arcosh formula and estimates, and the
remaining assertions of Lemma 19.1 still require proof. The global
abelian integral, subsequent frequency results, and the full dissertation
remain unfinished.

## Previous progress: local gluing of normalized abelian primitives

`SourceAbelianDiscPrimitive.lean` uses the proved zero enclosing-circle
period to construct an actual quotient primitive throughout an isolating
disc minus the selected gap. Inverse-square-root endpoint estimates give
finite limits along every approach in this cut complement at open gaps.

`SourceAbelianDiscGluing.lean` fixes the left endpoint value to zero and
compares the resulting primitive with both independently normalized
half-plane primitives. The right endpoint value is consequently zero as
well. Collapsed gaps use the analytic removable extension of the actual
quotient. Every real source, signed index, and finite `p > 1` admits such
a normalized disc chart, and any two charts agree on their overlap.

`SourceAbelianLocalExtension.lean` joins both complete half-planes and
the isolating cut disc into one open domain and one analytic function.
It has the actual quotient derivative even at the newly included real
points, retains both zero endpoint limits on the whole joined domain,
and is independent of the chosen chart on overlaps. Every smooth path
inside this domain integrates the actual quotient to the function's
endpoint difference, including paths crossing the real axis.

Public checks construct the continuation at exponent 3/2, verify its
actual derivative and chart independence at real points, and evaluate
cross-half-plane path integrals at a collapsed free gap with negative
index. No open-gap or assumed primitive existence premise is needed for
the chart construction.

This completes the local gluing step around the selected gap in Section
19. Continuation across the rest of the real axis, the indexed `-i n π`
constants, joint source analyticity, and the remaining assertions of
Lemma 19.1 are still required. The globally normalized abelian integral,
frequency results, and full dissertation remain unfinished.

## Previous progress: normalized half-plane abelian primitives

`PrimitiveRemovableBoundary.lean` proves that a holomorphic extension
of a primitive's derivative through a boundary point gives a full relative
boundary limit. A prescribed common boundary value fixes the primitive
uniquely on a connected open domain.

`SourceAbelianHalfPlane.lean` constructs the endpoint-normalized abelian
primitive on each complete open half-plane for every real source, signed
gap index, and finite `p > 1`. Existing square-root estimates handle open
gaps. At a collapsed gap, the actual quotient's removable extension gives
a finite boundary value at the common endpoint. Subtracting that value
makes both endpoint limits zero. Uniqueness makes the values independent
of the primitive chosen during construction; no open-gap assumption is
required.

`SourceAbelianHalfPlaneProperties.lean` proves spectral analyticity and
identifies the primitive with the actual integral along every smooth
integrable connector from either selected endpoint into its half-plane.
The full normalized value commutes with exponent inclusion and is an
invariant of the original periodic spectrum with algebraic multiplicities.
At the zero source it is exactly `-i λ + i n π` on both half-planes for
every signed index, establishing Lemma 19.1(vi) on these domains.

Public checks verify the free normalization at a negative index above
the real axis and a positive index below it, compare independently chosen
primitives at exponents 3/2 and 3, and prove invariance under the actual
source phase rotation without an assumed isospectrality premise.

This begins Section 19. Gluing the half-plane constructions across the
real axis outside the open gaps, establishing the indexed `-i n π`
endpoint constants, joint source analyticity, and the remaining estimates
of Lemma 19.1 are still required. The complete globally normalized abelian
integral, subsequent frequency results, and the full dissertation remain
unfinished.

## Previous progress: Lemma 17.5 completed

`RealActionRotationOrbit.lean` proves that finite coordinate rotations
are dense in every prescribed action torus at every finite Banach
exponent, including `p = 1`. Equal-radius pairs differ by the difference
of their complex arguments, a formula that also handles radius zero.
Finite lists of these rotations match any finite target block exactly
while retaining the original tail. The resulting block replacements
converge in the full sequence norm, so the orbit closure is exactly the
action torus.

`SourceBirkhoffLemma17_5.lean` pulls the closed actual isospectral set
back through the global Hilbert inverse. It contains every finite
rotation orbit point, hence the entire coordinate torus by density.
Consequently, equal original Hilbert actions imply equality of the
original periodic spectrum and all algebraic multiplicities, without
a finite-gap hypothesis.

Inclusion into Hilbert space preserves the original actions and normalized
discriminant. This transfers the implication to every `1 < p ≤ 2`, with
a Hilbert normalized family constructed internally. Actual isospectral
sets are therefore exactly the original action level sets in this range.
Their Birkhoff images equal the whole prescribed action tori, and they
are compact in the original source norm. Together with the previously
proved inclusion for `p > 2`, this completes Lemma 17.5(i) and (ii).

Public checks cover full-norm finite-rotation approximation at `p = 1`,
exact matching of signed finite coordinate blocks at `p = 3`, construction
of a normalized family with a unique actual isospectral preimage for every
torus point at `p = 3/2`, and recovery of the entire discriminant and
algebraic multiplicities from the original actions below two.

Next continue into Chapter 4: the abelian integral `F` and its estimates
in Section 19, followed by the frequency analysis in Section 20 supporting
Theorem 18.1. Those results and the subsequent convexity and wellposedness
results remain unfinished. The full dissertation is not complete.

## Previous progress: complete isospectral Hilbert action flows

`RealActionRotation.lean` constructs a one-mode coordinate rotation at
every sequence exponent. Its selected velocity is `(-y_k,x_k)`, every
unselected coordinate is fixed, and every quadratic action is preserved.
The derivative exists in the full sequence norm for every real time.
Rotation times add, negative time reverses the motion, and a collapsed
selected action gives the constant curve.

`SourceBirkhoffActionHamiltonian.lean` differentiates the analytic
coordinate action-radius identity to obtain `dI_k = x_k dx_k + y_k dy_k`
at every point of the complex map domain, including closed gaps. The
proved canonical Poisson identities identify the original action
Hamiltonian's coordinate velocity with precisely this one-mode rotation
for every finite `p ≥ 2`.

`SourceHilbertActionRotation.lean` lifts the coordinate rotation through
the actual global Hilbert Birkhoff inverse. The inverse Jacobian proves
that its source-norm derivative is the original action Hamiltonian at
every time, with no open-gap hypothesis. Infinitesimal isospectrality
makes every fixed-parameter discriminant derivative zero, so the whole
normalized discriminant is constant along the complete curve. Therefore
the original periodic spectrum and all algebraic multiplicities are
preserved. Finite lists of rotations retain their exact coordinate
meaning and are isospectral, without restrictions on indices or times.

Public checks verify a quarter-turn at a negative index with the canonical
signs and an unchanged positive index, reversal by negative time, a
stationary source at zero original action, preservation of full spectral
data under norm limits of finite rotation sequences, and coordinate
action preservation at exponent 3.

Next prove that finite coordinate rotations approximate every point of
the prescribed Hilbert action torus. Continuity of the global inverse
and closedness of actual isospectral sets then give the converse torus
inclusion. Transfer to `1 < p < 2` remains after that. Lemma 17.5(i) and
the full dissertation are not yet complete.

## Previous progress: actual isospectral invariants and compactness

`PeriodicDiscriminantSpectralData.lean` proves that the original periodic
spectrum together with its algebraic multiplicities determines the
normalized discriminant at real-type even potentials. The canonical
endpoint product determines its square; the known endpoint value fixes
the sign, and analytic uniqueness gives equality everywhere. Conversely,
equality of discriminants recovers the original spectrum and every
algebraic multiplicity, without a reality assumption.

`SourceIsospectralSet.lean` defines actual isospectral sets using the
original operator spectrum and algebraic multiplicities. Equality of
discriminants characterizes membership and proves closedness in the
source norm at every finite `p > 1`. Common spectral data give identical
canonical roots and action-circle integrals. Comparing both definitions
on a common admissible circle proves equality of every full complex
indexed action, including closed gaps and the finite central block.

Consequently, the Birkhoff image of an actual isospectral set lies in its
prescribed action torus for every finite `p > 1`. This proves Lemma
17.5(ii). For `1 < p ≤ 2`, closedness inside the compact original action
level set proves compactness of the actual isospectral set, as asserted
in Lemma 17.5(i), with no finite-gap hypothesis.

Public checks cover invariance of full actions under the actual source
phase rotation at exponent 3, recovery of algebraic multiplicities from
discriminants at complex potentials, preservation of spectral data under
source-norm limits at exponent 3, and norm-convergent subsequences of
actual isospectral sequences at exponent 3/2.

The converse torus inclusion in Lemma 17.5(i) remains: lift Hilbert
coordinate rotations to the action Hamiltonian flows, prove they preserve
the discriminant, pass to limits of finite rotations, and transfer the
result to `1 < p < 2`. Equality of action level sets and actual isospectral
sets has not yet been proved. The full dissertation remains unfinished.

## Previous progress: compact action tori and source action level sets

`DominatedCompactness.lean` proves that a closed family of complex
coefficient sequences dominated coordinatewise by one finite-exponent
sequence is compact in the full norm topology. The existing uniform-tail
subsequence theorem supplies norm convergence. Continuous complex
inclusion and real projection give the corresponding real-sequence
criterion.

`RealActionTorus.lean` defines the torus with prescribed quadratic
actions `(x_n² + y_n²)/2 = I_n`. Coordinate evaluation proves closedness.
For any nonempty torus, one reference element bounds both components of
every other element by the sum of its own component magnitudes. This is
a summable majorant, so the torus is norm compact at every finite Banach
exponent, including `p = 1`. Empty tori and infinitely many nonzero actions
are covered. A zero action forces both corresponding coordinates to vanish.

`SourceActionTorus.lean` defines level sets of the original spectral
actions and identifies them exactly with preimages of the coordinate
action tori. These level sets are closed at every finite `p > 1` and
their images lie in the prescribed tori. For `1 < p ≤ 2`, surjectivity
gives equality of those images with the whole tori, and the global
homeomorphism makes the level sets compact in the original source norm.
No finite-gap or finite-support hypothesis is imposed.

Public checks cover compactness at exponents 1 and 3 for arbitrary action
sequences, the fully collapsed torus being exactly the zero target,
source-norm convergent subsequences with all actions retained at `p = 3/2`,
and a unique original source in the action level set for every point of
its coordinate torus.

This proves the compact-torus foundation for Lemma 17.5. The remaining
step is to identify these original action level sets with the actual
isospectral sets, including both directions of the Hilbert assertion
and its exponent transfer. Lemma 17.5 is not yet complete.

## Previous progress: global analytic inverse and open dense range

`SourceBirkhoffGlobalInverse.lean` bundles the actual real Birkhoff map
as a global homeomorphism for every `1 < p ≤ 2`. Its inverse agrees near
each target with the analytic local inverse of Proposition 17.1, hence
is analytic everywhere. Its strict derivative is exactly the inverse of
the original real Birkhoff Jacobian at the recovered source. Global
inverses commute with increasing the exponent within this range, even
for independently constructed normalized families. A family realizing
the bi-real-analytic diffeomorphism of Theorem 14.1(v) is constructed.

`SourceBirkhoffDenseRange.lean` proves that every finite output truncation
belongs to the actual real map's range at every finite exponent above
one. Below two this follows from Proposition 17.3. Above two the finite
block is realized in Hilbert space and the actual source is included
into the larger exponent; map compatibility gives exactly the desired
truncation. Norm convergence of finite truncations proves dense range.
Together with the existing open embedding, the image is open and dense
for every `1 < p < ∞`, as asserted in Theorem 14.1(iv).

Public checks construct the global analytic homeomorphism at `p = 3/2`,
verify that its inverse derivative inverts the original Jacobian at any
target, and compare its source Fourier coefficients with those of an
independently constructed Hilbert inverse. At `p = 3`, arbitrary targets
can be approximated in the full target norm by actual images, and every
finite truncation has an actual finite-gap preimage.

Next continue with Lemma 17.5: define the action tori, prove their
compactness, and identify the images of actual isospectral sets.
That identification and the remaining dissertation results are still
unfinished. Surjectivity for `p > 2` is not claimed.

## Previous progress: Proposition 17.3

`SourceHilbertFiniteActionReduction.lean` composes the actual Hilbert
angle flows in list order. Admissibility checks each nonnegative time
against the current selected action, so every move stops before collapse.
All actions are nonincreasing, and every unselected rectangular coordinate
is retained. The displacements sum to an element of every finite source
exponent above one. For `p ≤ 2`, this gives literal equality after inclusion
into Hilbert space and proves that an admissible finite sequence preserves
whether its source belongs to exponent `p`.

Finite-set induction constructs such a list making every selected action
smaller than any prescribed positive bound. Already small actions,
including closed gaps, are skipped. The resulting theorem also retains
every outside coordinate and supplies the displacement at all exponents.

`RealActionTail.lean` transfers finite coordinate blocks between arbitrary
real sequence exponents. A bound on their quadratic actions bounds the
block norm. Finite truncations of any target in a finite exponent converge,
so small enough actions on a suitable finite block, with the original
outside coordinates, yield a target of arbitrarily small norm in that
same exponent. The candidate can initially be given only in Hilbert space.

`SourceBirkhoffProposition17_3.lean` takes the Hilbert preimage of an
arbitrary exponent-`p` target. The constructed finite reductions put its
output inside the neighborhood of zero already in the range of the
exponent-`p` map. Exponent compatibility and Hilbert injectivity identify
the reduced source with this exponent-`p` preimage. The total displacement
then recovers the original source in exponent `p`. This proves Proposition
17.3 for every `1 < p ≤ 2`, without a supplied preimage or range premise.
Together with Proposition 17.2, a normalized family with bijective actual
real map is constructed throughout this range.

Public checks construct a family with a unique source for every target at
`p = 3/2`, apply different strict bounds to two signed modes while retaining
an unrelated mode, verify preservation of nonmembership in the stronger
source space, and exercise the inclusive endpoint `p = 2`.

Proposition 17.3 is complete. Next package the global analytic inverse
for `1 < p ≤ 2` and continue to the isospectral-torus statements of
Lemma 17.5. Surjectivity for `p > 2` is not claimed.

## Previous progress: complete Lemma 17.4

`ConjugateCotangentLinear.lean` makes conjugate-exponent cotangent
recovery a bounded complex-linear map. For source pairs it reconstructs
the Hamiltonian direction with the original Fourier reflection and Poisson
signs; its inclusion into Hilbert space is the original Hamiltonian.

`SourceHilbertAngleStrongRegularity.lean` applies this to the actual angle
cotangent. For conjugate exponents `p ≤ 2 ≤ q`, the Hilbert angle vector
has an exponent-`p` representative that depends analytically on the source
near every real source with its selected gap open. The identification
allows independently constructed normalized families at the two exponents.

`IntegralDisplacement.lean` proves a Banach-space integration result:
a continuous stronger-space representative of a curve's derivative
integrates to its displacement through a bounded linear inclusion. The
result holds on the entire interval before a positive terminal time,
including negative times.

`SourceHilbertAngleDisplacement.lean` uses that result for `1 < p < 2`
and continuous Hilbert inclusion for `p ≥ 2`. It constructs a continuous
curve in the actual real source space of every finite exponent above one,
with precisely the Fourier coefficients of the original flow displacement.
No membership of the initial Hilbert source in the stronger space is
assumed. The public theorem `lemma17_4` combines this with the initial
value, continuous differentiability, actual Hamiltonian equation,
uniqueness, and vanishing-action limit. Lemma 17.4 is now complete.

Public checks cover the sign and reflected frequency of an imaginary
cotangent at conjugate exponents 3 and 3/2, recovery of a negative-time
displacement by integration, and the exponent-3/2 realization of a
general Hilbert source's displacement. The constructed-family check now
includes every exponent's continuous displacement in the same theorem
as existence, uniqueness, and the action limit.

Next use finite successive action reductions and a small action tail
to prove Proposition 17.3 for `1 < p < 2`. That proposition and
surjectivity outside the Hilbert case are not yet complete.

## Previous progress: actual angle Hamiltonian flow and uniqueness

`SourceAngularThetaRectangularDifferential.lean` identifies the actual
branch-independent angle cotangent with `(-y_k dx_k + x_k dy_k)/(2 I_k)`.
The identity holds for every finite exponent above one and transfers
between independently constructed normalized families. Canonical Poisson
relations then give both rectangular velocities along the actual angle
Hamiltonian, including unselected closed gaps.

`SourceAngularThetaHamiltonian.lean` defines that Hamiltonian vector with
the original source Fourier reflection and Poisson signs. It proves
analyticity on the selected open-gap domain and preservation of the real
source form for exponents at least two.

`SourceHilbertAngleHamiltonian.lean` proves that the complex Birkhoff
Jacobian sends this vector to the explicit radial vector. Jacobian
injectivity identifies it with the previously constructed inverse-Jacobian
vector. The lifted action-reduction curve therefore solves the original
angle-Hamiltonian equation for all times before collapse; its selected
gap remains open throughout that interval.

`AutonomousODEUniqueness.lean` propagates local ODE uniqueness across a
preconnected open time domain. Smoothness only near the reference
trajectory is needed, without a global Lipschitz constant.
`SourceHilbertAngleFlowUnique.lean` applies this to prove uniqueness of
the actual Hamiltonian solution on the whole interval `(-∞, I_k(φ₀))`.
It packages the initial value, continuous differentiability, differential
equation, uniqueness, and vanishing-action limit for every real source
whose selected gap is open. Thus Lemma 17.4's initial-value statement
and part (i) are proved.

Public checks cover uniqueness for the nonglobally-Lipschitz scalar field
`x²`, the zero velocity of every nonselected mode at exponent 3, and the
construction of a normalized family with the full Hilbert existence,
uniqueness, and action-limit conclusions without supplied flow premises.

Lemma 17.4(ii) remains: the source displacement must be continuous in
every finite exponent above one. Next obtain the stronger-exponent
regularity of the angle Hamiltonian from its compatible cotangents and
integrate the vector field in that exponent. Proposition 17.3 and
surjectivity outside the Hilbert case are not yet complete.

## Previous progress: Hilbert action-reduction curves

`RealActionReduction.lean` constructs the explicit one-mode radial curve
in every real sequence space. For positive initial action `a`, the selected
coordinate pair is multiplied by `sqrt(1-t/a)`. Its action is exactly `a-t`
for `t ≤ a`; every other coordinate and action is unchanged. The curve is
continuous through collapse and smooth for all `t < a`, including negative
times. Its derivative solves the autonomous radial equation with velocity
`-(x_k,y_k)/(2 I_k)` in the selected mode.

`SourceHilbertActionReduction.lean` lifts that curve through the proved
global Hilbert Birkhoff inverse. The original spectral actions satisfy the
same exact reduction and conservation laws. The lifted curve starts at
the given source, is smooth before collapse, and solves the differential
equation whose vector field is the radial vector pulled back by the actual
inverse Jacobian. The derivative of the global inverse is explicitly
identified with that inverse Jacobian.

At the collapse time the curve converges in the source norm to an actual
source whose selected periodic gap is closed. Every other action remains
fixed. A further theorem chooses a finite nonnegative time strictly before
collapse at which the selected action is positive and below any prescribed
positive threshold.

Public checks cover the exact negative velocity of a 3-4 coordinate pair,
an unrelated nonzero mode, action growth at negative time, the source-space
differential equation, and the source-norm limit with its closed gap and
conserved other actions.

This completes the radial-curve construction needed for Lemma 17.4. The
identification of its pulled-back vector with the actual angle Hamiltonian,
uniqueness for that Hamiltonian equation, and continuity of the displacement
in every stronger exponent remain to be proved. Proposition 17.3 and
surjectivity outside the Hilbert case are not yet complete. Next establish
the Hamiltonian identification and stronger-exponent displacement estimate,
then use finite successive action reductions for Proposition 17.3.

## Previous progress: global Hilbert inverse and Proposition 17.2

`ClosedLocalHomeomorph.lean` proves that a closed local homeomorphism
from a Hausdorff space to a preconnected target is bijective whenever it
has one singleton fiber. The locus of fibers with at most one point is
both open and closed; the range is also open and closed. The proof applies
to infinite-dimensional spaces without local compactness assumptions.

`SourceBirkhoffLocalHomeomorph.lean` packages Proposition 17.1 as a local
homeomorphism for the actual real Birkhoff map at every finite exponent
above one. `SourceHilbertGlobalInverse.lean` combines this with Hilbert
properness and the singleton zero fiber to prove global Hilbert
bijectivity. It bundles the original spectral map as a homeomorphism and
proves its global inverse analytic at every target point by agreement
with the existing analytic local inverses. A normalized family realizing
this global real analytic homeomorphism is constructed.

`SourceBirkhoffProposition17_2.lean` discharges the Hilbert injectivity
premise in the existing exponent-extension argument. Proposition 17.2
is now proved for every `1 < p < ∞`. Each actual real Birkhoff map is an
open embedding. The proof above two uses finite-gap collision reduction;
below two it uses coefficient-preserving exponent inclusion.

Public checks give a unique source for every Hilbert target, verify
analyticity of the global inverse at arbitrary targets, eliminate
collisions at exponent 3, construct an injective family at exponent 3/2,
and verify openness of images of arbitrary open source sets.

The global Hilbert inverse and Proposition 17.2 are complete. Surjectivity
at other exponents is not claimed. Next is Proposition 17.3 for `1 < p < 2`,
including the action-angle flow and regularity argument of Lemma 17.4.
The remaining dissertation results are still in progress.

## Previous progress: bounded action continuity and Hilbert properness

`SourceActionSegmentCircle.lean` strengthens the common action contour:
one constructed circle stays outside every periodic cut along every point
of every eventual real interpolation segment. The construction works at
all finite exponents above one, including collapsed selected gaps.

`SquareRootPathStability.lean` proves a quantitative branch-preservation
lemma. A continuous root path anchored at its initial value cannot cross
the separating circle while its square stays close. Applied to the actual
jointly analytic canonical root and the proved discriminant limits,
`SourceCanonicalRootCoefficientContinuity.lean` gives uniform convergence
of the correctly normalized root on compact sets valid along the segments.
No replacement by a principal square root or unproved sign choice occurs.

`UniformInverseCompact.lean` supplies uniform inversion near compact nonzero
limits. `SourceActionCoefficientContinuity.lean` combines the canonical-root
and spectral-derivative limits to prove uniform convergence of the actual
critical-root quotient, then convergence of its weighted circle integral.
Every original indexed real Hilbert action converges under bounded
coefficient limits. The public theorem constructs its contour, requires
only first-component coefficient limits, permits countably generated
filters, and includes open and collapsed gaps.

`SourceHilbertProperness.lean` discharges
`SourceHilbertActionsContinuousOnBoundedCoefficients`. The action-mass
trace identity and coefficient compactness now prove properness of the
actual Hilbert action sequence map and the real Hilbert Birkhoff map,
without a separate spectral-continuity premise. An existence theorem
constructs a normalized family with both proper maps.

Public checks retain a negative root branch, construct segment-wide circles
at exponent 3, take action limits at collapsed gaps, verify the discharged
continuity obligation, and obtain compact preimages of arbitrary compact
Birkhoff target sets in the original source norm.

Hilbert properness and bounded-coefficient action continuity are complete.
Global injectivity and surjectivity, the global inverse, and the remaining
claims of Proposition 17.2 and subsequent chapters are not yet complete.
Next combine Hilbert properness with the proved local inverse and zero fiber,
then use exponent compatibility for the global Birkhoff conclusions.

## Previous progress: discriminant and spectral derivative coefficient limits

`UniformDualCoefficientLimits.lean` moves finite Fourier truncation across
the bilinear coefficient pairing and proves an explicit head/tail bound.
A bounded coefficient-null family pairs to zero uniformly against every
sequence dominated by one fixed finite-exponent majorant. This is a general
conjugate-exponent result; it does not require norm convergence of the input.

`SourceDiscriminantCoefficientContinuity.lean` applies that argument to the
actual two Hilbert cotangent coefficient sequences. Cotangent values on
bounded coefficient-null directions tend uniformly to zero over simultaneous
bounded source and spectral balls. Differentiating the actual discriminant
along straight real-parameter source segments and applying the mean value
bound gives uniform discriminant convergence on every bounded spectral set.
The theorem permits arbitrary filters and complex sources, with no real-type
condition or strong source-norm convergence. Pointwise and locally uniform
versions are exported.

`SourceDiscriminantDerivativeCoefficientContinuity.lean` applies the Cauchy
integral convergence theorem to obtain the same locally uniform and bounded-set
uniform convergence for the actual spectral derivative. Thus the numerator
of the action integrand now converges on every fixed common action circle.

Public checks cover both functions on arbitrary fixed circles, the real-source
specialization using only first-component coefficient limits, and reflected
unit Fourier modes whose source norms stay bounded away from zero while their
entire discriminants and spectral derivatives converge to the free functions.

Next prove convergence of the correctly normalized canonical square-root
branch on the common action circles, then pass to the quotient and action
integral. Convergence of the discriminant square alone does not choose a
square-root sign. `SourceHilbertActionsContinuousOnBoundedCoefficients`,
unconditional properness, and Proposition 17.2 remain unfinished.

## Previous progress: uniform Hilbert discriminant cotangent tails

`ClassicalDiscriminantGradientEnergy.lean` bounds the actual physical
discriminant gradient and its transported diagonal term by cubic solution
growth controlled by integrated potential energy. The time derivative has
an integrable potential factor. Its integral norm, and hence every Fourier
coefficient of either gradient component, is bounded by the same energy-only
constant. The estimate includes frequency zero and imposes no physical
supremum bound. The generic Fourier estimate now accepts an integrated
derivative bound; its previous supremum-bound API is retained.

`SourceDiscriminantCotangentDecay.lean` transfers that estimate through exact
finite-source realization and density to every complex Hilbert source.
Both actual cotangent coefficient sequences satisfy an explicit bound of
the form `C(M,R)/(1+|n|)` on simultaneous source-norm and spectral balls.
One square-summable majorant controls the entire family. The reusable
`DominatedTails.lean` theorem then gives uniformly small Fourier tails:
the finite cutoff is chosen before the potential and spectral parameter,
and every larger cutoff works for both components.

Public checks cover the tail criterion at exponent 3, the zero-frequency
cotangent direction, the physical Fourier normalization, and a common
cutoff for arbitrary bounded complex source families with moving spectral
parameters. No real-type condition or coefficient convergence is needed
for these uniform estimates.

Next use the uniform cotangent tails along bounded interpolation segments
to prove discriminant continuity under coefficient limits, then control its
spectral derivative and the canonical-root branch on common action circles.
`SourceHilbertActionsContinuousOnBoundedCoefficients` remains unproved;
unconditional properness and Proposition 17.2 remain unfinished.

## Previous progress: canonical coefficient continuity and common action circles

`BoundedSegmentLimits.lean` proves that interpolation from a fixed vector to
a bounded family stays bounded and that every converging linear coordinate
converges uniformly along those segments. `SourceSegmentResolventPersistence.lean`
then proves eventual common resolvent membership on any compact spectral set
for every point of every segment, with one eventual index for all parameters.

`SourceSpectralSelectionCoefficientContinuity.lean` upgrades strong continuity
of any periodic eigenvalue selection on real sources to continuity under
bounded coefficient limits. Spectral discreteness supplies arbitrarily small
circles around the limit value. Along each real interpolation segment the
selection is continuous and cannot cross the common spectral-free circle.
This retains its original label without assuming a common cluster assignment.

`SourceCanonicalCoefficientContinuity.lean` applies that argument to both
actual canonical periodic endpoints. Every fixed original indexed endpoint,
midpoint, and gap converges at every finite `p>1`, including closed gaps.
The real-type Fourier relation makes first-component coefficient convergence
sufficient. These theorems allow arbitrary filters and do not assume strong
convergence, an externally chosen contour, or a positive gap.

`SourceActionCoefficientCircle.lean` constructs one real-centered circle for
each selected action, valid at the limit and eventually for the family. The
selected segment stays inside, and convergence of adjacent endpoints plus
global real spectral ordering keeps every other gap outside the closed disc.
The actual indexed actions therefore use this same circle, including at
collapsed gaps. Convergence of their integrands is not yet proved.

Public checks cover uniform segment persistence for complex sources, actual
indexed gap convergence at exponent 3, construction of a common Hilbert action
circle, and real sources formed from moving reflected unit Fourier modes.
Those sources have norms bounded away from zero while both actual canonical
endpoints at every fixed index converge to the corresponding free value.

Next prove convergence of the critical-root quotient on the constructed
common action circles. `SourceHilbertActionsContinuousOnBoundedCoefficients`
remains unproved; unconditional properness and Proposition 17.2 remain
unfinished. The previously planned global indexed-pair continuity step is
now complete for bounded coefficient limits of real sources.

## Previous milestone: spectral trace and ordered eigenvalue limits

`ContourOperatorCoefficientConvergence.lean` identifies the bounded spectral
restriction `L P` with the first weighted resolvent integral. Every continuous
scalar weight on a spectral-free limit circle preserves operator-norm
convergence of the integrals under bounded coefficient limits. In particular,
the bounded spectral restrictions converge, without assuming norm convergence
of the original potentials or their unbounded operators.

`ContourTraceCoefficientConvergence.lean` transports each varying contour
range to the fixed finite-dimensional limit range. The transport tends to the
identity, the reduced operators converge in norm, and continuity of trace on
this fixed space proves convergence of every intrinsic power trace. The
contour midpoint and squared-gap expressions consequently converge as well.

`RealSpectralPairCoefficientConvergence.lean` reconstructs an ordered real
rank-two eigenvalue pair from the midpoint and the nonnegative square root of
the squared gap. Both endpoints converge, including when they coincide at the
limit. This theorem explicitly assumes that the specified pair eventually
exhausts the chosen circle; it derives eventual rank two from the limit rank.
A separate unconditional corollary at a zero coefficient limit proves
midpoint limit `π n` and squared-gap limit zero in every fixed free disk.
`SourceSpectralTraceCoefficientConvergence.lean` exports the restriction,
power-trace, symmetric-expression, and ordered-pair limits in period-one
source coordinates. The convergence theorems cover finite `p>1` and countably
generated filters; the weighted restriction identity also covers `p=1`.

Public checks cover a cubic resolvent weight at exponent 3, arbitrary source
power traces, ordered endpoints converging to a double eigenvalue, and moving
unit Fourier modes whose norms stay one but whose fixed-disk midpoint and
squared gap converge to the free values.

The global indexed pair identification and continuity of the critical-root
quotient and individual actions under bounded coefficient limits remain.
`SourceHilbertActionsContinuousOnBoundedCoefficients` is still unproved;
unconditional properness and Proposition 17.2 remain unfinished.

Next prove compact resolvent-set persistence uniformly along the real line
segments from the limit source to the approximating sources. These segments
remain bounded and converge coefficientwise to the same limit, uniformly in
the segment parameter. Existing strong continuity of canonical endpoints
along each segment should then prevent them from crossing an isolating
circle, supplying the missing global indexed-pair identification. This is a
planned proof route, not yet a formalized result.

## Previous milestone: compact spectral convergence and cluster stability

`ResolventReferenceChange.lean` factors the spectral pencil through a full
resolvent at any common reference point. Invertibility of the bounded transition
operator characterizes the entire resolvent set. Operator-norm convergence at
the reference point therefore gives eventual spectral membership and resolvent
convergence at every limit resolvent parameter, including moving parameters.
This reference-change result also covers the endpoint exponent `p=1`.

`ResolventCompactConvergence.lean` upgrades this to locally uniform convergence
on the limit resolvent set and eventual common spectral membership on each
compact subset. The previously constructed high reference point supplies these
conclusions for every bounded coefficientwise convergent family at finite
`p>1`. On every spectral-free limit circle, the normalized contour projections
converge in operator norm. The contour limit theorem uses a countably generated
filter, including ordinary sequences.

`SpectralClusterCoefficientStability.lean` proves eventual equality of the
finite projection ranks and hence of the total enclosed algebraic
multiplicities. Eigenvalues may split or coalesce inside the circle.
`SourceSpectralCoefficientConvergence.lean` supplies the corresponding
compact-set, contour, rank, and multiplicity theorems in period-one source
coordinates, without an assumption of strong convergence of the potentials.

Public checks cover reference transport at `p=1`, uniform convergence on
arbitrary compact sets at source exponent 3, preservation of a cluster with
multiplicity two, and convergence of contour projections for moving unit
Fourier modes whose potential norms do not tend to zero.

Next identify the limiting indexed spectral data and prove continuity of
individual actions under bounded coefficient limits.
`SourceHilbertActionsContinuousOnBoundedCoefficients` remains unproved;
unconditional properness and Proposition 17.2 remain unfinished.

## Previous milestone: norm-resolvent limits from bounded coefficient limits

`ConvolutionSandwichCoefficientContinuity.lean` views two-sided convolution
as a linear map from potentials into bounded operators. Cutting off both
multiplier symbols leaves dependence on only finitely many potential
coefficients. The cutoffs converge in operator norm, proving compactness of
the potential-to-operator map and its continuity along bounded coefficientwise
limits whenever the conjugate symbol exponent is finite.

`DoubleResolventCoefficientContinuity.lean` identifies the existing double
free resolvent with a pair of these convolution sandwiches. Consequently
`R₀ Φ R₀ : FLᵖ → FL¹` converges in operator norm under bounded coefficientwise
convergence of potentials, at each fixed parameter off the free lattice.
The theorem is also provided in the actual period-one source coordinates.

`NeumannResolventCoefficientContinuity.lean` retains summable output for the
full Neumann resolvent. Its fixed-point equation bounds the difference of
two full resolvents by the difference of their double free resolvents, with
a common positive Neumann margin. The existing height-decay estimate then
constructs this margin uniformly on every bounded family. For every bounded
coefficientwise convergent family, a positive height is constructed above
which every full resolvent exists and converges in operator norm. The theorem
covers all finite exponents `p>1`, complex potentials, and period-one source
pairs; no externally supplied spectral-membership or smallness premise is
needed in the final common-height statement.

Public examples verify compact potential dependence, convergence for moving
unit Fourier modes whose source norms stay one, the double-resolvent result
at exponent 3, the explicit full-resolvent difference estimate, and the
constructed common-height result for actual Hilbert source pairs.

Next propagate this norm-resolvent limit from the common high region to
spectral contours and prove continuity of the spectral data and individual
actions. `SourceHilbertActionsContinuousOnBoundedCoefficients` is still an
unproved obligation; unconditional properness and Proposition 17.2 remain
unfinished.

## Previous milestone: coefficient compactness and the properness criterion

`CoefficientCompactness.lean` proves that every bounded sequence of Fourier
coefficients has a coefficientwise convergent subsequence with a limit in the
same `ℓᵖ` space, including `p=∞`. The proof combines compact coordinate balls
with the sequence-space bound on pointwise limits. For `ℓ²`, an exact Fourier
truncation energy identity upgrades coefficientwise convergence to norm
convergence whenever the squared norms converge to the limit's squared norm.

`SourceHilbertCoefficientCompactness.lean` carries this construction to real
sources, preserving the conjugate-reflection relation. The first component
determines the second, and the original Hilbert pair norm has exactly twice
the first component's squared norm.

`SourceHilbertActionPropernessCriterion.lean` uses the proved trace identity
to show that bounded action sequences have bounded source preimages and that
convergence of actions rules out energy loss at a coefficientwise source
limit. It then proves compactness of preimages of compact action sets, and
hence properness of both the action map and the real Birkhoff map, conditional
on `SourceHilbertActionsContinuousOnBoundedCoefficients`.

That named proposition is an explicit, still unproved spectral obligation:
each individual real action must converge along bounded, coefficientwise
convergent real Hilbert source sequences. The compactness, boundedness, and
strong-convergence parts are proved; unconditional properness and Proposition
17.2 are not yet claimed.

Public examples include moving unit Fourier modes: their coefficients tend
to zero while their norms stay one. This checks the essential distinction
between coefficient compactness and norm compactness. Further examples cover
real-source extraction at exponent 3, the exact action norm, the strong-limit
upgrade, and the conditional properness theorems.

Next prove the named spectral continuity obligation from continuity of the
spectral data under bounded coefficient limits, then apply the properness
criterion and the singleton zero fiber toward global invertibility.

## Previous milestone: the full Hilbert action–mass trace formula

`SourceRealActionRealCenteredCircle.lean` proves that every real-centered
isolating circle computes its indexed real action, including collapsed gaps,
at every finite exponent `p>1`.

`SourceFiniteGapActionTrace.lean` applies finite-hole contour decomposition
to the weighted, regularized logarithmic derivative around the finitely many
open gaps. The individual circles compute the actions, and the exterior
circle computes source mass. Thus the finite action sum equals source mass;
analyticity through collapsed gaps handles all other spectral points.

`SourceHilbertActionTrace.lean` extends this equality by continuity and
actual finite-gap density to every real Hilbert source. In the repository's
pair normalization, the resulting formula is

`∑ₙ Iₙ(φ) = ‖φ‖²/2`.

The public theorem `sourceHilbert_sum_actions_eq_half_norm_sq` needs neither
a finite-gap assumption nor a chosen Birkhoff family. For every constructed
Hilbert Birkhoff family, the squared norms of its two real output components
sum to the squared source norm. Consequently its zero fiber is exactly `{0}`.

Public examples cover a real-centered circle at exponent 3, the vanishing
of a finite-gap source with no open gaps, the unconditional infinite trace,
the zero-fiber consequence, and the two-component norm identity.

The action/mass trace identity is now proved. Weak continuity of the spectral
actions and properness of the action map remain next steps toward Proposition
17.2 and global injectivity; the norm identity alone does not prove properness.

## Previous milestone: mass identification and the evaluated exterior contour

The analytic remainder's local primitive now gives an exterior primitive
with coefficient `2i h(0)`. Comparing it with the mass-normalized actual
primitive proves `h(0) = -i sourceHilbertMass/2`. Thus every sufficiently
large weighted contour of the regularized quotient equals `π` times source
mass, or equivalently `π ‖φ‖²/2`, for real Hilbert finite-gap sources.
All auxiliary regularity, normalization, and coefficient premises are
fully discharged.

Next identify the finite collection of isolating-circle integrals with the
indexed real actions and apply finite-hole decomposition to their weighted
regularized quotient. This will give the finite-gap action/mass trace
identity; the existing continuity-and-density theorem extends it to every
real Hilbert source. Spectral-action weak continuity and properness remain
later steps toward global injectivity.

## Previous progress: exact exterior remainder and contour coefficient

The analytic inversion germ now has zero linear coefficient, proved from
the actual zero exterior period. Two divided differences produce an exact
analytic remainder: `q(z) = -i + z⁻² h(1/z)`. The weighted exterior circle
integral is exactly `2πi h(0)`, at all finite exponents `p>1` for actual
finite-gap sources, without any assumed residue or expansion coefficient.

Next take a primitive `H` of `h` near zero with `H(0)=0`. Then
`-iz-H(1/z)` has derivative `q(z)` on the exterior. Compare it along the
upper imaginary ray with the already mass-normalized exterior primitive;
the ray limit should give `h(0) = -i sourceHilbertMass/2`. Finally consolidate
the individual action contours. Density extension, spectral-action weak
continuity, and properness remain later steps toward global injectivity.

## Previous progress: removability and the leading value at infinity

The logarithmic derivative is now uniformly bounded on sufficiently large
half-integer circles by the free derivative and root asymptotics. Maximum
modulus extends that bound over a full exterior region. At finite-gap sources,
inversion and the removable-singularity theorem construct an analytic germ
at infinity, with the exact leading value `-i`. These conclusions hold for
every finite exponent `p>1`, without extra analytic or quantitative premises.

Next extract the higher coefficients of this analytic germ. The established
zero exterior period should remove the inverse-frequency term; compare the
next coefficient with the mass-normalized exterior primitive's ray limit.
Then evaluate the weighted contour to prove the finite-gap action/mass trace
identity. Density extension, spectral-action weak continuity, and properness
remain subsequent steps toward global injectivity.

## Previous progress: the mass-normalized exterior primitive

The finite-hole contour theorem and actual disjoint isolating circles now
prove zero period for the regularized quotient on every sufficiently large
circle. A general circular-hole filling argument constructs a primitive on
the whole exterior. This supplies the actual finite-gap exterior primitive
at every finite `p>1`, without period or contour-geometry assumptions.
At the Hilbert exponent, one additive correction gives this same primitive
the exact coefficient `2y (F(iy)-y) → ‖φ‖²/2` on the upper imaginary ray.

Next combine the existing exterior discriminant-derivative and canonical-root
asymptotics on large circles separated from the free lattice. Use those
bounds to establish removable-singularity control for the exterior quotient
at infinity, so that the ray coefficient determines a Laurent coefficient.
Then consolidate and
evaluate the weighted action contours to prove the finite-gap action/mass
trace formula. Its density extension, spectral-action weak continuity,
and properness remain later steps toward global injectivity.

## Previous progress: the finite-gap exterior spectral functions

The canonical root and Floquet multiplier now extend analytically through
all collapsed gaps at every real source and finite exponent `p>1`. The
multiplier stays nonzero, and its logarithmic derivative is the analytic
extension of `Δ'/root`. For finite-gap sources, compactness of the finite
union of open-gap segments gives a full exterior region of analyticity.

Next establish zero exterior period for the filled quotient, construct its
exterior primitive, and match it to the mass-normalized upper primitive.
Then control the expansion at infinity and consolidate the action contours
to prove the finite-gap action/mass trace identity. A vertical-ray limit
alone still does not suffice. Density, spectral-action weak continuity,
and properness remain later steps toward global injectivity.

## Previous progress: the mass-normalized upper primitive

The canonical Floquet multiplier is analytic and nonzero off the gap cuts;
its local logarithmic derivative is the actual quotient `Δ'/root`. The root's
upper normalization fixes its sign, and its square identity transfers the
source mass coefficient to the root and multiplier. The eventual principal
logarithm satisfies `2y (log multiplier(iy)-y) → sourceHilbertMass φ` for
absolutely summable real Hilbert sources. Matching any global upper-half-plane
primitive to the logarithm up to a constant constructs a mass-normalized
primitive on the entire upper half-plane. At real finite-gap sources its
coefficient is exactly `‖φ‖²/2`, with no remaining regularity assumption.

Next continue this primitive across the closed gaps to an exterior domain
containing only finitely many open cuts. Prove the required expansion at
infinity, using global growth or removable-singularity control; the vertical
coefficient limit alone is not a contour asymptotic. The library has annular
zero-period primitives and the root derivative identity available. Consolidate
the finite action contours and identify the contour coefficient to establish
the finite-gap action/mass trace formula. The existing density reduction then
extends it to every real Hilbert source. Spectral-action weak continuity and
properness remain subsequent obligations for global injectivity.

## Previous progress: the canonical finite-gap source mass coefficient

Absolute period-one Fourier synthesis now gives the actual continuous
representative and exact physical/source mass equality by bilinear
Parseval. The canonical discriminant of every absolutely summable complex
Hilbert source recovers `sourceHilbertMass` as its first upper coefficient.
The finite-gap Sobolev bootstrap discharges summability, giving the exact
limit `2y (exp(-y) Δφ(iy)-1) → ‖φ‖²/2` for real Hilbert finite-gap sources.
Equal canonical discriminants consequently give equal source norms there.

Next recover the same first coefficient for the canonical root and the
Floquet multiplier `(Δ + root)/2`. The existing root/free asymptotic uses
`-2i sin(z)`, positive along the upper imaginary ray, and the square identity
`root² = Δ²-4` fixes the difference from the discriminant at this order.
Establish the logarithmic multiplier's derivative `Δ'/root` and match it
to the existing half-plane primitive, retaining its additive constant.
Then consolidate the finitely many action contours into an exterior contour
to prove the finite-gap action/mass trace identity. The established density
reduction extends that identity to all real Hilbert sources. Weak continuity
of spectral actions and properness remain subsequent obligations.

## Previous progress: the first high-energy mass coefficient

For every continuous complex potential, the actual classical discriminant
now satisfies `2y (exp(-y) Δ(iy) - 1) → ∫₀¹ φ₁ φ₂`. The proof isolates an
explicit quadratic Volterra term with an inverse-square remainder, then
uses an exponential approximate identity and dominated convergence. The
remainder estimate is uniform in the real spectral part. Equal classical
discriminants therefore have equal physical masses.

Next use the existing H¹ realization of finite-gap sources and the
classical/canonical discriminant identification to transport this limit.
Prove the Fourier/physical mass identification with the original source
normalization. Then identify the inverse-frequency coefficient of the
canonical discriminant-ratio primitive and combine finite action contours
into an exterior contour to establish the finite-gap trace formula.
The analytic action-sum density reduction is already available. After the
trace identity, prove weak continuity of spectral actions and action-map
properness to finish the remaining Hilbert global injectivity argument.

## Previous progress: analytic ℓ¹ Hilbert action map

The actual action sequence is now holomorphic into complex ℓ¹ on its
constructed domain and real analytic into real ℓ¹ on all real Hilbert
sources. Both sums converge absolutely; directional derivative sums
converge absolutely and equal the derivative of the total. The real
total equals half the sum of the two Birkhoff output norm squares.
The source-mass identity is reduced, by actual finite-gap density, to
its finite-gap case. Properness of the actual action map transfers to
the actual Birkhoff map. The missing trace and properness premises
remain explicit.

Next prove the finite-gap action/mass identity. Consolidate the finitely
many action contours into an exterior contour, integrate the canonical
discriminant-ratio primitive, and identify its inverse-frequency
coefficient with the physical mass. The required mass correction is
stronger than the existing leading half-plane asymptotic. Then obtain
weak continuity of the spectral action coordinates and use the trace
formula to prove action-map properness. Do not replace these actual
spectral assertions with assumed properness or a norm identity.


## Previous progress: global injectivity reduced to Hilbert finite-gap sources

The full exponent-extension step of Proposition 17.2 is proved. Nonlinear
output support equals the open-gap set. Any collision is approximated,
in arbitrary neighborhoods of its two distinct sources, by a finite-gap
collision over one finite output truncation. Above two, finite-gap
Hilbert realizations and full map compatibility lift this collision to
Hilbert space; below two, direct inclusion transports it. Thus global
injectivity for every finite `p>1` follows from injectivity on Hilbert
finite-gap sources. All premises on that missing Hilbert result remain
explicit. The reduction does not assert Proposition 17.2 itself.

Next establish the missing Hilbert finite-gap injectivity result, or
formalize the cited global Hilbert theorem [23, Theorem 19.3]. Reuse the
proved finite-gap reduction to avoid redoing exponent extension. Neither
local invertibility nor density by itself proves this remaining global
uniqueness assertion. Continue with Proposition 17.3 only once this
prerequisite has been addressed or its dependencies made explicit.



A primary reference for the missing Hilbert argument is Grébert–Kappeler–Pöschel,
[Normal Form Theory for the NLS Equation, Global Diffeomorphism section](https://arxiv.org/html/0907.3938#Ch2.S7).
It proves properness of the action map from the action-sum/norm identity,
weak continuity of spectral data, and weak convergence plus convergence
of Hilbert norms. Properness, local invertibility, and the singleton zero
fiber then give global bijectivity by connectedness. This is a concrete
alternative to finite-gap inverse spectral reconstruction. The actual
action-sum identity and weak-continuity prerequisites have not yet been
located in the current library; establish them with the repository's
period and pair-norm normalization before applying this route.

## Previous progress: Proposition 17.1 for every 1 < p < ∞

Proposition 17.1 is complete for the constructed actual Birkhoff family.
The full sequence Jacobian commutes with exponent inclusion, for any two
constructed families. Below two, Hilbert injectivity and injectivity of
the source inclusion give a trivial kernel. Compact normalization and
the Fredholm alternative give bijectivity. Real/complex derivative
compatibility transfers this to the actual real spaces. Both complex
and real analytic local inverses now exist at every real source for
all finite `p>1`, with both inverse identities and the exact derivative.

Next address Proposition 17.2, global injectivity. First identify or
formalize the Hilbert global injectivity result used by the dissertation,
then transport injectivity across exponents using the established local
inverses and compatibility. Do not assume that external theorem as an
axiom or conclude global injectivity from local invertibility alone.


## Previous progress: Proposition 17.1 for 2 ≤ p < ∞

The actual complex and real Jacobians are now bounded isomorphisms at
every real source for `2≤p<∞`. Canonical Hamiltonian directions supply
preimages of all finite output modes; truncation gives dense range, and
the compact perturbation gives bijectivity. Differentiation of the real
inclusion and the source real/imaginary decomposition give real
bijectivity. The inverse function theorem supplies analytic complex and
real local inverses, including both local identities and inverse derivatives.
A constructed-family theorem supplies the actual real local inverses.

Next extend Jacobian injectivity to `1<p<2`, using compatibility with
the Hilbert exponent and its established invertibility, then apply the
compact Fredholm alternative. The real derivative inclusion is already
available at every finite exponent above one. Finish Proposition 17.1
across the full exponent range before continuing with global injectivity.


## Previous progress: Lemma 16.3 at every real source

Theorem 15.2, Lemma 15.3, the free Fourier Jacobian identity, and finite-gap
regularity in all nonnegative Sobolev weights (including H¹) are complete.
Appendix G.3–G.4, finite-p G.5, and both G.6 assertions are proved for
constructed physical H¹ potentials. G.5's printed infinite endpoint is
refuted and stays excluded.

The actual discriminant-gradient disc suprema have common outer ℓp bounds
on H¹ balls. The contour quotient is now controlled as well: for every
`0<r≤π/2`, one cutoff gives a positive lower bound on `|Δ²−4|` and a
uniform bound on `|Δ/(Δ²−4)|` at every point of every distant circle.
The literal quotient-weighted gradient Fourier integrand has a common
summable majorant for finite `p>1`, `q>1+1/p`, including the conjugate
exponent. No pole-avoidance or denominator lower-bound premise is supplied.

The actual midpoint derivatives now form an outer ℓp sequence in source
operator norm at every H¹ potential in a common open neighborhood of the
real locus, for finite `p≥2`. The physical/source gradient identification is
proved for every compatible continuous representative, with reversed Fourier
indices and exact period conventions. Hölder duality bounds the actual source
operator by the two conjugate physical Fourier norms. The existing H¹-ball
majorants and zero-free contours supply the full estimate; no gradient or
majorant premise is left. Collapsed gaps and finite central heads are included.

G.7's exact classical Dirichlet normalization is now proved: at a simple
root, the bilinear quantity `Q=2∫g₁g₂` is nonzero, and the actual derivative
of any continuous local root branch is the integral against `(g₂²,g₁²)/Q`.
Spectral differentiation of the Volterra solution supplies the denominator
identity. The free normalization is exactly two, with the two opposite
exponential waves and factor one half verified explicitly.

The formula is now instantiated at all canonical signed Dirichlet roots of
real continuously represented sources, including the H¹ sources. Completed
source and physical boundary characteristics agree by bounded physical
restriction and density. Both actual root-cotangent Fourier components are
identified at reversed frequency for every finite source exponent `p≥2`.
No simplicity or candidate-gradient premise is added at these real sources.

One common open complex neighborhood now supports this formula at every
index for finite `p≥2`. Both ordinary boundary sequences are analytic and
simple on a common domain for every finite `p>1`, by uniform tail counts and
continuity in the finite central block. The actual H¹ Dirichlet cotangent
has both normalized physical Fourier coefficients throughout the constructed
domain; reality, simplicity, and normalization are not additional premises.

The actual canonical Dirichlet and Neumann roots now have locally uniform
`O(1/|n|)` displacement on physical H¹ balls. The Dirichlet normalization
satisfies `Q−2=O(1/|n|)`, `|Q|≥1`, and an inverse error of the same order.
Combining these with the actual solution bounds gives a uniform pointwise
`O(1/|n|)` error for the normalized gradient against the two exact free waves.
These estimates apply at nearby complex sources and derive all root and
denominator bounds from the source data.

The normalized gradient error now satisfies its exact signed time ODE and a
uniform derivative bound. Its actual unit-interval Fourier coefficients
have a common summable tail majorant on source neighborhoods and H¹ balls
for outer exponent `s>1` and inner exponent `q>1+1/s`. At each fixed source,
the full sequence, including the finite head, is summable; in particular
the conjugate Fourier norms form an outer ℓp sequence for finite `p≥2`.

The actual Dirichlet root derivative minus the explicit free functional
`h ↦ (h₁(-n)+h₂(n))/2` now has a physical Fourier coefficient pair with outer
ℓp summability in the conjugate component-sum norm, for every finite `p≥2`.
Both component identities are proved on a common complex neighborhood of
the entire real source locus. Exponent compatibility and density identify
the free functional at every such source exponent. The actual source
operator error is summable too, including every signed central index.

Both actual derivative estimates now hold on one shared complex domain in
the literal conjugate Fourier pair norm. A bounded scalar functional has a
conjugate coefficient representative with equal norm, proved by finite dual
tests and bounded pointwise limits. Component recovery and frequency
reversal form a bounded complex-linear map from source operators to physical
Fourier gradients. It gives the midpoint estimate and the Dirichlet error
estimate, their full-direction duality formulas, and their outer ℓp
summability, for every finite `p≥2`.

The actual anti-discriminant derivative error now satisfies G.6 at both
canonical boundary sequences of every complex H¹ source, for finite `p≥2`.
Continuous physical realization identifies its full cotangent and Fourier
coefficients. The actual boundary displacement supplies the asymptotic
hypothesis; the resulting operator and conjugate Fourier pair norms are
outer ℓp sequences, including the finite head. The reference is exactly
`i cos(πn) (h₁(-n)−h₂(n))`, proved at every finite `p>1` by exponent
compatibility and density.

The omitted-root-product normalization is now proved at both actual boundary
sequences for every real source and every finite `p>1`. Closed-gap reality
and parity select the signed square root, including collapsed gaps. Generic
ℓp-displaced sampling controls the squared error; both the product and its
reciprocal differ from `cos(πn)` by ℓp sequences, with bounded reciprocals
across all signed indices. The existing open-gap sign APIs remain available.

The finite-gap coordinate derivative estimate is now proved for finite
`p≥2`. The exact free functional selects the signed component with factor
minus two. The closed-gap error splits into the two G.7 errors and three
anti-discriminant corrections controlled by G.6, scalar spectral-derivative
summability, and inverse omitted-product normalization. Finite-gap regularity
constructs a compatible real Hilbert source and physical H¹ representative.
The actual coordinate derivative agrees with the closed-gap expression
outside the finite set of open gaps; finite modification includes every
remaining index. Both source operator norm and the conjugate Fourier pair
norm give outer ℓp sequences, with the local common-domain construction as
the coordinate hypothesis.

Lemma 16.1 is now proved in the full range `1<p<∞`. The Hilbert source
cotangents have every outer exponent above one, by the physical estimates
with inner exponent two. Restriction along coefficient inclusion then
proves the actual real H¹ midpoint, Dirichlet, and anti-discriminant
estimates below two. Finite-gap regularity supplies the physical H¹
representative; the shared closed-gap decomposition and finite modification
complete the full source-operator estimate. Conjugate-gradient recovery
identifies both literal signed Fourier modes and gives exactly the two
ℓp norm sequences. A final existence theorem supplies a constructed
Birkhoff family satisfying the estimates at every real finite-gap source.

Lemma 16.2 is now proved for the full range `1<p<∞`. At finite-gap sources,
the beta correction is a finite sum over the open gaps, with each summand
controlled in ℓp by a shifted reciprocal lattice. The normalized-action
root and complete exponential phase multiplier are summably close to one.
Closed-gap vanishing removes their derivatives in the exact product rule;
Lemma 16.1 and bounded scalar multiplication control the signed derivative
errors, and finite modification includes the open gaps. The normalized sum
and difference give both actual rectangular derivative errors in operator
norm. Exact free Fourier functionals and conjugate-gradient recovery then
prove both literal conjugate-pair norm sequences. A constructed Birkhoff
family supplies the domain and all data for the final existence theorem.

Lemma 16.3 is now proved at every real source for `1<p<∞`. The actual
finite-gap Jacobian remainder has two ℓp row majorants, hence its finite
output truncations converge in operator norm and the remainder is compact.
The existing density of real finite-gap sources and continuity of the
Jacobian extend compactness to all real sources. An explicit bounded
Fourier inverse gives `Aφ = F⁻¹ dφΩ`; the exact identity for `Aφ−Id`
transfers compactness. The normalized Jacobian is complex analytic on the
constructed domain and real analytic on the complete real source space,
and normalization preserves bounded isomorphisms in both directions.
A constructed-family existence theorem supplies the full Lemma 16.3.

Next prove Proposition 17.1: use the compact perturbation and canonical
gradient identities to establish invertibility of the Jacobian, then apply
the inverse function theorem to the actual real Birkhoff map. The sharper
G.1 integral bound, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Milestones

1. **Sequence spaces:** finite truncations, density, weighted coefficients,
   bounded Fourier multipliers, convolution estimates.
2. **Fourier realization:** identify the `p = 2` model with periodic `L²`, prove
   the periodic-distribution interpretation, and fix period-one/period-two and
   signed-component conventions.
3. **First spectral milestone:** domain inclusion, differentiation and potential
   multiplication, the free Zakharov–Shabat resolvent, and compactness.
4. **General analysis:** audit exact convolution, discrete Hilbert transform,
   contour integration, infinite product, and compact operator dependencies.
5. **Spectral data:** localization, multiplicities, finite-dimensional reduction,
   and locally uniform sequence asymptotics (Chapter 1).
6. **Classical dependencies:** formalize the necessary results from reference
   [23], Grébert–Kappeler, *The defocusing NLS equation and its normal form*.
   Conditional development may use explicit hypotheses, but final main theorems
   must instantiate them with proofs.
7. **Coordinates:** actions, angle branches, analytic rectangular coordinates,
   canonical relations, and the precise conclusions of Theorem 14.1.
8. **Applications:** frequencies and Hamiltonian (Theorems 18.1–18.3), dynamics
   (Theorem 18.5), and Sobolev estimates (Theorems 23.1–23.4).

## Statement audit

- Equation (2.4) and Lemma 8.1 on printed page 48 use inconsistent prefactors.
  With the actual zero-potential spectra, the displayed `-2` periodic product
  is zero at `λ=0`, while the displayed `2` antiperiodic product equals two.
  Thus no value of `∆` can satisfy both `∆=f+2=g-2`, even as limits. Euler's
  symmetric free product proves that the periodic prefactor must be `-1`
  (as used in the proof on the same page); the free value at zero forces the
  antiperiodic prefactor to be `4`. The full periodic product's `-4` in (2.1)
  is correct. Retain these distinctions when implementing Section 8; the
  corrected perturbed products are implemented, and their classical
  discriminant identification is proved for continuously represented even
  Hilbert potentials. The intrinsic shifted identity and full product/spectrum
  characterization now extend to every finite p>1.
- Lemma 8.1(iii)'s detailed quotient by `2 cos λ` is undefined at the
  arbitrarily large points `λ=π(n+1/2)`, all outside the stated radius-`π/4`
  free discs. Lean's totalized quotient has error exactly one there for every
  numerator. The formal audit rejects that literal uniform quotient bound;
  it does not reject an additive asymptotic or a suitably restricted quotient.
  Fixed-potential additive trace and derivative asymptotics normalized by
  `exp(|Im λ|)` are now proved on the full free-disc exterior.
- Lemma 6.9's printed page-43 displacement estimate fails with its claimed
  local uniformity at zero. The actual signed single-mode family has roots
  `nπ±t` and Hilbert pair norm squared `2t²`, whereas the printed budget is
  at most `24 C t⁴` for `t≤1` and cutoffs at least one. The formal counterexample
  works in every open neighborhood of zero and beyond every prescribed cutoff.
  It refutes a necessary single-root consequence of the sum estimate; it does
  not assert failure of an eventual estimate for each fixed potential with an
  unrestricted potential-dependent cutoff. Retain an additive leading-tail
  term in the corrected estimate.
- On printed pages 33 and 53, the auxiliary Dirichlet domain is
  `f₋+if₊=0` at both endpoints, but the displayed formula labeled
  `χD*` has the monodromy sign of the auxiliary Neumann domain
  `f₋−if₊=0`; the displayed `χN*` has the Dirichlet sign. This is an
  exact algebraic mismatch with the printed `δ=χD*−χN*` when the
  functions are labeled by their actual endpoint domains. The corrected
  domain-based identity is `δ=χN*−χD*`. Keep the actual domain labels and
  preserve the sine normalization in formal proofs.
- Propositions 6.1 and 6.3 on printed pages 35–36 repeat the nonlinear-only
  budget with locally uniform cutoffs. The scalar-root formalization retains
  the additive leading-tail term required by the single-mode audit. Do not
  present these corrected estimates as proofs of the literal printed bounds;
  the original periodic spectral multiplicities are now identified with the
  scalar analytic orders in all sufficiently distant strips.
- Preserve `1 < p < ∞` versus `1 < p ≤ 2` hypotheses. Do not assume that the
  Birkhoff map is surjective for `p > 2`.
- Treat analyticity on a positive cone using an ambient open extension.
- Encode locally uniform sequence estimates with neighborhood norm bounds.
- Renormalized quantities must be defined by convergent expressions before
  proving identities involving subtraction on the classical domain.
- Preserve the smooth-approximation notion of rough solutions in Section 18.
- The Hessian display on printed page 12 requires correction: the preceding
  expansion for `H` gives `4 - 2 δ_nm`; `-2 δ_nm` is the corresponding Hessian
  of the renormalized Hamiltonian at zero.

## Completion policy

Every implemented theorem must compile without `sorry`, `admit`, or project
axioms. Main-result completion also requires an audit of transitive axioms.
Dependencies and source-page references should be recorded as each theorem is
introduced. Definition-only stubs do not count as proved results.

## Current next proof target

Corollary 13.2, Lemma 15.1, the rectangular construction, and Theorem 15.2
are proved throughout `1 < p < ∞`. Lemma 15.3 is proved on the real
open-gap locus using the actual rectangular derivatives and regular
cotangent pairings. Next extend its three identities across closed gaps
and retain the root family of the sequence-valued Birkhoff map. Preserve
the physical bracket sign `−i` and the mixed value `−δₙₘ`.
The remaining assertions of Theorem 14.1 follow later. See `STATUS.md`
for current coverage; the entries below record the historical sequence
of proof targets.

## Earlier proof targets

The Fourier-side convolution multiplication estimate
`FL^p × FL^{1,p} → FL^p` is now proved for every finite `p≥1`, with a constant
depending only on `p`. The scalar and pair domain inclusions, differentiation,
and the two-component operator are also proved, with explicit period-two signs
and maximum-pair-norm bounds. Both signed free modes have eigenvalue `π n`.

The free resolvent away from `πℤ` is now constructed as a bounded inverse into the
one-derivative domain, with both inverse identities and a spectral-gap bound on
the base space. Compactness follows from operator-norm convergence of finite
Fourier cutoffs. The signed-mode formulas and resolvent identity are also proved.

The `FL^p → FL^1` Hölder estimate is now proved with the conjugate-symbol norms
kept explicit. It bounds `Φ R₀` and supplies a sufficient Neumann condition.
Under that condition, the perturbed inverse is constructed with both inverse
identities, norm bounds, and compactness. For `p=1`, the condition follows from
`|Im z| > ‖φ‖`, giving an admissible parameter for every `l1` potential.

Uniform high-imaginary-part regions are now proved for all finite Banach
exponents. A concrete reciprocal envelope has conjugate norm tending to zero;
Fourier recentering makes the bound uniform in the real part. Each norm ball of
potentials therefore has a common Neumann height, and every finite-p potential
has a compact two-sided inverse at some parameter without a smallness assumption.

The unbounded realization is now a partial linear map on the base space with
exactly the included one-derivative domain. Its domain is dense and its graph is
closed, using the bounded two-sided inverse to characterize graph membership.
Base-norm limits of graph points remain in the graph.

The full resolvent set is now defined by bijectivity of the spectral pencil.
It is nonempty for every potential; the joint domain in potential and parameter
is open. A single totalized resolvent agrees with the Neumann construction and
is jointly complex analytic on its domain, with compact base-space values.

The periodic spectrum is now proved closed and discrete, with finitely many
points in every bounded region. Each point is an eigenvalue with a
finite-dimensional domain eigenspace. The proof includes compact-operator
spectral finiteness away from zero and the reciprocal spectral transformation.

The general resolvent identities, commutation, and explicit joint Fréchet
derivative are now proved. Spectral differentiation gives `∂z R = -R²`; potential
differentiation gives `Dφ R[ψ] = R Φ(ψ) R_D`. The full and free constructions
agree at zero potential, and the pre-Neumann identity is proved without a
smallness restriction when the required resolvents exist.

Periodic root spaces are now defined recursively with domain membership at
each step. Their full union is finite dimensional and attained at a finite level,
using a bounded compact-pencil representation and the proved stabilization of
nonzero compact-operator generalized eigenspaces. The resulting algebraic
multiplicity is positive exactly on the periodic spectrum.

Bounded finite-rank projections onto individual full root spaces are now
constructed from topological kernel/range decompositions of stabilized compact
pencils. They are independent of the reference resolvent parameter, commute
with every resolvent, and have rank equal to algebraic multiplicity. Every base
vector has a unique root-space/complement decomposition.

Distinct full root spaces are now proved disjoint, and their projections
annihilate each other. Finite sums give bounded, compact cluster projections
whose ranges are the sums of root spaces and whose kernels are intersections
of the individual kernels. Cluster rank is the sum of algebraic multiplicities;
composition corresponds to intersection of parameter sets.

The normalized resolvent circle integral from Section 3, equation (1.4), is now
constructed as a bounded operator with a domain-valued factorization and proved
compact. It vanishes on resolvent disks and is unchanged by radius deformation
through resolvent annuli. A root-chain calculation proves identity on enclosed
full root spaces and zero on excluded ones. It commutes with resolvents and
individual spectral projections; composing with a finite cluster projection
selects precisely the parameters inside the circle.

Nested-circle integration now proves the contour projection law, using a
circle-integral interchange theorem and the resolvent identity. Local spectral
finiteness gives nearby resolvent annuli, so radius deformation proves
idempotence for every resolvent circle. Compactness then gives finite rank.
Decomposing the finite-dimensional contour range under a restricted resolvent
identifies it with the enclosed root spaces, proving equality with the algebraic
cluster projection on the whole base space. Rank is the sum of enclosed
algebraic multiplicities; circles enclosing the same spectrum give equal operators.

For a fixed circle, the admissible potential set is open, and the contour
projection is analytic in operator norm. Uniform Banach-algebra inversion along
the circle and bounded linear integration establish this dependence. Projections
less than one apart have the same rank, so total enclosed algebraic multiplicity
is locally constant.

Appendix B.1 is now proved with both stated constants, including `α=0`,
summability, one-sided tail estimates, and translated bilateral lattice bounds.
The reciprocal Sobolev constant is now at most `2p`. Punctured-strip geometry
then gives `freeL1Bound ≤ 2p/r` and the stated `8p/r` operator estimate of
Lemma 3.2(iii), with the library's maximum pair norm. Under `2p * ‖φ‖ < r`,
all spectral circles are admissible and the entire spectrum lies in the union
of disks about `πℤ`.

Lemma 3.2(ii) is also proved: the free `FL^p → FL^1` norm is at most
`4p / abs(Im z)^(1/p) + 1 / abs(Im z)` for nonzero imaginary part. Removing
the central coefficient gives the separate tail and central contributions.
The numerical Neumann region lies in the full resolvent set, where the
resolvent is compact and analytic. Its height bound tends to zero and gives
a common region for every bounded potential set.

The double-resolvent operator, its coefficient formulas, and the factorization
of `(Φ R₀)²` through `FL^1` are proved. The squared Neumann condition yields
a two-sided domain inverse, agrees with the full resolvent, and gives a
quantitative norm bound. One-sided potentials provide verified examples
outside the original Neumann condition, with exact two-term inverses.

Lemma 3.4 is now proved with the explicit maximum-pair-norm constant `32p²`.
The proof splits the reciprocal symbols into near and far windows about the
opposite scalar frequencies. The far symbols decay as `|n|^(-1/p)`, including
the endpoint, while the near-near term contains only the potential tail
`|k| ≥ |n|`. The symmetric tails converge to zero, and the numerical estimate
supplies squared Neumann criteria for entire punctured strips and circles.

Corollary 3.5 is also proved: the height region and the tail estimate give one
central box and one open convex neighborhood of any potential, containing zero,
on which every exterior resolvent is compact and analytic. The periodic
spectrum lies in the exact central box and the high-frequency quarter-pi disks.
The box uses a strict real boundary and a non-strict imaginary boundary; the
coverage proof treats the vertical edges separately.

Lemma 3.6 is proved for even-supported coefficient potentials. Closed
complementary parity subspaces have contractive coordinate projections, which
also preserve the weighted operator domain. The operator, spectral pencil,
full resolvent, and spectral circle integrals satisfy the corresponding
projection identities and preserve both parities. Signed free modes retain
the parity of their spectral index, including negative frequencies.

The high-frequency disk count in Proposition 1.1(i) is proved. A coefficient
induction rules out longer free Jordan chains, and the two signed modes give
algebraic multiplicity two. Contour rank and total multiplicity are constant on
any preconnected admissible family. The uniform convex neighborhood from
Lemma 3.4 therefore gives rank two and total algebraic multiplicity two in
every sufficiently far disk, for every positive radius at most `π/4`.

The parity assertion in Proposition 1.1(i) is also proved. A continuous
preconnected family of projections cannot deform zero into a nonzero
projection, since a nonzero projection has norm at least one. Applied to
the complementary parity part of each contour, this keeps its entire range
in parity `n`. All enclosed generalized eigenvectors have that parity, all
ordinary eigenfunctions have it in the weighted domain, and opposite-parity
inputs are annihilated. The result is uniform on the even potentials in the
same open convex neighborhood used for the multiplicity count.

The closed/open central rectangles and all boundary edges are constructed.
The uniform height estimate is retained at equality, proving that the horizontal
edges, as well as the vertical edges, are resolvent points. One open convex
neighborhood works for every larger positive cutoff. Open, closed, and mixed
boundary conventions then give identical central spectra. The finite central
algebraic spectral projection is constructed, and its free rank is `4N+2`,
by counting the signed indices `-N,…,N` with multiplicity two.

The central projection’s analytic deformation and total count in Proposition
1.1(ii) are now proved. At a sufficiently larger cutoff, a circle of radius
`πK+π/2` avoids the entire localized spectrum and selects exactly the central
box’s spectral values. The full projections are equal, so circle analyticity
and rank stability give central rank and total multiplicity `4K+2`. One open
convex neighborhood works for every larger cutoff. The proof does not require
that the circle contain the corners of the box with the same cutoff.

The central parity split in Proposition 1.1(ii) is now proved. Filtering the
signed free indices gives `N+1` indices in the cutoff’s parity and `N` in the
other. The parity components of the free projector equal the corresponding
filtered spectral clusters. General rank stability for continuous preconnected
families of finite-rank projections transfers their ranks to even potentials.
The component ranges equal the parity intersections of the central spectral
space, so their dimensions are `2N+2` and `2N`, with the larger part switching
with the cutoff’s parity. The total count, parity counts, and analytic
projection families share one neighborhood and one cutoff.

The localization and counting conclusions are now assembled in
`PeriodicCountingData`. One open convex neighborhood and threshold support all
larger cutoffs, central and high-disk multiplicities, parity conclusions, and
analytic projection families. Every noncentral spectral value has a unique disk
index, and each high disk admits a pair of eigenvalues counted with multiplicity,
allowing repetition for a double value.

The real-type clause (iv) is now proved for all finite Banach exponents. Absolute
convergence of coefficient duality and of the double convolution sum establishes
the adjoint identity for conjugate-reflected kernels. Together with the real
free symbols, this gives symmetry on the weighted domain. Its strictly positive
coefficient energy forces every eigenvalue to be real. Spectral discreteness
and the eigenvector characterization then put every nonreal parameter in the
resolvent set, without assuming a Hilbert-space realization.

The analytic local reduction used in Lemma 3.7 is now constructed. The explicit
intertwiner `QP + (1-Q)(1-P)` equals the identity at the reference projection,
has analytic inverse nearby, and induces equivalences of the full ranges.
The contour projection is analytic in the stronger domain norm, so `L P_D`
is bounded and analytic. Its commutation with the spectral projection gives
an analytic operator on a fixed finite-dimensional reference range, with an
exact intertwining identity and the correct enclosed-eigenvector action.

Lemma 3.7 is now proved. The range equivalence conjugates the local reduction
to the intrinsic restriction, so traces of all powers are reference-independent
and analytic. Its eigenvalues are exactly the enclosed spectral values. In
dimension two, the characteristic polynomial and Cayley–Hamilton give the
midpoint and squared-gap identities, including repeated values and Jordan blocks.
One counting neighborhood supports analyticity for every sufficiently high index;
the source normalization `γ²/2` follows from the centered-square trace identity.

Section 4's coefficient boundary spaces are now constructed. Frequency reflection
is an isometry at every Sobolev regularity, and the positive/negative reflected
graphs are closed complementary subspaces with isometric amplitude coordinates
and contractive projections. Both signed boundary modes have free eigenvalue
`π n`. For already-reflected Dirichlet potentials, Lemma 4.4's operator invariance,
restricted bounded operators, projection intertwining, and the opposite signs
in the potential's mode action are proved for every finite Banach exponent.

The full resolvents of both boundary restrictions are now constructed. Each
resolvent set is defined by bijectivity of its own pencil, and normalization
by the fixed free inverse gives both inverse identities, compactness, and joint
analyticity on the full open domain of reflected potentials and parameters.
The periodic resolvent set is their intersection and the periodic spectrum is
the union of the boundary spectra. Both spectra are closed and discrete with
finite bounded portions; compact-resolvent spectral transformation proves that
every spectral point has an eigenvector satisfying the selected boundary condition.
The periodic resolvent and circle projections preserve both boundary spaces.

Boundary root chains now use the actual restricted pencils, and their ambient
images equal the corresponding boundary intersections of periodic root spaces
at every level. The full spaces are finite dimensional and stabilize; their
ranks define algebraic multiplicity and sum to periodic multiplicity. Free
boundary spectra are the full signed lattice, each value has multiplicity one,
and the free quarter-pi contour has rank one in each summand. The free central
algebraic count is `2N+1` for both boundary conditions.

The coefficient counting argument of Theorem 1.4 is now proved. Boundary cluster
spaces are finite sums of the actual restricted full root spaces, and their
images are exactly the boundary intersections of periodic clusters. Bounded
cluster projections on both the boundary and ambient spaces have these ranges
and ranks equal to sums of boundary algebraic multiplicities. Circle projectors
select the same clusters and are analytic in operator norm. Rank constancy on
the reflected part of a common convex neighborhood carries the free counts to
every reflected potential there. `BoundaryCountingData` gives one simple value
in each high disk and `2N+1` central values counted algebraically, for both
conditions and every larger cutoff, together with the periodic localization.

Lemma 4.5 is now proved for the coefficient restrictions. The boundary contour
lifts analytically into its weighted boundary domain; inclusion recovers the
base projector, and applying the original operator through the lift gives a
bounded analytic spectral restriction. A general trace theorem handles varying
finite-dimensional ranges using local projection transport. In dimension one,
its intrinsic trace equals the enclosed eigenvalue. The trace-defined Dirichlet
and Neumann functions are analytic on one open convex neighborhood in the
reflected potential space and agree with the previously counted simple values.
Their free values are `πn`, and they have actual weighted-domain eigenvectors.

The physical piecewise interval extensions and their normalized Fourier formulas
are now proved. Translates of the half-interval kernel give linear maps from
finite period-one coefficient pairs into the actual boundary `ℓp` spaces for
`p>1`, including `∞` for this finite-input construction. The odd reciprocal tail
is not in `ℓ1`, as witnessed by the constant input `(0,1)`. The derivation from
(1.8)–(1.9) corrects the missing normalization on printed page 31.

The Hilbert exponent is now handled uniformly. Mathlib's interval Parseval
identity is connected to our normalization, giving the exact finite-input
energy identity. Dense finite coefficient inclusion then yields unique bounded
interval extensions on all `PairSpace 2`, with boundary membership, injectivity,
and the same energy identity. Odd-index sampling extracts the normalized
shifted Hilbert kernel `2/[π(2k-2n-1)]` as a bounded `ℓ2` operator.

The first non-Hilbert exponent is now proved. The ordinary kernel `-1/j`
and unnormalized shifted kernel `-2/(2j+1)` differ by an absolutely summable
sequence with square decay. Young's inequality handles this correction at
all Banach exponents and supplies the ordinary Hilbert `ℓ2` bound.
The discrete Cotlar identity is proved on finite complex sequences, including
both diagonal square-kernel terms. Hölder `ℓ4 × ℓ4 → ℓ2` and the ordinary
`ℓ2` bound give a support-independent quartic estimate. Density constructs
both ordinary and normalized shifted Hilbert transforms on all `ℓ4`, with
exact agreement with the finite reciprocal formulas.

The general doubling step is now proved: any uniform finite-input estimate at
`p` gives an estimate at `2p`, and density supplies unique continuous ordinary
and shifted operators. The Hölder product and exact square-norm identity work
at general doubled exponents. Induction constructs both operators at every
`2^(n+1)`, with bound `2^n B₂ + (2^n-1)(3M+1)`. These exponents are proved
unbounded. The old quartic product is a specialization of the general product.

The duality step is now proved. Finite conjugate tests detect each truncated
sequence norm, using mathlib's finite Hölder extremizer; density detects the
full norm. Antisymmetry of the finite Hilbert kernel transfers every proved
finite-exponent estimate to the conjugate exponent with the same constant.
The transposition identity extends to arbitrary conjugate inputs. Applying this
to the dyadic estimates constructs ordinary and shifted transforms at
`2, 4/3, 8/7, …`, all in `(1,2]` and arbitrarily close to one.

Finite interpolation and the full Hilbert exponent range are now proved.
Complex phase/exponential families retain finite support, are entire in the
strip parameter, and have normalized endpoint norms. Their finite scalar kernel
pairing is uniformly bounded in the imaginary direction. Mathlib's Hadamard
three-lines theorem bounds the interior pairing by the maximum endpoint constant.
Conjugate unit tests detect the output norm, and rescaling removes normalization.
This constructs `HilbertEstimate.interpolate` with a support-independent bound.

An intermediate-value argument chooses a reciprocal interpolation parameter.
The dyadic and conjugate estimates bracket every finite `p>1`, supplying completed
ordinary and shifted transforms on every `Coeff p`. Uniqueness identifies them
with previous constructions at overlapping exponents. Hölder duality and density
also prove absolute convergence and the exact reciprocal coefficient series on
all inputs. Thus the boundedness part of Appendix C.1 needed here is established.

The full-range interval maps are now constructed. Zero insertion along integer
embeddings is a linear isometry, including the supremum endpoint. Inserting
`a/2` at even indices and `i Sa/2` at odd indices defines the bounded
half-interval Fourier map and recovers the exact physical finite coefficients.
Combining the two input halves with signed reflection defines the Dirichlet
and Neumann maps on all `PairSpace p`, `1<p<∞`. They land in the actual closed
boundary spaces, are bounded and analytic there, and are uniquely determined
by the finite Fourier formulas. At `p=2` they equal the earlier Parseval maps.
The coefficient statement of Lemma 4.3 is therefore proved.

The classical domain identifications in Lemma 4.2 are now proved. Actual
functions on `[0,1]` form complex Banach spaces with their exact physical
component-sum `H¹` norm. Signed extension and physical restriction are continuous
linear inverses, with operator bounds `1` and `√2 π`. Membership agrees with the
original equal/opposite component endpoint conditions, including odd modes.

The physical Hilbert-space operator bridge is now proved. Convolution realizes
actual multiplication of arbitrary `L²` potentials with `H¹` functions, and the
full coefficient and physical eigen-equations agree on `[0,2]`. Nonzero domain
vectors remain nonzero as physical `L²` functions.

Lemma 4.1's classical interval transfer is now proved. Arbitrary original `L²`
potentials have an a.e. reconstructed Dirichlet coefficient extension. Both
signed eigenfunction extensions intertwine the actual differential equation,
and nonzero original eigenfunctions enter the selected boundary and periodic
coefficient spectra with the same eigenvalue.

The converse restriction now identifies the original classical eigenvalue sets
with the coefficient boundary spectra. They are closed, discrete, and finite
in bounded regions; their union equals the periodic coefficient spectrum.
Both free sets are exactly `πℤ`, including odd modes, and a.e. equal potentials
have equal eigenvalue sets.

Original physical potential classes now carry the exact component-sum `L²` norm.
Their Dirichlet coefficient map has norm factor `√2/2` and is bounded, injective,
and analytic. Pullback gives one open convex physical neighborhood and cutoff
for both high-index branches, unique original eigenvalues in the high disks,
and uniform coefficient counting data.

Both signed physical `L²` base-space equivalences are now proved. The Dirichlet
map has closed, dense range and hence is onto; isometric component sign changes
give the Neumann map. Forward synthesis is actual signed reflection, and the
inverse is actual restriction almost everywhere. Both exact norm factors are
proved. The maps commute with classical domain extension and base inclusion.

The original operator/resolvent correspondence is now proved. The physical
classical-domain operator realizes the actual differential expression for any
original representatives. Its partial linear realization is closed and densely
defined on exactly the original endpoint domain. Physical and coefficient
pencils intertwine, their resolvent sets agree, and the physical inverse is
bounded with compact base-space resolvent. Its spectrum is exactly the original
classical eigenvalue set.

Original physical root spaces are now independently defined using the physical
pencil and domain at every chain level. The base/domain isomorphisms identify
each level and the full generalized eigenspaces. Their finite dimensions define
physical algebraic multiplicities and prove agreement with coefficient counts.
The physical central finite set, central multiplicity `2N+1`, unique algebraically
simple high-disk eigenvalues, and exclusion of other spectrum now hold uniformly
on one physical neighborhood for both boundary conditions, with analytic branches.
The free physical multiplicities and the periodic sum formula are also proved.
Both boundary spectral problems use the Dirichlet extension of the potential;
the boundary sign selects the eigenfunction extension and restricted domain. Preserve this distinction in the transfer.
Individual kernel membership alone remains insufficient for uniform boundedness.
Only boundedness is needed from Appendix C.1; its additional isomorphism assertion
is not assumed here.
The actual rectangular contour integral is now constructed as four oriented
operator-norm edge integrals. Its domain-valued factorization proves compactness,
and it commutes with resolvents and algebraic root-space projections. Horizontal
and vertical subdivision cancel shared edges; Cauchy's theorem gives invariance
under edge motion through filled resolvent strips. The central corner rectangle
and boundary agree exactly with the existing box, and one common neighborhood
admits all sufficiently large contours in the domain norm.
Logarithmic edge primitives now compute the exact simple-pole residue `2πi`;
exterior poles and all higher pole terms integrate to zero. Applying these
formulas along finite Jordan chains proves full root-space selection and exact
finite-cluster filtering. In particular the actual central rectangular integral
absorbs the central algebraic projection, and its range contains the central
algebraic range. Mixed-contour Fubini and the resolvent identity now show that
an enclosing circular projection captures all action of the rectangular integral.
Finite-cluster filtering then identifies the whole rectangular operator with the
central algebraic projection. The actual rectangle is idempotent, has exactly
the central full-root-space range, and varies analytically with rank `4N+2` on
one common neighborhood for all larger cutoffs. The unified statement uses Corollary 3.5's height-`N` box;
the printed norm-dependent height is now proved at `p=2`, with uniform
central count `4N+2` and equality of spectral clusters. The explicit sufficient
height `(1+8pM)^p` holds for every finite exponent. Direct substitution of the
printed `(1+8M)^p` into the existing `4p` estimate fails already at `p=3`,
`M=1`; this is a limitation of that argument, not a spectral counterexample.
The actual contour now equals the full enclosed cluster projection for every
ordered admissible rectangle. At the printed Hilbert height and the proved
all-exponent height, its boundary is admissible and the moving integral is
analytic with rank `4N+2`, uniformly on one counting neighborhood; no regularity
of the height function is needed beyond a uniform sufficient bound.
Resolve the general printed bound separately, retaining the distinction from
the proved bound.
The source's finite-exponent coefficient pair norm and weighted pair norm are
now implemented exactly, with energy exponent `sp` and sharp comparison factor
`2^(1/p)`. The proved heights and actual analytic contour neighborhoods transfer
to the component-sum parameter space without increasing the height constants.
Canonical period doubling is now an isometry onto the even coefficient space,
with contractive sampling, exact projection identities, and convolution
compatibility. Splitting the actual physical integrals identifies every
integrable period-one function's period-two coefficients with even insertion,
preserving the coefficient norm. Absolutely summable sequences have an injective
continuous period-one realization. Pair insertion covers all even potentials
and supplies the parity hypotheses for resolvents and contours.
Every Banach `lp` sequence now synthesizes continuously and injectively into
mathlib's genuine tempered distributions. Signed half-integer Fourier samples
of Schwartz tests give an absolutely convergent action, and localized smooth
frequency tests recover every coefficient. Finite Fourier sums converge in the
pointwise tempered-distribution topology, including at infinity. Translation
proves period two and characterizes period one exactly by even support. At
absolute summability the action is integration against the existing continuous
series. Actual distributional differentiation now agrees with `iπn`, and its
graph within the same Fourier class is exactly the scalar one-derivative domain.
The signed-pair free operator has the same exact domain identification. Scalar
and free pair graphs are closed even at infinity; limits only require the two
base coefficient norms. Finite-exponent continuous representatives satisfy
weak integration by parts against Schwartz tests. Multiplication by every Fourier
polynomial is now Mathlib's genuine smooth distribution multiplication; the
coefficient convolution is its unique continuous extension to `ℓ¹` multiplier
data. Arbitrary converging smooth coefficient approximations give the same limit.
The test action is an absolutely convergent sum of actual Fourier integrals of
the continuous multiplier times a Schwartz test. This also proves agreement with
all temperate smooth multipliers and with ordinary function products for `ℓ¹`
potential data. On the finite-exponent one-derivative domain the full signed
operator and its eigenvalue equations agree with these distributional products.
The Schwartz-to-circle bridge is now a continuous periodization map, with an
absolutely convergent physical translate sum and exact period-two Poisson formula.
It preserves the integral; a coefficient test at `n` periodizes to half the wave
at `-n`. Explicit Schwartz lifts cover all Fourier polynomials and prove uniform
density of periodizations. Its kernel is the common annihilator of the realized
Fourier distributions, and translating a test by two preserves periodization.
Periodization now commutes with every classical derivative. Each derivative is
a continuous linear image into continuous circle functions, is uniformly bounded,
and has an absolutely convergent physical translate sum. The same Fourier
truncations converge uniformly in every fixed derivative order, and periodizations
satisfy the genuine temperate-growth condition for smooth Schwartz multipliers.
A finite Leibniz seminorm estimate now proves that uniform convergence of all
multiplier derivatives gives convergence in genuine Schwartz topology after
multiplication by any fixed Schwartz window. Windowed Fourier reconstruction
converges in that topology, and every tempered distribution evaluates it through
an absolutely convergent scalar coefficient series, without a periodicity or
Fourier-class hypothesis on the distribution.
A direct construction now sums any series absolutely summable in all Schwartz
seminorms, with quantitative seminorm tails and actual Schwartz convergence.
Products of two Schwartz tests have inverse-square seminorm decay as one factor
is translated by the period lattice. Their convergent sums identify the two
sides of the periodization/window exchange under arbitrary periodic distributions.
Consequently, actual period-two invariance is equivalent to annihilating the
periodization kernel. Every periodic tempered distribution has an absolutely
convergent Fourier reconstruction from its coefficient-test values, and those
values determine it uniquely. The intrinsic Banach `ℓᵖ` condition is now equivalent
to unique representation by distributional synthesis, including `p=∞`.
The realization now extends to every positive weight with polynomially bounded
reciprocal. This condition is proved for every real Sobolev exponent, including
negative and fractional regularity. Weighted Schwartz sampling is a continuous
linear map into `ℓ¹`; weighting the coefficient sequence cancels the reciprocal
weight in the actual action. Weighted synthesis is continuous and injective,
preserves the raw Fourier coefficients, and is intrinsic across weights and
exponents. Arbitrary finite truncations converge distributionally, including
at infinity. Actual periodicity and weighted `Memℓp` are equivalent to unique
weighted synthesis. The full real Sobolev scale has a direct public API.
Weighted multipliers now have continuous linear maps with the pointwise
weight-comparison constant. Monotone real Sobolev embeddings are contractive,
injective, compose correctly, and preserve the actual distribution.
Differentiation maps regularity `s+1` to `s` with constant `π`, at every real `s`
and Banach exponent including infinity. The actual distributional derivative
has exactly this domain and a closed graph. Intrinsically, simultaneous
regularity `s` of a periodic distribution and its derivative is equivalent to
regularity `s+1` of the distribution. The exponent-changing embeddings are
now implemented below; the full two-input Young inequality is proved subsequently.
The source's distinct infinity pair norm is now implemented as `lp` of
sum-norm pairs, with complete weighted variants and exact supremum formulas.
Its comparison with the maximum product has sharp factor two. The first signed
coefficient is reflected explicitly in the equivalences to the scalar-coordinate
spaces, respecting (1.2). At every real Sobolev regularity, the endpoint pair
space has continuous injective actual distributional synthesis, coefficient
recovery, its exact intrinsic norm formula, and a unique representation theorem
for arbitrary periodic pairs with the stated endpoint regularity.

Increasing the sequence exponent is now a contractive continuous injection,
including the infinity target. Weighted versions preserve raw coefficients,
compose across exponents, and combine with decreasing real Sobolev regularity.
General Hölder triples provide weight-ratio embeddings into smaller exponents,
with the ratio norm as the explicit constant. Finite-exponent Sobolev reciprocal
summability is characterized exactly by the strict threshold `(s-t)r > 1`;
at the infinity multiplier endpoint zero regularity gain is allowed.
All these embeddings preserve the actual periodic distribution, and arbitrary
periodic source inputs have unique target representatives under the Hölder
condition. This supplies the coefficient estimate in Appendix A.9, without
asserting its separate fractional interval-Sobolev identification. That physical
identification remains a subsequent proof target; the full two-input Young
inequality is now proved below.

Appendix B.2 is now proved with its exact exponent relation and constant one
for all Banach exponents, including infinity. A weighted arithmetic-geometric
mean argument bounds finite trilinear convolution pairings. Finite norming
tests turn this into uniform finite Young estimates. Hölder and exponent
inclusion prove pointwise absolute convergence for arbitrary inputs; dominated
convergence of finite cutoffs and the `lp` Fatou property give full membership
and the norm bound. The convolution is a continuous complex bilinear map with
operator norm exactly one, is commutative, and agrees with the old `l1`-factor
construction. Finite input cutoffs converge in output norm, including conjugate
inputs with infinity output.

Appendix A.7 is now proved in the period-two model: every Banach Young triple
gives an actual periodic tempered product with the exact Fourier norm bound.
The construction is intrinsic to the two distributions, independently of their
exponent representations. It agrees with genuine polynomial multiplication
and is the unique joint continuous extension agreeing with polynomial
multipliers in either variable. Every admissible triple has a finite input
exponent; approximation in that factor handles the infinity endpoints without
claiming norm density in `l∞`. Shared Wiener representations recover actual
smooth and ordinary function multiplication.

The displayed mixed three-sequence inequality in Appendix B.3 is now proved
for its positive finite real exponents, including values below one. Powers of
magnitudes divide the sequence exponent with exact norm identities. The source
conditions construct an intermediate exponent satisfying the two scaled Young
relations. Applying the full Young inequality twice gives the exact nested
norm bound with constant one and proves convergence at all three summation
levels. Unit modes attain the bound. The next Fourier-space target is the
physical fractional Sobolev identification in Appendix A.9; the printed
general-`p` central spectral height and the main Birkhoff dependencies also remain.


The physical translation-energy foundation for Appendix A.9 is now in place.
Actual circle `L²` translations are strongly continuous isometries, and Parseval
gives both their exact Fourier increment energy and the factor-two physical
interval normalization. Nonnegative kernel energies admit a genuine physical
double-integral formula and an exact Fourier diagonalization by Tonelli,
including infinite energies. The fractional kernel on `[-1,1]` defines a
physical regularity predicate and has translation-invariant energy, symmetric
frequency weights, and exact single-mode and constant-function identities.
The spectral comparison is now proved below; the interval boundary estimate
below `s=1/2` remains necessary before claiming the physical statement of
Appendix A.9.


The fractional spectral weights now have uniform two-sided bounds by
`|n|^(2s)` for `0<s<1`. Quadratic phase cancellation and bounded phase increments
prove that the unit-frequency model kernel is globally integrable, and its
mass on `[0,1]` is positive. Exact frequency scaling gives the model integral
on `[-n,n]`; its positive core and finite total mass give frequency-independent
constants. The bounds include zero and negative frequencies and lift to the
full physical energy, including infinite values. Physical fractional regularity
is now equivalent to summability of the conventional homogeneous Fourier square
sum. The weighted coefficient identification is now proved below; the
nonperiodic interval boundary estimate for Appendix A.9 remains.


The periodic fractional Sobolev identification is now proved for `0<s<1`.
Homogeneous moment summability together with `L²` is equivalent to the project’s
`(1+|n|)^s` weighted square summability. Contractive Hilbert synthesis and actual
Fourier coefficients give both inverse identities and a unique weighted
representative for every physically regular periodic function. Explicit bounds
compare the weighted norm with the physical fractional energy plus the `L²`
term, which retains the zero mode. The next Appendix A.9 dependency is the
nonperiodic interval boundary estimate below one half, followed by the endpoint
conclusion through lower regularity.


The interval boundary kernel is now evaluated exactly for arbitrary positive
length `L`: its exterior mass at `x∈(0,L)` is
`[x^(-2s)+(L-x)^(-2s)]/(2s)`. The corresponding nonnegative double integral is
the mixed interaction of the actual zero extension and equals the weighted
boundary energy, including infinite values. The intrinsic interval difference
energy has also been defined and respects almost-everywhere equality.
The boundary weight has exact mass `2 L^(1-2s)/(1-2s)` below one half and is
integrable if and only if `s<1/2`. Constant interval data therefore has finite
zero-extension interaction exactly below half regularity; its intrinsic energy
vanishes at every exponent. Bounded interval data has an explicit exterior
energy bound below half. The next dependency is the fractional Hardy estimate
controlling the boundary-weighted square integral by the intrinsic interval
energy plus `L²` for arbitrary data, followed by the extension/periodization
comparison. These results do not yet prove the interval identification in A.9.

Planned Hardy proof: for `0<s<1/2`, average the inequality
`|f(x)|² ≤ (1+ε)|f(y)|²+(1+1/ε)|f(x)-f(y)|²` over `x<y<2x`,
with `δ<x<L/2`. Reversing the triangular integral gives the coefficient
`c_s=(2^(2s)-1)/(2s)=∫₁² t^(2s-1)dt<1` in front of the truncated
left-boundary energy. Choose `ε>0` with `(1+ε)c_s<1` and absorb that term.
The difference term is controlled by the intrinsic interval kernel because
`0<y-x<x`; the remaining half interval is controlled by `L²`. First work
with `δ>0`, where weighted square integrability follows from `L²`, then pass
to the nonnegative integral as `δ` decreases to zero. Reflection supplies the
right endpoint. This avoids assuming the weighted integrability being proved.


The fractional Hardy estimate described above is now proved. The annular mass
produces `c_s=(2^(2s)-1)/(2s)`, and its integral representation proves
`0<c_s<1` for `0<s<1/2`. A measurable triangular kernel gives an exact Tonelli
identity for arbitrary nonnegative data, a uniform truncated averaging bound,
and domination of the difference term by the intrinsic interval energy.
With `ε_s=(1-c_s)/(2c_s)`, the actual square-energy preestimate has coefficient
`a_s=(1+c_s)/2<1`. Every positive cutoff has finite weighted energy from `L²`;
only then is the averaged term absorbed. Increasing cutoff intervals and
nonnegative monotone convergence give the full left endpoint estimate.
Reflection yields both endpoint weights. In particular, arbitrary interval
`L²` data with finite intrinsic fractional energy has finite zero-extension
exterior interaction below one half. Almost-everywhere replacement removes the
global measurability assumption in the finiteness conclusion.
The next A.9 step is the extension/periodization comparison with the already
identified physical periodic space, followed by the Fourier-Lebesgue embedding
and the separate half-regularity consequence through lower regularity.


The zero-extension and forward periodization comparison are now proved.
Full line difference energy equals intrinsic interval energy plus twice the
exterior interaction, including infinite values. This yields the exact
zero-extension regularity equivalence for arbitrary positive interval length
and `0<s<1/2`. A measure-preserving change of variables and Tonelli identify
line difference energy with actual translation-increment energy, also for
arbitrary `L²` representatives.

For period two and displacements at most one, the periodic increment is the
sum of three adjacent zero-extension increments, outside an irrelevant finite
set of endpoint crossings. Its square integral is at most nine times the full
line square increment integral. The normalization of circle `L²` gives a
periodic energy bound by `9/2` times the line translation energy. Actual
interval Fourier reconstruction and almost-everywhere invariance transfer
this bound to arbitrary original interval data. In particular, finite intrinsic
energy and interval `L²` imply `(1+|n|)^s` weighted square summability of the
actual Fourier integrals throughout `0<s<1/2`, with no matching endpoint values.
The next step is to assemble the sharp `q>1/(s+1/2)` Fourier-Lebesgue conclusion
from the existing Hölder coefficient embedding, handle `s=0`, and deduce the
separate `s=1/2` consequence by decreasing regularity.


The period-two A.9 membership conclusions are now assembled. The coefficient
map uses monotone exponent inclusion for `q≥2` and the explicit Hölder exponent
`r=(1/q-1/2)⁻¹` below two. It is an injective continuous linear map and preserves
raw coefficients. Composing with the physical interval bridge gives the
source's strict range `q>1/(s+1/2)` for positive subcritical regularity.
At zero, only `L²` is required, and the equality target two is also available.
Infinity follows from `L²` independently of fractional energy.

An arbitrary-length kernel comparison proves
`E_t(f) ≤ L^(2(s-t)) E_s(f)` for `0≤t≤s`. For each finite `q>1`, choose
`max(0,1/q-1/2)<t<1/2`; lowering the intrinsic half energy before periodization
then proves the separate half-regularity conclusion. No critical
zero-extension or matching-endpoint assumption is introduced.

Next, combine the existing quantitative Hardy, periodization, spectral, and
coefficient bounds into a single bound in an intrinsic interval norm, then
prove the Fourier scaling needed for the arbitrary-period statement. The
current membership theorems use period two; arbitrary-length energy estimates
alone do not establish the source's general-period identification.


The uniform intrinsic bounds above are now proved. The coercive Hardy gap is
inverted explicitly, giving a finite exterior constant for every positive
interval length below half regularity. Almost-everywhere replacement extends
the quantitative bound to arbitrary interval `L²` representatives. The
period-two Parseval identity retains its exact factor `1/2`; combining Hardy,
periodization, and the lower spectral estimate gives a finite weighted Fourier
norm bound in the original full intrinsic energy `N+E_s`.

Composition with the continuous coefficient embedding gives the complete
period-two Fourier-Lebesgue norm bound throughout the positive subcritical
range. The explicit intermediate index
`t(q)=(max(0,1/q-1/2)+1/2)/2` and a quantitative lowering inequality give the
half-regularity bound in the original intrinsic half size. At zero, only `N`
is used, and the constant `sqrt(1/2)` is attained by a constant function even
for the infinity target. These are uniform inequalities on representatives;
the intrinsic normed quotient API is implemented in the later step below.

The next A.9 step is the actual Fourier scaling from period two to arbitrary
positive periods, including the normalization of physical square and
fractional energies. The existing arbitrary-length kernel estimates do not
replace that coefficient identification.


The arbitrary-period scaling step is now proved. Restricted Lebesgue measure
under `x ↦ cx` has inverse Jacobian `c⁻¹`; `MemLp` and nonnegative integrals
transport with that exact factor. Kernel homogeneity and two changes of
variables give the fractional factor `c^(2s-1)`, including infinite energies.
The full intrinsic size has a proved bound accounting separately for its
square-integral and fractional terms.

The actual normalized integral on `[0,L]` with frequency `2πn/L` agrees with
mathlib's interval Fourier coefficient and with the period-two coefficient of
`f((L/2)·)`. Thus A.9's membership and uniform intrinsic bounds now hold on every
positive period, including the zero branch with no fractional hypothesis and
the separate half conclusion. At zero the normalization is `L^(-1/2)`.

The next function-space step is the reverse comparison from physical periodic
fractional energy to intrinsic interval energy, followed by the normed
intrinsic Sobolev function-space identification. The forward comparison alone
already proves A.9's coefficient conclusions; the reverse direction is the
remaining part of the equality of Sobolev spaces invoked in its proof.


The reverse comparison is now proved. Enlarging the intrinsic interval
integral, changing to displacement variables, and applying Tonelli bounds it
by twice the full translation energy. The exact tail mass is `1/s`, and the
uniform `L²` increment estimate gives
`E_interval ≤ 2(E_periodic+(4/s)‖f‖²)` for every positive index, including
infinite energies. Below half this combines with forward periodization to
identify the physical periodic and intrinsic interval regularity conditions.

Actual Fourier reconstruction and bidirectional dilation finiteness give the
weighted square-summability criterion on every positive interval length,
together with a unique weighted representative. The reverse spectral bound
retains the zero mode: `I_s ≤ R_s ‖a‖²` with
`R_s=2+2(C_upper(s)+4/s)` for `0<s<1`. Below half, the forward and reverse
bounds give explicit norm equivalence for arbitrary period-two interval data.

The intrinsic normed quotient and continuous Fourier embedding are now
implemented in the following step.


The intrinsic function-space step is now proved on every positive interval.
A normalized circle `L²` class represents arbitrary interval data by the
coordinate change `x ↦ 2x/L`, with exact square-energy factor `L`. Reconstruction
is almost everywhere, and equality of constructed classes is exactly interval
almost-everywhere equality. Thus the representation imposes no endpoint condition.

The physical difference quotient `(f(x)-f(y))/|x-y|^(1/2+s)` is square integrable
precisely when the intrinsic fractional energy is finite. Its class and the
scaled original `L²` class form an injective linear graph in a product of `L²`
spaces. The induced norm has square exactly `N+E_s`; its equality with the
previously defined intrinsic size is proved. Both graph components are
continuous, with the normalized `L²` inclusion factor `1/sqrt(L)`.

The existing A.9 bounds now give continuous complex-linear Fourier injections
from this actual normed space, preserving the original normalized Fourier
integrals. The positive subcritical source range and the separate half case
are both covered, including nonperiodic ramps. At zero regularity, the earlier
ordinary `L²` API still applies; the fractional graph at zero is not identified
with the ordinary `L²` norm.

The completeness and continuous weighted Fourier equivalence steps are now
proved below, with quantitative bounds on arbitrary interval lengths.


The intrinsic space is now a complete complex Hilbert space. Convergence in
`L²` gives an almost-everywhere convergent subsequence of the original circle
classes. Pulling its convergence back to the physical interval and taking a
further subsequence for the difference quotients identifies the graph limit
pointwise almost everywhere on the interval square. This proves closedness
of the actual physical graph, with no restriction on its real index and no
endpoint assumptions. Completeness follows from its isometric inclusion into
the product of complete `L²` spaces, including at the critical half index.

The induced complex inner product is
`L * inner(f,g) + inner(Q_s f,Q_s g)` in normalized circle coordinates, with
the usual conjugate-linearity in the first argument. Convergence in the
intrinsic norm is equivalent to simultaneous convergence of the two graph
components. Norm-summable series of nonperiodic half-regularity ramps now
exist in the intrinsic space, and both difference-quotient and Fourier maps
commute with these sums.

The continuous weighted Fourier equivalence and its approximation consequences
are now proved in the next step.


The subcritical identification is now a genuine continuous linear equivalence
between the intrinsic Hilbert quotient and the normalized-frequency weighted
coefficient space `(1+|n|)^s ℓ²`. Analysis is given by the actual normalized
physical Fourier integrals; synthesis is the existing `L²` Fourier inverse.
Both inverse identities are proved. For physical interval length `L`, the
analysis bound is `sqrt(C_Sob(s)) sqrt(D_s(L/2))`, while the synthesis bound is
`sqrt(D_s(2/L)) sqrt(R_s)`, with `D_s(c)=c⁻¹+c^(2s-1)`. The dependence on interval
length is retained in both directions. Synthesis and its norm bound hold for
all `0<s<1`; the two-sided equivalence requires `0<s<1/2`.

The A.9 intrinsic Fourier map factors through this exact equivalence and the
proved weighted Hilbert coefficient inclusion. Finite Fourier truncations
retain precisely the selected actual coefficients, have a uniform bound
independent of their finite support, and converge in the full intrinsic norm
below half regularity. Hence classes with finite Fourier support are dense,
including when the original interval input has unequal endpoint values.

The next Section 6 weight and shifted-norm step is now implemented below.
The resonant splitting and complementary free inverse feed Lemma 6.4 and the
eigenvalue and weighted-gap asymptotics of Propositions 6.1 and 6.3. The printed
general-`p` central-height constant in Proposition 3.1 remains independent.


The displayed Section 6 weight class is now formalized with lower bound one,
symmetry, submultiplicativity, and monotonicity on the nonnegative integers.
The normalization does not impose `w(0)=1`; constant weights greater than one
are included. Scaled Sobolev weights `(1+c|n|)^s` with `c,s≥0` include both the
existing normalized-frequency weights and the source's exact `π` scale. Every
source weight has tempered reciprocal and a contractive inclusion into the
unweighted coefficient space.

Translated weights `w(n+i)` define the same coefficient space, with continuous
identity maps and comparison factor `w(i)` in both directions. Reindexing gives
an isometric map from the shifted-weight class to the original weight, and the
resulting modulation has raw coefficients `a(n-i)`. Its norm is exactly the
source's shifted scalar norm. The modulation also agrees with Mathlib's actual
multiplication of the synthesized tempered distribution by `exp(iπix)`.
The scalar results include the infinity exponent.

For finite Banach exponents, the pair norm modulates the first physical
component by `-i` and the second by `i`. The exact energy is
`Σ_n w(n+i)^p (|f_minus(-n)|^p+|f_plus(n)|^p)`, as in Section 6's signed mode
coordinates. Both comparisons again have factor `w(i)`, with no additional
pair-norm constant. Unit weights give isometric pair shifts.

The resonant projections and complementary free inverse are now implemented.
The projections select physical frequencies `-n` and `n`, sum to the identity,
and are idempotent and mutually annihilating. The complement is characterized
by vanishing of those two coordinates.

All nonresonant denominators dominate `|m-n|≥1` throughout the closed strip,
including its center. The zeroed reciprocal defines a continuous linear inverse
into the domain with weight `w(k)(1+|k|)`. Both compositions with the free pencil
give the appropriate complementary projection, and the complementary solution
is unique. The domain map has bound `1+(1+|λ|)/π`. Forgetting the source weight
identifies the pencil with the original free differential operator on its
existing domain. The base inverse and both projections contract every signed
shifted finite-exponent pair norm with constant one.

Lemma 6.4 is now proved. Weighted convolution is a continuous bilinear map
with Young constant one, constructed by a norm-summable series and identified
with the existing raw-coefficient product. The punctured reciprocal lattice
belongs to the conjugate space for every finite Banach input exponent,
including `p=1`. Its Hilbert norm is at most two. The chosen exponent-only
constant `c_p=max(‖puncturedLattice‖_{p′},2)` therefore has `c₂=2`.

The complementary inverse gains weighted `ℓ¹` regularity uniformly in the
strip and in every scalar shifted norm. Composing it with the off-diagonal
weighted product gives the actual `T_n`, with the source's sign-reversing bound
`‖T_n f‖_{w,p;i}≤c_p‖φ‖_{w,p}‖f‖_{w,p;-i}`. The original potential/domain
identification is proved. Squaring restores the shift with bound `(c_p‖φ‖)²`.

Lemma 6.5 is now proved. Weighted scalar and pair tails retain `|k|=|n|`
and converge in norm for every finite exponent. The two closed half-radius
windows isolate the potential remainder. Monotonicity and symmetry give the
near-near comparison `w(j-n)w(n)≤w(j-k)w(k-n)`, which positive coefficient
majorants transfer to a full shifted norm bound with the factor `1/w(n)`.
The two far terms use uniform reciprocal-tail decay, including the `p=1`
conjugate-infinity endpoint and the central lattice parameter.

The actual square factors through the two scalar double-complementary
inverses. The resulting estimate in shift `n`, and equivalently in the induced
operator norm, is
`C_p‖φ‖(‖φ‖/(1+|n|)^(1/p)+‖R_n φ‖/w(n))`, with
`C_p=64p c_p+c_p²`. It is valid for every integer center, including zero,
and all parameters of the full closed strip. The exact finite-`p` pair norm
and the inverse-weight improvement are retained.

The locally uniform threshold after Lemma 6.5 is now proved. Forgetting the
weight preserves both physical Fourier components and commutes with `T_n`.
The exact unit-weight pair norm is invariant under signed shifts. A common
bound in the weighted full norm and weighted tail therefore controls both
operator squares. For every positive tolerance, one open convex neighborhood
containing the potential and zero has a common cutoff `N≥1` valid on every
full closed strip with `|n|≥N`. Taking tolerance `1/2` gives the source's
simultaneous unweighted and weighted shifted contraction.

The squared Neumann inverse and the Q-equation are now proved. Conjugating
by the signed shift gives a small square; the geometric series is then
transported continuously back to the original operator algebra. It gives
both inverses of `Id-T_n²` and the factorization
`T̂_n=(Id+T_n)(Id-T_n²)⁻¹`, with both inverse identities for `Id-T_n`.
The inverse commutes with `T_n` and agrees with the unweighted inverse on
common inputs.

The actual potential is implemented continuously from the weighted derivative
domain to the base via the one-derivative weighted Hölder embedding and
convolution. Its coefficients identify it with the original potential and
its composition with the complementary inverse is exactly `T_n`. The
reconstructed `v=A_λ⁻¹ Q_n T̂_n Φu` lies in the complementary derivative
domain, satisfies the Q-equation and `Φv=T̂_n T_n Φu`, and is unique.
Existence and uniqueness hold uniformly over the previously constructed
open convex neighborhood and every sufficiently distant full closed strip.

Lemma 6.6 is now proved. Continuous extraction and synthesis identify the
two physical resonant modes with `Fin 2 → ℂ`, including an explicit lift
into the derivative domain. The free pencil acts there by `λ-nπ`. The map
`S_n=(λ-nπ)Id - coordinates ∘ T̂_n Φ ∘ synthesis` has an explicit `2×2`
matrix in this basis. Reconstruction preserves the resonant amplitudes and
its full differential residual is the synthesis of `S_n c`. Conversely,
every domain eigenvector is reconstructed from its two coefficients.

The unit-weight base and derivative-domain equivalences preserve original
Fourier coefficients and identify the full weighted equation with the
existing periodic operator. Thus the determinant criterion concerns the
original periodic spectrum, with nonzero eigenvectors preserved in both
directions. One open convex neighborhood and one cutoff `N≥1` make the
criterion valid on every full closed strip with `|n|≥N`.

Lemma 6.7(i), on source pages 40–41, is now proved for arbitrary complex
potentials and every finite Banach exponent. Reflected bilinear convolution
testing gives a Green identity for the actual free pencil and potential.
Applied to the reconstructed vectors, the exact residual identity forces
equality of both resonant diagonals. The common coefficient `a_n`, both
`b_n` coefficients, and the displayed common-diagonal matrix are implemented.

The printed unconditional reality clause in Lemma 6.7(ii) is false for
general complex potentials. Constant components `(a,b)` have the actual
correction `ab/(λ+nπ)` for `n≠0`. Choosing `(1,i)` gives `i/(2πn)` at a
positive central resonance. The formal counterexample meets the source's
half-size contraction at arbitrarily large indices. The source proof assumes
`φ*=±φ` for both conjugation identities; the corrected statement now
retains that condition.

The conditional identities in Lemma 6.7(ii) are now proved. Physical conjugation
is a norm-preserving involution on every symmetric weighted coefficient space,
including infinity. The potential star exchanges these conjugate-reflected
components; both Fourier coefficient identities characterize `φ*=εφ`.
For `ε²=1`, signed conjugation commutes with the actual domain potential and
intertwines the complementary inverse at `λ` with that at `conj λ`.

Uniqueness of the actual Neumann inverse proves the corresponding correction
identity. Its resonant action gives `a_n(conj λ)=conj(a_n(λ))` and both signed
off-diagonal exchange formulas. On the real spectral axis, the diagonal has
zero imaginary part for either reality type. A common open convex neighborhood
and frequency cutoff provide both inverse hypotheses throughout the full
closed strips. The argument covers every finite Banach exponent.

The source's basis order is now explicit. Physical coordinates use
`(e_n⁻,e_n⁺)`, and the displayed matrix uses the reverse order. The `b_n⁺`
and `b_n⁻` names have been corrected to follow the source definitions. An
explicit simultaneous reversal of both matrix indices gives the printed
form, preserves the determinant, and retains the eigenvalue criterion.
The actual potential-source vectors have exactly the component shifts
`φ_+(k+n)` and `φ_-(k-n)`. Thus the leading signed coefficients are the raw
second coefficient at `2n` and the raw first coefficient at `-2n`.

Equations (1.14)–(1.15) are now proved. The operator exchanges physical
components, its square preserves them, and continuous testing of its
convergent even Neumann series preserves those closed component subspaces.
The common diagonal is the odd correction. The off-diagonals are the even
corrections, with their actual Fourier leading terms removed by `T_n²`.
Individual unwanted terms vanish, and the remaining odd/positive-even
scalar series converge to the precise source coefficients and remainders.

The uniform shifted bound on `(Id-T_n²)⁻¹ Φe_n±` is now proved with the
source constant two and the exact opposite component norm. It also controls
the unweighted finite-exponent pair norm. The exact finite-series remainder
gives the geometric error `2·2⁻ᵐ`, uniformly on one open convex potential
neighborhood and every sufficiently distant full closed strip. One truncation
length works for both vectors and every parameter in that set.

The analytic assertion of Lemma 6.8 is now proved. Resolvent identities
normalize the complementary inverse at the strip center. Its domain-valued
extension is analytic and equals the actual inverse, including at central
lattice points and closed strip edges. Weighted convolution makes the actual
domain potential continuous linear in the potential; composition proves
joint analyticity of `T_n`.

Banach-algebra inversion and the squared factorization give analytic even
and full corrections on a proved open joint domain. Inverse uniqueness
identifies them with the existing Neumann constructions. Continuous resonant
extraction gives all three source coefficients with the correct basis labels.
One open convex potential neighborhood and one cutoff give joint analyticity
on every distant closed strip, explicitly accompanied by the small-square
witness and equality to the actual coefficients. All finite Banach exponents,
including `p=1`, are covered; the free complementary extension also covers
infinity in the existing `WithLp ∞` maximum pair norm.

The diagonal Hölder estimate on source pages 41–42 is now proved. The even
inverse and its source vectors commute with forgetting the weight. The unit
square has exactly the same norm in shifted and unshifted coordinates, so
the simultaneous contraction gives a vector bound with the unweighted
potential norm retained. The actual diagonal Fourier series is absolutely
convergent and is bounded by that vector norm times a reciprocal row norm.
For finite conjugate exponent this row norm equals the source's displayed
sum after the signed reindexing. The `p=1` endpoint uses the conjugate
infinity norm. The actual full-strip supremum is defined, bounded by this
same expression, and dominates all original coefficient values, uniformly
on one potential neighborhood and every distant closed strip.

Lemma 6.8(i) is now proved. Powered Young with inner exponent `min(p,p')`
constructs an outer `ℓ^p` sequence of reciprocal row norms. Contractive
exponent inclusion treats both sides of two. At the sampled frequency `2n`,
the exact support split at `N` separates a reciprocal tail from a potential
tail; this even improves the intermediate potential cutoff from `N/2` to `N`.
Appendix B.1 bounds the reciprocal tail, and the inner conjugate identity
produces the exact power `min(1,p-1)` after raising to `p`.

The actual full-strip supremum tail is an `ℓ^p` sequence. Its power series
converges and obeys the printed bound with the unweighted source pair norm
and `N/2` tail, with explicit constant `(8 max(p,p'))^p 2^(p-1)`.
All cutoffs beyond one threshold work uniformly on an open convex potential
neighborhood containing the given potential and zero. The source range
`1<p<∞` is retained for this summability result.

The reciprocal region estimates following (1.16) are now proved for every
finite `p>1`. Iterating powered Young constructs the exact nested row norm
sequence at `2n`. Its double power sum is jointly summable, and exchanging
the kernel indices preserves the norm. The exact support split puts the two
kernel tails at `N/2` and the near-near potential tail at `N`.

The two far regions have equal norms. Each has outer power sum at most
`C_p ‖a‖_p^p/M^min(1,p-1)` for reciprocal cutoff `M>0`, and the near majorant
has sum at most `C_p ‖R_N a‖_p^p`, where
`C_p=(16 max(p,p')²)^p`. These are actual convergent sums at the source inner
exponent `p'`, controlled through `min(p,p')`. The signed physical sum formula
is proved, including vanishing resonant-denominator terms.

The actual off-diagonal double Fourier series and their weighted Hölder
bounds are now proved. The first physical coefficient is reflected where
required by the source basis; both coefficient labels retain their correct
leading Fourier modes. Spectral-weight reflection is an exact isometry and
reverses the scalar shift. Two successive Hölder tests give joint absolute
convergence and the full-index form of (1.16), with the exact shifted vector
norm and double reciprocal row retained.

The half-contraction vector bound yields
`w(2n)|b_n^- - φ_-(-2n)| ≤ 2‖φ_-‖² ‖doubleRow(weight φ_+)‖`
and the corresponding positive bound with the components exchanged and the
first potential reflected. One open convex neighborhood and one cutoff give
both bounds for the actual coefficients and analytic extensions throughout
all distant closed strips, including `p=1` with conjugate infinity.

The proof-consistent weighted inequality in Lemma 6.8(ii) is now proved for
all finite `p>1`. A disjoint split avoids counting the far-far corner twice.
The near region retains both potential tails at `N`; regional power sums
then give an explicit exponent-only constant. Reflection preserves weighted
tails, and integer-half-cutoff decay loses at most three.

Both actual weighted full-strip remainder suprema have convergent power
tails with bound
`C_p ‖φ_±‖^p (‖φ‖^(2p)/N^min(1,p-1) + ‖R_(N/2)φ‖^(2p))`,
where `C_p=3·4^p·2^(p-1)·(16 max(p,p')²)^p`. One open convex potential
neighborhood and one threshold work for both signs and every larger cutoff.
This uses the `p`-power sum and full pair norm in the proof on source page 43.
The printed page-41 statement omits those left-hand powers and writes the
positive component in the first numerator; its literal form is not asserted.
See STATUS.md for the precise source-display qualification.

Lemma 6.9's uniform smallness, localization, and root-gap estimates are now
proved. Norm-and-tail neighborhoods make the actual suprema arbitrarily
small. The signed weighted leading coefficients also decay locally uniformly,
giving the source numerical bounds on all full coefficients. The scalar
analytic determinant equals the actual reduced determinant and has the
original periodic spectral zero criterion; at zero potential it is exactly
the centered square.

Any zero in a distant strip lies within `3π/32` of its center. On the circle
of radius `π/4`, the determinant perturbation is strictly smaller than the
centered square. Analyticity and matrix agreement share the same cutoff and
potential neighborhood. Cauchy's estimate gives the derivative bound `1/8`,
and the actual full-strip product supremum controls any pair of zeros by
`|ξ-η|²≤6|b_n⁺b_n⁻|_{U_n}`, without choosing square-root branches.

The scalar analytic zero count is now proved independently of the existing
spectral algebraic count. Local analytic factorization identifies each pole
of `f'/f` with its analytic zero order. Finite pole removal and Cauchy's
integral theorem give the disc argument principle. The principal logarithm
of a strict boundary ratio gives Rouché's theorem. Applied to the actual
determinant and its centered square, it gives count two on the closed disc,
open refined disc, and whole strip. A multiset representation yields two
roots allowing coincidence, exhausts all strip zeros, and records their
exact analytic orders. Their localization and factor-six gap estimate hold
on one open convex potential neighborhood with one signed-frequency cutoff.

The source displacement display has now been audited against the actual
operator. `SingleResonantPotential` places amplitudes at `-2n` and `2n`; the
complementary source vanishes and the actual determinant is `(z-nπ)²-ba`.
`RootDisplacementSourceAudit` uses equal real amplitudes to refute the printed
budget locally uniformly at zero, including on the valid small-square domain.
`RootDisplacementPower` proves a branch-free per-root power estimate and
separates both leading Fourier modes from their actual remainders.

The corrected displacement power sum is now proved. Injective frequency
sampling controls the two weighted leading coefficients by the pair Fourier
tail, retaining its cutoff boundary. The actual diagonal and remainder
suprema give one summable majorant for both roots. For `B=‖φ‖_(w,p)`,
`T=‖R_(N/2)φ‖_(w,p)`, and `δ=min(1,p-1)`, its sum is at most
`C_p [T^p + (B^p/N^δ+T^p)(1+B^p)B^p]`, with an explicit exponent-only
constant. Root selection preserves the scalar analytic multiplicities,
localization, and factor-six gap bound on the same open convex neighborhood
and signed-frequency cutoff; every larger displacement tail converges and
obeys this estimate. This is the corrected quantitative form of Lemma 6.9,
not the disproved printed display.

The weighted gap power tail is now proved for the same root sequences. For
`B=‖φ‖_(w,p)`, `T=‖R_(N/2)φ‖_(w,p)`, and `δ=min(1,p-1)`, its sum is bounded by
`G_p [T^p + E_p B^p (B^(2p)/N^δ + T^(2p))]`, where
`G_p=2^p (2^(p-1))²` and `E_p` is the existing off-diagonal summation constant.
The proof transfers weights to the full-strip product supremum, applies a
valid power-mean bound for every finite exponent, and sums the leading and
remainder majorants. No diagonal term is needed. The same open convex
neighborhood, signed cutoff, root localization, and exact analytic orders
support both displacement and weighted gap tails for every larger cutoff.

The bridge to the original periodic spectrum is now proved. Forgetting the
spectral weight commutes with the complementary inverse, so the weighted and
unit-weight determinants agree on their common contraction domain. The
uniform square estimate provides both domains together. On a distant disc,
the spectral count two and positivity identify each algebraic multiplicity
with the occurrence count in the scalar pair, hence with its analytic order.
The contour midpoint and squared gap coincide with the same pair's formulas.

`PeriodicResonantPair` records these original spectral identifications and
localization bounds. Any two such pairs agree up to exchange, and arbitrary
modewise label choices give exactly the same displacement and gap tails.
`exists_uniform_periodicRoots_with_power_sums` retains both quantitative sums
on the same neighborhood. `exists_uniform_periodicGapSummability` expresses
the weighted bound directly using the intrinsic contour-defined squared gap,
via `|γ²|^(p/2)=|γ|^p`. These are corrected original spectral versions of
Propositions 6.1 and 6.3, with the additive leading Fourier-tail terms retained.

The midpoint sequence consequence and ordinary boundary asymptotics are now
proved. `SpectralDisplacementTail` turns a convergent signed tail into global
`Memℓp` membership by adding only finitely many omitted modes. Convexity gives
the original contour midpoint exactly half the two-root displacement budget.
For reflected potentials, each ordinary Dirichlet or Neumann eigenvalue is a
periodic root in the same disc, so the existing displacement sum bounds both
branches on one common neighborhood and cutoff.

The completed interval extension pulls this estimate back to the source
period-one `CoeffPair p` for all finite `p>1`; both boundary displacement
sequences belong to `ℓp` and retain every larger quantitative tail. The physical
interval extension also gives the actual original `L²` boundary eigenvalues
square-summable displacements, together with their unique high-disc spectral
characterization on the same neighborhood.

The auxiliary coefficient realization is now proved. `AuxiliaryPhase`
constructs `G(f₋,f₊)=(f₋,if₊)` as a linear isometry in both base and domain
norms, and verifies the exact operator and pencil conjugation with potential
`(iφ₋,-iφ₊)`. Neumann-reflected potentials become Dirichlet-reflected ones.
The phase images give the auxiliary closed complementary spaces, their raw
`±i` reflection conditions, and the same decomposition at all real Sobolev
regularities. Domain inclusion preserves the auxiliary boundary condition.

`AuxiliarySpectrum` defines the actual restricted auxiliary operator and
pencil; its resolvent set is actual bijectivity. Restricted-pencil conjugation
then proves equality with the ordinary spectrum at the transformed potential.
The spectra are closed, discrete, finite in bounded sets, and every spectral
point has a nonzero eigenvector in the actual auxiliary domain.

The source Neumann potential extension feeds both auxiliary branches.
`exists_uniform_auxiliaryPeriodOneAsymptotics` supplies both starred source
coefficient branches with global `ℓp` displacement membership, unique actual
high-disc spectral identification, and every larger corrected power tail on
one open convex potential neighborhood. Together with the ordinary branches,
this proves all four coefficient displacement conclusions in Corollary 6.2.
The budgets use the actual reflected/conjugated potential tails.

The actual auxiliary root-chain recursion is now identified level by level
with ordinary boundary chains. Its full root space is finite dimensional and
stabilizes, and its dimension equals the conjugate ordinary multiplicity.
`AuxiliaryCountingData` records actual spectral localization, central algebraic
count `2N+1`, and simple high-disc eigenvalues for both auxiliary restrictions.
These hold on one open convex neighborhood containing the given potential and
zero, for every larger cutoff, including after source period-one extension.

The original auxiliary H¹ endpoint conditions in (1.10) are now defined
independently of Fourier coefficients. Physical phase conjugation identifies
them with the ordinary endpoint conditions and intertwines the actual
differential expression. The source phased extension reconstructs the original
function on the closed interval and gives a unique auxiliary weighted-domain
representative. Actual Fourier integrals define the Neumann potential extension;
its conjugation identity proves equality of original auxiliary eigenvalue sets
with the actual coefficient spectra. Both directions of the physical/coefficient
eigenvalue equation transfer are proved, completing this physical form of
Lemma 5.1.

The auxiliary physical domain now stores actual closed-interval functions and
has exactly the original component-sum H¹ norm. Phase rotation is an isometry
from the ordinary domain, proving completeness. Actual Fourier extension and
restriction are continuous linear inverses with bounds `1` and `√2 π`.
Physical L² phase isometries transport inclusion and the differential operator;
representative theorems prove their actual physical action. The independently
defined physical pencil is invertible exactly at the conjugate ordinary
resolvent parameters. Its bounded inverse satisfies both original-space inverse
identities, and its base-space resolvent is compact. The resulting unbounded
operator has precisely the original auxiliary endpoint domain, is densely
defined and closed, and has spectrum equal to the original auxiliary eigenvalue
set and the actual coefficient auxiliary spectrum.

Actual physical auxiliary generalized root spaces now use the original
pencil and H¹ domain at every chain step. Phase conjugation identifies every
level and full root space, proving stabilization and finite dimension.
Algebraic multiplicity is the actual physical full-root-space dimension and
agrees with the auxiliary coefficient multiplicity at the Neumann extension.
Physical clusters give central count `2N+1` and simple high-disc eigenvalues.
One common open convex L² neighborhood supports both counting data and analytic
high-index branches, together with full square-summable displacements and
all larger quantitative tails. This completes the physical starred part of
Corollary 6.2.

The completed half-interval map now preserves conjugation with index reversal
at every `1<p<∞`, including its odd Hilbert tail. Hence both signed source
extensions preserve real type, in particular the Neumann potential extension
used by both auxiliary problems. Proposition 5.2(iv) now holds for source
period-one coefficient potentials. Actual Fourier-integral compatibility also
proves it for arbitrary real-type original physical L² potentials, with the
real-type hypothesis imposed only a.e. and invariant under representatives.
Both actual auxiliary resolvent sets contain every nonreal parameter.

Both bounded period-one auxiliary eigenfunction extensions are now constructed
in the source's actual component-sum pair norms. Their finite Fourier formulas
are the actual integrals of the phased reflection, and density proves uniqueness
of the completed map. Compatible finite H¹ inputs agree with the original
Sobolev extension. The maps have an explicit common bound at every `1<p<∞`,
are analytic into the closed source-norm auxiliary targets, and preserve the
source norm exactly at `p=2`. The constant input `(0,1)` also proves that the
strict lower exponent restriction cannot be dropped.

The free spectral products now have an explicit symmetric cutoff and a proof
that pairing positive and negative indices equals the original integer cutoff,
including zero factors. Euler's product proves convergence at every complex
parameter. The full product gives `(2 cos λ)^2-4` with prefactor `-4`; the even
subproduct gives `2 cos λ-2` with prefactor `-1`. The formal source audit above
refutes the printed prefactors in Lemma 8.1(ii) and determines their necessary
replacements from free values.

The full perturbed periodic product now converges pointwise off `πℤ`.
The free resolvent and Sobolev embedding make relative displacements absolutely
summable at every finite Banach exponent. The actual finite central polynomial
retains original algebraic multiplicities; distant counted pairs supply the
tail. The resulting product has exactly the actual periodic spectral zeros
off the lattice and is unchanged by modewise label exchanges. For large finite
cutoffs, all artificial central free factors cancel and only constant
normalizations remain. One open convex neighborhood and threshold support
this construction for every larger central cutoff and every finite `p>1`
potential, using the already proved displacement and counting results.

The products now converge locally uniformly in the spectral parameter off
`πℤ`. Half-gap balls give summable uniform relative majorants, while compact
quadratic majorants upgrade the free Euler products on the whole plane.
The actual normalized polynomial cutoffs converge to a holomorphic limit off
the lattice, and their derivatives also converge locally uniformly there.
This stage concerns fixed potentials; uniform convergence in the potential
is established in the later stages below.

The actual products now extend to entire functions, with polynomial and
derivative convergence locally uniform on the whole plane. The maximum
modulus principle transfers uniform Cauchy estimates from circles avoiding
the countable lattice to their discs. Continuity uniquely fixes the filled
values. Reciprocal maximum-modulus bounds prevent extra zeros at lattice
points, while every actual spectral value makes all sufficiently large
cutoffs vanish. Thus the entire zero set is precisely the original periodic
spectrum, and pair-label independence holds globally.

The entire product now has the exact original spectral algebraic multiplicity
as its analytic order at every complex parameter. Finite spectral polynomials
have the prescribed central exponents and counted pair orders. Disjointness
identifies the unique contributing factor, and Rouché stability on isolating
discs passes these orders to the limit. Infinite analytic order is excluded
explicitly, including at filled free lattice points.

The central-cutoff choice is now eliminated. Enlarging the central cluster
absorbs exactly the intervening disjoint spectral pairs, preserving their
original multiplicities and the constant normalization. All sufficiently large
finite polynomial cutoffs agree exactly, including at spectral zeros. Uniqueness
of limits gives equality of the entire functions for arbitrary admissible
cutoffs and pair labels. Every finite `p>1` potential has one such function for
all larger cutoffs, retaining exact orders and polynomial/derivative convergence.

The finite polynomial part of potential analyticity is now proved. Generalized
root chains of the contour reduction agree with the original domain recursion,
so the determinant has exactly the original spectral multiplicities. Local
projection transport and the finite determinant formula give joint analyticity
of all sufficiently large central polynomials on one potential neighborhood.
Their normalized limits define the canonical full periodic product directly
from the potential, with the exact original zeros, orders, and locally uniform
spectral-parameter and derivative convergence.

The relative-product tails are now controlled uniformly over actual potential
neighborhoods. Finite products satisfy exponential perturbation bounds even
when factors vanish. A fixed finite conjugate-exponent multiplier has uniformly
small absolute tails on bounded `ℓp` families, although those families may have
no uniform coordinatewise tails. Reciprocal free denominators give these
multipliers on closed half-gap balls. The corrected root displacement budget
supplies one common displacement norm bound on an open convex potential
neighborhood, proving uniform paired relative-product convergence there without
continuity of root labels.

The central and free factors are now restored. Central root localization and
the exact total multiplicity give a uniform bound for the central correction.
Finite spectral covers preserve the unrestricted potential factor, and maximum
modulus fills the free lattice uniformly over it. One open convex potential
neighborhood works for every compact spectral set. The intrinsic approximants
therefore converge locally uniformly jointly in both variables, and their
eventual joint analyticity proves joint continuity of the canonical product.

The Banach-space derivative limit argument is now proved. Schwarz estimates
turn uniform function differences on a larger ball into operator-norm bounds
for Fréchet derivative differences on a smaller ball. Local uniform analytic
approximation is preserved by differentiation, giving continuous complex
Fréchet derivatives of every finite order. Applied to the canonical product,
this proves joint complex smoothness, locally uniform operator-norm convergence
of the polynomial derivatives, and entire restrictions to every complex affine
line. The hypotheses use actual joint balls, not a compactness assumption on
the infinite-dimensional potential domain.

Joint Banach-space analyticity is now proved. Schwarz estimates on equally
spaced nested balls give geometric bounds for the factorial-normalized Fréchet
Taylor coefficients and a positive operator-norm convergence radius. Along
every complex affine line, the same coefficients are the ordinary Taylor
coefficients of an entire scalar function. Cauchy's theorem identifies the
sum with the canonical product, yielding its actual joint Fréchet power
series. Potential and weighted pullbacks and all mixed iterated derivatives
are analytic as well.

The odd free-product identity and complete-sequence perturbed parity products
are now proved. Affine reindexing preserves finite-exponent ℓp displacements.
Exact finite cutoff identities keep the zero-mode denominator and the literal
asymmetric odd interval. The resulting even and odd limits are entire, with
locally uniform polynomial and derivative convergence, including at p=1 and
free lattice points. Their free specializations recover Δ−2 and Δ+2 with
prefactors −1 and 4.

Actual central parity root multisets and polynomials are now constructed.
Parity root-space dimensions count the original Jordan chains and sum to the
full algebraic multiplicity. Projection commutation distributes parity over
finite spectral clusters, turning central rank counts into exact multiplicity
sums. The two central polynomials multiply to the full original polynomial,
with the precise parity zero sets and analytic orders. Root multisets retain
shared eigenvalues and have the exact uniform central cardinalities.

The actual central roots are now assigned two slots per parity index and
spliced into the distant counted pairs. Finite replacement preserves ℓp
displacements. The completed sequences enumerate exactly the original parity
eigenvalues, including the weighted-domain eigenvector characterization.
Their entire parity products have exactly these whole-plane zero sets:
spectral isolation and reciprocal maximum-modulus bounds prevent extra zeros
when filling the free lattice. Both the literal cutoffs and their derivatives
converge locally uniformly in the spectral parameter. Actual data supply this
construction on common neighborhoods and central thresholds for finite p>1.

Label and cutoff independence of the actual parity products is now proved.
Larger central polynomials absorb the counted pairs in their parity. Even
literal cutoffs are intrinsically normalized central polynomials at `2M`;
odd cutoffs retain one additional counted boundary factor at `2M+1`. All
sufficiently large finite cutoffs agree exactly for arbitrary admissible
central cutoffs and root labels, including at spectral zeros. Uniqueness of
limits gives one pair of entire functions independent of these choices.

Exact analytic orders of both actual parity products are now proved. Every
fixed point eventually lies inside the central box, where the intrinsic parity
polynomial has the original order and the odd boundary factor has order zero.
Spectral isolation and Rouché stability pass these orders to the entire limits.
The orders of their product add to the full original spectral multiplicity.
The neighborhood existence theorem retains these orders and choice independence.

The actual parity products now multiply exactly to the canonical full product.
The literal finite identity retains the positive odd boundary factor; bounded
spectral displacements make this factor tend to one. Completed central labels
also identify every sufficiently large full cutoff with the intrinsic normalized
central polynomial. Thus the limit fixes the entire normalization, and its
spectral derivative satisfies the product rule. Actual potential neighborhoods
admit choice-independent entire factors with exact orders and this identity.

Joint analyticity of the finite central parity polynomials is now proved on
the actual even-supported potential subspace. The parity contour projection
has precisely the full contour range intersected with the parity subspace.
Its analytic transport gives a fixed finite-dimensional operator whose root
chains and characteristic-root multiplicities equal the original parity root
spaces. Its determinant is therefore the actual central parity polynomial.
All sufficiently large normalized parity approximants are jointly analytic on
one common neighborhood, with the corrected prefactors and odd endpoint intact.

Joint uniform convergence of the parity approximants is now proved. Complete
paired products converge uniformly over every norm-bounded displacement family
on each spectral compact set; affine parity sampling preserves a common norm
bound. The fixed central box bounds all central root labels, so actual completed
pairs have one displacement bound over an open convex potential neighborhood.
Both literal parity cutoffs therefore converge uniformly over its even-supported
potentials. The odd boundary factor and its inverse tend uniformly to one,
with simultaneous eventual nonvanishing. Removing it proves uniform convergence
of both intrinsic central parity approximants at `2M` to their actual products.

Intrinsic parity limits are now defined directly from the potential, agree
with every admissible completed-root construction, and retain its exact
orders and factorization. The normalized polynomials converge uniformly on
actual joint neighborhoods of the even-supported potential space. Combined
with eventual analyticity, this gives complex smoothness, uniform convergence
of Fréchet derivatives, and positive-radius Taylor expansions. Both limits
are jointly analytic, including on the source period-one coefficient space
and at spectral collisions. Every mixed iterated derivative is analytic.

The classical fundamental solution is now constructed for arbitrary continuous
potentials on the full unit interval. A factorial Picard-iterate estimate
proves existence and uniqueness without restricting the coefficient size.
The solution satisfies the original physical spectral equation. Its normalized
columns have Wronskian one, their matrix propagates every initial vector, and
the monodromy trace detects periodic and antiperiodic solutions through the
characteristic determinant. The free trace is exactly `2 cos z`.

The classical construction is now jointly analytic in the spectral parameter
and continuous potential. The coefficient-to-Volterra map is bounded complex
linear, and its factorial power bound makes `1-V` invertible for every
coefficient size. The inverse equals the earlier initial-value solution and
depends analytically on the coefficient in the supremum norm. Composing with
the actual joint coefficient map proves analyticity of the monodromy, trace,
and boundary determinants, including at multiple roots. All mixed derivatives
of the trace are analytic.

The forward bridge from original Hilbert parity eigenvectors to classical
monodromy is now proved for potentials with a continuous representative on
the unit interval. Absolute continuity and the almost-everywhere original
equation give the constructed classical solution. Fourier parity supplies
the endpoint sign and makes restriction to the unit interval injective.
Nonzero eigenvectors have nonzero initial values, so intrinsic even and odd
product zeros force trace values `2` and `-2`. Their zero sets are disjoint;
full-product zeros force zeros of the classical discriminant squared minus four.

The reverse spectral bridge is now proved under the same Hilbert and continuous
representative assumptions. Signed repetition of a classical endpoint solution
has weighted Fourier coordinates with the correct parity. An almost-everywhere
parity translation identity makes unit-interval vanishing determine an original
base vector, so the original eigen-equation can be checked on that interval.
The extension therefore gives a nonzero original parity eigenvector. Intrinsic
even and odd product zeros are now equivalent to trace values `2` and `-2`;
the full-product zero set equals the trace-squared-minus-four zero set.

The inhomogeneous bridge is now proved for original domain-valued sources.
The inverse Volterra operator constructs physical C¹ forced solutions, with
uniqueness among absolutely continuous almost-everywhere solutions. The source
signs agree with `(z-L)a=b`. Fixed-parity source equations can be checked on the
unit interval, and signed extension proves the converse. Fixing the initial
vector gives a unique original preimage. At every finite root-chain length,
extending a prescribed original source is equivalent to a two-coordinate
classical endpoint equation involving the zero-initial forced solution.

The normalized zero-initial chain operator now gives the exact spectral
factorization and a convergent whole-curve Taylor series with positive radius.
Every spectral derivative is the corresponding signed chain curve multiplied
by its factorial. Evaluating the two columns gives the same series and derivative
identities for the fundamental matrix and actual monodromy. The boundary matrix
series has constant coefficient `M(z)-σI` and signed chain endpoints thereafter.

Finite original parity chains are now identified with the actual boundary
Taylor equations. Their classical curves are finite convolutions of normalized
chains and arbitrary initial values. Alternating those initial values gives
the ordinary Taylor coefficients. The finite boundary convolution is a linear
map on finitely many complex pairs; each kernel vector yields a unique original
chain top vector, and each original finite parity root vector has a unique
representing kernel jet.

The reconstruction is now complex linear, with the actual physical curve and
initial values retained. Domain inclusion gives a linear equivalence of each
finite boundary Taylor kernel with the corresponding original parity root
space. All finite nullities agree with the original root dimensions, increase,
and eventually equal the full original parity algebraic multiplicity. The
free nullity sequence is computed exactly at all lengths and Fourier indices.

Scalar truncated multiplication is now identified with its formal Taylor
convolution, with exact nullity `min(N,m)` for a scalar series of order `m`.
Its formal order equals the analytic vanishing order for convergent Taylor
series, including infinite order. Diagonal two-by-two formal systems split
linearly and have eventual nullity equal to their determinant order. The
actual monodromy boundary maps now equal the formal matrix Taylor actions
built from their convergent coefficients.

General formal matrices now reduce to diagonal form through row and column
units. Every finite nullity is preserved, and for nonzero determinant it has
the exact form `min(N,a)+min(N,b)`, where `a+b` is the determinant order. A
singular formal matrix has nullity at least `N`; the original root-dimension
bound therefore proves that each actual boundary formal determinant is
nonzero. Its order now equals the original parity algebraic multiplicity.

Scalar Taylor extraction now respects multiplication, by the iterated
product rule and its factorial coefficients. Consequently, forming the
formal determinant commutes with the convergent matrix Taylor expansion.
Classical analytic boundary determinant orders now equal original parity
algebraic multiplicities. The shifted traces `Δ−2`, `Δ+2` and the full
characteristic function `Δ²−4` have the exact original multiplicities,
and hence the same vanishing orders as the intrinsic canonical products.

Equal finite orders now give canonical filled quotients that are entire and
nonvanishing. The actual shifted traces and full characteristic function
factor exactly as those quotients times their canonical spectral products,
including at common zeros. The parity quotients multiply to the full quotient.
A bounded quotient is a nonzero constant; a prescribed finite limit at infinity
determines that constant and, in particular, a limit of one proves normalization.

The first product estimates at infinity are now proved. On a fixed vertical
line, all free denominators dominate their height-one values once the absolute
imaginary height is at least one. The existing finite-exponent resolvent
summability gives a common summable majorant. Dominated convergence makes the
absolute relative-displacement sum tend to zero; an exponential product bound
then makes the relative product tend to one. Rescaling retains the even and
odd signs, and completed actual pairs transfer this limit to all three
canonical products for every finite `p>1` and even-supported potential.

The classical solution now has an exact scalar Duhamel formula in each
coordinate after multiplication by any common exponential weight. The weights
`exp(izt)` and `exp(-izt)` isolate the decaying coordinate in the upper and lower
half-planes. The decaying kernel has integral at most the reciprocal decay
rate, uniformly in the oscillatory part. Its actual coordinate error is thus
bounded by `‖Φ‖ B/(2|Im z|)`, provided the opposite weighted coordinate is bounded
by `B`. Nonzero triangular potentials verify both signs and the height-two
constant `1/4`.

The coupled integral equations now close this bound without a hypothesis on
the unknown solution: for decay rate `a≥2‖Φ‖²`, the slow coordinate is bounded
by `2(|u(0)|+‖Φ‖|v(0)|/a)`. Applying this to the two normalized columns gives
trace error at most `2‖Φ‖²/a+2‖Φ‖²/a²`. Thus the exponentially normalized
classical trace tends to one at both imaginary ends, and every fixed shift
of the trace, as well as `Δ²−4`, has ratio one to its free function. These
limits allow an arbitrary varying real spectral part for fixed continuous
potentials.

The classical/canonical filled factors now tend to one at both ends of every
fixed vertical line. For compatible continuous Hilbert potentials, boundedness
alone therefore proves each exact normalization by Liouville's theorem.
Outside fixed discs around `πℤ`, the scalar free resolvent has a common operator
bound into `ℓ¹`. Finite Fourier inputs tend to zero as `|z|→∞`, and density plus
equicontinuity extends this to all finite Banach exponents. Consequently the
absolute relative-displacement sum vanishes there. Full and parity spectral
products, and all intrinsic canonical products for finite `p>1`, have ratio
one to their free functions along every such escaping path, including real
midpoints between consecutive lattice points.

A real phase gauge now removes the real spectral part without changing either
the potential supremum norm or the solution norm. Gronwall gives the global
trace bound `|Δ(z)|≤2 exp(|Im z|+‖Φ‖)`, uniform in the real part and on potential
norm balls. Every free sphere lies outside all open free discs. Maximum modulus
therefore extends an exterior entire-function bound across every disc, and
compactness handles an omitted bounded central region. Exact parity and full
normalization now reduce to a quotient bound at large exterior parameters.

The remaining quotient bound is now proved. Periodic reduction bounds both
free parity inverses on every horizontal strip outside fixed free discs. The
classical half-plane limits give bounds above and below this strip. Pulling back
real at-top filters turns the canonical exterior limits into one uniform
positive lower bound for all large separated spectral parameters. Division
then bounds the actual filled quotient at exterior infinity. Maximum modulus
and its vertical limit fix the entire factor to one. Thus the corrected
identities `f=Δ−2`, `g=Δ+2`, and `fg=Δ²−4` hold for every even Hilbert potential
with a compatible continuous representative, at every complex parameter.

Parity-preserving finite Fourier truncations now converge inside each parity
subspace at every finite exponent, and lift to the original one-derivative
domain. The exact classical identity on even Hilbert domain potentials and
continuity of both products imply `f+2=g−2` for every even Hilbert potential,
without any continuous-representative assumption. The intrinsic discriminant
is now defined as `f+2`, jointly analytic for finite p>1. At p=2 it equals
`g−2`, its square minus four is the full spectral product, and its ±2 levels
are the original parity spectra. Classical traces of any convergent even domain
approximation have this intrinsic limit, with only Hilbert-norm convergence.

The exponent comparison is now proved for arbitrary common potentials. The canonical contractive base and domain inclusions
commute with the actual spectral pencil. A larger-exponent domain vector has
absolutely summable coefficients; its equation with a smaller-exponent potential
and source recovers the derivative at that smaller exponent. Induction transports
every finite generalized root space onto its counterpart. Full root spaces,
spectra, and both parity multiplicities agree, hence so do all normalized central
polynomials and all canonical products. Density of the Hilbert image above two,
and direct comparison below two, establish `f+2=g−2` for every finite p>1.
The squared discriminant minus four is the full product, with exactly the
original spectral zeros and multiplicities. Its values on the dense absolutely
summable Hilbert potentials uniquely determine the continuous extension.

The printed cosine-quotient domain is now audited using arbitrarily large free
cosine zeros in the exterior. A valid additive formulation is proved for each
fixed even potential at finite p>1: both `Δ−2 cos` and `Δ′+2 sin`, divided by
`exp(|Im z|)`, tend to zero uniformly in sufficiently large exterior parameters.
The derivative proof uses Cauchy circles of half the separation radius.

The normalized reciprocal sine is now bounded on the full exterior, using
compact periodic reduction on a strip and an explicit constant-four bound
above imaginary height one. Hence `Δ′/(−2 sin) → 1` at every fixed potential,
with uniform spectral thresholds. All sufficiently large critical points lie
inside arbitrary radius-r free discs, for 0<r≤π/4. The entire derivative is
nontrivial, with finite orders, isolated zeros, and finitely many zeros on
every compact set. Its zero-potential critical set is exactly πℤ.

The free derivative now has exact order one at each lattice point, count one
in a disc of radius less than π around it, and count 2N+1 in the central disc.
Rouché transfers these counts to Δ′ beyond a fixed-potential cutoff, with no
boundary zeros. The count-one multiset gives a unique simple critical point
strictly inside each distant disc. The central and distant open discs exhaust
all critical points, with one common cutoff and any 0<r≤π/4.

For each tolerance, the corrected displacement budget now becomes small on
one open convex potential neighborhood. Complete actual parity pairs have
bounded full displacement norms and small tails there. Uniform finite-head
resolvent decay plus the common tail bound makes both absolute relative sums
small at exterior infinity. Exponential product control and parity subsum
comparison give simultaneous full/even/odd canonical ratio estimates.

The valid additive trace and derivative asymptotics, and the derivative ratio,
now have one potential neighborhood and one spectral threshold for each positive
tolerance. Both may depend on the tolerance. Joint limits permit the potential
to converge while the spectral parameter escapes. The cosine-quotient source
audit remains in force.

The neighborhood derivative estimate now gives one integer cutoff for the
distant count one and the central count 2K+1, simultaneously for all nearby
even potentials and every larger central cutoff. Both boundary families are
zero-free; each distant critical point is unique and simple. The central and
distant open discs exhaust all critical points on that same neighborhood.

Real-type critical points are now proved real. Gauss–Lucas excludes nonreal
critical points of the positive-degree central spectral polynomials. The
nontrivial canonical derivative has finite orders, so locally uniform limits
preserve nonvanishing off the real axis. Differentiating Δ²−4 transfers this
to Δ′. One theorem now packages every assertion of Lemma 8.3.

The free-reference off-diagonal product estimate is now proved. Keeping the
signed linear term gives a quadratic infinite-product remainder bound.
Arbitrary half-unit sampling perturbations change the bounded Hilbert
transform by an ℓ¹ square-kernel convolution. Young puts the absolute rows
in ℓ^(2p); Hölder returns their squares to ℓᵖ. Rescaling gives the spectral
relative product with its local factor omitted, uniformly on displacement
norm balls and over all samples in closed half-π free discs.

A positive lp majorant now controls the off-diagonal product throughout every
free disc at once. Filled sine quotients have exact center values and a
uniform disc bound. Restoring the local factor gives a filled local product
whose sampled error from sine belongs to lp, uniformly on displacement norm
balls. Off the lattice it agrees exactly with sine times the full relative
product, even when spectral numerators vanish.

The paired product is now identified off the lattice as minus four times the
restored sine factors. Maximum modulus carries the lp majorants through all
free centers, and Cauchy controls derivatives on smaller discs. Rescaling
both parities and interleaving their coefficient majorants transfers the
bounds to the actual canonical discriminant. One open convex potential
neighborhood supplies common lp norm bounds for every admissible sampling
sequence. This completes both sampled error assertions and the local
uniformity of Lemma 8.4.

The inverse filled sine quotient now bounds a critical-point displacement
by its sine value. Lemma 8.4 controls the distant critical roots in lp.
The 2N+1 central analytic roots are enumerated with multiplicities and
spliced into the unique simple distant sequence. The completed sequence
has exact global analytic multiplicities and an lp displacement bound
uniform on one open convex potential neighborhood. This proves the
displacement assertion of Lemma 8.5.

The normalized single product is now constructed from the literal cutoffs
`2 ∏[-N,N] (ξn−z)/πn`, with exceptional denominator one at zero. Euler
products fix the free limit as minus twice sine. Local uniform convergence
extends through the free lattice, including derivative convergence. The
filled product has exactly the selected closed root set, hence exactly the
critical zero set for a complete critical labeling. Its quotient by minus
twice sine tends to one along every separated escaping path.

Each critical-root fiber is now proved finite, and finite cutoff orders
stabilize to the derivative's analytic multiplicities. Rouché stability
on isolating discs transfers these orders to the entire product. The
filled quotient is entire, tends to one on the free-disc exterior, and
is globally bounded by maximum modulus. Liouville and an escaping
cosine-zero sequence fix the quotient to one. This proves the derivative
product identity and locally uniform cutoff convergence on the whole
plane, together with the previously obtained locally uniform lp bounds.

Finite multisets can now be enumerated in order on prescribed finite
ordered index sets, retaining repetitions. A separate complex lexicographic
relation orders the central critical multiset. Replacing the central head
preserves complete labeling and all multiplicities. Real-part bounds order
the two distant tails and separate them from the central cluster. Thus
complete ordered critical sequences now exist on a common potential
neighborhood, with lp norm bounds and the exact derivative product.

Ordered finite enumerations are now unique even with repetitions. A
complete critical sequence remains a valid labeling at every larger
central cutoff. Comparing two sequences at a common cutoff proves global
uniqueness. Canonical critical coordinates and their lp displacement
coefficient are now defined, with exact multiplicities, reality at
real-type potentials, the derivative product, common local norm bounds,
and exact free values `nπ`.

Joint continuity now gives locally uniform potential limits of the
discriminant and its derivative. Compact root confinement and Rouché
preserve zero-free compact sets and circular counts. Distant canonical
coordinates are continuous at every even potential; imaginary parts of
all canonical coordinates are continuous at real-type potentials.
Restricting root multisets to central subsets now identifies analytic
counts with counts of canonical indices, retaining repeated roots.

Real-diameter discs now separate prefixes and suffixes of the real
critical sequence. Their zero-free boundaries preserve counts under
perturbation, and finite ordered-count bounds trap each nearby real part
between arbitrarily close barriers. This proves full canonical coordinate
continuity at real-type potentials, including central collisions and
complex even perturbations. A combined theorem now packages all assertions
of Lemma 8.5 with the canonical roots and their common local lp bounds.

Conjugation symmetry now passes from finite parity polynomials to the
discriminant. Its values and derivatives are real on the real axis at
real-type potentials. Real Rolle and distant critical uniqueness give
strict interlacing between distinct actual distant gap endpoints.
Multiplicity at least two proves the collapsed-gap equality, even for
complex potentials. The canonical critical coordinates therefore lie
in every sufficiently distant actual real periodic gap, regardless of
the order of the pair slots.

The full central periodic multiset now retains every original algebraic
multiplicity and is the sum of the parity multisets. An ordered paired
enumeration sorts it without losing repeated values. Complete endpoint
labelings record this central multiset, the exact original distant
pairs, and both lp displacements. Sorting the distant slots and replacing
the center preserves these data. Real-part separation proves global
lexicographic order on one potential neighborhood at every sufficiently
large cutoff.

Ordered paired multiset uniqueness and central cutoff growth now prove
that the complete ordered endpoint sequences are independent of cutoff.
Canonical left and right endpoints retain spectral exhaustion, real-type
reality, and lp displacements. One neighborhood gives common valid cutoffs
for these fixed coordinates. At zero potential both endpoints are exactly
`nπ`, with identically zero displacement coefficients.

The periodic product now has locally uniform parameter limits and stable
circular counts on the full potential space. Within the central real-part
bounds, these analytic counts equal counts of both endpoint slots, including
repeated values. Compact confinement controls imaginary parts; stable
prefix and suffix counts control real parts. Both canonical endpoint
coordinates are now continuous at real-type potentials under arbitrary
even complex perturbations, including spectral collisions.

Real scaling preserves real type and produces continuous canonical
endpoint paths. The endpoint discriminant levels cannot change along
these paths, so their free values identify each signed index's parity.
Filtering by these levels recovers the exact central parity multisets.
Neighboring real gaps are strictly separated; Rolle and repeated-root
multiplicity give a critical point in every open or collapsed gap.

One distinct critical witness per real gap now exhausts the full central
critical multiset at every common cutoff. Ordered enumeration uniqueness
identifies each witness with its canonical critical index. This proves
global indexed interlacing, strict inequalities for open gaps, and equality
for collapsed gaps. Each real gap contains exactly one critical point,
and every critical point belongs to exactly one gap. The canonical critical
sequence is strictly increasing, so the exact multiplicity formula makes
every critical point simple, with nonzero second discriminant derivative.

A strict real second-derivative test and the real-axis derivative bridge
now make every canonical critical coordinate a strict local maximum or
minimum, including at collapsed gaps. Fermat's theorem identifies all
real local extrema with the canonical critical sequence; each indexed
gap contains exactly one.

The exact factorization behind Lemma 8.6 is now proved. Deleted-pair
polynomial cutoffs and their derivatives converge locally uniformly on
all of the complex plane. Their entire limit `Gₙ` gives
`∆²−4 = −4((λ−τₙ)²−γₙ²/4)Gₙ`, correcting the printed positive sign.
At a canonical critical point, with `a = λₙ•−τₙ`, differentiation gives
`(2Gₙ+aGₙ′)a = γₙ²Gₙ′/4`; a nonzero coefficient yields the exact quotient
formula without dividing by the gap. At zero potential `Gₙ` is the square
of the filled sine quotient and has value one at the removed root.

The remaining product now equals the squared free sine quotient times
the two omitted-diagonal relative products off the free lattice, including
at actual endpoint zeros. Maximum modulus and Cauchy's estimate give
bounded lp majorants for its error and derivative error on half-pi and
quarter-pi discs. These estimates hold on a common potential neighborhood
for the canonical product. Canonical endpoint displacements now have
bounded full norms and arbitrarily small local tails; ordering preserves
the original pairwise tail estimates.

Free squared-quotient displacement bounds now give locally uniform lp
tail representatives for `Gₙ(cₙ)−1` and `Gₙ′(cₙ)`. Finite modification
proves full lp membership at each fixed potential. The actual midpoint
offset has locally bounded lp norm, and the bounded multiplier estimate
therefore gives locally uniform lp tails for `2Gₙ+aGₙ′−2`, retaining the
exact squared-gap identity at all even complex potentials.

A finite-block and small-tail split now makes the relative products
uniformly close to one on distant free discs. Maximum modulus, Cauchy,
and arbitrarily small critical localization give uniform smallness of
`Gₙ(cₙ)−1` and `Gₙ′(cₙ)`. The midpoint coefficient consequently has norm
at least one on a common tail. Its exact quotient supplies locally
uniformly bounded lp coefficients in `cₙ−τₙ=γₙ²aₙ`, completing Lemma 8.6
for all finite exponents greater than one and all even complex potentials,
including collapsed gaps. This uses genuine uniform small-tail control,
not decay inferred from a bounded lp ball.

The real gap characterization is now complete. Positive real pair
denominators and the negative full-product normalization give the correct
cutoff signs. Passing to the limit and using spectral exhaustion proves
that closed gaps are exactly where `|∆|≥2`, open interiors exactly where
`|∆|>2`, and endpoints exactly where equality holds. Continuity and the
known endpoint parity give `(-1)^n ∆≥2` on each closed gap, strictly inside
an open gap, for every signed index.

Complete actual Dirichlet and Neumann sequences now enumerate the central
root multisets and the distant simple branches, retaining every algebraic
multiplicity and lp displacement. One neighborhood and cutoff work for
both boundary conditions. The ordinary period-one interval extension
transfers these results to source coefficient potentials. The normalized
Section 9 cutoffs now converge locally uniformly to entire functions with
exactly the actual boundary spectra as their zeros; the free value is
`sin λ`. This proves the fixed-potential product construction, without
yet claiming independence from central label choices or joint analyticity.

Complete boundary labelings now retain their exact central multisets at
every larger cutoff. The normalized intrinsic central polynomials therefore
identify all such products, independently of labels and cutoff. Their limit
defines the intrinsic Dirichlet and Neumann characteristic functions, with
locally uniform convergence of values and first spectral derivatives. Finite
root-polynomial orders and Rouché stability identify the exact analytic zero
orders with the original restricted-operator multiplicities. Both intrinsic
functions equal sine at zero potential. All these conclusions also hold for
the original period-one coefficient realization.

Projection transport now gives intrinsic shifted determinants on varying
finite spectral ranges, jointly analytic even at determinant zeros. Boundary
contour restrictions retain all original generalized root chains and
algebraic multiplicities. Their determinants equal the actual finite
boundary root products. Consequently one open convex neighborhood and
threshold give joint analyticity of both normalized central polynomials
at every larger cutoff, including after the source interval extension.

Complete ordinary boundary root displacements now have uniformly bounded
full lp norms: distant roots belong to the corresponding periodic pair,
and the common central box bounds every central enumeration. Hölder tails
give single-product convergence uniform over bounded families off the free
lattice; maximum modulus fills the free centers uniformly. Intrinsic boundary
polynomials therefore converge uniformly over one potential neighborhood
and every compact spectral set for both boundary conditions. Local analytic
approximation gives joint complex smoothness, operator-norm convergence of
Fréchet derivatives, and joint Banach-space analyticity of the intrinsic
infinite products. Pullback proves joint analyticity and exact spectral zeros
on the original source coefficient space, completing ordinary Lemma 9.1(i).

Canonical ordinary boundary coordinates are now constructed by sorting the
actual central multiset while fixing distant branches. Their ordered
labelings agree across cutoffs, retain exact original multiplicities and lp
displacements, and recover the intrinsic characteristic products. Free values
are the signed lattice and real-type roots are real at every index. Both
canonical sequences have common locally bounded full lp norms and complete
labelings at all sufficiently large cutoffs.

Local uniform characteristic families and exact analytic counts on the
central vertical strip now give stability of prefix and suffix counts.
Compact root confinement controls imaginary parts; arbitrarily close real
barriers control each ordered real coordinate. Thus every canonical ordinary
boundary coordinate is continuous at real type under complex perturbations,
including collisions. The ordinary source interval extension preserves real
type, so pullback proves Lemma 9.1(ii) on the original coefficient space.
Both canonical source sequences are analytic outside a finite central block
at arbitrary complex potentials.

The classical part of the boundary gap comparison is now established. The
literal endpoint functions have their exact free normalization and joint
analyticity, and their zeros are exactly the original physical separated
eigenvalues. Unimodularity gives `Δ²−4=δ²−4χDχN`; real-type monodromy symmetry
then gives the trace bound at boundary roots, with strictness characterized
by nonzero anti-discriminant. Comparing compatible physical representatives
locates real boundary eigenvalues in some original periodic gap, while
keeping the periodic and reflected boundary potentials distinct. Real scaling
now gives continuous boundary roots and original periodic endpoints with the
same physical representative. A midpoint-barrier continuation theorem
preserves the initial free gap index, proving indexed interlacing for all
compatible continuous real-type potentials in the Hilbert realization.
Collapsed gaps identify both boundary roots with the endpoint, and the
literal signed trace bounds hold for every integer index.

Boundary reflection conditions and all generalized root spaces now commute
with finite exponent inclusion. This preserves original boundary spectra,
algebraic multiplicities, and every fixed central multiset, including at
p=1. Comparing ordered central enumerations in a block containing any given
signed index proves canonical boundary coordinate invariance for p>1.
Canonical displacements and normalized characteristic functions agree too.
Both original periodic endpoints and their displacement sequences are now
exponent independent, by the analogous ordered paired-multiset comparison.
Finite-polynomial physical formulas and density identify the half-interval
map across exponents. This proves compatibility of the completed ordinary
and auxiliary reflected extensions. A continuous inclusion in the source
pair topology commutes with all three distinct potential realizations;
source boundary coordinates, normalized characteristics, and the original
periodic endpoints consequently agree across finite exponents.

Finite source Fourier polynomials now reconstruct their actual periodic and
Dirichlet-reflected Hilbert potentials. Both agree with one continuous
pointwise real-type curve on the original unit interval. The continuous-case
interlacing proof gives the correct signed gap for each finite real-type
polynomial. Exact exponent compatibility carries this to all finite p>1.
Symmetric Fourier truncations preserve real type and converge in the source
pair norm; continuity of both boundary roots and original periodic endpoints
passes the inequalities to every real-type source potential. This completes
the ordinary Dirichlet and Neumann Lemma 9.1(iii), including collapsed gaps,
strict neighboring-gap separation, and the alternating discriminant level.

The starred boundary roots are now canonical signed coordinates of the
actual auxiliary restricted pencils through their proved phase conjugation.
Their normalized entire characteristics have exactly the auxiliary spectra,
with original generalized multiplicities as analytic orders. Pullback proves
joint analyticity and coordinate continuity at real-type source potentials;
both canonical coordinates and normalized products are exponent independent.
This establishes the auxiliary analogues of Lemma 9.1(i–ii).

The source phase map now has exact coefficients `(i φ₁, -i φ₂)` and commutes
with period doubling. It transforms the Neumann-reflected auxiliary source
potential into the Dirichlet-reflected ordinary potential of the rotated
source. Thus all starred signed roots and normalized characteristics are
literally ordinary ones at that source. The unrestricted periodic pencils
are phase-conjugate at every chain length; their spectra and original
algebraic multiplicities agree, also on period-one source potentials.

The intrinsic periodic spectrum together with algebraic multiplicities now
uniquely determines both complete ordered signed endpoint sequences, even
when comparing different even potentials. Applying this to the source phase
proves exact endpoint invariance. Ordinary indexed interlacing therefore
transfers to both actual starred boundary restrictions at every finite p>1,
including neighboring-gap separation, collapsed-gap equality, and the
alternating original discriminant level. This completes the starred
interlacing portion of Lemma 9.1(iii).

The actual classical auxiliary endpoint characteristics are now given by
monodromy formulas with the signs dictated by the page-33 domains. Their
zeros satisfy the normalized endpoint equations, both are jointly analytic,
and their Neumann-minus-Dirichlet difference is the classical monodromy
anti-discriminant. The page-53 printed starred D/N monodromy labels are
proved to be swapped relative to those domains. On the full finite-exponent
source space, the corresponding difference of normalized canonical products
is entire, jointly analytic, exponent independent, and zero at the free
potential. It is currently named `sourceAntiDiscriminantCandidate` because
its agreement with the physical monodromy anti-trace for arbitrary `L²`
source input is not yet proved; agreement on dense finite Fourier input and
uniqueness of continuous extension are now proved.

Classical initial-value uniqueness now proves exact phase conjugation for
continuous potentials. The phase fixes both diagonal monodromy entries and
the discriminant, rotates the off-diagonal entries by `i` and `-i`, and
identifies each actual auxiliary characteristic with the ordinary separated
characteristic of the rotated continuous potential. The classical
anti-discriminant consequently equals the ordinary Neumann-minus-Dirichlet
characteristic difference after phase rotation.

The monodromy characteristic's zeros are now proved equivalent to the
actual physical auxiliary eigenvalues of every continuous curve and to the
Neumann-extended coefficient spectrum. For finite source Fourier pairs, the
Neumann extension is exactly the source auxiliary coefficient potential;
therefore each classical auxiliary characteristic and normalized starred
source product have precisely the same zeros. This establishes the zero-set
part of the dense-subspace comparison. Analytic orders and the entire
normalization factor remain to be identified.

The source-normalized complete boundary product now has ratio one to the
free sine along every separated escaping spectral path. This passes to both
intrinsic boundary characteristics and their ordinary and actual starred
source pullbacks at every finite exponent. An exterior threshold bounds the
intrinsic/free ratio below by one half. Separately, the classical monodromy
characteristic has sine-scale growth in the imaginary spectral height, so
its ratio to an intrinsic boundary characteristic is uniformly bounded on
the distant separated exterior. Weighted Volterra entry bounds now prove
that both classical separated characteristics have ratio one to free sine
as imaginary height tends to positive infinity, uniformly in real spectral
part. The phase-conjugated classical auxiliary characteristics share that
limit. Thus classical-to-intrinsic and actual auxiliary-to-starred-source
quotients tend to one along upper separated paths, including the matched
finite Fourier source input. A convergent scalar endpoint Taylor series now
identifies every coefficient with a signed normalized forced-solution chain.
Finite scalar Taylor kernels are exactly the separated endpoint equations for
such chains, and their nullity is the truncated classical analytic order.
The corresponding physical forced chains now define a linear injection into
each finite boundary root space. This proves finite classical analytic orders
and the inequality from classical order to physical algebraic multiplicity.
The scalar Taylor kernel is now linearly bijective with each finite physical
root space. Their dimensions are `min N m`, and the classical characteristic's
analytic order equals the full physical algebraic multiplicity. The intrinsic
boundary characteristic already has that physical order. Their filled
quotient is now entire and bounded; its upper limit one proves exact equality
of the classical and intrinsic normalized characteristics for continuous
physical potentials.

The normalized starred source characteristics now equal the actual classical
auxiliary monodromy functions on every finite Fourier source pair. Their
Neumann-minus-Dirichlet difference equals the classical anti-discriminant
there, for every finite exponent, and the jointly analytic candidate is the
unique continuous extension of those dense finite values. Next connect this
extension with physical monodromy for arbitrary `L²` source data. The full
source identity `∆²−4=δ²−4χDχN` has already been proved by finite-input
comparison and density, so Lemma 9.2(ii) holds at every indexed Dirichlet
root, even if it is multiple. For Lemma 9.2(iii), the generic entire boundary product has a
single ℓᵖ majorant for its sine error on every closed half-π free disc and
its derivative error on every quarter-π disc, uniformly on displacement-norm
balls. That transfer and high-index evaluation are now proved: both starred
products, their difference, and its derivative have uniform free-disc
majorants; all distant canonical Dirichlet samples obey one ℓᵖ tail bound.
The complete sampled sequences lie in ℓᵖ pointwise. A compactness bound for
the jointly analytic candidate on a fixed spectral ball, together with
Cauchy's estimate, now uniformly controls the finite central samples.
Combining that finite block with the tail completes the locally uniform full
ℓᵖ norm assertion of source Lemma 9.2(iii). Next connect the source candidate
with physical monodromy for arbitrary `L²` input, then continue to the action
coordinate prerequisites.
For Lemma 10.1, a common source neighborhood and cutoff now localize both
periodic endpoints, both ordinary boundary roots, and the critical point in
their free quarter-π discs at all distant indices. Those discs are pairwise
disjoint and satisfy explicit linear pointwise separation bounds.
The real-type five-coordinate clusters are now proved to lie in their
indexed gaps and to be strictly separated in real part, with a metric lower
bound by the intervening periodic endpoint gap.
The finite central disc construction is now proved: each midpoint disc
contains its real-type five-coordinate cluster, and a finite minimum of
the positive inter-cluster gaps supplies one margin making all central
discs pairwise disjoint. The discs can now be frozen at the base potential:
continuity of the five coordinates and finite intersection yield one open
source neighborhood where every nearby central cluster remains inside its
assigned disc. The central and uniform tail neighborhoods are now
intersected: every signed index has an explicit assigned disc containing
all five nearby source coordinates. Central discs are mutually disjoint,
as are the free tail discs. Bounded finite margins and localization of the
two outer central endpoints now prove cross separation as well. A connected
source ball supports pairwise disjoint discs for every index and all five
coordinates. The real-type source locus is convex and connected; the union
of its local connected balls is an open connected `Ŵp`. Every point of
this union inherits one local common sequence of pairwise disjoint discs,
with free quarter-π discs at high indices. Convexity of the discs also
contains the complete periodic endpoint segment. This completes the
source-coefficient geometric statement of Lemma 10.1. Next use these
isolating neighborhoods for Lemma 10.2's analytic symmetric spectral
coordinates and the action-coordinate prerequisites.
The next contour step is now proved: every assigned disc contains exactly
its own two canonical periodic endpoints from the actual spectrum, and
every circular boundary lies in the resolvent set. The finite enclosed
spectral set is exactly that endpoint pair. The complete canonical multiset
labeling and pairwise disc disjointness now identify each root's algebraic
multiplicity with its occurrence count in the indexed pair. Summing those
counts proves that every assigned Cauchy–Riesz projection has rank two,
including when the two endpoints coincide. The first two analytic contour
traces now agree on each common disc neighborhood with the canonical
periodic midpoint and squared gap. These canonical functions are therefore
analytic at every source potential in the open connected almost-real domain,
even at double endpoints. The endpoint product now equals the quadratic
expression in the midpoint, squared gap, and spectral parameter. This
identity proves joint analyticity on the same domain, completing Lemma
10.2(iii). A two-step symmetric recurrence now expresses every endpoint
power sum as a polynomial in the analytic midpoint and squared gap. This
proves the full family in Lemma 10.2(i), including coincident endpoints.
The canonical midpoint displacement is now an actual ℓᵖ sequence, with a
uniform full norm bound and uniformly small ℓᵖ tails on a source
neighborhood around every parameter. This proves the midpoint part of
Lemma 10.2(ii). The canonical gap is now an actual ℓᵖ sequence, and its
square belongs to ℓᵖ⁄² pointwise for every finite p>1, including p<2.
The squared-gap `p/2` power tail sum is now exactly the `p` power of the
unsquared gap's ℓᵖ tail norm. Common endpoint tail estimates make it
uniformly small on a source neighborhood around every parameter. This
completes all three assertions of Lemma 10.2 in the source-coefficient
setting. Next formalize the standard roots and contour geometry of
Lemma 10.3, followed by the action-coordinate prerequisites. The
arbitrary-L² physical anti-trace identification remains a separate gap.
For Lemma 10.3, equation (2.9)'s normalized principal standard root is
now defined and its square is identified with the canonical endpoint
factor at every point outside the gap segment. A collapsed gap reduces
exactly to the linear midpoint expression. Next prove that the normalized
radicand avoids the principal square-root cut on the segment complement,
then establish joint analyticity and the cross-disc estimates.
The general preimage calculation for the principal square-root cut is
proved: `1-w²` can leave the slit plane only when `w` is real and
`|w.re|≥1`. For the normalized endpoint ratio, this real condition now
forces the spectral parameter onto the closed endpoint segment. Thus the
canonical source radicand is in the slit plane off its gap segment. The
principal standard root is therefore analytic in the spectral parameter
throughout this complement. The analytic midpoint and squared gap now
also make it jointly analytic in source coefficients and spectral parameter
on the same connected almost-real source domain, including collapsed gaps.
The root norm squared is now identified with the product of its endpoint
distances, and roots are nonzero on distinct isolating discs. Abstract
two-sided endpoint bounds transfer to the root. The free quarter-π disc separation now proves the explicit (2.10)
bounds for every two distinct tail indices on a common connected source
neighborhood. A finite central block now has both a locally uniform positive lower
bound and a uniform upper bound. Its finite index span turns these into
the full index-scale estimate (2.10) for all distinct central indices
on one connected source neighborhood. Sharpening the outer endpoint
localization now gives a π/4 pointwise gap between any central disc and
a positive tail disc, and the same lower bound for standard roots in
both orientations. The mirrored strict negative outer-endpoint
localization gives the same π/4 bound for central–negative-tail pairs.
A finite bound on the central discs’ offsets from the free lattice
centers and the quarter-π tail radius now give a common `|m−n|` upper
bound for mixed-pair roots in both orientations. The fixed π/4 separation
and lattice-center triangle inequality likewise yield one `|m−n|`
lower bound in both orientations, conditional on endpoint localization,
pointwise separation, and segment exclusion. The positive and negative
tail geometry supplies these conditions on every assigned central/tail
disc pair when nearby clusters lie in the disc family. One constant now
gives both sides of (2.10) for all mixed pairs. Uniform tail isolation
and finite central-disc isolation now supply a single connected source
neighborhood and disc family for that mixed estimate. Next reconcile the
central-block estimate with this same disc family. The central estimate
now permits its margin to be reduced below any prescribed positive bound,
in particular π/4. A common connected source neighborhood and
pairwise-disjoint all-index disc family now combine the central,
mixed, and tail estimates into the full two-sided bound (2.10).
The reciprocal root is analytic outside its gap segment, and Cauchy's
theorem gives the off-diagonal circle integral zero. The normalized
diagonal integral equals `−1` when the gap collapses. Circle inversion
and the complex mean-value theorem now establish the same value for
every midpoint-centered circle strictly enclosing the gap, even when
the gap is noncollapsed. Interpolating centers and radii of two discs
that contain the gap now keeps the segment strictly inside every
intermediate circle. A shifted inversion computes the integral on large
circles about any center, and annulus invariance carries its value to
every smaller circle still enclosing the full gap. Thus the diagonal
normalized integral is `−1` on any such circle; the off-diagonal integral
is zero on filled circles in a different isolating disc. A general
holomorphic one-form theorem and its source-root specialization now prove
invariance of the path integral along smooth closed-loop homotopies that
stay away from the gap. Reparameterizing a circle on the unit interval
identifies its path integral with the existing circle integral. Thus the
normalized value is `−1` for any smooth closed loop with a gap-avoiding
smooth homotopy from an enclosing circle. A periodic twice-smooth polar
radius above the gap-enclosing radius now supplies such a homotopy;
its contour therefore has value `−1`, with a cosine modulation as an
explicit noncircular example. The affine radial homotopy also remains
inside any outer disc that bounds both endpoint radii. Confined to an
assigned isolating disc, it transfers the off-diagonal zero circle
integral to the polar contour. Thus the normalized indexed integral is
`−δₘₙ` for this noncircular class. The same identity now applies to any
smooth loop with a smooth homotopy from an enclosing circle whose image
avoids the indexed gap and stays in the assigned isolating disc. The
homotopy image is compact, so no auxiliary neighborhood is needed in
the theorem statement. An affine homotopy now supplies the deformation
for every twice-smooth loop uniformly close to an enclosing circle.
Explicit distance bounds keep every intermediate point outside a disc
containing the indexed gap and inside an outer disc contained in its
isolating disc; hence this class also satisfies `−δₘₙ`. Convex
contraction now proves off-diagonal zero for every twice-smooth closed
loop contained in an assigned isolating disc, with no homotopy or
circle-closeness hypothesis. The full indexed theorem therefore requires
a gap-avoiding circle homotopy only for the diagonal case; that homotopy
need not remain in the isolating disc. Next establish the diagonal value
for the full admissible contour class of Lemma 10.3. The inverse-root
integral is now locally constant in the uniform topology on smooth loops
avoiding the gap: compactness supplies a positive uniform buffer, and
every sufficiently close smooth loop deforms affinely within the gap
complement. Thus a known diagonal `−1` value persists under all such
small deformations. It remains to connect every admissible
counterclockwise contour to a known one, or prove the same value by a
winding-number argument. Local constancy and connectedness now carry
the integral across any continuous family of twice-smooth gap-avoiding
loops, including moving basepoints. The normalized `−δₘₙ` theorem uses
only such a continuous family from an enclosing circle; it no longer
requires the homotopy map on the full square to be twice smooth.
The boundary values in equation (2.12) now hold on both sides of every
noncollapsed canonical complex periodic gap for all `−1≤t≤1`, including
the midpoint and endpoints. A connectedness argument fixes the root
branch throughout the upper half-plane; reflection fixes the lower
branch. Their continuity gives joint one-sided limits as the spectral
parameter approaches each gap point through its entire open side, even
when the longitudinal coordinate varies. The cosine parametrization of
Lemma 10.4 now removes the endpoint singularities of the side kernel:
its integral equals `±i` times an ordinary integral over an interval
of length at most `π`. Compactness gives an attained maximum of `‖f‖`
on the gap, and this one maximum bounds both normalized side integrals
uniformly in the stopping point. The result applies to the actual
canonical source root through its proved side limits. The weighted
integral in the dissertation's `r` parameter is now proved integrable
and equal to the cosine integral by substitution. An independently
defined straight side path integral has the same value and satisfies
the same canonical-source maximum bound. Removing the left singular
endpoint gives that value as a limit; at the right gap endpoint,
removing both singular endpoints does too. Next continue with the
infinite standard-root product in Lemma 10.5.
The printed general-`p` central-height constant remains a separate open item.

The Lemma 10.5 factor step is in `SourceStandardRootProductFactors.lean`:
normalized errors have an exact midpoint/spectral/square-root decomposition,
the free spectral terms cancel for `k,-k`, and the paired factor is
`1+a_k+a_{-k}+a_ka_{-k}`. A global norm estimate controls the principal
square-root error by the radicand error. Next use the source midpoint and
squared-gap sequence bounds to prove locally uniform summability of the
paired errors and convergence of the infinite product.

`SourceStandardRootMidpointProduct.lean` now constructs the source midpoint
factor correction as an `ℓ¹` sequence. Its `k,-k` pairing is absolutely
summable, and the correction has uniformly small `ℓ¹` tails on a source
neighborhood. Next bound the square-root remainder by a summable tail,
then combine it with the midpoint correction and quadratic error term
to build the locally uniform paired product.

`SourceStandardRootSqrtRemainder.lean` proves the rationalized pointwise
root-error bound, absolute summability of the source square-root remainder,
and a shared summable `1/k²` majorant on source neighborhoods and bounded
spectral regions. Next combine midpoint and square-root terms to show
absolute summability of paired factor errors, control their quadratic
cross term, and construct the locally uniform nonzero product.

`SourceStandardRootPairedProduct.lean` now constructs the omitted-zero
product itself. The normalized single-factor error is an `ℓ²` sequence,
the paired excess is `ℓ¹`, and the natural finite paired cutoffs converge.
Off the noncentral gap segments, no factor vanishes and neither does the
infinite product. Next prove locally uniform convergence and analyticity
in the spectral parameter and source potential, then extend from omitted
index zero to an arbitrary omitted index.

`SourceStandardRootPairedProductAnalytic.lean` defines the natural finite
cutoffs and proves their pointwise convergence to the existing product.
Each factor and cutoff is spectrally analytic off the noncentral gaps; the
cutoffs are jointly analytic on the common connected almost-real source
domain. Factor continuity on compact subsets is available for the next step:
prove locally uniform convergence, then pass analyticity to the limit.

`SourceStandardRootPairedProductUniform.lean` proves a uniform `1/|k|`
bound for single-factor errors on source neighborhoods and bounded spectral
sets, hence a shared summable `1/k²` bound for their paired cross term.
For each fixed source potential, it then gives a summable factor majorant
on compact spectral sets and uniform convergence of the finite cutoffs
there. Next show the gap-complement domain is open and transfer spectral
analyticity to the limit; the source-uniform midpoint tails are available
for the later joint-analyticity argument.

`SourceStandardRootPairedProductHolomorphic.lean` bounds every periodic
gap segment within a fixed radius of its free lattice point, proving the
family locally finite and the noncentral-gap complement open. Compact-
uniform product convergence then becomes local uniform convergence on that
domain. Analytic finite cutoffs give spectral analyticity of the infinite
omitted-zero product for each source potential. Next prove source-uniform
product convergence and joint analyticity, then extend the omitted index.

`SourceStandardRootPairedProductJointUniform.lean` uses a fixed reciprocal
lattice and source-uniform Hölder tails to control all finite midpoint
correction sums. Combined with the square-root and quadratic cross-term
majorants, this gives uniformly vanishing finite absolute tails for complete
paired-factor errors near any source and on bounded spectral sets.
`UniformProductTails.lean` supplies the finite-prefix product criterion, so
the paired cutoffs converge uniformly on a joint neighborhood wherever the
finite cutoffs are continuous. The existing connected source domain makes
this available at every point of the noncentral-gap complement. Next prove
joint analyticity of the limit on an open joint domain, then extend from
omitted index zero to arbitrary omitted indices.

Joint local uniform convergence and analytic finite cutoffs now imply
joint continuity of the infinite omitted-zero product wherever the source
lies in the common connected almost-real domain and the spectral point
avoids noncentral gaps. The pointwise nonvanishing theorem strengthens
this to nonvanishing on a joint neighborhood at each such point. Next
establish a common open analytic domain for all finite cutoffs and pass
Banach-space analyticity to the locally uniform limit.

`SymmetricSegmentIncidence.lean` expresses membership in a complex gap
segment through its midpoint, squared endpoint difference, and a compact
real parameter. The incidence set is closed; continuity of the symmetric
gap data therefore makes avoidance of each fixed moving gap locally
stable without ordering the endpoints. `SourceStandardRootPairedJointDomain.lean`
adds a source-uniform free-lattice bound, so all sufficiently distant gaps
avoid one spectral ball. Finite-gap stability and this tail bound prove the
joint moving-gap complement open. On a single connected source domain,
all finite paired cutoffs are analytic and converge locally uniformly on
that open complement. Next apply a Banach-space analytic-limit theorem to
the infinite product, then extend to arbitrary omitted indices.

`LocalAnalyticApproximationOn.lean` extends the Banach-space
fixed-ball approximation criterion to an open domain. Uniform convergence
and analytic finite approximants survive Fréchet differentiation on
smaller balls, yielding `ContDiffOn ℂ ∞` and uniform operator-norm
convergence of first derivatives. Applied in
`SourceStandardRootPairedProductJointSmooth.lean`, the omitted-zero
paired product is jointly complex smooth on the open moving-gap domain.
Next establish a local Taylor expansion for complex-smooth maps there,
then treat arbitrary omitted indices.

`BanachTaylorBoundsOn.lean` and `BanachSmoothAnalyticOn.lean` now supply
the local Taylor expansion for scalar-valued complex-smooth maps on open
Banach domains. The Fréchet series has positive radius and sums along
short complex lines by Cauchy's theorem. Applied in
`SourceStandardRootPairedProductJointAnalytic.lean`, this proves joint
analyticity of the omitted-zero paired product on the open moving-gap
domain. The next product step is arbitrary omitted indices.

`SourceStandardRootOmittedFinite.lean` starts the arbitrary-index case
of Lemma 10.5 with the literal symmetric cutoffs and the existing
single-root free normalization. The moving-gap complement is open for
every omitted index on one common connected almost-real source set;
every cutoff is jointly analytic and nonzero on its domain, and the
zero-index cutoff is definitionally related to the paired construction.
Next prove local uniform convergence of these cutoffs and analyticity
and nonvanishing of their infinite limit.

`SourceStandardRootOmittedProduct.lean` factors each literal symmetric
cutoff into its zero mode and paired factors with the omitted root
replaced by `1`. The paired deviations remain absolutely summable
because only one pair changes. This proves pointwise convergence of
the literal cutoffs for every omitted index and nonvanishing of the
limit on the corresponding gap complement; at index zero the limit
equals the previous paired product. Next upgrade convergence to local
uniform convergence on the open joint domain and prove joint
analyticity of the limit.

`UniformProductTails.lean` now allows a bounded zero-mode prefactor in
the natural-number product criterion. With the previous paired-factor
tail estimate, `SourceStandardRootOmittedJointAnalytic.lean` proves
local uniform convergence of the literal cutoffs for every omitted
index on its open joint moving-gap domain. The local Banach-space
analyticity theorem gives joint analyticity, and the pointwise factor
argument gives nonvanishing. This completes the product assertions of
Lemma 10.5 in the current source model. Next formalize Corollary 10.6.

`JointSingleSpectralProducts.lean` establishes the numerator's first
analyticity ingredient: the entire normalized single-root product is
jointly analytic in the spectral parameter and arbitrary `ℓᵖ`
displacements, with literal finite cutoffs converging uniformly on
compact spectral sets over bounded displacement families. Next delete
one prescribed numerator factor, retain analyticity across its root,
and divide by Lemma 10.5's nonzero omitted-root product.

The deleted numerator and Corollary 10.6 quotient are now formalized.
The numerator converges uniformly over compact spectral sets and bounded
`ℓᵖ` families and is jointly entire across its omitted root. The literal
finite quotient factors converge to a jointly analytic function on the
moving-gap complement over one common connected source domain. Next
work through Lemma 10.7: assemble the full canonical-root product and
its analytic and boundary behavior.

The canonical root now has its full normalized product, pointwise
convergence of the literal cutoffs, arbitrary-index factorization,
and the identity `root² = Δ²−4` off the gaps. Its spectral and joint
analyticity clauses are proved, as is analytic extension through a
collapsed gap using the omitted product. Finish Lemma 10.7 by proving
the opposite boundary values on the two sides of each noncollapsed gap,
then continue to the asymptotics of Lemma 10.8.

`SourceCanonicalRootGapSides.lean` multiplies the established standard-root
side limits by the omitted product, which is continuous at points on the
selected gap. `SourceCanonicalRootGapIsolation.lean` uses the global
isolating discs to put every point of one gap outside all other gaps and
combines the analytic, collapsed-gap, and opposite-side clauses on one
connected source neighborhood. Lemma 10.7 is complete in this source
model. Next formalize Lemma 10.8's canonical-root asymptotics.

`SourceSingleRootAsymptoticFactors.lean` begins Lemma 10.8. It factors
the literal finite quotient exactly into midpoint and gap-correction
products, proves the inverse square-root perturbation bound on the
half-unit ball, and bounds the correction product's error by the
exponential of the sum of radicand norms. Next prove the uniform
isolating-disc separation and powered Young estimate for that sum,
then the midpoint quotient asymptotics and infinite-product limit.

`SquaredReciprocalRows.lean` proves the reciprocal-square kernel belongs
to every `ℓᵗ` above one half and applies powered Young with
`t = min(1,p/2)`. `SourceSquaredGapReciprocalRows.lean` instantiates this
for the canonical source gaps: every physical off-diagonal row converges
and its row-sum sequence lies in `ℓ^(p/2)`, including `1 < p < 2`.
Next transfer this row bound to the radicand on each isolating disc,
then estimate the midpoint quotient and pass to infinite products.

`SourceMidpointDiscSeparation.lean` now establishes a common local
midpoint-distance constant across central, mixed, and tail indices.
It transfers that geometry and the physical reciprocal-square row
summability to a uniform bound for every finite off-diagonal radicand
sum on each isolating disc. Next control the midpoint quotient, then
combine it with the gap correction and pass to the product limit.

`SourceSingleRootMidpointBounds.lean` pairs the root-minus-midpoint
displacement with the punctured reciprocal lattice. It bounds all
finite midpoint products uniformly over the isolating discs and joins
this with the squared-gap row estimate into a finite full-quotient
bound whenever that row is small. Next derive eventual row smallness
from its `ℓ^(p/2)` membership, control the first-order midpoint term
in `ℓᑫ` across omitted indices, and pass to the infinite product.

`FiniteExponentTail.lean` extracts two-sided coordinate decay from any
finite positive `ℓʳ` exponent. `SourceSquaredGapRowTails.lean` applies
this to the physical reciprocal-square rows, and
`SourceSingleRootAsymptoticTailBounds.lean` removes the finite
product's small-radicand assumption on all sufficiently remote discs
for each fixed source. Next make that row threshold uniform on a source
neighborhood, obtain the first-order `ℓᑫ` omitted-index estimate, and
pass to the infinite product.

`UniformWeightedRows.lean` shows that a summable nonnegative kernel has
uniformly vanishing translated rows for families with uniformly small
tails. `SourceSquaredGapUniformRowTails.lean` applies this to the actual
source gaps and produces a common half-unit threshold.
`SourceSingleRootUniformAsymptoticTailBounds.lean` combines it with
midpoint separation on a connected neighborhood, giving the finite
full-quotient estimate with one threshold for all nearby sources.
Next prove the first-order `ℓᑫ` omitted-index estimate and pass to the
infinite product.

`SeparatedReciprocalRows.lean` proves that changing a linearly separated
reciprocal denominator by a bounded midpoint displacement gains a
reciprocal-square factor. The resulting correction rows are absolutely
summable and form an `ℓᑫ` sequence for every Banach exponent, with a
square-kernel norm bound. `SourceMidpointHilbertCorrection.lean`
instantiates this for the physical periodic midpoints on distant source
discs and supplies one connected neighborhood with uniform separation
and midpoint-displacement bounds. Next identify the free-lattice term
with the sampled Hilbert transform to complete the signed first-order
`ℓᑫ` estimate for `1 < q < ∞`, then pass to infinite products.

`FreeLatticeSampledRows.lean` now identifies every selected free-lattice
reciprocal row with the sampled discrete Hilbert transform. Together
with the square-kernel correction, `PhysicalMidpointHilbertRows.lean`
proves absolute convergence of each physical row and an `ℓᑫ` norm
bound for the signed sums when `1 < q < ∞`.
`SourceMidpointHilbertCorrection.lean` specializes this to all distant
source discs, uniformly over nearby potentials and every selection of
one spectral point per disc. Next turn this selection-uniform bound into
the `ℓᑫ` sequence of disc suprema required by Lemma 10.8, handle the
`q=1` endpoint where needed, and pass to the infinite-product estimate.

`UniformSelectionSup.lean` now upgrades any norm bound valid for every
independent coordinate selection to an `ℓᑫ` bound for the least
coordinatewise supremum majorant. `SourceMidpointHilbertDiscSup.lean`
applies this to the signed midpoint sum on every distant isolating disc.
It proves the required supremum sequence lies in `ℓᑫ` for
`1 < q < ∞`, locally uniformly near a real-type source. For `q=1`,
the same supremum lies in every finite `ℓʳ` with `r>1`, giving the
`ℓ^{1+}` endpoint. Next use these first-order bounds in the
infinite-product estimate of Lemma 10.8.

`SourceSingleRootQuotientTailLimit.lean` now places each sufficiently
distant assigned disc in the moving-gap complement by comparing two
local isolating-disc families. The literal finite quotient products
therefore converge on those discs to the analytic quotient of
Corollary 10.6, and their neighborhood-uniform finite bound passes to
that infinite quotient. Next retain the signed first-order sum when
estimating the midpoint product, control its quadratic remainder in a
sequence space, and combine it with the squared-gap correction to get
the full `ℓᑫ + ℓ^(p/2) + ℓ^{1+}` asymptotic of Lemma 10.8.

`PhysicalMidpointProductRemainder.lean` now puts the absolute physical
midpoint row in the doubled exponent using reciprocal-kernel Young
convolution, then applies the quadratic product theorem to return the
nonlinear remainder to the original exponent. The source specialization
and `SourceMidpointProductDiscSup.lean` control the supremum of the
exact infinite midpoint product minus its signed linear sum in `ℓᑫ`,
including `q=1`, with a bound quadratic in the numerator displacement.
Next combine this remainder with the signed disc-supremum term, identify
the midpoint product with the quotient factor, and add the squared-gap
correction to complete the sequence estimate.

`SourceMidpointProductFullDiscSup.lean` now combines the signed row and
quadratic remainder before taking coordinatewise disc suprema. The full
infinite midpoint product minus one has a locally uniform `ℓᑫ` bound
when `1 < q < ∞`; an `ℓ¹` numerator gives every finite exponent above
one, matching the `ℓ^{1+}` endpoint. Next identify this product with
the literal midpoint cutoff limit, then compare the latter with the
infinite single-root quotient using the squared-gap row.

`SourceMidpointProductCutoffLimit.lean` now proves that each literal
symmetric finite midpoint quotient converges to the unconditional
midpoint product used above. The proof checks absolute summability from
disc separation and identifies every finite factor exactly with its
off-diagonal perturbation. Next pass the finite quotient-minus-midpoint
estimate to the two infinite limits and extract its `ℓ^(p/2)` disc row.

`SourceSingleRootGapCorrectionLimit.lean` now passes the finite
quotient-minus-midpoint estimate to the actual analytic quotient and
the infinite midpoint product. `SourceSingleRootGapCorrectionDiscSup.lean`
uses the physical reciprocal-square row to give a uniform-in-disc-point
`ℓ^(p/2)` majorant for their difference on one connected source
neighborhood, also when `1 < p < 2`. Next intersect this neighborhood
with the midpoint-product disc bound and state the full first
asymptotic of Lemma 10.8, including the `q=1` endpoint.

`SourceSquaredGapNorm.lean` now bounds the squared-gap half-exponent
norm by the square of the unsquared-gap norm and extracts a common
local source bound. `SourceSingleRootQuotientAsymptoticDiscSup.lean`
combines the midpoint and gap rows for the actual analytic quotient on
one connected source neighborhood: its distant-disc error is
`ℓᑫ + ℓ^(p/2)` for `1 < q < ∞`, and `ℓʳ + ℓ^(p/2)` for every finite
`r > 1` when `q=1`, with common local constants and threshold. This
formalizes the first assertion of Lemma 10.8 near real-type base
sources. Next derive its stated sine-product consequence from the
appropriate free-product identity.

`SourceDeletedFreeSine.lean` now identifies the free deleted numerator
with the filled sine quotient at every complex spectral point,
including the removed free root. `SourceFreeSineQuotientAsymptotic.lean`
specializes the quotient asymptotic to the free numerator: near a
real-type base source, the filled sine quotient divided by the
omitted standard-root product has locally uniform
`ℓᵖ + ℓ^(p/2)` disc majorants. This proves the corresponding
sine-product consequence in the source setting. Next compare the
remaining Chapter 2 statements with this local formulation and
continue through the subsequent lemmas.

For Lemma 10.10, `SourceCriticalMidpointGapSquaredTail.lean` now
transfers the existing canonical Lemma 8.6 estimate to source
coordinates. On a common open source neighborhood, the critical-root
offset equals the squared periodic gap times a uniformly bounded
`ℓᵖ` sequence at every sufficiently distant signed index. It also
shows that a collapsed distant gap has its critical root exactly at
its midpoint, even for complex source potentials. The remaining
Lemma 10.10 work is the uniform squared-gap bound at the finitely
many central indices.

`CriticalOffsetCoefficientOpenGap.lean` now handles the algebraic
nonvanishing issue at every open real gap, including central indices.
The critical point lies in the gap interior, where the discriminant
has modulus greater than two; hence the deleted periodic product is
nonzero. The quadratic critical identity then makes the coefficient
nonzero and gives the exact squared-gap offset formula. To finish
Lemma 10.10, establish the corresponding local bound across collapsed
central gaps and control the finitely many coefficients uniformly on
a source neighborhood.

`CriticalOffsetCoefficientCollapsedGap.lean` now proves that a
collapsed canonical pair at any real-type potential has exactly two
spectral occurrences, including in the central block. Analytic
orders then show that deleting this pair leaves a nonzero product at
the common endpoint. Together with the open-gap result, this makes
the midpoint coefficient nonzero and gives the exact squared-gap
critical-root formula at every index of each real-type potential.
The remaining Lemma 10.10 step is to extend that formula and its
uniform `ℓᵖ` coefficient bound to a complex source neighborhood.

`SourceDeletedPairOmittedSquare.lean` now identifies the deleted
periodic-pair product with the square of the corresponding omitted
standard-root product, first for literal cutoffs and then for their
entire limits. On any common isolating-disc family, the deleted
periodic product is nonzero throughout the selected disc, even along
the selected gap and at its endpoints. This supplies the nonvanishing
input for extending the central critical-offset argument to nearby
complex sources.

`SourceCriticalOffsetCoefficientNonzero.lean` now combines the
nonzero deleted product with indexed cluster separation. A collapsed
complex periodic pair has its canonical critical root at the common
endpoint. Thus the midpoint coefficient is nonzero and the exact
squared-gap critical-offset identity holds at every signed index on
the connected almost-real source domain. The remaining quantitative
Lemma 10.10 task is a common local `ℓᵖ` norm bound for the quotient
coefficients, especially at the finitely many central indices.

`JointSpectralDerivative.lean` proves a general regularity lemma:
the spectral derivative of a jointly analytic complex Banach-space
family is jointly continuous. `SourceDeletedPairJointAnalytic.lean`
applies the omitted-product square identity to make the deleted
periodic-pair product jointly analytic, with jointly continuous
spectral derivative, on the open moving-gap complement. The central
quotient's numerator now has the needed local continuity; next
combine this with critical-root and midpoint continuity to bound
finitely many central coefficients on one source neighborhood.
