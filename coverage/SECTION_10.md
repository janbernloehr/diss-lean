# Section 10: potentials of almost real type

This audit follows the source statements and proofs on printed pp. 54–59.
The neighborhood assertion is proved with the real-type locus used in
the proof. The printed all-complex version has a formal counterexample.
Lemmas 10.2 and 10.3 are covered on the same common domain, including the
preceding simple-root assertions and general piecewise C¹ contours.
Lemma 10.4 is covered with the selected-root index correction, actual
side traces, improper endpoint limits and the sharp constant one.
Lemma 10.5 is covered on the unchanged common domain, with literal
symmetric cutoffs, paired absolute convergence, both analytic domains
and nonvanishing. Corollary 10.6 is covered with its full displacement
space, literal unordered quotient product and printed closed-disk domain.
Equation (2.13), Lemma 10.7 and equation (2.14) are covered on the same
common domain, including collapsed gaps, actual side limits and Figure 2.4
on the real locus. Lemma 10.8 has full-disk supremum decompositions and
precise bounded-offset estimates. Its printed original-topology uniformity
claim is refuted at p=4, q=1 by a formal quotient counterexample. The
free-sine consequence is now proved in the stronger locally uniform
ℓ(p/2)+ℓ(1+) class on every original disk. Remark 10.9 now has a proved
ℓ(p/4) supremum remainder after its exact moving-denominator Taylor term.
The printed integer-kernel replacement is now refuted by an actual real
source counterexample at p=8, arbitrarily near zero. The full p/2
optimality assertion remains under audit, followed by the later statements.

## Lemma 10.1: precise domain and quantifiers

For every finite p>1, `sourceLemma10_1` constructs one open connected
set W in the original complex coefficient source space, containing the
entire real-type source locus. For each ψ∈W it supplies an open connected
V with ψ∈V⊆W. The frozen base φ is real-type, but ψ and the other sources
in V need not be real-type.

One N, one positive central margin ε≤π/4, one real c≥1, and the family
`sourceIsolatingDisc hp hp1 φ N ε` are chosen for this V. These choices
precede every nearby source χ∈V and every signed spectral index. They are
not chosen separately for different χ or indices.

`SourceIsolatingNeighborhoods` records the literal conditions:

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Disks centered on the real line | `.discs` | Each disk is `ball (a : ℂ) r` with a real and r>0. |
| Full periodic gap containment | `.gap` | The entire straight segment between the actual canonical periodic endpoints, at every nearby complex source. |
| Dirichlet, Neumann, and critical roots | `.cluster` | All five actual cluster coordinates, including both periodic endpoints, for all χ∈V and all signed n. |
| Two-sided distance estimate (2.7) | `.set_distance` | One c≥1 gives c⁻¹\|i−j\|≤dist(D_i,D_j)≤c\|i−j\| for every i≠j. |
| Exact free tail | `.tail` | One cutoff, with D_n exactly the open radius-π/4 disk about nπ whenever \|n\| exceeds it. |
| Pairwise disjointness | `.disjoint` | Derived from the strictly positive lower bound; no extra hypothesis. |

The package additionally gives the same two-sided bounds for every pair
of points in the distinct disks through `.pointwise_distance`.
Collapsed periodic gaps are allowed; no simplicity is assumed here.

## Literal set distance and positive separation

`spectralSetDistance s t` is `Metric.infDist 0` of the image of subtraction
on s×t. `spectralSetDistance_isGLB` proves that, for nonempty s,t, it is the
greatest lower bound of the set of all actual `dist z w` with z∈s,w∈t.
Thus it is the source's infimum distance, not the Hausdorff distance.
The disks are nonempty because every radius is strictly positive.

Pairwise disjoint open disks alone would not suffice: tangent open disks
can have zero infimum distance. The construction first obtains disjoint
disks with central margin ε, then replaces each central margin by ε/2.
The tail disks remain unchanged. Continuity of all five coordinates at
the real base and a finite intersection give a neighborhood where the
nearby central clusters still fit in the smaller disks. Intersecting with
the original neighborhood retains all tail inclusions, and a contained
source norm ball supplies connectedness.

For a pair with at least one central index, shrinking loses at least
ε/2 from the sum of radii. `shrunk_disjoint_balls_pointwise_separation`
turns the original center-distance inequality into this positive
pointwise separation. For two tail indices, the free-disk estimate gives
at least (π/2)\|i−j\|, which also dominates ε/2. Thus all distinct pairs
have one positive lower bound δ=ε/2, before converting to index scale.

`exists_source_isolating_lattice_offset_bound` supplies R≥0 such that
every z∈D_n satisfies \|z−nπ\|≤R. With t=\|i−j\|≥1 and d=dist(z,w),
triangle inequalities give

```
πt ≤ 2R+d,       d ≤ πt+2R,       δ ≤ d.
```

`exists_index_comparison_constant` takes
c=max(1,max((1+2R/δ)/π,π+2R)) and derives c⁻¹t≤d≤ct. Passing the lower
bound to the infimum and choosing any point pair for the upper bound
gives the literal set-distance estimate. This includes central/central,
central/tail, and tail/tail pairs with the same c.

## Global connected neighborhood

The local neighborhoods cover the real-type locus. Their union is open.
Each local set is connected and meets that connected locus at its real
base. Adjoining the locus to each local set produces a family with a
common nonempty intersection; its union is connected and equals the
original union. Every point in the union retains one local family and
one local neighborhood contained in W.

The result also exposes the frozen real base and the explicit N,ε
construction, so later contour arguments can use the existing actual
isolating-center and radius APIs.

## The printed all-complex domain is false

The statement on p. 54 says a neighborhood of FL_c^p. The preceding
paragraph, the base potentials in the proof, and the final union use
FL_r^p. The corrected theorem above uses FL_r^p; the printed alternative
is independently refuted in `SourceIsolatingDomainCounterexample.lean`.

`sourceCollisionPotential` is the constant source (iπ,iπ). Its only
nonzero source Fourier coefficients are the two zero modes, and its
period-doubled operator potential is exactly `constantCollisionPotential`.
For raw frequency k the operator block is

```
L_k = [ -πk   iπ ]
      [  iπ   πk ].
```

The exact spectral-pencil calculation proves that the block is
square-zero at k=+1 and k=−1. `collisionMode_mem_root_two` puts every
vector in either two-dimensional block in the second actual periodic
root space. `collisionFourModeEmbedding_injective` proves independence
of all four component modes. The root-space definition of algebraic
multiplicity then yields `four_le_sourceCollisionMultiplicity`.
Only a lower bound of four is needed or claimed.

Conversely, `periodicMultiplicity_le_two_of_disjoint_clusters` uses the
actual canonical enumeration with algebraic multiplicity. For a spectral
point in one assigned set, disjointness excludes occurrences in every
other indexed pair. Its total multiplicity is therefore bounded by the
two slots of that one pair. This argument works for arbitrary sets; no
ball shape, real centering, or neighborhood topology is needed.

Consequently, `sourceCollisionPotential_not_isolatable` rules out any
disjoint isolating family for this source.
`not_sourceLemma10_1_all_complex` refutes a domain containing all complex
sources at every finite p>1. The correction is recorded in
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md).

## Lemma 10.1 verification

The public examples exercise the global theorem at p=3/2, zero-potential
local families and collapsed gaps, all ordinary cluster coordinates,
full gap segments, central and negative-index infimum distances, positive
real-centered disks, exact free tails, and disjointness. A tangent-disk
example checks that shrinking creates positive separation. A separate
example exposes the greatest-lower-bound characterization of set distance.
The counterexample checks include the multiplicity lower bound,
four-coordinate injectivity below two, impossibility of arbitrary
disjoint shapes, and negation of the printed all-complex domain.


## Lemma 10.2: one common analytic domain

For every finite p>1, `sourceLemma10_2` constructs W, open and connected
in the original complex coefficient space, with the entire real-type
locus contained in W. All fields of `SourceLemma10_2Data` use this same W:

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Retained Lemma 10.1 isolation | `.isolation` | Each ψ∈W has an open connected V with ψ∈V⊆W, one disk family and one constant satisfying all quantitative isolation conditions. |
| Periodic power sums, clause (i) | `.power_sums` | Actual left/right endpoint powers, for all signed n and all natural k (including k=0). |
| Midpoint and squared gap, clause (ii) | `.midpoint`, `.squared_gap` | Complex analytic at every point of W, including collapsed gaps. |
| Locally uniform sequence asymptotics | `.uniform_sequences` | One neighborhood, cutoff and bound for both complete sequences and all sufficiently distant tails. |
| Joint pair factor, clause (iii) | `.joint_factor` | Complex analytic on ℂ×W, at arbitrary complex spectral parameters. |
| Exact pair identity | `sourcePeriodicPair_factorization` | The actual product equals (τ_n−z)²−γ_n²/4 at every complex source and spectral parameter. |
| Preceding simple-root paragraph | `.simplicity` | Every ordinary boundary and critical coordinate is complex analytic, with nonzero spectral derivative of its defining characteristic. |

Complex analyticity is stronger than the stated real analyticity. No
analyticity or continuity of individually ordered periodic endpoints on
W is assumed. Their symmetric functions are obtained from the existing
spectral-cluster trace formulas. The midpoint and squared gap determine
all power sums through the symmetric-pair recurrence, including the
constant power. Composition with the source projection and polynomial
operations gives joint analyticity of the exact pair factor.

## Simplicity and connectedness on the same domain

`exists_local_source_allCriticalPoints_simple_analytic` intersects one
common distant-index analyticity neighborhood with finitely many central
analyticity neighborhoods and the all-index simplicity neighborhood.
This gives one open source set around each real-type base where all
critical coordinates are simple and analytic simultaneously.

`exists_sourceSimpleSpectralDomain_within` works inside any prescribed
open set containing the real locus. Intersect that set with the common
ordinary boundary-root domain and the interior of the all-critical-root
property. Take the connected component containing zero. Local
connectedness makes this component open, and connectedness of the real
locus places the entire locus in it. This avoids assuming that an
arbitrary intersection of connected sets is connected.

Applying the construction inside the Lemma 10.1 domain gives W above.
At each point ψ∈W, a source ball contained in both W and its previous
isolating neighborhood retains the same disks and distance constant.
`SourceIsolatingNeighborhoods.mono` records this restriction explicitly.

`SourceSimpleSpectralDomainData.boundary_multiplicity` identifies
simplicity with algebraic multiplicity one for the actual ordinary
boundary operator, using the characteristic's analytic order.
`.critical_order` proves analytic order one for the actual derivative
of the discriminant at each canonical critical point. These statements
hold for every ψ∈W, not just real-type sources, and include central and
negative indices. The assertion that lexicographically ordered periodic
labels can be discontinuous is not supplied as a formal counterexample
by this milestone.

## Literal half-exponent and locally uniform sequences

`sourcePeriodicMidpointDisplacement` has coordinates τ_n−nπ in `Coeff p`.
`sourcePeriodicSquaredGapSequence` has coordinates γ_n² in `Coeff (p/2)`.
The second exponent is the literal extended-real division p/2, rather
than a new Banach exponent or an assumption p≥2. When 1<p<2, the norm
notation denotes the existing ℓ^(p/2) quasi-norm; the proof does not
assume a triangle inequality for that space.

`lp_norm_eq_sq_of_apply_eq_sq` proves the exact identity

```
‖(g_n²)_n‖_(p/2) = ‖g‖_p².
```

It compares the powered norms through their sums of nonnegative real
powers. The half exponent is positive because p is finite and greater
than one. Applying this identity to the full actual gap sequence gives
`norm_sourcePeriodicSquaredGapSequence`. Applying it after any finite
truncation gives `norm_sourcePeriodicSquaredGapSequence_tail`; no symmetry
of the removed set is needed.

The precise common-neighborhood statement is: for every φ∈W and η>0,
there are an open U with φ∈U⊆W, N≥2, and R≥0 such that every ψ∈U satisfies

```
‖(τ_n(ψ)−nπ)_n‖_p ≤ R,      ‖(γ_n(ψ)²)_n‖_(p/2) ≤ R²,
```

and, for every M≥N, their tails outside [−M,M] are bounded by η and η²
respectively. All choices precede ψ and M. U, N and R may depend on η;
a single neighborhood working for all tolerances is not asserted.
`exists_uniform_sourceLemma10_2_sequences` proves these bounds near
arbitrary complex base sources even without membership in W; the main
theorem then intersects U with W. Both complete sequences, including
all central indices, vanish at the free potential.

## Lemma 10.2 verification and remaining scope

Public examples instantiate the common domain at p=3/2 and explicitly
construct the squared-gap sequence at exponent 3/4 with its exact
quasi-norm. They exercise arbitrary powers at a negative index, joint
analyticity at a nonreal spectral point, boundary multiplicity and
critical zero order, common isolation and tail quantifiers, truncation
by the asymmetric set {0,−1,3}, the exact all-complex factorization, and
free collapsed gaps. No additional source correction is needed for
Lemma 10.2; the Lemma 10.1 domain correction remains in force.


## Lemma 10.3: the unchanged common domain

`SourceLemma10_2Data.standardRoots` produces `SourceLemma10_3Data` on
exactly its input W. No further shrinking or separate existential domain
is used. Consequently `sourceLemma10_3` supplies an open connected W
containing every real-type source, with all Lemma 10.2 properties retained.

| Source requirement | Field or theorem | Exact scope |
| --- | --- | --- |
| Principal-branch definition (2.9) | `sourceStandardRoot`, `normalizedStandardRoot` | The literal expression (τ_n−z)√(1−γ_n²/(4(τ_n−z)²)), with the principal square root. |
| Spectral analyticity | `SourceLemma10_3Data.spectral` | At every complex source, on the full complement of its actual closed gap. |
| Joint analyticity | `.joint` | On the moving-gap complement over the same W. |
| One local family | `.neighborhoods` | For every ψ∈W, one open connected V with ψ∈V⊆W and one `SourceStandardRootNeighborhoods` package. |
| Fixed-disk joint domain | `SourceStandardRootNeighborhoods.joint` | (ℂ∖D_n)×V, including points on the boundary of the open disk. |
| Two-sided root bound (2.10) | `.bounds` | The same c≥1 from quantitative isolation, for all nearby sources, all m≠n and all z∈D_m. |
| Normalized contour identity | `.contours` | Every finite piecewise C¹ contour inside D_m, avoiding G_m, with winding one about τ_m. The value is −1 if m=n and zero otherwise. |

The bound uses the exact identity |w_n(z)|²=|λ_n⁻−z||λ_n⁺−z|.
Both endpoint distances have the same lower and upper bounds from
`.pointwise_distance`. Nonnegativity transfers those bounds to |w_n|
without changing c. Gap containment and pairwise disjointness ensure
that z∈D_m avoids G_n when m≠n. Central and negative indices are included.

## General contours and the orientation convention

`PiecewiseC1Loop` consists of a finite number of paths between consecutive
vertices, each C¹ on the closed unit interval, with the last vertex equal
to the first. The definition allows corners, self-intersections, repeated
vertices and repeated traversals. Individual pieces need not be loops.
Its `integral f` is the finite sum of the actual complex one-form path
integrals. `normalizedIntegral f` multiplies that sum by (2πi)⁻¹.

`windingIntegral z` is the normalized integral of the reciprocal pole
1/(w−z). It is complex-valued; the contour theorem uses the conventional
orientation condition `windingIntegral τ_m = 1`. This condition concerns
the reciprocal pole, not the inverse standard root being evaluated.
The contour must avoid the entire closed gap. This winding-one convention
expresses a single counterclockwise circuit around the gap; simplicity
of the curve or a chosen homotopy is not an additional assumption.

`windingIntegral_circle` proves that a positively oriented circle has
value one about every point in its interior. `integral_circle` identifies
the piecewise-contour integral with the existing circle integral using
the same orientation. `repeatPath` constructs actual repeated traversals,
and `integral_repeatPath` proves that their integrals multiply by the
number of traversals. `polygon` constructs contours with literal straight
pieces and permits corners without matching endpoint derivatives.

## A single-valued primitive fixes the sign

Put t=τ_n, g=γ_n² and S(z)=√(1−g/(4(t−z)²)). The new correction is

```
F(z) = −log(1+S(z)).
```

Outside the actual gap, t−z is nonzero and the square-root radicand lies
in the principal slit plane. The principal square root has nonnegative
real part, so 1+S(z) lies in the open right half-plane. Thus this logarithm
is single-valued throughout the needed domain. Differentiating S² and
then the logarithm gives the formally checked identity

```
F′(z) = 1/w_n(z) + 1/(z−t).
```

`hasDerivAt_standardRootLogCorrection` proves this for arbitrary complex
t,g whenever the denominator and slit conditions hold. Applying the
actual source branch-cut theorem supplies these conditions off G_n.

`PiecewiseC1Loop.integral_eq_zero_of_primitive` evaluates the derivative
integral on each C¹ piece and telescopes the vertex differences. The
closed-chain condition cancels the final difference, even when the
pieces are not individually closed. Integrability follows from continuity
on the domain and C¹ regularity of the pieces; it is not an extra source
hypothesis. Therefore
`normalized_sourceStandardRoot_inv_piecewiseIntegral_eq_neg_winding`
proves the full formula

```
(2πi)⁻¹ ∫_Γ dz/w_n(z) = −windingIntegral(Γ,τ_n).
```

This holds at every complex source for every gap-avoiding piecewise C¹
contour, independently of W. It also covers collapsed gaps, clockwise
orientation and any number of traversals. No contour-deformation
hypothesis or reduction to the Hilbert exponent appears in the proof.

For m≠n, the inverse root is holomorphic on the whole convex disk D_m.
An actual primitive there makes its integral zero on every piecewise C¹
closed contour inside D_m. Combining this with the diagonal winding-one
formula proves `standardRoot_piecewiseIntegral_indexed` and the local
`.contours` field using the same family as the norm estimate.

## Collapsed gaps and the following boundary-value formulas

`sourceStandardRoot_analyticOnNhd_of_zeroGap` proves that a collapsed root
is analytic on all of ℂ, including its midpoint, where the original
complement-of-gap assertion says nothing. The exact value is τ_n−z.
At zero source this is nπ−z, fixing the sign of the contour normalization.

For noncollapsed gaps, the existing
`sourceStandardRoot_tendsto_gap_upper_side` and
`sourceStandardRoot_tendsto_gap_lower_side` prove (2.12) under arbitrary
approach from the corresponding open side in the coordinate
u=(z−τ_n)/(γ_n/2). Their limits are respectively
−i(γ_n/2)√(1−t²) and +i(γ_n/2)√(1−t²), for every −1≤t≤1.
The midpoint, both endpoints, and arbitrary complex gap directions are
included. These are stronger approach limits than just vertical paths
with the longitudinal parameter held fixed.

## Lemma 10.3 verification and remaining scope

The public checks instantiate the common domain at p=3/2, transfer any
Lemma 10.2 domain unchanged, expose the literal branch formula and free
sign, and check root bounds at central and negative indices. They test
joint analyticity outside the fixed open disk and both values of the
indexed contour identity. The general winding formula is exercised with
clockwise winding. A concrete two-piece repeated circle has period −2;
a concrete two-edge polygon has a genuine corner and nonclosed pieces
and integrates to zero in a gap-free convex disk. Additional checks cover
collapsed-root analyticity at its midpoint and complex upper/lower side
limits at the midpoint and an endpoint. No new source correction is
needed for Lemma 10.3.

Next: Lemma 10.4, its gap-side endpoint integral bound and the printed
index convention in its denominator. The dissertation remains incomplete.


## Lemma 10.4: actual traces and the selected-root correction

The source on printed p. 56 uses w_m in both the statement and proof,
with m unbound, while the path follows G_n. Equation (2.12) and the
substitution require w_n. `SOURCE_ERRATA.md` records the correction and
its precise formal evidence. The result below uses n consistently and
is proved for every original complex source with γ_n≠0, not only sources
in the almost-real neighborhood. All finite exponents p>1 are included.

| Requirement | Formal result | Exact scope |
| --- | --- | --- |
| Actual gap | `sourceStandardRoot_gapSegment_eq_periodicSegment` | The affine image of [-1,1] is exactly the canonical segment G_n. |
| Actual endpoints | `sourceStandardRoot_gap_left_endpoint`, `sourceStandardRoot_gap_right_endpoint` | Coordinates -1 and 1 are λ_n⁻ and λ_n⁺. |
| Boundary denominator | `sourceStandardRoot_tendsto_sideTrace` | The trace is the limit of the actual root under arbitrary approach within the appropriate open side, including endpoints. |
| Continuous side values | `sourceStandardRootSideTrace_continuous` | Continuity in the closed affine gap coordinate. |
| Genuine integrability | `sourceStandardRootSideIntegrand_intervalIntegrable` | Continuous f on G_n suffices for any two closed-gap endpoints. |
| Exact substitution | `sourceStandardRootSideIntegral_eq_weighted` | The signed inverse-square-root integral, with the actual half-gap Jacobian canceled. |
| Improper interpretation | `sourceStandardRootSideIntegral_tendsto`, `sourceStandardRootSideIntegral_double_trunc_tendsto` | Omitting the left branch point, or both branch points, converges to the same side integral. |
| One attained maximum | `sourceLemma10_4` | One z∈G_n maximizes |f| and controls both sides and all endpoints. |
| Literal supremum | `sourceLemma10_4`, `sourceLemma10_4_sup` | Real suprema of the actual sets of integral norms and data norms. |
| Sharp constant | `sourceLemma10_4_const_sharp` | Constant data c have supremum exactly |c|. |

The chosen side is represented by a Boolean and the stopping point by
t∈[-1,1]. Together they parametrize the two closed copies G_n⁺ and G_n⁻.
The upper and lower traces are respectively -iδ√(1-t²) and +iδ√(1-t²),
where δ=γ_n/2. Their identification with the actual root is proved by the
existing arbitrary-approach limit theorem; it is not an assumed boundary
formula. Both trace values vanish at the two branch points.

`sourceStandardRootSideIntegral` is defined by the literal affine pullback

```
∫_a^b f(τ_n + δ r) · δ / sourceStandardRootSideTrace(n,r,side) dr.
```

This is a boundary-trace integral; the value of the totalized principal
root formula on its branch cut is not substituted for its side limit.
Only f restricted to G_n is needed. Endpoint division is totalized in
Lean, but genuine integrability and the truncation-limit theorems prove
that endpoint values do not change the intended improper integral.
No assumption of an off-gap extension of f is made.

The main theorem chooses one attained maximum before quantifying over
all stopping points and both sides. The set of integral norms is
nonempty (it includes the left endpoint) and bounded above by that same
maximum. The supremum bound therefore concerns the literal real sSup,
not a newly defined quantity stipulated to satisfy the estimate. The
right-hand data supremum is likewise finite and attained on the actual
canonical gap.

For constants c, `sourceStandardRootSideIntegral_const_full` proves the
exact normalized values +ic on the upper side and -ic on the lower side.
Both full sides attain |c|; the entire set of values has supremum |c|.
The two endpoint integrals have opposite signs for arbitrary continuous
data, and stopping at the initial endpoint gives zero.

## Lemma 10.4: evidence for the index correction

For real-type ψ and m≠n, w_m is real on the whole closed real gap G_n,
and δ_n is real. Thus δ_n/w_m(τ_n) has imaginary part zero. It cannot
equal either ±i, as the printed substitution would require at r=0 with
constant data one. `sourceLemma10_4_printed_kernel_counterexample`
provides an actual noncollapsed real source for every selected index
and every finite exponent p>1. This formally refutes that wrong-index
kernel identity. It does not purport to disprove every possible
wrong-index integral bound.

Public checks expose the literal trace-based integrand and supremum,
exercise both endpoint singularities, one- and two-endpoint truncations,
midpoint stopping, both orientation signs, constant sharpness and a
nonconstant test function. An actual noncollapsed real source at p=3/2
and index -1 attains the sharp value one. The correction check also uses
actual noncollapsed sources, so neither sharpness nor the index witness
is conditional on an uninhabited hypothesis.

Next: Lemma 10.5, convergence, analytic domains and nonvanishing of the
omitted standard-root product. The dissertation remains incomplete.


## Lemma 10.5: the actual product and its normalization

The source on printed p. 57 defines

```
f_n(z) = (1/π_n) ∏_{m≠n} w_m(z)/π_m,   π_0=1, π_n=nπ for n≠0.
```

`sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ)` is literally
that finite product over [-N,N] with n erased. Its definition includes
the outer division by π_n at every cutoff, even before the cutoff
reaches n. `sourceStandardRootOmittedProduct` is the zero-mode prefactor
times the infinite product of positive/negative pairs, with the selected
factor replaced by one. `tendsto_sourceStandardRootOmittedPartialProduct`
identifies this value as the limit of the literal cutoffs at every source,
spectral point and omitted index. No limit or normalization is assumed.

The paired factors have summable norms of their deviations from one.
`exists_uniform_absolute_sourceStandardRootOmittedPairedFactor_tails`
strengthens this to a common vanishing bound on arbitrary finite subsets
of the high-frequency tail, uniformly for all nearby sources and all
spectral points in a prescribed bounded region. After a cutoff at least
|n|, omission no longer changes the tail. This gives the normal convergence
used in the analyticity proof. Absolute convergence concerns these paired
blocks, as in the source's displayed regrouping.

## Lemma 10.5: one unchanged common domain and local family

`SourceLemma10_3Data.omittedProducts` takes any open common domain W
with the Lemma 10.3 data and returns `SourceLemma10_5Data` on exactly W.
It does not construct a replacement W or shrink it. Each local package
is built from the already supplied V,D,c and extends its
`SourceStandardRootNeighborhoods`; its isolation, root bounds, root
analyticity and general contour identity remain available.

| Source requirement | Formal field or theorem | Exact scope |
| --- | --- | --- |
| Spectral domain | `sourceStandardRootOmittedDomain_eq_compl_iUnion` | The literal complement of the union of all G_m with m≠n. |
| Spectral analyticity | `SourceLemma10_5Data.spectral` | Every source in the same W and every integer n. |
| Joint analytic domain | `.joint` | The open moving-gap complement over W; openness is proved. |
| Local uniform convergence | `.locally_uniform` | Actual symmetric finite cutoffs, jointly in source and spectral point. |
| Uniform convergence on compact sets | `SourceLemma10_3Data.omittedCompact`, `.omittedSpectralCompact` | Joint compact sets and spectral compact sets at a fixed source. |
| Printed fixed-disk domain | `SourceOmittedRootNeighborhoods.omitted_joint` | (ℂ∖⋃_{m≠n} closure(D_m))×V, retaining the source's overlines. |
| Stronger fixed domain | `SourceLemma10_3Data.omittedFixed` | Analyticity and nonvanishing also on the complement of the open disks, including their boundaries. |
| Nonvanishing | `SourceLemma10_5Data.nonzero`, local `.omitted_nonzero` | The whole moving-gap domain, even for arbitrary complex sources, and the printed local fixed domain. |
| Omitted gap itself | `SourceOmittedRootNeighborhoods.omitted_disk` | The whole omitted disk D_n is analytic and nonzero, including all points of G_n and collapsed gaps. |

The joint proof uses the same analytic midpoint and squared-gap
coordinates as Lemma 10.3. Every finite cutoff is analytic, and the
uniform paired tails give a locally uniform limit on the open joint
domain. Restriction to a fixed source gives spectral analyticity.
Containment of each actual gap in its fixed disk gives the claimed local
joint domain. Pairwise disjointness puts all of D_n in the complement of
the unomitted gaps. Nonvanishing follows from summable paired deviations
and the nonzero actual factors; finite products alone would not suffice.

## Lemma 10.5: free normalization and ordering checks

`sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient` proves
that the actual free product is the filled quotient sin(z)/(z−nπ) on all
of ℂ. The omitted point is filled by cos(nπ), of norm one. The function
is entire and vanishes at every unomitted lattice point. These assertions
check the sign and the prefactor for positive, zero and negative indices,
and delimit the nonvanishing domain precisely.

`sourceStandardRootRelativeError_zero_source_positive_norm` proves the
exact harmonic error |z|/(π(k+1)) for an individual positive-index factor
at zero source. Its series is not summable when z≠0, whereas the paired
deviations are summable. A public check uses z=i and formally verifies
that this is in the actual free omitted domain. Pairing is therefore an
essential convergence convention, not merely a notation choice.

The source's isolated a_k a_{-m} in one intermediate estimate is recorded
as a proof-index typo: the next lines use the required a_k a_{-k}.
The statement of Lemma 10.5 itself needs no new correction.

Public checks instantiate the full package at p=3/2, transfer an arbitrary
Lemma 10.3 domain unchanged, expose the literal cutoff formula, and test
negative-index omission before its index enters the cutoff. They check
joint and spectral compact convergence, the printed closed-disk domain,
analyticity and nonvanishing on the entire omitted gap, and uniform
absolute tails over arbitrary finite sets. Free checks cover the omitted
negative center's sign, its unit norm, every other zero, entire extension,
and paired versus individual convergence at the same genuine domain point.

Next: Corollary 10.6, the quotient product with variable displaced roots.
The dissertation remains incomplete.


## Corollary 10.6: literal product and all root parameters

The source on printed p. 57, visually checked, states that

    ∏_{m≠n} (σ_m−λ)/w_m(λ)

is analytic on

    (ℂ \ ⋃_{m≠n} closure(U_m)) × ℓᵖ × V_φ.

The bar over U_m is present in the printed formula. The displacement
parameter is a=σ−σ⁰, where σ⁰_m=mπ. `exists_displacedRoots_iff_memℓp`
proves that `Coeff p` represents exactly this affine root space. No root
ordering, distinctness, size bound or numerator nonvanishing condition is
added. The omitted index ranges over all integers, including zero and
negative indices; p ranges over every finite exponent greater than one.

`sourceSingleRootQuotientPartialProduct` is the literal product over
[-N,N] with n erased. The existing finite quotient identity cancels both
π_n prefactors and every π_m factor exactly, including at early cutoffs.
`SourceSingleRootQuotientCommonDomain.lean` proves local uniform convergence
of these cutoffs in λ, a and ψ, hence uniform convergence on every compact
subset of the triple domain. The numerator is jointly entire and the
omitted-root denominator is analytic and nonzero there.

## Corollary 10.6: individual absolute convergence and unordered products

Unlike the separate factors in Lemma 10.5, the quotient factors have
absolutely summable individual deviations from one. For noncentral m,
put e_m=w_m/(πm)−1. The existing midpoint correction b_m and square-root
correction r_m satisfy

    e_m = b_m − λ/(πm) + r_m.

If d_m=a_m/(πm)−b_m−r_m, then exactly

    (σ_m−λ)/w_m(λ)−1 = d_m/(1+e_m)

where the denominator is nonzero. Hölder gives a_m/(πm)∈ℓ¹, and both b
and r already belong to ℓ¹. The normalized root errors e belong to ℓ²
and tend to zero along the cofinite filter. Eventually |1+e_m|≥1/2,
so the individual quotient error is bounded by 2|d_m|. The finitely many
remaining indices cause no summability problem.

`summable_norm_sourceSingleRootQuotientFactor_sub_one` proves the absolute
summability. `hasProd_sourceSingleRootQuotient_subtype` identifies the
unconditional product over {m∈ℤ | m≠n} with the analytic quotient on the
natural domain. `tendsto_finset_sourceSingleRootQuotient` gives convergence
over all finite subsets with n erased. These assertions do not rely on
choosing positive/negative pairs or a particular enumeration. The product
identity is asserted only where the unomitted actual gaps are avoided;
no analyticity is claimed for totalized division at excluded gap points.

## Corollary 10.6: unchanged domains and degeneracy checks

`SourceLemma10_5Data.quotients` constructs `SourceCorollary10_6Data` on
exactly the supplied W. Its local `SourceSingleRootQuotientNeighborhoods`
extends the earlier omitted-root package, preserving the same V, D and c.
Both the quotient and the literal unordered product are jointly analytic
on the printed closed-disk complement times all a and V. The larger open
moving-gap domain and the whole selected disk are also covered. In
particular, the selected gap's endpoints and collapsed case are included.

The free quotient is one at every point of its natural domain, including
λ=nπ. The omitted coordinate a_n has no effect on the function. Every
unomitted numerator root remains a zero. The explicit displacement

    a_0=i, a_{−1}=π+i, a_m=0 otherwise

has σ_0=σ_{−1}=i. At zero source, i lies in the actual natural domain;
with n=−1 the quotient equals zero. Thus a collision between the omitted
root and an unomitted root is allowed, and does not create a pole.

Public checks cover the complete package at p=3/2, the same-domain transfer,
literal finite normalization, unordered product identity, convergence over
all finite subsets, joint compact convergence, printed closed-disk
analyticity, selected-gap analyticity, arbitrary omitted-coordinate changes,
free values at nπ and i, and the explicit collision at p=3/2.
The source statement requires no new correction.

Next: equation (2.13) and Lemma 10.7, the canonical-root product and its
analytic domains. The dissertation remains incomplete.


## Equation (2.13) and Lemma 10.7: exact product and domains

The source on printed pp. 57–58, visually checked, defines the canonical
root by

    R(λ) = 2i w_n(λ) f_n(λ) = 2i ∏_{m∈ℤ} w_m(λ)/π_m,

with π_0=1 and π_m=mπ for nonzero m. Its literal finite products use
[-N,N]. Restoring an omitted index gives the same finite product once
N≥|n|. The limit factors through every omitted n, and its square is the
actual source Δ²−4 on the complement of ALL closed periodic gaps. The
paired convention from Lemma 10.5 is retained for the full standard-root
product; Corollary 10.6's unconditional quotient result is not incorrectly
applied to these separate factors.

`SourceCorollary10_6Data.canonicalRoots` constructs `SourceLemma10_7Data`
on exactly its supplied W. The package retains the entire preceding
corollary. The full joint moving-gap domain is open: it is the intersection
of the omitted domains for indices 0 and 1. The literal symmetric cutoffs
converge locally uniformly there. Uniform convergence on joint compacts
and on spectral compacts at a fixed source is explicit.

The printed fixed domain is

    (ℂ \ ⋃_{m∈ℤ} closure(U_m)) × V_φ.

The bar over U_m is present in the printed formula. Every local
`SourceCanonicalRootNeighborhoods` retains the original V, D and c and
proves analyticity on this exact closed-disk complement. Spectral
analyticity and nonvanishing on the full gap complement hold for every
original complex source, a stronger scope than restricting to W.

## Equation (2.14): actual boundary values on closed complex gaps

For the affine coordinate λ=τ_n+(γ_n/2)t, -1≤t≤1, the upper and lower
traces are the actual limits of the canonical root from the corresponding
open sides of the gap. The limits allow arbitrary approaches within each
side, including to the midpoint and both endpoints. The chosen sides
are oriented by the complex half-gap, as in the standard-root formulas.
The traces are defined by multiplying the corresponding standard-root
trace by 2i f_n at the same point.

`SourceCanonicalRootBoundaryData` includes:

- continuity of both traces on the CLOSED parameter interval [-1,1];
- actual upper and lower limits for every noncollapsed gap;
- the exact opposite-value relation (2.14);
- zero values at both endpoints on both sides;
- nonzero interior values for a noncollapsed gap;
- both traces' squares equal to the actual source Δ²−4 at the gap point.

The entire selected gap belongs to the omitted product's domain by the
original isolating family. These statements therefore hold for all
complex sources in the same W, with no new separation hypothesis or
source-neighborhood shrink.

The globally totalized algebraic expression for a standard root at a
point on its cut is not substituted for its boundary trace. In particular,
the raw midpoint expression of a noncollapsed gap must not be used to
claim the canonical-root square identity at that cut point. The package
states the raw root's square identity off the gaps and the trace square
identities on them.

## Lemma 10.7: collapsed gaps and the branch normalization

If γ_n=0, the canonical root is exactly

    R(λ) = 2i (τ_n−λ) f_n(λ)

and is analytic on the entire original selected disk D_n. Its value at
τ_n is zero, and its derivative there is -2i f_n(τ_n), which is nonzero.
Thus the analytic continuation has a simple zero. This is an extension
for the fixed source, not a joint extension through arbitrary nearby
sources where the gap could reopen.

At zero source, the actual root equals -2i sin(λ) on all of ℂ and is
entire. Its value at π/2 is -2i, the first cutoff at i is 2, and its
derivative at -π is +2i. These values check the factor 2i, the π_0=1
normalization and the choice of branch, beyond merely checking a square.

## Figure 2.4: real-source signs, including negative indices

For real-type sources and an open real gap, the upper and lower traces
are real and have opposite signs. Their signs relative to (-1)^n are
positive above and negative below. In the adjacent bands the canonical
root is purely imaginary, with sign (+i)(-1)^n on the left and
(-i)(-1)^n on the right. `sourceCanonicalRoot_figure_gap_signs` and
`sourceCanonicalRoot_figure_band_signs` give these four assertions for
every integer n. The equivalence between parity of |n| and n handles
negative indices and the change from band n−1 to band n.

These real/imaginary signs describe the figure on the real-type locus;
for complex sources the exact opposite boundary-value relation is used.
A genuine open gap at n=−1 witnesses a negative upper real value and a
positive lower real value. The proof obtains the source from the existing
real Floquet gap-opening theorem and derives strict endpoint separation.

Public checks include the full package at p=3/2, preservation of the
Corollary 10.6 domain, literal cutoff normalization, restoration at a
negative index, both compact convergence statements, the exact gap-union
and closed-disk domains, the discriminant identity and nonvanishing off
cuts, trace squares on cuts, endpoint and midpoint approaches, collapsed
continuation and its simple-zero derivative, and both negative-index
figure signs. No new source correction is required.

Next: Lemma 10.8, the quotient-product asymptotic estimate with its sequence
exponents and local uniformity. The dissertation remains incomplete.

## Lemma 10.8: supremum estimates on the complete original disk family

The displayed statement and proof on printed pp. 58–59 were visually
checked. Let a=σ−σ⁰ be the original ℓp numerator displacement and let
α=σ−τ be its offset from the source midpoints. The source's introduction
defines a sum of sequence classes as an exact decomposition, and ℓ(1+)
as membership in every finite exponent r>1.

`SourceLemma10_8Estimates` retains the whole Lemma 10.7 package on exactly
the supplied W. At each φ in W it keeps the original V, disk family D
and distance constant c. This family is chosen before a and before the
target exponent. Near each (a,φ), one open joint neighborhood supplies
all the estimates below. No real-type or near-zero restriction is added.

The positive distance inequality extends to the closure of each disk.
Consequently, its closure avoids every other actual gap and lies in the
selected omitted-root domain. Each closed disk is compact. Applying joint
continuity over finitely many such compact slices gives a common local
bound for the finite central part of the quotient error.

For the tail, `SourceQuotientAsymptoticGeometry` uses an auxiliary free
family with empty central disks and the usual quarter-π tail disks.
This is only an adapter to the existing tail estimates: every auxiliary
disk is a subset of the corresponding actual D_n, and all tail disks
agree exactly. The actual central disks remain nonempty and are covered
by the separate finite bound. The original separation constant is retained.

`sourceQuotientDiscSup` is literally

    E_n(a,ψ) = sup { |Q_n(λ,a,ψ)−1| : λ ∈ D_n }.

Its defining set is nonempty and bounded above. Every pointwise error is
at most E_n, and E_n is at most any upper bound for the disk image. This
is the least upper bound, not just a chosen dominating sequence. The
unordered product from Corollary 10.6 equals Q_n on each actual D_n.

## Lemma 10.8: exact sequence classes and uniformity proved so far

For each T≥0, consider the family of parameters in the joint neighborhood
for which α∈ℓq and ||α||q≤T. The bounds are uniform on this family:

| Offset exponent | Exact decomposition of E | Uniform bound |
| --- | --- | --- |
| 1<q<∞ | A_q+B_(p/2) | Separate bounds on both sequence norms |
| q=1 | A_(p/2)+B_(1+) | One pair chosen first; every finite r>1 projection of B has a uniform bound |
| q≥p, including ∞ | A_q+B_(p/2) | Locally uniform in the original ℓp root topology, with the same neighborhood and bounds for all q≥p |

The q=1 construction does not merely choose unrelated remainders for
different r. It gives functions into the actual `CoeffOnePlus` space,
then bounds every projection of those fixed functions. When p/2>1, the
whole endpoint sequence can be placed in ℓ(p/2); when p/2≤1, it belongs
to every ℓr for r>1. These alternatives give a genuine fixed pair and
cover the quasi-Banach range. Adding a zero component gives the printed
three-term decomposition at every finite q≥1.

For q≥p, the offset's original ℓp norm is bounded locally by the root
displacement norm and the midpoint-displacement bound. Contractive
sequence inclusion supplies q=∞ as well. For q<p, the proof currently
requires an explicit bound on ||α||q. It does not claim that this stronger
norm is locally bounded in the weaker ℓp topology.

For the free numerator a=0, α=−(τ−σ⁰) belongs to ℓp with a local norm
bound. The filled sine quotient divided by the omitted standard-root
product therefore has a full-disk supremum decomposition with q=p,
locally uniformly in the source. Away from λ=nπ the filled quotient
equals the printed sin(λ)/(λ−nπ); at the center it uses the removable
value cos(nπ), including the negative-index sign.

## Lemma 10.8: concrete checks and remaining source audit

Public checks instantiate the complete estimate package at p=3/2,
test the q=∞ target, identify the literal least upper bound, and project
one fixed endpoint remainder at both r=2 and r=3. An open neighborhood
of zero in W is shown to contain an actual non-real source, so the
general complex-source coverage is not vacuous.

At free source with free roots the supremum is zero on every actual disk.
An explicit finitely supported numerator displacement moves the zeroth
root onto −π, colliding with the −1 root. In the quotient with −1 omitted,
the numerator vanishes at −π while the omitted denominator is nonzero.
The actual selected central disk contains −π, and its supremum is at
least one. This witnesses that the finite head has not been discarded.

## Lemma 10.8: the original-topology claim is false in general

The p=4, q=1 case is now refuted by actual finite-block numerator
perturbations at the free source. This is stronger than observing that
an ℓ1 input norm need not be bounded in ℓ4.

For a_m=b on 1≤m≤L and zero elsewhere,
`sourceSingleRootQuotient_block_eq_finiteProduct` proves

    Q_n(nπ,a,0) = ∏_(1≤m≤L) (1−b/(π(n−m)))    (n outside the block).

If 0≤b≤π and 2L<n≤3L, the sum of the deficits is between b/(3π)
and one. The finite-product estimate gives |Q_n−1|≥b/(6π), hence
||B||₂²≥L(b/(6π))² for every ℓ2 majorant B. With L=k⁴ and b=δ/(2k),
the input has ||a||₄=δ/2 while ||B||₂≥δk/(12π). Increasing k yields
unbounded output norms on every ℓ4 neighborhood, with all offsets in ℓ1.

`not_locally_uniform_sourceQuotientDiscSup_mixed` applies the obstruction
to the literal supremum on any actual disk-estimate neighborhood of the
free source whose disks contain the free centers. The three printed
components would give an ℓ2 majorant by contractive ℓ1 inclusion and the
ℓ2 projection of the ℓ(1+) component. Their combined norm bound is
impossible, independently of how the components are chosen or cancel.
`exists_sourceQuotientDiscSup_uniformity_counterexample` constructs such
a neighborhood from `sourceLemma10_8_estimates` itself.

`SourceQuotientDiscEstimates.free_sup_mem_l2_of_summable` separately
proves individual ℓ2 membership for every summable free-source offset
in an actual estimate neighborhood. Thus the discrepancy is specifically
local uniformity, not the pointwise sequence class. Public checks also
test the exact finite product at a negative free center, constant small
input norm as the support grows, and an arbitrarily large output bound.

A sufficient correction is the already proved explicit ℓq offset bound
when q<p. The original-topology result for q≥p remains valid. The formal
counterexample uses p=4, q=1; it does not classify every pair q<p.

The free-sine display's unspecialized q is now the sole remaining
Lemma 10.8 audit question. Its unconditional q=p consequence is proved.
A general-q specialization requires appropriate estimates for the free
midpoint offset, which cannot be inferred from an arbitrary numerator's
offset. The present counterexample does not settle that separate claim.
After resolving it, proceed to Remark 10.9 and Lemma 10.10.

## Lemma 10.8: quadratic diagonal contribution to the free-sine audit

The remaining general-q question cannot be settled by the numerator
counterexample, which varies the roots while holding the source at zero.
The free numerator fixes those roots; its offset is the negative midpoint
displacement. The new work isolates an actual source contribution that
has better sequence summability than the existing endpoint-average bound.

For physical coefficients a,b, define f_j=b_j a_(−j). Hölder gives
f∈ℓ(p/2) and ||f||_(p/2)≤||a||p ||b||p, including p/2<1. The quadratic
diagonal is the signed row

    A2_n(z) = ∑_(j≠2n) f_j / (z+πn−πj).

`resonantDiagonalQuadratic_eq_physical` identifies this with the first
actual resolvent iterate. Sampling each z_n independently in its free
quarter-π disk and filling unused odd rows yields a sampled discrete
Hilbert transform at indices 2n. For finite r>1 and r≥p/2, contractive
sequence inclusion and the Hilbert bound give

    ||sup_(z∈disk_n) |A2_n(z)||r
      ≤ π⁻¹ (H_r+||HilbertSquare||) ||a||p ||b||p.

The supremum is literal. Its coefficient sequence is obtained from the
uniform bound over every independent selection, not merely from estimates
at one center. Bounded input families have a single ℓ(p/2)+ℓ(1+) pair;
the ℓ(1+) summand is fixed before choosing any projection exponent.

The actual diagonal's remainder is explicitly the diagonal row tested
against T_n² E_n, where E_n is the actual even corrected source vector.
`weightedResonantA_sub_quadratic` proves exact equality with that
remainder. The estimates retain the spectral square bound and reciprocal
row norm before giving |R_n(z)|≤C_p ||φ||⁴ on the contraction region.
No half-exponent sequence estimate for R is claimed from this pointwise
quartic inequality.

Period-one embedding removes the odd physical frequencies and produces

    A2_n(z,φ) = ∑_(m≠n) φ₂,m φ₁,−m / (z+πn−2πm).

At the free center this equals −(2π)⁻¹ times the source Hilbert row.
The components are independent complex sequences; reflection introduces
no complex conjugation. The source transport supplies a quadratic bound
for the actual free-disk supremum using the original pair norm.
`exists_local_sourceResonantDiagonalQuadraticExpansion` supplies one open
original-source neighborhood and one cutoff on which the actual analytic
diagonal differs from this term by at most C_p ||φ||⁴, throughout every
distant closed resonant strip. No contraction assumption is left as a
premise on that neighborhood.

This proves the needed summability for the quadratic contribution only.
The nonlinear remainder still requires sequence estimates, and the
diagonal centers must still be related quantitatively to the actual
periodic midpoints. The unconditional free-sine result remains q=p until
those steps, or another complete argument, resolve its printed general q.

## Lemma 10.8: midpoint-center comparison at the half exponent

The midpoint-to-center step left open above is now proved, locally
uniformly on the original source space. Write ζ_n for the named center
solving ζ_n=nπ+a_n(ζ_n) on distant strips, and τ_n for the actual canonical
periodic midpoint. Then

    |τ_n−ζ_n| ≤ (8/π) sup_(z∈strip_n) |b_n⁺(z)b_n⁻(z)|.

For distinct endpoints, subtracting the two root equations controls the
sum of their diagonal residuals. At a repeated endpoint, actual analytic
order two forces the determinant derivative to vanish, giving the same
bound. A repeated simple root would not suffice; the public checks
include a concrete failure when one simply duplicates a simple root.
Second-derivative bounds for the diagonal make the midpoint Taylor error
proportional to the squared gap. All estimates apply to complex sources.

The full off-diagonal coefficients are bounded by actual ℓp sequences,
including their leading Fourier coefficients and double reciprocal-row
remainders. Hölder places their product in ℓ(p/2), even below exponent
one. The comparison therefore produces an actual half-exponent tail
sequence with a locally uniform norm bound. The canonical midpoint has
an existing uniform coordinate bound, and the named diagonal center
always stays within π/4 of the free center. These control a fixed finite
head and give the full sequence result. The named center retains its
existing free fallback at central indices where its fixed-point
existence is unavailable.

`exists_uniform_sourceMidpointCenterError` proves the full neighborhood
and norm assertion. `memℓp_sourceMidpointDisplacement_iff_center` proves
that for any r≥p/2, midpoint and diagonal-center displacements have
equivalent ℓr membership. This resolves the midpoint transfer required
by the quadratic-diagonal approach. The nonlinear diagonal remainder at
the moving centers still needs sequence bounds; its quartic pointwise
bound is insufficient. The printed general-q free-sine claim remains
unresolved, and its unconditional q=p version remains proved.

## Lemma 10.8: completion of the refined free-sine consequence

Eight modules close the remaining Lemma 10.8 free-sine exponent audit.
The literal free-sine quotient error on every original isolating disk has
one locally uniformly bounded ℓ(p/2)+ℓ(1+) decomposition for every finite
p>1. This implies the printed consequence for every q≥1 by taking its
ℓq summand to be zero. The separate original-topology uniformity claim
for arbitrary numerators remains formally refuted at p=4, q=1.

`YoungConvolutionTranspose.lean` transposes the absolutely convergent
Banach-space convolution series through the conjugate pairing.
`UnweightedDoubleRowTesting.lean` tests the two remaining actual
resolvent symbols against arbitrary outer rows.
`ResonantDiagonalRemainderRows.lean` uses the auxiliary exponent 2p and
its conjugate to identify the exact transposed nonlinear diagonal
remainder. Young and Hölder retain two source-frequency reciprocal rows
instead of discarding their dependence on the index.

`ResonantDiagonalRemainderMajorants.lean` applies powered Young to both
rows. Each has an ℓp majorant; their product belongs to ℓ(p/2), including
the quasi-normed range p<2. The resulting majorant controls the actual
nonlinear remainder simultaneously over each full strip on the proved
contraction region. Its norm is quartic in the unweighted component norms.
`SourceDiagonalRemainderMajorants.lean` supplies the contractions on one
original-source neighborhood and cutoff, with a common majorant norm.

`SourceDiagonalCenterSummability.lean` combines the quadratic disk
estimate with this nonlinear bound at the moving diagonal centers.
A fixed finite head covers the named center's free fallback.
`SourcePeriodicMidpointRefined.lean` adds the previous midpoint-center
error. The full actual canonical midpoint displacement is locally
uniformly in every finite ℓr with r>1 and r≥p/2, on a single neighborhood
independent of r. Thus p>2 includes ℓ(p/2); p≤2 gives ℓ(1+), without
claiming ℓ1. One fixed mixed pair realizes these estimates.

`SourceFreeSineQuotientRefined.lean` inserts the actual free-minus-midpoint
offset into the existing full-disk quotient estimates. The theorem
`sourceLemma10_8_freeSine_refined` keeps the common almost-real source
domain and the original disk family, including every central disk and
the filled value at the removable free center. Its two summand maps are
chosen before every ℓ(1+) projection exponent, with uniform bounds on
one source neighborhood.

Lemma 10.8's audit is now resolved: bounded-offset estimates, the valid
original-topology range, the arbitrary-numerator uniformity counterexample,
and the unrestricted free-sine consequence are all accounted for. The
printed arbitrary-numerator uniformity assertion has not been proved;
it is false as stated. Next: Remark 10.9's sharpness expansion, then
Lemma 10.10 and the remaining Section 10 statements.

Validation: `./scripts/check.sh` passed (6,893 build jobs, the full public example suite, and the axiom audit of 31,950 NLS declarations). The build retains 21 existing warnings; the eight new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Remark 10.9: exact Taylor expansion and remaining sharpness audit

Five modules prove the exact Taylor expansion underlying Remark 10.9.
For every finite p>1, the literal supremum over each original isolating
disk of

    | product_(m≠n) (τ_m−z)/w_m(z) − 1 − sum_(m≠n) γ_m²/[8(τ_m−z)²] |

is an ℓ(p/4) sequence, locally uniformly in the original source topology.
The estimate includes every central disk, repeated roots and collapsed
gaps. It does not round the exponent up to one or require a distant-index
cutoff. The disk family and common almost-real domain are retained.

`InverseSqrtProductTaylor.lean` proves the exact algebraic identity

    (sqrt(1−q))⁻¹ − 1 − q/2
      = (sqrt(1−q)−1)² (1/2 + (sqrt(1−q))⁻¹).

A uniform inverse-root bound controls the absolutely convergent infinite
product after its signed linear term, without a small-radicand hypothesis.
`SourceMidpointQuotientTaylorGeometry.lean` derives that inverse-root bound
from the original two-sided disk separation, identifies the unordered
product with the actual midpoint-numerator quotient, and records the
coefficient 1/8 and the moving midpoint denominator explicitly.

`SourceMidpointQuotientTaylorMajorant.lean` squares the actual reciprocal
squared-gap row using quasi-norm Hölder. `SourceRemark10_9Taylor.lean`
constructs the literal supremum coefficient and gives one common norm
bound near each source. The public theorem is
`sourceRemark10_9_exactTaylor`.

`SourceSquaredGapRowLowerBound.lean` shows that the row centered at m+1
is at least |γ_m|². Thus improved summability of the absolute row would
force the same improvement for the actual squared gaps. This gives a
necessary condition, not an example realizing a sharp exponent.

At this milestone, the printed replacement of the exact leading sum
by sum_(m≠n) γ_m²/(m−n)² was unresolved. The subsequent actual-source
counterexample recorded here refutes its asserted remainder class at
p=8. The corrected moving-denominator expansion remains valid. The full
p/2 optimality assertion still requires a separate audit before Lemma
10.10 and the remaining Section 10 statements.

Validation: `./scripts/check.sh` passed (6,898 build jobs, the full public example suite, and the axiom audit of 31,985 NLS declarations). The build retains 21 existing warnings; the five new modules and eight focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs or additional axioms were introduced.

## Remark 10.9: actual-source counterexample to Remark 10.9's printed remainder

Four modules resolve the printed integer-kernel replacement in Remark
10.9. At p=8, every open neighborhood of zero in the original source
space contains a real potential and an original isolating-disk family
for which the literal printed remainder supremum is outside ℓ². Hence
it is outside the asserted ℓ(p/4)+ℓ(1+) class. This is a counterexample
using actual spectral data, not freely chosen abstract gaps.

`QuarterPowerWitness.lean` constructs the real ℓ⁸ sequence |n|^(-1/4),
zero at n=0, and proves that the squares of every nonzero real multiple
fail ℓ² membership. `SourceSquaredGapNonSummability.lean` scales this
sequence into the target of the already verified inverse Birkhoff chart,
restricted to an arbitrary prescribed open source neighborhood. The
chart preserves reality and the actual action-radius identity. The
bounded normalized-action roots and exact action-gap factorization then
force the actual squared gaps of the inverse source to lie outside ℓ².

`SourceRemark10_9LatticeTerm.lean` identifies the printed signed sum with
the nonnegative physical squared-gap row S for real sources. When the
midpoint displacement has norm at most one, the exact linear term L at
the free center nπ satisfies |L_n(nπ)| ≤ S_n/8. The printed row therefore
cannot be replaced by that Taylor term modulo an ℓ² error for the
constructed source.

`SourceRemark10_9Counterexample.lean` proves boundedness of each printed
supremum on every original disk before using it. If those suprema formed
an ℓ² sequence, combining them with the verified exact Taylor remainder
would give an ℓ² majorant for S on the tail. Finite-head completion and
the neighboring-row lower bound would put the squared gaps in ℓ², a
contradiction. The conditional obstruction works for every isolating
family containing the source; the final theorems construct such a family.

The public results are `sourceRemark10_9_printed_counterexample` and
`sourceRemark10_9_printed_decomposition_counterexample`. The latter
explicitly excludes a decomposition with one ℓ(8/4) summand and one
ℓ(1+) summand. The corrected moving-denominator expansion from the
previous milestone remains valid, including for these same sources and
disks. Seven public checks cover small nonzero real sources, both
remainder classes on the same data, the literal lattice sum, and bounded,
nonnegative suprema on all disks.

Next: prove or correct the full p/2 optimality assertion for actual source
potentials, then audit Lemma 10.10 and the remaining Section 10 statements.
The p=8 obstruction at exponent two does not by itself prove optimality
at every exponent below p/2. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed (6,902 build jobs, the complete public example suite, and the axiom audit of 32,016 NLS declarations). The build retains 21 existing warnings; the four new modules and seven focused public checks are warning-free. The source inventory verified 156 candidate labels, and `git diff --check` passed. No admitted proofs, additional axioms, or heartbeat overrides were introduced.
