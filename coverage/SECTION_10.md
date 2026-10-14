# Section 10: potentials of almost real type

This audit follows the source statements and proofs on printed pp. 54–56.
The neighborhood assertion is proved with the real-type locus used in
the proof. The printed all-complex version has a formal counterexample.
Lemmas 10.2 and 10.3 are covered on the same common domain, including the
preceding simple-root assertions and general piecewise C¹ contours.
Lemma 10.4 and later statements remain to be audited.

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
