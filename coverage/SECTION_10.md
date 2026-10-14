# Section 10: potentials of almost real type

This audit follows the source statement and proof on printed pp. 54–55.
The neighborhood assertion is proved with the real-type locus used in
the proof. The printed all-complex version has a formal counterexample.
Lemma 10.2 and later statements are not certified by this milestone.

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

## Verification and remaining scope

The public examples exercise the global theorem at p=3/2, zero-potential
local families and collapsed gaps, all ordinary cluster coordinates,
full gap segments, central and negative-index infimum distances, positive
real-centered disks, exact free tails, and disjointness. A tangent-disk
example checks that shrinking creates positive separation. A separate
example exposes the greatest-lower-bound characterization of set distance.
The counterexample checks include the multiplicity lower bound,
four-coordinate injectivity below two, impossibility of arbitrary
disjoint shapes, and negation of the printed all-complex domain.

Next: Lemma 10.2, including common-domain analytic power sums and pair
factors, and locally uniform original sequence bounds for the midpoint
and squared gap. The remaining dissertation is incomplete.
