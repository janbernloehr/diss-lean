# Implementation status

## Implemented and checked

The library has thirty-two modules and 329 named public theorems. All compile on the
pinned Lean/mathlib v4.33.1 toolchain.

| Module | Implemented scope |
| --- | --- |
| `NLS.SequenceSpaces.Basic` | Integer-indexed complex `lp` coefficients |
| `NLS.SequenceSpaces.Truncation` | Finite projections; coefficient formula; linearity; composition and idempotence; projection and tail norm bounds; continuous linear projections; convergence for finite `p`; density of finite-support coefficients |
| `NLS.SequenceSpaces.Weighted` | Positive, unit, and real-exponent Sobolev weights; weighted coefficient spaces; weighting equivalence and isometry; normed complex vector space and completeness; coefficient decay; weighted truncation bounds and convergence |
| `NLS.SequenceSpaces.Multiplier` | Bounded diagonal symbols; norm bound; continuous linear operator; commutation with truncations |
| `NLS.SequenceSpaces.Translation` | Reindexing by an integer equivalence preserves the norm; shifts as linear isometry equivalences |
| `NLS.SequenceSpaces.Convolution` | Absolutely convergent Banach-space construction; coefficient formula; `lp × l1 → lp` norm bound, including `p=∞`; continuous bilinear map; single-mode shift identity |
| `NLS.SequenceSpaces.Embedding` | General weighted Hölder embedding into `l1` when the reciprocal weight belongs to the conjugate space; explicit bound and injectivity |
| `NLS.SequenceSpaces.SobolevEmbedding` | Reciprocal one-derivative weight is in `lq` for `q>1`, including infinity; continuous embedding `FL^{1,p} → FL^1` for every finite `p≥1` with an explicit constant |
| `NLS.ZakharovShabat.Potential` | Scalar Fourier-side potential multiplication on the one-derivative domain; convolution coefficient formula; norm and operator-norm bounds; constant unit potential identity |
| `NLS.ZakharovShabat.Domain` | Contractive, injective scalar inclusion with dense range for finite `p`; period-two differentiation and its norm bound; scalar Fourier modes |
| `NLS.ZakharovShabat.Operator` | Pair domain inclusion and density; free, potential, and total operators; coefficient formulas; maximum-pair-norm bounds; nonzero signed free eigenmodes; zero and unit potential identities; spectral pencil |
| `NLS.SequenceSpaces.Compact` | Compactness of finite Fourier projections; uniform symbol-tail bound for the cutoff error; operator-norm convergence and compactness of vanishing diagonal multipliers, including `p=∞` |
| `NLS.ZakharovShabat.FreeResolvent` | Closed free lattice and positive spectral gap; inverse into the one-derivative domain; both inverse identities and continuous linear equivalence; domain and base-space bounds; signed-mode formulas and resolvent identity |
| `NLS.ZakharovShabat.FreeResolventCompact` | Uniform decay of reciprocal symbols; operator-norm convergence of scalar resolvent cutoffs; compactness of scalar and pair free resolvents for all Banach exponents |
| `NLS.ZakharovShabat.ResolventEstimates` | Reciprocal symbols in the conjugate space; scalar and pair `FL^p → FL^1` maps and Hölder bounds; the endpoint bound `1 / abs(Im z)` for `p=1` |
| `NLS.ZakharovShabat.PerturbedResolvent` | Potential/free-resolvent composition; explicit Neumann condition; convergent geometric correction; factorization and both inverse identities; domain and base-space norm bounds; compactness; an admissible parameter for every `l1` potential |
| `NLS.SequenceSpaces.DominatedConvergence` | Coordinatewise convergence plus an `lp` majorant implies norm convergence at finite Banach exponents, along arbitrary filters |
| `NLS.ZakharovShabat.UniformResolvent` | Explicit reciprocal envelopes; convergence of their conjugate norms; Fourier recentering; bounds uniform in real parts and bounded potential sets; existence of a compact two-sided inverse for every finite-p potential |
| `NLS.ZakharovShabat.ClosedOperator` | Partial linear map on the base space; exact one-derivative domain; agreement with the domain-to-base operator; dense domain; closed graph via a bounded inverse; stability under base-norm graph limits |
| `NLS.ZakharovShabat.ResolventAnalytic` | Full resolvent set and joint open domain; potential dependence in operator norm; totalized inverse with both identities; nonempty resolvent set; agreement with Neumann construction; joint complex analyticity; compactness on the full resolvent set |
| `NLS.FunctionalAnalysis.CompactSpectrum` | Riesz-lemma proof of finiteness of compact-operator eigenvalues and spectral values away from zero; finite-dimensional nonzero eigenspaces, without self-adjointness |
| `NLS.ZakharovShabat.PeriodicSpectrum` | Closed periodic spectrum; spectral transformation through a compact resolvent; finiteness in every bounded region; discrete subspace topology; equivalence with domain eigenvalues; finite geometric multiplicities |
| `NLS.ZakharovShabat.ResolventCalculus` | General inverse difference identities; resolvent commutation; potential differences; joint Fréchet derivatives into the domain and base space; spectral and potential derivative formulas; compatibility with the free resolvent and the pre-Neumann identity |
| `NLS.FunctionalAnalysis.CompactGeneralized` | Compact shifted powers after removal of the constant term; finite-dimensional generalized eigenspaces at nonzero values; Riesz-lemma stabilization; finite-dimensional full generalized eigenspaces |
| `NLS.ZakharovShabat.RootSpaces` | Domain-aware recursive periodic root spaces; reference-independent definition; bounded compact-pencil representation; finite-dimensional closed full root spaces; finite stabilization; algebraic multiplicity and its spectral characterization |
| `NLS.FunctionalAnalysis.CompactDecomposition` | Fredholm bijectivity for injective compact perturbations of a nonzero scalar identity; topological kernel/range decomposition at a stabilized exponent; commutation of projections with maps preserving both summands |
| `NLS.ZakharovShabat.SpectralProjections` | Bounded finite-rank periodic root-space projections; independence of the reference resolvent parameter; idempotence and resolvent commutation; rank equals algebraic multiplicity; compactness; unique topological decomposition; vanishing exactly on the resolvent set |
| `NLS.ZakharovShabat.SpectralClusters` | Reciprocal resolvent representation of full root spaces; disjointness at distinct parameters; projection annihilation and commutation; finite cluster spaces and compact projections; range and kernel formulas; additive algebraic multiplicities; composition by intersection; unique cluster/complement decomposition |
| `NLS.FunctionalAnalysis.CircleIntegral` | Bounded linear maps and evaluation commute with Banach-valued circle integrals; interchange of continuous double circle integrals |
| `NLS.ZakharovShabat.ResolventContour` | Normalized resolvent circle integrals into the base space and domain; circle integrability, factorization, compactness, norm bound; Cauchy vanishing and annulus deformation; root-chain integral formula; inside/outside action on full root spaces; resolvent and projection commutation; finite-cluster selection |
| `NLS.ZakharovShabat.ContourProjection` | Existence of resolvent annuli; nested-circle product law; idempotence, finite rank, and topological range/kernel decomposition of the contour operator |
| `NLS.ZakharovShabat.ContourSpectrum` | Finite enclosed spectrum; identification of the whole contour range with enclosed root spaces; equality with the algebraic cluster projection; algebraic-multiplicity rank formula; kernel formula; equality for circles with the same enclosed spectrum; isolated-value projections |

## Current mathematical milestone

For every `1 ≤ p < ∞`, we have constructed the coefficient-space operator

`operator hp φ : Domain p →L[ℂ] PairSpace p`

with `Domain p = ScalarDomain p × ScalarDomain p` and
`ScalarDomain p = WeightedCoeff (Weight.sobolev 1) p`. The domain inclusion is
injective, contractive, and has dense range. With the maximum norm on pairs,

`‖operator hp φ f‖ ≤ (π + C_p * ‖φ‖) * ‖f‖`.

Here `C_p` is the norm of the reciprocal weight in the Hölder conjugate space.
Potential multiplication is the previously proved convolution construction,
which establishes the coefficient estimate underlying Appendix A, Lemma A.8.

Both scalar components use modes `exp(i π n x)` on the period-two circle.
Differentiation has symbol `i π n`; the free operator therefore has symbols
`-π n` and `+π n`. The dissertation's signed modes use scalar frequencies `-n`
and `n`, respectively. Their included vectors are proved nonzero and satisfy
`L₀ eₙ⁻ = π n eₙ⁻` and `L₀ eₙ⁺ = π n eₙ⁺`.

The domain and operator follow Chapter 1, §3, printed page 23; the signed-mode
convention follows §2, equation (1.2). The spectral pencil is explicitly a map
from the domain to the base space. The unbounded realization is now proved
closed, as detailed below. The physical Fourier/distribution realization remains
unproved.
The dissertation's pair norm is not used for these numerical bounds; its
comparison with the chosen maximum norm is a separate proof obligation.

For every `1 ≤ p ≤ ∞` and every `z ∉ πℤ`, the free equation is now a
continuous linear equivalence between the one-derivative domain and base space.
The inverse `freeResolventToDomain z hz` satisfies both inverse identities.
Writing `δ(z) = dist(z, πℤ) > 0`, we prove

- `‖freeResolvent z hz‖ ≤ 1 / δ(z)` on the base space;
- `‖freeResolventToDomain z hz‖ ≤ 1 / δ(z) + (1 + ‖z‖ / δ(z)) / π`;
- `R₀(z) - R₀(w) = (w - z) R₀(z) R₀(w)`;
- compactness of `freeResolvent z hz` on the base space.

The compactness proof constructs finite Fourier cutoffs and proves convergence
in operator norm from uniform decay of the reciprocal symbol. This establishes
the coefficient-space content of Chapter 1, Lemma 3.2(i), printed page 24, and
extends it to all Banach exponents. It does not assert compactness of the inverse
as a map into the stronger domain norm.

For finite `p≥1`, the free resolvent now also maps into `FL^1`. Let `B_p(z)` be
`freeL1Bound p hp z hz`: the maximum of the conjugate-space norms of the two
reciprocal symbols. These are finite by the reciprocal Sobolev-weight estimate.
Hölder and convolution give

`‖Φ R₀(z)‖ ≤ B_p(z) * ‖φ‖`.

Under the explicit sufficient condition `B_p(z) * ‖φ‖ < 1`, the geometric series
converges in operator norm and defines the correction `Q = (1 - Φ R₀(z))⁻¹`.
We prove the factorization `z - L(φ) = (1 - Φ R₀(z)) (z - L₀)` and construct
`Rφ = R₀(z) Q`, with both inverse identities on their correctly typed spaces.
The inverse takes values in the one-derivative domain, is compact on the base
space, and satisfies

`‖Rφ‖ ≤ δ(z)⁻¹ / (1 - B_p(z) * ‖φ‖)`.

This establishes the coefficient-space Neumann construction used before
Corollary 3.3, printed pages 23–24. For `p=1`, `B_1(z) ≤ 1 / |Im z|`, so
`|Im z| > ‖φ‖` suffices. Every `l1` potential therefore has an admissible
parameter; the proof chooses `z = i (‖φ‖ + 1)`.

For every finite `p≥1`, uniform high-imaginary-part regions are now established.
Define `U_p(N)` as the conjugate-space norm of the explicit envelope

`n ↦ min (1 / (N + 1)) (3 / (1 + abs(n)))`.

We prove `U_p(N) → 0` and `B_p(z) ≤ U_p(N)` whenever `abs(Im z) ≥ N + 1`,
uniformly in `Re z`. The proof shifts frequencies by `floor(Re z / π)` and
uses dominated convergence at finite conjugate exponents; the infinite conjugate
exponent uses the uniform height cap directly.

Consequently, every bounded set of potentials has a common height above which
the Neumann condition holds, for both signs of the imaginary part. Every
potential in `PairSpace p`, for any `1 ≤ p < ∞`, has a two-sided inverse into
the one-derivative domain whose base-space realization is compact. The theorem
`exists_compact_inverse` states this without a smallness hypothesis on the
potential.

These are qualitative uniform regions with a concrete envelope, rather than
the sharper numerical rates and vertical-strip bounds in Lemma 3.2(ii–iii).
Those constants remain to be proved. Analytic dependence and spectral
discreteness are now established below.

The actual unbounded realization is now defined as

`unboundedOperator hp φ : PairSpace p →ₗ.[ℂ] PairSpace p`.

Its domain is exactly the range of `domainInclusion`, independently of the
potential, and its evaluation agrees with `operator hp φ`. It is densely defined
and closed for every finite Banach exponent. For any constructed two-sided
inverse `R` at `z`, its graph is characterized by the base-space equation

`domainInclusion (R (z • x - y)) = x`.

Continuity of this equation proves graph closedness. The accompanying limit
lemma shows that if included domain vectors converge to `x` and their operator
images converge to `y`, then `x` has a domain representative with image `y`.
This establishes the coefficient-space closedness assertion on printed page 23.

The full resolvent set `resolventSet hp φ` is now defined by bijectivity of the
spectral pencil, with no exclusion of the free lattice. Normalizing the pencil
by the fixed free inverse at `i` gives an endomorphism of `PairSpace p`;
bijectivity of the pencil is equivalent to invertibility of this endomorphism.
Banach-algebra inversion then defines `resolventToDomain hp φ z` and its included
base-space version `resolvent hp φ z`. Both functions are extended by zero outside
the resolvent set; inverse identities and analyticity are asserted only on it.

The joint domain `{(φ,z) | z ∈ resolventSet hp φ}` is open. On that domain,
the resolvent is jointly complex analytic in `(φ,z)`, in operator norm, both
into the one-derivative domain and into the base space. In particular it is
analytic in `z` for each fixed potential, as in Corollary 3.3, printed page 24.
It agrees with the constructive Neumann inverse wherever the Neumann condition
holds, so every potential has a nonempty resolvent set. The full base-space
resolvent is compact by factoring through the fixed compact free resolvent.
These results establish compactness and analytic dependence throughout the full
coefficient-space resolvent set; the corollary's specific numerical region
remains an open proof obligation.

The periodic coefficient-space spectrum is now defined as the complement of
the full resolvent set. At any fixed resolvent point `w`, we prove, for `z ≠ w`,

`z ∈ periodicSpectrum hp φ ↔ (w-z)⁻¹ ∈ spectrum ℂ (resolvent hp φ w)`.

The generic compact-operator argument is proved using Riesz's lemma on the
successive finite-dimensional spans of eigenvectors. Infinitely many distinct
eigenvalues bounded away from zero would produce bounded vectors whose compact
images stay a fixed distance apart. Together with mathlib's Fredholm alternative,
this gives finiteness of the compact spectrum away from zero, with no
self-adjointness hypothesis. Nonzero compact-operator eigenspaces are also
proved finite dimensional by compactness of their identity map.

The spectral transformation implies that every bounded part of the periodic
spectrum is finite. The spectrum is closed and has the discrete subspace topology;
every spectral point has a nonzero eigenvector in the one-derivative domain.
The domain eigenspaces embed into nonzero eigenspaces of the compact resolvent,
so their geometric multiplicities are finite. This proves the coefficient-space
discreteness conclusion of Corollary 3.3. Generalized eigenspaces and algebraic
multiplicities are now constructed below. Spectral projections and quantitative
localization remain separate proof obligations.

The general inverse difference formula is now proved for simultaneous changes
of potential and spectral parameter. It specializes to

`Rφ(z) - Rφ(w) = (w-z) Rφ(z) Rφ(w)`

and commutation of the resolvents. Varying the potential at a fixed parameter gives

`Rφ(z) - Rψ(z) = Rφ(z) Φ(φ-ψ) R_D,ψ(z)`.

Here `R_D` takes values in the one-derivative domain, so each potential operator
is applied on its actual domain. Differentiating the inverse equations proves
the explicit joint complex Fréchet derivative in operator norm. Applied to an
increment `(δφ,δz)` and a base vector `a`, it is

`Rφ(z) (Φ(δφ) (R_D,φ(z) a)) - δz • Rφ(z) (Rφ(z) a)`.

The domain-valued derivative is proved as well. In particular,
`∂z Rφ(z) = -Rφ(z)²` and `Dφ Rφ(z)[ψ] = Rφ(z) Φ(ψ) R_D,φ(z)`.
These formulas are available through both derivative predicates and mathlib's
`deriv`/`fderiv`. All derivative assertions are restricted to the open full
resolvent domain. The zero-potential inverse agrees with the free inverse, and
the pre-Neumann identity on printed page 23,
`Rφ(z) (I - Φ R₀(z)) = R₀(z)`, now holds whenever both resolvents exist,
without imposing the sufficient Neumann smallness condition.

Periodic root spaces are now defined directly from the unbounded operator:

`G₀(z) = {0}`, `Gₙ₊₁(z) = {domainInclusion f | (z-L)f ∈ Gₙ(z)}`.

The definition enforces one-derivative domain membership at each step, and
contains no choice of reference parameter. Its first level is the included
ordinary eigenspace. For every resolvent point `w`, we prove

`Gₙ(z) = ker (I + (z-w) Rφ(w))ⁿ`.

Equivalently, these are the generalized eigenspaces at `-1` of the compact
operator `(z-w) Rφ(w)`. This representation remains valid at `z=w`.
The full root space is the increasing union of all finite levels.

The generic compact-operator proof establishes finite-dimensional generalized
eigenspaces and finite stabilization at every nonzero value. Finite-level
dimensionality follows by removing the constant term from a shifted operator
power; stabilization follows from Riesz vectors in successive kernels and
compactness. Consequently, each periodic full root space is finite dimensional,
closed in the base space, and reached at a finite level. Its dimension defines
`periodicAlgebraicMultiplicity hp φ z`, which is positive exactly on the periodic
spectrum and zero exactly on the resolvent set.

Bounded projections onto these full root spaces are now constructed. For any
stabilized exponent `n` and resolvent point `w`, the root space and
`range (I + (z-w) Rφ(w))ⁿ` are topologically complementary. The generic proof
compresses a shifted power to an arbitrary complement of its finite-dimensional
kernel, applies the Fredholm alternative, and constructs a bounded projection.
It requires no self-adjointness.

`periodicSpectralProjection hp φ z` has exactly the full root space as its range,
is idempotent and compact, and has rank equal to the algebraic multiplicity.
It commutes with every resolvent. Changing the reference resolvent point gives
the same projection; one stabilized exponent describes its kernel at every such
point. Every base vector has a unique decomposition into a root vector and a
vector in the closed projection kernel. The projection is zero exactly on the
resolvent set.

Distinct full root spaces are now proved disjoint by representing them as
generalized eigenspaces of the same resolvent at distinct reciprocal values.
Any bounded map commuting with that resolvent preserves every full root space.
Consequently, projections at distinct parameters annihilate each other, and
all individual spectral projections commute.

For a finite set `s` of parameters, `periodicClusterSpace hp φ s` is the sum of
the associated root spaces and `periodicClusterProjection hp φ s` is the sum of
their projections. We prove that it is bounded, idempotent, and compact, has
exactly the cluster space as its range, and has kernel equal to the intersection
of the individual kernels. It commutes with every resolvent, and its rank is
`∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z`. Cluster and kernel form a
topological direct sum with unique decomposition of every base vector.
Multiplying cluster projections selects their intersection; disjoint clusters
therefore have annihilating projections. Parameters in the resolvent set
contribute zero, so no separate spectral-membership assumption is needed.

The actual normalized circle integral is now defined as

`resolventCircleIntegral hp φ c r = (2πi)⁻¹ • ∮ ζ in C(c,r), Rφ(ζ)`.

For a nonnegative-radius circle contained in the resolvent set, circle
integrability is proved in operator norm. A second integral valued in the
one-derivative domain gives a bounded factorization through `domainInclusion`,
which also proves compactness. A uniform bound `M` on the resolvent along the
circle gives the bound `r*M` on the normalized integral. The contour operator
vanishes if the closed disk is contained in the resolvent set; changing the
radius through a closed annulus of resolvent points leaves it unchanged.

The root-chain recurrence gives a weighted integral formula for every finite
root space: all higher pole terms integrate to zero, leaving the simple-pole
term. Consequently the contour operator fixes full root vectors at values
inside the circle and annihilates those outside the closed disk. It commutes
with every resolvent and every individual algebraic spectral projection. For
any finite parameter set `s`, its product with `periodicClusterProjection s` is
the cluster projection filtered to the open disk. Boundary parameters are
resolvent points and have zero algebraic projection.

The Cauchy–Riesz projection properties from Section 3, equation (1.4), are now
proved. For two concentric resolvent circles with `0 ≤ r < R`, the product of
their contour operators is the inner operator. The proof exchanges circle
integrals of a continuous function on the product of circles and uses the
resolvent identity plus the scalar Cauchy integral formulas. The annulus between
the two circles need not be free of spectrum for this product law.

Every resolvent circle has a slightly larger resolvent annulus, using local
spectral finiteness and a positive radial gap. Radius deformation then proves
idempotence. Its range is the eigenspace at one of a compact operator and is
therefore finite dimensional; range and kernel form a topological direct sum.

`enclosedPeriodicSpectrum hp φ c r` is the finite set of spectral values in the
open disk. The finite-dimensional contour range is invariant under any reference
resolvent, so its restriction decomposes into generalized eigenspaces over `ℂ`.
Injectivity excludes a generalized eigenvalue at zero. The reciprocal spectral
transformation and contour selection law identify the range with the sum of
the enclosed periodic root spaces. Consequently the contour integral equals
`periodicClusterProjection hp φ (enclosedPeriodicSpectrum hp φ c r)` as a bounded
operator on the entire base space. Its rank is the sum of enclosed algebraic
multiplicities, and its kernel is the intersection of the corresponding
individual projection kernels. Circles with the same enclosed spectral values
give equal operators, even with different centers; an isolated single value
gives its individual root-space projection.

Analytic dependence on the potential for fixed contours, local constancy of
projection rank, and agreement of multiplicities with characteristic-function
zero orders remain to be proved.

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 740 declarations under `NLS`, including generated
definitions and instances. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.

The examples exercise multiplication at `p=1,2,3`, convolution and differentiation
at `p=∞`, domain density at `p=1`, the operator bound at `p=3`, the frequency-shift
sign, both signed free spectral equations, and nonzero off-diagonal coupling.
Resolvent checks use the concrete parameter `z=i`, exercise both inverse identities,
the bounds, compactness at `p=1,3,∞`, cutoff convergence, signed-mode denominators,
and the resolvent identity. Perturbation checks cover the Hölder and convolution
bounds at `p=3`, convergence of the Neumann series, and a concrete nonzero
potential with both entries equal to one at `z=2i`: both inverse identities,
compactness, and the norm bound are checked. Uniform-estimate checks exercise
`p=1,3`, a parameter with a far-negative real part, one height for a whole norm
ball, and compact inverse existence for an arbitrary `p=3` potential. Closed-operator
checks cover `p=1,3`, domain density, evaluation on included vectors, and preservation
of the graph under sequential base-norm limits. Analytic-resolvent checks cover
`p=1,3`, the open joint domain, nonempty resolvent sets, joint and separate
analyticity, both full inverse identities, compactness, and agreement with the
concrete nonzero Neumann example at `z=2i`. Spectral checks cover `p=1,3`,
finiteness in balls and arbitrary bounded sets, the discrete topology, domain
eigenvectors, finite geometric multiplicity, the free Fourier eigenvalues, and
the spectral transformation at the nonzero test potential. Calculus checks
cover `p=1,3`, general differences, commutation, joint derivatives into both
spaces, the potential derivative, the spectral derivative sign on the zero
Fourier mode at `z=i`, and the pre-Neumann identity for the nonzero potential.
Root-space checks cover `p=1,3`, finite stabilization, finite dimensionality,
compatibility with ordinary eigenspaces, the bounded representation for arbitrary
reference points, positive/zero algebraic multiplicity, and a two-dimensional
Jordan block distinguishing generalized from ordinary eigenvectors. Projection
checks cover `p=1,3`, the unique decomposition, idempotence, rank, compactness,
resolvent commutation, one kernel exponent for all reference points, a fixed
signed free eigenmode, vanishing at the nonzero test potential's resolvent point,
and the generalized kernel/range decomposition of a Jordan block. Cluster
checks cover `p=1,3`, the reciprocal representation, disjoint root spaces,
annihilation, idempotence, unique decomposition, kernel intersections, compactness,
rank additivity, the intersection of two overlapping clusters, and the preservation
or annihilation of actual free Fourier modes. Contour checks cover `p=1,3`,
domain factorization, compactness, commutation, norm bounds, vanishing on
resolvent disks, annulus deformation, generalized root vectors, and selection
within finite clusters. A circle of radius `π/2` about zero is explicitly proved
to avoid the free lattice; its normalized integral fixes the constant free mode
and kills the mode at `π`, checking both the orientation and the inside/outside
selection. Further contour checks cover nested-circle products, idempotence,
finite rank, whole-space equality with the enclosed cluster projection, and the
rank and kernel formulas. The explicit free circle of radius `π/2` is proved to
enclose exactly zero, and its entire contour operator equals the individual
projection at zero. No admission or extra project axiom is used by the library.

## Next milestones

1. Prove analytic dependence on the potential for fixed contours and local
   constancy of the resulting finite projection ranks.
2. Prove the sharper numerical rates and vertical-strip estimates from Lemma
   3.2(ii–iii), then develop spectral localization.
3. Prove the periodic Fourier/distribution realization, period-one embedding,
   pair-norm comparison, and compatibility with physical-space multiplication.

Spectral localization, classical Birkhoff prerequisites, and the main dissertation
theorems remain unimplemented. Further sequence-space work includes
symmetric cutoff convenience functions, embeddings between regularities, and the full
range of Young inequalities beyond the `l1`-factor case.
