# Implementation plan

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

## Immediate next proof targets

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
