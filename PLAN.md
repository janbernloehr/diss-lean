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
throughout this complement. Next prove joint analyticity in the source
coefficients and spectral variable, then the cross-disc estimates and
contour identity.
The printed general-`p` central-height constant remains a separate open item.
