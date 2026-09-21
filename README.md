# dNLS in Lean

Formalization of mathematics supporting Jan Molnar's *Features of the Nonlinear
Fourier Transform for the dNLS Equation* (2016).

Source: <https://janbernloehr.de/Download/fs16/diss.pdf>

The library currently proves sequence-space foundations, the full discrete
Young convolution inequality, the mixed three-sequence inequality, and the
canonical periodic-distribution product (Appendices B.2, B.3, and A.7). It also
proves a closed, densely defined coefficient-space Zakharov–Shabat
operator with norm bounds and signed free Fourier modes. The free resolvent is
constructed away from `πℤ`, with both inverse identities, explicit bounds, and
compactness proved by finite Fourier approximation. For nonzero potentials,
Hölder estimates yield a Neumann-series resolvent under an explicit smallness
condition, with both inverse identities and compactness. Uniform estimates now
prove that every potential at every finite Banach exponent has an admissible
parameter; one height works for any fixed norm ball of potentials. The full
resolvent set is open, and the resolvent is compact and jointly complex analytic
in the potential and spectral parameter throughout its domain. The periodic
spectrum is closed and discrete, with finitely many eigenvalues in every bounded
region. Full periodic root spaces stabilize and have finite dimension, defining
algebraic multiplicities that are positive exactly on the spectrum. Bounded
finite-rank projections onto these root spaces commute with every resolvent,
give topological direct-sum decompositions, and have rank equal to algebraic
multiplicity. Projections at distinct parameters annihilate each other. Their
finite sums project onto finite spectral clusters, with rank equal to the sum
of algebraic multiplicities and composition given by intersection of clusters.
The normalized circle integral of the resolvent is constructed in operator norm,
factors through the operator domain, and is a compact finite-rank projection.
It equals the algebraic projection onto all enclosed root spaces, with rank
equal to their total algebraic multiplicity. For a fixed resolvent circle, these
projections depend analytically on the potential and have locally constant rank.
General resolvent identities and explicit spectral and potential derivatives
are also proved in
operator norm. Appendix B.1's quantitative reciprocal-series inequalities,
including explicit tail and lattice bounds, are also proved. These give the
numerical height-decay and punctured-strip bounds in Lemma 3.2(ii–iii),
the explicit compact analytic resolvent region of Corollary 3.3, and uniform
spectral disk localization for sufficiently small potentials. The double-resolvent
operator and squared Neumann inversion are constructed, including both inverse
identities and quantitative bounds. One-sided potentials have exact two-term
resolvents even when the original Neumann condition fails. Lemma 3.4's
frequency-tail estimate is proved with the explicit constant `32p²` in the
maximum pair norm, giving further punctured-strip and spectral-circle criteria.
Corollary 3.5 now localizes the spectrum of every potential to a central box
and the remaining quarter-pi disks, uniformly on an open convex neighborhood
containing both that potential and zero. The exterior resolvent is compact
and analytic. Closed complementary even/odd Fourier subspaces and their
invariance under even-supported potentials are also proved (Lemma 3.6),
including preservation by the full resolvent and spectral circle projections.
The high-frequency disk count in Proposition 1.1(i) is proved: each sufficiently
far disk has total algebraic multiplicity two, uniformly on such a neighborhood.
For even-supported potentials, each such disk’s entire generalized eigenspace
has the parity of its index, and its contour projection annihilates the opposite
parity. All four edges of every sufficiently large central rectangle are now
uniformly in the resolvent set. The finite central spectral projection is
constructed algebraically. It equals a large-circle projection and depends
analytically on the potential; its rank and central algebraic multiplicity are
`4N+2`, uniformly for every sufficiently large cutoff. For even-supported
potentials, the cutoff’s parity contributes `2N+2` and the other parity `2N`;
both parity-component projections are analytic on the same neighborhood.
All localization and counting conclusions now use one cutoff and one open
convex neighborhood, valid for every larger cutoff. Each noncentral spectral
value has a unique high-disk index; each disk supplies an eigenvalue pair,
allowing a repeated double value. The central box uses Corollary 3.5's height-`N`
convention. For real-type potentials, every periodic spectral value is now
proved real at every finite Banach exponent, using absolutely convergent
coefficient duality and convolution symmetry. Every nonreal parameter therefore
lies in the resolvent set. The analytic reduction needed for Lemma 3.7 is also
constructed: explicit invertible transport identifies nearby spectral ranges,
and the domain-valued contour projection makes `L P_D` bounded and analytic.
The transported operator acts on one fixed finite-dimensional space and
intertwines with the actual spectral restriction. Lemma 3.7 is now proved:
the first and second traces give the actual eigenvalue midpoint and squared
gap, analytic on the common potential neighborhood for all high-frequency disks.
The proof includes repeated eigenvalues and nontrivial Jordan blocks, without
choosing analytic branches of individual eigenvalues.
Section 4's Dirichlet and Neumann coefficient spaces are now constructed as
closed complementary subspaces, including their weighted domains and contractive
projections. The operator preserves both spaces for already-reflected potentials;
its bounded restrictions and the exact signed free-mode and potential-action
formulas are proved. Identification of the weighted domains with physical
boundary conditions and the interval-extension estimates at general exponents
remain open.
Both boundary restrictions now have full compact resolvents, jointly analytic
on their own open domains. Their spectra are closed and discrete, with finite
bounded portions and an eigenvector characterization. The periodic spectrum is
exactly their union. Periodic resolvents and circle projections preserve both
boundary spaces. Domain-aware boundary root spaces are finite dimensional and
stabilize, and periodic algebraic multiplicity is the sum of the two boundary
multiplicities. Each free boundary eigenvalue has multiplicity one; the free
central count is `2N+1` for each boundary condition. The coefficient counting
argument of Theorem 1.4 is now proved for reflected nonzero potentials: on one
common neighborhood and for every sufficiently large cutoff, each high disk has
one simple Dirichlet and one simple Neumann eigenvalue, and each central count
is `2N+1`. Boundary cluster and contour ranks count the actual restricted root
spaces, including Jordan chains. The projectors are analytic on that same
neighborhood. Lemma 4.5's coefficient statement is now proved: the boundary
projectors lift analytically into the weighted boundary domains, and the trace
of the bounded restriction defines each high-index simple eigenvalue. Both
functions are analytic on one open convex neighborhood in the reflected
potential space, with the same cutoff and counting data.
The physical reflected interval extensions are now defined, and their normalized
Fourier integrals are computed for continuous input and finite Fourier polynomials.
Finite input gives actual elements of both boundary coefficient spaces for `p>1`,
with an explicit reciprocal kernel bound. A one-sided constant proves failure at
`p=1`. The integrals also detect missing normalization factors in the calculation
on printed page 31: the even coefficient carries `1/2`, and the odd kernel carries
`i/π`. Parseval now gives the uniform `p=2` estimate and completion to all
Hilbert coefficient pairs: the squared output norm is the mean of the two
input energies. The extension is injective, contractive in the maximum pair
norm, and boundary-valued. Its odd coefficients define a bounded shifted
Hilbert transform with the exact finite-input kernel. The ordinary and shifted
Hilbert kernels now also have bounded extensions on all `ℓ4`: a summable kernel
correction gives the ordinary `ℓ2` operator, and the discrete Cotlar identity
with Hölder proves a uniform quartic bound. The general exponent-doubling theorem
now iterates this argument to construct both transforms at every `p=2^(n+1)`,
with explicit bounds and exact finite-input formulas. Duality transfers the
ordinary bounds unchanged to conjugate exponents, constructing both transforms
at `2, 4/3, 8/7, …`, with exponents arbitrarily close to one. The transposition
identity holds on all conjugate inputs. Finite analytic power families and
mathlib's three-lines theorem now interpolate between proved endpoints, giving
ordinary and shifted Hilbert transforms for every `1<p<∞`. Their reciprocal
series converge absolutely and give the coefficients on all inputs. Even/odd
insertion now assembles the bounded half-interval map. Signed reflection gives
unique bounded, analytic Dirichlet and Neumann interval extensions for every
`1<p<∞`, proving the coefficient form of Lemma 4.3. They agree with physical
Fourier integrals on finite polynomials and with the Parseval map at `p=2`.
Absolutely summable Fourier series now give continuous period-two functions with
exactly the prescribed normalized interval integrals. Every one-derivative
coefficient domain at finite `p` has a unique continuous representative, with
uniform bound `2p`, uniform finite approximation, and bounded endpoint traces.
Reflection agrees with `x ↦ 2-x`, and odd reflection symmetry gives zero endpoint
values. At `p=2` the representative agrees with the normalized `L²` Fourier
inverse. Its Fourier derivative now has a square-integrable physical realization:
integrating it recovers the function's increment. The representative is absolutely
continuous, its classical derivative agrees almost everywhere with that realization,
and the derivative's Fourier integrals recover the symbol `iπn`. Conversely,
complex integration by parts and Parseval recover weighted coefficients from any
classical periodic `H¹` function. Both reconstruction identities are proved, giving
a characterization by unique weighted Fourier representatives. The general derivative
formula retains the endpoint jump for nonperiodic input. Classical `H¹[0,1]`
Dirichlet and Neumann pairs now extend into the actual weighted boundary domains:
matching endpoints make the signed component-swap fold absolutely continuous,
with a square-integrable reflected derivative. Synthesis recovers the physical
extension on `[0,2]` and the original pair on `[0,1]`, including all endpoints.
Conversely, every weighted boundary pair restricts to the original classical
endpoint domain, and extending that restriction recovers the pair. Each classical
interval pair has a unique weighted boundary representative; equality depends
only on values on `[0,1]`. The physical Sobolev energy now satisfies exact Parseval
and reflection identities. The standard interval pair norm obeys
`‖extension f‖ ≤ ‖f‖H¹ ≤ √2 π ‖extension f‖`, with the length-two normalization
and derivative factor `π` retained. Lemma 4.2 is now bundled as a continuous
linear equivalence from each original interval domain, carrying exactly this
physical `H¹` norm, onto its weighted boundary domain. Both interval spaces are
complete. The inverse evaluates the physical representative on `[0,1]`.
At the Hilbert exponent, `ℓ2 × ℓ1` convolution now equals actual physical
multiplication. The full coefficient operator agrees almost everywhere with
`diag(i,-i)∂ₓ + [[0,φ₋],[φ₊,0]]` for arbitrary `L²` potentials, and the physical
and coefficient eigen-equations are equivalent on a full period. Lemma 4.1 now
transfers both original classical boundary eigenfunctions through signed
reflection, using the Dirichlet extension of the potential in both cases.
Restriction proves the converse: the independently defined original classical
eigenvalue sets equal the coefficient boundary spectra. They are closed,
discrete, finite in bounded regions, and their union is the periodic spectrum
of the reflected potential. For the zero potential both sets are exactly `πℤ`.
Original potentials now form the actual complete component-sum `L²[0,1]` space.
Their Dirichlet Fourier extension is bounded, injective, and complex analytic,
with exact norm factor `√2/2` into the maximum coefficient-pair norm. The
high-index eigenvalue branches are analytic on one open convex physical
neighborhood with one cutoff for both boundary conditions. Each high disk
contains exactly that original classical eigenvalue.
Both signed extensions are now continuous linear isomorphisms from the full
physical `L²` space onto their coefficient boundary spaces, with exact inverse
norm factor `√2`. Their inverses are actual interval restrictions, and their
base coefficients agree with classical `H¹` extension followed by inclusion.
The original unbounded interval operator is now constructed on physical `L²`,
with exactly the classical endpoint domain and the actual differential action.
It is closed and densely defined. Its physical pencil has the same resolvent
set as the coefficient boundary pencil, with a bounded inverse and compact
base-space resolvent. The physical spectrum equals the original classical
eigenvalue set.
Physical root spaces are now defined using the original pencil and domain at
every chain level. They are finite dimensional, stabilize, and correspond to
the coefficient root spaces. Physical algebraic multiplicities therefore agree.
One common physical neighborhood gives central count `2N+1`, one algebraically
simple eigenvalue in each high disk, and no other spectrum, for both boundary
conditions and every larger cutoff. The full coefficient operator now realizes
the actual distributional differential expression, using the unique continuous
extension of smooth potential multiplication to the Fourier domain.
The actual rectangular resolvent integral now uses four oriented Bochner edge
integrals. It factors through the domain, is compact, and commutes with
resolvents and algebraic projections. Subdivision and Cauchy's theorem prove
invariance when an edge moves through a resolvent strip. The central corners
and boundary agree exactly with the existing box. Scalar residue formulas now
prove selection of full generalized eigenspaces and every finite spectral
cluster, and the central rectangular integral fixes the central algebraic
projection. Mixed rectangular/circular integration now controls the whole
space and proves equality with the central spectral projection. The actual
rectangular integral is idempotent, has exactly the central generalized-eigenspace
range, and is analytic with rank `4N+2` on one common counting neighborhood.
Explicit bounds now place the resolvent on and above height `(1+8pM)^p`
for every finite exponent and every potential of norm at most `M`. At `p=2`,
the smaller printed height `(1+8M)^2` also works. One common neighborhood gives
central algebraic count `4N+2` in each potential's Hilbert norm-height box,
with its cluster projection equal to the existing rectangular integral.
These use coefficient maximum pair norms. The printed general-`p` height
`(1+8‖φ‖ₚ)^p` still needs an additional argument: direct substitution into the
proved `4p` Neumann estimate is insufficient. The actual contour formula now
holds for every ordered rectangle with resolvent boundary, with its whole
range and rank identified. In particular, contours at the printed Hilbert
height and the proved all-exponent height equal the fixed central projection
and are analytic with rank `4N+2`. This even holds for discontinuous choices
of uniformly bounded sufficient heights. The finite-exponent component-sum
pair norm is now implemented exactly, including all real Sobolev weights.
Its continuous linear equivalence with the maximum norm has sharp reverse
factor `2^(1/p)`. The proved heights and analytic contour neighborhoods now
transfer to this actual source-norm parameter space. The separate infinity
norm and full weighted distributional realization are now implemented below.
The main dissertation theorems remain future work. The canonical period-one
coefficient embedding is now an isometry onto the even subspace and commutes with convolution. Actual integrable
period-one functions have exactly the inserted period-two Fourier integrals,
with their coefficient norm preserved. Absolutely summable data has an
injective continuous period-one realization. The pair embedding covers exactly
the even potentials and supplies the existing resolvent parity hypotheses;
arbitrary Banach `ℓᵖ` data now has an injective continuous linear realization
as actual tempered distributions. Schwartz tests recover each coefficient, and
finite Fourier sums converge distributionally even at `p=∞`. Period one is
equivalent to even Fourier support; for `ℓ¹` input this agrees with integration
against the continuous synthesis. The multiplier `iπn` now agrees with actual
distributional differentiation, with an exact characterization of the scalar
and signed-pair free operator domains. Their graphs are closed even at `p=∞`,
and finite-exponent continuous representatives satisfy weak integration by parts.
Potential multiplication now agrees with actual smooth distribution multiplication
and extends uniquely to `ℓ¹` multiplier data by continuity. Its action uses
absolutely convergent sums of real-line integrals against the continuous domain
representative. The full signed derivative plus off-diagonal product, including
its eigenvalue equations, agrees with the existing coefficient operator.
Schwartz periodization is now a continuous map to the period-two circle, proved
to equal the absolutely convergent sum of physical translates. Poisson summation
gives its exact half-integer Fourier samples, including the normalization factor
one half. Explicit Schwartz lifts cover all Fourier polynomials, and their
periodizations are dense in the uniform norm. The kernel is exactly the common
annihilator of all synthesized distributions at each Banach exponent.
Periodization now commutes with classical differentiation of every order.
Each derivative is a continuous circle-valued linear image of the original
Schwartz test, and the same Fourier truncations converge uniformly in every
fixed derivative order. These bounds prove that periodizations are genuine
smooth multipliers of Schwartz space. A finite Leibniz estimate now upgrades
uniform convergence of every multiplier derivative to convergence in every
weighted Schwartz seminorm after fixing any Schwartz window. Windowed Fourier
series therefore converge in genuine Schwartz space, and every tempered
distribution acts on them through an absolutely convergent scalar series.
The converse is now proved for every Banach `ℓᵖ` class, including infinity:
an arbitrary period-two tempered distribution has a unique synthesis
representation exactly when its coefficient-test values belong to `ℓᵖ`.
A direct Schwartz-series construction and summable translated-product estimates
prove that every periodic distribution annihilates the periodization kernel.
Normalized window reconstruction then gives an absolutely convergent Fourier
formula and coefficient uniqueness, without assuming the distribution came from
synthesis. This realization now extends to every positive weight with a
polynomially bounded reciprocal, including every real Sobolev exponent. Weighted
sampling is continuous into `ℓ¹`; the raw coefficients give an absolutely
convergent action independent of the weight and exponent. Intrinsic weighted
coefficient regularity is equivalent to unique weighted synthesis, and finite
Fourier truncations converge distributionally even at negative regularity and
`p=∞`.
Monotone Sobolev embeddings now preserve this actual distribution and decrease
the coefficient norm. At every real regularity `s`, differentiation is bounded
from `FL^{s+1,p}` to `FL^{s,p}` with constant `π`. Its actual distributional graph
is closed and has exactly that domain, including infinity. Intrinsically, a
periodic distribution and its derivative both lie in regularity `s` exactly
when the distribution lies in regularity `s+1`.
The source's infinity pair norm is now implemented as the supremum of the
frequencywise component sum, with a complete complex normed space for every
positive weight and exact real Sobolev formulas. Its comparison with the
maximum pair norm has sharp factor two. Signed pair coordinates and scalar
Fourier coordinates are related explicitly by reflection of the first
component, as in (1.2). The weighted endpoint space synthesizes injectively
into actual periodic distribution pairs, with the exact source norm recovered
from their coefficients and a unique representation for every endpoint pair.
Exponent embeddings now preserve the same actual distribution. Increasing
sequence exponent is contractive, including the infinity target and all real
Sobolev regularities. A weight ratio in `ℓʳ` gives a bounded embedding when
`1/q = 1/p + 1/r`, with its explicit Hölder norm as constant. For Sobolev
weights the finite-`r` reciprocal is summable exactly when `(s-t)r > 1`.
This estimate now composes with the physical interval regularity bridge to
prove Appendix A.9's Fourier-Lebesgue membership range for every positive period,
including the zero- and half-regularity conclusions.
Appendix B.2 is now proved for every Banach exponent triple satisfying
`1 + 1/r = 1/p + 1/q`, including all infinity endpoints. Convolution is
absolutely convergent at every frequency, belongs to `ℓʳ`, and satisfies the
printed norm bound with constant one. Its continuous bilinear map has norm
exactly one, agrees with the earlier `ℓ¹`-factor construction, and is commutative.
Finite cutoffs of finite-exponent inputs converge in the full output norm,
even when that output norm is `ℓ∞`.
Lean and mathlib are pinned to **v4.33.1**; `lake-manifest.json` records the resolved
dependency commits.

## Build

With a standard elan installation:

```sh
lake exe cache get
lake build
```

In the original Codex workspace, use the locally installed toolchain:

```sh
./scripts/lake.sh build
```

For the build, public-API examples, and a transitive axiom audit:

```sh
./scripts/check.sh
```

The audit rejects admitted proofs and additional mathematical axioms in every
declaration under `NLS`, including definitions and instances.

The examples check multiplication at `p = 1, 2, 3`, convolution and differentiation
at `p = ∞`, domain density, operator bounds, Fourier signs, both signed free
spectral equations, and nonzero off-diagonal potential coupling. Resolvent checks
cover inverse identities, bounds, signed modes, operator-norm cutoff convergence,
the resolvent identity, and compactness at `p = 1, 3, ∞`. Perturbation checks
include convergent Neumann series and the concrete nonzero potential `(1,1)`
at `z = 2i`, with inverse identities, compactness, and a resolvent norm bound.
Uniform-estimate checks cover `p = 1, 3`, Fourier recentering at a negative real
part, bounded potential sets, and compact inverse existence for arbitrary `p=3`
potentials. Closed-operator checks verify the actual partial-map realization at
`p = 1, 3`, its dense domain, evaluation, and stability under graph limits.
Analytic-resolvent checks cover the full inverse identities, openness, joint
analyticity, compactness, and agreement with the nonzero Neumann example.
Spectral checks cover discreteness, finiteness in bounded sets, finite-dimensional
eigenspaces, the free Fourier eigenvalues, and the reciprocal spectral transformation.
Calculus checks cover general resolvent identities, joint derivatives, potential
variations, and a concrete spectral-derivative sign check at `z=i`. Root-space
checks cover stabilization, finite dimensionality, algebraic multiplicities, and
a Jordan block with a nontrivial generalized eigenvector. Projection checks
cover decomposition, idempotence, rank, compactness, resolvent commutation,
reference-independent kernels, fixed free eigenmodes, and vanishing at a
verified resolvent point of a nonzero potential. Cluster checks cover distinct
root spaces, annihilation, finite-sum ranks, kernel intersections, compactness,
overlapping clusters, and included/excluded free Fourier modes. Contour checks
cover domain factorization, compactness, resolvent commutation, norm bounds,
Cauchy's theorem on resolvent disks, annulus deformation, generalized root spaces,
finite-cluster selection, nested-circle products, idempotence, finite rank,
whole-space identification, the rank and kernel formulas, and an explicit free
circle of radius `π/2` whose integral equals the individual projection at zero.
Squared-Neumann checks include both Fourier coefficient signs and a one-sided
potential at `z=i` whose perturbation norm is at least two but whose square
vanishes, verifying failure of the original condition and validity of the new inverse.
Frequency-tail checks exercise cutoff boundaries, both frequency signs, `p=1,3`,
and admissible circles about `±200π` for the two-sided constant potential `(1,1)`,
which fails the earlier small-potential strip condition. Localization checks
also exercise both central-box boundary conventions, common cutoffs along
`[0,φ]`, and the full neighborhood result at the `p=1` endpoint. Parity checks
include negative frequencies, nonconstant even potentials, resolvent and contour
preservation, and a counterexample when the even-support hypothesis is omitted.
Central-region checks cover horizontal edges, a negative corner, the degenerate
zero-height boundary, every larger cutoff, signed free endpoints, and free
central ranks at both even and odd cutoffs. Deformation checks distinguish
spectral selection from geometric containment, exercise negative endpoint and
excluded disks, and verify the central count along the entire segment `[0,φ]`.
Central parity checks cover zero, even, and odd cutoffs, negative residue
representatives, nonconstant even potentials, and addition to the total count.
Unified counting checks cover unique disk assignment, repeated and distinct
value alternatives, spectral membership, and common cutoffs and analytic domains.
Real-type checks cover conjugate frequency reversal, nonconstant complex-amplitude
potentials at `p=3`, the `p=1` endpoint, positive energy, and an imaginary
constant potential with a verified nonreal eigenvalue when real type fails.
Reduction checks use moving nonorthogonal projections, their explicit shear
transport and analytic inverse, compressed identity, a negative free eigenmode,
two-dimensional reference ranges at `p=3`, and domain-norm analyticity at `p=1`.
Symmetric-eigenvalue checks cover a nontrivial Jordan block, distinct eigenvalues,
negative free indices, the source normalization `γ²/2`, the `p=1` endpoint,
and exclusion of a free eigenvalue outside the selected contour.

Boundary-space checks cover reflection without conjugation, negative Sobolev
regularity at `p=∞`, the complementary decomposition, negative free indices,
and separation of the two boundary conditions. A nonconstant complex potential
has the exact positive Dirichlet and negative Neumann coupling from index `-3`
to `5`. Further checks cover restricted norm bounds, odd-frequency reflected
potentials and projection intertwining at `p=1`, and failure of invariance for
a potential lacking reflection symmetry.

Boundary-resolvent checks distinguish the two spectra for the constant potential
`(1,1)`: `1` is a Dirichlet eigenvalue and a Neumann resolvent point, with a
nonzero Neumann inverse, its inverse identity, compactness, and joint analyticity.
They also verify totalization outside the individual resolvent set, compatibility
with the preceding bounded operator, the spectral union and bounded spectral
finiteness at `p=1`, and boundary preservation by a negative-index circle.

Boundary-root checks construct a nonconstant complex reflected potential with a
length-two Dirichlet Jordan chain at `π`. Its top vector is outside the ordinary
eigenspace, and its algebraic multiplicity is at least two. Free checks cover a
negative Neumann index, absence of longer chains at `p=1`, zero multiplicity at
an off-lattice point, contour rank one at a negative index, and central counts
one and five at cutoffs zero and two. The multiplicity splitting is also
instantiated at the endpoint `p=1`.

Boundary-counting checks use a nonconstant complex reflected potential with
explicit norm `1/1000`; a connected small-potential ball proves rank one for
both boundary components in every disk, including a negative-index multiplicity
count. Its Dirichlet cluster annihilates Neumann input. A restricted cluster fixes
the earlier length-two Jordan-chain vector. Other checks cover empty clusters,
a two-index free cluster, one cutoff for every larger box along the full path
`[0,φ]`, unique simple boundary eigenvalues at `p=1`, and shared analytic projector
neighborhoods at `p=3`. For `(1,1)`, the value `1` belongs to the Dirichlet disk
spectrum but is excluded from the Neumann disk spectrum and contributes rank
zero to the Neumann cluster.

Boundary-eigenvalue checks evaluate the intrinsic trace on nonorthogonal moving
one-dimensional ranges and verify its analyticity. A nonzero imaginary constant
potential has trace-defined Dirichlet value `i/1000` and Neumann value `-i/1000`
in the same disk, using actual domain eigenvectors and an explicit rank-one
deformation. Further checks cover the signed negative free value, exact recovery
of a negative free boundary mode by the domain lift, analyticity into the weighted
boundary domain at `p=1`, shared neighborhoods for both analytic simple eigenvalue
functions at `p=3`, and actual weighted-domain eigenvectors at `p=1`.

The wrapper also works with a standard `lake` on `PATH` when the workspace-local
installation is absent. No shell startup files are modified.

## Design conventions

- `NLS.Coeff p` is mathlib's complex `lp` space indexed by `ℤ`.
- Banach-space results require `[Fact (1 ≤ p)]`. Norm convergence of truncations
  additionally requires `p ≠ ⊤`.
- Finite projections are first defined for arbitrary finite frequency sets.
- Weighted spaces carry the transported `lp` norm topology, not the pointwise
  topology of the underlying raw sequences.
- The original operator spaces use maximum pair norms. `CoeffPair` and
  `WeightedCoeffPair` implement the dissertation's finite-`p` component-sum
  norms, with continuous linear equivalences and sharp factor `2^(1/p)`.
  The spectral-height bounds transfer without increasing their constants.
  `CoeffPairInfty` and `WeightedCoeffPairInfty` implement the distinct infinity
  norm `sup_n w(n)(|a(n)|+|b(n)|)` in signed pair coefficients, with sharp factor
  two. Their `toScalarMax` equivalences reflect the first sequence before
  entering the original scalar-coordinate operator spaces.
- Both scalar components use period-two modes `exp(i π n x)`. The free symbols
  are `-π n` and `+π n`; the signed modes `eₙ⁻` and `eₙ⁺` both have eigenvalue `π n`.
- The operator is a bounded map from the one-derivative domain to the base space.
  The free equation has a bounded inverse into that domain; its base-space
  resolvent is compact. Sufficient conditions for the perturbed inverse are
  `freeL1Bound * ‖φ‖ < 1` or the broader squared criterion `‖(Φ R₀)²‖ < 1`;
  for `p=1`, `|Im z| > ‖φ‖` suffices for the first condition.
  A common high-imaginary-part region is proved for each bounded potential set
  at every finite `p`. The partial-map realization on the base space has exactly
  the included one-derivative domain and is proved closed and densely defined.
  The full resolvent is jointly complex analytic in the potential and parameter
  on an open domain, and compact throughout that domain. Its periodic spectrum
  is closed and discrete, with finite-dimensional stabilized root spaces and
  finite algebraic multiplicities. Bounded root-space projections and their
  complementary decompositions are proved. Resolvent circle integrals and their
  action on root spaces are proved, as are their idempotence and full equality
  with the enclosed finite cluster projections. Fixed-contour projections depend
  analytically on the potential; their ranks and total enclosed algebraic
  multiplicities are locally constant. The punctured-strip estimate and spectral
  localization for small potentials are proved, along with the numerical
  height-decay estimate and its Neumann region. The double-resolvent frequency-tail
  bound of Lemma 3.4 is proved with constant `32p²` in this norm. Its squared
  criterion admits whole punctured strips and circles. Arbitrary-potential
  localization is proved uniformly on open convex potential neighborhoods
  containing zero, with the central box and disks specified in Corollary 3.5.
  The closed even/odd coefficient subspaces are complementary. Even-supported
  potentials preserve both subspaces, as do their resolvents and spectral
  circle projections. At `π n`, free root spaces are exactly two-dimensional
  ordinary eigenspaces; deformation from zero proves the high-frequency disk count
  and the parity of all enclosed root vectors for even-supported potentials.
- Every Banach coefficient sequence now defines a genuine period-two tempered
  distribution, with exact coefficient recovery and period-one/even-support
  equivalence. Arbitrary periodic distributions with Banach Fourier regularity
  have unique coefficient representations, including the infinity endpoint.
  Scalar differentiation and the signed-pair free operator have exact
  distributional graph identifications. Potential multiplication is the unique
  continuous extension of the actual smooth operation, with real-line test integrals
  and faithful identification of the full operator equation. General Young triples
  give periodic distribution products with the exact constant-one Fourier norm
  bound. These agree with smooth polynomial multiplication, are independent of
  exponent representations, and are uniquely determined by continuous extension
  from polynomial multipliers, including both infinity-input endpoints.
- Physical translations of arbitrary periodic `L²` functions are strongly
  continuous isometries with exact Fourier phases and increment Parseval energy.
  The fractional translation seminorm is an actual nonnegative double integral
  and equals its exact Fourier-weighted sum, including infinite energies.
  For `0<s<1`, these weights have proved two-sided bounds by `|n|^(2s)`, with
  positive finite constants. Physical fractional regularity is equivalent to
  summability of the conventional homogeneous Fourier energy and to a unique
  representative in the project’s weighted Sobolev coefficient space. Fourier
  synthesis reconstructs the original function, with quantitative norm bounds
  retaining the constant mode. For arbitrary positive interval length, the
  interaction with the exterior is exactly an endpoint-weighted integral. Its
  weight is integrable precisely below half regularity; exact constant-function
  energies and bounds for bounded interval data are proved. A fractional Hardy
  inequality now controls both endpoint weights for general interval `L²` data
  with finite intrinsic energy when `0<s<1/2`, including arbitrary almost-everywhere
  representatives. Zero extension has an exact full-energy decomposition,
  and periodization is now controlled by its line translation energy. Thus
  interval data with finite intrinsic fractional energy has weighted square-
  summable actual Fourier coefficients for `0<s<1/2`, without endpoint matching.
  Appendix A.9's actual Fourier coefficients now belong to `ℓ^q` for
  `q>1/(s+1/2)`. At `s=0`, interval `L²` alone suffices for every `q≥2`,
  including infinity. Intrinsic half regularity gives every finite `q>1`
  by lowering regularity first. The weighted coefficient embedding is an
  injective continuous linear map. The composite bound is now proved in
  the original interval's intrinsic Gagliardo size, with finite constants
  depending only on regularity and the target exponent. Its zero-regularity
  normalization is sharp, and the half-regularity bound uses an explicit lower
  index. Actual Fourier scaling now extends these conclusions to every
  positive interval length. Square energy scales by `c⁻¹` and fractional
  energy by `c^(2s-1)`; the zero-regularity norm bound has normalization
  `L^(-1/2)` on length `L`. The reverse periodic-to-interval bound is now
  proved as well. Below half, weighted square summability is equivalent to
  finite intrinsic interval energy on every positive length; explicit two-sided
  norm bounds hold in the period-two model. Intrinsic interval classes now
  form a normed complex vector space with norm squared exactly equal to the
  physical square energy plus fractional difference energy. Every original
  interval input reconstructs almost everywhere. The actual Fourier maps
  are continuous linear injections in this norm, including at half regularity.
  The graph is closed, so the intrinsic space is now proved complete, including
  at half regularity. Its complex inner product preserves the physical
  normalization. Intrinsic convergence is equivalent to convergence of both
  graph components. Below half, actual Fourier analysis is now a continuous
  linear equivalence with the weighted Hilbert coefficient space, with explicit
  forward and inverse bounds for every positive interval length. Finite Fourier
  truncations converge in the full intrinsic norm, and finite Fourier support
  is dense. Synthesis alone remains continuous throughout `0<s<1`.
- Section 6's normalized, symmetric, monotone submultiplicative weights are
  now represented, including `(1+|nπ|)^s` and the displayed normalization
  `w(n)≥1`. Shifted scalar norms agree with actual Fourier-wave multiplication,
  and translated weights give the same coefficient space with comparison
  factor `w(i)` in both directions. The finite-`p` pair norm uses opposite
  component shifts and has the exact signed coefficient energy, without an
  extra pair-norm factor. The resonant projections now select first-component
  frequency `-n` and second-component frequency `n`. The complementary free
  inverse exists throughout the closed strip, including `λ=nπ`, and gains one
  weighted derivative. Both projected inverse identities and uniqueness are
  proved, with exact agreement with the existing free differential pencil.
  The projections and base inverse are contractions in every signed shifted
  finite-`p` norm. Weighted Young convolution has constant one and agrees with
  the existing product. Lemma 6.4 is now proved for every finite Banach exponent:
  `T_n=Φ A_λ⁻¹ Q_n` maps shift `-i` to shift `i` with bound
  `c_p ‖φ‖`, uniformly on the full strip, and `c_2=2`. It agrees exactly with
  the original potential applied to the complementary domain inverse. Two
  applications restore the input shift. Lemma 6.5 is now proved for all finite
  Banach exponents on the full strip: the shifted square has bound
  `C_p ‖φ‖ (‖φ‖/(1+|n|)^(1/p) + ‖R_n φ‖/w(n))`. The tail retains its boundary,
  and the additional inverse-weight gain is proved in the near-near term.
  The actual square agrees with the double-inverse factorization. The locally
  uniform contraction threshold is now proved: one open convex neighborhood
  and one frequency cutoff bound both the unweighted and weighted shifted
  squared norms by `1/2` throughout the closed strips. The squared Neumann
  inverse and the Q-equation are now solved: `v=A_λ⁻¹ Q_n T̂_n Φu` is the
  unique complementary solution in the weighted derivative domain, with
  `Φv=T̂_n T_n Φu`. The weighted and unweighted inverses agree on common
  inputs. Lemma 6.6 is now proved for the original periodic spectrum:
  `λ` is a periodic eigenvalue exactly when the explicit `2×2` resonant
  matrix has determinant zero, with a locally uniform frequency cutoff.
  Eigenfunctions are reconstructed in the actual derivative domain.
  Lemma 6.7(i) is now proved: the two diagonal corrections agree for
  arbitrary complex potentials. A bilinear Green identity gives the source
  matrix form at every finite Banach exponent. The printed unconditional
  reality clause in 6.7(ii) has a proved counterexample: constant components
  `(1,i)` give `a_n(nπ)=i/(2πn)` at arbitrarily large positive indices
  satisfying the half-size contraction. The conditional conjugation identities
  under the proof's assumption `φ*=±φ` are now proved for both coefficients,
  with a locally uniform cutoff. On the real spectral axis, `a_n` is real
  for either type; the off-diagonal relation retains the appropriate sign.
  The component parity expansions (1.14)–(1.15) and their convergent scalar
  Neumann series are now proved. The `b_n⁺`/`b_n⁻` names follow the source's
  basis order, with leading physical coefficients `φ_+(2n)` and `φ_-(-2n)`.
  An explicit basis reversal gives the printed matrix and preserves its
  determinant. Both even vectors now have shifted and unweighted norm bounded
  by twice the opposite potential component norm. Their finite even sums have
  error at most `2·2⁻ᵐ` times that component norm, uniformly on a potential
  neighborhood and all sufficiently distant full closed strips. Lemma 6.8's
  analytic assertion is now proved: all three coefficients have jointly analytic
  extensions in the potential and spectral parameter that equal the actual
  source coefficients, including at strip centers and boundaries. The diagonal
  coefficient and its actual full-strip supremum now satisfy the source's
  Hölder bound with the exact reciprocal sum and unweighted potential norms.
  Lemma 6.8(i) is now proved for every finite `p>1`: the actual diagonal
  suprema have a summable `p`-power tail, bounded using the unweighted pair
  norm, the `N/2` Fourier tail, and decay `N^(-min(1,p-1))`. One cutoff and
  open convex potential neighborhood work for every larger tail cutoff.
  The proof-consistent form of Lemma 6.8(ii) is now proved: both actual
  weighted remainder suprema have convergent `p`-power tails, with bound
  `C_p ‖φ_±‖^p (‖φ‖^(2p)/N^min(1,p-1) + ‖R_(N/2)φ‖^(2p))`.
  The three-region Hölder estimate retains both potential tails in the near
  region. One open convex potential neighborhood and cutoff work for both
  coefficients, every larger cutoff, and every distant full strip. This
  follows the power sum and full pair norm in the source proof on page 43;
  the page-41 display omits the left-hand powers and uses `φ_+` in the first
  norm. That literal display is not claimed.
  Lemma 6.9 now has locally uniform bounds `|a_n|≤π/32`, `|b_n^±|≤π/16`,
  and an actual analytic determinant identified with the reduced matrix and
  original periodic spectrum. Any strip zero lies within `3π/32` of `nπ`,
  and the centered square strictly dominates the determinant perturbation
  on the radius-`π/4` circle. Cauchy's estimate gives `|a_n′|≤1/8` in that
  disc, and any two strip zeros satisfy `|ξ-η|²≤6|b_n⁺b_n⁻|_{U_n}`.
  A proved scalar argument principle and Rouché theorem now give exactly two
  analytic zeros, with multiplicity, on both the refined disc and the full strip.
  Two roots, allowing coincidence, exhaust all strip zeros and have exactly the
  corresponding analytic orders. A formal single-mode counterexample shows that
  the printed displacement bound cannot hold locally uniformly at zero: the
  roots move linearly with amplitude, while its budget is of higher order.
  The corrected quantitative tail sum is now proved, including the additive
  leading Fourier-tail contribution. One open convex neighborhood and cutoff
  give two roots with exact analytic multiplicities, localization, gap control,
  and every larger convergent displacement power tail, for all finite `p>1`.
  The bound holds for arbitrary source spectral weights and all signed modes.
  The same roots now also have convergent weighted gap power tails for every
  larger cutoff. Their bound retains the leading weighted Fourier tail and
  uses only the off-diagonal remainder estimate, with an explicit exponent-only
  constant. The weighted determinant now agrees with the original periodic
  spectrum, and each scalar analytic order equals the corresponding spectral
  algebraic multiplicity in distant strips. The same two actual periodic
  eigenvalues have both corrected power sums; their midpoint and squared gap
  agree with the intrinsic contour invariants. The weighted gap estimate is
  also proved directly for that intrinsic squared-gap sequence, independently
  of root ordering. This gives corrected forms of Propositions 6.1 and 6.3;
  the literal nonlinear-only printed budgets are not asserted.
  The original periodic midpoint now has a full `ℓp` displacement sequence
  and a quantitative tail bounded by half the two-root displacement budget.
  Both ordinary Dirichlet and Neumann branches also have full `ℓp`
  displacements and common quantitative tails, first for reflected potentials
  and then for original period-one coefficient inputs at every finite `p>1`.
  The physical interval `L²` branches have square-summable displacements while
  retaining their unique original high-disc eigenvalue characterization.
  The Section 5 auxiliary coefficient spaces are now constructed by the
  exact phase map `(f₋,f₊)↦(f₋,if₊)`, with closed complementary spaces at
  every Sobolev regularity. The actual restricted pencils are conjugate to
  ordinary boundary pencils with potential `(iφ₋,-iφ₊)`. Their spectra are
  closed and discrete and have actual auxiliary-domain eigenvectors. The
  source Neumann potential extension now gives both starred coefficient
  branches full `ℓp` displacements, common quantitative tails, and unique
  high-disc spectral identification. This completes all four coefficient
  displacement conclusions of Corollary 6.2. Actual auxiliary generalized
  root spaces are now conjugate to ordinary boundary root spaces, including
  all Jordan chains. Both auxiliary spectra have simple high-disc eigenvalues
  and central algebraic count `2N+1`, uniformly for source period-one
  potentials. The original physical auxiliary H¹ endpoint domains now have
  unique weighted representatives under the source phased reflection. Their
  eigenvalue equations transfer in both directions, and the physical eigenvalue
  sets equal the actual auxiliary coefficient spectra at the Neumann-extended
  potential. The original auxiliary domains now have their exact physical H¹
  norm and complete-space structure. The physical L² operators are densely
  defined and closed, with compact two-sided resolvents and spectra equal to
  the original auxiliary eigenvalue sets. Actual physical generalized root
  spaces now stabilize and have finite dimension, defining multiplicities
  that agree with the coefficient problem. Both starred physical branches
  have locally uniform algebraic counts, analytic simple high-disc values,
  and square-summable displacements with quantitative tails. This completes
  the physical L² starred displacement conclusions of Corollary 6.2.
  The actual source Neumann potential extension now preserves real type at
  every `1<p<∞`. Proposition 5.2(iv) holds for both source coefficient
  auxiliary problems and both original physical L² operators. The physical
  hypothesis is imposed a.e. on the original interval, and every nonreal
  parameter belongs to the actual auxiliary resolvent set.
  Both period-one auxiliary eigenfunction extensions are now bounded in the
  source's actual component-sum pair norms for `1<p<∞`. Their finite Fourier
  formulas agree with the physical phased reflection and uniquely determine
  the completed maps. At `p=2` they preserve the source norm exactly; at
  `p=1` the constant input `(0,1)` proves failure of coefficient membership.
- Section 8 now has symmetric free spectral products and their Euler limits.
  The full product has the correct `-4` normalization; the even subproduct
  needs `-1`. A formal audit of (2.4)/Lemma 8.1(ii) finds that the printed
  `-2` and `2` prefactors give incompatible discriminant values at zero.
  The free values require `-1` and `4`. Perturbed full periodic products now
  converge locally uniformly on the whole complex plane, using actual central
  algebraic multiplicities and distant spectral pairs. The limits are entire,
  have exactly the periodic spectrum as their zeros (including lattice points),
  and are independent of both pair labels and admissible central cutoffs.
  Their derivatives also converge locally uniformly on the whole plane.
  The extension across `πℤ` is uniquely fixed by
  continuity and the earlier relative formula. Every analytic zero order now
  equals the original spectral algebraic multiplicity, with finite order
  explicitly proved at every parameter. Every finite `p>1` potential supplies
  the required data on a common open convex neighborhood. Exact identities
  between finite cutoffs preserve the normalization, including at spectral
  zeros and double roots. The finite central polynomials are now jointly
  analytic in the spectral parameter and potential, using transported contour
  determinants with original generalized-root-space multiplicities. Their
  normalized limits define a canonical product directly from the potential,
  agreeing with every admissible earlier construction. Paired relative products
  now converge uniformly over a common open convex potential neighborhood and
  each closed off-lattice half-gap ball. Hölder tails and the corrected spectral
  displacement budget give this convergence without continuous root labels.
  Restoring the bounded central correction and free factor now gives full
  polynomial convergence uniformly on every compact spectral set times one
  open convex potential neighborhood, including the free lattice. Finite
  spectral covers and maximum modulus retain the whole potential neighborhood
  without assuming it compact. The canonical product is jointly continuous,
  and the intrinsic polynomials converge locally uniformly jointly in both
  variables. Banach-space Schwarz estimates now also give joint complex
  Fréchet smoothness and local uniform operator-norm convergence of the
  polynomial derivatives. Every complex affine-line restriction is entire,
  including simultaneous spectral and potential perturbations. The actual
  factorial-normalized Fréchet series now has positive convergence radius and
  sums to the product, proving joint Banach-space analyticity. This includes
  weighted potential pullbacks and every mixed iterated derivative.
  Complete paired root sequences with finite-exponent ℓp displacements now
  also give entire even and odd subproducts, with locally uniform cutoff and
  derivative convergence on the whole spectral plane. Exact rescaling identities
  retain the central denominator and asymmetric odd cutoff. The free limits
  are Δ−2 and Δ+2, with corrected prefactors −1 and 4. Actual central parity
  root multisets are now constructed with original Jordan multiplicities and
  exact uniform cardinalities. Their polynomials factor the full central
  polynomial and retain the exact parity zero sets and analytic orders.
  The central roots are now spliced into the distant counted pairs, preserving
  ℓp displacements and the actual parity root multisets. The completed pairs
  give entire products whose whole-plane zero sets are exactly the original
  parity eigenvalues, with locally uniform cutoff and derivative convergence.
  Exact central growth and normalization identities now show that sufficiently
  large literal cutoffs agree for every admissible labeling and central cutoff.
  Thus both entire parity products are independent of those choices, including
  at roots. Both entire products now have exactly the original parity root-space
  multiplicities at every point, including the free lattice. Their product has
  the full spectral multiplicities and now equals the canonically normalized
  full product exactly. This equality follows from the finite cutoff identities
  and the odd boundary factor tending to one. The central parity polynomials
  and their normalized approximants are now jointly analytic in the spectral
  parameter and even-supported potential on common neighborhoods. Their contour
  determinants retain the original parity generalized eigenspaces. The literal
  cutoffs and intrinsic approximants at `2M` now converge uniformly on each
  compact spectral set over one actual potential neighborhood, including roots
  and free-lattice points. Intrinsic parity limits now depend only on the
  potential, retain the exact original orders, and factor the canonical full
  product. Both are jointly Banach-space analytic on the even-supported
  potential space and on the source period-one coefficient space for finite
  p>1. Their Taylor series converge locally, their polynomial derivatives
  converge uniformly on joint neighborhoods, and all mixed derivatives are
  analytic. A classical fundamental matrix is now constructed for every
  continuous potential on the unit interval, with no smallness assumption.
  Its determinant is one, its trace has the exact free value `2 cos z`, and
  its boundary determinants detect periodic and antiperiodic solutions at
  trace values `2` and `-2`. The Volterra integral operator now has a global
  inverse with factorial power bounds. This proves joint Banach-space
  analyticity of the classical solutions, monodromy, trace, and boundary
  determinants for arbitrary continuous potentials, including at multiple
  roots. All mixed derivatives of the trace are analytic. Original Hilbert
  parity eigenvectors now give nonzero classical solutions whenever the
  potential has a continuous representative on the unit interval. Intrinsic
  even and odd product zeros therefore force trace values `2` and `-2`, and
  the two factors have disjoint zero sets. The reverse bridge is now proved
  by signed Sobolev extension: every nonzero classical periodic or antiperiodic
  solution gives an original parity eigenvector. Thus both intrinsic parity
  zero sets equal the corresponding classical trace sets, and the full product
  has exactly the zeros of the trace squared minus four. Inhomogeneous Volterra
  solutions now handle the actual equation `(z-L)a=b` for domain-valued sources.
  Each original parity root-chain extension is equivalent to a two-coordinate
  classical endpoint equation, and fixing the initial vector makes the original
  preimage unique. The bounded zero-initial chain operator now generates an
  explicit spectral Taylor series, convergent in the supremum norm of whole
  solution curves with positive radius. All spectral derivatives are the
  factorial-scaled signed chain curves. Evaluating both columns proves the
  corresponding series and derivatives for the fundamental matrix and monodromy;
  the boundary multiplier changes only the constant coefficient. Finite chains
  with arbitrary initial data are now identified with the actual boundary Taylor
  equations. The finite linear convolution kernel uniquely parametrizes every
  original finite parity root vector, with the alternating initial signs retained.
  This correspondence is now a complex linear equivalence. Every finite kernel
  dimension equals the original finite root dimension, and the dimensions
  eventually equal the full original parity algebraic multiplicity. The free
  sequence has its exact value at every length, including negative Fourier indices.
  Scalar Taylor kernels now recover analytic vanishing orders exactly. General
  two-by-two formal matrices reduce to diagonal form through invertible operations
  preserving every finite nullity and determinant order. The actual boundary
  formal determinant is nonzero and its order equals the original parity
  algebraic multiplicity. Formal extraction now commutes with the analytic
  determinant Taylor series, proving equality of classical analytic determinant
  orders and original multiplicities. The functions `Δ−2`, `Δ+2`, and `Δ²−4`
  have the same vanishing orders as the canonical even, odd, and full spectral
  products. Their quotients now extend to entire nonvanishing functions,
  giving exact factorizations even at common zeros; the two parity factors
  multiply to the full factor. Their exact normalization is now proved below
  using Liouville's theorem. The canonical full, even, and odd
  products now have ratio one to their free functions at both ends of every
  fixed vertical line, for all finite `p>1` and even-supported potentials.
  The actual continuous-potential solutions now satisfy free-propagator
  integral formulas with a common exponential weight. In both half-planes,
  the decaying coordinate's error is at most the potential supremum norm
  times a bound for the opposite weighted coordinate, divided by twice the
  imaginary height. The coupled equations now supply that coordinate bound
  when `|Im z|≥‖Φ‖²`. The normalized classical trace has error at most
  `2‖Φ‖²/a+2‖Φ‖²/a²`, with `a=2|Im z|`. Its shifted and full characteristic
  ratios tend to one against their free functions at both imaginary ends,
  allowing the real spectral part to vary arbitrarily. The entire quotient
  factors now have vertical limit one, which determines their constant value
  once boundedness is established. The canonical full and parity products also have free ratio
  one along every path escaping to infinity at a fixed positive distance from
  `πℤ`, for all finite `p>1`. This includes real paths between the lattice
  points. A norm-preserving real phase rotation now gives the global bound
  `|Δ(z)|≤2 exp(|Im z|+‖Φ‖)`, including the real axis and uniformly on potential
  norm balls. Maximum modulus extends an entire-function bound across all free
  discs, and a bounded central region may be omitted from the hypothesis.
  Periodicity and compactness now bound the inverses of both free parity
  factors on every strip outside fixed free discs. Combining this with the
  half-plane limits bounds the classical/free ratios globally on that exterior.
  The canonical/free ratios have norm at least one half beyond a uniform
  spectral threshold, proving the missing quotient bound. Consequently, for
  even Hilbert potentials with compatible continuous representatives, the
  intrinsic products are exactly `Δ−2`, `Δ+2`, and `Δ²−4`, including at their
  roots. Parity-preserving finite Fourier approximation now removes the
  continuous-representative requirement from `f+2=g−2` for all even Hilbert
  potentials. The intrinsic discriminant `f+2` is entire and jointly analytic;
  it is also `g−2`, its square minus four is the full product, and its levels
  `±2` give exactly the original parity spectra. Actual classical traces of
  convergent even domain approximations tend to this function using only
  Hilbert-norm convergence. The intrinsic even-product construction and joint
  analyticity are available at every finite `p>1`. Exponent inclusions now
  identify every finite root-chain space, full root space, parity multiplicity,
  and canonical product. Density of the Hilbert image above `p=2`, and direct
  inclusion below it, prove `f+2=g−2` and `Δ²−4=fg` for every finite `p>1`.
  The discriminant has the original full and parity spectra with their exact
  multiplicities and is the unique continuous extension of the Hilbert values
  on the dense absolutely summable potentials. For every fixed even potential
  at finite `p>1`, both additive errors `Δ−2 cos z` and `Δ′+2 sin z`, divided
  by `exp(|Im z|)`, tend to zero uniformly at sufficiently large parameters
  outside fixed free discs. A formal audit shows that the printed cosine
  quotient includes arbitrarily large denominator zeros in its stated domain.
  The additive formulation remains meaningful there. A bound on normalized
  reciprocal sine now gives `Δ′/(−2 sin z) → 1` uniformly at exterior infinity
  for each fixed potential. Every sufficiently large critical point lies in
  an arbitrarily small free disc. The derivative is nontrivial and entire;
  its zeros are isolated, have finite orders, and are finite on compact sets.
  The free critical set is exactly `πℤ`. Rouché's theorem now proves one
  simple critical point in each sufficiently distant free disc and exactly
  `2N+1` roots counted with multiplicity in the central disc. These open discs
  exhaust the critical points, and their boundaries have none. The valid trace
  and derivative asymptotics and all three canonical/free ratios now hold on
  one open convex potential neighborhood beyond one spectral threshold for
  each tolerance. Joint limits allow the potential to converge while the
  spectral parameter escapes.
  These estimates now supply one common integer cutoff and open convex
  neighborhood for all the critical-point counts, boundary nonvanishing,
  simplicity, and exhaustion, valid at every larger central cutoff.
  For real-type potentials every discriminant critical point is now proved
  real. Gauss–Lucas gives real critical points of the finite central spectral
  polynomials; locally uniform derivative limits preserve nonvanishing off
  the real axis. The exact full-product identity transfers this to Δ′.
  This completes Lemma 8.3's counts, locally uniform cutoff, exhaustion, and
  reality assertions.
  The free-reference off-diagonal product estimate is now proved in ℓᵖ: for
  roots `πk+a(k)`, omitting the local factor gives a relative product whose
  error from one has an explicit bound on displacement norm balls, uniformly
  over arbitrary samples in the closed half-π free discs. The proof retains
  the signed Hilbert sum and controls the nonlinear remainder quadratically
  using doubled-exponent Young and Hölder estimates. A common positive ℓᵖ
  sequence now bounds the error throughout each disc simultaneously. Filling
  the sine quotient at its removable center and restoring the local factor
  gives sampled sine-product errors in ℓᵖ, including center and boundary
  samples, uniformly on displacement norm balls. Paired estimates now pass
  through all free centers by maximum modulus and transfer to the actual
  canonical parity products. Cauchy then proves both sampled errors in
  Lemma 8.4: `Δ(λn)−2 cos(λn)` and `Δ′(λn)+2 sin(λn)` belong to ℓᵖ, with
  one open convex potential neighborhood and uniform norm bounds for all
  samples in the quarter-π free discs. The displacement assertion of
  Lemma 8.5 is now proved: complete actual critical-point sequences have
  uniformly bounded ℓᵖ displacements on one potential neighborhood. Their
  central repetitions and global analytic multiplicities are retained.
  The normalized single product is now constructed as a locally uniform
  limit on the whole plane, with locally uniform derivative convergence.
  Its free value is exactly `−2 sin z`; for complete critical sequences it
  has exactly the critical zero set and the correct exterior normalization.
  The product now has exactly the derivative's analytic orders, including
  repeated central roots. Its filled quotient is bounded and identically
  one, proving `Δ′(z)=2 ∏n (ξn−z)/πn` with locally uniform cutoff convergence
  on the whole plane. Central roots can now be sorted lexicographically
  with repetitions retained, and free-disc separation gives a globally
  ordered bi-infinite sequence. Sorting preserves common local lp bounds
  and the product identity. Ordered labels now agree across all admissible
  cutoff choices, defining canonical critical coordinates with exact
  multiplicities and the product identity. Their displacement norms have
  common local bounds; at zero potential the coordinates are exactly `nπ`.
  Locally uniform potential limits now preserve critical counts on zero-free
  circles. Distant canonical coordinates are continuous at arbitrary even
  potentials, and all coordinate imaginary parts are continuous at real-type
  potentials. Analytic counts on central subsets equal counts of canonical
  indices, including repetitions. Real-diameter barriers and stable prefix
  and suffix counts now prove central real-part continuity, including at
  collisions. Every canonical coordinate is therefore continuous at each
  real-type potential under arbitrary even complex perturbations. This
  completes Lemma 8.5. Conjugation symmetry now proves the discriminant
  and its derivative real on the real axis. Rolle and distant uniqueness
  put the critical point strictly between distinct real gap endpoints;
  a collapsed pair equals the critical point by its multiplicity. Thus
  canonical critical coordinates interlace all sufficiently distant actual
  real gaps. Full periodic endpoints now admit a globally ordered paired
  enumeration: central sorting preserves all original multiplicities,
  distant sorting preserves each pair multiset, and both displacements
  remain in ℓᵖ. One potential neighborhood supports the construction at
  every sufficiently large cutoff. Ordered labels are now unique across
  cutoffs, defining canonical left and right endpoints with ℓᵖ displacements.
  The same canonical coordinates work at every large cutoff on one
  neighborhood; both equal `nπ` at zero potential. Stable periodic counts
  now prove coordinate continuity at every real-type potential under
  arbitrary even complex perturbations, including colliding endpoints.
  Continuity along real scaling now identifies the discriminant level
  of every canonical pair and recovers the exact central parity multisets.
  Distinct indexed real gaps are strictly separated, and every open or
  collapsed gap contains a critical point. Central count saturation now
  identifies that point with its canonical critical index, proving global
  interlacing, strict open-gap inequalities, and collapsed-gap equality.
  Each gap contains exactly one critical point; all critical points are
  simple and have nonzero second discriminant derivative. Every canonical
  critical point is now a strict real local maximum or minimum, including
  collapsed gaps. Each gap contains exactly one local extremum, and there
  are no others. The entire product with one endpoint pair removed now
  has the corrected quadratic factorization and exact critical midpoint
  identity used in Lemma 8.6, valid also at collapsed gaps. Its error from
  the free squared sine quotient and the derivative error now have locally
  uniform lp bounds on the source discs. Canonical endpoint displacements
  also have bounded norms and arbitrarily small local tails. Evaluation at
  canonical critical points now gives locally uniform lp tails for the
  remaining-product value minus one and its derivative. The midpoint
  coefficient now has norm at least one on a common distant tail, proved
  using uniform small tails and critical localization. Its exact quotient
  gives the squared-gap midpoint offset with locally uniformly bounded lp
  coefficients, completing Lemma 8.6 for even complex potentials, including
  collapsed gaps. The closed real gaps are now exactly the set where
  `|∆|≥2`; open interiors correspond to `|∆|>2`, and equality occurs exactly
  at endpoints. The signed inequality `(-1)^n ∆≥2` holds throughout every
  gap and is strict in its interior, including negative indices. Complete
  Dirichlet and Neumann sequences now retain all actual algebraic
  multiplicities and have lp displacements, on a common neighborhood
  and cutoff. Their Section 9 products converge locally uniformly to
  entire functions with exactly the boundary spectra as zeros and free
  value `sin λ`, including for original period-one potentials. Independence
  from central labels, parameter analyticity, canonical boundary coordinates,
  starred products, and the anti-discriminant remain next.
- No spectral or classical Birkhoff results are introduced as axioms.

See [PLAN.md](PLAN.md) for the implementation sequence and [STATUS.md](STATUS.md)
for the precise implemented scope.
