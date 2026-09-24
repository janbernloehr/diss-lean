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
  value `sin λ`, including for original period-one potentials. The products
  now agree across all central labelings and cutoffs. Intrinsic characteristic
  functions, defined from the actual central spectra, retain the exact
  original algebraic multiplicities as analytic zero orders. Their finite
  approximants and first derivatives converge locally uniformly, and both
  intrinsic functions have the exact free sine normalization. Boundary
  contour determinants now retain every original generalized multiplicity
  and depend jointly analytically on the potential and spectral parameter.
  Both normalized central polynomials are jointly analytic for every large
  cutoff on one common neighborhood, including for source potentials.
  Complete boundary displacements now have common full lp bounds. These
  give convergence uniform over one potential neighborhood and every compact
  spectral set, including free lattice points. Analytic approximation proves
  joint Banach-space analyticity of the infinite ordinary boundary products,
  including their source period-one realization and all characteristic zeros.
  This completes Lemma 9.1(i) for Dirichlet and Neumann spectra. Canonical
  ordered boundary coordinates now retain the exact spectra, multiplicities,
  lp displacements, and characteristic products independently of cutoff
  choices. They have the signed free values, are real at real-type reflected
  potentials, and have common local full lp bounds at all large cutoffs.
  Every coordinate is now continuous at real-type potentials under complex
  perturbations, including repeated roots. Pullback through the real-type
  preserving source extension proves ordinary Lemma 9.1(ii) on the original
  coefficient space. Both sequences are analytic outside a finite central
  block at arbitrary complex potentials. The classical endpoint formulas now
  have the exact original physical zero sets and satisfy
  `Δ² − 4 = δ² − 4χDχN`. Real-type symmetry gives the boundary trace bound;
  a common continuous representative places boundary roots in some original
  periodic gap. Continuation from the free potential now proves the matching
  gap index, including collapsed gaps and the signed discriminant inequality,
  for compatible continuous real-type potentials. Boundary root spaces and
  algebraic multiplicities now agree under finite exponent inclusion,
  including at p=1. For p>1, the ordered boundary roots, lp displacements,
  and normalized characteristics are exponent independent. Both original
  periodic endpoints and their displacements now agree across finite
  exponents too. The half-interval Fourier map and both reflected extensions
  commute with inclusion, as do the distinct source potential realizations.
  This identifies the source boundary roots, normalized characteristics,
  and original periodic endpoints across exponents. Finite Fourier input now
  has a common continuous physical representative in both realizations.
  Symmetric real-type truncations and coordinate continuity extend the
  indexed interlacing theorem to every finite source exponent p>1. This
  completes ordinary Lemma 9.1(iii), including collapsed gaps, strict
  neighboring-gap separation, and the signed discriminant bound. The
  auxiliary starred boundary problems now have canonical roots and normalized
  entire products with their actual spectra and multiplicities. Their
  characteristics are jointly analytic, their roots are continuous at
  real-type potentials, and both agree across finite exponents. Phase
  conjugation now preserves the original periodic spectrum and every
  generalized multiplicity. On the period-one source, starred roots and
  normalized characteristics equal ordinary ones at the explicitly rotated
  source. The periodic spectrum and multiplicities uniquely determine the
  ordered signed endpoint sequences, which are therefore unchanged by this
  rotation. Both actual starred root sequences now interlace in the original
  indexed periodic gaps at every finite source exponent p>1, with strict
  separation between neighboring gaps, collapsed-gap equality, and the
  signed original discriminant bound. The actual classical auxiliary endpoint
  characteristics are now defined and jointly analytic, and their Neumann
  minus Dirichlet difference is the classical anti-discriminant. The printed
  starred D/N monodromy labels have the opposite signs from the source's own
  endpoint conditions; this is recorded in exact Lean identities. A jointly
  analytic source-space difference of normalized starred products is
  constructed. Classical initial-value uniqueness now proves exact phase
  conjugation of the monodromy: the diagonal entries and discriminant are
  unchanged, while the off-diagonal entries acquire opposite factors of
  `i`. Thus each actual auxiliary characteristic equals the ordinary
  separated characteristic of the rotated continuous potential, and the
  classical anti-discriminant is their Neumann-minus-Dirichlet difference.
  The classical auxiliary characteristic zeros now coincide with the actual
  physical auxiliary spectrum. For finite Fourier source data, each
  normalized starred source product now equals its actual classical auxiliary
  monodromy characteristic as an entire function. Their domain-based
  Neumann-minus-Dirichlet difference therefore equals the classical
  anti-discriminant on every finite source pair, at every finite exponent.
  Finite pairs are dense, so the jointly analytic source candidate is the
  unique continuous extension of those classical anti-discriminant values.
  Direct comparison with physical monodromy for arbitrary `L²` source data
  remains. The full source identity
  `∆²−4 = δ²−4χDχN` now follows at every finite exponent by density and
  joint analyticity. At every indexed Dirichlet root it gives
  `∆²(μₙ)−4 = δ²(μₙ)`, with no simplicity assumption.
  The generic entire boundary product now has ℓᵖ sine-error and derivative-error
  majorants on all free half-/quarter-π discs, uniformly on bounded sets of
  root displacements. Both starred source products now inherit these bounds
  on one source neighborhood. Their difference and derivative have a common
  ℓᵖ majorant on the free discs. At all sufficiently distant ordinary
  Dirichlet roots, the sampled values and derivatives have a uniform ℓᵖ tail
  bound. Joint analyticity and compactness control the finitely many central
  samples, with Cauchy's estimate covering their derivatives. Both full
  sampled sequences therefore have locally uniform ℓᵖ norm bounds, proving
  the source coefficient form of Lemma 9.2(iii).
  The first high-index step toward Lemma 10.1 is also formalized: on one
  source neighborhood, both periodic endpoints, both ordinary boundary
  roots, and the critical point lie in their common free quarter-π disc at
  every distant index. These discs are disjoint and have explicit linear
  pointwise separation. The finite central isolating discs remain.
  At real-type source potentials, every five-coordinate cluster lies in its
  indexed real periodic gap, and different indexed clusters have a positive
  lower bound on their mutual distance, even when coordinates within a
  cluster collide.
  Every cluster in a finite central block now fits strictly inside an
  explicit midpoint-centered complex disc. A single positive enlargement
  margin can be chosen for the entire block so that these discs are pairwise
  disjoint, including when a periodic gap collapses. Keeping the central
  coordinates in these fixed discs now holds on one open source
  neighborhood by continuity of all five canonical families. Combining
  these central discs with the uniform high-index discs now gives one
  neighborhood and an explicit disc choice for every signed index. The
  central discs are also disjoint from both tails: the two outer central
  endpoints are localized and the common central margin is at most π/4.
  Shrinking to a source ball makes this common neighborhood connected.
  The real-type source locus is convex, hence connected. The union of its
  local connected neighborhoods is now an open connected `Ŵp` containing
  that locus. Every point of `Ŵp` has a common local disc sequence for all
  nearby source potentials, and each periodic endpoint segment is inside
  its assigned disc. This proves the source-coefficient geometry of
  Lemma 10.1.
  The complete periodic endpoint labeling now identifies the actual
  periodic spectrum inside each assigned disc as exactly its indexed
  endpoint pair. Each circular boundary avoids the periodic spectrum,
  and the corresponding finite enclosed spectral set is that same pair.
  The algebraic multiplicity in each disc equals the number of occurrences
  in its endpoint pair. Consequently every corresponding Cauchy–Riesz
  projection has complex rank two, even at a collapsed double endpoint.
  The first two contour traces recover the canonical periodic midpoint
  and squared gap in every assigned disc. Frozen contours make both
  functions analytic on the open connected almost-real source domain,
  including at collapsed gaps. This proves the analyticity assertion of
  Lemma 10.2(ii)'s analyticity assertion.
  The indexed endpoint product equals the quadratic expression in this
  midpoint and squared gap, and is jointly analytic in the spectral
  parameter and source coefficients. This proves Lemma 10.2(iii).
  A two-root recurrence expresses every endpoint power sum as a polynomial
  in the midpoint and squared gap, proving Lemma 10.2(i), including at
  coincident endpoints.
  The canonical midpoint minus `πn` is now an actual source `ℓᵖ` sequence.
  Its full norm is locally bounded, and its tails are uniformly small on
  a common source neighborhood. The canonical gap is an actual `ℓᵖ`
  sequence, and its square belongs to `ℓᵖ⁄²` for every finite `p>1`.
  The squared-gap `p/2` power tail sum equals the `p` power of the
  unsquared gap's `ℓᵖ` tail norm. Those tails are uniformly small on a
  common source neighborhood, completing the source-coefficient form
  of Lemma 10.2(ii).
  Equation (2.9)'s normalized standard root is now defined. Its square
  equals the canonical endpoint factor outside the gap segment, and it
  reduces to the linear midpoint expression when the gap collapses.
  The contour estimates and identity of Lemma 10.3 remain.
  A general slit-plane lemma shows that `1-w²` meets the principal
  square-root cut only when `w` is real with `|w|≥1`. The corresponding
  endpoint ratio is now proved to force the spectral parameter onto the
  closed gap segment. Hence equation (2.9)’s radicand lies in the
  principal slit plane everywhere outside that segment. The
  standard root is now analytic in the spectral parameter on the full
  complement of the closed canonical gap segment. On the same
  connected almost-real source domain as Lemma 10.2, it is jointly
  analytic in source coefficients and spectral parameter off the moving
  gap segment, including where the endpoints coincide. Its norm squared
  is exactly the product of the two endpoint distances off the segment.
  On any different disjoint isolating disc the root is nonzero, and
  two-sided endpoint distance bounds transfer to the root norm. For any two
  distinct free tail discs this gives equation (2.10) with explicit
  constants π/2 and 3π/2, uniformly on a connected local source
  neighborhood. For every finite central index block, a possibly
  smaller common source neighborhood gives a positive lower bound for
  roots evaluated in any other central disc. Boundedness of the finite
  disc union also gives an upper bound. Together these yield the
  `|m−n|`-scaled estimate (2.10) for all distinct indices in that
  central block on one connected source neighborhood. The same estimate
  remains valid when every central disc margin is shrunk below any
  prescribed positive bound. The outer
  central endpoint also gives a pointwise π/4 separation from every
  positive tail disc. Thus roots in either central–positive-tail
  orientation have norm at least π/4. The mirrored negative-tail
  argument gives the same bound on the other side. The finite
  central discs have uniformly bounded lattice offsets; triangle
  inequalities give an upper bound proportional to `|m−n|` for mixed
  central–tail roots in both orientations. Combining the lattice-center
  triangle inequality with the fixed π/4 gap also gives a common
  `|m−n|` lower bound in both orientations, assuming the relevant
  endpoint localization, pointwise separation, and segment exclusion.
  Under strict localization of the two outer central endpoints, the
  positive and negative tail geometry now supplies those conditions
  whenever all nearby spectral clusters lie in their assigned discs.
  One constant then gives both sides of (2.10) for every mixed pair.
  Uniform tail isolation and finite central-disc isolation now choose
  those discs on a single connected neighborhood around each real-type
  source potential, proving the local mixed-pair estimate. The bounded
  central radius now yields one connected neighborhood and one
  pairwise-disjoint disc family for all indices. On that family one
  constant proves the full two-sided estimate (2.10) for every distinct
  pair. The inverse root is analytic off its gap and integrates to zero
  over a circle whose filled disc avoids that gap, including circles
  inside another assigned isolating disc. For a collapsed gap, the
  normalized diagonal circle integral is `−1`. Circle inversion and
  the complex mean-value theorem now give the same `−1` value for
  every midpoint-centered circle with radius greater than half the
  gap norm, including noncollapsed gaps. A shifted inversion and the
  annulus theorem now give the same diagonal value for any positively
  oriented circle, with any center, whose open disc contains the closed
  gap segment. Together with the off-diagonal result this proves the
  circular-contour form of Lemma 10.3's identity. A holomorphic one-form
  theorem now proves that the reciprocal root's curve integral is
  invariant under any smooth closed-loop homotopy confined to a
  neighborhood away from its gap. The unit-interval circle path now has
  exactly the same integral as the standard `0..2π` circle integral.
  Hence any smooth closed loop supplied with a gap-avoiding smooth
  homotopy from an enclosing circle has normalized integral `−1`.
  A smooth periodic polar-radius graph now has that homotopy whenever
  all its radii stay beyond a disc containing the gap. Thus the value
  holds for these genuinely noncircular contours, including a positive
  cosine modulation. The same radial deformation stays inside an outer
  disc containing the filled contour. When this disc lies in the
  indexed isolating disc, all other inverse-root integrals vanish.
  Combining both cases gives the normalized `−δₘₙ` identity for these
  polar contours. More generally, the same identity now holds for any
  smooth loop supplied with a smooth homotopy from an enclosing circle
  whose entire image stays inside the assigned isolating disc and avoids
  the indexed gap. Compactness lets the theorem use the homotopy image
  directly, without an auxiliary neighborhood. Constructing that
  homotopy for every admissible contour in the lemma remains. A geometric
  deformation lemma also shows that
  interpolating two discs containing the gap segment keeps every
  intermediate circle disjoint from it. A new affine-homotopy theorem
  handles any twice-smooth closed loop uniformly close to an enclosing
  circle: explicit inner and outer distance bounds keep the deformation
  away from the gap and inside its isolating disc. The normalized
  `−δₘₙ` identity therefore holds for this additional class without a
  polar parametrization or a supplied homotopy. More generally, convex
  contraction proves that every twice-smooth closed loop inside an
  assigned isolating disc has zero off-diagonal inverse-root integral.
  The indexed identity therefore needs a gap-avoiding circle homotopy
  only for the diagonal case; that homotopy may leave the isolating disc.
  The inverse-root integral is now also locally constant under uniform
  smooth perturbations of any loop avoiding its gap: compactness supplies
  a positive perturbation radius, and an affine homotopy stays gap-free.
  In particular, a known diagonal `−1` value persists on all sufficiently
  close smooth loops. Local constancy and connectedness now also show
  that a merely continuous homotopy preserves the integral when each
  intermediate loop is twice smooth and avoids the gap; basepoints may
  move. This yields the normalized `−δₘₙ` identity for loops connected
  to an enclosing circle by such a family, without twice-smoothness of
  the full homotopy square. The diagonal identity for every admissible
  counterclockwise contour remains open.
  The principal square root now has proved upper and lower boundary
  limits on the negative real axis. The normalized standard root and
  actual canonical source root satisfy both straight transverse limits
  in formula (2.12) for every point of a noncollapsed complex periodic
  gap, including its midpoint and endpoints. The same boundary values
  now hold for arbitrary approaches within each open side of the gap,
  allowing the longitudinal coordinate to vary. A cosine parametrization
  now gives the normalized side-integral estimate of Lemma 10.4 for
  continuous data on every noncollapsed canonical gap. The integrand's
  endpoint singularities cancel almost everywhere, and one attained
  maximum bounds both sides and every stopping point. The weighted
  `r`-integral and an independently defined straight side path integral
  now equal that boundary integral. Truncated path integrals converge
  to it, with both singular endpoints removed when the stopping point
  is the right gap endpoint.
  Ordinary and starred intrinsic boundary
  characteristics now have exact free-sine exterior ratio one, while the
  classical separated characteristic has sine-scale growth. These give a
  uniform bound on the classical-to-intrinsic ratio outside distant free-root
  discs. The classical characteristic now also has ratio one to free sine
  as imaginary height tends to positive infinity, uniformly in real spectral
  part. The classical-to-intrinsic and actual auxiliary-to-starred-source
  quotients therefore tend to one on separated upper paths, fixing their
  normalization constants. The classical
  separated characteristic now has a convergent scalar Taylor series built
  from normalized forced-solution chains. Its formal order equals its analytic
  order, and each finite scalar Taylor kernel is exactly the system of
  separated endpoint conditions on a finite chain. At finite order `m`, its
  kernel dimension is `min N m` at truncation length `N`. Every original
  physical generalized eigenvector now reconstructs a unique finite scalar
  jet: the classical forced ODE identifies each interval-domain chain level,
  and its left endpoint determines the scalar coefficient. The resulting
  linear map from the scalar Taylor kernel onto each finite physical root
  space is bijective. Thus the finite physical root-space dimension is
  `min N m`, and the characteristic's analytic order equals the full original
  physical algebraic multiplicity at every spectral parameter. Equal zero
  orders fill the classical-to-intrinsic quotient across every root. An
  exterior bound and maximum modulus make it globally bounded, while its
  upper limit is one. Hence the intrinsic boundary product equals the literal
  classical monodromy endpoint characteristic for continuous physical data.
- No spectral or classical Birkhoff results are introduced as axioms.

See [PLAN.md](PLAN.md) for the implementation sequence and [STATUS.md](STATUS.md)
for the precise implemented scope.

The first Lemma 10.5 product lemmas now express each normalized
standard-root factor as midpoint displacement, free spectral term, and
square-root error. The spectral terms cancel exactly for paired indices
`k` and `-k`; the principal square-root error is bounded by its radicand
error. Infinite-product convergence and joint analyticity are next.

The midpoint contribution to the paired standard-root product now belongs
to `ℓ¹`, and its tails are uniformly small on a neighborhood of any source
potential. This uses the existing conjugate-exponent Hölder embedding for
the punctured reciprocal lattice. The square-root remainder and full
product convergence remain open.

The square-root remainder in each normalized factor is now absolutely
summable over indices. On a neighborhood of any source potential and any
bounded spectral region, its distant terms share one summable `1/k²`
majorant. Combining this with the midpoint correction and the quadratic
paired-error term is the next step toward Lemma 10.5's product.

The paired product for the omitted central index is now defined and its
finite cutoffs converge at every source potential and spectral parameter.
The limit is nonzero outside the noncentral gap segments. The proof places
single-factor errors in `ℓ²` and their paired cross term in `ℓ¹` by Hölder.
Analyticity and arbitrary omitted indices remain.

The natural finite paired cutoffs are now analytic in the spectral parameter
away from the noncentral gaps. On the connected almost-real source domain,
they are jointly analytic in the spectral parameter and source coefficients.
Each paired factor is continuous on compact subsets of the gap complement,
providing the continuity hypothesis for the next uniform-convergence step.

For each fixed source potential, the natural paired cutoffs now converge
uniformly on every compact spectral set avoiding the noncentral gaps.
The proof gives a shared summable majorant for the paired factor errors:
the midpoint terms are fixed `ℓ¹` sequences, and the square-root and
quadratic terms are uniformly `O(k⁻²)` on bounded spectral sets.

The complement of the noncentral periodic gap segments is now proved open.
The paired product converges locally uniformly there and is analytic in the
spectral parameter for every fixed source potential. Together with the
earlier nonvanishing theorem, this establishes the omitted-zero product's
spectral holomorphy and nonzero value on its natural domain.

The paired-factor errors now have uniformly vanishing finite absolute tails
on a source neighborhood and bounded spectral region. A finite-prefix
bound turns these tails into uniform convergence of the natural paired
cutoffs on a joint spectral/source neighborhood. On the common connected
almost-real source domain, this applies at every point of the noncentral-gap
complement. Joint analyticity of the infinite limit and arbitrary omitted
indices remain open.

The uniform joint limit is now continuous on the common almost-real
source/gap-complement locus. At each point of this locus the omitted-zero
product is nonzero on some open joint spectral/source neighborhood.
The next domain construction places the analytic finite cutoffs and their
uniform limit on one open joint set.

That common domain is now constructed. A gap segment is determined by its
midpoint and squared endpoint difference, so its incidence relation is
closed even when endpoint labels collide. Uniform endpoint bounds keep all
distant gaps away from a fixed spectral ball on one source neighborhood.
The moving-gap complement is therefore open jointly in spectral and source
variables. On one connected almost-real source domain, the finite paired
cutoffs are analytic and converge locally uniformly to the product on this
same open joint domain. Passing joint analyticity to the limit is next.

On this open domain the infinite paired product is now jointly complex
smooth to every finite Fréchet order. The first derivatives of the finite
cutoffs converge uniformly in operator norm on a smaller ball around each
point. This uses the fixed-ball uniform convergence and Banach-space
Schwarz bounds; a local Taylor-series argument remains to turn the
smoothness theorem into an explicit joint analyticity theorem.

The local Taylor argument is now formalized. On any open Banach-space
domain, a scalar-valued `ContDiffOn ℂ ∞` map is analytic there: Schwarz
bounds give a positive Fréchet-series radius, and one-variable Cauchy
expansion along short complex lines identifies its sum. Consequently the
infinite paired standard-root product is jointly analytic in the spectral
parameter and source potential on the open moving-gap complement over
one connected almost-real source domain. Arbitrary omitted indices and
the remaining parts of the dissertation are still to be formalized.

For an arbitrary omitted index `n`, the literal symmetric finite cutoff
from Lemma 10.5 is now defined using the dissertation's `π₀ = 1`,
`πₙ = nπ` normalization. Its joint moving-gap domain is open, and every
finite cutoff is jointly analytic and nonzero there. The zero-index
cutoff agrees exactly with the previously proved paired cutoff. The
locally uniform infinite-product limit for arbitrary `n` is next.

The literal cutoffs for every omitted index now converge pointwise at
all complex spectral parameters. Symmetric factorization reduces them
to paired factors differing from the established omitted-zero product
at only one pair, so absolute summability persists. The resulting
infinite product is nonzero wherever all unomitted gap segments are
avoided, and it agrees with the established paired product at `n = 0`.
Joint local uniform convergence and analyticity remain next.

The arbitrary-index case of Lemma 10.5 is now proved on a common
connected almost-real source domain. Every omitted-index product is
jointly analytic and nonzero on its open moving-gap complement; its
literal symmetric cutoffs converge locally uniformly there. Restricting
the joint result gives spectral analyticity for each fixed source.
The next dissertation step is Corollary 10.6 on quotients of the
entire spectral product by these standard-root products.

The full normalized single-root spectral product is now jointly entire
in the spectral parameter and its `ℓᵖ` root-displacement sequence.
The symmetric finite cutoffs converge uniformly on compact spectral
sets over bounded displacement families. This supplies the numerator
analyticity needed for Corollary 10.6; deleting one root and forming
the quotient remain the next steps.

Corollary 10.6 is now represented by the literal symmetric products of
`(σₘ−λ)/wₘ(λ)` with any index `n` omitted. Their limit is analytic
jointly in the spectral parameter, the `ℓᵖ` root displacements, and the
source potential on the open moving-gap complement. The proof uses a
jointly entire deleted numerator and the nonzero omitted standard-root
product from Lemma 10.5. Lemma 10.7 on the canonical root comes next.

The full canonical-root product of equation (2.13) is now formalized.
It squares to the source discriminant expression `Δ²−4` off the gaps,
is analytic in the spectral variable there, and is jointly analytic in
the spectral variable and source potential on a connected almost-real
source domain. A collapsed gap gives an analytic linear-factor extension.
The boundary-sign clause of Lemma 10.7 is the next step.

The boundary-sign clause is now proved on the same connected almost-real
source domain as joint analyticity. Isolating discs keep distinct gap
segments disjoint. On a noncollapsed gap, the upper and lower limits of
the canonical root exist and are exact negatives; on a collapsed gap it
extends analytically across the segment. The next target is the
asymptotic estimate in Lemma 10.8.

The first Lemma 10.8 step now factors each literal finite quotient into
a midpoint quotient and an inverse square-root gap correction. For a
radicand perturbation of norm at most one half, the correction differs
from one by at most twice that norm. The finite correction product has
an exponential error bound, reducing the remaining estimate to uniform
source-disc separation and sequence summation.

The reciprocal-square sum in Lemma 10.8 is now an actual convergent
sequence of rows in `ℓ^(p/2)`. A powered Young argument covers both
`p ≥ 2` and `1 < p < 2`; the latter does not assume a Banach norm at the
half exponent. On an open connected neighborhood of every real-type
source, periodic midpoints now stay a distance proportional to the
index separation from every other isolating disc. The squared-gap
radicand at each such point is bounded by the matching reciprocal-square
row term, and every finite off-diagonal radicand sum is bounded by the
full row sum.

For a root-minus-midpoint displacement in `ℓᑫ` with finite `q ≥ 1`,
Hölder's inequality now bounds every finite midpoint quotient uniformly
on those discs by an exponential in its `ℓᑫ` norm. When a squared-gap
row is small, this combines with the gap correction to bound the
literal finite quotient product. The remaining work is to prove the
uniform sequence estimate in the omitted index and pass to the infinite
product limit.

The physical squared-gap row is now proved to vanish as the omitted
index tends to either end of the integer lattice, including when
`p/2 < 1`. For each fixed source, its large-index threshold activates
the finite full-quotient bound simultaneously for every cutoff,
spectral point in the corresponding isolating disc, and admissible
root sequence.

The squared-gap rows now vanish uniformly on an open neighborhood of
each source. A summable reciprocal-square kernel controls the uniformly
small gap tail, and its translates control the finite central block.
Combining this with midpoint-disc separation gives one connected
neighborhood and one large-index threshold for the finite full-quotient
bound. The first-order `ℓᑫ` estimate across omitted indices and the
infinite-product asymptotic remain open.

The physical first-order reciprocal row now differs from the free
lattice row by an `ℓᑫ` correction for every Banach exponent. The proof
uses midpoint-disc separation and the summable reciprocal-square
kernel, with bounds uniform over nearby source potentials and spectral
samples in all distant discs. Identifying the free row with the sampled
Hilbert transform will give the signed `ℓᑫ` estimate for `1 < q < ∞`.

The signed first-order midpoint sum now has an `ℓᑫ` bound for
`1 < q < ∞`: the free lattice part is a sampled discrete Hilbert
transform, and the physical midpoint correction is controlled by a
reciprocal-square convolution. The bound holds for any choice of one
spectral point in each distant isolating disc, with constants shared
on a connected neighborhood of a real-type source. Taking the
supremum over each disc and passing to infinite products remain open.

The coordinatewise supremum of the signed midpoint sum over each
distant isolating disc now lies in `ℓᑫ` for `1 < q < ∞`. For `q=1`, it
lies in every finite exponent above one. These are locally uniform
bounds near a real-type source. The proof uses the fact that the
sampled Hilbert estimate holds for every independent choice of one
point from each disc. The infinite-product estimate remains open.

The finite quotient estimate now also applies to the analytic infinite
quotient on sufficiently distant discs. Pairwise disjoint isolating
discs put those spectral points outside every other periodic gap,
where the literal finite cutoffs converge to the quotient. The sharper
sequence asymptotic still requires a quadratic midpoint-product
remainder estimate and combination with the squared-gap correction.

The nonlinear error of the infinite midpoint product now has a
quadratic `ℓᑫ` bound. The result retains the signed first-order sum
exactly and controls the supremum of the remainder over each distant
isolating disc, including at `q=1`. Combining this with the signed
sum and the squared-gap correction is the remaining product estimate.

The signed and quadratic midpoint terms are now combined: the full
infinite midpoint product minus one has an `ℓᑫ` disc-supremum bound
for `1 < q < ∞`, and the `q = 1` case has an `ℓ^{1+}` bound. The
remaining Lemma 10.8 work connects this product to the literal
single-root quotient and controls the squared-gap factor.

The midpoint product is now identified with the limit of the literal
symmetric cutoff factors. Its disc-supremum bound therefore applies to
the midpoint part of the single-root quotient. A separate squared-gap
comparison is still needed for the complete quotient estimate.

The squared-gap comparison now reaches the actual analytic infinite
quotient. Its difference from the midpoint product has a uniform
`ℓ^(p/2)` disc majorant, including `1 < p < 2`. Combining it with the
midpoint `ℓᑫ` and `ℓ^{1+}` majorants is the next Lemma 10.8 step.

The first quotient asymptotic of Lemma 10.8 is now formalized near
real-type base sources for the actual analytic infinite quotient on
distant source discs. The error has locally uniform
`ℓᑫ + ℓ^(p/2)` majorants when `1 < q < ∞` and
`ℓ^{1+} + ℓ^(p/2)` majorants at `q=1`.

The free deleted numerator is now identified with the filled sine
quotient, including at its removable center. Specializing the
quotient theorem to free numerator roots gives the sine-product
consequence with `ℓᵖ + ℓ^(p/2)` disc majorants near real-type base
sources. The dissertation's wider setting and later lemmas still
require work.

The distant-index step toward Lemma 10.10 is in
`SourceCriticalMidpointGapSquaredTail.lean`. It states the locally
uniform squared-gap critical-root offset in source coordinates for
all sufficiently distant indices and derives equality with the
midpoint for collapsed distant gaps.

For every open real periodic gap, including central gaps,
`CriticalOffsetCoefficientOpenGap.lean` proves that the coefficient
in the critical midpoint identity is nonzero and solves the offset
exactly as the squared gap times its quotient.

At a real-type potential, the exact squared-gap critical-root formula
now holds at every index, including collapsed central gaps.
`CriticalOffsetCoefficientCollapsedGap.lean` proves this using the
exact algebraic multiplicity of a collapsed periodic pair.

The deleted periodic-pair product is now identified with the square
of the omitted standard-root product wherever the other gap segments
are avoided. This proves that it is nonzero throughout each assigned
isolating disc, including on the selected gap and its endpoints.

The exact squared-gap critical-root formula now extends to every
index of the connected almost-real complex source domain. At a
collapsed gap, cluster separation identifies its critical root with
the common endpoint.

The deleted periodic-pair product is jointly analytic on the omitted
root domain, and its spectral derivative is jointly continuous there.
`SourceCriticalGapQuotientContinuity.lean` uses this to prove fixed-index
quotient continuity and a common bound for any finite central block.
`SourceCriticalGapQuotientUniform.lean` combines that block with the
uniform distant tail. This yields the all-index squared-gap formula
of Lemma 10.10 and a locally uniform `ℓᵖ` coefficient bound on a complex
source neighborhood of each real-type potential.

The first part of Lemma 10.11 now has a collapsed-gap extension on an
open almost-real source domain. In
`SourceCriticalRootRatioCollapsed.lean`, the critical factor cancels
the linear standard-root factor, so the deleted single-root quotient
extends the discriminant derivative divided by the canonical root
analytically across that gap. The path-integral identity of Lemma
10.11(ii) remains to be formalized.

`SourceCriticalRootRatioCollapsedContour.lean` proves the closed-circle
integral vanishes when the indexed gap is collapsed and the filled
circle avoids all other gaps. The open-gap contour and admissible-path
statements of Lemma 10.11(ii) remain.

`RealGapArcoshIntegral.lean` formalizes the real open-gap primitive:
the signed discriminant has arcosh value zero at both endpoints, so
its arcosh derivative has zero integral whenever the endpoint kernel
is integrable. The endpoint integrability and comparison with the
canonical-root quotient are established below.

`SourceCriticalRootRatioFactorization.lean` separates the selected
critical-over-standard-root factor from an analytic deleted quotient.
The identity holds at every source potential off all gaps, and the
deleted quotient is analytic across the selected gap on an open
almost-real source domain. This is the product form needed to compare
the open-gap boundary integral with the arcosh derivative.

`RealGapArcoshRadicand.lean` identifies the arcosh denominator
exactly as the endpoint-distance product times the deleted periodic
pair product on the real axis, and proves the latter has positive
real value in the open gap. `RealDeletedPeriodicProduct.lean` shows
that the product is real on the whole real axis and strictly positive
on the closed gap, then obtains a uniform positive lower bound there.
`EndpointSqrtWeight.lean` proves the corresponding inverse square-root
weight is interval-integrable for arbitrary real endpoints and remains
so after multiplication by a continuous numerator.
`RealGapArcoshIntegrability.lean` applies this estimate to real-type
source potentials. It proves the discriminant arcosh kernel is
integrable across an open gap and its real interval integral vanishes,
without a separate endpoint-integrability assumption. The boundary
comparison is developed in the following files.
`SourceCanonicalRootGapSideSquare.lean` proves that both explicit
canonical-root boundary values square to the discriminant radicand at
each point of the selected gap. This starts the comparison with the
arcosh derivative integral.
`RealGapCanonicalRootValue.lean` specializes the boundary square
identity to real-type sources: the gap parameter is real, the squared
boundary value is four times the signed arcosh radicand, and the upper
boundary value is real and nonzero throughout an open gap's interior.
`RealGapCanonicalRootSign.lean` combines continuity, endpoint-product
positivity, and connectedness to show that the upper boundary value
equals either plus or minus twice the positive arcosh square root on
the entire interior.
`RealGapCanonicalRootRealAxis.lean` transfers this fixed-sign identity
from the normalized gap parameter to every interior real spectral
point between the periodic endpoints. This supplies the pointwise
boundary quotient needed for the interval-integral comparison.
`RealGapCanonicalRootUpperIntegral.lean` proves that the real-axis
integral of the complex discriminant derivative divided by the upper
canonical-root boundary value is zero on every open real source gap.
The parity sign of the numerator and the fixed boundary-root sign both
cancel as constants. `RealGapCanonicalRootLowerIntegral.lean` proves
the corresponding lower-side real-axis integral vanishes because its
canonical-root boundary value is the negative of the upper one.
The enclosing-contour path integral still needs to be related to
these two boundary integrals.
`SourceCriticalRootRatioGapSides.lean` identifies each interior
boundary value of the discriminant quotient with the selected
standard-root side kernel multiplied by the analytic deleted critical
factor. This gives the pointwise connection to the existing straight
gap-side path-integral construction; its integral form follows below.
`RealGapCanonicalRootAffineIntegral.lean` pulls both vanishing
real-axis boundary quotient integrals back to the signed interval
`[-1,1]` with the exact affine Jacobian. This puts them in the same
coordinate as the straight gap-side path integrals.
`SourceCriticalRootRatioGapSideIntegral.lean` identifies the straight
side-path integrands with those affine pullbacks and proves that the
upper and lower side-path integrals both vanish on every open real-type
source gap. Relating an enclosing contour to these side paths remains
the main open part of Lemma 10.11(ii).
`SourceCriticalRootRatioContourHomotopy.lean` proves the full quotient
is holomorphic off all periodic gaps and its curve integral is invariant
under smooth gap-avoiding loop homotopies. For real-type sources, a
continuous homotopy with twice-smooth loop slices suffices. Concentric
circle integrals also agree across any annulus avoiding all gaps, in
particular when the inner circle encloses the selected gap and the
outer disc avoids every other gap. The slit-to-circle deformation is
still required to turn the vanishing side-path integrals into the
enclosing-contour identity.
`SourceCriticalRootRatioGapSideRegularity.lean` proves the deleted
critical factor is continuous on the entire closed selected gap. The
upper and lower straight side-path integrands are therefore interval
integrable even at the branch-point endpoints, and their doubly
truncated integrals tend to zero as both cutoffs vanish. These endpoint
limits are the boundary input for a future slit-to-contour deformation.
`SourceCriticalRootRatioGapSideLimits.lean` proves that the actual
discriminant-derivative quotient approaches the two explicit boundary
quotients from the corresponding open sides of every noncollapsed gap.
The result holds on an open complex source neighborhood containing the
real-type locus. The remaining argument must deform an enclosing
contour to these sides, then extend the resulting zero contour identity
through the complex source neighborhood before proving arbitrary
admissible-path independence in Lemma 10.11(ii).
`SourceCriticalRootGapNeighborhood.lean` uses compactness of the selected
closed gap to find a uniform transverse neighborhood avoiding all other
gaps. On that neighborhood, both the reciprocal omitted-root product
and the regular critical-root numerator have finite bounds. The
remaining local estimate concerns the selected standard root near its
two branch points.
`SourceStandardRootTransverseBound.lean` supplies that estimate: at any
nonzero vertical offset from an open real gap, the selected root's norm
is at least the real half-gap times `sqrt(1-t²)`, uniformly for
`-1 ≤ t ≤ 1`. This pairs with the regular-factor neighborhood bounds
to support a dominated limit of paths approaching the slit.
`SourceCriticalRootRatioTransverseBound.lean` combines these two
estimates. For every open real-type gap, a fixed vertical neighborhood
has a uniform bound on the full discriminant-derivative quotient after
multiplication by the cosine-path Jacobian. The proof also checks that
nonzero vertical shifts remain in the full canonical-root domain.
`SourceCriticalRootRatioVerticalIntegrability.lean` proves that every
nonzero vertical translate of a real-type gap avoids all periodic gap
segments. The full quotient along that translate is continuous in the
gap parameter, and its cosine-weighted pullback is interval integrable
through both endpoints. These facts provide the integrability input
for the forthcoming dominated slit limit.
`SourceCriticalRootRatioVerticalLimits.lean` identifies positive and
negative vertical translates with the oriented upper and lower gap
sides. Consequently, at each interior point of an open real-type gap,
the full discriminant-derivative quotient along those translates tends
to its corresponding canonical-root boundary quotient. These are the
pointwise input for the dominated slit limit.
`SourceCriticalRootRatioCosineIntegralLimit.lean` applies dominated
convergence in the cosine angle, where the Jacobian cancels the root's
endpoint singularity. The upper and lower vertically displaced quotient
integrals converge to their respective boundary integrals as the
displacement tends to zero. The transverse bound is strengthened to the
closed signed gap interval, including both endpoints.
`SourceCriticalRootRatioCosineBoundaryZero.lean` identifies both boundary
integrals with the previously vanishing straight gap-side integrals.
Thus each vertically displaced cosine integral tends to zero on an
open real-type gap. The remaining work for Lemma 10.11(ii) includes
relating a surrounding contour to these displaced paths and extending
the identity through the complex source neighborhood.
`SourceCriticalRootRatioHorizontalLimit.lean` makes the cosine
substitution theorem public and applies it to the full quotient. The
cosine integral is exactly the straight horizontal integral in the
signed gap parameter, so both upper and lower displaced horizontal
integrals tend to zero. Connecting them to a closed shrinking contour,
including its short endpoint connectors, remains to be proved.
`SourceStandardRootVerticalEndpointBound.lean` proves that the selected
standard root on either vertically shifted endpoint has norm at least
the square root of the real gap length times the shift magnitude.
`SourceCriticalRootRatioConnectorBound.lean` combines this with the
uniform regular-numerator bound to control the full quotient after
multiplication by that square-root weight. A contour must avoid the
branch points themselves, so its endpoint connectors will use small
arcs outside the gap.
`SourceStandardRootEndpointCircleBound.lean` proves a square-root
lower bound on circles of radius at most half the gap length around
either endpoint. `SourceCriticalRootRatioEndpointCircleBound.lean`
combines it with the bounded regular numerator to give a common
weighted quotient bound for both circles, wherever their points avoid
the periodic gaps. `SourceCriticalRootRatioOuterArcs.lean` constructs
both outward endpoint semicircles inside the full root domain for a
common small radius and applies the weighted quotient bound uniformly
along them. `SourceCriticalRootRatioOuterArcIntegral.lean` proves the
resulting half-circle integrands are interval-integrable and bounds each
arc integral by a constant times the square root of its radius. Both
arc integrals therefore vanish as the contour shrinks.
`SourceCriticalRootRatioStadiumPath.lean` concatenates the upper and
lower shifted gap segments with the two outward semicircles into an
actual closed path. A common small-radius bound keeps its full range in
the canonical-root domain. `SourceCriticalRootRatioStadiumIntegral.lean`
identifies the curve integral of that path with the signed sum of the
two displaced horizontal integrals and the two outward arc integrals.
Each piece has its established zero limit, so the actual closed
stadium-path integral tends to zero as the radius shrinks.

`PiecewiseHolomorphicLoopHomotopy.lean` supplies the homotopy tool for
this next step. It applies the open-path holomorphic homotopy identity
to four smooth pieces and cancels the moving endpoint traces at their
joins. Its affine specialization compares concatenated loops with
corners without requiring the full loop to be twice differentiable at
the joins.
`SourceGapStadiumAffine.lean` now proves this range condition for any
domain containing all stadiums in a positive radius interval. It also
proves twice-smoothness of the four pieces and identifies their affine
homotopies with the corresponding pieces at interpolated radii.
`SourceCriticalRootRatioStadiumHomotopy.lean` combines these facts to
prove radius invariance of the critical-root quotient stadium integral
for all sufficiently small positive radii. The shrinking-radius limit
then makes each such integral exactly zero at an open real-type gap.
`SourceCriticalRootRatioMidpointCircle.lean` constructs a convenient
enclosing circle centered at the real gap midpoint. A sufficiently
small positive margin beyond each endpoint gives a positive radius,
contains the whole gap in the circle's interior, and keeps the entire
circumference in the canonical-root domain.
`CircleArcCurveIntegral.lean` provides arbitrary-angle circle arcs as
twice-smooth bundled paths, identifies their curve integrals with angle
integrals, and proves that four consecutive clockwise arcs making one
full turn sum to the negative of the usual circle integral. This sets
up a four-piece deformation whose arc endpoints can match the four
stadium corners exactly.
`StadiumCircleCorners.lean` selects the circle through those four
corners and casts its four clockwise arcs to the corresponding stadium
endpoint types. The arcs are twice smooth and their integrals sum to
the negative of the standard circle integral.
`SourceCriticalRootRatioStadiumCircleHomotopy.lean` proves that the four
affine deformations avoid the periodic cuts and transfers the zero
stadium integral to its corner circle. `SourceCriticalRootRatioStadiumCircleVanishing.lean`
extends this to all sufficiently small midpoint-centered circles and,
by annulus invariance, to every larger midpoint-centered circle whose
filled disc avoids the other gaps. `SourceCriticalRootRatioNearMidpointCircle.lean`
uses an affine homotopy to give the same zero integral for any smooth
closed contour uniformly close to such a circle, within an explicit
gap-free annulus. Its circle corollary permits small changes of both
center and radius. `VerticalCircleHomotopy.lean` and
`SourceCriticalRootRatioVerticalCircle.lean` reduce any enclosing
circle at a real-type source to a real-centered enclosing circle with
the same integral. `NestedCircleHomotopy.lean` and
`SourceCriticalRootRatioRealCenteredCircleVanishing.lean` then move that
real center to the gap midpoint. The resulting theorem in
`SourceCriticalRootRatioEnclosingCircleVanishing.lean` proves zero for
every enclosing circle around an open real-type gap whose filled disc
excludes the other gaps, regardless of center. Admissible paths and
extension to nearby complex sources remain for the full statement of
Lemma 10.11(ii).
`SourceCriticalRootRatioCircleZeroRealNeighborhood.lean` fixes one
circle near an open real-type source and proves its integral is
holomorphic in the source and zero at every nearby real-type source.
`RealLineIdentity.lean` and `SourceCriticalRootRatioCircleComplexLineZero.lean`
extend that zero to complex parameters near the base point along each
real-type source direction. The remaining source step is a uniform
extension to arbitrary complex directions.
`SourceRealTypeDecomposition.lean` supplies the conjugate-reflection
involution and a norm-controlled splitting of each complex source
perturbation into two real-type parts, preparing that extension.
`RealFormIdentity.lean` turns this splitting into a local uniqueness
principle for holomorphic scalar functions on complex normed spaces.
`SourceCriticalRootRatioCircleComplexNeighborhoodZero.lean` consequently
proves that one fixed gap-enclosing circle has zero quotient integral
for every complex source in a neighborhood of an open real-type source.
The admissible noncircular contour case of Lemma 10.11(ii) remains open.
`SourceCriticalRootRatioComplexLoopZero.lean` covers smooth closed loops
with a supplied smooth gap-avoiding homotopy to the fixed circle, for
every source in that complex neighborhood.
`SourceCriticalRootRatioComplexNearCircle.lean` supplies the homotopy
automatically for smooth contours uniformly close to the fixed circle,
under explicit inner and outer gap-isolation margins.
`SourceCriticalRootRatioCircleAllGaps.lean` also covers collapsed base
gaps: the fixed-circle integral vanishes for every complex source in
a neighborhood of any real-type base potential.
`ConvexHolomorphicPathIntegral.lean` and
`SourceCriticalRootRatioHalfPlanePaths.lean` establish path
independence in the upper and lower half-planes at real-type sources.
`SourceCriticalRootRatioArbitraryHalfPlanePathLimit.lean` uses this to
show that the quotient integral along any smooth family of paths
between the vertically shifted endpoints of an open real gap tends
to zero as the height shrinks. Actual endpoint paths still require
an improper-integral argument.

`InverseSqrtIntegral.lean` proves that a measurable function with an
inverse-square-root endpoint bound is integrable, including after a
positive scale change. `SourceCriticalRootRatioEndpointConnectorIntegrable.lean`
applies the existing weighted quotient estimate to both endpoints of
an open real-type gap. The quotient is integrable on short upward and
downward vertical connectors, parametrized by distance from the
endpoint. Their integrals over shrinking initial connector pieces
also tend to zero, by continuity of the integral primitive at the
singular endpoint. Identifying these improper integrals with actual
endpoint path integrals remains to be done.

`VerticalSegmentIntegral.lean` identifies the actual curve integral of
a vertical `Path.segment` with its real-coordinate integral, in both
orientations, and transfers coordinate integrability to curve
integrability. `SourceCriticalRootRatioEndpointSegmentIntegral.lean`
applies these results at both endpoints of an open real-type gap.
The upward and downward segments starting at the branch points are
curve-integrable, and their curve integrals tend to zero as the
segments shrink. The full endpoint-to-endpoint admissible path theorem
remains open.

`SourceCriticalRootRatioEndpointDogleg.lean` constructs a concrete
endpoint-to-endpoint path through the upper half-plane: up from the
left branch point, across at positive height, and down to the right
branch point. For all sufficiently small heights its three pieces and
their concatenation are curve-integrable. Its integral is the signed
sum of the three component integrals and tends to zero as the height
shrinks. `HorizontalSegmentIntegral.lean` and
`EndpointDoglegHeight.lean` connect the curve integral to the
rectangular Cauchy identity. The source theorem in
`SourceCriticalRootRatioEndpointDoglegHeight.lean` proves the dogleg
integral is height-independent and therefore exactly zero for every
sufficiently small positive height. General admissible endpoint paths
remain open.

`SourceCriticalRootRatioLowerEndpointDogleg.lean` and
`SourceCriticalRootRatioLowerEndpointDoglegHeight.lean` give the
corresponding construction below an open real-type gap. The signed
rectangle identity proves depth invariance, and the shrinking-depth
limit makes every sufficiently shallow lower dogleg integral exactly
zero. A common positive-height range now gives curve-integrable,
zero-integral endpoint-to-endpoint paths on both sides of the gap.
General admissible paths and nearby complex sources remain open.

`SourceCriticalRootRatioEndpointDetours.lean` replaces each horizontal
crossing by any twice-smooth crossing that remains entirely in the same
open half-plane. Keeping the short vertical endpoint connectors fixed,
path independence shows that every such endpoint-to-endpoint detour is
curve-integrable and has exactly zero integral. The result applies to
both upper and lower crossings. Arbitrary admissible endpoint paths and
nearby complex sources remain open.

`SourceCriticalRootRatioOpenPathHomotopy.lean` proves that a smooth
fixed-endpoint deformation through the complement of all periodic gaps
preserves the critical-root quotient integral of an open path.
`SourceCriticalRootRatioHomotopyDetours.lean` applies it to the actual
singular endpoint paths: at sufficiently small upper or lower connector
lengths, any smooth crossing homotopic to the straight crossing through
that gap complement is curve-integrable and has integral zero. The
crossing may leave its original half-plane. General admissible endpoint
paths and nearby complex sources remain open.

`SourceCriticalRootRatioContinuousOpenPathHomotopy.lean` uses compactness
and a uniform gap-avoidance buffer to prove local constancy of the
quotient integral on smooth open paths. A homotopy need therefore only
be continuous as a two-parameter map, provided every slice is twice
smooth and avoids the gaps. `SourceCriticalRootRatioContinuousHomotopyDetours.lean`
applies this to upper and lower endpoint detours with short vertical
connectors, again giving curve integrability and exactly zero integral.
General admissible endpoint connectors and nearby complex sources
remain open.

`SourceCriticalRootRatioEndpointPuncturedBound.lean` extends the
inverse-square-root estimate from endpoint circles to every point of a
small punctured endpoint neighborhood outside the spectral gaps.
`SingularEndpointPathIntegrability.lean` gives a general criterion for
integrating a one-form with this parameter singularity. Applying both,
`SourceCriticalRootRatioCurvedEndpointConnector.lean` proves that a
smooth curved connector beginning at either open-gap branch point is
curve-integrable when it avoids the gaps, remains in that neighborhood,
and departs from the branch point at a linear rate. Equality of general
endpoint-path integrals remains open.

`SourceCriticalRootRatioCurvedEndpointDetour.lean` now composes two
such curved connectors with any smooth crossing in the full root
domain. The resulting path starts and ends at the singular gap branch
points, is curve-integrable, and its integral is exactly the left
connector integral plus the crossing integral minus the right
connector integral. Showing this sum vanishes for general curved
connectors remains open.

`SingularEndpointPathIntegrability.lean` now also bounds the norm of a
curve integral from a square-root weighted bound on its pulled-back
one-form. `SourceCriticalRootRatioCurvedConnectorIntegralBound.lean`
applies this at both open-gap endpoints: the connector integral is
bounded explicitly by its maximum speed divided by the square root of
its radial departure rate. In particular, a family of short curved
connectors whose speed and departure both scale with its size has
integral tending to zero. Comparing full paths with curved connectors
to a zero-integral dogleg remains open.

## Latest milestone: shrinking complete curved detours

`SourceCriticalRootRatioCurvedDetourLimit.lean` proves that complete
branch-point-to-branch-point paths have integrals tending to zero as
positive height or depth shrinks. Both endpoint connectors may curve,
provided their radial departure and speed have uniform bounds
proportional to the height or depth. The middle path may be any smooth
crossing contained in the corresponding open half-plane. The proof
combines the curved connector estimates with the crossing integral
limit and the exact three-piece path integral decomposition. Exact
zero for a fixed general curved detour remains open.

## Latest milestone: fixed-height curved-detour comparison

`SourceCriticalRootRatioCurvedDetourComparison.lean` identifies the
integral of a curved detour at a fixed small height or depth. For any
smooth crossing in the corresponding half-plane, it equals the left
connector's integral minus its vertical reference integral, minus the
same difference at the right connector. Thus the crossing creates no
additional error; the comparison isolates the exact endpoint work
needed to extend fixed-height zero-integral results to curved paths.

## Latest milestone: exact-zero piecewise curved detours

`ConvexHolomorphicPrimitive.lean` evaluates a holomorphic one-form
along a `C¹` path in an open convex domain by a primitive's endpoint
values. `SourceCriticalRootRatioHalfPlanePrimitive.lean` supplies such
primitives above and below the real axis and proves that regular
piecewise paths telescope across corners. Applying this,
`SourceCriticalRootRatioPiecewiseCurvedDetour.lean` proves exact zero
for complete paths that first leave both singular gap endpoints along
short vertical segments, then follow arbitrary `C¹` curved tails and
a crossing within one open half-plane. Exact zero for connectors
curving immediately at the branch points remains open.

## Latest milestone: primitive limits at open-gap endpoints

`IntegrableDerivativeBoundary.lean` proves that a function with an
integrable derivative on a punctured interval has a finite one-sided
limit and an integral formula for its values. Applied to the quotient
primitives, `SourceCriticalRootRatioPrimitiveVerticalLimit.lean`
establishes finite limits along upward and downward vertical rays at
both endpoints of every open real-type gap.
`SourceCriticalRootRatioPrimitiveCommonBoundary.lean` proves that the
left and right ray limits agree within each half-plane: their
difference is the horizontal quotient integral, which tends to zero.
`ConvexHolomorphicPrimitive.lean` also evaluates integrable singular
endpoint paths when the primitive has the required boundary limit.
Establishing a limit along every half-plane approach to an endpoint
remains necessary for immediately curved connectors.

## Latest milestone: pathwise limits for curved detours

`ConvexHolomorphicPrimitive.lean` now proves that a primitive has a
finite limit along any smooth, integrable path with a singular starting
point, and evaluates the path integral as the endpoint value minus
that limit. `SourceCriticalRootRatioCurvedConnectorPrimitiveLimit.lean`
applies this to linearly departing curved connectors in either open
half-plane. For a complete detour, `SourceCriticalRootRatioCurvedDetourPrimitiveDefect.lean`
shows its integral equals the right connector's pathwise limit minus
the left connector's. The next milestone identifies those limits.

## Latest milestone: exact zero for immediately curved detours

`SquareRootPrimitiveBoundary.lean` proves that a primitive with
inverse-square-root derivative growth at a real boundary point has a
full half-plane limit whenever it has a vertical-ray limit. It compares
each nearby point to the ray by three short regular segments.
`SourceCriticalRootRatioPrimitiveBoundary.lean` applies this to the
critical-root quotient: within each half-plane, the primitive has the
same boundary value at both endpoints of an open real-type gap.
`SourceCriticalRootRatioCurvedDetourZero.lean` then proves that every
sufficiently short detour with smooth, linearly departing, immediately
curved endpoint connectors and a smooth crossing in that half-plane
has exactly zero quotient integral. The upper and lower results are
separate; arbitrary paths outside these connector assumptions remain
to be treated.

## Latest milestone: zero for arbitrary integrable half-plane paths

`ConvexHolomorphicPrimitive.lean` now proves that an integrable smooth
path between two singular boundary points has zero one-form integral
when its primitive has the same boundary value at both ends.
`SourceCriticalRootRatioSmoothEndpointPathZero.lean` applies this to
any `C¹` curve-integrable path across an open real-type gap whose
interior stays entirely above or entirely below the real axis.

For paths with corners, `SingularEndpointPrimitiveDetour.lean` proves
a three-piece cancellation theorem. Its quotient specialization in
`SourceCriticalRootRatioIntegrableDetourZero.lean` allows arbitrary
smooth, curve-integrable singular connectors and a smooth crossing in
one half-plane. These results do not require the earlier shortness or
linear-departure assumptions; integrability of each singular
connector remains an explicit hypothesis.

## Latest milestone: weighted upper gap-side action integral

`SourceActionGapSideIntegral.lean` identifies the recentered weighted
upper-side path integral with the weighted canonical-root integral over
an open real-type gap. The path integrand is interval integrable through
both endpoints, doubly truncated paths converge to its full value, and
that value is real and nonzero. Relating this boundary integral to the
enclosing action circle and fixing its orientation remain to be proved.

## Latest milestone: weighted action circle and stadium

`SourceCriticalRootRatioStadiumCircleHomotopy.lean` now gives the
stadium-to-corner-circle integral equality for any integrand
differentiable on the cut-free root domain. The prior quotient result
is a specialization. `SourceActionStadiumCircle.lean` applies this to
the recentered weighted quotient and proves that the positively
oriented action circle is the negative normalized integral over the
clockwise stadium. The remaining boundary step is to take the
weighted stadium integral to the two gap sides as its radius shrinks.

## Latest milestone: weighted endpoint arcs vanish

`SourceActionOuterArcLimit.lean` identifies the action's weighted
endpoint semicircle integrals with bundled curve integrals and gives
both an explicit square-root radius bound. Thus both outward arc
contributions tend to zero as the stadium shrinks. The weighted upper
and lower horizontal integrals still need to be identified with their
gap-side boundary limits before the stadium limit can be assembled.

## Latest milestone: weighted horizontal boundary limits

`SourceActionCosineIntegralLimit.lean` proves dominated convergence of
the recentered weighted quotient from positive and negative vertical
displacements to the respective upper and lower canonical-root
boundary integrals. `SourceActionHorizontalLimit.lean` transfers both
limits to the ordinary straight horizontal path integrals by cosine
substitution. The boundary values still need to be matched to the
gap-side path integrals when assembling the shrinking stadium limit.

## Latest milestone: weighted boundary values and gap sides

`SourceActionBoundaryGapSide.lean` identifies both weighted cosine
boundary integrals with their straight gap-side path integrals. The
upper value is real and nonzero on every open real-type gap, and the
lower value is its negative. Together with the horizontal limits and
vanishing endpoint arcs, these are the boundary terms needed to
evaluate the shrinking weighted stadium.
