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

## Latest milestone: shrinking weighted stadium and nonzero action

`SourceActionStadiumLimit.lean` decomposes the recentered action
stadium into its four oriented pieces and proves that its integral
tends to twice the upper gap-side boundary value. That value is real
and nonzero on an open real-type gap. Combining the limit with the
stadium-to-circle deformation, `SourceActionCircleNonzero.lean` proves
that the action on all sufficiently small corner circles is nonzero.

## Latest milestone: exact action on small gap circles

`SourceActionMidpointCircleValue.lean` proves radial invariance of the
weighted action on cut-avoiding annuli, then identifies the action on
every sufficiently small midpoint circle with minus twice the upper
gap-side boundary integral divided by π. The formula shows that these
actions are real and nonzero on every open real-type gap. Establishing
the canonical-root orientation needed for a strictly positive sign
remains open.

## Latest milestone: real exterior signs of standard-root factors

`SourceStandardRootRealExteriorSign.lean` shows that the principal
standard-root factor is positive to the left of its real periodic
gap and negative to the right. Strict ordering of canonical gaps
then determines the real-part sign of every unselected factor at a
point inside the chosen gap. Combining these factor signs in the
normalized omitted product is the next orientation step toward
positivity of the action.

## Latest milestone: reality of the omitted root product

`SourceStandardRootOmittedRealGap.lean` proves that each finite
symmetric omitted-root cutoff is real at an interior point of the
selected real gap. Pointwise convergence passes this reality to the
infinite product. Its sign now reduces to counting the negative
normalized factors in the finite cutoffs and passing their common
sign to the limit.

## Latest milestone: normalized factor signs

`SourceStandardRootNormalizedFactorSign.lean` identifies the signs
introduced by the exceptional zero-mode denominator and the positive
and negative integer denominators. For every index other than the
selected gap, it proves the sign of the normalized real standard-root
factor in all four index-order cases. The finite symmetric product
can now be grouped into positive and negative paired blocks to
establish its parity sign.

## Latest milestone: positive omitted product at index zero

`SourceStandardRootOmittedZeroPositive.lean` proves that every
normalized factor retained after omitting index zero is positive on
the open central real gap. Its finite symmetric cutoffs are positive;
their limit is nonnegative and, because the omitted product cannot
vanish on that gap, strictly positive. This fixes the canonical-root
orientation for the central gap and supplies the base case for the
general index-parity calculation.

## Latest milestone: central upper canonical-root orientation

`SourceCanonicalRootZeroUpperSign.lean` combines the positive central
omitted product with the positive upper-side standard-root factor.
It proves that the full canonical-root upper boundary value is
strictly positive and equals twice the positive arcosh square root
at every interior point of an open central real gap. The identity is
also stated in real spectral coordinates for the weighted action
integral.

## Latest milestone: positive central action

`SourceActionZeroGapPositive.lean` proves that the central upper
weighted boundary integral is the strictly negative real arcosh
area. The exact small-circle formula reverses its sign, proving
that the action is real and strictly positive on every sufficiently
small midpoint circle around an open central real-type gap. Extending
the omitted-product orientation by index parity remains necessary
for the corresponding theorem at every gap.

## Latest milestone: symmetric omitted-pair signs

`SourceStandardRootOmittedPairSigns.lean` expresses each real
symmetric pair of normalized factors in the omitted product. It
proves that the pair indexed by `j+1` is negative exactly when
`j+1 < |n|`; the omitted pair and every later pair are positive.
The remaining parity calculation must include the zero-mode
prefactor and the finite product of those negative pairs.

## Latest milestone: finite omitted-product parity

`SourceStandardRootOmittedPrefactorSign.lean` proves that the zero-mode
prefactor is negative on every noncentral real gap. The paired factors
are real, and `SourceStandardRootOmittedFiniteParity.lean` counts their
signs: once the cutoff reaches a nonzero index `n`, multiplying its
real omitted product by `(-1)^|n|` gives a strictly positive number.
The next step is to pass this sign to the nonvanishing infinite
product, then fix the canonical-root orientation on every gap.

## Latest milestone: infinite omitted-product parity

`SourceStandardRootOmittedParitySign.lean` passes the finite sign to
the infinite standard-root product on every open real-type gap. The
product is real and nonzero there, so its real part has the strict
sign `(-1)^|n|`, including the central index. This is the orientation
input needed to identify the upper canonical-root branch and prove
positivity of the action for arbitrary gap indices.

## Latest milestone: all-index upper canonical-root orientation

`SourceCanonicalRootUpperParitySign.lean` combines the omitted-product
sign with the positive upper-side factor. On the interior of every
open real-type gap, the upper canonical root is exactly the positive
arcosh square root times `(-1)^|n|`. The same identity is available in
real spectral coordinates for the weighted action integral.

## Latest milestone: positive actions on all open real gaps

`SourceDiscriminantDerivativeParity.lean` makes the discriminant
derivative's parity sign explicit. In
`SourceActionAllGapPositive.lean`, that sign cancels the upper
canonical-root sign in their quotient. The upper weighted boundary
integral is the negative real arcosh area, so every sufficiently
small midpoint circle around an open real-type gap has a strictly
positive real action. This extends the earlier central-gap result
to every integer gap index.

## Latest milestone: action characterization on enclosing midpoint circles

`SourceActionMidpointCircleCharacterization.lean` transfers small-circle
positivity to every midpoint-centered circle enclosing the selected
real gap whose filled disc avoids the other gaps. On this class of
circles, the action is real and nonnegative, and it vanishes exactly
when the selected periodic gap collapses. A contour-independent action
for the full admissible circuit class remains to be formalized.

## Latest milestone: existence of isolating midpoint circles

`SourceActionMidpointCircleExistence.lean` uses strict separation from
the neighboring real spectral gaps to construct a positive range of
midpoint circles whose filled discs avoid all other gaps. On every
circle in that range, the action is real and nonnegative, and it
vanishes exactly when the selected gap collapses. This gives the
real-type sign and zero criterion of Lemma 11.1 for these explicit
circuits; extending the definition to arbitrary admissible circuits
remains open.

## Latest milestone: an indexed action at real-type sources

`SourceRealAction.lean` selects a midpoint circle from the radius
range where the action is constant and defines a complex-valued
indexed action for each real-type source. It proves independence from
the circle inside that range and shows that the value is real and
nonnegative, vanishing exactly for a collapsed periodic gap. The
construction below connects this real-source value to a complex-
differentiable action on nearby complex sources. Extension to arbitrary
admissible circuits remains open.

## Latest milestone: fixed enclosing-circle representation

`SourceRealActionEnclosingCircle.lean` proves that the indexed
real-source action equals the contour integral on any enclosing
midpoint circle whose filled disc avoids the other periodic gaps.
This representation permits a fixed contour at a chosen real-type
source to be used for the subsequent local analytic extension.

## Latest milestone: local holomorphic circle action through a real action

`SourceRealActionLocalHolomorphic.lean` chooses a fixed midpoint circle
representing each indexed real-source action and proves that its
circle integral is complex Fréchet differentiable on a source
neighborhood. Along every complex affine source line through the
base point, this circle action is analytic. A common complex-
differentiable action across overlapping neighborhoods is constructed
below; full Banach-space analyticity and arbitrary admissible circuits
remain open.

## Latest milestone: stable midpoint circle near a real action

`SourceRealActionLocalCircleStability.lean` proves that the specific
midpoint circle representing an indexed real action remains an
isolating contour for all sources in an open complex neighborhood.
The selected gap stays inside the circle, while its filled disc
continues to avoid every other gap. This supplies the geometric
stability needed to identify the local circle action with nearby
real-source actions.

## Latest milestone: local complex extension of the indexed real action

`SourceRealActionLocalAgreement.lean` proves that one fixed circle
computes the indexed action at every nearby real-type source. The
same circle action is complex Fréchet differentiable throughout an
open complex source neighborhood. The proof nests a moving midpoint
circle inside the fixed disc and applies contour invariance.

## Latest milestone: line analyticity and real sign on a neighborhood

`SourceRealActionLocalLineAnalytic.lean` proves that the fixed-circle
extension is analytic along every complex affine source line through
each point of its open neighborhood. At every real-type source there,
its value is real and nonnegative, and it vanishes exactly when the
selected periodic gap collapses.

## Latest milestone: uniqueness of local action germs

`SourceRealActionLocalOverlap.lean` applies the norm-controlled
real-form identity principle to complex-differentiable source
functions. Any two fixed-circle extensions representing the same
indexed action on real-type sources agree on a complex neighborhood
of each real-type point in their overlap. This proves compatibility
of the locally defined action germs.

## Latest milestone: compatibility across convex overlaps

`SourceRealActionConvexOverlap.lean` strengthens local uniqueness:
two complex-differentiable extensions of the indexed real action
agree throughout any convex overlap containing a real-type source.
The proof restricts to complex lines from that source and uses the
one-variable analytic identity principle.

## Latest milestone: compatible action charts on source balls

`SourceRealActionBallOverlap.lean` puts every local action extension
on a ball centered at a real-type source. The real-part projection
contracts distance to such centers, so every nonempty overlap of
these balls contains a real-type source. The corresponding fixed-circle
action formulas therefore agree throughout the overlap. These ball
charts provide the compatibility needed to glue a complex action.

## Latest milestone: a glued complex action near all real-type sources

`SourceComplexAction.lean` glues all valid real-centered ball charts
into a single complex action at each gap index. Its open domain
contains every real-type source, and the action is complex Fréchet
differentiable there. It agrees with every fixed-circle chart on that
chart's ball and restricts to the indexed real action.

## Latest milestone: connected domain and real properties of the complex action

`SourceComplexActionProperties.lean` proves that the glued action's
open domain is connected: each chart ball meets the connected real-type
source locus. The action is analytic along every complex affine line
through every point of that domain. On real-type sources it is real,
nonnegative, and zero exactly when the selected periodic gap collapses.

## Latest milestone: uniqueness of the complex action extension

`SourceComplexActionUniqueness.lean` proves that the glued function is
the unique complex Fréchet differentiable function on its domain that
agrees with the indexed action at every real-type source. Uniqueness
is checked on each real-centered convex chart ball and then covers
the entire domain.

## Latest milestone: explicit source derivative under the action circle integral

`ParametricCircleIntegral.lean` now retains the Fréchet derivative
constructed by differentiation under a fixed circle integral.
`SourceActionCircleSourceFDeriv.lean` applies it to the weighted
critical-root quotient and gives the action's source derivative as
an explicit angle integral on a complex source neighborhood. The
spectral integration-by-parts simplification needed for Lemma 11.1's
gradient formula remains to be proved.

## Latest milestone: commuting source and spectral derivatives

`MixedSpectralSourceDerivative.lean` proves that the source Fréchet
derivative and the spectral derivative commute for a jointly analytic
family on an open product domain. `SourceDiscriminantMixedDerivative.lean`
applies this to the canonical discriminant. Combining this identity
with the canonical-root derivative and contour integration by parts
is the next step toward Lemma 11.1's gradient formula.

## Latest milestone: source and spectral derivatives of the canonical root

`SquareRootDerivative.lean` differentiates a nonvanishing square root
from the identity `Q² = Δ² − 4`. `SourceCanonicalRootSourceFDeriv.lean`
applies it to the canonical root away from the moving periodic gaps,
giving both its source Fréchet derivative and spectral derivative as
`Δ / Q` times the corresponding discriminant derivative. These formulas
prepare the quotient simplification inside the action integral.

## Latest milestone: source derivative of the critical-root quotient

`QuotientDerivative.lean` gives the directional Fréchet derivative of
a nonvanishing scalar quotient. `SourceCriticalRootRatioSourceFDeriv.lean`
applies it to the action integrand `Δ′ / Q` and proves the pointwise
identity `D_source(Δ′ / Q) = ∂_z((D_source Δ) / Q)` off the moving gap
cuts. The remaining contour step is to integrate this identity by
parts in the weighted action circle.

## Latest milestone: integration by parts on the action circle

`CircleIntegralIntegrationByParts.lean` proves a closed-circle identity
for `∮ z f′(z) dz` using only analyticity near the circle; enclosed gap
cuts cause no problem. `SourceDiscriminantVariationCircle.lean` shows
that `(D_source Δ) / Q` meets those hypotheses, and
`SourceActionCircleGradientIntegrand.lean` concludes that the circle
integral of the source derivative of `z Δ′ / Q` equals the negative
circle integral of `(D_source Δ) / Q`. The remaining step is to
identify this circle integral with the action's source Fréchet
derivative from differentiation under the integral.

## Latest milestone: the fixed-circle action gradient formula

`ParametricCircleIntegral.lean` now identifies each directional source
Fréchet derivative of a jointly analytic circle integral with the
circle integral of the directional derivative. Combining this with
the contour integration-by-parts result,
`SourceActionCircleGradient.lean` proves equation (2.17)'s negative
normalized discriminant-variation formula for any fixed circle that
avoids the periodic cuts at a real-type source. Transferring the
formula to the glued indexed action is the next step.

## Latest milestone: indexed complex-action gradient at real sources

`SourceComplexActionGradient.lean` transfers the contour formula from
each fixed-circle chart to the glued indexed complex action. At every
real-type source and gap index, it selects one isolating circle on
which the source Fréchet derivative is the negative normalized
integral of the discriminant variation over the canonical root, in
all complex source directions. This establishes the gradient formula
of Lemma 11.1 for the action extension at real-type sources. Extending
the formula across its complex domain and proving full Banach-space
analyticity remain separate tasks.

## Latest milestone: contour invariance of the action gradient

`SourceActionGradientContourHomotopy.lean` proves that the gradient
integral of `(D_source Δ) / Q` is unchanged under smooth homotopies
that avoid all periodic cuts. It specializes this to nested
isolating circles and to two circles inside a common larger
isolating circle. This removes the dependence on the chosen chart
contour wherever the stated geometric comparison applies.

## Latest milestone: normalized action on noncollapsed gaps

`SourceNormalizedActionNoncollapsed.lean` defines the a priori
quotient `Iₙ / γₙ²` and proves, at every real-type source with a
nonzero selected gap, complex Fréchet differentiability and
analyticity along each complex source line. It also combines the
action contour gradient with the quotient rule to give the
directional derivative of this normalized action. The removable
extension through collapsed gaps and the uniform estimates in
Theorem 11.2 remain open.

The same file now identifies an open complex domain for each indexed
quotient: the action domain intersected with the analytic and nonzero
locus of the squared periodic gap. Every real-type source with a
noncollapsed selected gap belongs to this domain, and the quotient is
complex differentiable throughout it.

`SourceComplexActionZeroLocus.lean` proves that, on a common complex
neighborhood of the real-type sources, the glued indexed action vanishes
whenever its selected squared gap is zero. The proof transfers the
collapsed-gap contour integral result through an action ball chart. It
also combines this zero-locus statement with analyticity of every
squared gap on one common neighborhood. Constructing the analytic
quotient at those zeros remains open.

`SourceNormalizedActionModel.lean` derives the open real-gap integral
formula corresponding to (2.19): four times the raw quotient is a
shifted cosine moment of the complementary spectral factor. It computes
the universal moment as `1 + 2u²` and gives the exact decomposition into
that moment and the factor-error integral. This supplies the analytic
identity behind the leading `1` in Theorem 11.2; controlling the error
uniformly and extending the quotient through collapsed complex gaps
remain to be proved.

`SourceNormalizedActionEstimate.lean` turns that identity into an
explicit bound. If the complementary factor differs from one by at most
`ε` along the selected gap, then the deviation of `4Iₙ/γₙ²` from one
is bounded by a term quadratic in the gap times the critical squared-gap
quotient, plus a controlled multiple of `ε`. The normalized critical
offset is identified exactly as twice the gap times that quotient.

`SourceNormalizedActionTailBound.lean` supplies that factor bound for
all sufficiently distant signed indices, locally uniformly near each
real-type source. It transports the deleted single-root product estimate
from isolating discs to every cosine-parametrized point of the selected
gap, then obtains the corresponding explicit normalized-action bound on
open real-type gaps. The full `ℓ^{p/2} + ℓ^{1+}` asymptotic and analytic
extension through collapsed gaps still remain open.

`SourceNormalizedActionSequenceMajorants.lean` expresses the critical
offset at every Banach exponent `q ≥ p/2` as the squared gap times its
bounded critical quotient. It transfers the sharper deleted-product
disc estimate to the cosine path. The gap-squared critical term is itself
an `ℓ^{p/2}` sequence, and the variable factor-error prefactor is bounded
by the source sequence norms. Hence the normalized-action deviation on
all sufficiently distant open real-type gaps has a genuine two-sequence
`ℓ^q + ℓ^{p/2}` majorant. The underlying factor majorants now have locally
uniform sequence-norm bounds, including when `p/2 < 1`. The critical
action term also has a locally uniform `ℓ^{p/2}` norm bound. A quantitative
quasi-norm addition estimate combines them into one locally uniform
`ℓ^q + ℓ^{p/2}` action majorant on distant open real-type gaps. The
remaining work is to extend the quotient analytically across collapsed
complex gaps and transfer the estimate to that extension.

`SourceNormalizedActionPositive.lean` proves the real-type positivity
part of Theorem 11.2 on every noncollapsed gap. The indexed action and
gap are real there, the action is strictly positive, and division by
the squared gap preserves positivity. Complex differentiability gives
a neighborhood on which the quotient's real part remains above half
its positive value at the base source. The raw quotient has value zero
at a collapsed gap by Lean's division convention; that value is not
the claimed analytic extension, which still needs to be constructed.

`SourceNormalizedActionCollapseEstimate.lean` isolates the limiting
calculation in (2.19). For a constant target factor `c`, it bounds the
distance of four times the open-gap quotient from `c` by the uniform
cosine-path factor error and a term quadratic in the gap. The
critical-offset term is proved to tend to zero near every collapsed
real-type source. Thus, if the deleted factor converges uniformly along
the shrinking path,
the quotient tends to the explicit candidate
`I * sourceCriticalRootRatioExtension(τₙ) / 4`. The next files prove
the uniform source continuity needed for this limit.

`SourceCriticalDisplacementContinuity.lean` upgrades fixed-coordinate
critical-root continuity to continuity of the full `ℓp` displacement
sequence. It uses the generic coordinate-plus-uniform-tail criterion in
`UniformTailContinuity.lean`, the locally uniform periodic gap and
midpoint tails, and the exact squared-gap critical-offset formula.
`SourceNormalizedActionFactorContinuity.lean` then applies joint
analyticity of the deleted quotient: its cosine-path factor converges
uniformly to the midpoint factor as a real-type gap collapses. This
removes the extra hypothesis from the preceding limit theorem and
gives an explicit normalized action continuous on the real-type source
locus, with value `I * sourceCriticalRootRatioExtension(τₙ) / 4` at a
collapsed gap. Extending this function analytically across collapsed
complex gaps, and transporting the sequence estimates to that
extension, remain open.

`SourceNormalizedActionCircleKernel.lean` now gives an exact complex
source factorization on a fixed isolating circle around each real-type
source and selected index. Writing the critical point as `τₙ + γₙ² Bₙ`,
it rationalizes the selected standard root and separates a holomorphic
term whose contour integral is zero. The remaining circle integral is
defined even when `γₙ = 0`, and the action equals `γₙ²` times this
candidate throughout a complex source neighborhood. Analyticity of the
candidate as a function of the source and agreement with the existing
real-type collapsed-gap value are addressed in the following files.

`SourceNormalizedActionCircleAnalytic.lean` proves joint analyticity of
that rationalized integrand at exterior spectral points over real-type
sources. A common neighborhood of the fixed circle then makes the
contour candidate complex Fréchet differentiable in the source and
analytic along every complex source line, while retaining the exact
action factorization. The following files identify this local
candidate with the glued indexed action; stronger Banach analyticity
and asymptotic conclusions of Theorem 11.2 still require proof.

`SourceCriticalRootRatioAnyCircleZero.lean` extends the zero integral
of the unweighted critical-root quotient to a prescribed isolating
circle after shrinking the source neighborhood. In
`SourceNormalizedActionGlued.lean` that circle is the one used by an
indexed-action ball chart. The glued complex action therefore equals
the squared periodic gap times the differentiable normalized contour
candidate throughout one complex neighborhood of each real-type
source. On noncollapsed gaps the candidate equals the raw quotient.

`SourceNormalizedActionCollapsedCircleValue.lean` evaluates the
rationalized contour candidate at a zero gap by the Cauchy integral
formula. The holomorphic constant term disappears, leaving exactly
`I * sourceCriticalRootRatioExtension(τₙ) / 4`, the previously defined
collapsed-gap value. Consequently the candidate agrees with the
continuous normalized-action extension on nearby real-type sources,
while it remains complex Fréchet differentiable on a neighborhood
that also contains collapsed complex sources. Full Banach analyticity
and the sequence asymptotics of Theorem 11.2 remain open.

`SourceNormalizedActionComplexExtension.lean` gives the resulting
chart-independent complex function a direct name. The historical
piecewise normalized-action formula equals the differentiable contour
candidate for all nearby complex sources, at zero and nonzero gaps.
For each fixed index, a single open complex neighborhood of the whole
real-type locus supports this differentiable extension and the exact
identity `Iₙ = γₙ² · (Iₙ/γₙ²)_ext`. Its restriction to every complex
source line is analytic. A neighborhood uniform in the index, full
Banach-space analyticity, and Theorem 11.2's sequence asymptotics are
still to be proved.

`SourceNormalizedActionComplexDerivative.lean` differentiates this
chart-independent extension through its fixed contour integral. On
one complex neighborhood of each real-type source, including points
with a collapsed selected gap, its Fréchet derivative is the contour
integral of the source derivative of the rationalized integrand. This
provides a derivative formula without dividing by the squared gap.

`SourceNormalizedActionCollapsedNonzero.lean` uses simplicity of the
discriminant's real critical points to show that deleting the selected
critical factor leaves a nonzero product at that root. At a collapsed
gap the normalized action is therefore nonzero. Together with the
existing positivity result for open real gaps, this gives a
nonvanishing normalized action at every real-type source and, for
each fixed index, on one open complex neighborhood of the entire
real-type locus. The exact squared-gap factorization holds there.
The next files establish reality and positivity of the collapsed
value; an index-uniform complex neighborhood remains open.

`SourceNormalizedActionCollapsedReal.lean` proves that the deleted
critical and standard-root products are real at a collapsed real gap,
so the complex normalized-action extension is real on the full
real-type locus. `SourceNormalizedActionFree.lean` matches the two
free deleted products factor by factor and gives the value `1/4` at
zero potential for every index. Connectedness and nonvanishing then
force positivity everywhere on the real-type locus in
`SourceNormalizedActionCollapsedPositive.lean`. For each fixed index,
one complex neighborhood has positive real part and supports a
nonvanishing, complex Fréchet-differentiable principal square-root
coordinate; its restriction to each complex source line is analytic.
The index-uniform neighborhood, full Banach analyticity, and sequence
asymptotics in Theorem 11.2 remain open.

`SourceNormalizedActionExtensionSequenceMajorants.lean` transports the
factor estimates to the normalized-action extension at every distant
real-type gap, including collapsed gaps. Locally in the source, its
deviation from `1/4` has `ℓq + ℓ^(p/2)` pointwise majorants with
uniformly bounded sequence norms. The common complex neighborhood and
the corresponding estimates for non-real-type sources remain open.

`SourceNormalizedActionCircleExpansion.lean` gives an exact complex
contour expansion of the normalized-action extension near each
real-type source and fixed index. Its leading term is one quarter of
the deleted factor at the gap midpoint; the remaining contour integral
has an explicit factor of the squared gap and is defined at complex
collapsed gaps. This reduces the complex-source sequence estimate to
bounding that correction integral uniformly over distant indices.

`SourceNormalizedActionCircleCorrectionBound.lean` proves that a small
complex squared gap keeps the selected root and every denominator of
the rationalized correction separated from zero on a contour. The
correction admits an explicit bound in terms of the spectral distance
and critical-gap quotient. Integrating it gives a quantitative
complex-source estimate for the normalized action on each fixed-index
chart. A common family of distant-index circles and uniform bounds
for their deleted factors are still needed for Theorem 11.2.

`SourceNormalizedActionUniformTailCircles.lean` constructs that common
family of circles. On one complex source neighborhood, every
sufficiently distant signed index has an eighth-π circle around its
free lattice point that encloses the moving periodic segment. Its
filled disc lies in the omitted-root domain, so the deleted factor is
analytic there; the contour also satisfies uniform midpoint
separation and small squared-gap bounds.

`SourceNormalizedActionFactorDiscMajorants.lean` transfers the
single-root quotient disc estimates to the deleted factor for nearby
complex sources. On the same family of distant free-centered circles,
its deviation from the free value has `ℓq + ℓ^(p/2)` pointwise
majorants whose sequence norms are uniformly bounded on one source
neighborhood. Consequently the deleted factor has a uniform scalar
bound on all those circles.

`SourceNormalizedActionUniformCircleCorrection.lean` applies the
complex contour correction estimate on those common circles. It
combines uniform midpoint separation, a local bound for the critical
gap quotient, and the deleted-factor bound to show that the contour
candidate differs from its midpoint term by at most a common constant
times the squared gap, for every sufficiently distant index and every
nearby complex source, including collapsed gaps.

`SourceNormalizedActionUniformCircleMajorants.lean` combines that
correction with the deleted-factor estimate at the moving midpoint.
The common-circle candidate now has locally uniform
`ℓq + ℓ^(p/2)` majorants at nearby complex sources, including
collapsed gaps and the quasi-Banach range `p/2 < 1`. It remains to
identify the candidate with the chart-independent normalized-action
extension on one common source neighborhood.

`SourceNormalizedActionCircleHomotopy.lean` proves contour invariance
of the normalized-action candidate under nested gap-enclosing circles,
and for two circles inside a common valid outer disc. The homotopy
stays outside the selected segment and inside the outer disc, where
the deleted factor is analytic. This works for complex collapsed gaps
without dividing by the squared gap.

`SourceRealActionUniformTailCircle.lean` makes that comparison on the
real-type locus. A π/16 circle centered at a distant gap midpoint
encloses the selected segment and fits inside the common free-centered
π/8 circle. The existing midpoint-circle formula and contour
invariance then show, with one source neighborhood and one cutoff,
that each distant free-centered circle computes the indexed real
action.

`SourceNormalizedActionUniformCircleRealAgreement.lean` identifies
the normalized contour candidate on those circles with the existing
normalized-action extension at every distant real-type gap. The
unweighted critical-root quotient integral vanishes on a valid
circle for both open and collapsed real gaps; the action factorization
handles open gaps, and the midpoint formula handles collapsed ones.
The cutoff and source neighborhood are common to all distant indices.

`SourceNormalizedActionUniformCircleLocalComplexAgreement.lean` proves
complex differentiability of the normalized candidate on any
prescribed valid circle near a real-type base source. Real-form
uniqueness then extends the common-circle identity to a complex
neighborhood for each fixed distant index. The common-ball result below
removes the index dependence from this neighborhood.

`SourceDistantCriticalPointsAnalyticNeighborhood.lean` gives one complex
source neighborhood and one cutoff on which every distant canonical
critical coordinate is analytic. It combines a uniform canonical
labeling, local simplicity of all critical roots, and the analytic
implicit-root theorem. This removes the index-dependent analyticity
neighborhood for the critical coordinates; uniformity for the remaining
normalized-action factors is still needed.

`SourceDistantCriticalGapQuotientAnalyticNeighborhood.lean` uses that
common critical-point neighborhood to make every distant critical
gap quotient analytic on one complex source neighborhood. A shared
isolating-disc family keeps the deleted product and its derivative in
their analytic domain and makes the offset coefficient nonzero, even
at complex collapsed gaps. The subsequent circle modules establish a
common analytic domain for the full normalized-action contour formula.

`SourceDistantCriticalPointsFreeCircles.lean` puts every distant critical
point strictly inside its free-centered π/8 circle on one complex
source neighborhood. `SourceDistantCriticalRootRatioJointAnalyticCircles.lean`
uses this separation to make the deleted spectral factor jointly
analytic along all those circles on a common neighborhood.

`SourceDistantNormalizedActionCircleIntegrandAnalytic.lean` combines the
uniform critical gap quotient, symmetric periodic data, and deleted
factor to prove joint analyticity of the rationalized normalized-action
integrand on every distant free circle, including collapsed complex
gaps. `SourceDistantNormalizedActionCircleCandidateAnalytic.lean` then
differentiates under the contour integral and obtains one complex
source neighborhood where all distant circle candidates are
differentiable. The common-ball identity below identifies them with
the chart-independent normalized action.

`SourceDistantCriticalRootRatioCircleZero.lean` proves that the
unweighted discriminant-derivative quotient has zero integral on all
distant free circles throughout one complex source ball. It extends
the existing local vanishing for each index along complex affine
source lines using the identity principle.

`SourceDistantActionFreeCircleCharts.lean` constructs action charts on
the same source ball and free-centered circles for all distant
indices. The glued complex indexed action therefore equals the circle
action there. `SourceNormalizedActionUniformCircleComplexAgreement.lean`
combines these charts, zero periods, the exact squared-gap identity,
and the collapsed-gap Cauchy value to prove that the common-circle
candidate equals the chart-independent normalized action throughout
one complex source ball for every sufficiently distant index.

`SourceNormalizedActionComplexUniformSequenceMajorants.lean` transfers
the common-circle `ℓq + ℓ^(p/2)` majorants to the chart-independent
normalized action at nearby complex sources, including collapsed gaps.
It also gives one source neighborhood on which all distant normalized
action coordinates are differentiable.

`TwoExponentMajorant.lean` turns tail bounds by an `ℓq` sequence plus
an `ℓ^(p/2)` sequence into an `ℓq` tail, including when `p/2 < 1`.
`SourceNormalizedActionComplexSequenceSpace.lean` applies this to the
complex normalized-action deviation and bounds its full `ℓq` norm
locally uniformly; finitely many central coordinates are controlled by
source continuity. `SourceNormalizedActionComplexAllCoordinates.lean`
shrinks to one source neighborhood where every coordinate is complex
differentiable and the entire deviation has that uniform `ℓq` bound.

`BoundedCoordinateHolomorphic.lean` proves that a locally bounded `ℓq`
map with complex-differentiable coordinates is norm-continuous, using
Schwarz estimates on finite truncations. Applied in
`SourceNormalizedActionComplexSequenceContinuity.lean`, this makes the
full normalized-action deviation norm-continuous near every real-type
source. `SourceNormalizedActionComplexUniformPositive.lean` then gives
one complex neighborhood and one positive lower bound for the real
parts of all normalized actions. On that same neighborhood all
principal square-root coordinates are differentiable, nonzero, and
square to four times the normalized action.
`SourceNormalizedActionRootSequenceSpace.lean` puts the root deviation
in `ℓq` with a locally uniform norm bound and Fréchet-holomorphic
dependence on the source.

`BoundedCoordinateDerivative.lean` shows that the derivatives of a
locally bounded, coordinatewise holomorphic `ℓq` map assemble into a
bounded complex-linear operator from source directions to `ℓq`. The
operator norm has an explicit local Schwarz bound.
`BoundedCoordinateDifferentiable.lean` proves a quadratic remainder
estimate uniform in finite truncations, then passes it to the full
`ℓq` norm. This identifies the operator as the Fréchet derivative.
`SourceNormalizedActionComplexSequenceDerivative.lean` applies this to
the normalized-action deviation at every source in a common complex
neighborhood, giving a Fréchet-holomorphic `ℓq`-valued map and an
explicit local derivative bound. The same generic result upgrades
the principal-root deviation to an `ℓq`-valued holomorphic map.

`BanachHolomorphicAffineLineTaylor.lean` restricts a Banach-space
holomorphic map to short complex source lines and proves convergence of
its Banach-valued Cauchy series at the line endpoint. Its first
coefficient is the Fréchet derivative applied to the line direction.
`SourceNormalizedActionAffineLineTaylor.lean` applies this to both the
normalized-action and principal-root deviations, giving convergent
`ℓq`-valued line Taylor series at every nearby complex source.

`TwoExponentDecomposition.lean` upgrades pointwise bounds by `ℓq` and
`ℓr` majorants to an exact sum with separate norm bounds, even for
`r < 1`; finitely many uncontrolled coordinates can be absorbed into
the `ℓq` term. `SourceNormalizedActionTwoExponentDecomposition.lean`
and `SourceNormalizedActionRootTwoExponentDecomposition.lean` apply this
to the complex normalized action and its principal square root.
Both deviations are exactly `ℓq + ℓ^(p/2)` with locally uniform
component norm bounds for every finite `q > 1`, considered separately.
`SourceSingleRootQuotientCommonExponentDomain.lean` now obtains the
quotient-disc majorants for every finite `q > 1` on one source
neighborhood when the critical-to-midpoint offset is in `ℓ¹`.
`SourceNormalizedActionSequenceMajorants.lean` establishes that this
endpoint condition holds, with a locally uniform norm bound, for
`1 < p ≤ 2`. `SourceNormalizedActionFactorCommonExponentDomain.lean`
uses both facts to bound the actual deleted factor on distant complex
discs: one neighborhood and tail cutoff work for every finite `q > 1`,
with a source-uniform sequence bound for each `q`.
`SourceNormalizedActionCommonExponentDomain.lean` carries this shared
domain through the fixed-circle correction and complex-action
identification. For `1 < p ≤ 2`, the full action deviation belongs to
every finite `ℓq`, `q > 1`, on one complex source neighborhood, with a
locally uniform `ℓq` norm bound for each exponent.
`SourceNormalizedActionRootCommonExponentDomain.lean` transfers this to
the principal-root deviation. On one complex source neighborhood it is
a locally bounded, Fréchet-holomorphic `ℓq`-valued map for every finite
`q > 1`. `SourceNormalizedActionHolomorphicCommonExponentDomain.lean`
establishes the same holomorphy statement for the action and provides
one neighborhood on which both maps have these properties for all
finite `q > 1`.
`OnePlus.lean` defines the algebraic intersection `ℓ^(1+)` with
complex-linear projections to each finite `ℓq`, `q > 1`.
`SourceNormalizedActionOnePlus.lean` realizes both deviations as
`ℓ^(1+)` sequences on the shared complex neighborhood, with locally
bounded projections into every such `ℓq`.
`OnePlusTopology.lean` equips this intersection with its projective
topology and proves that it is a Hausdorff topological complex vector
space; continuity is equivalent to continuity of every `ℓq`
projection. `SourceNormalizedActionOnePlusTopology.lean` then proves
that both deviations are continuous as `ℓ^(1+)`-valued maps on one
complex source neighborhood.
`OnePlusComplete.lean` proves that the projective space is complete by
embedding it as the closed, coordinate-compatible subspace of the
product of its Banach `ℓq` realizations.
`SourceNormalizedActionOnePlusDecomposition.lean` gives the exact
`ℓ^(p/2) + ℓ^(1+)` decomposition of both deviations for every finite
`p > 1`, with one complex source neighborhood, locally uniform bounds
on the `ℓ^(p/2)` components, and locally uniform bounds on every
finite-`ℓq` projection of the `ℓ^(1+)` components.
When `q < p/2`, the full deviation is already in `ℓ^(p/2)` and the
`ℓq` component is zero. A full multivariable Fréchet power-series theorem in Mathlib's
`AnalyticOnNhd` sense remains open in Theorem 11.2.

Theorem 12.1 (psi-functions) is now started in `SourcePsiFree.lean`.
At zero potential the indexed psi-function is the entire filled sine
quotient with the normalization of (2.20). Its omitted center is
nonzero and all other free centers are zeros. The canonical root is
identified with `-2i sin z`, and the normalized psi/root contour
integral is `δₘₙ` on every free-centered circle of radius `0 < r < π`.
Constructing the moving roots and analytic psi-functions for nonzero
potentials remains open.
`SourcePsiCandidate.lean` defines the entire numerator family of
equation (2.23) for arbitrary `ℓᵖ` root displacements. It is jointly
analytic in the spectral parameter and displacements, is the limit of
the literal symmetric products, vanishes at every displaced root
other than the deleted one (including root collisions), and is
independent of the deleted coordinate. At zero displacement it is the
free psi-function above.
`SourcePsiContourAnalytic.lean` forms the quotient of that numerator
with the canonical root on the moving-gap complement. The integrand
is jointly analytic in the spectral variable, root displacements,
and source potential. Around any real-type source, each scalar
coordinate of the contour map in (2.22) has an enclosing circle and
has a joint Banach power series in both parameters on a neighborhood.
`ParametricCircleIntegralHigher.lean` supplies the general theorem:
fixed-circle integration preserves joint analyticity for Banach-valued
integrands on an open parameter domain. Equation (2.22) uses the
unnormalized integral,
while (2.21) uses `1/(2π)`; this factor is included in the scalar
equation. All coordinates vanish at the free data. Analyticity of the
full selected `ℓᵖ`-valued equation remains open.
`DeletedCoordinate.lean` realizes the omitted-index root-displacement
space as a complete closed kernel of coordinate evaluation in `ℓᵖ`.
Its continuous projection sets only the selected coordinate to zero.
`SourcePsiDeletedCoordinate.lean` proves that the numerator and every
scalar contour equation factor through this projection, remain
holomorphic on the omitted-coordinate Banach parameter space, and
vanish at the free data.
`SourcePsiSingleVariation.lean` proves the exact one-root variation
identity for the finite and entire psi products. Away from the moved
free center, the numerator is affine in that root displacement and
its derivative at the free sequence is the free psi-function divided
by the corresponding linear root factor. This is the first input to
the free Jacobian of Lemma 12.5.
`SourcePsiGeneralVariation.lean` extends the exact one-root identity
to arbitrary displacement data. The cross-multiplied formula remains
valid at spectral root collisions; away from the original moved root,
the numerator is affine in that coordinate and its complex derivative
is explicit. This prepares the nonfree Jacobian calculation.
`SourcePsiCoordinateVariation.lean` carries this variation through a
fixed contour at a real-type source. If the circle avoids the moved
root and canonical-root cuts, the scalar equation is exactly affine
along that retained coordinate; its derivative is the weighted
Cauchy-kernel integral of Lemma 12.5, both in the ambient and deleted
`ℓᵖ` parameter spaces. Bounds on these entries remain to be proved.
`SourcePsiGapFactorization.lean` proves the exact change-of-deleted-index
identity for the psi numerator and rewrites its integrand as the local
factor `(σₘ-z)/wₘ(z)` times a regular single-root quotient. It also
rewrites the scalar contour equation in the form (2.27), connecting it
to the quotient estimates of Lemma 10.8 and the gap integral estimate
of Lemma 12.3.
`SourcePsiQuotientDiscMajorant.lean` applies the existing Lemma 10.8
disc estimates to any psi root-displacement sequence: its offset from
the periodic midpoints lies in `ℓᵖ`. On one source neighborhood, the
regular quotient error on every sufficiently distant selected disc
has an `ℓᵖ` majorant, including when the intermediate squared-gap
exponent `p/2` is below one.
`SourcePsiFreeLatticeBound.lean` bounds the omitted-root denominator
on free quarter-π discs by a constant times `|n-m|`, then combines it
with that quotient majorant. Near the free source, the weighted regular
factor in (2.27) is bounded on all distant discs by
`(2/π)(1+|Bₘ|)` for a suitable `B ∈ ℓᵖ`, uniformly in the omitted index.
`SourcePsiCollapsedGapCircle.lean` evaluates the selected-gap psi
contour exactly at the free source. The regular factor is analytic
through the selected free center for every deleted-coordinate input,
and the contour equals `-2πi aₘ` times its weighted value there. A
quotient majorant at that center yields
`|Fₘⁿ| ≤ 4|aₘ|(1+|Bₘ|)`. When one `B ∈ ℓᵖ` bounds all centers, the
whole contour sequence belongs to the deleted-coordinate `ℓᵖ` space.
The current quotient majorant covers all sufficiently distant centers;
a bound for the finitely many remaining centers is still needed for an
unconditional local version of Lemma 12.4.
`SourcePsiFreeSequence.lean` patches the distant-index quotient
majorant at finitely many free centers by their exact errors. The
resulting global `ℓᵖ` majorant proves that the entire free-source psi
contour equation defines a map from deleted-coordinate `ℓᵖ` to itself
for arbitrary root-displacement inputs; its value at zero is zero.
Continuity and the Fréchet derivative of this sequence-valued map
remain to be proved.
`SourcePsiFreeEquationFactorization.lean` identifies every coordinate
of the free-source sequence equation as `Fₘ(a)=2aₘQₘ(a)`, where `Qₘ`
is the single-root quotient. The quotient error `Q(a)-1` itself lies
in `ℓᵖ` and vanishes at `a=0`. The nonlinear remainder obeys
`‖F(a)-2a‖ ≤ 2‖a‖‖Q(a)-1‖ₚ`, reducing the sequence-valued derivative
at zero to continuity of the quotient-error map there.
`SourcePsiFreeQuotientTail.lean` extracts a quantitative distant-index
quotient majorant at zero source, whose `ℓᵖ` norm tends to zero with
the root displacement. `SourcePsiFreeQuotientContinuity.lean`
combines this uniform tail control with analytic continuity at each
of the finitely many remaining centers to prove continuity of the
full quotient-error map at zero. Finally,
`SourcePsiFreeSequenceDerivative.lean` uses the exact remainder bound
to prove that the sequence-valued free psi equation has Fréchet
derivative `2 · id` at zero, equal to the invertible free Jacobian
operator. Extending the sequence-valued map and its derivative to
nonzero source potentials remains open.
`SourcePeriodicMidpointGapContinuity.lean` upgrades the periodic
midpoint and gap displacements from coordinatewise continuity to
continuity in `ℓᵖ` at every real-type source. This gives one free-source
neighborhood on which **all** moving periodic gaps lie in disjoint
free eighth-π discs; `SourcePsiNearFreeGapGeometry.lean` proves the
selected circles avoid every gap and the closed quarter-π discs avoid
all nonselected gaps. `SourcePsiNearFreeDiscMajorant.lean` uses those
analytic discs to patch the Lemma 10.8 tail majorant across the finite
head. The quotient error, and hence the weighted regular psi factor
in (2.26), now has an all-index `ℓᵖ` disc majorant near the free
source. Applying the selected-gap integral estimate to the complete
nonzero-source sequence-valued equation requires separate treatment
of open and collapsed gaps.
`SourcePsiFreeCircleVariation.lean` supplies a concrete common
contour condition near the free root sequence: if `‖a‖ < r` and
`‖a‖ + r < π`, every displaced root avoids the radius-`r` circle
around each free center. The nonfree scalar derivative formula then
holds on all those circles, including on the deleted-coordinate
parameter space, at zero source potential.
`SourcePsiFreeJacobian.lean` evaluates the free two-pole contour
integral and proves the exact scalar Jacobian entries of (2.22):
moving retained root `k` changes coordinate `m` by `2t` if `m = k`
and by zero otherwise. The result is also stated as a directional
derivative on the omitted-coordinate Banach space.
`SourcePsiFreeFrechet.lean` lifts those directional values through
finite `ℓᵖ` truncations: each fixed-circle scalar equation is Fréchet
differentiable at the free sequence, and its derivative is the bounded
functional `2 · eval_m` on the omitted-coordinate space. Constructing
the full sequence-valued equation, its uniform `ℓᵖ` bounds, and
invertibility away from the free potential remain open.
`SourcePsiFreeOperator.lean` packages these rows into the bounded
operator `2 · id` on the deleted-coordinate space, proves that its
inverse is `(1/2) · id`, and gives the resulting continuous linear
equivalence. This is the free linear model for the later implicit
function theorem; identifying it as a derivative of a sequence-valued
contour map still requires the missing uniform estimate.
`SourcePsiFreePerturbation.lean` proves the inverse free operator has
norm at most `1/2`. A Neumann-series argument then shows that any
bounded operator at distance less than `2` from the free Jacobian is
invertible and bijective. This gives a quantitative target for the
nonfree Jacobian estimates in Lemma 12.5.
`CompactLpMultiplier.lean` proves that every finite-`p` coefficient
sequence has uniformly vanishing tails and therefore acts as a compact
diagonal multiplier on `ℓᵖ`.
`CompactRowMajorant.lean` proves the more general compactness criterion
needed for Lemma 12.6: if every output row of a bounded operator is
controlled by one `ℓᵖ` sequence times the input norm, its finite output
cutoffs converge in operator norm. The criterion also applies directly
to the deleted-coordinate space of the psi root parameters. Establishing
the common row bound for the nonfree Jacobian remains open.
`CompactPuncturedKernel.lean` turns the matrix estimate of Lemma 12.6
into that row bound: a zero-diagonal remainder with entries controlled
by `bₘ / |r-m|`, for one `b ∈ ℓᵖ`, is compact on the deleted-coordinate
space. The proof uses the translated punctured reciprocal lattice and
Hölder duality. Deriving this entrywise estimate from the nonfree psi
contour integral remains open.
`DeletedDiagonal.lean` builds the diagonal operator on the omitted-coordinate
space and its continuous linear inverse whenever the retained entries
have a uniform positive lower bound. This is the diagonal-isomorphism
half of Lemma 12.6; the required lower bound for the nonfree psi
Jacobian must still be obtained from Lemma 12.5.
`DeletedJacobianDecomposition.lean` combines these two results into a
conditional form of Lemma 12.6: a bounded deleted-coordinate Jacobian
with a uniformly invertible diagonal and the specified reciprocal
off-diagonal matrix bound is a diagonal isomorphism plus a compact
operator. The sequence-valued psi contour map, its Jacobian matrix
representation, and these bounds remain to be established.

`SourceStandardRootFirstMoment.lean` differentiates the standard root off
its selected gap and proves that its centered inverse-root circle moment
vanishes. Combined with the known inverse-root integral, this evaluates
every affine weighted contour integral and establishes the affine case of
the gap maximum estimate in Lemma 12.3. The full contour-to-gap argument
for a general analytic numerator remains to be formalized.

`SourceStandardRootWeightedStadium.lean` establishes the first part of that
argument: for a numerator analytic on the canonical-root domain, a
sufficiently small enclosing circle integral equals the negatively
oriented integral over the corresponding gap stadium.

`SourceStandardRootWeightedOuterArcLimit.lean` controls the two outward
endpoint semicircles in that stadium. For any numerator continuous at
the endpoints of an open real gap, both arc integrals are bounded by a
constant times the square root of the radius and converge to zero.

`SourceStandardRootWeightedTransverseBound.lean` proves the uniform
bound needed for those limits. A numerator analytic on an open
neighborhood of the selected real gap is bounded on a compact
thickening, and the standard-root lower bound cancels the cosine
Jacobian's endpoint singularity on short vertical approaches.

`SourceStandardRootWeightedCosineLimit.lean` applies dominated convergence
on those approaches, while `SourceStandardRootWeightedHorizontalLimit.lean`
identifies the resulting upper and lower straight-side limits with the
gap-side boundary integrals of Lemma 10.4.

`SourceGapStadiumIntegralDecomposition.lean` gives the generic oriented
four-piece path integral identity. In
`SourceStandardRootWeightedStadiumLimit.lean` it combines with the side
and arc limits: for a numerator analytic near the selected gap and
continuous on the canonical-root domain, the shrinking stadium
integral tends to twice the upper gap-side boundary integral.

`SourceStandardRootWeightedCornerCircleLimit.lean` transfers the
shrinking-stadium limit to shrinking corner circles using their exact
contour deformation. When the numerator is analytic on the full
canonical-root domain and near the selected gap, these circle
integrals tend to minus twice the upper gap-side boundary integral.

`SourceStandardRootWeightedCircleValue.lean` proves that constancy by
holomorphic annulus deformation. It identifies the exact integral and
establishes the Lemma 12.3 maximum bound on every isolated midpoint
circle around an open real gap. Its new local annulus theorem shows
that two midpoint circles have the same weighted integral whenever
the numerator is analytic near the intervening annulus; this uses
avoidance of only the selected gap, with no condition on the other
periodic gaps. The exact-value theorem still asks for analyticity on
the whole canonical-root domain for the stadium-to-circle deformation.
The dissertation only assumes analyticity on a neighborhood containing
its chosen contour.

`SourceGapStadiumCircleLocalGeometry.lean` proves that every point of
the four stadium-to-circle affine homotopies stays in a filled midpoint
disc of radius `R` when the stadium height is at most `R-d`.
`SourceGapStadiumCircleLocalHomotopy.lean` combines this with gap-cut
avoidance and proves the contour identity for an integrand
differentiable only on the root domain inside that disc.
`SourceStandardRootWeightedLocalStadiumCircle.lean` applies it to the
weighted inverse-root quotient with a numerator analytic near the
disc. `SourceGapStadiumLocalIntegralDecomposition.lean` makes the
four-piece stadium identity depend only on continuity along a local
domain containing its path. `SourceStandardRootWeightedLocalStadiumLimit.lean`
then proves that the shrinking stadium still tends to twice the upper
gap-side integral using a numerator analytic near that disc.
`SourceStandardRootWeightedLocalCircleValue.lean` combines this limit
with the local stadium-to-circle identity and annulus invariance. It
identifies the exact weighted integral on any midpoint circle whose
filled disc lies in the analytic neighborhood and proves its
Lemma 12.3 gap-maximum bound. Neither result assumes global
analyticity or excludes other periodic gaps from the disc. The
`SourceStandardRootWeightedLocalContourHomotopy.lean` now proves
invariance under a smooth gap-avoiding loop homotopy in the numerator's
local analytic domain. In particular, every enclosing circle with an
arbitrary center inside an analytic midpoint disc has the same exact
value and maximum bound, provided its filled disc lies in the midpoint
disc. An arbitrary circuit still needs a homotopy or winding argument
connecting it to a reference circle in that domain; the dissertation's
weaker neighborhood-of-contour hypothesis is not yet covered.

`SourceStandardRootGapSideMeanValue.lean` applies the first mean-value
theorem to the cosine parameterization of a real gap. For a numerator
that is real-valued on the gap, its upper boundary integral is `iπ`
times an attained numerator value. The local contour identities then
give the real mean-value clause of Lemma 12.3 in
`SourceStandardRootWeightedLocalRealMeanValue.lean`: the integral on
either a midpoint circle or a nested enclosing circle, normalized by
`2πi`, is the negative of a numerator value at some gap point.

`SourceStandardRootWeightedLocalSmoothContour.lean` transports the
exact gap-side value, maximum bound, and real mean-value formula from
a circle to any smooth enclosing loop with a gap-avoiding homotopy in
the local analytic domain. It also constructs that homotopy for a
noncircular polar graph whose radius stays between an inner disc
containing the gap and the enclosing analytic midpoint disc, proving
all three conclusions for those contours. General circuits without a
specified homotopy remain outside the current formalization.

`SourcePsiNearFreeRegularAnalytic.lean` proves that the weighted
regular factor of the psi equation is analytic across each selected
near-free gap and has a common `ℓᵖ` disc majorant. It bounds the
factorized numerator on the gap by the root, midpoint, and half-gap
displacements. `SourcePsiSelectedGapContourBound.lean` applies the
local Lemma 12.3 maximum estimate on nested fixed free-centered
circles. For real-type sources near zero, the open-gap coordinates of
the psi equation form an `ℓᵖ` sequence.

`SourcePsiNearFreeCollapsedGap.lean` evaluates the selected-root
integral by a Cauchy residue when the gap collapses, allowing the pole
to move off the fixed free-circle center. The same all-index regular
factor bound controls those coordinates. Together with the open-gap
estimate, this proves that the complete fixed-circle psi equation is
an element of the deleted-coordinate `ℓᵖ` space for every near-free
real-type source and every deleted root input. Extension to a complex
source neighborhood and local uniform bounds are addressed by the
later complex-gap estimates; sequence-valued analyticity remains for
the full Lemma 12.4 statement.
`SourcePsiQuotientQuantitativeDisc.lean` retains the explicit norm
estimates of the distant-disc quotient majorants and proves a uniform
bound over every fixed bounded ball of root inputs and a common source
neighborhood. `SourcePsiQuotientUniformHeadDisc.lean` bounds the finitely
many remaining discs by joint analyticity and compactness. Patching
these bounds yields one `ℓᵖ` quotient majorant whose norm is locally
uniform near any root input and the free source, and gives the same
uniform norm control for the regular factor of every deleted psi
equation. `SourcePsiNearFreeUniformEquation.lean` applies the open-gap
maximum estimate and collapsed-gap residue with that same majorant.
It constructs the complete deleted-coordinate psi sequence for every
near-free real-type source and gives a locally uniform `ℓᵖ` norm bound
near any root input over the free source, independent of the deleted
index. Extending this sequence and its bound to a complex source
neighborhood requires the complex-gap estimate described below.
`SourceStandardRootInverseCorrection.lean` compares the selected
complex standard root with its collapsed-gap inverse on the fixed
free circle, with error proportional to the squared gap.
`SourceStandardRootComplexGapCircleEstimate.lean` integrates that
comparison against an analytic factor and bounds the contour by a
Cauchy residue plus a quadratic-gap correction.
`SourcePsiNearFreeComplexCoordinate.lean` applies the estimate to each
psi equation coordinate without assuming a real-type source.
The complex-gap contour estimate and coordinate bound need analyticity
only on the closed free eighth-π disc, which matches the uniform tail
geometry around arbitrary real-type sources.
`SourcePsiNearFreeComplexUniformEquation.lean` absorbs its quadratic
gap correction into the periodic-gap displacement sequence. It builds
the complete deleted `ℓᵖ` psi equation on a complex source neighborhood
of zero and proves a locally uniform norm bound independent of the
deleted index. `SourcePsiComplexContourAnalytic.lean` extends scalar
contour holomorphy from real-type base points to any complex parameter
whose fixed circle remains in the canonical-root domain.
`SourcePsiComplexSequenceAnalytic.lean` defines the complete deleted
equation sequence and combines its uniform norm bound with scalar
coordinate holomorphy to prove Fréchet holomorphy in the ambient `ℓᵖ`
space near every deleted root input and the free complex source. The
coordinate-deletion projection then upgrades this to holomorphy with
values in the deleted `ℓᵖ` Banach space itself. The remaining work for
the global Lemma 12.4 is extension from the free source neighborhood
and the real-locus statement; the later inverse-function argument is
also open.
The bundled near-free theorem
`exists_nearFree_complex_deletedPsi_equation_formula_analytic` records
the fixed-circle formula, local boundedness, and deleted-space
holomorphy on one neighborhood of each root input over the free source.
`SourcePsiGlobalContourFamily.lean` begins the extension to arbitrary
real-type sources. It combines uniform free-centered circles for all
sufficiently distant gaps with finitely many individual enclosing
circles on one common complex source neighborhood. Every selected
circle encloses its moving gap and avoids the other gaps.
`SourcePsiGlobalScalarAnalytic.lean` intersects that neighborhood with
the joint analytic domain of the canonical-root integrand. It proves
every scalar psi equation coordinate has a joint Banach power series
in the root input and complex source on the common contour family,
for all indices and all root inputs. The selected sequence-valued
equation is currently known to be Fréchet-holomorphic there; its
joint power series remains to be established.
`SourcePsiGlobalHeadDiscBound.lean` uses joint quotient analyticity and
compactness to bound the finitely many nonstandard contour discs near
any root input. It patches that finite bound with the quantitative
Lemma 10.8 tail majorant, producing one `ℓᵖ` quotient-error majorant
on every selected contour disc with a locally uniform norm bound near
an arbitrary real-type source.
`SourcePsiShiftedDiscLatticeBound.lean` proves that a shifted selected
disc stays uniformly separated from sufficiently distant deleted free
roots. It uses this to bound the weighted regular psi factor by the
quotient majorant and gives one distance cutoff for a finite family of
head discs. The all-disc majorant now exposes the cutoff beyond which
its selected circles are free-centered.
`SourcePsiGlobalDistantDeletedRegularFactor.lean` combines that cutoff
with the all-disc quotient majorant. On one neighborhood of any root
input and real-type source, a single `ℓᵖ` majorant with locally uniform
norm controls the weighted regular factor on every selected contour
for all sufficiently distant deleted indices. The finitely many
remaining deleted indices still need a separate head estimate.
`SourcePsiFinitePairCoordinateBound.lean` supplies that head tool: any
finite set of deleted/selected scalar equation coordinates has one
common local bound on arbitrary valid fixed circles. Its proof uses
the already established scalar holomorphy and a finite intersection
of parameter neighborhoods.
`SourcePsiGlobalTailCoordinateBound.lean` combines the eighth-disc
complex-gap estimate, uniform tail geometry, and the global quotient
majorant. It obtains one constant that bounds every sufficiently
distant selected psi coordinate by the root, periodic-midpoint, and
periodic-gap displacement magnitudes, uniformly in every deleted
index near any real-type source.
`SourcePsiGlobalTailSequenceBound.lean` uses local `ℓᵖ` norm bounds for
the periodic midpoint and gap displacements to assemble those distant
selected coordinates into a deleted `ℓᵖ` sequence. Its norm bound is
locally uniform in both Banach parameters and in every deleted index.
The remaining global equation bound concerns the finitely many
selected head coordinates.
`SourcePsiGlobalHeadKernelBound.lean` establishes a common local bound
for the inverse standard-root kernel on any finite collection of
selected head circles. This follows from joint root analyticity and
compactness, and prepares the remaining finite-head contour estimate.
`SourcePsiGlobalHeadCoordinateBound.lean` combines that kernel bound
with the distant-deleted regular-factor majorant, finite-pair scalar
holomorphy, and shifted-disc separation. It bounds every selected
head coordinate uniformly in the deleted index near an arbitrary
real-type source, with a cutoff that can be enlarged to cover a
prescribed finite set of indices.
`SourcePsiGlobalEquationSequenceBound.lean` patches the finite head to
the free-centered tail. On one fixed global contour family near any
real-type source, the full psi equation is a deleted `ℓᵖ` sequence
with a locally uniform norm bound independent of the deleted index.
The next steps in Lemma 12.4 establish sequence-valued analyticity
and real-locus compatibility.
`SourcePsiGlobalEquationAnalytic.lean` uses the sequence norm bound
and scalar contour holomorphy to prove a local Fréchet-holomorphic
realization in the deleted `ℓᵖ` space near every real-type source and
deleted root input, with the selected-contour coordinate formula and
a local norm bound. The new `BanachHolomorphicLineBounds.lean` applies
Banach-valued Cauchy estimates on parameter balls. For this selected
equation it gives one radius and norm constant that bound the Taylor
derivatives on every complex line through a real-type base, uniformly
over unit directions and derivative orders.
`SourcePsiGlobalEquationLinePowerSeries.lean` now proves that these
Banach-valued line restrictions actually equal power series on one
common disc, independent of the unit direction.
`BanachHolomorphicLineJets.lean` and the selected-equation application
prove that each line Taylor jet scales by the corresponding power
when its root/source direction is scaled by a complex contraction.
`BoundedCoordinateTaylor.lean` now shows that analytic scalar
coordinates and a local `ℓᵖ` norm bound give uniform multilinear
Taylor coefficient bounds for every finite sequence truncation.
`SourcePsiGlobalEquationTaylorTruncation.lean` verifies those
hypotheses on one selected contour chart at every real-type source.
`BoundedCoordinateTaylorAssembly.lean` constructs the `ℓᵖ`-valued
continuous multilinear Taylor coefficient at every order from these
uniformly bounded finite truncations, retaining the same geometric
norm bound and the scalar coordinate formula.
`BoundedCoordinateAnalytic.lean` proves that these coefficients have a
positive common convergence radius and sum to the original sequence
map, yielding Banach-space analyticity from locally bounded analytic
coordinates.
`SourcePsiGlobalEquationTaylorTruncation.lean` now also applies the
criterion on one selected contour chart, proving Banach-space
analyticity of the selected psi equation near each real-type base.
The assembled coefficients equal its actual Fréchet Taylor
coefficients, so the same geometric norm bound holds for the full
sequence-valued equation, not only its finite truncations.
`SourcePsiSelectedJacobianAnalytic.lean` upgrades the specific selected
contour chart used for the invertible root Jacobian to an analytic
deleted-space equation. Its proof uses continuity to obtain a local
norm bound and the chart's scalar contour formulas for analyticity.
The equation's real-locus compatibility is established below.
`SourcePsiRealGapQuotient.lean` begins that compatibility argument:
for real-type source data and real displaced roots, the omitted-root
psi quotient is real on the real spectral axis away from the other
gaps. The factorized contour numerator becomes real after removing
its explicit imaginary unit, including on the selected real gap.
`SourcePsiRealTailOpenGap.lean` applies the real mean-value form of
Lemma 12.3 to an open real gap with small free-centered geometry. Under
the explicit quarter-disc quotient domain and circle hypotheses, its
free eighth-π psi equation coordinate is real. The subsequent global
steps extend this local argument.
`SourcePsiGlobalTailQuarterDisc.lean` establishes that connection for
open tail gaps: on one neighborhood of any real-type source, every
sufficiently distant free quarter-π disc avoids all other periodic
gaps, including the finite nonstandard head. Hence each distant open
real-gap psi coordinate is real for real displaced-root inputs,
uniformly in the deleted index. Later steps cover collapsed gaps and
the selected head.
`SourcePsiRealTailCollapsedGap.lean` evaluates each collapsed tail
coordinate by its Cauchy residue and proves it real for real-type
source data and real displaced roots. Combining this with the
open-gap mean-value result shows that every sufficiently distant
coordinate is real on the real locus. The selected head is handled
below by a contour-reflection argument.
`SourceStandardRootWeightedLocalRealMeanValue.lean` now proves the
real mean-value formula for an outer real-centered circle by nesting a
smaller midpoint circle inside it. `SourcePsiRealCenteredOpenGap.lean`
applies that formula to the factorized psi equation on any real-centered
open-gap contour whose weighted regular factor is analytic across the
filled disc. This removes the free-center geometry restriction from
the open-gap reality argument; selecting such analytic head contours
uniformly is the next step.
`SourcePsiGlobalContourFamily.lean` now exposes a real-centered version
of its common contour family, including the finitely many selected head
circles. The property follows from the explicit real isolating-disc
centers and is preserved on a shared source neighborhood. The earlier
contour-family interface remains available for existing analytic and
norm estimates. Head-coordinate reality still needs the regular-factor
analyticity and finite-index cases connected to this family.
`SourcePsiRealCenteredShiftedDisc.lean` connects lattice separation to
the new open-gap theorem. It proves that a deleted free root outside a
selected shifted head disc makes the weighted regular factor analytic
throughout that disc; the corresponding open real-gap psi coordinate is
then real. The same file now handles collapsed gaps through their
Cauchy residues and combines both cases: every real selected gap has a
real coordinate on a separated real-centered disc. A common cutoff
for the finite head family remains to be connected to this result.
`SourcePsiGlobalRealDistantDeleted.lean` supplies that common cutoff.
On one neighborhood of an arbitrary real-type source, every coordinate
of the selected psi equation is real for all sufficiently distant
deleted indices and every real displaced-root input. This includes
shifted head contours, free tail contours, open gaps, and collapsed
gaps. The finite deleted-index cases are addressed by the reflection
argument below.
`SourceStandardRootConjugation.lean` proves that for real-type source
data, every standard root commutes with
complex conjugation off its gap, and the full canonical root acquires
the expected minus sign from its `2i` normalization. This reflection
identity applies on the gap complement without requiring the deleted
free root to lie outside a selected head disc.
`SourcePsiContourConjugation.lean` proves the entire deleted numerator
commutes with conjugation for real displaced roots and the full psi
contour integrand is anti-conjugate on the real-type gap complement.
`RealCircleIntegralReflection.lean` proves that an anti-conjugate
integrand has a real circle integral about a real center.
`SourcePsiContourConjugation.lean` applies it to every psi equation
coordinate without requiring the deleted free root outside the disc.
`SourcePsiGlobalRealCoordinates.lean` combines this with the common
real-centered contour family: all selected coordinates are real on the
real locus, for every deleted index and every gap.
`SourcePsiGlobalHeadDiscBound.lean` through
`SourcePsiGlobalEquationSequenceBound.lean` now retain the real-center
property through the quotient majorant and uniform sequence norm.
`SourcePsiGlobalEquationAnalytic.lean` carries the same family into its
locally bounded Fréchet-holomorphic deleted-sequence map and proves that
every coordinate is real when the source and displaced roots are real.
`SourcePsiRealJacobianEntry.lean` starts Lemma 12.5: the exact
retained-root variation kernel is anti-conjugate on real data. Its
integral over a real-centered contour is real, so the corresponding
scalar Jacobian entry from the root-variation formula is real whenever
the selected contour avoids the moved root. The diagonal and
off-diagonal quantitative estimates remain to be proved.
`LocalRealAxisDerivative.lean` proves that a holomorphic scalar function
with locally real values on the real axis has a real derivative there.
`SourcePsiGlobalRealJacobian.lean` applies this to the locally selected
analytic equation: for every real-type source and every real displaced-
root input, all retained-root directional derivatives are real, with
no contour-avoidance assumption. This establishes the reality assertion
of Lemma 12.5 for the global equation; its asymptotic entry estimates
and diagonal nonvanishing are still open.
`SourcePsiJacobianKernelBound.lean` isolates the off-diagonal contour
estimate: a bound on the weighted numerator and a lower bound
proportional to the index distance for the moved-root denominator give
the inverse-index-distance decay of that Jacobian entry. Establishing
the required uniform spectral bounds for the selected contour family
is the remaining quantitative step.
`SourcePsiJacobianGapFactorization.lean` proves the exact
gap-factorized formula for each scalar Jacobian entry. In the diagonal
case the moved-root ratio cancels, leaving a single regular factor
divided by the selected standard root. The formulas are also connected
to the deleted-coordinate derivative, preparing direct applications of
the gap mean-value estimate in Lemma 12.3.
`SourcePsiJacobianDiagonalMeanValue.lean` applies that estimate to an
open real selected gap. Under explicit contour analyticity and root
avoidance hypotheses, the diagonal derivative equals `2π` times the
regular quotient at some point of the gap. It is nonzero if the
omitted quotient and deleted root have no zeros there. The remaining
work is to derive these hypotheses from the full root-localization
domain and to prove the uniform asymptotic estimate.
`SourcePsiQuotientTailNonzero.lean` supplies the first nonvanishing
input: the `ℓᵖ` majorant of the regular quotient error tends to zero
in the two-sided index tail. For each fixed nearby source and root
input, the quotient is therefore nonzero throughout every sufficiently
distant selected disc. A common cutoff on parameter neighborhoods and
the finite head still need separate arguments.
`SourcePsiJacobianDiagonalAsymptotic.lean` proves the quantitative
denominator algebra behind the diagonal estimate of Lemma 12.5. Every
point of a selected gap is bounded by its midpoint and gap
displacement coefficients. Under the explicit contour, analyticity,
and quotient-majorant hypotheses, the diagonal derivative differs
from `2` by at most four times the `ℓᵖ` quotient error plus four times
the gap-location error divided by the free lattice distance. The
remaining work is to make those hypotheses locally uniform over the
full root-localization domain and handle the finite head.
`SourcePsiJacobianDiagonalTail.lean` converts an `ℓᵖ` quotient majorant
and the source midpoint and gap displacement coefficients into a
two-sided tail estimate, uniformly over every distinct deleted index.
It also proves that any diagonal Jacobian family satisfying the
resulting quantitative bound converges uniformly to `2` and has one
common nonzero tail. Establishing the bound for the actual Jacobian
family throughout `Ωp` remains open.
`SourcePsiJacobianCollapsedDiagonal.lean` evaluates the diagonal
Jacobian entry at a collapsed real gap by a Cauchy residue at its
midpoint. It proves the same quantitative `2 + error` bound as for
open gaps, then combines both cases under a quotient majorant on the
selected contour disc. The remaining work is to supply one locally
uniform majorant and contour hypotheses across the actual domain
`Ωp`, then establish the off-diagonal estimates and operator results.
`SourcePsiJacobianOffDiagonalMeanValue.lean` proves the open-real-gap
mean-value identity for an off-diagonal Jacobian entry. The attained
value contains the root ratio `(σ_m-μ)/(σ_k-μ)` times the same regular
quotient used in the diagonal estimate. Quantitative separation of
these roots and control of the selected gap are the next steps toward
the `ℓᵖ_m/|m-k|` bound in Lemma 12.5.
`SourcePsiJacobianOffDiagonalGapGeometry.lean` bounds the selected
root's distance to any point of its gap by the root, midpoint, and gap
`ℓᵖ` coefficients. If the varied root and selected gap remain in
their quarter-π neighborhoods, it bounds their ratio by those
coefficients divided by half the free lattice separation. The
remaining factor is the regular quotient at the attained gap point.
`SourcePsiJacobianOffDiagonalEstimate.lean` combines the attained
value with the existing quotient-disc bound. On a free-centered
selected circle, with roots in their quarter-π discs and an analytic
regular factor, an open-gap off-diagonal Jacobian entry is bounded by
`(8/π)` times the selected root, midpoint, and gap displacements,
times `(1+‖B_m‖)/|m-k|`. The varied-root denominator is proved
analytic and nonzero on the disc from the same localization. Uniform
assembly over the full domain and collapsed gaps is still needed.
`SourcePsiJacobianOffDiagonalCollapsed.lean` evaluates a collapsed-gap
off-diagonal entry exactly by a Cauchy residue. It has the same
root-ratio and regular-quotient expression as the open-gap mean-value
formula, with the periodic midpoint as the evaluation point.
`SourcePsiJacobianOffDiagonalAllGaps.lean` bounds that midpoint value
by the same `ℓᵖ_m/|m-k|` expression as the open-gap entry and combines
both cases for every real periodic gap on a free-centered contour.
The bound still assumes an analytic regular factor, a quotient-disc
majorant, and quarter-π localization; assembling these uniformly on
the full `Ωp` domain is the next obligation.
`SourcePsiJacobianOffDiagonalRowMajorant.lean` packages the selected
root, midpoint, and gap displacement terms, multiplied by the
bounded quotient correction, into an actual `ℓᵖ` coefficient
sequence. The combined all-gap Jacobian theorem is restated with
entry bound `‖majorant_m‖/|m-k|`. The local contour and majorant
hypotheses still need to be assembled uniformly on `Ωp`.
`SourcePsiJacobianUniformOffDiagonalTail.lean` assembles the selected
contour family, local quotient-disc majorant, small-gap tail, and
regular-factor analyticity on one neighborhood of any real-type base
source. For real root inputs localized in their free quarter-π discs,
it gives one selected-row cutoff and an `ℓᵖ` row majorant for every
deleted index; the quotient majorant has a locally uniform norm
bound. The finite shifted head and the operator representation remain
to be connected to the full Lemma 12.5–12.6 statements.
`SourcePsiDiagonalRootCancellation.lean` proves directly from the
finite products that the numerator product with root `m` deleted,
its spectral quotient, and the regular psi factor do not change
when that root moves. The argument remains valid at root collisions
and when the selected root lies on a contour; it prepares a diagonal
variation formula without the current contour-avoidance premise.
`SourcePsiDiagonalVariationNoAvoid.lean` now proves that formula for
the deleted-coordinate scalar equation. The selected root may lie on
the contour: its variation is exactly affine, and the derivative is
the contour integral of the regular factor divided by the standard
root. Only the omitted equation root must avoid the contour; the
regular factor is assumed analytic on the enclosed disc.
The open-gap diagonal mean-value formula, its quotient and
nonvanishing forms, and both quantitative `2 + error` estimates now
use this derivative. None requires the selected root to avoid its
contour. The cancellation proof also imports only its direct spectral
dependencies, keeping this stronger result available to the earlier
Jacobian modules without an import cycle.
The collapsed-gap residue formula and the combined all-real-gap
diagonal `2 + error` bound now also allow the selected root on the
contour. The collapsed result needs only the zero-gap identity,
regular-factor analyticity, and avoidance of the omitted equation
root; real-type data are used by the combined theorem to split the
open and collapsed cases.
`SourcePsiJacobianUniformDiagonalTail.lean` assembles the contour
geometry, quotient-disc majorant, small-gap tail, and regular-factor
analyticity on one neighborhood of any real-type source. It gives a
shared initial row cutoff and an `ℓᵖ` quotient correction with locally
bounded norm for every deleted index and real-root input. For each
parameter pair, the `ℓᵖ` tail gives a further cutoff where every
diagonal entry is nonzero. That final cutoff depends on the parameter
pair; a bounded `ℓᵖ` ball alone has no uniform coordinate tail.
`SourceDisplacedRootsProper.lean` proves that every `ℓᵖ` displaced-root
sequence has finite preimage on compact spectral sets and hence closed
range, without quarter-π localization. `SourcePsiDeletedProductNonzero.lean`
uses this to prove the zero-set fact needed for finite diagonal rows:
the deleted numerator is nonzero wherever every retained root is
absent, including at its own omitted root. Changing only that root
leaves the deleted product fixed and lets the complete-product zero
theorem apply. The regular quotient is nonzero wherever its standard
denominator is defined and the retained roots are absent.
`SourcePsiJacobianAllGapNonzero.lean` applies that zero-set result to
the diagonal Jacobian. For either an open or collapsed real gap,
absence of every retained root from the selected gap makes the actual
diagonal derivative nonzero under the selected contour and
regular-factor hypotheses. The selected
root may itself lie on the contour.
The uniform diagonal-tail theorem now combines this zero-set result
with its already selected free-centered contours. On the quarter-π
localized real-root locus, the same neighborhood and initial row
cutoff make every distant diagonal entry nonzero uniformly in the
deleted index and parameter pair. The earlier parameter-dependent
cutoff remains available without root localization.
`SourcePsiSelectedJacobianEntry.lean` defines the bounded root-direction
Fréchet Jacobian of the locally selected sequence-valued psi equation.
On the common open set where the selected sequence agrees with its
scalar contour formulas, applying this operator to a retained
coordinate vector gives exactly the corresponding scalar contour
derivative. `SourcePsiSelectedJacobianDiagonalTail.lean` transfers the
uniform scalar diagonal nonvanishing theorem to this bounded operator:
both selected contour families are free-centered beyond a common row
cutoff, so the operator's diagonal entries are nonzero on every distant
retained row of the real quarter-π root locus. Finite-head spectral
separation still requires assembly. `SourcePsiSelectedJacobianOffDiagonalTail.lean`
likewise transfers the scalar `ℓᵖ` row majorant to the off-diagonal
entries of the bounded operator on a common free-centered tail.
`SourcePsiSelectedJacobianCombinedTail.lean` chooses one neighborhood,
contour family, and cutoff where both conclusions hold for the same
operator. This supplies the shared tail data needed for the eventual
diagonal-plus-compact decomposition. The global sequence analyticity
and selected-Jacobian matrix theorems now retain the all-gap contour
geometry of that same family, including its finitely many head rows.
The finite-head spectral separation needed for nonzero diagonal
entries remains open. `SourcePsiSelectedJacobianAllGapNonzero.lean`
applies the scalar all-gap nonvanishing theorem directly to the bounded
selected Jacobian at any retained row, including finite head rows and
collapsed gaps, under explicit contour avoidance, regular-factor
analyticity, and retained-root separation hypotheses.
`SourcePsiSelectedJacobianDiagonalEstimate.lean` transfers the scalar
`2 + error` diagonal tail estimate to the bounded selected Jacobian.
Its `ℓᵖ` correction has a locally uniform norm bound, and the same
theorem gives tail nonvanishing on the quarter-π localized real-root
locus.
`DeletedJacobianSymbol.lean` extracts a bounded diagonal symbol from
any bounded operator on the deleted coefficient space. Its norm is at
most the operator norm. Subtracting the corresponding diagonal
multiplier produces a zero-diagonal remainder without changing any
off-diagonal matrix entry, preparing the operator-level compactness
argument of Lemma 12.6.
`DeletedJacobianInvertibleDiagonal.lean` shows that finitely many
nonzero retained diagonal entries and a fixed tail lower bound give a
global positive lower bound. The extracted diagonal multiplier is then
a Banach-space isomorphism.
`SourcePsiSelectedJacobianDiagonalSeparation.lean` supplies the tail
separation for the actual selected Jacobian: after a cutoff depending
on the parameter pair, every retained diagonal symbol entry has norm
at least one. Consequently, nonvanishing of the finitely many earlier
entries suffices to make its extracted diagonal multiplier bijective.
`CompactTailRowMajorant.lean` sharpens the compactness criterion for
deleted-coordinate operators: an `ℓᵖ` output-row majorant is needed
only on a two-sided tail. The finitely many head rows are controlled by
the operator norm and absorbed into a finite modification of the
majorant. This removes a finite-head estimate from the compactness
part of Lemma 12.6.
`DeletedJacobianMatrixExpansion.lean` expresses a bounded deleted
operator on finite input truncations as the finite sum of its matrix
entries, and proves those sums converge to each output coordinate.
This is the density step needed to turn reciprocal off-diagonal entry
bounds into the row majorant used by compactness.
`CompactTailReciprocalMatrix.lean` now derives that row majorant from
zero diagonal entries and reciprocal off-diagonal matrix bounds on
the tail. The row kernel is constructed in the conjugate `ℓᑫ` space,
identified with the operator by the finite matrix sums, and then
fed to the tail-only compactness theorem. Thus no separate kernel
representation is needed to prove compactness from matrix estimates.
`SourcePsiSelectedJacobianCompactRemainder.lean` applies this criterion
to the selected psi Jacobian. On the real quarter-π localized root
locus, its bounded off-diagonal remainder is compact. The proof uses
the selected scalar entry estimates only on distant rows; all finite
head rows follow from boundedness. The remaining diagonal
invertibility question is confined to finite-head nonvanishing for a
contour family shared with this compact decomposition.
`DeletedJacobianCompactRemainder.lean` factors out the operator step:
tail reciprocal estimates for any bounded deleted operator imply its
canonical off-diagonal remainder is compact. The selected psi theorem
now applies that general result directly, which allows later diagonal
and compact estimates to be assembled on one chosen contour family.
`SourcePsiSelectedJacobianDiagonalCompact.lean` now performs that
assembly. One selected bounded Jacobian equals its extracted diagonal
multiplier plus a compact remainder. Its diagonal has a fixed lower
bound on a parameter-dependent tail, and nonvanishing of the finitely
many earlier retained entries makes the multiplier bijective. This is
the operator conclusion of Lemma 12.6 under the remaining finite-head
spectral nonvanishing condition.
`SourcePsiIsolatingRootSeparation.lean` formalizes the geometric part of
that finite-head condition: roots assigned to pairwise disjoint spectral
discs avoid every other periodic gap and hence every other standard
root gap. If a selected contour lies in its assigned disc, the omitted
root also avoids that contour.
`SourcePsiSelectedJacobianIsolatingDiagonal.lean` connects those
separation lemmas to the *same* selected contour family used by the
diagonal-plus-compact theorem. It now chooses one local isolating-disc
family along with the bounded selected Jacobian. If the displaced roots
lie in their assigned discs and are real, the diagonal multiplier is
bijective and the remainder is compact. No quarter-π bound is imposed
on the finitely many head roots.
`SourcePsiRegularFactorIsolatingDisc.lean` derives the needed
regular-factor analyticity from the global analytic quotient domain and
disjointness.
`SourceCriticalRootRatioUniformCircle.lean` now retains the stronger
per-gap construction: after fixing one isolating-disc family, a selected
real-centered contour can be chosen with its whole closed disc inside
its assigned isolating disc on a smaller source neighborhood. The old
unconstrained contour theorem follows by forgetting this containment.
This is the head-contour ingredient for a shared isolating-disc family.
`SourcePsiGlobalContourFamily.lean` now combines that head construction
with the uniform free-centered tail circles. It produces one local
contour family whose selected closed discs all lie inside one fixed,
pairwise disjoint isolating-disc family, while retaining the all-gap
contour geometry.
The selected quotient majorant, distant deleted-root regular-factor
bound, finite head coordinate bound, and global equation sequence bound
now retain the same isolating-disc family and closed-disc containment
through their successive neighborhood restrictions. The analytic global
equation and selected Jacobian carry this family to the operator result.
Matching this local root-placement formulation exactly to the
dissertation's Ωᵖ domain is the next step toward the full Lemma 12.6
statement.
`CompactTailRowColumnReciprocalMatrix.lean` strengthens the operator
compactness criterion: reciprocal entry estimates are needed only for
distant rows and distant input columns. The finitely many uncontrolled
columns factor through a finite-rank projection. The corresponding
deleted-Jacobian theorem in `DeletedJacobianCompactRemainder.lean`
is used by the selected psi Jacobian. The scalar off-diagonal estimate
now requires quarter-π localization only on distant input columns;
root placement in the assigned isolating discs supplies that tail bound.
`CompactIdentityFredholm.lean` formalizes the Fredholm alternative for
`1 - T` with compact `T`, then factors a compact perturbation `D + K`
of a bijective diagonal through it. The local selected-Jacobian theorem
now concludes bijectivity from injectivity under its isolating-disc
hypotheses. This establishes the operator step of Corollary 12.8;
the injectivity proof of Lemma 12.7 appears below.
`SourcePsiCandidateRootVariation.lean` starts that proof at the entire
numerator. Differentiating its zero identity along a moving retained
root gives the exact relation between the root-sequence variation and
the spectral derivative. At a simple retained root, vanishing of the
variation forces the corresponding direction coefficient to vanish.
`SourcePsiCandidateSimpleRoots.lean` proves that the full spectral
product has a simple zero at each root separated from the others, and
transfers simplicity to every retained zero of the psi numerator.
Pairwise disjoint isolating discs supply the needed separation. Thus a
deleted direction is zero if its entire-numerator variation vanishes
at every retained root. The gap-zero and interpolation results below
derive that vanishing from the Jacobian kernel.
`SourcePsiCandidateEntireVariation.lean` defines that variation as the
Fréchet derivative of the psi numerator in a root-sequence direction.
It is entire in the spectral variable and equals the derivative along
the affine root-sequence line. If it vanishes identically, the new
root-variation and simple-root lemmas show that the deleted direction
is zero under the local isolating-disc hypotheses.
`SourcePsiCandidateContourVariation.lean` identifies the root-direction
derivative of the psi contour integrand with the entire variation
divided by the canonical spectral root. On each admissible fixed
circle, the scalar psi-equation derivative is the integral of this
quotient throughout a local source neighborhood. This is the contour
identity used at the start of Lemma 12.7's kernel argument.
`SourcePsiSelectedJacobianKernelContour.lean` transfers that identity
from scalar equations to the bounded selected sequence Jacobian for
arbitrary deleted-root directions. If such a direction lies in its
kernel, the variation contour integral vanishes in every retained row.
The gap-zero results below turn these zero integrals into zeros of the
entire variation. The interpolation result below gives uniqueness once
these zeros are assembled into a simple gap product.
`SourcePsiCandidateVariationRealAxis.lean` proves that the entire
variation takes real values on the real spectral axis when the base
displaced roots and the direction are real. This supplies the reality
hypothesis for the real-gap mean-value lemmas.
`SourcePsiVariationOpenGapZero.lean` combines that reality theorem with
the weighted circle mean-value lemma. On a retained open real gap, a
zero variation contour integral forces a zero of the entire numerator
variation in the gap. In particular, a real direction in the bounded
selected Jacobian kernel has such a zero wherever the prescribed circle
and omitted-root domain satisfy the stated hypotheses.
`SourcePsiVariationCollapsedGapZero.lean` handles the complementary
collapsed-gap case: Cauchy's formula forces the variation to vanish
at the periodic midpoint when its contour integral is zero. This also
applies directly to complex directions in the selected Jacobian kernel.
`DeletedRealImag.lean` and `DeletedRealOperator.lean` prove that a
bounded operator with real matrix entries preserves the real and
imaginary parts of a deleted-sequence kernel direction. The selected
psi-Jacobian has real entries at real data, so
`SourcePsiSelectedJacobianKernelRealImag.lean` applies this result to
its actual bounded operator. `SourcePsiVariationComplexOpenGapZeros.lean`
then gives separate open-gap zeros for the entire variations of both
real components of any complex kernel direction. The interpolation
uniqueness mechanism is now proved in `EntireCircleDecay.lean`,
`SimpleZeroQuotient.lean`, and `SimpleZeroInterpolation.lean`: shared
simple zeros fill the quotient analytically, and uniform decay on
expanding circles forces the numerator to vanish.
`SourceGapSampleSummability.lean` proves that arbitrary samples from
the periodic gaps have `ℓᵖ` displacements, even with one freely chosen
deleted coordinate. `SourcePsiVariationGapZeroSequence.lean` uses this
to select simultaneous zeros of a numerator variation in all retained
gaps as a valid `ℓᵖ` spectral sequence.
`SourcePsiSelectedKernelGapZeroSequence.lean` now combines the open- and
collapsed-gap row results with that selection. Under a common admissible
circle family, each real kernel direction has a simultaneous `ℓᵖ` zero
sequence; a complex kernel direction yields one for each of its real
components. `SourceGapInterpolationProduct.lean` turns such a selected
sequence into an entire product with exactly its indexed roots and proves
that they are simple under the common isolating-disc geometry. The
variation multiplied by the deleted linear factor vanishes at every
product zero, as required by the interpolation lemma.
`SourceGapInterpolationOuterCircles.lean` proves that the product divided
by its free sine normalization tends uniformly to one on the large
half-integer-radius circles, which are eventually zero-free.
`SourcePsiVariationCutoffFormula.lean` computes the root-direction
derivative of each literal deleted product as an explicit finite
product-rule sum and proves that those sums converge to the entire
numerator variation. `SourcePsiVariationCutoffResolvent.lean` rewrites
each cutoff derivative as the cutoff product times a finite root-resolvent
sum whenever the spectral parameter avoids the retained roots. It also
transfers any established limit of these sums to an exact formula for
the entire variation. `SourcePsiRootResolventExterior.lean` proves
absolute convergence of the actual-root resolvent series and a uniform
small bound on the large half-integer-radius circles. For deleted
directions it identifies the entire variation exactly as the psi
numerator times this series. `SourcePsiInterpolationQuotientExterior.lean`
combines the two product normalizations with the resolvent bound to show
uniform decay of the interpolation quotient on the large circles. The
simple-zero interpolation theorem then makes the entire variation zero;
with distinct original roots, the deleted direction is zero.
`SourcePsiSelectedJacobianInjectivity.lean` makes that connection for a
common contour family: it proves that real kernel directions vanish,
splits a complex kernel direction into real and imaginary parts, and
concludes injectivity of the bounded selected Jacobian.
`SourcePsiLocalJacobianInjectivity.lean` supplies those hypotheses from
the holomorphic selected-equation construction and proves local
injectivity at real root data in the isolating discs. The diagonal and
compact decomposition now retains the same selected contour data.
`SourcePsiLocalJacobianBijectivity.lean` combines its Fredholm reduction
with interpolation injectivity to prove local bijectivity of the bounded
selected psi root Jacobian. `SourcePsiDeletedRootFill.lean` formalizes
the dissertation's choice of a root inside the omitted index's assigned
disc: filling that unused coordinate leaves the psi variation unchanged.
`SourcePsiFilledInterpolationUniqueness.lean` and the selected-Jacobian
injectivity theorem now require localization only at retained indices.
`SourcePsiRootPlacementDomain.lean` proves that this retained-root
condition is open in the deleted `ℓᵖ` parameter space and states local
injectivity on the resulting open domain.
The scalar psi equation and its selected-root derivative are now shown
in `SourcePsiDeletedRootFill.lean` to agree exactly with those computed
from any filled full root sequence. `SourcePsiRegularFactorIsolatingDisc.lean`
accepts such a full sequence, and `SourcePsiFilledRegularFactor.lean`
proves that the filled root avoids other selected contours and makes the
regular gap factor analytic there. `SourcePsiFilledDiagonalVariation.lean`,
`SourcePsiFilledDiagonalMeanValue.lean`, and
`SourcePsiFilledDiagonalAllGapNonzero.lean` extend the diagonal derivative,
open-gap mean-value, and collapsed-gap residue arguments to any chosen
fill. The isolating-disc proof now fills the omitted coordinate with its
real periodic midpoint. Consequently, the diagonal-plus-compact and
Fredholm arguments need root placement only at retained indices.
`SourcePsiRootPlacementDomain.lean` now states local bijectivity on that
open retained-root domain, with no condition on the artificial omitted
root `nπ`. Matching the remaining local data and equation normalization
to the dissertation's full Ωᵖ and Corollary 12.8 remains future work.
`SourcePsiEquationOpenGapZero.lean` and
`SourcePsiEquationCollapsedGapZero.lean` prove the zero-equation
counterparts of the gap mean-value and Cauchy arguments. The deleted
psi numerator has exactly the retained displaced roots as zeros;
`SourcePsiEquationAllGapZero.lean` uses this and disjoint isolating
discs to identify a zero in a selected real gap with that gap's root.
`SourcePsiLocalEquationGapRoots.lean` applies the result to the
Banach-valued selected equation: on the open retained-root placement
domain, every real solution has each retained root in its periodic
gap. This proves the root-location part of Proposition 12.9 locally;
the global real-analytic solution map is constructed below.
`AnalyticImplicitBanachRoot.lean` proves the analytic implicit-zero
theorem for a Banach-valued unknown and parameter, including a local
analytic zero branch through any nondegenerate zero.
`SourcePsiAnalyticImplicitStep.lean` identifies the bounded selected
root Jacobian with the partial derivative of the joint equation.
`SourcePsiLocalImplicitBranch.lean` applies the local Jacobian theorem
and constructive implicit theorem on the same selected contour family:
at a real solution in the open retained-root domain, joint analyticity
of the selected Banach-valued equation gives an analytic local solution
branch. Establishing that joint analyticity, then joining the local
branches globally, were the remaining steps toward the existence and
real-analyticity clauses of Proposition 12.9; both are proved below
for the formalized gap-solution domain.

`BanachSmoothAnalyticOn.lean` now proves the local complex-smooth-to-analytic
step for arbitrary complete complex normed codomains, including the deleted
sequence space of the selected equation. The coordinatewise Taylor
construction below now supplies a power series for the selected equation.

`BanachHolomorphicC1.lean` proves a quantitative local Lipschitz bound for
the Fréchet derivative of a bounded complex-holomorphic Banach-space map.
It follows that complex differentiability on an open Banach-space domain
implies `C¹`, providing the first regularity upgrade for the selected
equation's already established holomorphy.
`SourcePsiLocalJacobianBijectivity.lean` and
`SourcePsiLocalImplicitBranch.lean` now expose this `C¹` regularity on
the same selected contour family as the real-locus Jacobian
isomorphism and the initially conditional analytic branch. The direct
power-series proof below establishes joint analyticity on that chart.

`BanachC1ImplicitRoot.lean` proves a constructive `C¹` implicit-zero
theorem for Banach-valued unknowns and parameters.
`SourcePsiC1ImplicitStep.lean` applies it to the selected psi equation:
each real zero in the open retained-root domain extends to a local `C¹`
zero branch, and the branch remains in that domain near its base point.
This local existence does not require joint analyticity. The later
analytic and global solution theorems strengthen this `C¹` result.
The strengthened implicit theorem now also gives an open neighborhood
in which that branch is the unique zero of the selected equation.
This local uniqueness is the gluing statement needed for continuation.

`SourcePsiFreeInitialSolution.lean` proves that the free potential and
zero deleted roots solve the selected Banach-valued equation on the
very contour family used for Jacobian bijectivity. Free contour
orthogonality and pairwise disjoint isolating discs give the zero
coordinatewise. The constructive `C¹` implicit theorem therefore
produces a local solution branch from the dissertation's free seed,
with nearby values in the retained-root placement domain.
`SourcePsiFreeUniqueness.lean` proves that this free solution is the
only selected-equation zero in that domain on the same contour family.
The proof works for complex deleted roots: the collapsed-gap Cauchy
formula locates a numerator zero at each free lattice point, and
isolating-disc separation identifies the corresponding root index.

`SourcePsiConjugateRootEquivariance.lean` proves conjugation symmetry
for arbitrary complex deleted-root inputs, from finite numerator
products through the selected Banach-valued equation. A two-integrand
circle-reflection theorem handles the orientation sign. This provides
the symmetry needed to identify locally unique branches with their
conjugates at real-type potentials.
`SourcePsiFreeRealBranch.lean` makes that identification near the free
potential. On every nearby real-type potential, its `C¹` solution has
real retained roots; the solved contour equation then places each
retained root in its selected periodic gap. This establishes the local
real seed for Proposition 12.9; real analyticity and global continuation
are established below for the canonical gap solution.
`SourcePsiLocalRealBranch.lean` extends the reality argument to every
real zero in a retained-root placement domain, using the corresponding
real-centered local contour family. Its nearby real-type solutions
have real roots in their periodic gaps, providing the local form of
the continuation step beyond the free source.
`SourcePsiGapRootTailBound.lean` supplies the first compactness estimate
for that continuation: all deleted-root sequences with roots in their
assigned periodic gaps have uniformly small `ℓᵖ` tails on a common
neighborhood of a source potential. The estimate uses endpoint and gap
tails and is uniform over the root chosen within each gap.
`UniformTailCompactness.lean` turns boundedness and eventual uniform
truncation tails into a norm-convergent subsequence in the coefficient
space. `SourcePsiGapRootSubsequence.lean` applies it when source
potentials converge and retained roots lie in their assigned periodic
gaps: a subsequence of the deleted-root vectors converges in `ℓᵖ`.
`SourcePsiGapRootLimitPlacement.lean` shows that the limit remains in
the periodic gaps of a real-type limiting source. It uses endpoint
continuity and a closedness argument for moving line segments.
`SourcePsiGapRootIsolation.lean` then places all gap-contained roots
over nearby sources, and their subsequence limit, in one fixed open
isolating-disc placement set. The next continuation step must show
that the limiting roots satisfy the selected equation.
`SourcePsiGapRootGraphCompact.lean` upgrades the subsequence argument
to compactness of the full gap-root graph over any compact set of
real-type sources, as well as compactness of each fixed-source fiber.
This supplies the properness input for finite-cover continuation
arguments; compatibility and continuity of the selected equation
across contour charts remain to be established.
`SourcePsiEquationContourHomotopy.lean` proves that the psi integrand
is holomorphic off the periodic cuts and that gap-avoiding loop
homotopies preserve its contour integral. Nested isolating circles,
and two circles within a common outer isolating circle, consequently
give identical scalar psi equation coordinates. Establishing the
common-circle geometry for overlapping local chart families and
passing the Banach-valued equation to limits remain next steps.
`SourcePsiEquationChartCompatibility.lean` lifts coordinatewise
contour invariance to equality of the selected Banach-valued equations
on comparable charts. It also passes zeros in varying contour charts
to a strongly convergent root/source limit in a fixed `C¹` chart,
provided the charts are eventually comparable and the limit belongs
to that chart. The remaining geometric obligation is to verify these
comparison and chart-membership conditions for continuation solutions.
`SourcePsiCommonIsolatingContour.lean` verifies the contour-comparison
condition whenever two families of filled contour discs lie inside the
same assigned isolating-disc family. A compactness argument constructs
one common outer circle in each disc, and disjointness from the other
periodic gaps makes the two Banach-valued selected equations equal.
`SourcePsiRealContourComparison.lean` removes the common-family
restriction at real-type sources: any two real-centered enclosing
contours whose filled discs avoid the other gaps have the same psi
coordinate. It builds a midpoint circle inside both contours, even
for collapsed gaps, and transfers the equality to selected
Banach-valued equations wherever their coordinate formulas hold.
`SourcePsiGapSolutionLimit.lean` proves the limit-of-solutions step for
real-type sources: if source potentials converge and gap-contained
deleted roots solve valid real-centered selected equations, a
subsequence converges strongly to gap-contained roots that solve the
selected equation in a `C¹` chart at the limiting source. The chart
may differ from every chart used along the sequence. The limiting
roots are real and lie in the chart's isolating discs, so its root
Jacobian is bijective. The implicit theorem then gives a locally
unique `C¹` solution branch through the limit. Conjugation symmetry
and the all-gap zero theorem show that, for every sufficiently nearby
real-type source, this branch has real roots in the assigned periodic
gaps. Within the local uniqueness neighborhood, any zero expressed
using another valid real-centered contour family agrees with the same
branch. This makes local uniqueness independent of the contour chart.
`SourcePsiGapSolvability.lean` packages a gap-contained zero using an
existential valid real-centered contour family. The free source is
solvable; solvability persists locally among real-type sources and
passes to limits of convergent real-type source sequences, even when
their contour charts vary. These are the open and closed ingredients
for continuation across the connected real-type source locus.
`SourcePsiGapGlobalExistence.lean` carries out that open-and-closed
argument on the real-type source subtype. For every real-type source
and every deleted index, it proves existence of gap-contained deleted
roots solving the selected psi equation on some valid real-centered
contour family. Real-analytic dependence of the root map remains open.
The solvability predicate also has an anchored local continuation
theorem: each specified gap solution extends to a `C¹` branch of gap
solutions over nearby real-type sources. This supplies the branch data
needed to compare distinct solutions while studying global uniqueness.
`SourcePsiGapMultiplicity.lean` proves that the presence of two
distinct gap solutions is open within the real-type source locus:
their anchored `C¹` branches stay distinct nearby. Compactness and
chart-independent local uniqueness make that multiplicity locus closed
as well. Since the free source has only zero deleted roots, connectedness
rules out multiplicity everywhere. Thus each real-type source and
deleted index has a unique gap-contained solution, independent of its
valid real-centered contour chart.
`SourcePsiGapRootMap.lean` names this unique solution as a map on the
real-type source subtype. It solves the selected equation, places each
retained root in its periodic gap, equals zero at the free source, and
is continuous. At every real-type source it agrees locally with a
complex `C¹` implicit branch.
`SourcePsiGapRootLineTaylor.lean` gives that local branch a uniform
short-direction Cauchy–Taylor expansion, whose sum equals the canonical
root at real-type endpoints. Its restriction to every complex affine
line through a real-type source is analytic. The joint Banach-space
power series now comes from the selected contour equation and the
analytic implicit theorem below.
`BanachC1ImplicitDerivative.lean` differentiates a Banach-valued
implicit zero branch and gives its derivative through the inverse root
Jacobian. `SourcePsiGapRootDerivative.lean` applies this to the
canonical gap roots: in a local contour chart their source derivative
solves the linearized selected-psi equation, and the root Jacobian is
bijective. The same anchored chart is now proved Banach analytic.
`SourceRealTypeBanachSpace.lean` identifies the real-type coefficient
locus as a closed real linear subspace, hence a complete real normed
space. On this actual real source space the canonical gap-root map is
globally `C¹`, using its local complex `C¹` extensions.
`SourcePsiGapRootDerivativeLipschitz.lean` bounds the derivative of each
local complex branch in operator norm and proves a quadratic first-order
remainder. `SourceRealTypeQuadraticRemainder.lean` identifies its linear
term with the real Fréchet derivative of the canonical root map on the
real-type Banach source space, giving a local quadratic remainder there.
`SourcePsiGapRootAnalyticReduction.lean` applies the Banach analytic
implicit theorem to the anchored canonical branch and restricts it to
the real-type source space. The canonical deleted gap-root map is
real analytic at every real-type source, proving the analyticity
component of Proposition 12.9 without a conditional equation premise.
`SourcePsiGapRootAnalyticExistence.lean` packages global existence,
pointwise uniqueness, real analyticity, and placement of every retained
root in its periodic gap into one theorem. It uses the formalized
`SourcePsiGapSolution` predicate. Its graph also lies locally in an open
retained-root placement domain. Filling the omitted coordinate with the
periodic midpoint places every root in one common family of isolating
discs over a neighborhood of each real-type source.
`SourcePsiOmegaDomain.lean` proves the deleted root coordinates are real,
defines their closed real Banach subspace and a local real `Ωᵖ`-style
placement domain, proves that domain open, and places the canonical graph
inside it. It also proves real analyticity into that real Banach space
and packages existence, uniqueness, the selected equation, and local
all-index placement. Identifying this local domain and the chart-based
solution predicate with the dissertation's full `Ωᵖ` setup remains open.
The local isolating-disc family, real-source neighborhood, and `ℓᵖ` tail
cutoff can now be chosen simultaneously for every deleted index `n`.
This supplies the real-side uniform placement and compactness needed
toward Lemma 12.10; the uniform inverse-Jacobian estimates and the
index-independent complex solution neighborhood are established below.
`DeletedOperatorExtension.lean` now realizes the selected Jacobian as
a block operator on one common `ℓᵖ` space, with value `2` on the omitted
diagonal and zero in its other omitted-row and omitted-column entries.
`SourcePsiJacobianFullExtension.lean` applies this to the actual psi
Jacobian, proves full-space invertibility is equivalent to deleted-space
invertibility, and obtains an invertible full extension at every
canonical real gap-root solution. Operator-norm convergence of these
extensions as the deleted index escapes to infinity is established below.
`UniformInverseBound.lean` proves the quantitative perturbation step:
if these full extensions converge in operator norm to an invertible
operator, their deleted-block inverses have one common norm bound for
all sufficiently large deleted indices. Finite boundedness now extends
that estimate to every integer index. The resulting theorem is
specialized to the actual selected psi Jacobians at the canonical real
gap roots. The construction of the limit operator, its invertibility,
and operator-norm convergence are established below for Lemma 12.10.
`SourcePsiJacobianFreeFullExtension.lean` identifies the selected
sequence equation on uniform free-centered contours with the existing
free equation. Consequently, at the canonical free gap root every
extended Jacobian is exactly `2 · id` on the common `ℓᵖ` space, so the
operator-norm convergence claim holds at the free source with zero
error. The nonfree limit operator and convergence estimate are established below.
`FiniteBlockOperatorConvergence.lean` proves that convergence of every
matrix entry gives operator-norm convergence on each fixed finite
input/output block, and that uniform finite-block approximation then
gives convergence of the full operators. The two-sided `|n| → ∞`
filter is identified with the cutoff form used by Lemma 12.10.
`SourcePsiJacobianFullMatrix.lean` identifies every retained full-space
matrix entry with its scalar contour derivative and records the fixed
deleted row and column. The remaining analytic work is to construct
the nonfree limit operator and prove scalar entry convergence together
with uniform finite-block approximation.
`DeletedCoordinateAtInfinity.lean` proves that deleting a coordinate
with `|n| → ∞` changes a fixed `ℓᵖ` vector by a norm tending to zero.
`SourcePsiLimitQuotient.lean` transfers this convergence through the
analytic single-root quotient at every fixed valid spectral point.
`SourcePsiLimitQuotientUniform.lean` uses joint analyticity and compactness
to make that convergence uniform on each fixed closed disc contained in
the omitted-root domain. It also passes the quotient limit through the
corresponding circle integral.
`SourcePsiLimitRegularFactor.lean` proves the deleted-index ratio in
(2.28) tends to one, names the candidate nonfree `Q*` matrix
integrand, and proves pointwise convergence of the corresponding
selected-Jacobian integrands.
`SourcePsiLimitRatioUniform.lean` strengthens the elementary ratio
limit to uniform convergence on every fixed free-centered disc. It
also verifies continuity on the contour for all sufficiently distant
deleted indices and passes this ratio limit through the fixed circle
integral.
`SourcePsiLimitIntegrandUniform.lean` combines the ratio and quotient
limits using compact-contour multiplication. When the fixed contour
avoids the retained root and standard-root gap, the complete retained
Jacobian integrand converges uniformly and its circle integral tends to
the candidate `Q*` entry integral. The contour may have any fixed center,
including the shifted central circles of the common contour family.
`SourcePsiVaryingRootIntegrandLimit.lean` extends the uniform integrand
and circle-integral limits to deleted-root vectors that vary with the
omitted index and converge strongly in `ℓᵖ`. It handles the moving
retained-root denominator by eventual contour avoidance. Establishing
this strong convergence for the actual gap-root vectors remains open.
`SourcePsiGapRootVaryingIndexCompactness.lean` proves that canonical
gap-root vectors along every sequence of omitted indices escaping in
absolute value have a strongly converging subsequence in the ambient
`ℓᵖ` space. Every retained root of the subsequential limit lies in its
periodic gap. Uniqueness of these limits is still needed for convergence
of the full index-filtered family.
`SourcePsiGapProductCompact.lean` identifies the full `ℓᵖ` product of
periodic gaps and proves it compact using a common endpoint-and-gap
majorant. Filling the omitted coordinate of each canonical gap-root
vector with the periodic midpoint places it in this compact set. This
is the compact parameter set used for uniform inverse bounds in the
proof of Lemma 12.10; convergence of the canonical root vectors is not
needed for that uniformity argument.
`CompactInverseBound.lean` combines the quantitative inverse
perturbation estimate with compactness: an operator-norm continuous
family of pointwise invertible bounded operators has uniformly bounded
inverses. The result is specialized to the compact periodic-gap product.
Applying it to the dissertation's `Q*` family still requires defining
that bounded operator family, proving its continuity, and proving its
pointwise invertibility.
`SourcePsiLimitScalarJacobianEntry.lean` defines the candidate entry as
the `Q*` contour integral divided by π and proves convergence of the
actual scalar retained-root derivatives for each fixed row and column.
It also identifies a retained entry of the bounded full-space Jacobian
with that scalar derivative on a valid selected chart.
`SourcePsiCommonJacobianCharts.lean` obtains one contour family and
analytic selected charts for all sufficiently distant deleted indices
from the index-uniform equation bound. It proves entrywise convergence
of the resulting bounded full-space Jacobians at a fixed coefficient
sequence with its deleted coordinate removed, when the retained root
avoids the contour. The candidate limit operator, the varying gap-root
data, and uniform operator tails remain open.

`SourcePsiLimitMatrixOperator.lean` constructs the bounded contour-limit
operator `Q*`, proves coordinatewise convergence of the common-contour
full Jacobians on every input, and gives one reciprocal off-diagonal
entry majorant shared by `Q*` and all sufficiently distant Jacobians.
`OperatorDiagonal.lean` extracts the diagonal multiplier of a bounded
full-space operator and proves that its off-diagonal remainder has zero
diagonal and unchanged other matrix entries.
`FullReciprocalMatrixTail.lean` derives a conjugate-space kernel from
the actual matrix row and proves the quantitative two-sided tail bound
`‖(id-Ps) C (id-Pt)‖ ≤ ‖b-Ps b‖ · ‖puncturedLattice‖` for reciprocal
off-diagonal entries. The output and input cutoffs can be chosen once
for every operator sharing the same tail-entry majorant.
`SourcePsiJacobianOffDiagonalUniformTail.lean` applies this estimate to
the actual common-contour Jacobians and `Q*`: one pair of finite cutoffs
makes all their high-output, high-input off-diagonal blocks smaller than
any prescribed positive error, eventually in the deleted index.
`SourcePsiQuotientUniformRootVariation.lean` uses the Schwarz lemma to
control root-parameter variation of the quotient on every selected disc
with one constant. A fixed quotient majorant therefore controls the
deleted root sequences up to a scalar error tending to zero.
`SourcePsiJacobianEscapingDiagonalTail.lean` combines this estimate with
the fixed midpoint and gap tails, proving that the diagonal corrections
to two are uniformly small on distant output rows, eventually in the
deleted index, for both open and collapsed gaps.
`OperatorDiagonalConvergence.lean` upgrades diagonal coordinate limits
and this uniform tail estimate to supremum-norm convergence of the
diagonal symbols and operator-norm convergence of their multipliers.
`SourcePsiJacobianDiagonalNormLimit.lean` applies it to the full psi
Jacobians, proving `Dⁿ → D*` in operator norm at every fixed gap-contained
root vector. The common `Q*` construction retains its free-tail contour
choices and scalar-entry identities, so the diagonal limit and the
off-diagonal high/high tail estimate hold on the same contour family.
`SourcePsiJacobianAllColumnTail.lean` applies the Schwarz lemma to the
refined equation coordinate bound along distinct input-coordinate
lines. It produces one fixed `ℓᵖ` majorant for distant output entries
of every off-diagonal column, including the finite head input columns.
`OperatorColumnConvergence.lean` upgrades scalar entry limits to full
column norm limits by dominated convergence, proves operator-norm
convergence after every finite input projection, and extends column
limits to strong convergence on all inputs using uniform boundedness
and density. It also gives eventual uniform output cutoffs for every
fixed finite input block.
`SourcePsiJacobianColumnNormLimit.lean` packages these conclusions for
the actual common-contour full psi Jacobians and the contour-limit
operator `Q*`. This controls the high-output, finite-input mixed block.
`SourcePsiJacobianFiniteRowTail.lean` obtains reciprocal decay on every
fixed finite output set, including nonstandard selected head circles,
from compact quotient/kernel bounds and distant input-root separation.
`FiniteOutputReciprocalTail.lean` turns these entries into conjugate-space
row kernels and gives one uniformly small input tail for every operator
sharing the bound. With coordinatewise limits, the same estimate proves
operator-norm convergence after every finite output projection.
The common `Q*` theorem now packages both mixed-tail directions and
finite-input/finite-output operator-norm limits on the same Jacobian
family.
`OperatorNormFromProjections.lean` gives a quantitative five-term bound
for the full operator difference from the two finite projections, the
diagonal difference, and the two off-diagonal high/high tails.
`SourcePsiJacobianNormLimit.lean` combines all these estimates on one
common contour family, proving full operator-norm convergence of the
actual Jacobians to `Q*` for every fixed gap-contained root vector and
real-type potential at every finite `p>1`. The deleted index can escape
in either direction. This establishes the fixed-root norm-limit claim
in Lemma 12.10.
`CompactOperatorTail.lean` proves compactness from small high/high tails
by approximating with the remaining finite rows and columns. It also
proves compactness of diagonal corrections whose symbols approach a
constant, including coordinate limits with eventual uniform tails.
The strengthened common-contour norm-limit theorem now proves that
the same `Q*` differs from `2I` by a compact operator. The Fredholm
alternative reduces its bijectivity to injectivity. The full-product
interpolation and conjugation results below now close that pointwise
kernel argument. Uniform convergence over the full gap product and
common inverse bounds for every finite-index Jacobian at a fixed
real-type potential are established below. Uniform control over nearby
complex potentials and compatibility of local charts are established
below. The complex zero branches are also glued over the entire real
source locus below.
`SourcePsiFullProductVariation.lean` supplies the entire variation of
the undeleted root product. At a simple root it recovers the direction's
corresponding coefficient; indexed real-gap placement makes the roots
distinct even when gaps collapse. A basis variation is exactly the
negative deleted psi numerator. Differentiating the full product
contour gives a continuous linear functional with the required sign
and `1/π` factor. `SourcePsiLimitOperatorContour.lean` extends the matrix
entry identity to all `ℓᵖ` directions by density and retains the actual
norm-limit operator and compact correction on the same contour family.
The kernel is therefore precisely the directions with vanishing
full-variation contours.
The strengthened construction now retains real centers through these
same limit theorems. `SourceEntireGapContourZeros.lean` provides shared
open-gap and collapsed-gap contour arguments for entire numerators.
The full product variation is real on the real spectral axis for real
root data and directions. `SourcePsiLimitKernelGapZeros.lean` therefore
obtains a zero in every periodic gap for each real direction in the
actual limit operator's kernel. These zeros form a complete `ℓᵖ`
displaced spectral sequence with no omitted index. Collapsed-gap
midpoint vanishing also holds for complex directions.
`SourcePsiFullProductResolventExterior.lean` proves the full variation
equals the complete root product times the complete actual-root
resolvent. A shared exterior ratio bound for full spectral products
also simplifies the existing deleted interpolation argument.
`SourcePsiFullProductInterpolation.lean` combines exterior quotient
decay, expanding-circle interpolation, and simple gap-contained zeros
to prove full-variation uniqueness. Coefficient recovery eliminates
every real direction in the actual `Q*` kernel.
`RealImag.lean` and `RealOperator.lean` provide full-space conjugation
and real/imaginary kernel decomposition from real matrix entries.
`SourcePsiLimitBijective.lean` verifies reality of the actual contour
entries and proves complex injectivity. The compact correction to `2I`
then gives pointwise bijectivity for every fixed real-type potential
and full gap-contained root vector at finite `p>1`. The entries,
operator-norm convergence, compactness, and bijectivity all concern
the same operator and real-centered contour family.
`SourcePsiGapLimitOperator.lean` identifies each scalar entry as twice
the normalized psi contour and proves independence of every valid
real-centered contour choice. Density gives one intrinsic bijective
limit operator on the full gap product; it retains the actual fixed-root
operator-norm limit and compact correction to `2I`.
`SourcePsiCommonJacobianRootVariation.lean` obtains an eventual local
root Lipschitz bound for all escaping full Jacobians from the common
bounded holomorphic charts. The same contours give the scalar limit
entries at every nearby gap-root vector.
`MatrixLimitNormBound.lean` passes the original norm bound through
scalar basis-entry limits. This transfers the Lipschitz estimate to
the actual intrinsic `Q*` family and proves its operator-norm
continuity. `SourcePsiGapLimitInverseBound.lean` defines its bounded
inverse, proves both inverse identities, and uses compactness of the
full gap product to obtain one inverse norm bound over all root vectors
at each fixed real-type potential.
`SourcePsiJacobianContourIndependence.lean` proves equality of the
actual selected sequence equations for every deleted root vector,
including when their definition defaults to zero. Their root derivatives
and full extensions therefore agree across every valid real-centered
contour family. This transports the actual pointwise norm limits and
eventual local Lipschitz estimates onto any one fixed family.
`CompactEquicontinuousLimit.lean` proves a general compactness criterion
for uniform convergence from these estimates. Applied in
`SourcePsiJacobianGapUniformLimit.lean`, it gives operator-norm
convergence of the actual full Jacobians uniformly over the entire
gap product, with a single absolute-index cutoff for each tolerance.
`SourcePsiJacobianGapOperator.lean` proves operator-norm continuity
of every finite Jacobian and its actual bijectivity on the gap product.
`SourcePsiJacobianGapInverseBound.lean` defines the full bounded
inverses and proves both inverse identities. Uniform comparison to
`Q*` bounds all distant inverse norms; compactness handles each of
the finitely many remaining indices. One constant bounds the full
inverses for every signed index and every gap-root vector at the fixed
real-type potential. The same bound holds for genuine two-sided
inverses of the original deleted blocks.
`SourcePsiJacobianSourceVariation.lean` passes the joint holomorphic
derivative estimate to the actual root Jacobians and their full
extensions. Both restrictions contract operator differences, so one
Lipschitz bound controls nearby complex potentials and roots on all
escaping-index charts. `SourcePsiAllIndexJacobianCharts.lean` combines
these with the finite remaining charts to obtain one joint radius and
constant for every index at each full root vector and real-type source.
`NearbyInverse.lean` proves actual two-sided inverse existence from
Neumann smallness and bounds its norm by twice the original inverse
norm. It also recovers the deleted block inverse from a full extension
inverse without increasing the norm.
`SourcePsiComplexJacobianInverseBound.lean` applies these estimates on
joint complex chart balls near every gap-root center. One inverse norm
bound works for all centers and indices, and the selected equations
retain their actual scalar contour formulas throughout each holomorphic
chart. Complex invertibility is a conclusion of the perturbation proof.
`SourcePsiComplexJacobianNeighborhood.lean` assembles a common open
neighborhood of the entire gap product at the fixed real-type source.
Compactness gives one positive tube radius. Real convexity of the gap
product, proved in `SourcePsiGapProductConvex.lean`, gives a convex
choice of neighborhood by adding a small open ball. At every point and
every deleted index there is a holomorphic selected contour chart with
actual full and deleted two-sided inverses bounded by one constant.
The chart construction now retains real centers, moving gap enclosure,
and canonical-root contour domains throughout each complex chart ball.
The real-line and real-form identity principles support Banach-valued
functions. `ConvexHolomorphicIdentity.lean` extends equality of a germ
throughout an open convex domain. Applied in
`SourcePsiComplexChartCompatibility.lean`, these results identify the
actual selected psi equations on every overlap of joint ball charts
centered at the same real source. Root inputs remain arbitrary complex
sequences in the joint real-form argument. The actual root derivatives
agree on the overlaps as well.
`GlueHolomorphicCharts.lean` defines the common function on the union
and proves exact local representation and holomorphy.
`SourcePsiGluedEquation.lean` constructs one analytic sequence-valued
equation for each deleted index, retaining its actual scalar contour
formulas. One convex full-space neighborhood of the entire gap product
at the fixed real source projects into every equation domain. The
actual root derivatives of the glued equations retain full and deleted
two-sided inverses with one norm bound independent of the point and
index. The chart control also retains equation norm bounds. A finite
subcover of the compact gap product gives one such bound across all
glued domains and every deleted index.
`SourcePsiUniformEquationTube.lean` fills the omitted coordinate of
each canonical solution with its periodic midpoint. Lifting nearby
deleted inputs to full root inputs allows compact thickening to give
one joint analytic radius around all canonical solution centers.
The glued equations have common equation and root inverse norm bounds
throughout these balls. Real contour comparison identifies every
canonical real solution as an actual zero of its glued equation.
`SourcePsiUniformEquationEstimates.lean` proves the joint derivative
bound `2C/r`, joint and root derivative Lipschitz bound `4C/r²`, and
source residual bound `2C/r` on the inner balls. Actual root derivative
bijectivity holds throughout the outer balls. These estimates and the
radius are independent of the deleted index and supply the quantitative
inputs for the implicit-function step.
`QuantitativeTriangularDerivative.lean` explicitly inverts the combined
equation-and-source derivative with inverse norm at most
`M(1+2C/r)+1`. `QuantitativeAnalyticInverse.lean` uses this bound and the
derivative Lipschitz constant to give explicit joint and covered image
radii, an analytic inverse throughout the image ball, and uniqueness
in the joint ball. These radii are independent of the index.
`SourcePsiUniformComplexBranches.lean` therefore constructs all analytic
psi zero branches on one complex source ball at each real base source.
They solve the actual glued equations, have canonical base values,
and stay in one common root ball with a local uniqueness theorem.
`ConvexRealAnalyticIdentity.lean` propagates equality of real analytic
germs on open convex Banach domains.
`SourcePsiUniformComplexBranchRealAgreement.lean` first uses continuity,
real contour comparison, and local uniqueness to identify the canonical
roots as a germ, then extends equality to every real source in the full
common source ball.
`SourcePsiUniformComplexExistence.lean` states the resulting existence
theorem without supplied equation or inverse data: one source radius
works for every signed deleted index, the branches retain the canonical
real roots, and their actual retained psi contour integrals vanish on
valid moving real-centered circles.
`SourceHolomorphicRealCenteredBalls.lean` proves that Banach-valued maps
on balls centered at different real-type potentials agree throughout
their overlap whenever they agree on its real locus. Projection to the
real part supplies a real point in every nonempty overlap; the complex
real-form identity gives a germ, and convex continuation propagates it.
`SourcePsiComplexBranchCompatibility.lean` identifies the actual root
branches from any two real base sources, independently of the chosen
equation tubes.
`SourcePsiComplexRootAtlas.lean` chooses uniform local branches at all
real sources and glues every signed-index root map on one open union.
The maps are analytic on that same domain, have exact local branch
representations, agree with all canonical real roots, and retain their
actual contour orthogonality at every nondeleted index.
The real-type projection is Lipschitz and continuous.
`SourcePsiComplexRootDomain.lean` contracts this union to the real
projection along segments in its covering balls, then to zero along
the real locus. The common domain is therefore contractible and simply
connected and contains the entire real-type source locus. The global
existence theorem supplies the domain, analytic branches, canonical
real agreement, and actual retained contour zeros without assumptions
about a preexisting branch family or domain.
`SourcePsiFullRootPlacement.lean` proves that the full assigned-root
placement set is open by combining one coordinate with the open
deleted-root projection. The compact full gap product therefore has
one positive perturbation margin inside its assigned isolating discs.
`SourcePsiUniformEquationTubeRestriction.lean` restricts the tube radius
while preserving the actual equations, contour formulas, zeros, bounds,
and root derivative inverses.
`SourcePsiIsolatingLocalBranches.lean` chooses the common tube radius
below both the root-placement margin and a prescribed source radius.
All complex branches retain their assigned discs on one source ball
independent of the deleted index. That ball stays inside the prescribed
open neighborhood, and its moving spectral clusters lie in the same
pairwise disjoint disc family.
`SourcePsiIsolatingComplexRootAtlas.lean` glues these families inside any
prescribed open neighborhood of the real locus. Local assigned-disc
placement survives gluing; filling the omitted root with the moving
periodic midpoint places the entire root vector in the same discs.
`SourcePsiLemma12_10.lean` proves the source-space version of Lemma 12.10.
The theorem `exists_sourcePsi_lemma12_10` supplies one open simply
connected complex domain contained in the actual almost-real spectral
neighborhood of Lemma 10.1. Every signed-index root map is analytic on
that domain and agrees with the canonical real gap roots. At each real
potential one source ball and one isolating-disc family work for all
indices. The actual retained contour integrals vanish throughout the
domain. The resulting psi numerators are jointly analytic in the
spectral parameter and potential, and entire in the spectral variable.
`StandardRootGapCorrectionExterior.lean` proves that the actual
principal-square-root gap correction product tends to one outside
fixed free spectral discs. The absolute squared-gap radicand sum is
bounded by the square of the ℓ¹ free gap-resolvent sum once the midpoint
displacement is uniformly small.
`SourceCanonicalRootExterior.lean` identifies the actual canonical root
with its midpoint product times these corrections, retaining the
literal symmetric cutoffs and their normalization. Its ratio to
`-2i sin λ` tends uniformly to one on the half-integer large circles,
which eventually avoid every closed periodic gap.
`CircleIntegralExteriorNormalization.lean` proves the oriented-pole
integral limit `2π` from uniform relative error.
`SourcePsiExteriorNormalization.lean` then restores the omitted
numerator root and proves that the actual psi quotient's raw
large-circle integral tends to `2π`; its normalized contour functional
tends to `1`. This holds for every root displacement vector and every
complex source at finite `p>1`, including Lemma 12.10's analytic family.
`CircleCauchyTransform.lean` proves the annular Cauchy decomposition and
analyticity of each circle transform on the circle complement.
`CircleCauchyTransformPeriods.lean` computes their contour contributions
by Fubini. `CircleHoleRemoval.lean` fills one hole analytically, subtracts
its period from enclosing contours, and preserves disjoint periods.
`FiniteCircleHoleDecomposition.lean` repeats this over a finite family
and proves that the outer integral equals the sum of the inner ones.
`SourcePsiFiniteContourDecomposition.lean` applies the theorem to the
actual psi quotient under explicit gap enclosures and disjoint
isolating-circle geometry. Retained contour zeros reduce this sum to
the omitted-gap contour.
`SegmentIsolatingCircles.lean` and `SourcePsiIsolatingCircles.lean`
construct all-index enclosing circles with disjoint closed collars
inside the actual assigned spectral discs, also at complex sources.
`SourcePsiIsolatingFiniteGeometry.lean` proves that the same fixed
circles give the finite decomposition at every sufficiently large
half-integer cutoff, enclosing exactly the signed indices `[-k,k]`.
`SourcePsiRealNormalization.lean` uses retained contour zeros and the
large-circle limit to prove exact omitted normalization for every
real gap solution: `1` for the normalized contour and `2π` for the raw
integral. The canonical real psi roots have full orthogonality on every
valid real-centered gap-circle family.
`SourcePsiAssignedCircleFamily.lean` proves that the original assigned
boundaries remain valid throughout their complex source ball, and
nested homotopy identifies the smaller circles' periods with theirs.
`SourcePsiComplexContourAnalytic.lean` now proves joint analyticity of
the normalized contour also at complex parameters, including the
omitted index. `SourcePsiIsolatingComplexNormalization.lean` composes
these periods with the root branches and uses the real-form identity
to extend exact orthogonality to every complex source ball.
`SourcePsiLemma12_11.lean` constructs one common open simply connected
complex source neighborhood retaining all of Lemma 12.10's analytic
branches and assigned root placement. One assigned circle family at
each source gives exact Kronecker periods simultaneously for every
numerator; the literal omitted raw integral is exactly `2π` everywhere
on this domain.
`SourceStandardRootZeroPeriodOffset.lean` now proves the exact
midpoint expansion (2.33) from a vanishing actual standard-root
period. Subtracting the midpoint factor and its collapsed-gap Cauchy
period leaves precisely the quadratic reciprocal-root correction.
`SourceStandardRootQuadraticOffset.lean` turns this identity into a
squared-gap root-offset bound from explicit circle geometry, factor
variation, and a midpoint lower bound.
`SourcePsiQuadraticRootOffset.lean` defines the actual midpoint-filled
regular factor `χ` in (2.31), identifies its period with the retained
psi equation, and proves (2.33) for the actual psi roots. On the
free-centered tail circles, `|χ-i| ≤ M ≤ 1/2` gives the lower bound
automatically and yields `|σ-τ| ≤ (384/π) M |γ|²`, with a constant
independent of both indices. `SquaredWeightQuotient.lean` packages the
literal division by squared gaps into an ℓp sequence, including
collapsed gaps; the corresponding psi offset sequence has zero at
the omitted index and the majorant norm bound.
`SourcePsiMidpointDenominator.lean` now proves the locally uniform
lattice denominator bound for the moving omitted midpoint, including
omitted indices in the finite head. `SourcePsiMidpointFilledFactorMajorant.lean`
derives actual chi-error ℓp majorants from quotient errors and a shifted
reciprocal lattice, with a norm bound independent of the deleted index
for bounded root inputs. `SourcePsiBranchFactorMajorant.lean` supplies
those bounds for the actual analytic branches from the full gap product
and common root radius. `SourcePsiFactorMajorantComplexRootAtlas.lean`
restricts each source ball to the majorant neighborhood while preserving
its branches, equations, and root isolation.
`SourcePsiComplexFactorAsymptotics.lean` constructs one common open
simply connected normalized analytic psi extension with locally
uniform chi tail majorants at every complex source. This proves the
tail form of (2.32), with a bound independent of the deleted index.
`CompactNonzeroLowerBound.lean` now turns nonvanishing and continuity
on a compact scalar family into a common positive bound on a closed
metric neighborhood. `SourcePsiUniformFilledBranchStability.lean`
uses the Schwarz lemma and midpoint sequence continuity to place all
actual filled analytic root graphs uniformly near their real gap
vectors, independently of the omitted index.
`SourcePsiMidpointQuotientFiniteHeadLowerBound.lean` proves a positive
regular-quotient midpoint bound near the entire compact real gap
product for every fixed finite selected head.
`SourcePsiFiniteHeadMidpointLowerBound.lean` controls the index ratio
from below and obtains the corresponding actual chi midpoint lower
bound near each real source, uniformly in the omitted index and also
at collapsed selected gaps.
`SourcePsiQuotientUniformJointVariation.lean` applies the Schwarz
lemma to simultaneous variation of the root sequence and source,
using one fixed reference ℓp majorant and one variation constant on
every selected disc. This gives arbitrarily small quotient errors
on the free-centered tail discs throughout one joint neighborhood.
`SourcePsiQuotientUniformGapProductTail.lean` uses compactness to give
one tail cutoff and closed neighborhood for the entire real gap
product and reference source. Combining this tail estimate with
finite-head nonvanishing gives a positive midpoint quotient bound
for every selected index. `SourcePsiUniformMidpointLowerBound.lean`
puts all actual filled branches in that neighborhood and proves the
chi midpoint lower bound uniformly over both indices, including
collapsed gaps. `SourcePsiMidpointBoundComplexRootAtlas.lean`
restricts the atlas source balls while retaining their chi majorants.
`SourcePsiComplexMidpointBounds.lean` constructs one common open
simply connected normalized analytic psi extension with positive
midpoint bounds and chi tail majorants locally at every complex
source, independently of both indices.
`SourcePsiGapProductDiscBound.lean` gives one quotient bound on a fixed
compact disc near the entire real gap product and reference source.
`SourcePsiLocalAssignedContourZero.lean` gives actual retained contour
zeros simultaneously on the fixed assigned boundaries near each real
source. `SourcePsiMidpointNormalizedOffset.lean` rescales chi to make
its midpoint value exactly the regular quotient and proves a quadratic
offset estimate with constants independent of the omitted index.
`SourcePsiCollapsedGapOffsetGeometry.lean` constructs a fixed inner
circle near a collapsed reference gap whose doubled disc stays inside
the assigned disc, separating every other moving midpoint.
`SourcePsiFiniteHeadRootOffset.lean` instantiates the rescaled contour
estimate for all actual analytic branches near a collapsed reference
gap, including complex sources with zero selected gap. Noncollapsed
reference gaps use continuity and assigned root placement. A finite
intersection gives one actual squared-gap offset bound for any fixed
finite head, uniformly over omitted indices near each real source.
`SourcePsiActualTailRootOffset.lean` transfers the actual retained
contour zeros to the free-centered tail circles and instantiates the
quadratic estimate with an ℓp majorant whose norm bound is independent
of the omitted index. `SourcePsiUniformSquaredGapOffsets.lean` patches
its finite head with the uniform head estimate and constructs the
actual ℓp quotient by squared gaps, including collapsed gaps.
`SourcePsiSquaredGapComplexRootAtlas.lean` restricts the source balls
to the offset bounds while preserving the analytic branches, assigned
root placement, chi majorants, and midpoint lower bounds.
`SourcePsiLemma12_12.lean` proves the full source-space Lemma 12.12 on
one common open simply connected normalized analytic psi domain.
The actual squared-gap offset norm is uniform over omitted indices
and locally uniform at every complex source. Filling the omitted
root with its moving midpoint gives the factorization at every index;
the offset there is zero. Its power-sum corollary proves explicit
summability and the literal locally uniform bound on `∑ |α_m^n|^p`.
Section 13 now has the actual terminal square-root sheets and regular
angular integrals. `SourceAngularRootSheet.lean` constructs jointly
analytic sheets normalized to the actual anti-discriminant at moving
Dirichlet roots, including terminal points on the canonical branch cut.
`SourceAngularDirichletRegularity.lean` identifies nonzero terminal
values with the exclusion of the two assigned periodic endpoints,
using actual spectral exhaustion and disjoint cluster isolation.
`SourceAngularIntegrand.lean` defines integrands and curve integrals
from the proved Lemma 12.12 psi family, proves joint analyticity on
regular sheets, and proves integrability and path independence for C¹
paths within convex regular charts.

`SourceStandardRootComplexEndpointBound.lean` and
`SourceAngularEndpointBound.lean` now prove inverse-square-root
control of the actual angular integrand at either endpoint of a
noncollapsed complex gap, for either spectral sheet.
`SourceAngularEndpointConnector.lean` proves integrability and a
quantitative integral bound for C¹ curved connectors leaving the
endpoint at a linear radial rate. `SourceAngularEndpointCommonDomain.lean`
derives their spectral hypotheses from the actual psi family and
isolation data on one open complex neighborhood of the entire real
locus. `SourceAngularImproperEndpointIntegral.lean` identifies these
curve integrals with limits of regular parameter truncations.
`SourceAngularCollapsedIntegrand.lean` proves that the actual
off-diagonal psi numerator vanishes at a collapsed complex gap's
midpoint and constructs its analytic removable extension by a filled
divided difference. `CurveIntegralInteriorCongruence.lean` and
`SourceAngularCollapsedPathIntegral.lean` identify the raw canonical
curve integral with this extension, including paths with the midpoint
as an endpoint, and prove path independence and zero loop integrals
in convex omitted-root charts. Negating the sheet negates the integral.
`SourceAngularCollapsedGapGeometry.lean` instantiates these results on
the full assigned isolating disc. Real interlacing identifies the
Dirichlet terminal with the collapsed endpoint, so its off-diagonal
angular integral is zero on both canonical sheet signs.
`CircleLogarithmicPrimitive.lean` constructs a single-valued exterior
Cauchy-transform primitive by integrating a normalized logarithmic
kernel; a zero contour period cancels its reciprocal correction term.
`AnnularHolomorphicPrimitive.lean` combines it with annular Cauchy
decomposition to prove existence of a primitive on a whole zero-period
annulus and path independence for arbitrary C¹ paths there, regardless
of winding. `SourceAngularAnnulusPrimitive.lean` supplies the periods
from actual Lemma 12.12 normalization and constructs one all-gap
annulus family at every complex source, simultaneously for all
off-diagonal indices. Their actual angular integrals are primitive
endpoint differences. `RadialSegmentGeometry.lean` proves outward
connector and annular-anchor geometry for star-convex cuts, also
when the radial and circle centers differ.
`PrimitiveRadialContinuation.lean` proves anchor independence and
local holomorphy by comparing convex-neighborhood primitives.
`PrimitiveOnDiscComplement.lean` extends an annular primitive to the
entire enclosing disc minus its cut, retaining its annular values.
`SourceAngularDiscComplementPrimitive.lean` applies this to each
actual moving gap at every complex source, simultaneously for all
off-diagonal indices. Every regular C¹ integral on the full cut
complement is a primitive endpoint difference, with arbitrary winding
and no homotopy assumption.
`SlitPrimitiveBoundary.lean` removes inverse-square-root derivative
growth by the coordinate `z = -w²` and proves one common boundary
limit for all approaches in the local slit complement.
`SegmentPrimitiveBoundary.lean` transfers it to both endpoints of any
complex segment. `SourceAngularPrimitiveBoundary.lean` applies the
proved actual bound to the full-domain off-diagonal primitives, giving
common limits at each noncollapsed complex periodic endpoint on one
all-gap disc family. `PrimitiveBoundaryPathIntegral.lean` and
`SourceAngularEndpointPathIndependence.lean` prove path independence
for integrable C¹ paths with regular or periodic endpoints, including
singular ends and arbitrary winding in the cut complement.
`CosineSegmentGeometry.lean` and `CosineRootCoefficient.lean` cancel
the endpoint square root in a cosine coordinate and prove that its
differential coefficient is constant on each connected angle chart,
with opposite signs on opposite charts.
`CosinePrimitiveEndpointAgreement.lean` compares the pulled-back
primitive with an analytic numerator primitive across the real angle
interval. Its endpoint differences are both equal and opposite, so
the two spectral boundary values coincide for any complex gap.
`SourceAngularPrimitiveCommonBoundary.lean` applies this to the actual
angular quotient and supplies a common all-gap family. Every integrable
C¹ path from the left periodic endpoint to either periodic endpoint
has zero off-diagonal integral on both canonical sheet signs.

The normalized cosine pullback is now exposed by
`CosinePrimitiveEndpointAgreement.lean`, using only the left endpoint
limit. `CosineRootCoefficient.lean` extends coefficient constancy to
connected charts crossing real regular angles, and
`CosineSegmentGeometry.lean` supplies those angles at every interior
point of a complex gap. `CosinePrimitiveSheetContinuation.lean` uses
the analytic cosine inverse to continue the normalized primitive onto
any regular prescribed sheet near that point. It proves both the exact
derivative and the exterior matching formula with the ratio of root sheets.

`SourceAngularCutInteriorPrimitive.lean` transfers the construction
to the actual angular integrand, including the literal `2i` factor.
The normalized psi family provides local analytic primitives at every
interior Dirichlet terminal, on a sheet whose terminal value is the
actual anti-discriminant. Endpoint exclusions and gap isolation prove
that this value is nonzero. The theorem applies at fixed complex
sources and requires the Dirichlet terminal to lie in its selected
gap interior; it does not assert that all complex Dirichlet terminals
do so.

`DenseSegmentComplement.lean` identifies continuous local continuations
from their values off a complex gap. `RootRatioPrimitive.lean` transports
the normalized exterior primitive to any regular prescribed sheet using
the locally constant full-root ratio. `DensePrimitiveGluing.lean` glues
these exterior values with the cut-interior charts into one analytic
primitive. The extension is unique among compatible continuous charts
for the fixed exterior normalization. `DensePrimitiveBoundary.lean`
retains its zero endpoint limit also for approaches through the cut.

`SourceAngularGluedSheetPrimitive.lean` gives the actual normalized
primitive on the entire regular prescribed-sheet part of each enclosing
disc, including the cut interior, with zero relative value at both
periodic endpoints. `SourceAngularGluedSheetPathIntegral.lean` evaluates
regular C¹ paths crossing the canonical cut by primitive differences,
and integrable singular-start paths by the normalized terminal value.
The actual psi family supplies these functions simultaneously for all
noncollapsed off-diagonal pairs. Singular-start integrability is explicit.

`ComplexSegmentComplementConnected.lean` proves path connectedness
of the cut complement inside any open convex domain containing the
left endpoint. `NormalizedSegmentPrimitiveUnique.lean` identifies the
additive constant of two exterior primitives using their endpoint
limits, then extends equality of normalized regular-sheet values
through the cut by density.

`SourceAngularPrimitiveChoiceIndependence.lean` applies this comparison
to the actual angular primitives. Different exterior primitives,
constants, and enclosing discs give the same values on overlapping
regular sheet domains. Different root charts also agree at a terminal
where their root values agree. Charts matching the actual Dirichlet
anti-discriminant therefore give one Dirichlet terminal value, including
on the cut, provided that the terminal is in both enclosing discs.
The actual psi family supplies all primitive data used by these
comparisons. Integrable C¹ endpoint paths in different discs and root
charts have equal actual integrals when their terminal roots agree.

`SourceAngularDirichletDiscFamily.lean` now constructs contour families
whose original assigned discs contain all actual Dirichlet terminals
and have exact Kronecker periods. One open neighborhood of all real
sources supports these families and the endpoint data, while retaining
the original simply connected Lemma 12.12 domain separately.

`SourceAngularDirichletDiscPrimitive.lean` constructs the angular
primitives on those original discs, retaining their full radii. The
actual Dirichlet terminal belongs to the regular prescribed-sheet
primitive domain. Avoidance of the other gaps proves nonzero terminal
anti-discriminant from Section 13's own endpoint exclusions; callers
do not supply terminal containment, root regularity, periods, or primitives
to the common-domain construction.

`SourceAngularRegularDirichletValue.lean` proves existence of a unique
regular Dirichlet angular value among constructions on every enclosing
disc, for all noncollapsed off-diagonal pairs on this common source
neighborhood under the two terminal endpoint exclusions. Every
integrable C¹ endpoint path on its prescribed
sheet evaluates to the constructed terminal value. Singular-start
integrability remains explicit, and source joint analyticity of the
primitive values has not yet been proved.

The normalized primitive comparisons now also include a collapsed
singleton cut. `ComplexSegmentComplementConnected.lean` proves path
connectedness of punctured open convex complex domains, so uniqueness
in `NormalizedSegmentPrimitiveUnique.lean` and
`SourceAngularPrimitiveChoiceIndependence.lean` requires no noncollapse
assumption.

`SourceAngularCollapsedSheetPrimitive.lean` uses the removable canonical
integrand to construct a primitive throughout the whole collapsed-gap
disc, including its endpoint. The exact root ratio transports its
normalized value to each regular prescribed sheet. Actual assigned
discs then supply unique regular Dirichlet values also at complex
collapsed gaps, without assuming that their Dirichlet roots equal the
collapsed endpoints.

`SourceAngularBeta.lean` defines the actual off-diagonal beta values:
the unique normalized primitive value at a regular Dirichlet terminal,
and zero at either periodic endpoint. One common open neighborhood of
all real sources supplies existence and uniqueness for all off-diagonal
pairs, including collapsed gaps and periodic terminals. Integrable C¹
endpoint paths on the normalized regular prescribed sheet evaluate to
beta; at periodic terminals the integral is zero on every regular
prescribed sheet. Real collapsed gaps have zero beta value by interlacing.

The pointwise beta values are now constructed. Joint source analyticity,
continuity across changing terminal types, uniform Theorem 13.1 bounds,
the diagonal eta values, and the convergent angular sum remain unfinished.
The path formulas retain explicit singular-start integrability and
require interiors in the regular sheet part of an enclosing disc.

`CanonicalPeriodOneBoundaryAnalytic.lean` now proves algebraic simplicity
and complex source analyticity of every Dirichlet and Neumann coordinate
at every real source, including central indices and collapsed periodic
gaps. Strict real interlacing separates the indexed roots, and their
complete canonical multiplicity formula gives multiplicity one.
`BoundarySimpleBranchAnalytic.lean` then identifies a continuous simple
branch locally with its analytic rank-one contour trace.

`SourceBoundaryRootsAnalyticNeighborhood.lean` combines the finite central
blocks with the uniform tail contour formulas to produce one open
neighborhood supporting all coordinates of both boundary sequences.
`SourceAngularBetaBoundaryDomain.lean` places the constructed beta values
on such a neighborhood, retaining the original simply connected psi
domain. Thus the moving Dirichlet terminals are analytic on the beta
construction domain. The following steps construct canonical
periodic-endpoint primitive families and prove beta source analyticity
at every terminal of an open real gap. Collapsed-gap source analyticity
remains to be proved.

`ParametricIntervalIntegralAnalytic.lean` proves full Banach source
analyticity of fixed interval integrals of jointly analytic families.
Compactness supplies the derivative bounds needed for differentiation
under the integral; callers need not assume them. Iterating the
operator-valued derivative gives complex smoothness and a power series.

`ParametricConvexPrimitive.lean` constructs an explicit jointly analytic
primitive by integrating along the affine segment from a fixed anchor.
Its anchor value is zero, its spectral derivative is the original
integrand, and it equals the endpoint difference of every primitive.
Evaluation at an analytic moving terminal is analytic.

`ParametricCosinePrimitive.lean` normalizes such a family at the fixed
angle pi. It matches an endpoint-normalized spectral primitive with the
exact selected-root sheet coefficient on their common angle chart.
`SourceAngularJointPrimitive.lean` applies this to the actual regular
angular integrands and gap numerators, including analytic evaluation
at a moving regular Dirichlet root. One common beta neighborhood supports
all jointly analytic gap numerators and both analytic boundary sequences.
The regular sheet primitives use a fixed regular anchor. The generic
cosine construction accepts analytic midpoint/half-gap functions and a
common angle chart. The following step constructs these from the
canonical roots near open real gaps. The later cosine and Cauchy
constructions prove beta analyticity through periodic terminals and
collapsed real gaps, as described below.

`AnalyticFromSquare.lean` recovers analyticity of a continuous nonzero
root from its analytic square. `SourceOpenGapEndpointAnalytic.lean`
therefore proves source analyticity of the actual canonical gap and
both labeled periodic endpoints near every open real gap, including
central indices.

`ParametricCosineChart.lean` constructs one open convex chart containing
the full real angle interval and one source neighborhood whose cosine
images remain in the joint spectral domain. Compactness supplies this
geometry. `SourceAngularCanonicalCosinePrimitive.lean` uses the actual
canonical midpoint and half-gap to construct jointly analytic cosine
primitives for every numerator index on the same local chart. The
original assigned discs still contain the moving Dirichlet terminals
and have the exact contour periods. At each source, these primitives
match the actual endpoint-normalized canonical spectral primitives
with the exact selected-root coefficient on a chart containing the
whole angle interval. The preserved periods construct the off-diagonal
sheet primitives used in this matching.

`SourceAngularCanonicalCosineCommonDomain.lean` places these local charts
near every open real gap on a common domain retaining all pointwise
beta values and both analytic boundary-coordinate sequences. The full
simply connected psi extension is retained on its original domain.
The endpoint normalization is now transferred to the Dirichlet sheet
at every terminal of an open real gap as described below. The Cauchy
construction supplies source analyticity at collapsed real gaps. The
later uniform-annulus construction places every term on one common
complex domain. Theorem 13.1's estimates remain unfinished.

`ParametricCosineTerminal.lean` constructs the analytic moving cosine
angle of an analytic spectral terminal at a noncritical base angle.
The implicit function theorem supplies both the angle and its exact
terminal equation near the base source.

`SourceAngularCanonicalCosineSheetMatching.lean` extends canonical
exterior matching throughout the convex angle chart's two halves.
Continuity and density then give the prescribed-sheet formula at
every regular chart point, including real angles on the cut. The
canonical chart data also retain the jointly analytic omitted product
on the original assigned disc and source neighborhood.

`SourceAngularBetaRegularAnalytic.lean` identifies the actual beta
value with this joint cosine primitive evaluated at the moving angle,
multiplied by an explicit analytic coefficient normalized by the
actual Dirichlet anti-discriminant. It proves complex source
analyticity of beta at every real source with a regular Dirichlet
terminal, for every off-diagonal pair and including central indices.
One actual common beta domain retains all pointwise values, both
analytic boundary sequences, and the full simply connected psi
extension. The following step supplies periodic-terminal source
analyticity on open real gaps; the later Cauchy construction covers
collapsed real gaps as well. The uniform-annulus construction below
gives a common complex analytic domain and hence continuity there.
The uniform bounds, diagonal eta, and the angular sum remain unfinished.

`ParametricSineTerminal.lean` constructs an analytic moving angle from
an analytic prescribed sine. At cosine endpoints the sine derivative
is nonzero. The spectral square identity and continuity recover the
cosine terminal equation with its exact sign.

`SourceAngularCanonicalCosineEndpoint.lean` proves that each actual
off-diagonal cosine primitive vanishes at both endpoint angles. Its
even derivative and the opposite exterior root coefficients force
the right-endpoint normalization as well as the left anchor. The
normalized actual Dirichlet anti-discriminant is an analytic sine
coordinate on open gap charts and satisfies the exact sine/cosine
square identity through a periodic terminal.

`SourceAngularBetaEndpointAnalytic.lean` uses this coordinate to
construct an analytic moving angle near either periodic Dirichlet
endpoint. Its normalized sine fixes the regular-terminal sheet
coefficient to minus i, and both endpoint-angle values are zero.
The same analytic expression agrees with beta through nearby regular
and endpoint terminals. Thus beta is complex source analytic at every
real source with an open selected gap, for every off-diagonal pair,
including central indices and both periodic terminals. The Cauchy
construction below also proves analyticity at collapsed real gaps.
The uniform-annulus construction supplies the common complex domain.
Theorem 13.1's bounds and angular-sum assertions remain to be proved.

`ParametricCircleTransforms.lean` proves joint Banach source and spectral
analyticity of fixed-circle Cauchy and exterior logarithmic transforms.
`ParametricAnnularPrimitive.lean` combines them into an explicit primitive
on the whole zero-period annulus, normalized at a fixed regular anchor.
The construction permits arbitrary winding and has an exact derivative.

`SourceAngularJointAnnulusPrimitive.lean` constructs such charts from the
actual canonical root, symmetric periodic coordinates, and assigned
contour periods near every real source. One chart supports every
off-diagonal numerator around the selected gap, including a collapsed
gap, and its inner disc contains the moving Dirichlet terminal. A common
domain retains both analytic boundary sequences, all actual beta values,
open-gap beta analyticity, and the full simply connected psi extension.

`SourceStandardRootCauchyZero.lean` proves that the reciprocal selected
standard root has zero interior Cauchy transform on every enclosing
circle. Inversion proves the result on large circles and annular Cauchy's
theorem transfers it to any assigned circle. Thus every additive
primitive constant cancels from the interior projection after division
by the selected root.

`SourceAngularCauchyCandidate.lean` uses this projection to construct a
jointly analytic quotient candidate on the whole enclosing disc.
Multiplication by the actual Dirichlet anti-discriminant coefficient and
evaluation at the moving terminal give a source-analytic angular
candidate at every real source, including collapsed gaps. The candidate
agrees with actual beta at endpoint terminals and collapsed real base
points. The following differential-equation argument identifies it at
nearby regular terminals as well.

`CircleCauchyTransformDerivative.lean` differentiates the Cauchy kernel
for a density analytic near the integrating circle.
`QuadraticCauchyEquation.lean` proves that interior Cauchy projection
preserves the equation `D H' + (z - tau) H = g`, where
`D = (z - tau)^2 - gap^2 / 4`: the difference of the kernels integrates
to zero as a full derivative around the circle.
`QuadraticRootPrimitive.lean` turns any analytic solution into a
primitive on every regular square-root sheet. Its limit at either
quadratic endpoint is zero, including a collapsed pair, because the
root square tends to zero and the solution stays analytic.

`SourceAngularCauchyEquation.lean` proves this equation for the actual
angular quotient candidate. `SourceAngularCauchySheetPrimitive.lean`
constructs actual normalized canonical and prescribed-sheet primitives
on the enclosing disc, with exact derivatives, zero endpoint limits,
and the required exterior matching coefficient.

`SourceAngularBetaCauchyAnalytic.lean` identifies the candidate with
actual beta throughout each local source chart, including nearby
complex sources, regular Dirichlet terminals, and both endpoint
conventions. Consequently every off-diagonal beta term is complex
source analytic at every real source, without a nonzero-gap condition.
The common-domain theorem retains all unique beta values, both analytic
boundary sequences, the full simply connected psi extension, and
annular charts for every selected index. All off-diagonal terms for that
selected index are analytic on the chart's complex source neighborhood.
This includes central indices and collapsed real gaps. The next
construction makes one source neighborhood support every selected index.

`LocallyUniformCoordinates.lean` proves that a continuous map into a
finite-exponent sequence space has uniformly small distant coordinates
on one source neighborhood. `SourceBoundaryDisplacementAnalytic.lean`
assembles the actual ordinary Dirichlet and Neumann displacement
sequences into Banach-analytic maps wherever all scalar roots are
analytic, using the existing local sequence-norm bounds. Consequently
both sequences have arbitrarily small distant free-disc displacements
on a common complex neighborhood of each real source.

`SourceAngularUniformAnnulusPrimitive.lean` combines the actual
Dirichlet tail with the uniform periodic midpoint and gap tails. Every
distant gap and terminal lie in a free sixteenth-pi disc, inside a
free eighth-pi annulus and the original quarter-pi assigned disc.
Fixed inner and outer radii give
all distant joint annular charts at once. Only the finitely many
remaining chart neighborhoods are intersected. Thus every selected
gap has a chart on one shared source neighborhood, including central
indices and collapsed gaps. The geometric chart constructor and source
restriction preserve all actual contour periods and primitives.

`SourceAngularBetaAnalyticCommonDomain.lean` takes the union of these
neighborhoods over the entire real source locus. On the resulting
common open complex domain every off-diagonal beta term is analytic.
The theorem retains unique actual beta values, both Banach-analytic
boundary displacement sequences, analytic scalar boundary roots,
analytic periodic midpoints and squared gaps, and the full simply
connected psi extension on its original domain. This proves the
analyticity assertion of Theorem 13.1(i) for all indices. Its uniform
quantitative estimate, diagonal eta modulo pi, the angular sum and its
decay, and the reality and canonical-bracket assertions remain unfinished.

`CirclePrimitiveBounds.lean` bounds a primitive's variation on an
entire enclosing circle by the half-circle length times its derivative
bound. The normalized Cauchy transform then has an explicit bound on
any smaller concentric disc. `QuadraticRootBounds.lean` supplies bounds
that depend only on the root square, allowing either sheet and zero gaps.

`SourceAngularBetaBound.lean` proves that the actual normalized Dirichlet
coefficient squares to the selected quadratic polynomial. Its norm is
at most `|mu_m - tau_m| + |gamma_m|/2`, with no nonzero-gap or
regular-terminal assumption. On a chart circle of radius `rho`, the
selected root is bounded below by `rho - r`. Removing the primitive's
constant in the Cauchy projection gives the explicit quotient bound
`pi * rho^2 * M / (rho - r)^3` whenever the actual gap numerator is
bounded by `M` on that circle. Multiplying the two estimates bounds the
actual beta throughout the complex chart, including collapsed gaps
and endpoint terminals.

`SourceAngularBetaLocalBound.lean` proves joint analyticity of the actual
gap numerator on the annulus. Compactness then supplies a local circle
bound at every complex source in the chart, hence a local beta bound
by `|gamma_m| + |mu_m - tau_m|`. This constant can depend on both indices.

`SourceAngularBetaRegularFactorBound.lean` identifies the actual gap
numerator with the retained psi root factor times the midpoint-filled
regular factor chi, divided by `pi * (n - m)`. A circle bound on chi
therefore gives an explicit beta estimate with the required
`1/|n - m|` factor. The remaining work for the quantitative assertion
of Theorem 13.1(i) is to assemble local bounds on chi and retained
roots, and chart radii, that are uniform in both indices. The fixed-pair
local estimates alone do not prove that uniform assertion.

`SourcePsiUniformRetainedRootBounds.lean` uses Lemma 12.12's actual
squared-gap offset sequences and the midpoint and gap norm bounds to
bound every retained psi root displacement from its free lattice point.
The bound is locally uniform at every complex source of the psi domain
and independent of both integer indices. The chi sequence majorants
also give one scalar bound on all sufficiently distant selected
eighth-pi discs, independent of the deleted index.

`SourceAngularUniformAnnulusPrimitive.lean` now exposes the quantitative
tail geometry: inner radius `pi/16`, outer radius `pi/8`, and circle
radius `3*pi/32`. All distant gaps and actual Dirichlet terminals lie
inside the inner disc. The whole circle lies inside the free disc of
the chi estimate, and the original quarter-pi assigned discs preserve
all exact periods and separation. The previous all-index chart theorem
uses this smaller tail family and a finite intersection for the head.

`SourceAngularBetaUniformTailBound.lean` combines these fixed charts
with the actual retained-root and chi bounds. One positive constant
and one selected-index cutoff work for every deleted index and every
selected index beyond the cutoff, on one complex source neighborhood:
`|beta_n^m| <= C * (|gamma_m| + |mu_m - tau_m|) / |n - m|`.
This includes collapsed gaps and endpoint terminals.

`SourceAngularBetaUniformTailCommonDomain.lean` takes the union of
these quantitative source neighborhoods over the entire real locus.
Every complex source in the resulting common open domain has a local
estimate with a constant and cutoff independent of both indices.
All beta terms remain analytic, both boundary displacement sequences
remain Banach analytic, all beta values retain their uniqueness, and
the full simply connected psi extension remains on its original domain.
The following construction also covers the finite selected central
gaps, with a bound uniform over all deleted indices.

`SourcePsiExtensionUniformFilledStability.lean` identifies the actual
analytic psi extension with a uniform branch family on one source ball,
using real agreement and the Banach identity theorem. The existing
Schwarz estimate therefore controls every midpoint-filled root graph
near its real gap-root vector, independently of the deleted index.

`SourcePsiMidpointShiftedDiscBound.lean` permits both the omitted
midpoint and the selected disc to move from their free lattice points.
Once the index difference dominates their shifts and the disc radius,
the midpoint denominator retains half the lattice separation. A compact
quotient bound then gives a uniform bound on chi on that selected disc.

`SourceAngularBetaUniformSelectedBound.lean` applies compact gap-product
quotient bounds to every actual filled root graph on a fixed selected
chart. One chi bound and retained-root bound cover all distant deleted
indices. A finite intersection of the actual local beta neighborhoods
covers the remaining deleted indices; a finite maximum index distance
restores the reciprocal-index factor. Thus a central selected gap has
one source neighborhood and beta constant for every deleted index,
also at collapsed gaps and endpoint terminals.

`SourceAngularBetaUniformBound.lean` combines the uniform selected-gap
tail with the finitely many central chart bounds. One source neighborhood
and positive constant control every off-diagonal pair, with no cutoff
in either index.

`SourceAngularBetaTheorem13_1.lean` proves Theorem 13.1(i) in full.
`exists_sourceAngularBeta_theorem13_1_i` gives one common open complex
neighborhood of the entire real source locus on which every actual
beta term is analytic and
`|beta_n^m| <= C * (|gamma_m| + |mu_m - tau_m|) / |n - m|`
locally uniformly at every complex source, with one constant for all
indices. Unique actual beta values, both analytic scalar boundary-root
families, both Banach-analytic boundary displacement sequences, and
analytic midpoint and squared-gap coordinates are retained. The full
normalized psi family remains on its original simply connected domain.

`UniformHolderSums.lean` proves absolute summability under the sum of
two actual coefficient-space majorants. A fixed finite-exponent
conjugate multiplier has vanishing norm tails, so the same estimate
makes symmetric sums uniformly Cauchy on any norm-bounded family.

`SourceAngularBetaSeries.lean` defines the actual correction
`sourceAngularBetaCorrection` with its diagonal omitted explicitly.
The actual gap sequence and the Dirichlet-minus-midpoint displacement
sequence are in `l^p`; the translated punctured reciprocal lattice is
in the finite conjugate space. Holder therefore proves absolute
convergence, with a bound independent of the deleted index. Local
sequence-norm bounds give uniform convergence of the symmetric partial
sums on one smaller open source neighborhood, for every deleted index.

`SourceAngularBetaSeriesAnalytic.lean` proves that the correction is
Banach analytic on the same common angular domain. The finite partial
sums are analytic, and the existing Banach holomorphic-limit theorem
and complex-smooth-to-analytic theorem apply to their local uniform
limit. `exists_sourceAngularBetaSeries_analytic_common_domain` retains
all data from Theorem 13.1(i) and adds absolute summability, local
uniform convergence, and analyticity of the actual beta correction
series, including collapsed gaps and endpoint terminals.

`ShiftedHolderDecay.lean` proves that absolute Holder pairings with
translated finite-exponent coefficient sequences vanish as the absolute
index tends to infinity. A finite truncation of the first sequence has
a vanishing finite head; Holder bounds the remainder uniformly by its
small coefficient-space norm. The result also applies to arbitrary
double-indexed series dominated by two such majorants.

`SourceAngularBetaDecay.lean` applies this result to the actual gap and
Dirichlet-minus-midpoint displacement sequences and the translated
punctured reciprocal lattice. The complete absolute beta sum tends to
zero at every complex source, which proves `beta^n = o(1)` in both
integer-index directions, including collapsed gaps and endpoint terminals.

`SourceAngularBetaTheorem13_1Series.lean` proves Theorem 13.1(i) and
(iii) in full. `exists_sourceAngularBeta_theorem13_1_i_iii` retains
the original normalized psi extension, both analytic scalar boundary
root families, both Banach-analytic boundary displacement sequences,
analytic midpoint and squared-gap coordinates, unique actual beta
values, and the locally uniform all-index reciprocal bound. On that
same common complex domain, `SourceAngularBetaSeriesData` records
absolute and local uniform convergence of the actual correction series,
its analyticity, and the decay of both its absolute sum and its value.

`ParametricTrigonometricTerminal.lean` constructs an analytic moving
angle with both prescribed sine and cosine coordinates, including
either cosine endpoint. Compatible angles differ by an integer
multiple of two pi. `SourceAngularDirichletAngle.lean` applies this
to the actual Dirichlet root and its normalized anti-discriminant:
every open real gap has an analytic terminal angle on a complex source
neighborhood and one fixed sheet sign.

`SourceAngularCosineLift.lean` constructs the literal discriminant
root on that cosine cover. Its square is the original radicand, it
is nonzero away from sine zeros, and its terminal value equals the
actual Dirichlet anti-discriminant, including at either endpoint.
Pulling back the original psi/root differential gives the regular
cosine numerator with the exact sheet coefficient; the numerator
index may equal the selected gap index.

`SourceAngularEtaCosineRepresentative.lean` defines the actual
diagonal eta representative, normalized to zero at angle pi. It is
jointly analytic in angle and source, and equals the integral of the
literal lifted differential along C1 angle paths whose interiors
avoid sine zeros. Singular terminal endpoints are allowed. Composing
with the constructed moving Dirichlet angle proves source analyticity
near every open real gap, including both endpoint terminal cases.

`SourceAngularEtaLocalCommonDomain.lean` constructs these local eta
charts on a common complex neighborhood of the entire real locus,
for the same normalized psi extension as Theorem 13.1(i) and (iii).
The theorem retains every beta value, analytic boundary and symmetric
coordinate, uniform all-index beta bound, and analytic correction
series with its decay.

`SourceAngularCosinePeriod.lean` derives the exact full-gap cosine
periods from the original normalized psi contours. The contour is
twice the upper gap-side integral, and the fundamental theorem of
calculus identifies this with the angle primitive at zero. Its value
is zero off the diagonal and `-i*pi` on the diagonal. Real-form analytic
continuation gives all these exact values on one complex source ball,
simultaneously for every numerator index.

`SourceAngularEtaSheetReflection.lean` proves the primitive reflection
identity and constructs the eta representative on the reflected angle
chart, normalized at minus pi. Both charts are jointly analytic and
have the same angular differential. Their normalizations differ on
the overlap by `2*kappa*pi`, so they agree modulo two pi and modulo pi
for either allowed sheet sign. Reflecting the angle and reversing the
sign preserves the actual spectral terminal and lifted root, and gives
exactly the same eta terminal value on the reflected chart. At the
right endpoint the original representative is `-kappa*pi`.

`SourceAngularEtaPeriodCommonDomain.lean` retains these exact periods
on each moving terminal's own source neighborhood, together with
both analytic sheet representatives and their overlap compatibility.
The same common-domain theorem preserves every previously proved
beta assertion and the full normalized psi extension.

`SourceAngularEtaRemainder.lean` separates the actual diagonal eta
differential into the explicit model `i / standardRoot` and a remainder
with regular numerator `gapNumerator - i`. The model has exact contour
period `2*pi`, so the actual normalized psi contour makes the remainder
period zero, for any complex source and also for collapsed gaps.

`SourceAngularEtaRemainderPrimitive.lean` constructs single-valued
remainder primitives on an all-gap family of entire isolating discs
minus their cuts. Every regular C1 spectral path in these domains has
an actual diagonal integral equal to its explicit model integral plus
the remainder primitive's endpoint difference. Arbitrary winding only
affects the explicit model term.

`SourceAngularEtaRemainderBoundary.lean` proves a weighted endpoint
bound from the actual remainder numerator. Both limits of any remainder
primitive exist for every approach in the cut complement, and the cosine
comparison makes them equal. At every complex source with the actual
endpoint spectral data, each open-gap remainder therefore has a primitive
normalized to zero at both endpoints. The integral splitting also holds
for paths with singular endpoints when the actual and model integrals
are integrable and the primitive's endpoint limits are specified.

`LogarithmicPathIntegral.lean` proves the scalar integrating-factor
identity for an integrable coefficient continuous on the open interval.
No endpoint derivatives are required. It evaluates exponentiated
logarithmic curve integrals from continuous endpoint data, and proves
that two such integrals differ by an integer multiple of `2*pi*i`.

`SourceAngularEtaModelCoordinate.lean` applies this to the spectral
coordinate `z - midpoint - standardRoot z`. The coordinate is nonzero
off the gap even when the gap collapses, and its logarithmic derivative
is `i` times the eta model differential. At both endpoints of an open
complex gap, the standard root and coordinate are continuous, and the
coordinate is nonzero.

`SourceAngularEtaModelPathPeriod.lean` proves that arbitrary model
path integrals with common endpoints differ by an integer multiple of
`2*pi`. Regular C1 paths require no supplied integrability and cover
collapsed gaps. For an open complex gap, integrable paths may start
or end at either periodic endpoint. Their interiors avoid the cut;
no homotopy or restriction on winding is required.

`SourceAngularEtaCanonicalPathPeriod.lean` combines these periods
with the single-valued remainder. At every complex source in the
actual normalized psi domain, one all-gap family has regular diagonal
canonical-sheet path independence modulo `2*pi`. The actual endpoint
spectral data also give this result for singular-start open-gap paths
with terminal outside the cut or at either periodic endpoint, assuming
integrability of both the actual and model differentials. The primitive
and its endpoint limits are constructed from the original normalization.

`GapRootPrimitiveGluing.lean` glues an endpoint-normalized exterior
primitive onto the whole regular domain of any analytic root of the
same gap endpoint polynomial. Cosine continuation supplies all interior
cut charts, and agreement on the dense cut complement fixes their
overlaps and the continuous extension uniquely.

`SourceAngularEtaPrescribedSheet.lean` splits the actual diagonal
differential on a prescribed full-root sheet. Dividing that root by
`2*i*omittedProduct` gives a root of the selected endpoint polynomial,
including at points on the canonical cut. The explicit model is
`-2*omittedProduct/fullRoot`; the remainder has numerator
`psiCandidate + 2*omittedProduct` over that same full root.

`SourceAngularEtaRemainderSheetPrimitive.lean` constructs an analytic
remainder primitive on the whole regular prescribed-sheet part of each
open-gap isolating disc. It has the exact full-root ratio matching the
normalized canonical exterior primitive, and both periodic endpoint
limits remain zero, including approaches through the cut. These data
are constructed at every complex source from the actual normalized psi
family and endpoint spectral data, on every regular prescribed sheet.

`SourceAngularEtaModelSheetCoordinate.lean` proves the corresponding
logarithmic model identity on the prescribed sheet. The coordinate
`z - midpoint - selectedSheetRoot` is analytic and nonzero throughout
the regular sheet of an open gap, also at cut-interior points. The
selected root tends to zero at either periodic endpoint, so the
coordinate has the sheet-independent limit `endpoint - midpoint` there.

`SourceAngularEtaPrescribedSheetPathPeriod.lean` combines this model
with the glued remainder. Integrable C1 paths from a periodic endpoint
to a regular terminal in the same prescribed sheet have actual diagonal
integrals differing by `2*pi*integer`. Their interiors may cross the
canonical cut. The actual Dirichlet theorem constructs the prescribed
sheet from the anti-discriminant whenever its terminal is in the gap
interior; it supplies the remainder data and proves the terminal root
normalization. Integrability of the actual and model differentials is
retained explicitly.

`SourceAngularEtaRemainderChoiceIndependence.lean` constructs the
endpoint-normalized remainder data from the actual psi family and proves
that its values agree across different exterior primitives and isolating
discs. Different regular root charts give the same terminal remainder
whenever their full roots agree there, including on the canonical cut.
In particular, charts matching the actual Dirichlet anti-discriminant
give one remainder value.

`SourceAngularEtaSheetChoicePathPeriod.lean` evaluates the exponential
of the prescribed model integral using its logarithmic coordinate. Its
periodic-start value is independent of the root chart, and equality of
the terminal full roots fixes its terminal value. This gives model
periods in `2*pi*integer` across different charts and discs. Combining
this with exact remainder agreement proves the same statement for the
literal diagonal eta integrals, assuming actual and model integrability.

`SourceAngularEtaSheetChoiceCommonDomain.lean` constructs all required
remainder data at each complex source from the original normalized psi
family. On a common all-gap family of discs, integrable paths to the
actual Dirichlet terminal in different regular charts normalized by its
anti-discriminant have eta values differing by `2*pi*integer`. The
terminal may lie on the cut interior. Each path is contained in its
own regular prescribed chart.

`ContinuousSquareRootPath.lean` proves that continuous roots of the same
nonvanishing square have one fixed relative sign on a connected parameter
set. It also recovers the real-parameter derivative of a continuous
nonzero root from the derivative of its square, using its local prescribed
root. `ContinuousQuadraticRootPathIntegral.lean` applies this to a root
given only along a spectral path and evaluates the exponential of its
logarithmic model integral from the two endpoint values.

`SourceAngularAdmissiblePathRoot.lean` records continuous root continuation
on the paper's admissible paths. Continuity on the closed unit interval
suffices; extension outside it is automatic. The interior avoids the
selected cut and lies in its isolating disc. The continued full root has
one fixed sign relative to the canonical root there, and the literal
angular integral is transported by that sign for every numerator index.
No single prescribed root chart is required to contain the path.

`SourceAngularEtaAdmissiblePathModel.lean` divides the continued full root
by the actual omitted product and evaluates the exponentiated eta model
integral. Two integrable C1 admissible paths from a common periodic
endpoint, with equal terminal full-root values, have model integrals
differing by `2*pi*integer`. This includes regular cut-interior terminals
and periodic endpoints, with arbitrary intermediate root charts. The
model's initial logarithmic coordinate is independent of the root sign.

`SourceAngularAdmissiblePathTerminalSheet.lean` proves that a continued
root agrees near its regular terminal with any analytic root chart having
the same terminal value. The square identity automatically extends outside
the unit interval by clamping. Only the final part of the path is required
to enter the terminal chart.

`SourceAngularEtaAdmissibleRemainder.lean` transports the remainder along
the whole admissible path by its fixed canonical sign. The initial limit
is zero and the final limit is exactly the value of the glued primitive
on the normalized terminal sheet, including at a cut-interior terminal.
The literal eta integral equals its continued-root model integral plus
this terminal remainder. A version stated using a final path limit also
covers singular periodic terminals.

`SourceAngularEtaAdmissiblePathPeriod.lean` combines the remainder with
the continued-root model periods to prove actual eta path independence
modulo `2*pi`. At regular terminals the prescribed chart is used only
locally. At either periodic endpoint the remainder is zero and every
continued full root vanishes, so either root sign gives the same eta value
modulo `2*pi`. A zero Dirichlet anti-discriminant in the isolating domain
is proved to force a periodic endpoint.

`SourceAngularEtaAdmissibleCommonDomain.lean` constructs all remainder
data from the original normalized psi family on one all-gap family of
discs. At each open gap, any two integrable C1 admissible paths to the
actual Dirichlet terminal have eta values differing by `2*pi*integer`,
provided the terminal is in that disc and the continued roots match its
anti-discriminant when it is nonzero. At a periodic terminal no sign
normalization is required. Neither path must stay on a single root chart;
actual and model integrability are retained explicitly.

`LocalAnalyticSquareRoot.lean` constructs an analytic square root near
any analytic radicand with a prescribed nonzero base root, without a
continuous root labeling or a principal-cut restriction on that value.
`ComplexCircleTerminal.lean` constructs a base angle for any complex
sine/cosine pair satisfying the circle identity and analytically continues
both coordinates. Reversing both coordinates changes the angle only by
an integer multiple of `pi`.

`SourceAnalyticHalfGap.lean` applies this to the actual analytic squared
gap at every open complex source gap. The local branch agrees with the
canonical half-gap at its base point. Its two endpoints and their segment
equal the actual unordered periodic pair and cut, even if the canonical
labels exchange places nearby.

`SourceAngularComplexDirichletAngle.lean` normalizes the actual Dirichlet
anti-discriminant by this half-gap and the omitted product. The exact
circle identity gives a constructed analytic moving terminal angle at
arbitrary complex sources, including either periodic endpoint with zero
anti-discriminant. Its lifted root squares to the literal discriminant
radicand throughout its omitted-root domain and equals the actual
anti-discriminant at the terminal.

`SourceAngularComplexAngleCommonDomain.lean` places these constructions
on one open complex neighborhood of the whole real locus. Every open
gap at every complex source there has an analytic half-gap and terminal
angle chart; assigned discs prove the required omitted-domain membership.
Overlapping terminal-angle charts agree modulo `pi`, including opposite
half-gap choices. All existing beta results and real eta charts are
retained on a larger domain. This angle-chart theorem does not yet
identify the integrated eta representatives at general complex sources.

`SourceAngularBranchCosinePrimitive.lean` constructs the actual joint
cosine primitive at every complex open gap with local assigned discs.
The analytic half-gap replaces ordered endpoint analyticity. A constructed
convex angle chart contains the full interval from zero to `pi`, its
spectral images stay in the assigned disc, and every numerator has the
exact primitive derivative and zero normalization at `pi`.

`SourceAngularBranchCosineLift.lean` proves joint analyticity of the
lifted full root, including its endpoint zeros, and its literal
discriminant square identity. Away from sine zeros the actual psi/root
pullback equals `-i` times the regular cosine numerator.

`SourceAngularBranchEtaRepresentative.lean` gives a joint analytic
diagonal representative on these complex branch charts. Every C1 angle
path from `pi` with interior sine nonzero has an automatically integrable
literal pullback whose integral is that representative. An actual
Dirichlet base angle in the chart gives a constructed analytic source
value, with its lifted root exactly normalized to the anti-discriminant.

`SourceAngularBranchEtaTerminal.lean` constructs those source values at
either complex periodic Dirichlet terminal of an open gap. Both base
angles belong to the chart, and the circle identity fixes their zero
sine coordinate. No real-source or nonzero anti-discriminant hypothesis
is required.

`HolomorphicPathPullback.lean` transports integrability and the exact
holomorphic curve integral along a mapped path using only the chain rule
on its open parameter interval. `SourceAngularBranchEtaSpectralPath.lean`
uses this to identify the actual spectral psi/root integral with the
analytic branch representative when the continued root matches the
cosine lift along the interior. The actual and model differentials are
automatically integrable on these mapped C1 paths. The model integral is
exactly the terminal angle minus `pi`, also at a periodic terminal.

`SourceAngularBranchEtaCommonDomain.lean` constructs joint primitive
charts at every complex open gap on one common neighborhood of the
whole real locus, retaining the normalized psi family and all beta
results. Every complex periodic terminal there has a constructed analytic
eta source representative. Regular terminals are covered by the local
representative theorem when their base angle lies in its angle chart.

`SourceAngularEtaJointAnnulus.lean` subtracts the exact diagonal model
period and constructs a jointly analytic annular remainder primitive.
`SourceAngularEtaCauchyCandidate.lean` takes its quotient by the selected
root and projects it into the whole enclosing disc. The result is joint
analytic through the cut, either periodic endpoint, and collapsed gaps.
Its moving Dirichlet evaluation is analytic wherever the actual terminal
is analytic, and vanishes at both periodic terminal conventions.

`SourceAngularEtaCauchyEquation.lean` proves the projected quadratic
root equation with the actual diagonal gap numerator minus `i` as its
right-hand side. `SourceAngularEtaCauchySheetPrimitive.lean` constructs
canonical and prescribed-sheet remainder primitives from this equation.
Both endpoint limits are zero, and the exact exterior root ratio matches
the sheet primitive, also for collapsed gaps.

`SourceAngularEtaCauchyTerminal.lean` identifies the explicit terminal
formula with every normalized remainder primitive matching the actual
anti-discriminant. The formula is independent of the annular chart,
anchor, and enclosing Cauchy circle. The literal eta integral along any
integrable C1 admissible continued root is its model integral plus this
analytic remainder. Actual and model integrability remain hypotheses;
regular terminals require anti-discriminant normalization, while either
root sign is permitted at a periodic terminal.

`SourceAngularEtaCauchyCommonDomain.lean` constructs one open complex
neighborhood of the entire real locus on which every complex source and
every gap index has such an analytic remainder chart. No nonzero-gap
condition or restriction to a convex terminal-angle chart is required.
The established beta results and real eta charts are retained on a
larger domain for the same normalized psi family.

`SourceAngularEtaModelTerminalAngle.lean` identifies every integrable
continued-root model integral with the actual complex terminal angle
modulo `pi`. Squaring its exponential endpoint identity removes the
half-gap sign and periodic anchor choice. Conditional anti-discriminant
normalization also fixes the continued root at a periodic terminal,
where both values vanish.

`SourceAngularEtaPeriodicAnchor.lean` extends the exact Cauchy remainder
decomposition to paths starting at either periodic endpoint. The same
terminal remainder is used because both initial endpoint limits vanish.
`SourceAngularEtaAnalyticRepresentative.lean` combines the terminal
angle minus `pi` with this remainder. The full representative agrees
with every normalized integrable C1 admissible spectral integral modulo
`pi`. Overlapping representatives differ by an integer multiple of `pi`,
including opposite half-gap branches, different annuli, and angle choices.

`SourceAngularEtaAnalyticChart.lean` constructs full eta charts at every
complex open-gap source from the actual annulus and analytic spectral
coordinates. It supplies all endpoint spectral data and source
analyticity, without requiring the terminal angle to lie in a convex
angle chart.

`SourceAngularEtaAnalyticPhase.lean` defines the unique chart-independent
phase `exp(2i eta)`. It is analytic and nonzero on each source chart and
equals the phase of the literal admissible spectral integral. The choice
of either periodic starting endpoint does not change this phase.

`SourceAngularEtaTheorem13_1Analytic.lean` assembles Theorem 13.1(ii) on
one common complex neighborhood of the whole real locus for the actual
normalized psi family. For each index the open-gap source domain is
open, the single eta phase is analytic and nonzero there, and every
complex open-gap source has a constructed local analytic eta
representative. The full beta results of (i) and (iii) are retained on
a larger domain. Literal integral comparisons retain actual and model
integrability as explicit hypotheses, with C1 admissible paths and
conditional normalization at regular terminals.

`QuadraticCosinePrimitive.lean` pulls the quadratic Cauchy equation back
to the cosine angle without division by the sine. The product of the
analytic interior solution with the cosine root has derivative equal
to the rotated numerator, even at either endpoint. If that derivative
is real on the real angle axis, the primitive is real there because its
value at `pi` is zero. Any cosine preimage of a noncollapsed gap point
is real.

`SourceAngularRealNumerator.lean` proves that the actual normalized psi
family has real displaced roots at real potentials. Conjugation of its
entire numerator and reality of the omitted standard-root product show
that the literal angular numerator becomes real after rotation by `-i`.
`SourceAngularCauchyReal.lean` applies the regular cosine calculation to
both off-diagonal beta and the eta remainder. Real interlacing makes
every terminal angle real, including arbitrary angle and half-gap
branches. Actual beta values and full eta representatives are real,
including periodic Dirichlet terminals.

`SourceAngularThetaAnalytic.lean` defines the actual angle representative
as eta plus the convergent beta correction. Absolute convergence makes
the full correction real when its terms are real. Theta representatives
are analytic, agree modulo `pi` on overlaps, and represent one nonzero
phase `exp(2i theta)`. The phase has unit norm at real potentials.
`SourceAngularThetaSpectral.lean` identifies this representative modulo
`pi` with the normalized admissible eta integral plus the actual beta
series. That literal sum is real for real potentials. These comparisons
retain C1 regularity, actual and model integrability, and terminal root
normalization explicitly; both periodic anchors are covered.

`SourceAngularThetaTheorem13_1.lean` assembles Theorem 13.1(iv), retaining
the full beta estimates, series convergence and decay, and eta
analyticity from (i), (ii), and (iii) for the same normalized psi family.
One common neighborhood of the entire real locus carries all results.
All off-diagonal beta terms and their full corrections are real at real
sources, including collapsed gaps. On every indexed open-gap domain,
theta has a single analytic nonzero phase, of unit norm on the real
locus. `exists_local_analytic_real_representative` constructs a local
analytic theta representative at any complex open-gap source and proves
that it is real on the real locus in its chart.

Corollary 13.2 and the later chapters remain.

### Corollary 13.2: bracket and angle differential foundations

`HilbertCotangent.lean` and `SourceCotangent.lean` construct the
square-summable Fourier coefficients of every continuous source
cotangent at `p >= 2`. Bilinear duality recovers its value on every
Hilbert direction, with a bound by the original operator norm.
`SourceBivector.lean` uses these coefficients to construct the physical
`-i` cross-component bracket. Its literal Fourier sum is absolutely
convergent and reverses the frequency in the second factor.

`SourceBracket.lean` applies this continuous bivector to Frechet
derivatives. The bracket is analytic for analytic functionals,
antisymmetric, obeys the product rule, and is preserved by restriction
along source exponent inclusions. `SourceCoordinateBrackets.lean`
checks the physical convention: opposite-component Fourier coordinates
at frequencies `n` and `-n` have bracket `-i`; same-component brackets
vanish.

`SourceAngularThetaDifferential.lean` defines one analytic angle
cotangent on each actual open-gap domain from the logarithmic
differential of `exp(2i theta)`. It equals the derivative of every local
analytic theta representative. `SourceAngularThetaPoisson.lean` defines
the actual angle brackets without selecting a branch, identifies them
with chart brackets, and reduces their prescribed values to identities
for the single-valued phases.

`SourceRealTypeFiniteApproximation.lean` proves that symmetric Fourier
truncations preserve real type and converge in every finite source
exponent. They eventually remain in any prescribed open neighborhood,
including a domain with one or several gap loci removed. Continuous
identities extend from finite real potentials. This gives the generic
bracket transfer and the actual angle-angle zero transfer, with the
finite identity retained as an explicit hypothesis.

The finite/Hilbert spectral computations of `{I_n,I_m}`, `{theta_n,theta_m}`,
and `{theta_n,I_m}` remain to be proved. Corollary 13.2 is not yet complete;
brackets at `1 < p < 2` also require spectral differential compatibility.

### Corollary 13.2: actual action brackets and spectral contour reduction

`SourceComplexActionAnalytic.lean` proves full Banach analyticity of the
glued indexed actions near the whole real source locus. A single open
almost-real neighborhood works for every index, intersected with that
index's original action chart domain. Joint analyticity of the weighted
integrand passes through the fixed-circle integral as a Banach power
series, and the chart formula identifies it with the actual action.

`SourceDiscriminantCotangent.lean` constructs the entire operator-valued
source differential of the discriminant. It is jointly analytic in
spectral parameter and source. Its quotient by the canonical root is
analytic off the periodic cuts and circle integrable as a cotangent.
`SourceActionPoissonGradient.lean` identifies the full derivative of
each actual action at a real source with the negative normalized
cotangent circle integral. `BilinearCircleIntegral.lean` transports
continuous bilinear pairings through both contours.

The resulting action-action bracket is the double spectral contour
integral of the discriminant bracket, weighted by the two inverse
canonical roots and `pi^-2`. Discriminant commutation on the two
isolating circles therefore implies commutation of the corresponding
actual actions. This is a proved reduction; the discriminant commutation
identity is still an explicit hypothesis awaiting its spectral proof.

`SourceActionPoisson.lean` supplies the actual angle-action bracket
and its single-contour formula: it is the negative normalized integral
of the angle-discriminant bracket divided by the canonical root.
Action-action brackets are analytic on the joint indexed action domain,
and angle-action brackets are analytic on the actual open-gap domain
intersected with the selected action domain. Their canonical values
extend from finite real potentials by the symmetric Fourier density
argument. Those finite canonical values remain explicit hypotheses.

Corollary 13.2's spectral computations remain unfinished. The contour
formulas now identify the discriminant commutation and mixed spectral
brackets needed for the next proof steps.

### Corollary 13.2: actual classical discriminant potential gradient

`ComplexVolterraVariation.lean` differentiates the globally invertible
Volterra equation in an arbitrary continuous operator coefficient.
The whole-curve derivative is the zero-initial forced solution, with
forcing given by the coefficient perturbation applied to the original
solution. No coefficient smallness is required.

`ClassicalPotentialVariation.lean` specializes this to the original
signed Zakharov--Shabat equation and identifies the actual potential
derivative at every point with a constructed C1 physical variation.
`ClassicalForcedKernel.lean` proves the variation-of-constants kernel
using the actual fundamental columns and their determinant-one identity.

`ClassicalDiscriminantGradient.lean` derives the actual monodromy-trace
derivative as an unconjugated physical integral against an explicit
continuous two-component gradient. Its values at zero and one are both
`(i T_10, -i T_01)`, where `T` is the actual monodromy. The derivative
formula and endpoint identity are proved from the ODE construction.
They provide the gradient and boundary data for the pending spectral
commutation proof; the coefficient-space canonical bracket identities
of Corollary 13.2 remain unfinished.


### Corollary 13.2: discriminant commutation and actual action involution

`ClassicalDiscriminantCommutation.lean` proves the first-order system
for the actual gradient and transported monodromy diagonal difference.
Their quadratic pairing has derivative `2i(z-w)` times the antisymmetric
physical gradient pairing. Matching endpoint values give a zero integral,
including coincident spectral parameters by antisymmetry. The actual
discriminant derivative vanishes along the Hamiltonian direction of every
other discriminant, with the original physical sign.

`IntervalBilinearParseval.lean` proves the unconjugated unit-interval
Fourier pairing with the required frequency reversal.
`FiniteSourceDiscriminantGradient.lean` differentiates the exact
finite-source/classical discriminant identity and recovers both actual
source cotangent coefficient sequences from the physical gradient.

`SourceDiscriminantPoisson.lean` identifies the actual finite Hilbert
source bracket with the zero physical pairing, transfers it by exponent
restriction, and uses finite Fourier density and analytic continuity to
prove discriminant commutation for every complex source at every finite
`p >= 2`. The previous contour reduction then gives `{I_n,I_m} = 0` for
the actual glued indexed actions at all real sources in that range,
including collapsed gaps. These results have no remaining commutation
or finite-identity hypothesis.

The angle-angle and mixed angle-action canonical identities, and the
spectral bracket compatibility required for `1 < p < 2`, remain to be
proved before Corollary 13.2 is complete.


### Corollary 13.2: actual monodromy and boundary characteristic Poisson flow

`ClassicalDiscriminantMonodromyFlow.lean` constructs the actual monodromy
variation along a discriminant Hamiltonian from the traceless transported
monodromy. The constructed numerator solves the original forced equation;
initial-value uniqueness identifies it with the genuine potential variation.
The endpoint identity gives
`2(z-w) dT_z[X_Delta(w)] = T_z T_w - T_w T_z`, including coincident parameters.

`ClassicalDiscriminantBoundaryFlow.lean` takes the original signed entry
combinations to prove the Dirichlet and Neumann characteristic variations
and the classical anti-discriminant variation. The characteristic formula
is `2(z-w) dchi_b(z)[X_Delta(w)] =
r (chi_b(z) delta(w) - delta(z) chi_b(w))`, with `r = 1` for Dirichlet and
`r = -1` for Neumann. Both signs and the original sine normalization are
retained. The zero-characteristic specialization supplies the boundary-root
spectral formula with the denominator cleared.

`ClassicalSeparatedGradient.lean` proves the physical potential gradient
integral for actual endpoint functionals and both separated characteristics.
`SourceBoundaryPoissonGradient.lean` differentiates their exact finite source
identities and recovers both source cotangent sequences with the necessary
Fourier frequency reversal. `SourceBoundaryDiscriminantPoisson.lean` uses
bilinear Parseval to identify the actual finite source bracket with the
physical characteristic variation. Exponent restriction and density extend
the formula to every complex source for finite `p >= 2`. It applies at every
actual canonical Dirichlet or Neumann root, holding that base-source spectral
parameter fixed under differentiation.

These are proved flow identities without supplied gradient or finite-identity
hypotheses. The moving boundary-root differential and the canonical
angle-angle and mixed angle-action calculations remain, along with spectral
bracket compatibility for `1 < p < 2`.


### Corollary 13.2: moving boundary-root differentials and action kernels

`SourceBoundaryRootDifferential.lean` differentiates the actual canonical
Dirichlet and Neumann characteristic zero equations. Their proved original
multiplicity one makes the spectral characteristic derivative nonzero at
every real-type source, including collapsed gaps and central indices.
The actual full coordinate cotangent is
`dmu_n = -dchi_b(mu_n) / chi_b'(mu_n)` for every finite `p > 1`.

`SourceBoundaryRootPoisson.lean` applies the actual continuous source
bivector to this equality. For finite `p >= 2`, the proved characteristic
flow yields the literal quotient
`{mu_n, Delta(w)} = r delta(mu_n) chi_b(w) /
(2 (mu_n-w) chi_b'(mu_n))`, where `r = 1` for Dirichlet and `r = -1` for
Neumann. Joint discriminant cotangent analyticity makes this bracket entire
in its fixed spectral parameter. Differentiating the cleared identity gives
its coincident value `-r delta(mu_n)/2` without a singular division.

`SourceBoundaryRootActionPoisson.lean` combines the actual root motion with
the action cotangent contour formula. Every boundary-root/action bracket
has a single-circle representation with the literal characteristic quotient
and canonical periodic root. Real interlacing ensures every boundary root
is avoided by an admissible action circle. Actual centered action charts
supply the formula for every real source and pair of indices.

The anti-discriminant square identity holds at both root families. At a
collapsed periodic gap the boundary root is its periodic endpoint and the
anti-discriminant vanishes. The actual root then commutes with every fixed
spectral discriminant and every indexed action. No root-gradient, finite-source
bracket, or nonzero-gap hypothesis is assumed in these conclusions.

Mutual boundary-root commutation and the canonical angle-angle and mixed
angle-action calculations remain, along with spectral bracket compatibility
for `1 < p < 2`.


### Corollary 13.2: separated-family and canonical boundary-root commutation

`ClassicalSeparatedCommutation.lean` factors the actual separated potential
gradient into forward and dual homogeneous solutions. Determinant one gives
the dual solution a fixed endpoint, with the original sign and normalization.
The forward cross-Wronskian vanishes initially and the dual cross-Wronskian
finally. Their product differentiates to `2i(w-z)` times the antisymmetric
physical gradient pairing. The fundamental theorem of calculus proves that
the pairing integral is zero; antisymmetry includes coincident parameters.

`SourceSeparatedPoisson.lean` identifies the finite Hilbert source bracket
with this physical cancellation using the actual characteristic cotangents
and bilinear Parseval. Exponent restriction and finite Fourier density extend
it to every complex source for finite `p >= 2`: each Dirichlet characteristic
family commutes with itself, as does the Neumann family.

The actual moving canonical root cotangent formula then proves mutual
commutation within the Dirichlet root coordinates and within the Neumann
root coordinates at every real-type source in that exponent range. Central
indices and collapsed periodic gaps are included. No finite identity,
physical cancellation, or root-gradient hypothesis remains in these results.
Cross-family commutation is not asserted.

The remaining anti-discriminant spectral brackets, canonical angle-angle
and mixed angle-action computations, and spectral compatibility for
`1 < p < 2` remain before Corollary 13.2 is complete.


### Corollary 13.2: anti-discriminant/discriminant flow and action kernels

`ClassicalAntiDiscriminantGradient.lean` obtains the actual potential-gradient
integral by adding the original two off-diagonal solution endpoint gradients.
`SourceAntiDiscriminantPoissonGradient.lean` differentiates the exact finite
realization identity and recovers both actual source cotangent coefficient
sequences with the required frequency reversal. Its full operator-valued
cotangent is jointly analytic for every finite `p > 1`.

`SourceAntiDiscriminantPoisson.lean` uses bilinear Parseval and the proved
physical Hamiltonian variation to obtain
`(z-w){delta(z),Delta(w)} = chi_D(z)chi_N(w)-chi_N(z)chi_D(w)`.
Exponent restriction and density make this an actual identity for every
complex source at finite `p >= 2`. Entire dependence on the second spectral
parameter determines the coincident value
`chi_N(z)chi_D'(z)-chi_D(z)chi_N'(z)` without a singular division.

`SourceAntiDiscriminantActionPoisson.lean` passes the actual action cotangent
circle integral through the source bivector. The resulting single-circle
kernel is the original characteristic determinant quotient divided by the
canonical periodic root. At actual canonical boundary roots, interlacing
ensures the circle avoids the fixed spectral parameter. The literal
Dirichlet and Neumann kernels retain their opposite prefactor signs, and
include collapsed gaps. The base-source root stays fixed in the differentiated
anti-discriminant functional.

The characteristic/anti-discriminant and anti-discriminant self brackets,
moving terminal combinations, canonical angle-angle and mixed angle-action
computations, and spectral compatibility for `1 < p < 2` remain.


### Corollary 13.2: moving terminal data and actual local Floquet logarithms

`MovingSpectralParameter.lean` proves the full cotangent chain rule for an
actual spectral family evaluated at a moving source coordinate.
`SourceBoundaryTerminalDifferential.lean` applies it to the actual
discriminant and anti-discriminant at every canonical boundary root.
Their cotangents include the spectral derivative times the root cotangent.
These results hold at every real source for each finite `p > 1`.

The signed multiplier `rho_b=(Delta(mu_b)+r_b delta(mu_b))/2` uses `r_D=1`
and `r_N=-1`. Its algebraic reciprocal and original characteristic polynomial
are proved at every complex source. In particular, it never vanishes,
including at collapsed gaps. `SourceBoundaryTerminalPoisson.lean`
differentiates the actual unimodular identity to cancel the extra
characteristic in the moving anti-discriminant bracket. The resulting
actual normalized multiplier bracket at finite `p >= 2` is
`{rho_b,Delta(w)}/rho_b = Delta'(mu_b)chi_b(w)/(2(mu_b-w)chi_b'(mu_b))`.
Entire spectral dependence gives the coincidence value `-Delta'(mu_b)/2`.

`SourceBoundaryFloquetLogActionPoisson.lean` constructs the actual local
function `log(rho_b(psi)/rho_b(phi))`, analytic and zero at the base source
`phi`. Its full differential is the multiplier cotangent divided by its
value. Thus the normalized kernel is the bracket of an actual local
logarithm. Passing the actual action cotangent through the source bivector
gives its single action contour kernel; interlacing supplies avoidance
automatically, without an open-gap or logarithm-branch hypothesis.

The characteristic/anti-discriminant and anti-discriminant self brackets,
canonical angle-angle and mixed angle-action identities, and compatibility
for `1 < p < 2` remain before Corollary 13.2 is complete.


### Corollary 13.2: anti spectral brackets and mixed root/Floquet separation

`ClassicalEndpointPoisson.lean` generalizes the physical cross-Wronskian
argument to every pair of continuous linear endpoint functionals. The
actual dual endpoint follows from determinant one. The two endpoint
values of the forward/dual Wronskian product determine the physical
bracket, including coincident parameters with the difference cleared.
`ClassicalAntiSpectralPoisson.lean` adds the original off-diagonal endpoint
gradients to obtain the actual characteristic/anti-discriminant flow and
anti-discriminant cancellation, with their original normalization.

`SourceAntiSpectralPoisson.lean` uses the actual cotangent coefficient
identities and bilinear Parseval to prove these brackets on finite Hilbert
sources. Exponent restriction and density extend them to every complex
source at finite `p >= 2`:
`2(z-w){chi_b(z),delta(w)} = r_b(chi_b(z)Delta(w)-Delta(z)chi_b(w))` and
`{delta(z),delta(w)}=0`. Entire dependence on the second parameter gives
the literal coincident characteristic/discriminant Wronskian.

`SourceBoundaryRootFloquetPoisson.lean` obtains the actual moving
root/anti-discriminant kernel, with coincident value `-r_b Delta(mu_b)/2`.
Root involution eliminates the second root's motion in a mixed
root/multiplier bracket. Real simplicity and distinctness of the indexed
roots give the actual separation relation
`{mu_n,log(rho_m/rho_m(base))} = -delta_nm/2`, with the sign and factor
fixed by the original period-one source bracket. This holds separately
in both ordinary boundary families at every real source, including
central indices and collapsed periodic gaps.

Mutual Floquet-logarithm commutation, the canonical angle-angle and mixed
angle-action identities, and compatibility for `1 < p < 2` remain.
Corollary 13.2 is not yet complete.


### Corollary 13.2: actual Floquet involution and canonical separation brackets

`SourceBoundaryFloquetCommutation.lean` proves that each signed
fixed-parameter discriminant/anti-discriminant family commutes at every
complex source for finite `p >= 2`. The spectral symmetry of the actual
anti-discriminant/discriminant bracket cancels both cross terms. The
actual moving multiplier cotangent retains the spectral derivative times
the root cotangent. At distinct real roots, the mixed separation relations
make both moving-root contributions zero. Consequently all actual moving
multipliers and their analytic local logarithms mutually commute within
either ordinary boundary family, including collapsed gaps.

`SourceBoundaryCanonicalSeparation.lean` defines the actual local momentum
`kappa_n=-2 log(rho_n/rho_n(base))`. This normalization converts the original
period-one mixed bracket `-delta_nm/2` into `delta_nm`. Its actual cotangent
and local analyticity follow from those of the actual local logarithm.
For every real source at finite `p >= 2`, all three canonical separation
relations hold simultaneously:
`{mu_n,mu_m}=0`, `{kappa_n,kappa_m}=0`, and `{mu_n,kappa_m}=delta_nm`.
The statements are independent for the Dirichlet and Neumann families,
with no open-gap or logarithm-branch assumption. Momentum analyticity
also holds at each finite `p > 1`.

The canonical angle-angle and mixed angle-action identities require
connecting these separation functionals to the actual normalized angular
integrals. That connection and compatibility for `1 < p < 2` remain before
Corollary 13.2 is complete.


### Corollary 13.2: actual spectral-curve cotangents and isospectral actions

`SourceBoundarySpectralCurveDifferential.lean` differentiates the original
monodromy characteristic polynomial. It proves the full actual cotangent
equation `r_b delta(mu) d log(rho) = d_source Delta(mu) + Delta'(mu) d mu`
at every real source for finite `p > 1`. The local logarithm is the actual
normalized Floquet logarithm, and the right side retains both fixed-source
variation and root motion. The equation uses no division by `delta(mu)`.
At a branch terminal, the full moving discriminant cotangent is zero.
The canonical momentum has the same equation with normalization `-2`.

`SourceBoundaryIsospectralAction.lean` proves that every actual indexed
action commutes with every fixed-parameter discriminant for finite
`p >= 2`. Its proof passes the actual contour cotangent through the source
bivector and uses the proved discriminant commutation. Every actual action
therefore satisfies the tangent equation
`r_b delta(mu){kappa_n,I_m} + 2 Delta'(mu){mu_n,I_m} = 0`
on the separation spectral curve. The cleared equation includes branch
terminals and collapsed gaps; its quotient form is proved whenever the
terminal anti-discriminant is nonzero. Both boundary families are covered.

These actual differential and bracket equations prepare the connection
to the normalized angular integrals. The angle-angle and angle-action
canonical values, and compatibility for `1 < p < 2`, remain unfinished.


### Corollary 13.2: actual Hamiltonian directions and normalized psi stationarity

`SourceHamiltonianDirection.lean` represents the actual source bivector
by a bounded linear Hamiltonian direction in the actual source space.
Frequency reflection and the original cross-component sign give a
Hilbert direction, and exponent inclusion places it in each source space
with `p >= 2`. Every source cotangent evaluates on this direction to its
actual bivector pairing. This representation commutes with exponent
restriction.

`SourceIsospectralDirection.lean` proves that every actual action direction
fixes the discriminant and its canonical square root off the spectral
cuts. `SourcePsiIsospectralContour.lean` differentiates the actual psi
contour equations with their numerator-root input fixed. The canonical
root denominator has zero variation in an isospectral direction, so both
the scalar equations and their full selected Banach-valued realization
have zero source variation.

`SourcePsiIsospectralRoots.lean` differentiates an actual canonical local
psi branch in its fixed contour equation. The proved bijective root
derivative forces the entire root-vector variation to vanish. Real-form
uniqueness identifies this derivative with every actual common-domain
analytic psi extension. The result holds in every isospectral direction
for finite `p > 1`. In particular, every actual normalized psi root vector
is stationary under every actual action Hamiltonian for finite `p >= 2`.
Every actual entire normalized psi numerator therefore commutes with every
action at every spectral parameter, including collapsed periodic gaps.

The moving angular integration terminals and normalized period computation
remain before the angle-action canonical value is proved. The angle-angle
identity and lower-exponent bracket compatibility also remain unfinished.

`SourcePeriodicIsospectral.lean` proves that the actual periodic midpoint
and squared gap are stationary in every isospectral direction for finite
`p > 1`. It differentiates the actual discriminant factorization with the
analytic nonzero omitted product. At a double root, spectral differentiation
of the linearized identity supplies the midpoint equation. This includes
every central index and collapsed gap, with no gap division or assumed
endpoint derivative. Both symmetric coordinates commute with every actual
action for finite `p >= 2`.

`SourceStandardRootIsospectral.lean` composes the actual stationary symmetric
coordinates with the normalized principal-root formula. Each actual standard
root is stationary off its selected segment. `SourceOmittedRootIsospectral.lean`
proves stationarity first for the literal finite products, then passes to the
actual infinite product using locally uniform convergence of full Fréchet
derivatives. The omitted product is stationary on its entire domain, including
the selected gap and either endpoint.

`SourceAngularIntegrandIsospectral.lean` combines these results with the
proved actual normalized psi stationarity. The actual canonical angular
integrand is stationary off the periodic cuts. Its actual regular gap
numerator is stationary on the full omitted-root domain, including selected
endpoints. Both therefore commute with every actual action in the bracket
range. Moving-terminal variation and the exact normalized period sum remain
before the angle-action value; the angle-angle identity and lower-exponent
bracket compatibility also remain unfinished.

`QuadraticCauchyUniqueness.lean` proves that an analytic solution of the
homogeneous quadratic root equation vanishes on an open connected domain
containing a root, including a double root. `SourceAngularCauchyIsospectral.lean`
uses this to prove zero source variation of the actual off-diagonal interior
angular Cauchy primitive throughout its enclosing disc. Differentiating its
actual equation leaves only the homogeneous equation, since the actual
midpoint, squared gap, and normalized gap numerator are already stationary.
Joint analyticity justifies commuting the source and spectral derivatives.
The result includes periodic endpoints and collapsed gaps for finite `p > 1`;
the candidate commutes with every actual action for finite `p >= 2`.
Moving-terminal variation, the normalized period sum, the angle-angle identity,
and lower-exponent bracket compatibility remain unfinished.

`SourceAngularBetaIsospectral.lean` now derives the actual off-diagonal
moving-terminal identity `delta(mu_m) d beta_nm = psi_n(mu_m) d mu_m` in
every isospectral direction for finite `p > 1`. The proof differentiates
the actual moving sheet identity and the actual Cauchy terminal formula.
`QuadraticSheetTerminalVariation.lean` supplies the algebraic cancellation:
the full omitted-product derivative cancels, and the stationary midpoint,
squared gap, and interior primitive leave the normalized numerator times
the actual root variation. The cleared equation includes periodic terminals
and collapsed gaps. Every actual action satisfies its bracket version for
finite `p >= 2`; at a regular terminal, the beta/action bracket equals
`psi_n(mu_m)/delta(mu_m)` times the root/action bracket. The diagonal eta
variation, normalized period sum, angle-angle identity, and lower-exponent
bracket compatibility remain unfinished.

`QuadraticCauchyStationarity.lean` now supplies the common differentiated
quadratic-equation argument for both beta and eta. The existing beta Cauchy
stationarity API is preserved. `SourceAngularEtaCauchyIsospectral.lean` proves
that the actual diagonal interior remainder is stationary, including endpoints
and collapsed gaps. `SourceAngularEtaRemainderIsospectral.lean` computes its
actual moving-terminal variation, retaining the diagonal model term.

`SourceAngularEtaDifferential.lean` defines the analytic cotangent of the single
actual eta phase and identifies it with every local eta representative's
derivative. It also proves that the actual theta cotangent is the eta cotangent
plus the derivative of the full beta correction. `SourceAngularEtaIsospectral.lean`
differentiates the actual half-gap and cosine-point equations and combines the
model-angle and remainder variations. Their model terms cancel to give
`delta(mu_n) d eta_n = psi_n(mu_n) d mu_n` in every isospectral direction for
finite `p > 1` on the actual open-gap charts, including periodic terminals.
The actual eta/action bracket has this cleared equation and its regular-terminal
weight formula for finite `p >= 2`. The theta/action bracket reduces to this
diagonal contribution plus the full beta-correction derivative. The exact
normalized period sum, angle-angle identity, and lower-exponent bracket
compatibility remain unfinished.


### Corollary 13.2: derivatives and brackets of the full beta series

`SourceAngularBetaSeriesDifferential.lean` now justifies differentiation of
the actual infinite beta correction. The actual common-domain analyticity
and local uniform convergence imply locally uniform convergence of the full
Fréchet derivatives in operator norm on smaller source balls. The finite
symmetric sums of actual beta cotangents therefore converge to the cotangent
of the actual correction for every finite `p > 1`. Evaluation gives the
corresponding directional limits, also for `1 < p < 2`, and the actual
Hamiltonian bracket limits for finite `p >= 2`.

Adding the single eta cotangent gives the actual theta cotangent and its
functional bracket as limits of eta plus the finite beta sums. Continuous
bilinearity also gives the actual angle-angle bracket as the limit with both
cotangents approximated by the same symmetric cutoff. The API checks include
these full source limits and a directional limit below the Hilbert exponent.
The results concern symmetric cutoffs, without an assertion of absolute
cotangent-norm summability. The exact normalized spectral period sum and the
canonical angle-action and angle-angle values still remain, as does bracket
compatibility for `1 < p < 2`.


### Corollary 13.2: actual beta/action kernels through branch terminals

`SourceDirichletActionKernel.lean` expresses the actual root/action and full
moving terminal anti-discriminant/action velocities using one actual contour
kernel. Its only terminal denominator is the simple Dirichlet characteristic
derivative. The latter velocity retains both the fixed-source variation and
the spectral derivative times the moving-root variation. Differentiating the
original spectral identity gives its coefficient `Delta(mu_m) Delta'(mu_m)`,
including at periodic and collapsed terminals.

`SourceAngularBetaActionKernel.lean` uses this full flow, stationarity of the
interior Cauchy primitive and omitted product, and the differentiated actual
terminal quotient to prove `{beta_nm,I_k} = psi_n(mu_m) K_mk` for finite
`p >= 2`. The formula requires no nonzero terminal square root or open selected
gap. Actual local annuli are constructed from the existing normalized psi
extension, so the public theorem also requires no supplied angular chart.
The full beta correction/action bracket is the limit of the symmetric
normalized kernel cutoffs. The theta/action bracket is the limit of its
actual eta contribution plus those cutoffs. The diagonal eta kernel and exact
normalized period sum still remain before the canonical angle-action value;
the angle-angle identity and lower-exponent bracket compatibility also remain.


### Corollary 13.2: the diagonal eta kernel and full theta/action sum

`SourceAngularTerminalActionFlow.lean` now supplies the shared actual
moving-root, terminal anti-discriminant, and omitted-product flow equations
for both beta and eta. Their earlier public formulas are preserved.
`QuadraticSheetTerminalVariation.lean` adds the cosine-angle calculation
using both differentiated terminal equations. The sine and cosine
constraints together determine the angle velocity even at periodic endpoints.

`SourceAngularEtaActionKernel.lean` derives the actual model-angle and
remainder action kernels. Their model terms cancel exactly, giving the
single eta cotangent the normalized kernel `psi_n(mu_n) K_nk` for finite
`p >= 2`. The selected eta chart has an open gap, but its Dirichlet
terminal can be either periodic endpoint. The remainder formula itself
also includes collapsed selected gaps.

The actual theta/action bracket is therefore the limit of one full
symmetric normalized kernel sum, with its diagonal included. The actual
common-domain data construct the needed eta chart at every real source
with an open selected gap; no extra angular chart is supplied to the
public theorem. API examples check the endpoint model flow, the actual
eta and remainder kernels, the full sum without a chart hypothesis, and
half-gap stationarity below the Hilbert exponent. Evaluating the normalized
spectral period sum, the canonical angle-action and angle-angle values,
and bracket compatibility for `1 < p < 2` remain unfinished.


### Corollary 13.2: actual uniform Dirichlet interpolation

`SimplePoleQuotient.lean` derives the principal coefficient
`f(mu) / g'(mu)` at a simple denominator zero. Subtracting the finite
principal parts gives an analytic filled remainder.
`SimplePoleCauchyInterpolation.lean` applies Cauchy's formula to identify
the exact finite interpolation error with an outer-circle integral.

`SourceDirichletRootCircleSelection.lean` proves that sufficiently large
half-integer circles enclose exactly the symmetric cutoff of the actual
Dirichlet roots, including at complex sources.
`SourcePsiDirichletInterpolationExterior.lean` derives inverse-radius
decay of the actual psi/Dirichlet quotient from the existing full-product
bounds. Its outer Cauchy integrals vanish uniformly on bounded evaluation sets.

`SourcePsiDirichletInterpolation.lean` now proves the actual interpolation
identity as a uniform limit of symmetric cutoffs:
`sum_m psi_n(mu_m) / chi_D'(mu_m) / (w - mu_m) -> psi_n(w) / chi_D(w)`.
It holds at every real source for finite `p > 1`, on bounded sets where
`chi_D(w)` is nonzero, with no open-gap or extra convergence premise.
Multiplying by the characteristic and reversing the spectral difference
gives the exact `-psi_n(w)` limit required by the action kernels.
API examples include this weighted limit below the Hilbert exponent.
Contour-limit transport and the normalized period value still remain
before the canonical angle-action identity; the angle-angle identity
and lower-exponent bracket compatibility also remain unfinished.


### Corollary 13.2: actual canonical angle-action brackets

`SourceAngularActionKernelPeriod.lean` passes the uniform actual
Dirichlet interpolation limit through every action chart's contour.
Multiplication by its bounded characteristic/root factor preserves
uniform convergence on the circle. The literal kernel constants and
reversed spectral differences give the normalized actual psi period
as the limit of the full symmetric terminal kernel sums. This spectral
transport holds for every finite `p > 1`, including branch terminals.

The original action-chart construction now exposes its real spectral
center, while preserving the previous local agreement APIs.
`SourceRealActionRealCenteredChart.lean` constructs such an actual chart
at every real source. Actual contour comparison transfers the proved
psi-period normalization to the chart's circle.

`SourceAngularThetaActionCanonical.lean` combines the two proved limits
to establish `{theta_n,I_k} = delta_nk` for finite `p >= 2`, at every
real source with an open selected angle gap. The public theorem supplies
its own action and angular charts. The terminal may be a periodic
endpoint, and the action gap may be collapsed. API checks cover the
matching-index value at `p = 2`, the distinct-index value, a periodic
terminal whose root/action bracket is zero but whose angle/action bracket
is one, and the contour limit at `p = 3/2`.

The angle-angle identity and bracket compatibility for `1 < p < 2`
remain unfinished. Corollary 13.2 and the later chapters are not complete.


### Corollary 13.2: Jacobi and actual angle-bracket action stationarity

`SourceBracketJacobi.lean` now proves Jacobi for the literal source
bracket of analytic functionals at exponents `p >= 2`. Differentiating
the constant bivector produces Hessian terms; their symmetry cancels
the full cyclic sum using the actual Hamiltonian directions.

`SourceAngularThetaLocalExactness.lean` constructs a local analytic
primitive of the single actual theta cotangent and proves that its
derivative is symmetric for every finite `p > 1`.
`SourceAngularThetaActionLocalCanonical.lean` extends the real
Kronecker identity to a complex germ near each real open-gap source,
so the canonical mixed bracket has zero cotangent there.

`SourceAngularThetaThetaActionStationarity.lean` combines these
results to prove that the actual theta/theta bracket is stationary
along every actual action Hamiltonian direction, for finite `p >= 2`
with both selected angle gaps open. It commutes with every actual
action, including those with collapsed gaps. API checks include
the complex germ, Jacobi, action stationarity at `p = 2` and `p = 3`,
and cotangent closedness at `p = 3/2`.

The theta/theta bracket's canonical zero value still requires its
spectral calculation. Bracket compatibility for `1 < p < 2` also
remains unfinished; Corollary 13.2 is not complete.


### Corollary 13.2: the exact actual beta/discriminant bracket

`SourceDirichletDiscriminantKernel.lean` uses a divided difference to
fill the apparent pole in the actual root-motion kernel. It is entire
and has value `-1/2` at its own real Dirichlet root. The actual moving
root and full terminal anti-discriminant share this kernel, including
coincident parameters and periodic terminals. Actual discriminant
Hamiltonian directions are isospectral at every complex source.

`SourceAngularTerminalIsospectralFlow.lean` supplies the general
terminal sheet equations in any isospectral direction with the stated
actual root and anti-discriminant velocities.
`SourceAngularBetaDiscriminantKernel.lean` applies them to every
off-diagonal beta, without dividing by the terminal square root.
The public actual beta/discriminant formula constructs its angular
chart and includes collapsed gaps at every real source for finite
`p >= 2`. The full correction is the limit of these actual kernels.

`SourcePsiDirichletDiscriminantInterpolation.lean` evaluates the full
symmetric filled kernel sum as `-psi_n(w)/2`, for every parameter and
every finite `p > 1`. At a Dirichlet zero, only its own kernel survives.
`SourceAngularBetaDiscriminantValue.lean` subtracts the omitted
diagonal to prove the exact full beta-correction/discriminant bracket
for finite `p >= 2`. At its own base-source Dirichlet root, that
bracket is zero. API checks cover coincidence, branch terminals,
the full correction formula, and filled interpolation at `p = 3/2`.

The diagonal eta contribution remains before the full theta/discriminant
identity. The theta/theta zero value and bracket compatibility for
`1 < p < 2` also remain unfinished.


### Corollary 13.2: the exact actual theta/discriminant identity

`SourceAngularEtaIsospectralKernel.lean` proves the diagonal eta kernel
in any actual isospectral sheet flow with the stated root and full moving
terminal velocities, for every finite `p > 1`. The two differentiated
terminal equations determine the model-angle velocity even at periodic
terminals. Its omitted-product term cancels the actual Cauchy remainder,
leaving the normalized psi numerator times the sheet-flow coefficient.

`SourceAngularEtaDiscriminantKernel.lean` supplies the actual discriminant
Hamiltonian direction and its proved terminal velocities. The actual
common-domain angle data construct the charts needed for the diagonal
kernel. No terminal square root or spectral difference is divided out.
`SourceAngularThetaDiscriminant.lean` adds the proved full beta correction
and cancels the omitted diagonal. Thus `{Delta(w),theta_n} = psi_n(w)/2`
for every spectral parameter at every real source for finite `p >= 2`.
Only the selected angle gap must be open; its terminal may be periodic.
The actual single-valued angle phase has velocity `-i phase_n psi_n(w)`
under the discriminant Hamiltonian flow.

`SourceAngularThetaDiscriminantLocal.lean` uses actual joint numerator
analyticity and the real-form identity principle to extend the bracket
identity to a complex neighborhood of every real open-gap source.
Differentiating that germ gives minus half the actual normalized
numerator's source cotangent, with the spectral parameter held fixed.

API checks cover both bracket orientations, the coincident periodic
terminal, the actual phase flow, the complex germ and its differential,
and the general eta kernel without a `p >= 2` premise. The theta/theta
zero value and bracket compatibility for `1 < p < 2` remain unfinished.
Corollary 13.2 and the later chapters are not complete.


### Corollary 13.2: actual theta/theta discriminant stationarity

`SourceAngularThetaThetaDiscriminantVariation.lean` applies Jacobi to
the actual local angle primitives and the proved theta/discriminant
germ. It expresses the entire spectral variation of the theta/theta
bracket as a difference of actual normalized psi source variations.
`SourcePsiSourceVariation.lean` identifies each source derivative with
the entire deleted-root variation by the chain rule. Pairing any
actual scalar cotangent with the action contour gives zero weighted
periods for the spectral variation.

`SourceRealCotangent.lean` proves that real cotangents give real
Hamiltonian directions and real brackets with the actual Fourier
signs. Constructed real angle representatives supply that property
for the theta cotangents and for the theta/theta bracket's derivative.
`SourceAngularThetaThetaDiscriminantGapZeros.lean` constructs a zero in
every periodic gap: real mean value handles open gaps, and Cauchy's
formula handles collapsed gaps. The full zero sequence has its
spectral displacement in the actual source exponent `ell^p`.

`SourcePsiVariationCombinationInterpolation.lean` proves uniform
quotient decay for differences of deleted-root variations with different
omitted indices. The full comparison product has simple zeros by actual
gap separation. Filling the quotient at those zeros and applying the
maximum-modulus argument forces the variation to vanish.

`SourceAngularThetaThetaDiscriminantStationarity.lean` consequently
proves that the actual theta/theta bracket commutes with every actual
discriminant at every real source for finite `p >= 2`, with both selected
angle gaps open. It includes every spectral parameter and permits all
other gaps to collapse. The final theorem assumes neither a gap-zero
sequence nor a growth estimate. The actual Hamiltonian direction of
the theta/theta bracket is isospectral.

API checks cover both bracket orientations at `p = 2` and `p = 3`,
the actual isospectral direction, the full gap-zero sequence, and
source-variation and real-cotangent APIs without a `p >= 2` premise.
The theta/theta bracket's zero value still needs a basepoint calculation
and isospectral transport; bracket compatibility for `1 < p < 2` also
remains unfinished. Corollary 13.2 and the later chapters are not complete.


### Corollary 13.2: actual theta/theta zero at periodic-terminal basepoints

`SourceBoundaryEndpointCotangents.lean` differentiates the actual
moving spectral-curve identity at a zero of the terminal
anti-discriminant. The full moving terminal discriminant cotangent is
zero there, and the anti-discriminant cotangent is twice the signed
moving Floquet cotangent. The proved Floquet involution consequently
gives terminal anti-discriminant involution within either boundary
family, including collapsed gaps. This reduction holds for every
finite `p > 1`; the actual source brackets use `p >= 2`.

`SourceAngularEndpointCauchyCotangent.lean` differentiates the actual
beta and eta remainder product formulas. At a periodic terminal the
anti-discriminant factor is zero, so the full cotangent is a scalar
multiple of its derivative. Both source and spectral terminal arguments
move. `SourceAngularEtaEndpointCotangent.lean` differentiates the
constructed terminal sine equation, whose cosine is nonzero at the
endpoint, and adds the Cauchy remainder. The single actual eta cotangent
has the same terminal-span reduction. Neither reduction assumes an
isospectral direction or divides by the zero terminal value.

`SourceAngularThetaThetaEndpoint.lean` constructs the beta charts from
the actual normalized psi extension and the eta charts from the common
angle data. Every term of each finite symmetric angle cotangent sum
lies in a commuting terminal span. The already proved operator-norm
convergence of these sums then gives `{theta_n,theta_m} = 0` whenever
all actual Dirichlet terminals are periodic, for finite `p >= 2` with
both selected angle gaps open. The theorem permits either own endpoint
in every gap, and all other gaps may be collapsed. It requires no
supplied angular chart, finite-gap condition, or convergence estimate.

API checks cover the actual full zero value at `p = 2` and `p = 3`,
the all-left-endpoint condition, both boundary families' terminal
involution, and the full endpoint cotangent reduction at `p = 3/2`.
The general theta/theta zero identity still requires isospectral
transport from these basepoints; bracket compatibility for `1 < p < 2`
also remains unfinished. Corollary 13.2 and the later chapters are not
complete.


### Corollary 13.2: constructed local real isospectral angle transport

`SourceRealTypeProjection.lean` turns the previously proved real-part
operation into a bounded real linear projection onto the complete closed
real-type source subspace. It fixes the original source values on that
subspace.

`SourceDirichletSpectralVectorField.lean` evaluates the actual
fixed-parameter discriminant cotangent at the actual moving indexed
Dirichlet root, then applies the actual source Poisson operator.
The resulting field is isospectral at every complex source, analytic
near every real source, and real on the real source form. The filled
kernel proves that only its own Dirichlet terminal data move. Its root
velocity is `-anti(mu)/2` and its full terminal anti-discriminant velocity
is `-Delta(mu) Delta'(mu)/2`, including periodic terminals. The normalized
actual psi numerator never vanishes at its own Dirichlet terminal, so
the indexed field is nonzero when its selected angle gap is open.
Every actual angle cotangent has its proved normalized numerator
velocity, and the actual theta/theta bracket has zero derivative along
every indexed field.

`SourceDirichletSpectralLocalFlow.lean` applies Picard-Lindelof to the
actual continuously differentiable field on the real source Banach
space. It constructs a local flow for nearby initial sources, and an
actual real integral curve through every real source for finite
`p >= 2`. The embedded curve solves the actual coefficient-space ODE
and preserves every discriminant at every spectral parameter on its
open time interval.

`SourceAngularThetaThetaLocalTransport.lean` proves that the actual
theta/theta bracket is constant along real integral curves with the
two selected gaps open. Its public existence theorem constructs such
a curve through every real open-gap source whose original ODE interval
stays in the actual common angle domain. Both the full bracket and every
discriminant are preserved.

API checks cover the real-space projection, the actual field velocities,
nonvanishing on an open gap, constructed local curves at `p = 2`,
and constructed angle/angle transport at `p = 3`. Global continuation
and transport reaching periodic-terminal basepoints remain before the
general theta/theta zero identity. Bracket compatibility for `1 < p < 2`
also remains unfinished. Corollary 13.2 and the later chapters are not
complete.


### Corollary 13.2: conserved spectral data and compact terminal sheets

`SourceDirichletSpectralConservation.lean` proves conservation on the
whole time interval of every actual real indexed spectral integral
curve. All periodic midpoints, squared gaps, oriented real gaps and
periodic endpoints are fixed, including collapsed gaps. Every other
Dirichlet root and its full terminal anti-discriminant are fixed too.
The selected root and anti-discriminant solve their actual two-coordinate
ODE using the original fixed discriminant and its spectral derivative,
including at either periodic endpoint.

`SourceDirichletSpectralSheet.lean` defines the actual fixed-discriminant
sheet above the original periodic segment. Its compactness is proved
for every finite `p > 1`, including a collapsed segment, from the entire
discriminant and its bound on that compact segment. Along every actual
real indexed curve for finite `p >= 2`, the selected terminal remains
on this fixed sheet. Both terminal coordinates consequently have one
finite bound throughout the whole curve interval.

`SourceAngularThetaThetaLocalTransport.lean` now derives open-gap
preservation from these conservation laws. Its new interval transport
theorem requires both angle gaps to be open at just one reference time.
The constructed local angle-transport curve preserves its bracket on
the original ODE interval, without a further shrink into the angle
domain.

API checks cover conserved collapsed gaps, other fixed Dirichlet
terminals, the fixed initial sheet ODE, compact sheet confinement of a
constructed curve, and angle/angle transport with initial open gaps.
The compact terminal sheet bounds the scalar spectral data; it does not
yet establish continuation of the original source-space curve. Global
source continuation, endpoint reachability, and bracket compatibility
for `1 < p < 2` remain before completing Corollary 13.2. Later chapters
are also unfinished.


### Corollary 13.2: conservation of the original Hilbert source norm

`ClassicalDiscriminantPhaseStationarity.lean` proves infinitesimal
opposite-phase invariance of the actual physical discriminant. The
transported-monodromy diagonal has matching endpoint values, and its
proved derivative is twice the phase-gradient pairing. The fundamental
theorem of calculus gives exact cancellation for every continuous
complex potential and every spectral parameter.

`SourceHilbertMass.lean` defines the actual holomorphic Hilbert mass by
the reflected coefficient pairing. Both original components occur in
its full cotangent. Its actual Hamiltonian direction is `-sourcePhase`,
with first component `-i phi_1` and second component `i phi_2`. On the
real source form the mass is exactly half the square of the original
source-pair norm, including at zero.

`SourceHilbertMassDiscriminant.lean` transfers the physical phase
identity through exact finite Fourier realization, then uses joint
cotangent continuity and finite Fourier density. The actual Hilbert
mass commutes with every actual source discriminant at every complex
source; phase or norm invariance is not supplied as an assumption.

`SourceDirichletSpectralMassConservation.lean` proves that every actual
indexed Hilbert spectral direction fixes mass. The mass is constant
throughout every complex integral-curve interval, and the original
source norm is constant throughout every real integral-curve interval.
Its public existence theorem constructs a real local isospectral curve
through every real Hilbert source whose norm remains exactly the initial
norm on the whole ODE interval, without positive-norm or open-gap
hypotheses.

API checks cover the original mass pairing and phase signs, its actual
norm identity, complex mass/discriminant commutation, constructed
norm-conserved curves, and stationarity of a curve through zero.
This supplies the source norm bound needed for Hilbert continuation.
Uniform source vector-field estimates and a continuation construction
remain, followed by endpoint reachability and the remaining transport
argument. Bracket compatibility for `1 < p < 2` and later chapters also
remain unfinished; Corollary 13.2 is not complete.


## Latest milestone: uniform Hilbert spectral speeds and finite endpoint limits

`VariableGronwall.lean` proves a norm comparison using the integral of a
continuous variable coefficient. A positive strict comparison followed
by a zero-perturbation limit includes a vanishing initial vector and
requires no sign assumption on the coefficient.

`ClassicalSolutionEnergyBound.lean` defines the sum of the two component
square integrals on the unit interval. It bounds the actual fundamental
columns by the initial vector norm times `exp(norm z + 1 + energy)`,
and the actual monodromy trace by twice that exponential. The estimate
does not depend on the physical potential's supremum norm.

`SourceDiscriminantEnergyBound.lean` identifies finite physical energy
with the square of the original Hilbert source-pair norm by Parseval.
Exact physical realization and finite Fourier density prove the actual
discriminant bound at every complex Hilbert source. The Banach-space
Schwarz lemma bounds the full actual source cotangent by
`4 exp(norm z + 1 + (norm phi + 1)^2)`. It also supplies one bound on a
source norm ball and bounded spectral set, without real-type assumptions.

`SourceDirichletSpectralVectorBound.lean` bounds the actual Hilbert
Poisson direction by twice the cotangent norm. The actual indexed field
therefore satisfies `norm X_k <= 8 exp(R + 1 + (M + 1)^2)` whenever the
original source norm is at most `M` and the selected Dirichlet coordinate
has norm at most `R`. Along an actual real indexed curve, conserved
source norm and compact fixed-sheet confinement supply those bounds
throughout its entire interval. The original source curve is Lipschitz;
no uniform speed bound is required from the caller.

`SourceDirichletSpectralEndpointLimit.lean` uses that Lipschitz estimate
and completeness of the original Hilbert source space to construct its
limits at both finite endpoints. Both limits are real, retain the
original source norm, and preserve every discriminant value. The proof
does not identify them with arbitrary assigned endpoint values of the
original function, and includes zero sources and collapsed gaps.

API checks distinguish the two-component physical energy from the
maximum component norm, verify actual Fourier-source solution bounds,
cover complex source trace and full cotangent bounds, and construct
Lipschitz local curves without a supplied curve or speed bound. Both
finite endpoint limits are checked with their conserved data.
Joining new local ODE solutions at these limits and constructing global
source continuation remain, followed by endpoint reachability and the
general theta/theta transport argument. Bracket compatibility for
`1 < p < 2` and later chapters also remain unfinished; Corollary 13.2 is
not complete.


## Latest milestone: actual continuation through both finite endpoints

`IntegralCurveJoin.lean` constructs a joined autonomous integral curve
from two actual curves with a common finite endpoint limit. The value
at the joining time is that common limit, independently of the old
functions' assigned endpoint values. Continuity of the actual field at
the limit makes the two one-sided derivatives converge to the same
vector. Differentiability at the interval boundary then proves the ODE
at the joining time, as well as on both original open intervals.

`SourceDirichletSpectralContinuation.lean` constructs a real local
Hilbert spectral curve through an arbitrary real source at any real
time. Every real actual indexed curve on a nonempty finite interval
extends past its right endpoint and past its left endpoint, using the
proved source-space endpoint limit and a newly constructed local
solution. The actual field is continuous at every such real limit,
including periodic terminals and collapsed selected gaps.

The public two-sided continuation theorem combines the two extensions.
The resulting curve agrees with the original at every time in its old
open interval, is real throughout the strictly larger interval, and
solves the actual indexed source equation at every time there, including
both joins. Source norm conservation and actual discriminant
stationarity preserve the original norm and every discriminant value
throughout the larger interval. No limit, replacement trajectory,
positive source norm, or open selected gap is supplied by the caller.

API checks construct local curves at arbitrary starting times, explicitly
verify the actual ODE at both old endpoint times, and check conserved
data across both joins. They also extend a constructed local curve
through an arbitrary real initial Hilbert source without a supplied
curve or continuation.
Constructing one compatible solution for all real times remains, followed
by periodic-terminal reachability and the general theta/theta transport
argument. Bracket compatibility for `1 < p < 2` and later chapters also
remain unfinished; Corollary 13.2 is not complete.

## Latest milestone: the complete actual Hilbert spectral flow

`IntegralCurveUniqueness.lean` proves uniqueness on any connected open
time domain from continuous differentiability of the field along the
first solution. Local Lipschitz uniqueness makes the equality locus
open, continuity makes it closed, and connectedness propagates a common
initial value throughout the domain. No uniform Lipschitz constant is
supplied. `SourceDirichletSpectralUniqueness.lean` applies this to the
actual indexed field at every finite `p >= 2`, using its proved
analyticity near real sources. Only the first solution must be real.

`SourceDirichletSpectralTrajectory.lean` takes the union of all actual
real Hilbert trajectory intervals through the initial source. Their
values agree on overlaps, so choosing a representative defines one
compatible actual curve. The domain is an open interval containing zero,
and the curve solves the actual equation throughout that domain.

`SourceDirichletSpectralGlobalExistence.lean` rules out finite endpoints
of this domain: continuation past its supremum or infimum would create
another actual trajectory with a time outside the purported bound.
The domain is therefore all real times. A public existence theorem
constructs an actual global real solution through every real Hilbert
source, preserving the original norm and every discriminant value.

`SourceDirichletSpectralFlow.lean` proves uniqueness, defines the named
flow on the original real source form, and proves its time-addition and
inverse-time laws by time translation and actual ODE uniqueness. It
solves the original coefficient-space ODE at every real time and agrees
with every actual local solution through its initial source on the
whole original interval. Norm, discriminants, and every periodic gap
are fixed at all times, including for zero sources and collapsed gaps.

`SourceAngularThetaThetaGlobalTransport.lean` proves all-time transport
of the full actual angle/angle bracket along every indexed Hilbert flow.
Only the two angle gaps must initially be open; their conservation keeps
the curve in the actual common angle domain. The selected flow gap may
be collapsed. The theorem uses the constructed global source flow,
without a supplied trajectory or global-continuation assumption.

API checks cover overlap uniqueness at `p = 3`, global existence,
actual derivatives at arbitrary real times, time addition, negative-time
inversion, conservation, zero-source stationarity, agreement with
complex local solutions, and full all-time angle/angle transport.
Periodic-terminal reachability and transport to the proved zero
basepoints remain before the general theta/theta zero identity.
Bracket compatibility for `1 < p < 2` and later chapters also remain
unfinished; Corollary 13.2 is not complete.

## Latest milestone: actual periodic-terminal reachability

`BoundedDerivativeLimit.lean` proves that any finite limiting derivative
of a bounded real differentiable curve is zero. A nonzero limit gives
an eventual positive slope bound, and the mean value theorem forces
growth exceeding the original bound. Negating the curve handles a
negative limit.

`RealSheetEndpoint.lean` proves that a complete bounded real trajectory
with `x' = v`, `v' = F(x)` and `v^2 = G(x)` reaches zero velocity whenever
`F` is nonzero at every sheet zero in its interval. If velocity never
vanished, continuity would fix its sign. Bounded monotone position
would converge, and the sheet identity would give a velocity limit.
The derivative-limit theorem forces that limit to be zero and also
forces the limiting acceleration to be zero, contradicting the sheet
zero condition. The proof does not assume a reachable endpoint.

`RealOpenGapEndpointSimple.lean` derives nonzero actual discriminant
derivatives at both endpoints of every open real periodic gap for all
finite `p > 1`, including central indices. The unique critical point is
strictly inside that gap, so an endpoint cannot be critical. No endpoint
simplicity premise is supplied by the caller.

`SourceDirichletSpectralGlobalSheet.lean` exports the actual all-time
terminal equations and fixed initial compact sheet of the complete
Hilbert source curve. Every periodic endpoint and every other indexed
Dirichlet root and full terminal anti-discriminant is fixed for all real
times, including at collapsed gaps and periodic terminals.

`SourceDirichletSpectralReachability.lean` applies the bounded-sheet
theorem to the actual global source flow. The real selected Dirichlet
coordinate has velocity minus half the terminal anti-discriminant.
Its reality also proves reality of that terminal value directly from
the actual ODE. The spectral identity gives the scalar sheet equation;
the actual gap characterization identifies its zeros with the original
two endpoints. At either open-gap endpoint the acceleration is nonzero.
The constructed flow therefore reaches one of its original periodic
endpoints at some finite real time, with zero full terminal
anti-discriminant. Collapsed gaps are handled at time zero. The public
theorem includes every real Hilbert source without open-gap, positive
norm, trajectory, or reachability assumptions.

API checks cover endpoint derivative nonvanishing at `p = 3`, the
actual global fixed-sheet equations, unchanged other terminals, and
a constructed periodic-terminal source preserving the original norm,
every discriminant value, and the full angle/angle bracket. Only the
two angle gaps must initially be open for the bracket transport check;
the selected flow gap may collapse.
Finite compositions of these actual moves, transport to the all-terminal
zero basepoints, and density remain before the general theta/theta
zero identity. Bracket compatibility for `1 < p < 2` and later chapters
also remain unfinished; Corollary 13.2 is not complete.

## Latest milestone: actual finite-gap Hilbert angle/angle involution

`SourceDirichletSpectralFiniteTransport.lean` defines a finite sequence
of actual indexed source flows by folding a list of index/time pairs in
list order. Every such sequence preserves the original Hilbert source
norm, all discriminant values, all periodic gaps, and both periodic
endpoints. A finite-set induction constructs a move list placing every
selected terminal at one of its original periodic endpoints, with zero
full terminal anti-discriminant. Every other Dirichlet root and terminal
anti-discriminant is retained. A further theorem constructs a list
making all terminals periodic whenever only finitely many are initially
nonperiodic; every initially periodic terminal retains its original root.

`SourceFiniteGap.lean` defines the actual real finite-gap locus at every
finite `p > 1` by finiteness of the open indexed periodic gaps. This is a
spectral condition, distinct from finite Fourier support. The proved
collapsed-gap identity makes each corresponding terminal
anti-discriminant zero. Thus every finite-gap source has only finitely
many nonperiodic Dirichlet terminals.

`SourceAngularThetaThetaFiniteGap.lean` proves that every finite sequence
of actual Hilbert flows preserves the full actual angle/angle bracket
when its two angle gaps are initially open. Periodic gap conservation
keeps both open throughout the composition. The constructed all-terminal
periodic basepoint has the proved zero bracket, so the original source
has zero bracket whenever only finitely many terminals are nonperiodic.
The public finite-gap theorem derives that condition from the actual
finite-gap locus, without a supplied trajectory, move list, basepoint,
or angle-transport premise.

API checks verify flow-list order, simultaneous placement over an
arbitrary finite set with all outside terminals retained, preserved
source norm and discriminants, construction of an all-terminal periodic
basepoint with unchanged full angle bracket, and bracket vanishing from
a spectral closed-gap tail condition. The finite-gap implication for
nonperiodic terminals is also checked at `p = 3`.
This proves the actual finite-gap Hilbert angle/angle identity. Density
and exponent extension remain before the general theta/theta zero
identity. Bracket compatibility for `1 < p < 2` and later chapters also
remain unfinished; Corollary 13.2 is not complete.

## Latest milestone: analytic spectral centers and a closing criterion

`ResonantDiagonalCenter.lean` constructs the unique solution of
`z = nπ + a_n(z)` in every full resonant strip with the proved distant
bounds. A contraction on a closed disc gives existence; the center
lies within `π/32` of the free lattice and has a nonzero residual
derivative. The center is real for a conjugation-symmetric diagonal.
Comparing two center equations gives the source stability factor `8/7`,
with the diagonal difference evaluated at one fixed spectral parameter.

`ResonantCenterCollapse.lean` proves that vanishing of both off-diagonal
entries at this center makes it the only determinant zero in the full
strip. Cauchy bounds give Lipschitz constants `1/8` for the diagonal
and `1/4` for each off-diagonal. These estimates force every determinant
zero to coincide with the center, including for complex sources.

`WeightedResonantDiagonalCenter.lean` names the actual centers and
constructs one open convex source neighborhood for every distant signed
index. The closing criterion identifies the original periodic spectrum
in the strip with the single center and proves determinant order two
there, using the earlier exact two-root count. The center is real for
either potential reality sign. These results hold for arbitrary spectral
weights and every finite `p > 1`.

`WeightedResonantDiagonalCenterAnalytic.lean` proves source continuity
from the center comparison, then applies the analytic implicit-root
theorem to the nonzero residual derivative. The centers and both actual
off-diagonal entries evaluated at them are analytic on one common
neighborhood for every distant index.

API checks cover a displaced center, stability at a fixed spectral
parameter, weighted original-spectrum closing with exact multiplicity
at `p = 3`, and a common analytic tail-equation neighborhood at `p = 3/2`.
The sequence-space map of these equations and a construction solving
their simultaneous tails are still needed for finite-gap density.
General angle/angle involution, bracket compatibility below two, and
later chapters remain unfinished; Corollary 13.2 is not complete.

## Latest milestone: the analytic sequence map of spectral closing equations

`WeightedResonantCenterRemainder.lean` assembles the actual off-diagonal
coefficients at the named spectral centers into an `ℓᵖ` pair remainder,
after subtracting the signed leading Fourier coefficients and multiplying
by `w(2n)`. The full-strip supremum estimates prove membership and a
quantitative joint norm budget using the original component-sum source
norm and its Fourier tail. `FunctionOrZero.lean` supplies the total
sequence constructor; proved membership retains every actual coefficient.

`WeightedResonantCenterRemainderSmall.lean` makes the joint remainder norm
arbitrarily small on one open convex source neighborhood for every larger
cutoff. `WeightedResonantCenterRemainderAnalytic.lean` combines scalar
moving-center analyticity with this sequence bound to prove Banach
analyticity of the actual pair map.

`WeightedResonantLeadingTail.lean` constructs the signed weighted leading
Fourier tail as a continuous linear map. Its norm is bounded by the source
Fourier tail at `2N` with constant one. The negative component samples
`φ₁(−2n)` and the positive component samples `φ₂(2n)`.

`WeightedResonantCenterClosingTail.lean` adds these two maps. Its high
coordinates are exactly `w(2n) b⁻_n(ζ_n)` and `w(2n) b⁺_n(ζ_n)`, and
its lower block is zero. On one neighborhood, it is analytic for every
larger cutoff and differs from the leading Fourier map by less than any
chosen positive tolerance. Its zero coordinates imply that the original
periodic spectrum in that strip consists of the actual center, with
determinant order exactly two. All results hold for arbitrary spectral
weights and every finite `p > 1`.

API checks cover the exact signed leading coefficients and tail norm
at `p = 3`, the constructed zero lower block and original-spectrum
closing implication, the combined Hilbert norm budget, and sequence
norm analyticity with arbitrary tolerance at `p = 3/2`.

The neighborhood can depend on the tolerance. Fixed-ball derivative
control, an inverse construction, and solving the simultaneous tail
equations remain before finite-gap density. General angle/angle
involution, bracket compatibility below two, and later chapters remain
unfinished; Corollary 13.2 is not complete.

## Latest milestone: fixed-ball derivative estimates for the actual closing map

`PowerTailBallBudget.lean` first fixes a positive source radius, then
chooses one cutoff valid for every larger cutoff. The center's Fourier
tail is small, and the contractive tail operator bounds every perturbation
throughout the fourfold source ball. This controls the power-tail budget
by the appropriate power of the radius without compactness of the ball.

`WeightedResonantCenterRemainderDerivative.lean` uses that estimate in the
actual component-sum remainder budget. With an explicit constant `K`
depending on the exponent and source norm bound, the remainder norm is
at most `K r²` on the fourfold ball. Schwarz estimates make its full
Fréchet derivative smaller than any positive tolerance on the threefold
ball. The remainder is Lipschitz there with that tolerance, and its
derivative is Lipschitz on the inner ball with constant `4K`. The latter
constant is independent of the chosen radius and cutoff. Membership and
the actual coefficients are proved throughout the outer ball.

`WeightedResonantCenterClosingTailDerivative.lean` identifies the full
closing-map derivative with the signed weighted leading Fourier operator
plus the actual remainder derivative. It constructs one fixed ball where
the derivative difference is arbitrarily small, for every larger cutoff,
and proves the full derivative's Lipschitz bound. The actual weighted
moving-center closing equations and the zero block below the cutoff are
retained. All results hold for arbitrary spectral weights and every
finite `p > 1`.

The radius may depend on the requested derivative tolerance. An adapted
source map, its local inverse, and solving the simultaneous tail equations
remain before finite-gap density. General angle/angle involution, bracket
compatibility below two, and later chapters remain unfinished; Corollary
13.2 is not complete.

API checks cover the fixed-ball squared tail budget at `p = 3`, an
actual Hilbert remainder contraction on a closed ball, the full closing
derivative's `1/4` approximation and Lipschitz bound at `p = 3`, and
arbitrary derivative tolerance on a fixed ball at `p = 3/2`.

## Latest milestone: the adapted source map and its uniform analytic inverses

`SourceWeightedPeriodOne.lean` embeds the original source pair into the
unit-weighted physical pair by an exact isometry. The original periodic
operator receives precisely `periodOnePotential`. A second isometry
reflects only the first output component, restoring the original index
of the negative leading coefficient.

`SourceAdaptedClosingMap.lean` adds the transported actual remainder to
the identity. The low Fourier block keeps the original coefficients;
the high first component at `n` is the negative equation at resonance
`−n`, and the second is the positive equation at resonance `n`.
`SourceAdaptedClosingMapDerivative.lean` transfers the quadratic remainder
bound, analyticity, arbitrarily small derivative difference from the
identity, and derivative Lipschitz bound to the original source norm.
One fixed ball works for every larger cutoff at every finite `p > 1`.

`NearIdentityAnalyticInverse.lean` constructs the required derivative
equivalences from the Neumann criterion and bounds their inverses by
two. The quantitative analytic inverse theorem then supplies actual
analytic inverse branches on common positive balls. A lower distance
bound shows that inverse displacement is at most twice target displacement.

`SourceResonantCenterClosing.lean` transports the common closing
neighborhood to the original period-one source, preserving the actual
original periodic operator and exact determinant order.

`SourceAdaptedClosingInverse.lean` applies this to the actual adapted
source map. One source radius and cutoff work for every larger cutoff,
with image and source radii expressed by the earlier quantitative
inverse formulas. Each branch fixes the original source at its image
and is unique in the stated source ball. Its high target coordinates
are exactly the actual moving-center spectral equations at the recovered
source. Zero high target coordinates imply a singleton original periodic
spectrum in that strip and determinant order exactly two there.

Constructing truncated targets inside the common image balls and
preserving the real-type locus remain before finite-gap density.
General angle/angle involution, bracket compatibility below two, and
later chapters remain unfinished; Corollary 13.2 is not complete.

Public-API examples verify the exact source norm, even physical coefficients,
and original operator identity at `p = 3`; unchanged low coefficients,
the derivative's `1/4` proximity, and the signed high equations on the
constructed source ball; the actual Hilbert analytic inverse and its
original-spectrum closing implication; and analytic right inversion with
uniqueness at `p = 3/2`.

## Latest milestone: Corollary 1.6, actual real finite-gap density

`SourceClosingTargets.lean` proves that symmetric truncations eventually
lie in every fixed positive image ball centered at the actual adapted
spectral map. Both the truncation error and the actual source remainder
tend to zero in the original pair norm. The first omitted index is
`N+1` for the retained closed Fourier block `[-N,N]`.

`SourceAdaptedClosingMapReality.lean` transports real type to the weighted
physical source and proves conjugacy of the actual off-diagonal equations
at the real moving centers. Thus every sufficiently large adapted map
preserves real type on one common source neighborhood.
`NearIdentityClosedSubspaceInverse.lean` constructs a fixed point inside
a preserved closed real subspace and identifies it with the ambient
inverse image. `SourceAdaptedClosingInverseReality.lean` applies this to
obtain actual analytic inverse branches that preserve real type on
smaller common image balls, uniformly in all larger cutoffs.

`SourceClosingApproximation.lean` inverts the actual truncated targets.
The recovered sources are real, arbitrarily close in source norm, and
solve both closing equations at every sufficiently distant resonance.
The original periodic spectrum there is the single actual center and
its determinant has order two.

`SourceFiniteGapClosingCriterion.lean` connects this spectral statement
to the canonical indexed gaps: both distant endpoints lie in the strip
and coincide. `SourceFiniteGapDensity.lean` proves density of the existing
actual real finite-gap locus at every finite `p > 1`, establishing
Corollary 1.6. Approximation can retain any open real source condition,
and continuous identities on that open set extend from finite-gap sources.

Public-API examples check the exact truncation boundary, reality,
common inverse target balls, real inverse images below two, actual
closing equations and original determinant order, finite canonical gaps,
and density at Hilbert and non-Hilbert exponents. They also use density
to extend a continuous identity within an open real source set.

General Hilbert angle/angle involution is the next application. Bracket
compatibility below two and later chapters remain unfinished;
Corollary 13.2 is not complete.

## Latest milestone: the Hilbert case of Corollary 13.2

`SourceAngularThetaThetaHilbert.lean` transfers the actual finite-gap
angle/angle identity to every real Hilbert source with both selected
gaps open. The bracket is analytic on the joint open-gap domain, and
actual finite-gap density retains that open condition. The file also
exposes this density transfer at other exponents when the corresponding
finite-gap identity is available.

`SourceCorollary13_2Hilbert.lean` combines the result with actual
action/action commutation and the mixed Kronecker identity. One
constructed common analytic source domain and normalized psi family
now carry all three Hilbert canonical relations. Action/action
commutation holds on the whole real source locus; angle/angle requires
both angle gaps open, while angle/action requires only the angle gap.
The physical Poisson sign and the original indexed actions are retained.

Public-API examples use arbitrary real Hilbert sources, verify mixed
normalization `1` on the diagonal and `0` off it, transfer involution to
the actual analytic phases, and construct the common source domain and
family carrying the canonical relations.

Angle/angle involution for `p > 2`, the bracket pairing for `1 < p < 2`,
and later chapters remain unfinished. This completes Corollary 13.2 at
`p = 2`, with its full exponent range still pending.

## Latest milestone: actual discriminant brackets for all finite exponents

`RegularSourceCotangent.lean` records a continuous source cotangent
with proved square-summable Fourier coefficients. Its physical pairing
uses the same frequency reversal and sign `-i`, has an absolutely
convergent Fourier formula, and is independent of the coefficient
witness. Restriction along every source exponent inclusion preserves
it, including below two. At exponents at least two it agrees exactly
with the existing source bivector.

`SourceDiscriminantRegularPoisson.lean` proves exponent compatibility
of the actual discriminant differential. Below two this constructs its
Hilbert coefficient pair by restriction of the Hilbert derivative.
The resulting coefficients depend analytically in the Hilbert norm
on both the source and spectral parameter, and are independent of the
source exponent. The actual discriminant bracket now vanishes for
every complex source at every finite `p > 1`, with absolute convergence
proved for the original Fourier expression.

Public examples exercise `p = 3/2`, analytic Hilbert coefficient
regularity, absolute convergence, compatibility across exponent two,
and agreement with the established bivector at `p = 3`.

This supplies the regular pairing and discriminant commutation needed
below two. Regularity and the canonical identities for the actual
action and angle cotangents below two are still pending, as is
angle/angle involution above two. Corollary 13.2 is complete at `p = 2`
only; its full exponent range and later chapters remain unfinished.

## Latest milestone: action commutation for every finite exponent

The action/action identity in Corollary 13.2 now holds for the full
range `1 < p < ∞`. `SourceActionRegularCotangent.lean` constructs
square-summable coefficient pairs for the actual indexed action
Fréchet derivatives at every real source. No finite-gap or open-gap
hypothesis is required, so collapsed action gaps are included.

The construction integrates the discriminant variation divided by the
canonical root around an existing action chart's isolating circle.
Both the original source cotangent and its Hilbert coefficient pair
are integrable. `RegularSourceCotangentIntegral.lean` proves that
integrating them preserves their coordinate identities and commutes
with the physical bilinear pairing. Any admissible chart produces the
same coefficient pair because its underlying cotangent is the actual
action derivative.

`SourceActionRegularPoisson.lean` applies discriminant commutation to
the resulting double contour integral. It proves vanishing of the
regular action bracket and of the literal Fourier formula, with
absolute convergence in the original derivatives. At exponents at
least two, this pairing agrees with the existing source bracket.
Public examples check these conclusions at `p = 3/2`, agreement with
the old bracket at `p = 3`, and independence of the chosen chart.

The action/action part of Corollary 13.2 is now complete for all finite
`p > 1`. The angle/action identity below two and angle/angle identity
away from two remain unfinished, along with later chapters. All three
canonical relations are currently complete together only at `p = 2`.

## Latest milestone: boundary separation relations for every finite exponent

The actual signed Dirichlet and Neumann roots, moving Floquet
multipliers, and normalized local Floquet logarithms now have proved
square-summable cotangent coefficients for every finite `p > 1`.
`SourceBoundaryExponentDifferential.lean` proves exponent compatibility
of the full moving root and multiplier differentials. Below two the
regular cotangents are restrictions of their actual Hilbert derivatives;
above two they use the existing continuous cotangent construction.
The root and multiplier Hilbert coefficient pairs themselves are
independent of the source exponent.

`SourceBoundaryRegularPoisson.lean` proves all three separation
relations within either ordinary boundary family: roots commute,
Floquet logarithms commute, and the mixed bracket is `-δnm/2`.
The local logarithm is the actual analytic logarithm normalized at the
source, with its derivative verified against the regular cotangent.
No supplied branch, finite-gap assumption, or open-gap assumption is
needed. The original mixed Fourier formula is absolutely convergent
and has the same exact normalization, including at collapsed gaps.

Public examples use `p = 3/2`, both boundary conditions, arbitrary
signed indices, the literal actual-derivative Fourier pairing, and
coefficient compatibility across exponent two to `p = 3`.

These are the spectral separation relations used in the angle
construction. The angle/action identity below two and angle/angle
identity away from two still require extension; this step does not
claim them. Corollary 13.2's action/action identity is complete for all
finite `p > 1`, while all three angle/action canonical relations are
currently complete together only at `p = 2`. Later chapters remain
unfinished.

## Previous milestone: actual psi root and contour compatibility across exponents

The canonical real gap-contained psi root sequence is now proved
independent of the source exponent under coefficient-preserving
inclusion. Its entire normalized psi numerator is therefore the same
function at every larger finite exponent. The actual common-domain
complex psi families used in the angle construction inherit this
agreement at real sources from their proved real-root agreement.

`SourceCanonicalRootExponent.lean` identifies the periodic gap segments,
standard roots, canonical root product, and their omitted and full
gap-complement domains across exponents. The equality keeps the
original normalization and includes spectral zeros.
`DeletedExponentEmbedding.lean` supplies the contractive inclusion
on the genuine deleted-coordinate sequence spaces.

`SourcePsiContourExponent.lean` proves equality of the normalized
contour functionals and equation coordinates on the same circles,
with both source potentials and numerator root data included.
`SourcePsiGapRootExponent.lean` carries actual gap-contained solutions
across exponents. It explicitly proves that every scalar equation is
zero and constructs the corresponding zero sequence in the target
space, so the selected equation map's out-of-domain default is not
used. The established real solution uniqueness then identifies the
actual selected roots.

Public examples cross exponent two from `p = 3/2` to `p = 3`, compare
entire numerators from `p = 2` to `p = 3`, preserve the literal contour
normalization, compare the canonical root at arbitrary spectral
parameters, and use the normalized common-domain psi families.

This proves compatibility of the actual spectral input to the angles.
Compatibility of the full angle phases and their differentials remains
to be established. The angle/action identity below two and angle/angle
identity away from two remain unfinished; Corollary 13.2 is still
complete in all three relations together only at `p = 2`. Its
action/action identity is complete for every finite `p > 1`, and later
chapters remain unfinished.

## Previous milestone: beta correction and derivative compatibility across exponents

The actual beta values, their full off-diagonal correction series, and
that correction's complex derivative now agree under source exponent
inclusion for every finite `1 < p ≤ q`. This includes collapsed gaps
and endpoint Dirichlet terminals.

`SourceAngularPrimitiveExponent.lean` preserves the prescribed square-root
sheets, their spectral domains, and the normalized primitive conditions.
It transports the same witnesses in both directions and identifies the
complete sets of regular Dirichlet terminal values whenever the fixed-source
psi numerators agree. `SourceAngularBetaExponent.lean` then preserves the
endpoint zero convention, the chosen beta values, and the full series.
For actual common-domain psi families, the preceding gap-root uniqueness
result supplies numerator agreement at every real source.

`SourceHolomorphicRealGerm.lean` packages the real-form identity principle
for analytic Banach-valued source maps. Using the already proved
analyticity of the beta series, `SourceAngularBetaExponentDifferential.lean`
extends the actual real agreement to a complex neighborhood and identifies
the full correction derivative after restriction by exponent inclusion.
No open-gap hypothesis or supplied exponent-compatibility assumption is
needed for the actual-family results.

Public examples compare prescribed-sheet domains at complex sources and
actual beta values, correction sums, complex germs, and full derivatives
across exponent two, from `p = 3/2` to `p = 3`.

The eta contribution, full theta phase, and theta differential still need
exponent compatibility. The angle/action identity below two and angle/angle
identity away from two remain unfinished. Corollary 13.2 is complete in all
three relations together only at `p = 2`; its action/action identity is
complete for every finite `p > 1`. Later chapters remain unfinished.

## Previous milestone: full angle phase and differential compatibility across exponents

The actual eta phase, full theta phase, and full logarithmic angle
differential now agree under coefficient-preserving source inclusion
for every finite `1 < p ≤ q`, at every real source with the selected
gap open. Compatibility is proved for independently constructed
common-domain families, without supplied phase or derivative agreement.

`SourceAngularEtaRemainderExponent.lean` identifies the normalized
omitted root products and both remainder differentials. It transports
normalized sheet primitive witnesses and compares the actual Cauchy
remainder values across different annuli, anchors, and circles. The
comparison includes endpoint Dirichlet terminals and collapsed gaps
where the annular charts are defined.

`SourceAngularEtaPhaseExponent.lean` compares the terminal sine and
cosine coordinates, allowing either half-gap sign. Actual eta
representatives therefore differ by an integer multiple of pi across
exponents, and their phases agree. The constructed common-domain
charts and previously proved psi agreement instantiate this at every
real open gap.

`SourceAngularThetaExponent.lean` combines eta and beta agreement.
Real-form uniqueness extends the full phase equality to a complex
neighborhood of each real open-gap source. Differentiation gives
compatibility of the complete angle cotangent, including the moving
spectral data and infinite correction series.

Public examples compare omitted products at complex sources and the
actual eta phase, theta phase, complex germ, and angle differential
across exponent two, from `p = 3/2` to `p = 3`.

Next use this cotangent compatibility to establish square-summable
angle coefficients below two and transfer the remaining canonical
relations. The angle/action identity below two and angle/angle identity
away from two remain unfinished. Corollary 13.2 is complete in all
three relations together only at `p = 2`; its action/action identity is
complete for every finite `p > 1`. Later chapters remain unfinished.

## Previous milestone: Corollary 13.2 for every finite exponent above one

Corollary 13.2 (printed page 72) is now proved for every finite `p > 1`:
actual actions commute; actual angles commute where both selected gaps
are open; and the angle/action bracket is the Kronecker delta wherever
the angle's own gap is open. The action gap need not be open.

`SourceAngularThetaRegularCotangent.lean` constructs square-summable
Fourier coefficients for the full actual angle differential. Below two,
this uses the proved restriction of a constructed Hilbert angle; above
two, continuity suffices. Coefficient uniqueness makes the choice
irrelevant and proves exponent compatibility of the entire pair.

`SourceAngularThetaThetaExponent.lean` transfers Hilbert angle commutation
to finite Fourier sources above two, then uses real Fourier truncation
and continuity on the joint open-gap domain. Below two, the actual
regular cotangents restrict from Hilbert space. This argument keeps
finite Fourier support distinct from the spectral finite-gap locus.

`SourceActionExponentDifferential.lean` compares real actions using one
common small midpoint circle, then proves equality of the complex germs,
full derivatives, and regular coefficient pairs under exponent inclusion.
`SourceCorollary13_2Regular.lean` uses this with the angle compatibility
to prove the remaining mixed relation below two and assembles all three
canonical relations for one actually constructed common-domain family.

`SourceAngularRegularFourier.lean` gives the literal Fourier angle/angle
and angle/action sums, with frequency reversal and the physical sign
`-i`. Their absolute convergence is proved for all finite `p > 1`.
Together with the previously proved action/action sum, these identify
the regular pairings with the original derivative formulas. On `p ≥ 2`
they agree with the existing source brackets.

Public examples verify angle commutation at `p = 3`, action coefficient
compatibility across two, and the full three-relation package and
absolutely convergent literal angle brackets at `p = 3/2`.

The next dissertation step is Chapter 3: rectangular Birkhoff coordinates
and their analytic extension through collapsed gaps (Sections 14–15),
leading to Theorem 14.1. Later chapters remain unfinished.

## Latest milestone: analytic gap-weighted eta coordinates through collapsed gaps

Section 15's gap-weighted eta coordinates now have constructed analytic
extensions through collapsed gaps on one complex neighborhood of the
whole real source locus, for every finite `p > 1`. Their open-gap values
are proved to be the actual `γₙ exp(±iηₙ)` expressions. This establishes
the analyticity part of Lemma 15.1; its index-uniform bound remains open.

`SourceAngularEtaRemainderGlobal.lean` glues the normalized Cauchy remainder
values by their proved overlap uniqueness. The resulting single remainder
is analytic on every actual annular chart with analytic Dirichlet roots,
including at closed gaps. It vanishes at endpoint terminals.

`SourceGapWeightedEta.lean` uses the Dirichlet displacement from the
periodic midpoint, the anti-discriminant divided by twice the omitted
root product, and the exponential of that remainder. No division by
the gap width appears. Both signed coordinates are analytic on the full
chart, and their product is exactly the squared periodic gap, even at
complex collapsed gaps.

`SourceGapWeightedEtaAngle.lean` identifies the formula with twice the
chosen half-gap times the exponential of the actual eta representative.
For the canonical half-gap, this is precisely Section 15's original
coordinate. `SourceGapWeightedEtaCommonDomain.lean` constructs one open
neighborhood carrying every indexed coordinate for the same actual psi
family. Both coordinates vanish at real collapsed gaps. At complex
collapsed gaps, the theorem asserts only their zero product, allowing
one coordinate to be nonzero as described in the dissertation.

Public examples construct the common analytic domain at `p = 3/2`,
verify the product identity without an open-gap assumption, check real
collapsed-gap vanishing, and identify an actual negative-sign coordinate
with its open-gap eta exponential.

Next prove the locally uniform, index-uniform estimate in Lemma 15.1,
then combine these coordinates with the normalized action factors and
beta correction to build the rectangular Birkhoff map of Theorem 15.2.
The remaining assertions of Theorem 14.1 and later chapters are unfinished.

## Latest milestone: complete analytic and uniform estimate of Lemma 15.1

Lemma 15.1 (printed page 75) is now proved for every finite `p > 1`.
The actual gap-weighted eta coordinates extend analytically to a common
complex neighborhood of the whole real source locus, and
`‖zₙ±‖ ≤ C (‖γₙ‖ + ‖μₙ−τₙ‖)` holds locally uniformly there with one
constant for every integer index and both signs. Closed gaps and
periodic endpoint terminals are included.

`SourceAngularEtaRemainderBound.lean` controls the normalized interior
Cauchy quotient by `π ρ² M / (ρ−r)³`, where `M` bounds the actual diagonal
numerator minus `i` on the enclosing circle. Multiplying by the actual
Dirichlet coefficient gives a remainder bound; the chart geometry bounds
that coefficient by three inner radii. No inverse gap width occurs.

`SourcePsiUniformRootNormBound.lean` derives a uniform full `ℓᵖ` norm
bound for every deleted root vector from its squared-gap offsets.
`SourceAngularEtaDiagonalBound.lean` identifies the diagonal numerator
with `i` times the actual deleted quotient and applies the bounded-input
quotient majorant to all sufficiently distant free-centered discs.

`SourceGapWeightedEtaBound.lean` proves the terminal sine-numerator
estimate and the coordinate bound with constant `4 exp(B)` whenever the
remainder has norm at most `B`. Analyticity supplies a local estimate
for each fixed chart. `SourceGapWeightedEtaUniformBound.lean` combines
the fixed-radius tail charts with a finite intersection of these head
neighborhoods, giving one constant for every index near each real source.
`SourceGapWeightedEtaLemma15_1.lean` takes the union of these neighborhoods
and proves local uniformity at every complex point of the common domain.
The exact product `zₙ⁺ zₙ⁻ = γₙ²` and real collapsed-gap vanishing persist.

Public examples check the complete common-domain result at `p = 3/2`,
the estimate at a complex collapsed gap with its displacement term
retained, and the interior Cauchy quotient bound without a regular-terminal
hypothesis. All new statements use the actual previously constructed
psi family and coordinates.

Next combine these coordinates with the normalized action factors and
beta correction to construct the rectangular coordinates in (3.2) and
the analytic sequence-valued Birkhoff map of Theorem 15.2. Lemma 15.3,
the remaining assertions of Theorem 14.1, and later chapters are unfinished.

## Latest milestone: analytic rectangular coordinates and exact action radii

Formula (3.2) now defines the actual rectangular coordinates `xₙ` and
`yₙ` for every finite `p > 1`. One constructed complex neighborhood of
the whole real source locus supports every coordinate analytically,
including at collapsed gaps. On that domain the exact identity
`xₙ² + yₙ² = 2 Iₙ` holds for the original glued indexed action.
Both rectangular coordinates vanish at real collapsed gaps.

`SourceNormalizedActionRootAnalytic.lean` upgrades the normalized-action
factors from complex differentiability to full Banach power-series
analyticity. Joint analyticity of the rationalized contour integrand
passes through its enclosing circle. Fixed tail circles and a finite
head intersection yield a single domain for all indices, preserving
the squared-gap action factorization. The principal square-root factors
are analytic on a smaller common positive-real-part neighborhood.

`SourceBirkhoffCoordinates.lean` multiplies the constructed signed eta
coordinates by the actual action root and beta exponential. The sum
divided by `√8` defines `x`; the difference divided by `√8 i` defines
`y`. Cancellation of the opposite beta phases and Lemma 15.1's product
identity prove the exact squared-radius formula without a nonzero-gap
assumption. `SourceBirkhoffCoordinateAngle.lean` proves agreement with
(3.1), including its positive sine orientation and `√2` normalization,
on every actual eta chart with the canonical half-gap.

`SourceBirkhoffCoordinateCommonDomain.lean` assembles the analytic domain
and its all-index action identities for the same psi family. Public
examples check the common rectangular domain at `p = 3/2`, the original
sine formula, and common-domain action-root analyticity at `p = 3`.

This establishes the scalar rectangular construction. The next step is
to prove its locally bounded `ℓᵖ` realization, assemble the analytic
sequence-valued map, and prove that real sources give real coordinate
sequences. Theorem 15.2 is not yet complete. Lemma 15.3, the remaining
assertions of Theorem 14.1, and later chapters remain unfinished.

## Latest milestone: complex analytic sequence-valued Birkhoff map

The rectangular coordinates now assemble into the actual Banach-valued
map `sourceBirkhoffMap : CoeffPair p → Coeff p × Coeff p` for every
finite `p > 1`. One constructed complex neighborhood contains the whole
real source locus and supports full power-series analyticity of this
map, locally uniform sequence-norm bounds, and exact evaluation at every
index. Its coordinates retain `xₙ² + yₙ² = 2 Iₙ` and vanish at real
collapsed gaps. This proves the complex sequence-map part of Theorem 15.2.

`SourceAngularBetaCorrectionBound.lean` combines the actual reciprocal
beta estimate with Hölder summation, producing one scalar bound for all
corrections and local bounds on the gap and Dirichlet-minus-midpoint
sequence norms. `SourceBirkhoffCoordinateBound.lean` bounds all action
roots by their actual `ℓᵖ` deviations and transfers these estimates to
both rectangular coordinates without a nonzero-gap assumption.

`TwoSequenceBound.lean` proves membership and a norm bound for any
sequence dominated by a constant times two coefficient magnitudes.
`SourceBirkhoffSequence.lean` defines the actual rectangular sequences,
proves exact evaluations wherever this majorant holds, and assembles
the coordinate power series using the bounded-coordinate analytic theorem.
Thus the total constructor's fallback is excluded throughout the domain.

`SourceBirkhoffSequenceLocal.lean` instantiates every bound near each
real source from the existing spectral and angular theorems.
`SourceBirkhoffMapAnalytic.lean` takes the union of these neighborhoods
and packages the analytic map, local bounds, scalar evaluations, and
action radii in `SourceBirkhoffMapComplexData`. The construction has no
unproved summability, local-bound, or analyticity premises.

Public examples check Banach-valued analyticity and exact sequence
coordinates at `p = 3/2`, local sequence-norm bounds and action radii at
`p = 3`, and the actual sequence entries at real closed gaps.

Next prove that real sources give real coordinate sequences and package
the real analytic restriction to complete Theorem 15.2. Lemma 15.3,
the remaining assertions of Theorem 14.1, and later chapters are unfinished.

## Latest milestone: Theorem 15.2, the real analytic Birkhoff map

Theorem 15.2 is now proved for every finite `1 < p < ∞`. The actual
rectangular sequence map restricts to a real analytic map from the
complete real source space to `RealCoeff p × RealCoeff p`, where
`RealCoeff p` is the space of real `ℓᵖ` sequences. Its continuous complex
inclusion equals the previously constructed complex analytic map on
every real source. The complex domain contains the entire real locus.

`SourceAngularRealCharts.lean` constructs actual eta charts for the
existing normalized root family inside any open part of its angular
domain. It proves reality of every off-diagonal beta and its convergent
correction. This avoids changing the root family when relating the
Birkhoff map to real angle representatives.

`SourceBirkhoffMapReal.lean` proves that the principal action root is real
and uses the exact cosine/sine formulas at open real gaps. At closed
gaps it uses the already proved vanishing theorem. Consequently both
actual complex sequence coordinates have zero imaginary part at every
real source, without any open-gap assumption.

`RealCoeff.lean` supplies bounded real linear maps for taking real
parts and including real sequences into complex sequences.
`SourceBirkhoffTheorem15_2.lean` defines `sourceRealBirkhoffMap`, proves
its full Banach-valued real analyticity by restricting scalars, and
identifies its complex inclusion with `sourceBirkhoffMap`. It also
proves the real action-radius identity. The existence theorem constructs
all data without supplied reality or analytic-extension hypotheses.

Public examples exercise Theorem 15.2 at `p = 3/2`, the real action-radius
identity at `p = 3`, and the actual real coordinates at closed Hilbert
gaps. Next prove Lemma 15.3's rectangular Poisson identities with the
stated sign `{xₙ,yₘ} = −δₙₘ`. The remaining assertions of Theorem 14.1
and later chapters remain unfinished.

## Latest milestone: rectangular Poisson identities at open real gaps

For every finite `1 < p < ∞`, the actual rectangular coordinates now
satisfy all three identities of Lemma 15.3 whenever their two selected
real periodic gaps are open: `{xₙ,xₘ} = 0`, `{xₙ,yₘ} = −δₙₘ`, and
`{yₙ,yₘ} = 0`. The diagonal mixed bracket has the required negative sign.
The identities concern the coordinates built from the same normalized
root family as the proved action-angle theorem.

`SourceBirkhoffCoordinateAngle.lean` now proves the cosine/sine formulas
throughout each analytic half-gap chart, retaining the earlier formulas
at a canonically normalized half-gap. `RectangularDifferential.lean`
differentiates a local amplitude whose square is twice the action.
`SourceBirkhoffCoordinateDifferential.lean` instantiates that calculation
with the actual action root, analytic half-gap, and full theta
representative. In particular, it proves the complete source derivative
formulas `dx = x/(2I) dI − y dθ` and `dy = y/(2I) dI + x dθ`.

`RegularSourceCotangentAlgebra.lean` preserves Hilbert coefficient
witnesses under addition and proves the bilinear determinant rule.
`SourceBirkhoffRegularCotangent.lean` uses it to construct regular
cotangents whose underlying functionals are exactly the actual
rectangular derivatives. This verifies the extra Fourier regularity
needed below exponent two.

`SourceBirkhoffOpenGapPoisson.lean` applies Corollary 13.2 and the exact
action radius to prove all three canonical identities. It also gives
the absolutely convergent literal mixed Fourier sum with physical
factor `−i`, and identifies the results with the existing source brackets
at exponents at least two. Public examples check the constructed mixed
sign at `p = 3/2`, the three source brackets at `p = 3`, and exact
derivative identification in the Hilbert case.

Theorem 15.2 remains complete. Lemma 15.3 still requires extending the
rectangular identities across closed gaps and applying them to the
family used for the sequence-valued Birkhoff map. The remaining
assertions of Theorem 14.1 and later chapters are unfinished.

## Latest milestone: canonical rectangular brackets across closed gaps

For every finite `2 ≤ p < ∞`, the actual rectangular coordinates now
satisfy all three canonical source-bracket identities at every real
source, including closed gaps: `{xₙ,xₘ} = 0`, `{xₙ,yₘ} = −δₙₘ`, and
`{yₙ,yₘ} = 0`. The coordinates retain the normalized root family of
the proved action-angle theorem. No angle at a closed gap is assumed.

`SourceFloquetGapOpening.lean` defines the analytic opening function
`ρₙ² − 1` using the actual Dirichlet Floquet multiplier. It vanishes
at a real closed gap and has root bracket `−ρₙ²`, which is nonzero.
`SourceFloquetGapOpeningWitness.lean` uses that bracket and real-form
uniqueness to produce a finite real Fourier source where the opening
function is nonzero. Spectral compatibility transfers this witness to
every finite exponent above one.

`RealAnalyticDenseNonzero.lean` applies the real analytic identity
principle to obtain density of the nonzero locus.
`SourceOpenGapDensity.lean` consequently proves that sources with any
prescribed finite set of gaps open form a dense open subset of the real
source space, for every finite `p > 1`. Arbitrarily small perturbations
can open those gaps while retaining any given open source condition.
This is different from the earlier density of finite-gap sources.

`SourceBirkhoffFixedFamilyAnalytic.lean` proves scalar rectangular
analyticity through closed gaps for the same angular family, using
local annular primitives. `SourceBirkhoffClosedGapPoisson.lean` combines
this with continuity of the physical source bivector for `p ≥ 2` and
the new density theorem to extend all three open-gap identities.
Public examples check simultaneous gap opening at `p = 3/2`, all three
brackets at arbitrary real sources for `p = 3`, and the diagonal mixed
sign at the zero Hilbert source using a constructed family.

Theorem 15.2 remains complete. Lemma 15.3 still requires closed-gap
regularity and canonical brackets for `1 < p < 2`, plus identification
for the family used by the sequence-valued Birkhoff map. The remaining
assertions of Theorem 14.1 and later chapters are unfinished.

## Latest milestone: Lemma 15.3 for the actual Birkhoff map

Lemma 15.3 is now proved for the actual sequence-valued Birkhoff map
of Theorem 15.2 at every finite `1 < p < ∞`, on the entire real source
space, including closed gaps. Its coordinate derivatives satisfy
`{xₙ,xₘ} = 0`, `{xₙ,yₘ} = −δₙₘ`, and `{yₙ,yₘ} = 0` with the physical
Poisson sign. The normalized root family is the map's own family.

`SourceNormalizedActionExponent.lean` identifies normalized action
factors across source exponents. The exact action factorization proves
agreement on open gaps; the new real open-gap density and continuity
extend it through closed gaps. The principal action roots therefore
agree as well.

`SourceBirkhoffCoordinateExponent.lean` constructs annular charts for
any existing angular family at real sources, with no open-gap condition.
The normalized remainder comparison identifies the chart-independent
eta values across exponents and root families. Together with the
spectral, action-root, and beta identities this identifies both actual
rectangular coordinates. Real-form uniqueness then proves agreement
of their complex germs and their complete complex derivatives.

`SourceBirkhoffCanonicalAllExponents.lean` restricts regular cotangents
from a constructed family at an exponent at least two. The derivative
comparison proves that their underlying functionals are precisely the
original rectangular derivatives, even below two and at closed gaps.
Restriction preserves the Hilbert Fourier coefficients and their
physical pairings, so all three canonical identities hold.

`SourceBirkhoffLemma15_3.lean` identifies the derivatives of the exact
sequence-coordinate evaluations on a neighborhood and transfers the
result to the map of Theorem 15.2. It also exports the absolutely
convergent literal mixed Fourier bracket, with frequency reversal and
factor `−i`, and the usual source-bracket identities for `p ≥ 2`.
An existence theorem constructs one real analytic map with all these
canonical regular cotangents at every real source.

Public checks construct such a map at `p = 3/2`, verify the absolutely
convergent diagonal mixed Fourier sum `−1` at the zero source below two,
and apply the existing source-bracket API to the exact map at `p = 3`.
Theorem 15.2 and Lemma 15.3 are complete. Next is Section 16: the
Jacobian, its value at zero, and the finite-gap gradient estimates.
The remaining assertions of Theorem 14.1 and later chapters are unfinished.

## Latest milestone: analytic Jacobian and closed-gap spectral derivatives

Section 16 now has the actual bounded Jacobian of the sequence-valued
Birkhoff map, its complex analyticity on the map's domain, and exact
coordinate evaluations in terms of the rectangular differentials.
At every real source those evaluations admit regular Fourier cotangents
with all three canonical pairings from Lemma 15.3.

`SourceBirkhoffJacobian.lean` defines `sourceBirkhoffJacobian` as the
full derivative of `sourceBirkhoffMap`. Its analyticity is Banach-valued
analyticity into the space of bounded linear operators. Bounded sequence
evaluation and neighborhood agreement identify each coordinate with
its scalar derivative; this applies to arbitrary complex directions.

`SourceGapWeightedEtaClosedDifferential.lean` proves the exact formula
at each real collapsed gap:

`d zₙ^sign = −2 (dμₙ − dτₙ + sign i/(2Pₙ(μₙ)) d[δ(μₙ)])`.

Here `Pₙ` is the omitted standard-root product, and the last derivative
is the full moving terminal anti-discriminant. The normalized eta
remainder and the amplitude vanish at the collapsed gap, while their
derivatives are treated by the product rule. Only the nonzero omitted
product is divided by; no closed-gap angle is defined.

`SourceGapWeightedEtaFiniteGapDifferential.lean` constructs every needed
annular chart for the existing angular family and removes chart premises
from the result. It expands the moving terminal derivative into the
fixed-source anti-discriminant cotangent plus its spectral derivative
times `dμₙ`. For every real finite-gap source it proves the formula at
all indices outside a finite set, simultaneously for both signs. The
finite-gap assumption is spectral, not finite Fourier support.

Public checks cover Jacobian evaluations at `p = 3`, the closed-gap
formula at zero for every signed index at `p = 3/2`, and the actual
finite-gap tail formula for the sequence map's own angular family.
Theorem 15.2 and Lemma 15.3 remain complete. The explicit Fourier
identification of the Jacobian at zero and the quantitative gradient
estimates of Lemma 16.1 are still unfinished, as are the remaining
assertions of Theorem 14.1 and later chapters.

## Section 16 progress: the free Jacobian is the Fourier transform

Section 16's identity at zero is proved for the actual sequence-valued
Birkhoff map at every finite exponent `1 < p < ∞`. The theorem
`SourceBirkhoffMapComplexData.jacobian_zero` identifies its full bounded
complex derivative with the explicit operator `sourceBirkhoffFourier`.
For arbitrary complex source directions `h`, its coordinates are

`dxₙ(0)h = −(h.fst(−n) + h.snd(n))/√2`,
`dyₙ(0)h = (h.fst(−n) − h.snd(n))/(√2 i)`.

The frequency reflection comes from the signed source convention.
`ClassicalFreePotentialGradients.lean` computes the actual free
characteristic, anti-discriminant, and discriminant gradients.
`SourceFreePotentialCotangents.lean` integrates against finite Fourier
inputs and uses density to identify the full Hilbert cotangents.
`SourceFreeSpectralDifferentials.lean` obtains the boundary-root,
periodic-midpoint, and moving-terminal derivatives; in particular the
free discriminant and periodic midpoints have zero first derivative.

`SourceBirkhoffFreeDifferential.lean` combines these results with the
closed-gap differential. At zero the normalized action root is one,
the beta correction is zero, and the gap-weighted coordinate vanishes.
The product rule therefore leaves just the gap-weighted differential.
`SourceBirkhoffFourier.lean` constructs the bounded Fourier operator and
transfers the Hilbert identity to smaller exponents by restriction and
to larger exponents by finite Fourier density. The result uses each
map's own angular family and applies to all complex directions.

Public checks cover bounded-operator equality at `p = 3/2`, both
coordinate formulas at `p = 3`, a single reflected Fourier mode, and
the signed moving-terminal derivative. Theorem 15.2 and Lemma 15.3
remain complete. Next are the quantitative finite-gap gradient estimates
of Lemma 16.1. Those estimates, the remaining assertions of Theorem 14.1,
and later chapters are unfinished.

## Section 16 progress: finite-gap sources and adapted closing coordinates

The spectral prerequisite for the regularity step in Lemma 16.1 is now
proved: a real source is finite-gap if and only if both actual
resonant off-diagonal coefficients vanish at the moving diagonal centers
outside a finite set. This holds at every finite exponent above one.

`ResonantDoubleRootClosing.lean` proves the double-root criterion from
Cauchy derivative bounds. The diagonal derivative has norm at most
`1/8`, and each off-diagonal derivative at most `1/4`. Equal norms of
the two off-diagonal values, together with a double determinant zero,
force both values and the diagonal residual to vanish.

`SourceClosedGapCenter.lean` instantiates this criterion using the
actual resonant coefficients. Canonical endpoint labeling and the
original spectral equivalence give determinant order two at a distant
collapsed gap. Real type supplies the conjugation identity, hence equal
off-diagonal norms. Uniqueness of the diagonal equation identifies the
collapsed endpoint with the named moving center.

`SourceFiniteGapAdaptedCoordinates.lean` combines this converse with
the existing closing implication to characterize the spectral finite-gap
locus. It further proves that, for every sufficiently large cutoff `M`,
`sourceAdaptedClosingMap hp φ M` is exactly the Fourier truncation of `φ`
to indices `−M < n < M`. Only the adapted image is finitely supported;
no finite Fourier support assumption is imposed on the original source.

Public checks cover the characterization at `p = 3`, the exact adapted
truncation identity at `p = 3/2`, and the double-root derivative criterion.
The next step is to recover `H¹` regularity through weighted adapted
inverse estimates, then prove the spectral gradient estimates needed
for Lemma 16.1. That regularity statement and the quantitative estimates
are not yet complete. The remaining assertions of Theorem 14.1 and later
chapters are also unfinished.

## Section 16 progress: quantitative Fourier-tail decay at finite-gap sources

Every real finite-gap source at every finite exponent `1 < p < ∞`
now has a proved geometric bound along quadrupled Fourier cutoffs.
Writing `α = min(1, p−1)`, for every rate `4^(−α) < q < 1` there are
`M > 0` and `C ≥ 0` such that

`‖sourceFourierTail (4^k M) φ‖^p ≤ C q^k` for every natural `k`.

The geometric variable is the cutoff level `k`, not the individual
Fourier frequency. This result is a quantitative decay step toward
Sobolev regularity; it does not yet assert `H¹` membership.

`SourceFourierTail.lean` constructs the tail in the original source
norm, proves convergence to zero and norm monotonicity, and establishes
that physical cutoff `2N` corresponds isometrically to source cutoff `N`.
`SourceFiniteGapTailRecurrence.lean` identifies the actual spectral-center
remainder with the negative source tail at all sufficiently large
cutoffs. It then specializes the established off-diagonal estimate to
obtain the exact recurrence

`T(4N)^p ≤ K ‖φ‖^p (‖φ‖^(2p)/(4N)^α + T(N)^(2p))`,

where `T(N) = ‖sourceFourierTail N φ‖` and
`K = offDiagonalSummationConstant p`. All source and physical cutoff
factors are retained. `QuadraticTailBootstrap.lean` proves that a
vanishing nonnegative tail satisfying this recurrence has the stated
decay, without an initial quantitative rate. The source theorem
constructs a strictly contracting rate as well as the constants.

Public checks cover the exact cutoff norm identity at `p = 3`, the
concrete rate `q = 1/2` at `p = 3`, and a constructed rate below two
at `p = 3/2`. Next convert these bounds to positive weighted Fourier
regularity and iterate the weighted argument to reach `H¹`. The
regularity conclusion, the spectral gradient estimates of Appendix
G.6–G.7, Lemma 16.1, remaining assertions of Theorem 14.1, and later
chapters are unfinished.

## Positive weighted regularity of finite-gap sources

Every real spectral finite-gap source at every finite exponent
`1 < p < ∞` now has positive Sobolev-weighted Fourier regularity.
More precisely, for every `s ≥ 0` satisfying

`s*p < min(1, p−1)`,

both original source components belong to the coefficient space with
weight `(1 + |n|)^s`. The theorem constructs a positive admissible
exponent, `s = min(1, p−1)/(2p)`, without an initial regularity or finite
Fourier support assumption.

`GeometricTailRegularity.lean` proves the general summability step:
a bound `‖tail(4^k M) a‖^p ≤ C q^k` implies weighted membership whenever
`4^(s*p) q < 1`. The proof sums nonnegative tails over geometric cutoffs;
it does not lose a power by estimating coefficients individually.
`SourceFiniteGapRegularity.lean` selects a compatible decay rate and
applies this result to both components of the actual finite-gap source.

Public checks cover the concrete weight `s = 1/4` at `p = 3` and
`p = 3/2`, together with existence of a positive weight at every finite
exponent above one. Next establish and iterate the weighted spectral
bootstrap to reach `H¹`. That conclusion, the gradient estimates of
Appendix G.6–G.7, Lemma 16.1, remaining assertions of Theorem 14.1,
and later chapters are unfinished.

## All Sobolev weights and H¹ for finite-gap sources

Every real spectral finite-gap source at every finite exponent
`1 < p < ∞` now has every nonnegative Sobolev weight at its original
exponent. In particular, both one-derivative source coefficient
sequences are in `ℓ²`: the `H¹` regularity prerequisite for Lemma 16.1
is proved, without a finite Fourier support or initial regularity
hypothesis.

`WeightedResonantCenterForget.lean` identifies the actual distant
moving centers and both closing equations after forgetting a spectral
weight. `SourceFiniteGapWeightedClosing.lean` uses this to identify the
weighted remainder with the negative leading Fourier tail.
`WeightedEvenLeadingTail.lean` proves equality of the leading-tail and
physical Fourier-tail norms for even physical support, with physical
cutoff `2N` for resonance cutoff `N`.

`SourceFiniteGapWeightedTail.lean` obtains the same quadratic recurrence
and geometric decay in every available spectral weight.
`SourceFiniteGapWeightedRegularity.lean` adds any nonnegative Sobolev
gain `t` satisfying `t*p < min(1,p−1)`. The gain range is independent
of the existing weight. `SourceFiniteGapSobolev.lean` iterates the fixed
positive gain `min(1,p−1)/(2p)`, preserves the original coefficients at
each step, and uses monotonicity to reach every nonnegative real weight.
Sampling the even physical frequencies recovers the original source.
The one-derivative embedding then converts the weight-two `ℓp` result
into weight-one `ℓ¹`, hence weight-one `ℓ²` and `H¹`.

Public checks cover `H¹` at `p = 3` and `p = 3/2`, weight five at
`p = 3`, and the geometric bound with its exact doubled physical cutoff
in an arbitrary available spectral weight. Next prove the quantitative
spectral gradient estimates of Appendix G.6–G.7 and use them in Lemma
16.1. Those estimates, Lemma 16.1 itself, remaining assertions of
Theorem 14.1, and later chapters are unfinished.

## Appendix G first-iterate identity and decay

The next Appendix G step now identifies and bounds the first
oscillatory correction in the actual classical fundamental solution.
For an absolutely continuous potential with integrable component
derivatives, the first Born vector satisfies

`exp(-|Im z| t) ‖F(t,z)v‖ ≤ B(t) ‖v‖ / (2‖z‖)` for `z ≠ 0` and `t ≥ 0`,

where `B(t)` is the maximum of the two component budgets
`|f(0)| + |f(t)| + ∫₀ᵗ |f′(s)| ds`. On the unit interval it is bounded
by the spectral-parameter-independent budget
`2‖φ‖∞ + max(∫₀¹ |φ₁′|, ∫₀¹ |φ₂′|)`.

`OscillatoryIntegralParts.lean` proves complex integration by parts
for the kernel `exp(c(t−2s))`, retaining both endpoint terms and the
factor two. It proves the kernel norm bound, the inverse-frequency
estimate, and its exponential normalization without assuming a smooth
potential. `ClassicalFirstBorn.lean` defines the free vector and the
remainder of the constructed classical solution, and derives the two
actual Duhamel equations for that remainder. Each consists of the
first Born vector plus the free propagator acting on the opposite
remainder component, with the original potential signs.
`ClassicalFirstBornBound.lean` applies the scalar estimate and proves
the bound uniform in time on `[0,1]`.

Public checks cover a constant amplitude's exact integral, including
both signs and `2c` in the denominator; the actual free remainder;
and the uniform normalized bound for a fundamental column. Next
control the full remainder by this first-iterate forcing and translate
the budgets into Sobolev bounds. This is the integration-by-parts part
of G.2; the full G.1–G.3 estimates, G.4–G.7, Lemma 16.1, remaining
assertions of Theorem 14.1, and later chapters are unfinished. The
previously proved finite-gap `H¹` and all-weight regularity remain
available for the spectral-gradient argument.

## Appendix G full remainder decay and time-derivative bound

The full classical fundamental-solution error now inherits the first
Born vector's inverse-frequency decay. For an absolutely continuous
potential with integrable component derivatives, every initial vector
`v`, every nonzero complex `z`, and every `t ∈ [0,1]`, Lean proves

`exp(-|Im z| t) ‖R(t,z)v‖ ≤ B ‖v‖ exp(‖φ‖∞) / (2‖z‖)`,

`exp(-|Im z| t) ‖∂ₜR(t,z)v‖ ≤ (B/2 + ‖φ‖∞) ‖v‖ exp(‖φ‖∞)`,

where `R` is the constructed solution minus its free solution and
`B = 2‖φ‖∞ + max(∫₀¹ |φ₁′|, ∫₀¹ |φ₂′|)`. In particular, these
bounds apply to both fundamental matrix columns without any smallness
assumption on the potential.

`NormalizedDuhamelBound.lean` transfers the exponential normalization
through the free propagator. `IntegralGronwall.lean` closes the resulting
integral inequality, including zero forcing and zero coupling.
`ClassicalRemainderBound.lean` applies these results to the actual two
remainder equations. `ClassicalRemainderDerivativeBound.lean` subtracts
the free ODE and cancels the spectral factor against the remainder's
decay to obtain the uniform time-derivative bound.

Public checks cover zero forcing with arbitrary nonnegative coupling,
the full error of one fundamental column, and the time derivative of
the other. These are the pointwise bounds needed before Appendix G.3
interpolation. The precise Sobolev budget comparison, the sharper G.1
integral estimate, the Fourier–Lebesgue estimates G.3–G.7, Lemma 16.1,
remaining assertions of Theorem 14.1, and later chapters remain
unfinished. Next connect these bounds to the proved finite-gap Sobolev
regularity and establish the Fourier–Lebesgue interpolation estimates.

## Appendix G fundamental-solution bounds on Sobolev balls

The Appendix G error estimates now apply directly to potentials
constructed from physical period-two `H¹` Fourier coefficient pairs.
Absolute continuity and integrability of the actual component derivatives
are proved from the coefficients; they are no longer extra premises.

For the maximum weighted Hilbert norm `‖a‖ ≤ M`, Lean proves the
supremum bound `‖φ‖∞ ≤ 4M` and the variation-budget bound
`B ≤ (8 + 2π)M`. Consequently, for `z ≠ 0`, `|Im z| ≤ H`, and
`t ∈ [0,1]`, the actual solution error satisfies

`‖R(t,z)v‖ ≤ (4 + π) M ‖v‖ exp(4M + H) / ‖z‖`,

`‖∂ₜR(t,z)v‖ ≤ (8 + π) M ‖v‖ exp(4M + H)`.

These constants are uniform on each coefficient `H¹` ball and each
horizontal spectral strip. They use the project's period-two Fourier
normalization and are not a claim of the exact numerical constants
printed in G.2.

`SobolevUnitCurve.lean` restricts the continuous Fourier representative
to the ODE interval, identifies its extended derivative almost
everywhere, and bounds its derivative integral using the physical
Fourier derivative. `ClassicalSobolevPotential.lean` constructs both
potential components and controls the first Born budget.
`ClassicalSobolevRemainderBound.lean` discharges the regularity premises
and proves normalized, ball-uniform, and unweighted strip estimates.
Public checks cover constant modes, derivative integrability, and
both fundamental columns on a fixed Sobolev ball and strip.

Next establish the time-norm and Fourier–Lebesgue interpolation estimates
of G.3 and connect the resulting gradient estimates to finite-gap sources.
The sharper integral estimate in G.1, the remaining G.3–G.7 estimates,
Lemma 16.1, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Appendix G.3 time norms along near-free spectral sequences

The two time-norm bounds used before interpolation in Appendix G.3
are now proved for the actual remainder. For physical period-two `H¹`
coefficient potentials, `‖a‖ ≤ M`, and spectral sequences satisfying
`‖νₙ − nπ‖ ≤ B` outside an initial finite set, one positive cutoff gives

`‖Fourier₍[0,1]₎(L R(νₙ)v)‖ℓ² ≤ (2 C(M,B) ‖v‖ / π) / |n|`,

`‖L R(νₙ)v‖H¹[0,1] ≤ (C(M,B) + D(M,B)) ‖v‖`,

where `C(M,B) = (4+π) M exp(4M+B)` and
`D(M,B) = (8+π) M exp(4M+B)`. Here `L` is any contractive
real-linear scalar observation of a column. Coordinate projections
therefore give all fundamental matrix entries. The cutoff is uniform
over the potential ball and every sequence with the given displacement
bound. The Fourier norm is the norm of the whole actual coefficient
sequence, with unit-interval frequencies `2πn` and no endpoint-matching
assumption. The physical `L²` square energy also has an explicit
inverse-frequency-squared bound.

`UnitIntervalEnergyBound.lean` proves the physical square-energy and
classical `H¹` bounds and applies Parseval after interval dilation.
`ClassicalRemainderTimeRegularity.lean` proves continuous time
differentiability and differentiation of bounded linear observations.
`ClassicalSobolevRemainderTimeBounds.lean` constructs the coefficient
sequences and bounds their norms. `ClassicalSobolevRemainderSequenceBounds.lean`
turns bounded displacement from `nπ` into a common strip, frequency
lower bound, and sequence cutoff.

Public checks cover the constant Fourier coefficient, Parseval for
nonmatching endpoints, the `H¹` norm of a matrix entry, and inverse-index
decay along the complex shifted lattice `nπ+i`. Next prove the
Fourier–Lebesgue endpoint bound and interpolation for general `q>1`,
then the shifted-free and gradient estimates in G.3–G.7. Those steps,
the sharper integral estimate in G.1, Lemma 16.1, remaining assertions
of Theorem 14.1, and later chapters remain unfinished.

## Appendix G.3 uniform Fourier–Lebesgue endpoint

The actual fundamental-solution remainder now has a uniform
Fourier–Lebesgue bound at every exponent `q > 1`, including infinity.
For physical period-two `H¹` coefficient potentials with `‖a‖ ≤ M`,
`|Im z| ≤ H`, and `|z| ≥ 1`, Lean proves

`‖Fourier₍[0,1]₎(L R(z)v)‖ℓq ≤ (2 C(M,H) + D(M,H)) ‖v‖ Kq`,

where `C` and `D` are the previously proved error and derivative
constants, and `Kq = ‖((1+|k|)⁻¹)ₖ‖ℓq`. The bound is uniform in the real spectral
frequency and over the entire Sobolev ball. Bounded displacement
`νₙ=nπ+O(1)` gives a common cutoff for the whole family of sequences.
At `q=2`, the new sequence is proved equal to the existing Parseval
sequence with `O(1/|n|)` decay.

`UnitIntervalCoefficientDecay.lean` identifies the actual unit Fourier
integral with the oscillatory integral, removes its constant phase,
and proves integration-by-parts decay with both endpoint terms.
For a `C¹` function with value bound `A` and derivative bound `D`, it
proves `|f̂(k)| ≤ (2A+D)/(1+|k|)`, including the zero frequency and
without endpoint matching. `UnitIntervalC1FourierLebesgue.lean`
uses the inverse bracket's `ℓq` membership to construct the actual
coefficient sequence and bound its full norm. The constant depends
only on the target exponent.
`ClassicalSobolevRemainderFourierBound.lean` applies this estimate to
all contractive scalar observations of fundamental columns.

Public checks cover nonperiodic data below exponent two, the zero-safe
coefficient bound, uniform control at `q=3/2`, equality with Parseval
at `q=2`, and the infinity exponent. This proves the uniform endpoint
needed before G.3 interpolation; decay at general finite `q` is still
to be proved. Next interpolate the uniform bound near exponent one
with the decaying `ℓ²` bound, then prove the shifted-free comparison
and gradient estimates. Those remaining G.3–G.7 steps, the sharper
integral estimate in G.1, Lemma 16.1, remaining assertions of Theorem
14.1, and later chapters remain unfinished.

## Appendix G.3 Fourier–Lebesgue decay by interpolation

The Fourier–Lebesgue decay for the actual remainder in Appendix G.3
is now proved with the displayed exponent. For `0 < ε < 1` and
`1+ε ≤ q ≤ 2`, potentials in a fixed physical period-two `H¹`
coefficient ball, and sequences `νₙ=nπ+O(1)`, Lean proves

`‖Fourier₍[0,1]₎(L R(νₙ)v)‖ℓq ≤ K(ε,M,B) ‖v‖ / |n|^((q−1−ε)/(1−ε))`

beyond one common cutoff. Here `B` bounds the spectral displacement,
`M` bounds the potential coefficient norm, and `L` is any contractive
scalar observation of a fundamental column. The constant is independent
of the target exponent within `[1+ε,2]` and uniform on the whole
Sobolev ball. The finite initial part of the sequence is unrestricted.
Both exponent endpoints and zero input vectors are included.

`NormInterpolation.lean` proves the quantitative sequence-norm
interpolation inequality by Hölder on powers of the same coefficients,
then transfers an inverse-scale endpoint bound into fractional decay.
`ClassicalSobolevRemainderInterpolation.lean` combines the actual
uniform `ℓ^(1+ε)` and decaying `ℓ²` estimates. Its common constant is
`K = (2C+D) K_(1+ε) + C`, using the preceding error, derivative, and
inverse-bracket constants. `ClassicalSobolevRemainderFourierDecay.lean`
uses the near-free frequency cutoff to replace spectral frequency
by the absolute integer index.

Public checks cover zero-bound interpolation, both target-exponent
endpoints, the explicit `ε=1/4, q=3/2` inverse-cube-root bound, and
that bound along `nπ+i`. Together with the earlier time-norm result,
this proves G.3's remainder estimates for the constructed Sobolev
potentials. The shifted-free comparison in the final part of G.3,
G.4–G.7, the sharper integral estimate in G.1, Lemma 16.1, remaining
assertions of Theorem 14.1, and later chapters remain unfinished.
Next prove the comparison with the free solution at `nπ` when the
spectral displacement is `O(1/|n|)`.

## Appendix G.3 shifted-free comparison

The final shifted-free comparison in Appendix G.3 is now proved for
physical period-two `H¹` coefficient potentials. For `0 < ε < 1`,
`1+ε ≤ q ≤ 2`, and `νₙ=nπ+O(1/|n|)`, Lean proves

`‖Fourier₍[0,1]₎(L (S(νₙ)v − E(nπ)v))‖ℓq ≤ K(ε,M,B) ‖v‖ / |n|^((q−1−ε)/(1−ε))`.

The actual Fourier integrals compare the constructed solution at `νₙ`
with the free solution at `nπ`. The constant and cutoff are uniform on
`H¹` coefficient balls and under a common inverse-index displacement
bound. Both exponent endpoints are included; the finite initial part
of each spectral sequence is unrestricted.

`ClassicalFreeFrequencyDifference.lean` bounds the free difference by
`2|z−x|‖v‖` and its derivative by `(2|z|+1)|z−x|‖v‖` for real `x`
and `|z−x|≤1`. `ClassicalShiftedFreeRemainder.lean` adds this to the
actual remainder, giving `O(1/|n|)` values and uniformly bounded time
derivatives. `UnitIntervalC1Interpolation.lean` provides reusable
Fourier interpolation for any `C¹` interval function with those bounds.
`ClassicalShiftedFreeFourierDecay.lean` applies it to the combined error
and proves the common sequence cutoff.

Public checks verify the actual Fourier-integral identity, recovery of
the earlier remainder at equal frequencies, the zero free difference,
the explicit inverse-cube-root bound at `ε=1/4, q=3/2`, and a uniform
cutoff along the nonreal sequence `nπ+i/|n|`.

Together with the preceding remainder bounds, this completes the G.3
estimates for the constructed Sobolev potentials. Next prove the
outer-index summability in G.4, then G.5–G.7's gradient estimates and
their application to finite-gap sources in Lemma 16.1. The sharper
integral estimate in G.1, remaining Appendix G estimates, Lemma 16.1,
remaining assertions of Theorem 14.1, and later chapters remain unfinished.

## Appendix G.4 Fourier-norm summability

Corollary G.4 is now proved for the constructed physical period-two
`H¹` potentials. For every finite real `p>1` and Fourier exponent
`q>1+1/p`, including `q=∞`, the norms of the actual unit-interval
Fourier coefficient sequences belong to outer `ℓp`:

- the solution remainder along `νₙ=nπ+O(1)`;
- the solution minus the free evolution at `nπ` when
  `νₙ=nπ+O(1/|n|)`.

The first assertion allows any common bounded displacement, hence
includes the dissertation's eventual `π/4` condition. For each fixed
spectral sequence, one `ℓp` majorant controls all indices, all potentials
in a fixed `H¹` coefficient ball, and all contractive scalar observations
of fundamental columns, with linear dependence on the initial vector
norm. The finite spectral head is arbitrary and may include zero.
A common tail majorant and cutoff also work across all spectral
sequences with the same eventual displacement bound and starting index.

`PowerDecaySummability.lean` proves two-sided power summability and
allows finite exceptions. `FundamentalFourierSummabilityExponents.lean`
chooses a positive interpolation parameter with decay exponent `α`
satisfying `αp>1`. `UnitIntervalFourierExponentEmbedding.lean` extends
the actual-coefficient norm bound to larger Fourier exponents, including
infinity. `ClassicalFourierTailSummability.lean` applies these results
to both G.3 errors. `ClassicalFourierBoundAllFrequencies.lean` supplies
coarse value and derivative bounds at every spectral frequency;
`ClassicalFourierSequenceSummability.lean` joins the finite head with
the summable tail and proves whole-sequence membership and uniformity.

Public checks cover inverse-index powers at zero and negative indices,
outer `ℓ³` membership of `ℓ^(3/2)` remainder norms, an arbitrary
exceptional spectral value at zero with a uniform ball bound, outer
exponents below two with Fourier exponents above two, and the infinity
Fourier exponent for the shifted-free error.

Next prove the fundamental-solution gradient estimate G.5, followed by
G.6–G.7 and their application to finite-gap sources in Lemma 16.1.
The sharper integral estimate in G.1, remaining Appendix G estimates,
Lemma 16.1, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Appendix G.5 Hilbert gradient summability

Both assertions of G.5 are now proved at the Hilbert exponent `p=2`
for the constructed physical period-two `H¹` potentials. The actual
endpoint-gradient error has an `ℓ²` sequence of unit-interval Fourier
`ℓ²` norms, comparing with the free gradient at `νₙ` under bounded
spectral displacement, or at `nπ` under `O(1/|n|)` displacement.
For each fixed spectral sequence, a single square-summable majorant
controls every potential in a fixed coefficient ball, every unit initial
vector, every contractive complex endpoint functional, and every
contractive scalar observation of the potential-gradient pair.
All indices are included, with arbitrary finite spectral heads and zero
frequencies allowed. Matrix entries are obtained from the basis vectors
and coordinate projections.

`EndpointGradientPolynomial.lean` isolates the actual cubic gradient
expression in five solution values, including the terminal columns.
When both sets of values have norm at most `E` and differ by at most
`D`, their gradient expressions differ by at most `6 E² D`.
`ClassicalEndpointGradientRemainder.lean` identifies this polynomial
with the existing actual gradient, constructs its free reference, proves
agreement at zero potential, and proves time `C¹` regularity.
`ClassicalEndpointGradientBounds.lean` gives inverse-frequency and
inverse-index pointwise bounds for both reference choices, uniformly
on Sobolev balls and spectral strips.

`ClassicalEndpointGradientL2.lean` constructs the actual Fourier
coefficients and transfers the pointwise bound by Parseval, also proving
a coarse all-frequency bound for finite heads.
`ClassicalEndpointGradientHilbertSummability.lean` constructs the
whole-sequence square-summable majorants and proves membership.
`ClassicalEndpointGradientErrorIntegral.lean` proves that integrating
the error gives the actual difference of endpoint potential derivatives;
it also verifies the free upper off-diagonal gradient and its sign.

Public checks cover the derivative identity, actual Fourier-integral
identity, free-reference sign, square summability along `nπ+i` and
`nπ+i/|n|`, and a uniform ball bound with an arbitrary exceptional
spectral value at zero.

Next extend the Fourier estimate to the conjugate exponents needed
for finite `p>2`. The printed `p=∞` endpoint needs a separate argument:
the proof chooses an exponent below `p′`, which is unavailable at
`p′=1`. This is a proof-gap observation, not a formal counterexample.
G.5 beyond its Hilbert case, G.6–G.7, the sharper integral estimate in
G.1, Lemma 16.1, remaining assertions of Theorem 14.1, and later
chapters remain unfinished.

## Appendix G.5 finite-exponent gradient summability

Both assertions of G.5 are now proved throughout the finite exponent
range for the constructed physical period-two `H¹` potentials. The
actual gradient-error Fourier norms belong to outer `ℓp` whenever
`1<p<∞` and `q>1+1/p`. Since `p′=p/(p−1)>1+1/p`, this includes
the dissertation's conjugate Fourier exponent for every finite `p≥2`,
and also extends that conclusion to finite `1<p<2`.

The two errors compare the actual potential gradient with its free
reference at `νₙ` under `νₙ=nπ+O(1)`, or at `nπ` under
`νₙ=nπ+O(1/|n|)`. For each fixed spectral sequence, one summable
majorant controls the whole Sobolev ball, all unit initial vectors,
all contractive endpoint functionals, and all contractive scalar
observations of the gradient pair. Arbitrary finite spectral heads,
including zero frequencies, remain included. The coefficient sequences
are the actual unit-interval Fourier integrals and agree with the
previous Hilbert construction at `q=2`.

`ClassicalEndpointGradientDerivative.lean` proves the exact time
equation. Its spectral term multiplies the small gradient error; the
other terms involve the reference-frequency difference and a mixed
solution/dual-solution product. `ClassicalEndpointGradientDerivativeBound.lean`
bounds that mixed product uniformly. `ClassicalSobolevGradientDerivativeBounds.lean`
cancels spectral growth against inverse-frequency value decay to obtain
uniform time-derivative bounds for both reference choices, plus coarse
all-frequency bounds for finite heads.

`ClassicalEndpointGradientFourierInterpolation.lean` applies the
existing C¹ Fourier interpolation to these actual error functions.
`ClassicalGradientFourierSummability.lean` constructs common
whole-sequence majorants, and `ClassicalEndpointGradientFiniteSummability.lean`
proves both uniform estimates, their sequence-membership conclusions,
and the explicit conjugate-exponent corollaries.

Public checks cover agreement at exponent two, the strip-uniform
derivative bound, the strict conjugate-exponent threshold, G.5 at
`p=3` and `p=4`, a uniform ball bound with an arbitrary exceptional
frequency, and the broader theorem's infinity Fourier exponent `q`.
This last case still has finite outer exponent `p`.

The printed outer endpoint `p=∞` has `p′=1` and is not proved here.
Its printed auxiliary-exponent argument does not apply at that endpoint;
a separate audit remains. Next resolve that endpoint question, then
prove G.6–G.7 and their finite-gap application in Lemma 16.1. The
sharper G.1 integral bound, G.5's infinite outer endpoint, G.6–G.7,
Lemma 16.1, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Appendix G.5 infinite-endpoint counterexample

The printed outer endpoint `p=∞` of G.5 is false for actual unit-interval
Fourier coefficients. Lean now proves a counterexample to both assertions,
including on every tail. This does not affect the proved finite-exponent
range `1<p<∞`, `q>1+1/p`, or its conjugate-exponent corollaries.

`AbsoluteSummabilityEndpoints.lean` proves that a continuous function with
absolutely summable Fourier coefficients on a positive interval must have
matching endpoint values. The proof uses uniform continuous synthesis and
L² Fourier uniqueness, then continuity at both endpoints.

`ClassicalTriangularPotential.lean` constructs the constant potential
`φ=(1,0)` from its explicit zero-mode physical H¹ coefficient pair. ODE
uniqueness identifies its second solution column as
`((exp(izt)−exp(−izt))/(2z), exp(izt))` for `z≠0`. Its upper monodromy
coupling is nonzero whenever `Im z≠0`, because the two exponentials have
different norms.

`ClassicalEndpointGradientEndpointObstruction.lean` proves that the second
component of the gradient of the upper diagonal monodromy entry has values
`−i M₀₁(z)` at zero and `0` at one. The corresponding free gradient is zero
at every reference frequency. A nonzero upper coupling therefore prevents
the actual gradient error from belonging to Fourier ℓ¹.

`ClassicalGradientInfinityCounterexample.lean` takes
`νₙ=nπ+i/(2(|n|+1))`. Its displacement is at most `π/4` at every index and
at most `1/(2|n|)` away from zero, so both printed frequency hypotheses
hold. Every frequency is nonreal. The actual H¹ gradient error fails
Fourier ℓ¹ membership at every index, for any free reference sequence;
in particular, both references `νₙ` and `nπ` fail on every tail. Thus the
printed `p=∞`, `p′=1` endpoint cannot be added to the finite-p result.

Public checks cover arbitrary positive interval lengths, a linear function
with a boundary jump, both frequency bounds, and failure on every tail for
each of G.5's two free references. No endpoint-matching assumption or
unproved regularity is supplied for the counterexample.

Next prove G.6–G.7 in their valid ranges and apply them to finite-gap
sources in Lemma 16.1. The sharper G.1 integral bound, G.6–G.7, Lemma 16.1,
remaining assertions of Theorem 14.1, and later chapters remain unfinished.

## Appendix G.6 characteristic-gradient summability

Both assertions of G.6 are now proved for constructed physical H¹
potentials throughout the printed finite range `2≤p<∞`. The actual
discriminant-gradient Fourier norms form an outer ℓp sequence for
`νₙ=nπ+O(1)`. The anti-discriminant gradient minus its free lattice
reference has the same summability when `νₙ=nπ+O(1/|n|)`.

The results use the stronger G.5 threshold `q>1+1/p` for every finite
`p>1`, and hence include `q=p′=p/(p−1)`. Each estimate has a common
whole-sequence majorant on every physical H¹ ball, simultaneously for
all contractive scalar observations. Explicit corollaries sum the norms
of both physical components, so the conclusion is not restricted to
one component. Arbitrary finite spectral heads are retained.

`ClassicalCharacteristicGradientRemainders.lean` identifies the actual
monodromy-trace gradient with the sum of its two diagonal endpoint
gradients. Both free diagonal terms vanish identically. The actual
anti-discriminant is the original off-diagonal monodromy sum, and its
gradient error is the sum of the two off-diagonal endpoint errors.
The lattice reference is proved to be
`(i(−1)^n wave(2n), −i(−1)^n wave(−2n))`. A separate identity checks
multiplication by i against the dissertation's exact component signs.

`IntervalCoefficientLinearity.lean` supplies additivity and interval-local
dependence of actual Fourier integrals. `ClassicalCharacteristicGradientFourier.lean`
uses these facts to identify the coefficient-space sums with the actual
discriminant gradient and anti-discriminant gradient error, including
explicit signed wave subtraction at the free lattice.
`ClassicalCharacteristicGradientSummability.lean` transfers the common
G.5 majorants, proves membership for all exponents above the threshold,
and specializes to the conjugate exponent and both-component norm sum.
These gradients already represent the actual potential derivatives by
the previously proved physical integral formulas.

Public checks cover an actual discriminant Fourier integral, the exact
factor i and lattice signs, both-component summability at `p=3` and
`p=4`, and a whole-ball bound with an arbitrary central frequency.
G.5's refuted infinite endpoint is not used; G.6 itself states finite p.

Next prove G.7's midpoint and Dirichlet-eigenvalue gradient estimates,
then apply the Appendix G bounds in Lemma 16.1. The sharper G.1 integral
bound, G.7, Lemma 16.1, remaining assertions of Theorem 14.1, and later
chapters remain unfinished.

## Appendix G.7 preparation: summable spectral-disc suprema

The spectral supremum required in G.7 now has a formal summability
proof. For any fixed radius `B≥0`, one outer ℓp majorant bounds the actual
discriminant-gradient Fourier norm at every point of every closed disc
`|z−nπ|≤B`, simultaneously over the whole physical H¹ ball and every
contractive scalar observation. The bound is chosen before all spectral
points. In particular it controls every point on G.7's circles of radius
`π/4`, not just one selected point per index.

`ClassicalGradientFourierPowerBound.lean` extracts one nonnegative
constant K and exponent α with `αp>1` from the time-value and derivative
bounds. The estimate `K d^(−α)` applies to every actual endpoint gradient
error satisfying those bounds, independently of the spectral frequencies.
`ClassicalGradientSpectralDiscBounds.lean` applies it uniformly over each
disc. One cutoff gives the required strip and inverse-frequency estimates;
an explicit bound using `|z|≤π|n|+B` controls all remaining finite indices.
The resulting whole-sequence majorant covers every potential, unit initial
vector, contractive endpoint functional, and contractive observation.

`ClassicalDiscriminantGradientDiscSup.lean` transfers that majorant to
the actual trace gradient and defines the real supremum of its Fourier
norm over the closed disc. The supremum set is proved nonempty and bounded
above. Its actual supremum is nonnegative, shares the common bound over
each H¹ ball, and forms an outer ℓp sequence whenever `1<p<∞` and
`q>1+1/p`, including the conjugate Fourier exponent `q=p/(p−1)`.
No assumed coefficient-space continuity or supplied supremum bound is used.

Public checks verify simultaneous control of every point on every
radius-`π/4` circle, actual disc-supremum summability at `p=3`, zero-radius
discs at `p=4`, and the whole-ball supremum bound for all observations.

This completes the spectral-uniform estimate needed before G.7's contour
argument. G.7 itself remains unfinished: the midpoint gradient contour
representation, its discriminant quotient bound, and the Dirichlet
normalization estimate must still be connected to the actual indexed
coordinates. Lemma 16.1, the sharper G.1 integral bound, remaining assertions
of Theorem 14.1, and later chapters also remain unfinished.

## Appendix G.7 preparation: contour quotient and integrand bounds

The quotient needed for G.7's midpoint contour estimate is now bounded
uniformly over physical H¹ balls and every sufficiently distant contour.
For any fixed radius `0<r≤π/2`, one cutoff and positive constant δ give
`δ≤|Δ(z)²−4|` on every circle `|z−nπ|=r`. The same construction supplies
one bound on `|Δ(z)/(Δ(z)²−4)|`. In particular, the actual denominator
has no zeros on G.7's distant radius-`π/4` circles; this is proved rather
than assumed.

`FreeCircleSeparation.lean` proves separation from every free lattice
center and the horizontal-strip bound on these circles.
`ClassicalSobolevDiscriminantError.lean` identifies the trace error with
the two diagonal solution errors and proves the uniform bound
`|Δ(z)−2cos(z)|≤2 C(M,r)/|z|`. `ClassicalSobolevContourQuotient.lean`
combines that decay with the existing uniform inverse bounds for the
free factors `2cos(z)−2` and `2cos(z)+2`. After one common cutoff, both
perturbed factors retain positive lower bounds. Their product bounds
`Δ²−4` away from zero, and the strip growth bound controls the numerator.

`ClassicalContourGradientIntegrandBound.lean` multiplies the actual
discriminant-gradient Fourier coefficients by the spectral quotient.
A coefficient identity verifies the literal physical Fourier integral
of `Δ/(Δ²−4)` times the gradient observation. Combining the quotient
bound with the previously proved spectral-disc majorant gives one outer
ℓp majorant for the full integrand, simultaneously at every point of
every distant contour, throughout the H¹ ball, and for every contractive
scalar observation. This holds for finite `p>1` and `q>1+1/p`, covering
the conjugate exponent. Only distant contours are asserted here; no
pole exclusion is claimed for arbitrary finite spectral heads.

Public checks cover quarter-pi separation from all lattice centers,
the quantitative trace error, a positive denominator bound and bounded
quotient on the whole ball, the actual weighted Fourier integral, and
a common outer ℓ³ integrand bound over all distant contour points.

Next establish the actual midpoint gradient contour representation and
pass the verified integrand bound through its integral. G.7's Dirichlet
normalization estimate and the identification with the indexed source
coordinate gradients also remain. G.7, Lemma 16.1, the sharper G.1
integral bound, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Appendix G.7: actual canonical midpoint contour formula

The actual canonical midpoint now satisfies the discriminant contour identity
`dτₙ[h] = −(2πi)⁻¹ ∮ Δ(z) dΔ(z)[h] / (Δ(z)²−4) dz`.
This is proved for every finite source exponent `p>1` on one common open
neighborhood of all real sources. The circular disc must contain both
selected indexed periodic endpoints and avoid every other periodic cut.
The selected endpoints may coincide; no simple-root or open-gap premise
is required. The result also specializes directly to every real source.

`QuadraticFactorVariationContour.lean` proves the underlying residue
calculation for a quadratic factor. The two enclosed poles give the
midpoint variation, while the squared-gap variation integrates to zero,
including at a double root. A nonvanishing analytic factor contributes
zero by Cauchy's theorem.

`SourceMidpointGradientContour.lean` applies this calculation to the
actual canonical discriminant factorization. Joint analyticity of the
omitted standard-root product makes the deleted product and its source
derivative analytic on the disc. Its proved nonvanishing permits division.
Differentiating the exact factorization supplies the linearized identity;
the midpoint derivative is not introduced by defining a contour integral.
Public checks cover the double-root calculation and the actual real-source
coordinate formula at `p=3`.

Next combine the contour formula with uniform isolation of the distant
indexed pairs and transfer the physical Fourier-gradient integrand bounds
through the integral to the source coordinate gradient. The Dirichlet
eigenvalue normalization estimate is still needed for G.7. G.7, Lemma 16.1,
the sharper G.1 integral bound, remaining assertions of Theorem 14.1, and
later chapters remain unfinished.

## Appendix G.7: uniform midpoint operator contours and norm transfer

The midpoint contour formula now applies on one open neighborhood of each
real source at every sufficiently distant signed index. The contours are
the fixed circles `|z−nπ|=π/4`. Both selected endpoints lie inside, and the
actual characteristic function `Δ²−4` is nonzero everywhere on the circle.
These facts are derived from the existing isolating-disc construction;
no isolation or nonvanishing premise is supplied by the caller. Nearby
complex sources and collapsed selected gaps are included.

`SourceMidpointGradientTail.lean` proves that the closure of each isolating
disc avoids all other periodic segments. Disjointness from the other open
discs persists on taking this closure. Intersecting the local isolation
neighborhood with the analytic midpoint neighborhood yields one cutoff
and neighborhood for every distant directional formula.

`SourceMidpointGradientOperatorContour.lean` proves that the source
Fréchet derivative of the discriminant is entire in the spectral parameter
in operator norm. Its quotient-weighted operator integrand is integrable
on every zero-free circle. Evaluation commutes with the contour integral,
so the directional identities recover the entire midpoint derivative as
an operator-valued contour integral. The normalized integral estimate gives
`‖dτₙ‖ ≤ (π/4) B` whenever the operator integrand has norm at most `B`
on that circle, uniformly on the constructed source neighborhood.

At every real source, an outer ℓs majorant for this operator integrand
transfers to an ℓs sequence of actual midpoint derivatives for every
finite `s>0`. The finite central block is unrestricted. This transfer is
conditional on the operator integrand majorant: identification of the
previously proved physical Fourier majorant with a source operator norm
bound remains to be proved. Public checks cover literal operator evaluation,
the common zero-free neighborhood and contour norm bound at `p=3`, and
whole-sequence ℓ³ transfer with arbitrary central indices.

Next identify the physical Fourier-gradient bounds with the actual source
derivative bounds to complete the midpoint estimate, then prove G.7's
Dirichlet normalization estimate. G.7, Lemma 16.1, the sharper G.1 integral
bound, remaining assertions of Theorem 14.1, and later chapters remain
unfinished.

## Appendix G.7: actual midpoint derivative summability at H¹ sources

The physical Fourier-gradient bounds now control the actual source midpoint
derivatives. For every finite source exponent `p≥2`, one open neighborhood
of the entire real source locus has the following property: at each H¹
potential in that neighborhood, the operator norms of the actual indexed
midpoint derivatives form an outer ℓp sequence. This includes nearby complex
potentials and collapsed gaps. The H¹ premise is equality of the source's
physical coefficients with the inclusion of a Sobolev-domain pair; no
contour geometry, derivative formula, or summable majorant is assumed.

`ContinuousSourceDiscriminantGradient.lean` extends the finite-input
comparison to every compatible continuous physical representative. Physical
compatibility is preserved along complex affine source lines, so differentiating
the exact discriminant identity identifies the genuine source and physical
derivatives. Testing the two unit Fourier directions recovers both physical
gradient coefficients at reversed frequency. Exponent compatibility preserves
these identities at every finite source exponent at least two.

`SourceCotangentNormBound.lean` proves that unit Fourier values determine an
actual continuous functional at a finite exponent. Hölder duality then bounds
the source pair operator norm by the sum of its two conjugate coefficient
norms. `SourceMidpointPhysicalFourierBound.lean` applies this to the literal
quotient-weighted discriminant derivative. Frequency reversal is isometric,
and the unit-interval Fourier conventions are identified exactly. The existing
physical H¹-ball estimate therefore supplies a common summable bound for the
actual source operator integrand at every distant contour point.

`SourceMidpointSobolevSummability.lean` supplies the continuous representative
from the physical Sobolev coefficients and combines the operator majorant with
the proved midpoint contours. The choice of conjugate exponent is derived for
every finite `p≥2`. A union of local contour neighborhoods gives the common
open neighborhood of all real sources. The finite central block is unrestricted.
The output is summability of the actual Fréchet derivatives in source operator
norm; no assumed gradient is substituted for the indexed coordinate derivative.

Public checks cover general compatible continuous directions, the physical
ℓ^(3/2) bound for the actual ℓ³ source operator, the real H¹ midpoint derivative
estimate without gradient premises, and its common open complex neighborhood.

Next prove G.7's Dirichlet gradient normalization and shifted-free estimate,
then use the gradient estimates in Lemma 16.1. G.7 as a whole, Lemma 16.1,
the sharper G.1 integral bound, remaining assertions of Theorem 14.1, and
later chapters remain unfinished. No infinite-exponent assertion is added.

## Appendix G.7: Dirichlet normalization and local root derivatives

The exact classical Dirichlet normalization and local eigenvalue derivative
are now proved. With `g=M(·,z)(1,1)` and the bilinear normalization
`Q=2∫₀¹g₁g₂`, every simple Dirichlet zero has `Q≠0`. The actual Fréchet
derivative of a continuous local branch of simple zeros is the integral
against `(g₂²,g₁²)/Q`; differentiability and the gradient formula are derived.

`ClassicalSpectralVariation.lean` differentiates the actual Volterra solution
in the spectral parameter. Its forced source is `(-i u₁,i u₂)`, and the
endpoint derivative is an exact forward/dual solution integral.
`ClassicalDirichletGradientNormalization.lean` identifies the dual solution
at a root as a nonzero multiple of `g`. The spectral and potential derivatives
share this factor, so their implicit-root quotient gives the normalized
squared-eigenfunction expression. Simplicity proves nonzero normalization.

`ClassicalDirichletRootGradient.lean` applies the analytic implicit-root
theorem to a genuine continuous local root selection and then differentiates
the root identity. Its hypotheses explicitly retain local root selection
and simplicity. The canonical indexed source-root instance and the uniform
shifted-free remainder estimate are still to be proved.

Public checks cover `Q(0,z)=2` for every complex `z`, the free gradient
`(exp(2izt)/2,exp(-2izt)/2)`, nonvanishing from simplicity, and the actual
local branch derivative. G.7 as a whole, Lemma 16.1, the sharper G.1 integral
bound, remaining assertions of Theorem 14.1, and later chapters remain
unfinished. No infinite-exponent assertion is added.

## Appendix G.7: canonical source Dirichlet gradients

The normalized squared-eigenfunction formula now describes the actual
canonical source Dirichlet root derivative at every real source with a
compatible continuous physical representative. Every signed index is
included, with no exclusion of the central block or collapsed periodic gaps.
The existing simplicity theorem supplies nonzero normalization; neither
simplicity nor a candidate gradient is an extra assumption in this result.

`ContinuousSourceBoundaryRealization.lean` constructs bounded restriction
of physical Hilbert synthesis to the original unit-interval L² space.
Density identifies the completed source boundary extension with the actual
reflected physical potential. This proves equality of the source and classical
Dirichlet and Neumann characteristics at every compatible continuous
potential, including complex and non-polynomial inputs.

`ContinuousSourceBoundaryGradient.lean` differentiates this equality along
compatible affine directions. Both actual characteristic cotangent coefficients
are the corresponding physical Fourier coefficients at reversed frequency.
`SourceDirichletNormalizedGradient.lean` combines the characteristic identity,
the genuine canonical root differential, and the proved normalization formula.
Inclusion into every finite source exponent `p≥2` preserves the directional
formula and the unit Fourier values of the root derivative. The physical H¹
specialization constructs its representative from the Sobolev coefficients
and identifies both components, without a supplied gradient formula.

Public checks cover the general continuous characteristic identity, nonzero
normalization at real H¹ canonical roots, both actual Fourier-direction values
at `p=3`, and the normalized integral in arbitrary compatible directions.
The root-gradient application in this checkpoint is at real sources. A common
complex neighborhood for this application and the uniform shifted-free
remainder estimate remain next. G.7 as a whole and Lemma 16.1 remain unfinished.

## Appendix G.7: Dirichlet gradients on a common complex domain

The actual canonical Dirichlet gradient formula now holds on one open
complex neighborhood of the entire real source locus, for every finite
source exponent `p≥2`. At each H¹ source in this domain, every signed root
has nonzero bilinear normalization and both actual source cotangent
coefficients equal the normalized physical Fourier coefficients at reversed
frequency. No real-type, simple-root, gradient, or normalization premise is
required at the evaluation point; membership in the constructed domain is
the only neighborhood condition.

`SourceBoundarySimpleNeighborhood.lean` proves a stronger boundary fact for
every finite `p>1`: one open domain containing all real sources supports
analytic and simple canonical Dirichlet and Neumann roots at every index.
Uniform tail labeling and original algebraic multiplicity one handle distant
indices. Joint continuity of the moving characteristic derivative preserves
simplicity in the finite central block. Intersecting these neighborhoods
and taking their union gives a common domain, including collapsed periodic
gaps without any open-gap assumption.

`SourceBoundarySimpleDifferential.lean` differentiates the genuine canonical
zero equation at complex simple sources. `SourceDirichletComplexGradient.lean`
transfers the fixed-parameter source characteristic derivative to its physical
representative across exponent inclusion. It combines the actual root
cotangent with the proved squared-eigenfunction quotient, giving the exact
normalized integral in every compatible continuous source direction.
`SourceDirichletComplexFourierGradient.lean` constructs the H¹ representative
and tests both unit Fourier directions, retaining the reversed-frequency
convention in the actual source cotangent.

Public checks cover the common simple analytic domain for both boundary
conditions, the actual complex-root characteristic quotient, and both H¹
Dirichlet gradient coefficients on the common `p=3` neighborhood. The
uniform shifted-free remainder estimate is still needed for G.7's Dirichlet
summability assertion. G.7 as a whole and Lemma 16.1 remain unfinished;
no infinite-exponent assertion is added.

## Appendix G.7: uniform Dirichlet root and gradient value estimates

The normalized physical Dirichlet gradient at the actual canonical root
now differs from the exact free pair
`(exp(2iπnt)/2, exp(-2iπnt)/2)` by `D/|n|` pointwise on the entire unit
interval. One source neighborhood and cutoff work for the whole physical
H¹ ball, including complex sources, at every finite source exponent `p≥2`.
The canonical-root displacement and normalization estimates used in this
bound are derived from the physical source data.

`ClassicalSobolevBoundaryRootDisplacement.lean` expresses each ordinary
characteristic error as the contractive endpoint functional of the actual
solution remainder. Its sine error is uniformly `O(1/|z|)`. The nonzero
filled sine quotient on quarter-π discs then gives inverse-index root
displacement. `SourceBoundarySobolevDisplacement.lean` supplies these discs
and the actual zero equations from canonical source tail isolation and
physical compatibility. Both Dirichlet and Neumann sequences are covered;
no inverse-index displacement premise is supplied.

`ClassicalDirichletNormalizationBounds.lean` estimates the bilinear product
of the actual solution components against the free solution. Integration
gives `Q−2=O(1/|z|)`, hence `O(1/|n|)` near the free lattice. Beyond one
cutoff, `|Q|≥1`, `|Q⁻¹|≤1`, and `Q⁻¹−1/2=O(1/|n|)`.
`SourceDirichletSobolevNormalization.lean` instantiates these bounds at the
actual signed roots, uniformly on the source neighborhood and H¹ ball.

`ClassicalDirichletGradientValueBounds.lean` combines the squared-solution
error and inverse-normalization error. `SourceDirichletGradientValueBound.lean`
uses the proved canonical-root estimates to give the uniform pointwise
free-wave error. Together with the previous common-domain identification,
this controls the values of the physical representative of the actual
Dirichlet cotangent. The needed time-derivative bound and Fourier
interpolation/summability step are not yet proved for this normalized error.

Public checks cover both actual sine errors, both canonical boundary
displacements at `p=3`, the quantitative inverse normalization, and the
uniform actual-root error with the two exact free waves and one-half
factors. G.7 as a whole and Lemma 16.1 remain unfinished. No
infinite-exponent assertion is added.

## Appendix G.7: Dirichlet gradient time bounds and Fourier summability

The normalized Dirichlet gradient error now has a uniformly bounded time
derivative at the actual canonical roots. Together with the proved
`A/|n|` value bound, this gives a summable sequence of physical Fourier
norms. For every finite source exponent `p≥2`, the inner conjugate-exponent
Fourier norms belong to outer ℓp, including the finite central head.

`ClassicalDirichletGradientTimeRegularity.lean` proves C¹ regularity and the
exact signed ODE for the normalized gradient and its free-wave error.
`ClassicalDirichletGradientDerivativeBound.lean` uses the cancellation to
bound the derivative by `2(π+B)A+2B+8M exp(4M+B)²`. The spectral shift,
normalization inverse, and physical potential bounds all come from the
previous estimates. `SourceDirichletGradientTimeBounds.lean` supplies both
time bounds on one neighborhood of any complex source and one H¹ ball.

`ClassicalDirichletGradientFourier.lean` constructs the actual unit-interval
Fourier coefficients and proves interpolation and summable power bounds.
`SourceDirichletGradientFourierSummability.lean` gives one outer ℓˢ majorant
for the tails, uniformly over the neighborhood, H¹ ball, and contractive
scalar observations, whenever `s>1` and `q>1+1/s`. It also proves full-sequence
summability at each fixed source and the conjugate-exponent specialization.
These results concern the total normalized physical expression; identifying
it with the genuine cotangent at every index uses the previously constructed
common simple-root domain.

Public checks cover the exact signed ODE, the uniform time bounds at source
exponent three, both Fourier components at inner exponent 3/2 and outer
exponent three, and a common outer ℓ² tail majorant. Next combine the
Fourier error bounds with the common-domain cotangent identification to
export summability for the actual Dirichlet derivative minus its free
half-wave functional. G.7 as a whole and Lemma 16.1 remain unfinished;
no infinite-source-exponent assertion is added.

## Appendix G.7: actual Dirichlet gradient summability on a common domain

G.7's Dirichlet derivative error now has a proved conjugate Fourier
coefficient pair whose norms form an outer ℓp sequence, for every finite
source exponent `p≥2`. This is the genuine canonical-root derivative minus
the explicit free functional `h ↦ (h₁(-n)+h₂(n))/2`, on one open complex
neighborhood of the entire real source locus. Both component identities
retain the reversed Fourier index. The finite central block is included.

`SourceFreeDirichletCotangent.lean` extends the exact zero-source derivative
from the Hilbert space to every finite source exponent at least two by
exponent compatibility and finite-source density. It defines the free
functional as a continuous linear map with the two signed half-wave terms.
`SourceDirichletGradientErrorCotangent.lean` subtracts the actual zero-source
Fourier identities on the common simple-root domain, identifies the error
coefficients, and bounds the genuine source operator by its two conjugate
physical Fourier norms.

`SourceDirichletSobolevSummability.lean` combines these identities with the
proved Fourier summability estimates. It constructs the physical Fourier
pair of the actual derivative error, proves its outer sequence membership
in the correct component-sum norm, and specializes to the conjugate exponent.
It also proves source operator summability and the real H¹ corollary.
No root-simplicity, normalization, candidate-gradient, or majorant premise
is supplied by the caller.

`SourceSpectralGradientSobolevSummability.lean` puts both the actual midpoint
operator estimate and the Dirichlet operator error estimate on one shared
complex domain. Public checks cover the free half-factors and index signs,
the actual Fourier pair at inner exponent 3/2 and outer exponent three,
the shared domain, and the real H¹ case.

The next step is to export the midpoint estimate in the literal conjugate
Fourier pair norm as well, then apply the gradient estimates in Lemma 16.1.
The midpoint result is currently exported in source operator norm. The
infinite-source-exponent case, the sharper G.1 integral bound, and later
unfinished results remain outside this milestone.

## Appendix G.7: both G.7 estimates in the conjugate Fourier norm

For every finite source exponent `p≥2`, both the actual midpoint gradient
and the actual Dirichlet gradient error now have outer ℓp summability in
the conjugate Fourier pair norm. One open complex neighborhood contains
the entire real source locus and works for both sequences, including the
finite central block and collapsed periodic gaps. The Dirichlet correction
is the exact functional `h ↦ (h₁(-n)+h₂(n))/2`.

`ConjugateCotangent.lean` recovers the conjugate coefficient representative
of a bounded scalar ℓp functional. Finite dual tests uniformly control every
truncation; the bounded pointwise limit gives membership in ℓq. Finite-mode
density proves that the representative recovers the entire functional,
and its norm equals the original operator norm.

`SourceConjugateGradient.lean` combines the two component representatives
and reverses their Fourier indices to obtain the physical gradient. This
recovery is a bounded complex-linear map into the component-sum coefficient
space, with norm bounded by twice the source operator norm. Its bilinear
duality formula holds for every source direction. It transfers summable
operator sequences to summable conjugate Fourier gradients.

`SourceSpectralConjugateGradients.lean` applies this recovery to the genuine
canonical midpoint derivative and Dirichlet derivative error. It defines
their physical coefficient pairs, proves both component identities and
full-direction duality formulas, and exports both G.7 estimates on the
same complex domain. The result is now in the literal Fourier pair norm,
not only the source operator norm. Public checks cover `p=3`, conjugate
exponent `3/2`, the Hilbert endpoint, the index signs, the exact free
correction, and the common complex domain.

Next apply the spectral gradient estimates to finite-gap sources in Lemma
16.1, including the work needed for its full `1<p<∞` range. This checkpoint
proves G.7 for finite `p≥2`; no other exponent range is claimed. The sharper
G.1 integral bound, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Latest progress: actual anti-discriminant gradient summability at boundary roots

G.6's anti-discriminant estimate now applies to the genuine source derivative
at every canonical Dirichlet or Neumann root of a complex H¹ source. For
finite `p≥2`, subtracting the actual zero-source reference gives an outer
ℓp sequence both in source operator norm and in the conjugate Fourier pair
norm. The entire signed sequence is included, with no reality, root
simplicity, displacement-bound, or finite-head premise supplied by callers.

`ContinuousSourceAntiDiscriminantGradient.lean` identifies the normalized
source anti-discriminant with the classical monodromy anti-trace at every
compatible continuous Hilbert potential. Opposite component phases preserve
physical synthesis. Differentiating along compatible affine directions
identifies the full source cotangent and both reversed-frequency Fourier
coefficients. The cotangent restricts correctly between any finite exponents
strictly above one; physical comparison also extends by Hilbert inclusion
to finite `p≥2`. Spectral derivatives retain the same normalization.

`SourceAntiDiscriminantGradientError.lean` identifies the actual cotangent
error with G.6's physical Fourier remainder and bounds its operator norm
by the two conjugate Fourier norms. Its free reference is proved exactly as
`h ↦ i cos(πn) (h₁(-n)−h₂(n))` for every finite `p>1`, including `1<p<2`.

`SourceAntiDiscriminantSobolevSummability.lean` derives the required spectral
displacement from the actual canonical boundary roots, applies the physical
H¹ summability theorem, and transfers the result to the genuine source
operator and its recovered conjugate gradient. Public checks cover exponent
restriction across two, both component signs, spectral differentiation,
non-Hilbert conjugate norms, and the Hilbert endpoint.

Next combine this estimate with the G.7 results and the omitted-root-product
normalization in the finite-gap differential formula for Lemma 16.1. That
lemma, the full `1<p<∞` gradient range, the sharper G.1 integral bound,
remaining assertions of Theorem 14.1, and later chapters remain unfinished.

## Latest progress: signed omitted-product normalization at actual boundary roots

At every real source and every finite `p>1`, the omitted standard-root
product evaluated at either canonical boundary sequence differs from
`cos(πn)` by an ℓp sequence. Its reciprocal has the same signed ℓp
normalization, and all reciprocal norms have one finite bound. These
results include endpoints, collapsed gaps, and the entire finite central
block; no finite-gap or H¹ premise is required.

The standard-root sign proofs now hold on the closed selected real gap.
Strict separation from every other indexed gap keeps all retained roots
strictly on an exterior ray, even when the selected gap is a singleton.
The finite-product parity count, reality, limit, and nonvanishing arguments
therefore select the same signed square root throughout the closed gap.
The existing open-gap APIs remain as specializations.

`DeletedProductSampledValues.lean` proves that arbitrary ℓp displacements
of the sampling lattice give an ℓp deviation from one for the actual
deleted periodic product. Its proof combines the existing product-error
majorants with the free squared-sine increment bound; only tail samples
need lie in the free discs.

`SourceOmittedProductBoundaryNormalization.lean` applies this result at the
actual boundary roots. The exact square identity and closed-gap sign imply
`|Pₙ−cos(πn)|≤|Pₙ²−1|`. Reciprocal perturbation on the tail gives the inverse
estimate; finite-exponent coefficient bounds include all remaining indices.
Public checks cover negative-index parity, all free collapsed gaps, exact
free inverse cancellation, both boundary sequences, and exponents on either
side of two.

Next combine this normalization with the actual G.6 and G.7 estimates in
the finite-gap differential formula for Lemma 16.1. The full lemma and its
`1<p<∞` gradient range, the sharper G.1 integral bound, remaining assertions
of Theorem 14.1, and later chapters remain unfinished.

## Latest progress: finite-gap coordinate gradient errors for finite p ≥ 2

At every real finite-gap source with finite `p≥2`, the derivative of the
actual gap-weighted eta coordinate differs from its signed free Fourier
functional by an outer ℓp sequence. The estimate holds both in source
operator norm and in the full conjugate Fourier pair norm. It includes
both infinite tails and all finitely many open gaps, for every sign.
The theorem uses the existing local common-domain coordinate construction.

`SourceGapWeightedEtaFreeCotangent.lean` identifies the reference exactly
as `h ↦ (sign−1)h₁(-n)−(sign+1)h₂(n)`. Thus the two signs select one
component with factor minus two. The free Dirichlet and anti-discriminant
cotangents have uniform operator bounds.

`SourceGapWeightedEtaClosedSummability.lean` decomposes the closed-gap
error into the midpoint and Dirichlet errors and three anti-discriminant
corrections. G.6, G.7, scalar spectral-derivative summability, and the
signed inverse omitted-product normalization prove summability of every
term at real H¹ sources. Bounded scalar multiplication and bounded-vector
multiplication are formalized for vector-valued sequences.

`SourceFiniteGapHilbertRealization.lean` constructs the real Hilbert
preimage and compatible physical H¹ domain representative directly from
finite-gap Sobolev regularity. No H¹ witness is supplied by callers.
`SourceGapWeightedEtaFiniteGapSummability.lean` then applies the exact
closed-gap derivative formula outside the finite open-gap set. A
vector-valued finite-modification theorem includes the remaining indices;
bounded conjugate-gradient recovery gives the physical Fourier norm.

Public checks cover both free signs below two, the Hilbert endpoint,
construction of the physical H¹ representative at `p=3`, the actual
operator error, inner `ℓ^(3/2)` / outer `ℓ³` gradient errors, and arbitrary
finite changes of operator sequences.

The `1<p<2` source-gradient range remains before the full Lemma 16.1.
The sharper G.1 integral bound, remaining assertions of Theorem 14.1,
and later chapters also remain unfinished.

## Latest progress: Lemma 16.1 for every finite p > 1

The full finite-gap eta gradient estimate now holds for `1<p<∞` in the
physical conjugate Fourier pair norm. Both signs and every signed index
are included. In the library's period-one coefficient convention, the
free gradient is `−2` times the second component at `−n` for sign `+1`,
and `−2` times the first component at `n` for sign `−1`.
The corresponding actual gradient plus twice that mode has an ℓp
sequence of conjugate-pair norms, as in Lemma 16.1.

`SourceHilbertGradientOuterSummability.lean` separates inner and outer
exponents. The actual Hilbert midpoint derivatives, Dirichlet derivative
errors, and anti-discriminant cotangent errors have every outer exponent
strictly above one. The physical Fourier threshold allows inner exponent
two throughout this range; neither finite gaps nor a gradient-bound
premise is needed for these H¹ estimates.

`SourceGradientExponentRestriction.lean` differentiates exponent
compatibility of the actual midpoint and restricts the free Dirichlet
functional exactly. Existing boundary-root and anti-discriminant
compatibility restrict the remaining actual cotangents. Bounded
composition preserves the independently chosen outer exponent, proving
the real H¹ G.6–G.7 estimates below two.

`SourceGapWeightedEtaAllExponentSummability.lean` constructs the physical
H¹ representative from finite-gap regularity below two and combines the
two exponent ranges. The closed-gap algebra now has a shared theorem
accepting the three gradient estimates at any finite source exponent.
Finite modification includes every open gap in the actual derivative
estimate. Existing APIs for `p≥2` remain available.

`SourceGapWeightedEtaLemma16_1.lean` identifies the free conjugate gradient
with the literal signed Fourier modes. Its final existence theorem supplies
one constructed Birkhoff family and domain satisfying both estimates at
every real finite-gap source, so no chart data or H¹ witness is assumed.
Public checks include independent inner/outer exponents, both boundary
conditions below two, both free Fourier signs, and the full estimate and
constructed-family existence at source exponent `3/2`, conjugate exponent `3`.

Next prove Lemma 16.2 for the rectangular Birkhoff-coordinate gradients,
then the compact-perturbation argument for the Jacobian. The sharper G.1
integral bound, remaining assertions of Theorem 14.1, and later chapters
also remain unfinished.

## Latest progress: Lemma 16.2 for every finite p > 1

Both actual rectangular Birkhoff-coordinate gradients now differ from
their explicit free Fourier gradients by sequences whose conjugate-pair
norms belong to ℓp, at every real finite-gap source and every `1<p<∞`.
The result includes all open gaps, collapsed gaps, and both signed tails.
A final existence theorem supplies the constructed Birkhoff family and
its domain, without an assumed normalization estimate or H¹ witness.

`SourceBirkhoffFiniteGapFactors.lean` proves that the beta correction is
an ℓp sequence at finite-gap sources. The sum over gap indices reduces
to the finite open-gap set; each summand is bounded by a shifted punctured
reciprocal lattice. The normalized-action root is summably close to one
at every real source. Exponentiation preserves summable deviations, so
the complete action-root and beta-phase multiplier differs from one by
an ℓp sequence, for every sign.

`SourceBirkhoffWeightedGradientSummability.lean` proves the exact
closed-gap product-rule formula. Vanishing of the eta coordinate removes
the derivatives of the action root and beta phase. Lemma 16.1, the scalar
multiplier estimates, and a uniform free-functional bound control the
remaining derivative error. Finite modification includes all open gaps.

`SourceBirkhoffRectangularGradientSummability.lean` forms the actual x/y
derivatives by the normalized signed sum and difference. Both errors
are ℓp sequences in source operator norm. The free functionals evaluate
as `−(h₁(-n)+h₂(n))/√2` and `(h₁(-n)−h₂(n))/(√2 i)`.
`SourceBirkhoffLemma16_2.lean` identifies their physical Fourier gradients
and proves both literal conjugate-norm estimates. Its existence theorem
retains the actual constructed complex analytic Birkhoff map.

Public checks cover exponentiation without a smallness premise, normalized
action roots at arbitrary real sources, finite-gap beta and multiplier
summability below two, both exact free functionals and gradients, the
full rectangular estimate at source exponent `3/2` / conjugate exponent
`3`, and constructed-family existence at the Hilbert endpoint.

Next establish the Jacobian's compact perturbation of the Fourier
transform and continue Section 16. The sharper G.1 integral bound,
remaining assertions of Theorem 14.1, and later chapters remain unfinished.

## Latest progress: Lemma 16.3 at every real source

The actual Birkhoff Jacobian is now a compact perturbation of its free
Fourier transform at every real source and every `1<p<∞`, without a
finite-gap hypothesis. Its normalization `Aφ = F⁻¹ dφΩ` is identity plus
a compact operator and depends real analytically on the whole real
source space. Bounded invertibility of `dφΩ` is equivalent to bounded
invertibility of `Aφ`, with explicit transport of both isomorphisms.
A final existence theorem supplies the actual constructed Birkhoff family.

`SourceBirkhoffFourierEquivalence.lean` constructs the bounded inverse
of the free Fourier transform, retaining the first component's frequency
reflection and both square-root and imaginary factors. Both inverse
identities are proved for whole coefficient sequences, giving a complex
Banach-space equivalence. This linear result also holds at infinity;
the nonlinear Jacobian assertions remain restricted to finite `p>1`.

`SourceBirkhoffJacobianCompact.lean` identifies the actual Jacobian rows
with the rectangular derivatives from Lemma 16.2 and produces two ℓp
row majorants at finite-gap sources. Finite output truncations converge
in operator norm, and both remainder components are compact. The actual
Jacobian is continuous on the full real source space. Density of real
finite-gap sources in the original source norm and closedness of the
compact operators therefore extend compactness to every real source.

`SourceBirkhoffLemma16_3.lean` normalizes by the explicit Fourier inverse,
proves the exact identity `Aφ−Id = F⁻¹(dφΩ−F)`, and proves complex
analyticity on the constructed domain and real analyticity on the
entire real source space. The free normalized Jacobian is exactly
identity. Both bijectivity and bounded-isomorphism assertions are
preserved by normalization, and the full constructed-family theorem
combines these conclusions with compactness.

Public checks cover both inverse identities below two, signed inverse
coordinates, the linear bounded-sequence endpoint, finite-gap truncation
convergence, all-source compactness above and below two, analyticity and
normalization at zero, isomorphism transport, and family existence.

Next prove Proposition 17.1, the local diffeomorphism property, using
the compact perturbation and the canonical gradient identities. The
sharper G.1 integral bound, remaining assertions of Theorem 14.1, and
later chapters remain unfinished.

## Latest progress: real analytic local inversion for 2 ≤ p < ∞

The upper-exponent part of Proposition 17.1 is now proved at every real
source. The actual complex and real Birkhoff derivatives are bounded
linear isomorphisms for `2≤p<∞`. Both maps have analytic local inverses,
with both local inverse identities and derivative equal to the inverse
of the actual Jacobian. No finite-gap or invertibility premise is supplied.

`CompactDenseRange.lean` proves the general Banach-space step: a compact
perturbation of identity with dense range is bijective. The existing
compact spectral decomposition gives a closed range for a stabilized
power. Density of all powers forces that range to be the whole space,
so its complementary generalized eigenspace vanishes. The Fredholm
alternative then gives invertibility, without requiring an adjoint.

`SourceBirkhoffJacobianRange.lean` uses the actual regular cotangents and
canonical relations to construct preimages of each pure output mode.
The negative Hamiltonian direction of the y coordinate gives the x mode;
the Hamiltonian direction of the x coordinate gives the y mode. All
finite output truncations lie in the derivative's range, and convergence
of truncations proves dense range for finite exponents at least two.

`SourceBirkhoffJacobianInvertible.lean` combines this with Lemma 16.3,
packages the actual Jacobian as a bounded complex equivalence, and proves
existence of an analytic complex local inverse at every real source.
`SourceBirkhoffRealJacobian.lean` differentiates the actual inclusion of
the real map into the complex map. This comparison holds for every
`1<p<∞`. Complex bijectivity transfers to real bijectivity by decomposing
a complex preimage into real and imaginary source parts.

`SourceBirkhoffLocalInverse.lean` supplies the analytic inverse on the
actual real source and real coefficient spaces for `2≤p<∞`. Its strict
derivative is the inverse real Jacobian. A constructed-family theorem
supplies the map, domain, and local inverses at every real source.

Public checks cover the general dense-range theorem, canonical mode
preimages at `p=2`, finite output truncations at `p=3`, complex and real
inverse identities, derivative inclusion below two, analytic real local
inversion, and constructed-family existence without extra premises.

Next extend invertibility and local inversion to `1<p<2` to finish
Proposition 17.1. The Hamiltonian-direction argument above uses `2≤p`;
square summability alone does not put these directions in a smaller
source space. The sharper G.1 integral bound, remaining assertions of
Theorem 14.1, and later chapters also remain unfinished.

## Latest progress: Proposition 17.1 for every 1 < p < ∞

The actual real Birkhoff map is now a local analytic diffeomorphism at
every real source for every `1<p<∞`. Both its real derivative and the
complex extension's derivative are bounded linear isomorphisms. The
local inverses satisfy both inverse identities on neighborhoods and
have derivative equal to the inverse of the actual Jacobian. A final
existence theorem supplies the constructed Birkhoff family and all its
real local inverses, without an invertibility or finite-gap premise.

`SourceBirkhoffJacobianAllExponents.lean` proves that the full sequence
Jacobian commutes with source and output exponent inclusion. This holds
for any two constructed families, without assuming identical normalized
root choices. The existing rectangular cotangent compatibility supplies
each coordinate of the operator identity.

For `1<p≤2`, a kernel vector maps into the Hilbert source space and is
annihilated by the Hilbert Jacobian. Its already proved injectivity and
injectivity of the source inclusion force the original vector to vanish.
The normalized derivative is a compact perturbation of identity by
Lemma 16.3, so the Fredholm alternative gives bijectivity. Together with
the upper-exponent argument, this proves complex invertibility and
analytic complex local inversion for the whole finite range above one.

`SourceBirkhoffRealJacobian.lean` now isolates the general transfer of
complex bijectivity to real bijectivity; the earlier upper-exponent API
is retained. `SourceBirkhoffProposition17_1.lean` applies that transfer
throughout the full range, packages the bounded real Jacobian inverse,
and proves the complete analytic local-inverse assertion with its exact
strict derivative. The constructed-family theorem includes every real
source and both local inverse identities.

Public checks cover arbitrary-family exponent compatibility, kernel
vanishing at `p=3/2`, complex and real bijectivity at arbitrary finite
`p>1`, the real inverse derivative and analytic local inverse at `p=3/2`,
and constructed-family existence throughout the full range.

Next address Proposition 17.2, global injectivity. Its dissertation proof
uses a previously established Hilbert-space global injectivity theorem;
that prerequisite must be formalized or obtained from proved results.
The sharper G.1 integral bound, remaining assertions of Theorem 14.1,
and later chapters remain unfinished.

## Latest progress: finite-gap and Hilbert reductions for Proposition 17.2

The exponent-extension part of global injectivity is now proved. Every
actual Birkhoff collision at any finite `p>1` induces a collision for
any constructed Hilbert Birkhoff family. Thus Hilbert global injectivity
implies global injectivity at every finite exponent above one. The
Hilbert premise remains explicit: Proposition 17.2 is not yet complete.

`RealCoeffTruncation.lean` constructs finite real output truncations and
proves their norm convergence for finite exponents. `SourceBirkhoffFiniteSupport.lean`
identifies the nonlinear output support exactly with the open periodic
gaps, using the real action-radius and zero-action characterizations.
Finite Birkhoff support is therefore equivalent to the actual spectral
finite-gap condition; it does not mean finite Fourier support of the source.

`SourceBirkhoffFiniteGapFibers.lean` proves that any pair of distinct
sources with the same output can be approximated in independently
prescribed open neighborhoods by distinct finite-gap sources with the
same finite output truncation. The analytic local inverses from
Proposition 17.1 lift the common truncation on both branches. Continuity
retains the neighborhoods and distinctness. Consequently global
injectivity is equivalent to injectivity on the finite-gap locus,
at every finite exponent above one, including the Hilbert exponent.

`RealCoeffExponent.lean` constructs coefficient-preserving real exponent
inclusions. `SourceBirkhoffMapExponent.lean` proves compatibility of the
full real Birkhoff maps across exponents and independently constructed
families. Injectivity at a larger exponent implies it at a smaller one.

`SourceBirkhoffInjectivityReduction.lean` lifts a finite-gap collision
above two to distinct coefficient-preserving real Hilbert sources, using
the previously proved finite-gap Hilbert realizations. Map compatibility
and injectivity of the output inclusion give equal Hilbert outputs.
Below two, direct inclusion transports any collision. The final results
reduce all global injectivity assertions to the Hilbert assertion; even
injectivity only on Hilbert finite-gap sources is enough. Above two,
the original and Hilbert global injectivity assertions are equivalent.

Public checks cover real truncation convergence below two, exact
finite-gap/support equivalence, simultaneous collision approximation in
arbitrary neighborhoods, the Hilbert finite-gap reduction, collision
transport below two, equivalence at `p=3`, and the explicit remaining
Hilbert finite-gap injectivity premise for arbitrary finite `p>1`.

Next prove Hilbert injectivity on finite-gap sources, or formalize the
Hilbert global theorem cited as [23, Theorem 19.3] in the dissertation.
No such theorem has been assumed as an axiom. Proposition 17.2, the
sharper G.1 integral bound, remaining assertions of Theorem 14.1, and
later chapters remain unfinished.

## Previous progress: analytic Hilbert action sequence and total

The actual Hilbert spectral actions now form a holomorphic ℓ¹-valued
map on the constructed complex domain and a real analytic ℓ¹-valued
map on the whole real source space. Both literal action series are
absolutely convergent. The derivative series is absolutely convergent
in every source direction and equals the derivative of the total action.
These are proved for the actual spectral actions, with no summability
or termwise-differentiation premise.

`QuadraticActions.lean` constructs `(xₙ²+yₙ²)/2` as an entire map from
two complex ℓ² spaces into ℓ¹, using bounded bilinear multiplication.
On real sequences the actions are nonnegative. Their ℓ¹ norm and total
are exactly `(‖x‖²+‖y‖²)/2`; the ordinary product's maximum norm is not
mistaken for the Hilbert sum of squares.

`SourceHilbertActionSequence.lean` composes this map with the actual
Birkhoff family and identifies every coordinate with its original
spectral action by the action-radius identity. Bounded ℓ¹ summation
gives complex and real analytic total-action functionals. Evaluation
of the sequence derivative gives the actual scalar action derivatives,
so their absolute convergence and termwise summation follow in norm.
A constructed-family theorem supplies the actual real analytic action
map and its spectral coordinate identities.

`SourceHilbertActionTraceReduction.lean` reduces the total to a finite
sum whenever the spectral gap tail is closed. Finite-gap density and
continuity prove that the source-mass trace formula for all real Hilbert
sources is equivalent to its finite-gap case. The proved source-mass
normalization then yields `sum Iₙ = ‖φ‖²/2` conditional on that finite-gap
identity. Properness of the actual action map implies properness of the
actual Birkhoff map through the quadratic factorization.

Public checks cover complex ℓ¹ analyticity, exact output normalization,
absolute convergence of actual actions and derivative series, termwise
differentiation, real ℓ¹ analyticity and norm, finite closed tails,
the explicit finite-gap trace obligation, properness transfer, and
constructed-family existence without a summability hypothesis.

Next prove the finite-gap source-mass trace identity, using contour
consolidation and the first nontrivial high-energy mass coefficient of
the discriminant primitive. Weak continuity of the spectral action
coordinates is also needed for Hilbert properness. The source-mass
identity and action-map properness have not been asserted unconditionally.
Proposition 17.2 and the other previously recorded unfinished results
remain open.


## Previous progress: the physical mass coefficient of the discriminant

For every continuous complex potential on one period, Lean now proves

`2y (exp(-y) Δ(iy) - 1) → ∫₀¹ φ₁(s) φ₂(s) ds` as `y → +∞`.

This identifies the first correction, including its sign and factor two;
it strengthens the earlier leading limit `exp(-y) Δ(iy) → 1`. No real-type,
finite-gap, or differentiability assumption on the potential is needed.

`ExponentialVolterra.lean` supplies the actual causal convolution, its
continuity and linearity, and the inverse decay-rate bound.
`ExponentialVolterraApproximation.lean` proves that the normalized kernel
recovers every continuous forcing at positive times. Dominated convergence
also proves recovery after integration against another continuous factor.
The endpoint zero is excluded from the pointwise recovery theorem.

`ClassicalMassCorrection.lean` isolates the explicit quadratic Volterra
iterate in the upper normalized trace. With `M = ‖φ‖` and `a = 2 Im z`,
the remainder is at most `(2 M⁴ + 2 M²)/a²` whenever `Im z > 0` and
`M² ≤ Im z`. The estimate is uniform in `Re z` and has no assumed solution
bound. `ClassicalDiscriminantMassAsymptotics.lean` combines this estimate
with kernel recovery to identify the physical mass coefficient. Equal
classical discriminants consequently have equal physical masses.

Public checks cover continuous forcing, the quantitative trace remainder,
the actual coefficient limit, arbitrary constant complex potentials, and
mass recovery from equality of discriminants.

Next transfer this coefficient to finite-gap source representatives, identify
their physical mass with `sourceHilbertMass`, and extract the corresponding
coefficient of the canonical discriminant-ratio primitive. Exterior contour
consolidation must still relate that coefficient to the finite action sum.
The action/mass trace identity, action-map properness, and Proposition 17.2
remain unfinished; none is assumed in these new results.


## Previous progress: finite-gap source mass recovered from the discriminant

The physical mass coefficient is now transported to the actual canonical
source discriminant. For every complex Hilbert source with absolutely
summable component coefficients,

`2y (exp(-y) Δφ(iy) - 1) → sourceHilbertMass φ` as `y → +∞`.

`SourceAbsoluteMassAsymptotics.lean` constructs the continuous period-one
representative by absolute Fourier synthesis and proves almost-everywhere
compatibility with the original source potential. Bilinear Parseval gives
exact equality of its physical mass and the reflected source pairing.
The existing classical/canonical trace identity then transfers the limit.
Equal canonical discriminants have equal mass on this source class.

`SourceFiniteGapMassAsymptotics.lean` uses the proved Sobolev bootstrap to
show absolute Fourier summability for all real finite-gap sources at every
finite exponent `p>1`. At the Hilbert exponent, the coefficient limit thus
requires only finite-gap membership and is exactly `‖φ‖²/2`. It leaves no
physical realization or summability premise. Two finite-gap Hilbert sources
with equal canonical discriminants have equal original source norms.

Public examples check the actual physical representative, the bilinear mass
identity for complex sources, the canonical coefficient limit, all-exponent
finite-gap absolute summability, the exact Hilbert normalization, and norm
recovery from equality of discriminants.

Next pass from the discriminant coefficient to the canonical-root/Floquet
multiplier and its logarithmic primitive, then consolidate the finite action
contours. The finite-gap action/mass trace identity, Hilbert action-map
properness, and Proposition 17.2 remain unfinished.


## Previous progress: a mass-normalized upper-half-plane primitive

The actual canonical Floquet multiplier `(Δ + root)/2` is now constructed.
Its companion multiplies with it to one off the periodic gap cuts, so it
never vanishes there. It is analytic on that domain, and on the principal
logarithm's slit plane its logarithmic derivative is exactly `Δ'/root`.
The branch condition is explicit; no global principal-log branch is assumed.

`SourceCanonicalRootVerticalAsymptotics.lean` specializes the exterior
product normalization to prove `exp(-y) root(iy) → 1` at every finite
exponent `p>1`. This fixes the upper sign. The root square identity then
transfers the proved source mass coefficient to the root and multiplier.
`LogarithmicCoefficient.lean` passes a scaled first-order limit at one to
the logarithm, including arguments that equal one infinitely often.

For absolutely summable real Hilbert sources,
`2y (log multiplier(iy) - y) → sourceHilbertMass φ`. The normalized multiplier
converges to one, which proves that its unnormalized value eventually lies
in the slit plane on the upper imaginary ray. The exponential normalization
subtracts exactly the real height from the logarithm.

`SourceMassNormalizedPrimitive.lean` matches any existing upper-half-plane
primitive of `Δ'/root` to that logarithm up to one constant on a terminal
imaginary ray. Subtracting the constant supplies an actual primitive on the
whole upper half-plane with `2y (F(iy)-y) → sourceHilbertMass φ`. For real
finite-gap Hilbert sources the limit is exactly `‖φ‖²/2`, with all absolute
summability assumptions discharged by the proved Sobolev bootstrap.

Public examples check logarithmic coefficient transfer without a punctured
limit, multiplier nonvanishing, the upper root sign, the precise local log
derivative, eventual branch validity, subtraction of the height, and the
global upper primitive with its finite-gap norm coefficient.

Next extend the normalized primitive across closed gaps to the exterior of
the finitely many open gaps and control its expansion at infinity. Then
consolidate the finite action contours and extract the corresponding contour
coefficient. A limit on one vertical ray alone does not establish that
contour identity. The action/mass trace formula and Proposition 17.2 remain
unfinished.

## Previous progress: analytic continuation through all collapsed gaps

`SourceOpenGapComplement.lean` removes only the noncollapsed periodic
segments. At every real source and finite exponent `p>1`, the actual
canonical root is analytic on this enlarged domain, including its defined
values at collapsed endpoints. Its square identity still holds there.
The Floquet multiplier remains analytic and has a reciprocal companion,
so it never vanishes, even at those endpoints.

The filled quotient is defined as the multiplier's logarithmic derivative.
It is analytic throughout the enlarged domain and agrees with `Δ'/root`
off all original cuts. Equality with that literal quotient is deliberately
restricted: division at a collapsed point does not give the analytic limit.

`SourceFiniteGapExterior.lean` proves that the union of the finitely many
noncollapsed segments is compact. Its complement is open and contains
an entire exterior region. Thus a positive radius exists beyond which the
actual root, multiplier, and filled quotient are analytic, and the multiplier
is nonzero. This holds at every finite exponent greater than one, with no
Fourier-support, auxiliary-domain, or continuation hypothesis.

Public examples check regularity at an actual collapsed endpoint, the
reciprocal identity on a collapsed segment, agreement with the original
quotient, and the complete exterior conclusion at `p=3`.

Next prove the exterior quotient's zero period and construct an exterior
primitive matching the mass-normalized upper primitive. Its expansion at
infinity still needs growth or removable-singularity control. The exterior
primitive, action/mass trace identity, and Proposition 17.2 are not yet proved.

## Previous progress: a mass-normalized primitive on the full exterior

`SourceFiniteGapExteriorPeriod.lean` proves that the regularized logarithmic
derivative has zero integral around every sufficiently large circle at an
actual real finite-gap source, for each finite exponent `p>1`. The proof
constructs disjoint gap circles, applies finite-hole Cauchy decomposition
only to the finitely many open gaps, and uses the established vanishing of
each individual gap period. All collapsed points remain inside the analytic
domain, so no tail gaps need to be excluded from the outer disc.

`ExteriorHolomorphicPrimitive.lean` supplies a general primitive on the
entire exterior of a disc from analyticity up to its boundary and one zero
circle period. Circular-hole filling gives an entire function; its entire
primitive plus the logarithmic Cauchy correction has the original derivative
on the full exterior. No global principal-log branch or finite outer radius
is assumed.

`SourceFiniteGapExteriorPrimitive.lean` combines these results to construct
the actual exterior primitive at every real finite-gap source. The radius
and zero period are supplied by proved spectral geometry.
`SourceFiniteGapExteriorMassNormalization.lean` fixes its additive constant
by comparing derivatives with the normalized upper primitive along the
upper imaginary ray. At the Hilbert exponent, the same exterior function
satisfies `2y (F(iy)-y) → ‖φ‖²/2`.

Public examples check the whole-exterior primitive theorem, all sufficiently
large zero periods, construction at `p=3`, and the combined derivative and
exact norm coefficient at `p=2`.

Next control this exterior primitive at infinity, derive its Laurent
coefficient from the established ray limit, and evaluate the consolidated
action contour. The ray limit alone does not prove a Laurent expansion.
The action/mass trace formula and Proposition 17.2 remain unfinished.

## Previous progress: analytic extension of the quotient at infinity

`SourceFloquetExteriorCircleBound.lean` combines the existing canonical-root
and discriminant-derivative asymptotics to bound the actual logarithmic
derivative by four on every sufficiently large half-integer circle. It also
proves convergence to `-i` on any escaping path uniformly separated from the
free lattice. These results hold for every real source at finite `p>1`.

`ExteriorCircleBounds.lean` proves maximum-modulus propagation on an annulus
and uses it to turn eventual bounds on escaping circles into a bound on an
entire exterior region. `ExteriorRemovableSingularity.lean` then proves that
a bounded analytic exterior function has an analytic inversion extension:
after setting `z = 1/w`, its singularity at `w=0` is removable.

`SourceFiniteGapAtInfinity.lean` applies these results to the actual
finite-gap logarithmic derivative, including every collapsed point in its
exterior. It constructs an analytic function on a disc about zero agreeing
with the inverted quotient at every nonzero point. The free asymptotic along
half-integer real spectral points proves that its value at zero is exactly
`-i`. No bound, continuation, or removability premise remains for finite-gap
sources at any finite exponent greater than one.

Public examples check propagation from escaping circles, removable
inversion, the leading sign on separated paths, and the complete normalized
analytic extension at `p=3`.

Next use the analytic extension and zero exterior period to extract the
higher expansion coefficients. Match them to the mass-normalized exterior
primitive's ray limit, then evaluate the consolidated action contour. The
higher coefficients, action/mass trace formula, and Proposition 17.2 remain
unfinished.

## Previous progress: exact exterior coefficients and weighted contour

`InversionCircleCoefficients.lean` proves two coefficient formulas for an
analytic function evaluated at inverse frequency. Its unweighted exterior
circle integral is `2πi g'(0)`, and weighting by the spectral parameter gives
`2πi (dslope g 0)'(0)`, the quadratic Taylor coefficient. The proof uses two
analytic divided differences and a primitive of their remainder; it does
not assume a Laurent contour formula or interchange an infinite series.

`SourceFiniteGapExteriorCoefficients.lean` applies these formulas to the
actual finite-gap logarithmic derivative. The established zero exterior
period forces `g'(0)=0`. At every finite exponent `p>1`, it constructs an
analytic remainder `h` near zero with the exact exterior identity

`sourceFloquetLogDerivative φ z = -i + z⁻² h(1/z)`.

For every sufficiently large circle, the weighted integral is exactly
`2πi h(0)`. The remainder and contour formula are constructed from actual
finite-gap membership, without an assumed expansion or vanishing residue.

Public examples check the residue sign and normalization for a linear germ,
the general weighted coefficient formula, and the combined exact remainder
and actual contour identity at `p=3`.

Next identify `h(0)` with `-i sourceHilbertMass φ/2` by comparing a primitive
of the analytic remainder with the mass-normalized exterior primitive.
Then consolidate the action contours to establish the finite-gap trace
formula. The mass identification, action/mass trace identity, and
Proposition 17.2 remain unfinished.

## Previous progress: source mass equals the exterior contour coefficient

`ExteriorPrimitiveCoefficient.lean` constructs an exterior primitive from
an analytic quadratic remainder and computes its upper-ray coefficient as
`2i h(0)`. A second theorem proves uniqueness of finite normalized primitive
coefficients. Equal derivatives make two primitives differ by a constant
along a terminal imaginary ray; their finite coefficient limits force that
constant to vanish. The additive normalization is therefore handled explicitly.

`SourceFiniteGapExteriorMass.lean` compares this constructed primitive with
the already mass-normalized actual finite-gap primitive. The analytic
remainder now has its proved value

`h(0) = -i sourceHilbertMass φ / 2`.

Consequently every sufficiently large positively oriented circle satisfies

`∮ z sourceFloquetLogDerivative φ z dz = π sourceHilbertMass φ`.

The equivalent norm formula has right side `π ‖φ‖²/2`. These conclusions
require only real Hilbert finite-gap membership; the expansion, period,
regularity, normalization, and coefficient are all constructed or proved.
The integral uses the regularized quotient, so collapsed points on the
circle cause no undefined analytic behavior.

Public examples check the primitive coefficient for a constant remainder,
uniqueness of normalized coefficients, mass identification for the actual
spectral remainder, and the complete large-contour norm identity.

Next consolidate the finitely many individual action contours into this
exterior contour and prove the finite-gap action/mass trace identity. The
existing density reduction then extends it to all real Hilbert sources.
The action-sum identity and Proposition 17.2 remain unfinished.

## Previous progress: the full Hilbert action–mass trace formula

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

## Previous progress: coefficient compactness and the properness criterion

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

## Latest progress: norm-resolvent limits from bounded coefficient limits

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
