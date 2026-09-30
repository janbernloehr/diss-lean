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

Theorem 13.1(ii) still requires comparison between different prescribed
root charts and paths traversing several charts, and analytic coverage
of every complex open-gap source point, including endpoint terminals.
Theorem 13.1(iv), Corollary 13.2, and the later chapters also remain.
