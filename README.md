# dNLS in Lean

Formalization of mathematics supporting Jan Molnar's *Features of the Nonlinear
Fourier Transform for the dNLS Equation* (2016).

Source: <https://janbernloehr.de/Download/fs16/diss.pdf>

The library currently proves sequence-space foundations, the `lp × l1 → lp`
convolution inequality, and a closed, densely defined coefficient-space Zakharov–Shabat
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
formula retains the endpoint jump for nonperiodic input. Physical Sobolev norm
comparison, interval-domain isomorphisms, Fourier/distribution realization, and
physical multiplication remain needed for the full spectral transfer.
The overview theorem's exact norm-dependent height, rectangular contour
identification, and main dissertation theorems remain future work.
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
- Pair spaces use the maximum of the component norms. The dissertation uses a
  different pair norm; comparison and transfer of constants remain to be proved.
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
- The coefficient representation is not yet identified with periodic
  distributions. That equivalence is a separate proof obligation.
- No spectral or classical Birkhoff results are introduced as axioms.

See [PLAN.md](PLAN.md) for the implementation sequence and [STATUS.md](STATUS.md)
for the precise implemented scope.
