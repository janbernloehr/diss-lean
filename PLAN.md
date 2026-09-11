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

Next are the double-resolvent estimate and squared Neumann condition in
Lemma 3.4, followed by arbitrary-potential localization in Corollary 3.5
and spectral multiplicity counts.
Physical-space interpretation, period-one embedding, and comparison with the
dissertation's pair norm remain separate proof obligations.
