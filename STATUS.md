# Implementation status

## Implemented and checked

The library has nineteen modules and 172 named public theorems. All compile on the
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
Those constants, analytic dependence, and Corollary 3.3's full conclusions
remain to be proved.

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

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 434 declarations under `NLS`, including generated
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
of the graph under sequential base-norm limits. No admission
or extra project axiom is used by the library.

## Next milestones

1. Establish analytic dependence of the resolvent.
2. Prove the sharper numerical rates and vertical-strip estimates from Lemma
   3.2(ii–iii), then develop discreteness and spectral localization.
3. Prove the periodic Fourier/distribution realization, period-one embedding,
   pair-norm comparison, and compatibility with physical-space multiplication.

Spectral localization, classical Birkhoff prerequisites, and the main dissertation
theorems remain unimplemented. Further sequence-space work includes
symmetric cutoff convenience functions, embeddings between regularities, and the full
range of Young inequalities beyond the `l1`-factor case.
