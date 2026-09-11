# Implementation status

## Implemented and checked

The library has fourteen modules and 122 named public theorems. All compile on the
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
from the domain to the base space. Closedness as an unbounded operator and the
physical Fourier/distribution realization remain unproved.
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
as a map into the stronger domain norm. The `FL^p → FL^1` estimates in Lemma
3.2(ii–iii), including their constants, remain to be proved.

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 330 declarations under `NLS`, including generated
definitions and instances. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.

The examples exercise multiplication at `p=1,2,3`, convolution and differentiation
at `p=∞`, domain density at `p=1`, the operator bound at `p=3`, the frequency-shift
sign, both signed free spectral equations, and nonzero off-diagonal coupling.
Resolvent checks use the concrete parameter `z=i`, exercise both inverse identities,
the bounds, compactness at `p=1,3,∞`, cutoff convergence, signed-mode denominators,
and the resolvent identity. No admission or extra project axiom is used by the library.

## Next milestones

1. Prove the `FL^p → FL^1` free resolvent estimates needed to control the potential
   perturbation (Lemma 3.2(ii–iii)), with explicit norm conventions.
2. Prove closedness and the required relative perturbation estimates for the
   general potential operator, then construct its resolvent by a Neumann series.
3. Prove the periodic Fourier/distribution realization, period-one embedding,
   pair-norm comparison, and compatibility with physical-space multiplication.

General-potential spectral theory, classical Birkhoff prerequisites, and the main
dissertation theorems remain unimplemented. Further sequence-space work includes
symmetric cutoff convenience functions, embeddings between regularities, and the full
range of Young inequalities beyond the `l1`-factor case.
