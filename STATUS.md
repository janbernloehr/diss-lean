# Implementation status

## Implemented and checked

The library has nine modules and 55 named public theorems. All compile on the
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

## Current mathematical milestone

For every `1 ≤ p < ∞`, we have constructed a continuous linear operator

`potentialMul hp φ : ScalarDomain p →L[ℂ] Coeff p`

with `ScalarDomain p = WeightedCoeff (Weight.sobolev 1) p`, and proved

`‖potentialMul hp φ f‖ ≤ C_p * ‖φ‖ * ‖f‖`.

Here `C_p` is the `lp` norm of the reciprocal weight in the Hölder conjugate
space. The construction is by convolution and has the expected coefficient
formula. This establishes the coefficient-space estimate underlying Appendix A,
Lemma A.8. Identifying it with physical-space multiplication requires the
separate Fourier/distribution realization.

The weighted topology is induced by the weighted `lp` norm. A type synonym
prevents accidental inheritance of pointwise convergence from raw sequences.

## Verification

Run `./scripts/check.sh` to build, check public-API examples, and audit transitive
axioms. The current audit covers 194 declarations under `NLS`, including generated
definitions and instances. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed.

The examples exercise multiplication at `p=1,2,3`, convolution at `p=∞`, the
frequency-shift sign, and the constant unit potential. No admission or extra
project axiom is used by the library.

## Next milestones

1. Construct the scalar domain inclusion and differentiation multiplier, then
   assemble the two-component Zakharov–Shabat operator with explicit Fourier
   and pair-norm conventions.
2. Construct the free resolvent away from `πℤ`, establish its estimates, and
   prove compactness by finite-rank approximation.
3. Prove the periodic Fourier/distribution realization and compatibility with
   physical-space multiplication.

The spectral theory, classical Birkhoff prerequisites, and main dissertation
theorems remain unimplemented. Further sequence-space work includes symmetric
cutoff convenience functions, embeddings between regularities, and the full
range of Young inequalities beyond the `l1`-factor case.
