# Initial implementation status

## Implemented and checked

The initial library has four modules and 28 named theorems. All compile on the
pinned Lean/mathlib v4.33.1 toolchain.

| Module | Implemented scope |
| --- | --- |
| `NLS.SequenceSpaces.Basic` | Integer-indexed complex `lp` coefficients |
| `NLS.SequenceSpaces.Truncation` | Finite projections; coefficient formula; linearity; composition and idempotence; projection and tail norm bounds; continuous linear projections; convergence for finite `p`; density of finite-support coefficients |
| `NLS.SequenceSpaces.Weighted` | Positive weights, unit and real-exponent Sobolev weights; actual weighted coefficient subtype; weighting linear equivalence and isometry; normed complex vector space and completeness; coefficient decay bound; weighted truncation bounds and convergence |
| `NLS.SequenceSpaces.Multiplier` | Bounded diagonal symbols acting on `lp`; linearity; operator bound; continuous linear operator; commutation with truncations |

The weighted space uses a type synonym to avoid inheriting the topology of
pointwise convergence from all raw sequences. Its topology is induced by the
weighted `lp` norm. This distinction is essential for the completeness and
convergence statements.

## Verification

Run `./scripts/check.sh` to build the library and audit the transitive axioms of
every declaration in the `NLS` namespace. The initial audit checks 116
declarations, including generated definitions and instances. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

## Not yet implemented

- Symmetric `[-N, N]` cutoff convenience API; currently cutoffs use arbitrary
  finite sets, directed by inclusion.
- Weighted embeddings and convolution estimates.
- Periodic distributions, the Fourier realization, and potential pairs.
- The Zakharov–Shabat operator and its resolvent.
- Spectral data, classical Birkhoff prerequisites, and dissertation main theorems.

The next substantial target is the multiplication estimate needed to define the
operator on its domain. The current multiplier module covers diagonal Fourier
symbols; physical-space multiplication is convolution and still requires a
separate construction.
