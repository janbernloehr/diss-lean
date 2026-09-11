# dNLS in Lean

Formalization of mathematics supporting Jan Molnar's *Features of the Nonlinear
Fourier Transform for the dNLS Equation* (2016).

Source: <https://janbernloehr.de/Download/fs16/diss.pdf>

This is the initial foundation layer, not a formalization of the main dissertation
theorems. Lean and mathlib are pinned to **v4.33.1**; `lake-manifest.json` records
the resolved dependency commits.

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

For the build plus a transitive axiom audit:

```sh
./scripts/check.sh
```

The audit rejects admitted proofs and additional mathematical axioms in every
declaration under `NLS`, including definitions and instances.

The wrapper also works with a standard `lake` on `PATH` when the workspace-local
installation is absent. No shell startup files are modified.

## Design conventions

- `NLS.Coeff p` is mathlib's complex `lp` space indexed by `ℤ`.
- Banach-space results require `[Fact (1 ≤ p)]`. Norm convergence of truncations
  additionally requires `p ≠ ⊤`.
- Finite projections are first defined for arbitrary finite frequency sets.
- Weighted spaces carry the transported `lp` norm topology, not the pointwise
  topology of the underlying raw sequences.
- Scalar sequence spaces are established before selecting a norm on potential
  pairs. The usual product norm is not silently identified with the thesis norm.
- The coefficient representation is not yet identified with periodic
  distributions. That equivalence is a separate proof obligation.
- No spectral or classical Birkhoff results are introduced as axioms.

See [PLAN.md](PLAN.md) for the implementation sequence and [STATUS.md](STATUS.md)
for the precise implemented scope.
