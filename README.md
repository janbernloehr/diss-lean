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
in the potential and spectral parameter throughout its domain. The main
dissertation theorems remain future work.
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
  resolvent is compact. The perturbed inverse requires the proved Neumann
  condition `freeL1Bound * ‖φ‖ < 1`; for `p=1`, `|Im z| > ‖φ‖` suffices.
  A common high-imaginary-part region is proved for each bounded potential set
  at every finite `p`. The partial-map realization on the base space has exactly
  the included one-derivative domain and is proved closed and densely defined.
  The full resolvent is jointly complex analytic in the potential and parameter
  on an open domain, and compact throughout that domain. Sharp rates and
  spectral discreteness remain future work.
- The coefficient representation is not yet identified with periodic
  distributions. That equivalence is a separate proof obligation.
- No spectral or classical Birkhoff results are introduced as axioms.

See [PLAN.md](PLAN.md) for the implementation sequence and [STATUS.md](STATUS.md)
for the precise implemented scope.
