# Actual Dirichlet spectrum and filled interpolation

## Complete actual spectrum

`exists_hillL2Dirichlet_negative_cutoff` proves a uniform negative-energy
cutoff on every bounded complex L2 potential family. Its locally uniform
version supplies compactness for actual real root limits. The actual free
characteristic has no nonpositive zero, including its filled value at zero.

`isClopen_hillDirichlet_lower_root_family` proves that the existence of a
Dirichlet zero at or below the periodic ground is open and closed in every
continuous real period-one L2 family. Actual simple real root continuation
supplies openness: a continued root cannot cross into the lowest open band.
The uniform lower bound supplies closedness. The real scalar homotopy from
zero therefore proves
`hillL2DirichletCharacteristic_ne_zero_at_or_below_lowest`, including equality
with the periodic ground.

`hillL2DirichletCharacteristic_zero_iff_label` proves that the complete complex
zero set of the actual characteristic is precisely the positive gap-indexed
Dirichlet energies. Endpoints and collapsed gaps are included. The sequence
`hillDirichletEnergySequence(j) = mu_(j+1)` is strictly increasing and tends
to infinity. No finite low roots or negative energies are discarded.

## Exact circle selection and finite Cauchy formula

`eventually_hillDirichlet_sequence_circle_selection` proves that the N-th
half-integer energy disc contains exactly the first N positive Dirichlet
energies, all strictly inside. Actual high gap endpoint localization supplies
the neighboring Dirichlet bounds; the complete low spectrum is retained.

`eventually_hillDirichlet_interpolation_cauchy_error` proves the literal finite
Cauchy identity using D for the actual characteristic and psi_n for the actual
globally selected normalized numerator:

```text
outer integral of psi_n(E)/D(E)/(E-w)
  = 2*pi*I * (psi_n(w)/D(w)
      - sum_(j<N) psi_n(mu_(j+1))/D'(mu_(j+1))/(w-mu_(j+1))).
```

This formula is used where D(w) is nonzero. Its poles, their completeness,
simplicity and derivative-normalized residues are all proved from the actual
Hill data. It does not apply a ZS RealType root constructor to Hill(-1,-q).

## Filled entire interpolation

Let K_k be the actual filled Dirichlet kernel:

```text
K_k(w) = D(w)/(2*(mu_k-w)*D'(mu_k))  if w != mu_k,
K_k(mu_k) = -1/2.
```

For the literal positive-index partial sums S_N(w),

```text
S_N(w) = sum_(j<N) psi_n(mu_(j+1))*K_(j+1)(w),
S_N(w) -> -psi_n(w)/2.
```

`tendsto_hillDirichletInterpolationSum` proves this at every complex w.
`tendstoUniformlyOn_hillDirichletInterpolationSum` proves convergence uniformly
on every bounded complex energy disc. Dirichlet energies, zero energy,
original endpoints and collapsed physical gaps are retained through the
actual filled cardinal values, not assigned total zero-over-zero values.

The actual characteristic-weighted Cauchy error identity holds on whole
evaluation discs, including the Dirichlet zeros. The previously proved
uniform outer Cauchy decay and boundedness of the actual characteristic on
a compact energy disc then give the full uniform interpolation limit.

This is a theorem about the actual positive-index partial sums. Absolute
summability and a Lean `HasSum`/`tsum` identification are not asserted here.
Convergence and source differentiation of the actual Abelian integral sum
also require their own proofs.

## Validation and reuse

Prior strict validation of all 876 unchanged selected sources; strict dependency-order compilation of four byte-identical canonical pole/Cauchy helpers and four new proof modules; then a fresh combined transitive axiom audit of all 884 selected modules. The reused helpers precede every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 884-module rebuild is claimed.

Fresh audit: 8483 selected declarations and 31027 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors and default 200000 heartbeats;
no sorry, added axioms, heartbeat increases or linter exceptions.
Thirteen shared import records and all three prior canonical reuse records
are unchanged. `CANONICAL_DIRICHLET_INTERPOLATION_REUSE.json` records the
four unchanged canonical logarithmic-derivative, finite-pole and Cauchy
helpers. No new branch sources were imported.

## Remaining article scope

Absolute summability as needed by the final angle construction, the actual
infinite Abelian sum, analytic source convergence and differentiation,
collapsed-gap integral extensions and canonical angle orientation remain
open. Thus the full physical angle/discriminant identity and Hamiltonian
frequency identities (69)/(84) are not yet proved.

Full rough W and chart compatibility, exact leading scalar and sharp root/
moment bounds, weighted remainders and compact derivatives, action/Birkhoff
realization and PDE identification remain open. All eleven main inventory
rows remain OPEN. A finite-gap energy value identity alone cannot justify
arbitrary Hamiltonian source differentiation.
