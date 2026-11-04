# Actual terminal phase and single-gap Abelian integral variation

Fix a real period-one L2 potential q and an open gap k. Write E=mu_k(q),
D for the actual Dirichlet characteristic, U for the actual nonvanishing
filled deflated canonical root of that gap, and X_b for the constructed
Fourier Gardner direction. Define the actual filled kernel

```text
K_k(b) = D(b) / (2 (E-b) D'(E))   if b != E,
K_k(E) = -1/2.
```

Dirichlet simplicity justifies D'(E) != 0. No sheet-root denominator occurs.

## Actual terminal derivative

`fderiv_hillDirichletTerminalAngle_gardnerDirection` proves

```text
D_source epsilon[X_b] = I * U(E) * K_k(b).
```

This holds for every differentiable complex source extension epsilon whose
cosine point and sine agree with the genuine sheeted Dirichlet terminal at
nearby real period-one L2 potentials. It includes terminal bandedges, where
the sine vanishes, and zero Dirichlet energy. The selected gap must be open;
no analytic angle at a collapsed gap is asserted.

Both actual terminal equations are differentiated. Nearby-real agreement
determines the complex derivative in the actual even Fourier Gardner
direction via the proved real-source jet uniqueness theorem. The proof
does not assume that independently constructed analytic branches agree on
a full complex neighborhood. No division by sine or cosine is used.

The actual filled-root energy identity is

```text
Delta(E) Delta'(E)
  = (E-tau) U(E)^2 + ((E-tau)^2-d^2) U(E) U'(E).
```

`hillDeflatedEnergyCanonicalRoot_energy_factor` proves it by differentiating
the actual radicand factorization on the open filled gap domain, retaining
endpoints and collapsed gaps. `deriv_hillLocalDeflatedComplexRoot_base`
identifies the local extension's energy derivative with that canonical one.
Stationary actual midpoint, half-gap and fixed-energy root, the genuine
moving-root chain rule, and actual moving sheet-root variation then supply
the differentiated terminal equations. The existing canonical quadratic
sheet algebra recovers the angle velocity from both equations, including
either terminal endpoint.

## Actual Abelian integral derivative

`exists_hillDirichletAbelianIntegral_gardner_variation` constructs genuine
analytic branches B_nk and epsilon, retaining their actual nearby-real
primitive, angle, sheet and real-valued agreement, and proves

```text
D_source B_nk[X_b] = psi_n(E) * K_k(b),
D_source B_nk[X_E] = -psi_n(E)/2.
```

Here psi_n is the actual globally selected normalized numerator. The
previously proved full actual source contribution to the cosine primitive
is zero. Its exact remaining terminal contribution is evaluated using the
new angle derivative and the actual cosine differential -I*psi_n(E)/U(E).
Thus this is the complete single-gap integral variation, including terminal
bandedges and the filled spectral diagonal.

## Validation and reuse

Prior strict validation of all 866 unchanged selected sources; strict dependency-order compilation of one byte-identical canonical algebra helper and three new proof modules; then a fresh combined transitive axiom audit of all 870 selected modules. The reused helper precedes every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 870-module rebuild is claimed.

Fresh audit: 8332 selected declarations and 30916 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors and default 200000 heartbeats;
no sorry, added axioms, heartbeat increases or linter exceptions.
Thirteen shared import records and the earlier canonical trace reuse record
are unchanged. `CANONICAL_QUADRATIC_SHEET_REUSE.json` records the unchanged
algebra helper from canonical main. No new branch sources were imported.

## Remaining article scope

The actual infinite sum of these terminal contributions, its analytic
convergence/differentiation, entire Dirichlet interpolation, collapsed-gap
contributions and canonical angle orientation remain open. Therefore the
full angle/discriminant identity and physical Hamiltonian frequency identities
(69)/(84) are not proved by this single-gap result.

Full rough W and cross-chart compatibility, the exact leading scalar and
sharp root/moment bounds, weighted remainders and compact derivatives,
action/Birkhoff realization and PDE identification remain open. All eleven
main theorem inventory rows remain OPEN. The finite-gap energy value
identity alone does not justify arbitrary Hamiltonian source differentiation.
