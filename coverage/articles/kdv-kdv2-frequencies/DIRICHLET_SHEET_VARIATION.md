# Actual moving Dirichlet sheet-root variation

At a real period-one L2 potential q, let E be its n-th Dirichlet energy,
D the actual Dirichlet characteristic, beta the actual sine slope at x=1,
chi the actual cosine slope at x=1, Delta the actual discriminant, and
r_D = 2 beta - Delta the signed sheet root. Let X_b be the constructed
Fourier Gardner direction at any complex b. Source derivatives below are
actual complex Frechet derivatives; primes are energy derivatives.

## Proved identities

The actual fixed-energy slope satisfies

```text
2 (E-b) D_source beta(E)[X_b] = chi(E) D(b),
D_source beta(E)[X_E] = -chi(E) D'(E) / 2.
```

The first equality is cross multiplied, hence also holds at b=E. The second
is the filled diagonal value proved by a frequency divided-difference limit,
including E=0. No global analytic square-root branch is assumed.

For any actual analytic Dirichlet branch a(p), with a(q)=E and
D_p(a(p))=0 near q, the genuine moving sheet satisfies

```text
2 (E-b) D'(E) D_source (r_D(p,a(p)))[X_b]
  = D(b) Delta(E) Delta'(E),

D_source (r_D(p,a(p)))[X_b]
  = D(b) Delta(E) Delta'(E) / (2 (E-b) D'(E))     (b != E),

D_source (r_D(p,a(p)))[X_E] = -Delta(E) Delta'(E) / 2.
```

Actual Dirichlet simplicity justifies the off-diagonal D'(E) denominator.
These formulas include a Dirichlet point at a bandedge and zero energy.
They never divide by r_D(E), which can vanish at a bandedge.

## Proof chain and declaration map

- `ClassicalHillDirichletSlopePairing`: actual scalar IVP boundary identities
  for squared solutions and their polarization. Its trace-kernel identity
  retains the first-energy cosine-sine factor.
- `HillDirichletSlopeVariation`: actual rough L2 source derivative and exact
  physical integral expression, obtained from the verified transfer map and
  its kernel, with all signs and constants proved.
- `HillDirichletGardnerSlope`: actual state and Dirichlet-label continuity
  transfer the endpoint identity from real finite Fourier truncations to
  real period-one L2 potentials. Public declarations are
  `hillDirichletSlope_gardner_cross_identity` and
  `hillDirichletSlope_gardner_diagonal`.
- `HillDirichletSheetVariation`: `hillDirichlet_wronskian_energy_factor`
  derives the energy relation from the actual monodromy determinant,
  including E=0 via a punctured quadratic limit. The genuine moving chain
  rule and already proved Dirichlet-branch variation give
  `hillDirichletSheetRoot_moving_gardner_cross_identity`,
  `hillDirichletSheetRoot_moving_gardner_off_diagonal` and
  `hillDirichletSheetRoot_moving_gardner_diagonal`.

## Validation

Prior strict validation of all 862 unchanged selected sources; strict dependency-order compilation of four new proof modules; then a fresh combined transitive axiom audit of all 866 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 866-module rebuild is claimed.

Fresh audit: 8299 selected declarations and 30885 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors and default 200000 heartbeats;
no sorry, added axioms, heartbeat increases or linter exceptions.
All thirteen shared import records and the canonical reuse record are
unchanged. The four new modules are necessary reusable spectral proofs.

## Remaining article scope

The terminal-phase derivative is still to be evaluated using the actual
sine and cosine data, stationary gap data and moving deflated root. At a
terminal bandedge this needs both trigonometric identities, avoiding a
vanishing sine denominator. The existing Abelian primitive decomposition
then supplies the actual integral variation. Entire Dirichlet interpolation,
canonical angle orientation, closed-gap and infinite-tail angle variation,
and physical Hamiltonian frequency identities (69)/(84) remain open.

Full rough W and cross-chart compatibility, the exact leading scalar and
sharp root/moment bounds, weighted remainders and compact derivatives,
action/Birkhoff realization and PDE identification remain open. All main
theorem inventory rows remain OPEN. The finite-gap energy value identity
alone does not justify arbitrary Hamiltonian source differentiation.
