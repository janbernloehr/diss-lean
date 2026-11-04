# Physical action derivatives and all-gap Abelian coordinate variation

## Actual analytic action and its derivative

`hillLocalContourAction` is the literal Arnold contour integral

```text
J_n(p) = (1/pi) contour_n E Delta_E(p,E)/R_local(E,p) dE.
```

The fixed circle is the base real potential's actual intrinsic gap contour.
`R_local` is the actual jointly analytic root chart, normalized to the
physical canonical root there. `exists_hillLocalContourAction_analytic_neighborhood`
provides an open complex L2 source neighborhood. One simultaneous
nearby-real matching germ identifies `J_n` with the actual real Hill action
`I_n`, by the already proved physical root matching, contour comparison
and Arnold formula. The selected gap may be closed.

`TraceRootVariation` differentiates the actual root relation
`R^2=Delta^2-4`; every nonzero root satisfies `DR=Delta DDelta/R`.
Mixed analytic derivative symmetry and the quotient rule then give

```text
D_p(Delta_E/R)[h] = d_E(D_p Delta[h]/R).
```

`TraceActionVariation` differentiates the literal contour using the
proved compact-contour Banach differentiation theorem and integrates the
exact energy derivative by parts. No primitive or preassigned gradient
is assumed. The result, with the physical source normalization, is

```text
D J_n(q)[h] = -(1/pi) contour_n D_p Delta(q,E)[h]/R(q,E) dE.
```

This holds in every complex L2 source direction for the constructed
extension. `fderiv_hillRealGapAction_extension_apply` proves the same
formula for every differentiable extension matching the actual physical
action near real sources, on every period-one (even period-two Fourier)
tangent. Restriction to that tangent space is explicit because real
period-one physical data do not determine arbitrary odd source jets.

## Actual spectral stationarity and coordinate variation

The actual trace involution makes `D I_n[X_b]=0` for every complex trace
energy b. Passing continuous linear functionals through the genuine
Bochner contour gives `D I_n[Y_m]=0` for every normalized contour tangent.
The tangents `Y_m` are also proved to have even support and zero mean.
No action-model or involution hypothesis is supplied.

For an open selected gap, `sqrt(J_n)` is a genuine analytic local amplitude
whose trace-direction derivative is zero. Multiplying it by the proved
actual analytic phase gives the physical coordinate variation. At a
closed selected gap, the already proved analytic coordinate extension
and its zero trace derivative give the same formula, since `z_n=0`.
Physical real-source jet uniqueness makes this universal for every
differentiable nearby-real matching coordinate extension:

```text
D z_n[X_b] = (-i psi_n(b)/2) z_n,
D z_n[Y_m] = i delta_(m,n) z_n.
```

The normalized genuine differential periods prove the second identity.
Both identities retain closed selected gaps, closed other gaps, terminal
bandedges, filled spectral diagonals and zero trace energy. They are
actual physical coordinate identities; no arbitrary target chart is
substituted for the constructed Abelian map.

## Validation and reuse

Three canonical helpers are reused byte-identically at fixed canonical
commit `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`: mixed spectral/source
symmetry, the scalar quotient derivative, and polynomial closed-circle
integration by parts. Their record is `CANONICAL_ACTION_VARIATION_REUSE.json`.
They are selected before all selected transitive consumers and strictly
compiled at the default heartbeat limit. All 988 prior selected sources
and all 21 prior provenance records remain unchanged. No branch source
or local variant was replaced.

Prior strict evidence for all 988 unchanged selected baseline sources; strict dependency-order compilation of three byte-identical canonical calculus helpers and five new proof modules; then a fresh combined transitive axiom audit of all 996 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1020 frozen source/checker/provenance hashes, 22 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 996-module rebuild is claimed.

Fresh audit: 9210 selected declarations and 31761 imported NLS
declarations, only `propext`, `Classical.choice`, `Quot.sound`.
Lean4.33.1/mathlib4.33.1, warnings as errors, default200000heartbeats.
No sorry, added axioms, heartbeat overrides or linter exceptions.

## Remaining source obligations

The contour derivative is the actual action differential. Identification
of `Y_m` with its physical Gardner Hamiltonian vector still needs the
Fourier/physical gradient-pairing and spatial-derivative bridge. Without
that step, diagonal variation along `Y_m` is not asserted as a canonical
bracket theorem. Source angle orientation, full Banach-valued analyticity,
the exact Fourier differential at zero, global inverse, negative-regularity
and rough W/chart realization remain open. Actual Hamiltonian frequency
identities (69)/(84), sharp estimates, action descent and PDE realization
are required for the remaining main conclusions. The prior positive
physical Fourier time convention is retained unchanged.
All eleven main inventory rows remain OPEN; the goal remains incomplete.
