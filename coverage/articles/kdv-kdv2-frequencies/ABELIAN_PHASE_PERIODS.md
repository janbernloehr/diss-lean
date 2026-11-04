# Physical Abelian phase, period duality and time orientation

## Actual phase and contour tangents

`hillDirichletAbelianPhase` defines the branch-independent physical phase
at an open selected gap by

```text
P_n(q) = -(cosine_n(q) + i sine_n(q)) exp(i summed_regular_n(q)).
```

The cosine and sine are the actual Dirichlet terminal/signed-sheet data.
Every actual sheeted terminal angle epsilon gives exactly
`P_n = exp(i (epsilon_n - pi + summed_regular_n))`.
The sum is the previously proved absolutely convergent physical correction
sum, not a supplied model. The selected n-th gap must be open; every other
gap may be closed. Terminal bandedges and angle branch cuts are included.

`exists_hillDirichletAbelianPhase_analytic_variation` constructs genuine
local complex L2 analytic extensions. `norm_hillDirichletAbelianPhase`
proves unit norm on real data, and `continuousOn_hillDirichletAbelianPhase`
proves continuity throughout the full real open-gap locus.
`fderiv_hillDirichletAbelianPhase_extension` proves that every differentiable
extension matching near real potentials has the same trace-direction
variation:

```text
D P_n(q)[X_b] = (-i psi_n(q,b)/2) P_n(q),     all complex b.
```

`unitCurveCoefficientsCLM` realizes actual unit-period Fourier integrals
as a bounded complex-linear map with norm at most one. It has exact
Parseval and agrees with the existing endpoint-matching physical Fourier
realization. `continuous_hillL2DiscriminantGardnerDirection_energy` proves
norm continuity of the actual tangent X_b on the entire complex energy
plane, including zero and the principal square-root cut. This follows by
rough-source approximation and closed-map descent through squared frequency.

For each positive m, `hillL2TracePeriodDirection` is the genuine coefficient
Bochner contour integral

```text
Y_m = -1/pi * contour_m X_b / R(b) db,
```

with the actual canonical root R and intrinsic gap contour. Circle
integrability and passage of every continuous linear functional through
this integral are proved. Every actual discriminant is stationary along
Y_m. The proved actual periods give exact orientation data

```text
D A_n[Y_m] = delta_(m,n),
D P_n[Y_m] = i delta_(m,n) P_n.
```

A_n is the previously constructed raw local Abelian angle. These are
proved statements about literal physical Fourier tangents and actual
Abelian data. Identifying Y_m with the Hamiltonian direction of the
physical action, and identifying the source's canonical Birkhoff angle,
remain required. No action model or Birkhoff map is silently assumed.

## Corrected physical time sign

The source uses Fourier coefficients paired against `exp(+i 2 pi n x)`
with the Hermitian L2 inner product (PDF p.2), hence reconstruction waves
`exp(+i 2 pi n x)`. Equations (1)-(3) have the actual linearized operators
`-d_x^3` and `d_x^5`. Lean proves, for every integer n and physical x,

```text
-d_x^3 exp(i 2 pi n x) = +i (2 pi n)^3 exp(i 2 pi n x),
 d_x^5 exp(i 2 pi n x) = +i (2 pi n)^5 exp(i 2 pi n x).
```

`hasDerivAt_kdvRHS_zero_unit_wave` and
`hasDerivAt_kdv2RHS_zero_unit_wave` obtain these signs by differentiating
the complete nonlinear physical fields at zero. The first-mode inequality
`linearKdV_first_wave_ne_negative` explicitly rules out the opposite sign.
These statements concern the complexifications of the actual real PDEs.

Thus the unnumbered p.3 display with `z_n' = -i omega_n z_n` is inconsistent
with the equations and the stated Fourier differential of Theorem 1.1.
The physical positive-mode flow is `exp(+i t omega_n)`, as in (80)/(91),
with the negative exponent at negative signed modes. The frequency
convention `omega_n = d H/d I_n` and its positive leading cubic/fifth-order
constants are retained. With bracket (3), evolution of any functional F
along the PDE is `{F,H}`; an angle with `{I,theta}=1` evolves by
`theta'=-dH/dI`. The source's displayed positive theta evolution likewise
needs this time-convention qualification.

`SignedPhaseFlow` now uses the physical sign. `TimeOrientation` proves
its exact positive-mode exponential and scalar time derivative. Both
compact-time and fixed-time nonextension adapters are ported to the same
positive physical exponent. The original generic negative-sign phase-gap
theorem remains proved, with a new positive-sign counterpart. All generic
group, topology, reality, mass and phase-separation conclusions are retained.
This corrects the earlier coverage choice to follow the p.3 time sign.

This is not yet an identification of generic coordinate flow with the
actual spectral Birkhoff evolution or with smooth PDE solutions.

## Validation

Prior strict evidence for the 965-module baseline; all 960 unaffected source files and nineteen provenance records remain unchanged. Strict dependency-order rebuild of all six affected prior selected modules, including five changed source files, and all five new modules; then a fresh combined transitive axiom audit of all 970 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, frozen source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No full 970-module rebuild is claimed.

Fresh combined audit: 8988 selected declarations and 31527 imported NLS
declarations, with only propext, Classical.choice and Quot.sound.
Lean4.33.1/mathlib4.33.1, warnings as errors, default200000heartbeats.
No sorry, added axioms or heartbeat/linter exceptions. No new branch
sources or canonical helpers were imported; all fourteen shared and five
canonical provenance records are unchanged and reverified.

## Remaining article scope

Physical action-gradient identification of Y_m, canonical angle orientation,
closed-own-gap analytic Birkhoff coordinates, full rough W and all chart
compatibilities, actual Hamiltonian frequency identities (69)/(84), sharp
leading scalars and root/moment bounds, weighted remainders/compact
derivatives, action descent and physical PDE realization remain open.
All eleven main inventory rows remain OPEN.
