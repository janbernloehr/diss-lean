# Unique physical action Hamiltonians and mixed coordinate identities

## The actual physical weak identity

For a continuous unit-interval test curve f, `hillPhysicalCurvePairing f`
is a genuine bounded complex-linear functional on the original L2 Fourier
source. Its definition uses `hillPhysicalDirection`, the actual interval-L2
Volterra pairing, and endpoint evaluation. Its value is exactly

```text
L_f(h) = integral_0^1 f(x) [-hillPhysicalDirection(h).lower(x)] dx.
```

The first-order-system minus sign is removed, so this is the actual
unconjugated physical source pairing. No functional or physical
realization is supplied as a hypothesis.

`HillPhysicalGradientPairing` proves absolute continuity, integrability of
the actual derivative, and periodic endpoint matching of the rough Hill
trace gradient. Its proved spatial derivative gives integration by parts
against every periodic absolutely continuous test with integrable derivative.
The actual even Fourier coefficient realization of each continuous
endpoint-matching physical curve is proved, as is the corresponding trace
source-derivative integral. All six former private proofs are now selected.

Passing the bounded test functional through the genuine Bochner contour,
and using the exact physical action derivative, proves

```text
L_f(Y_m) = -D I_m[X_g],       g = f derivative,
X_g = periodDouble(unitCurveCoefficients(g)).
```

The tests include every periodic AC f whose actual derivative has a
continuous endpoint-matching representative g. Thus they include the full
smooth periodic test class. This is the physical weak identity
`Y_m = partial_x(gradient I_m)`, with the exact source period, sign and
action normalization. Every differentiable nearby-real action matching
extension is covered, and no open-selected-gap hypothesis occurs.

## Uniqueness from actual physical Fourier tests

`UnitWaveCurves` constructs the unit wave `exp(i 2 pi k x)` on the
physical interval for every integer k. Its endpoint matching, absolute
continuity and actual almost-everywhere derivative, including the
normalization `i 2 pi k`, are proved. These are actual members of the
weak test class, including zero and negative modes.

`hillPhysicalCurvePairing_unitWaveCurve` identifies their physical
pairings with the genuine normalized unit Fourier integrals. On the even
period-two source space these recover every even coefficient. Odd
coefficients vanish there, so the pairings separate all period-one L2
tangents. `IsHillHamiltonianDirection.unique` therefore proves uniqueness
for the full physical weak identity. The contour tangent has also proved
even support and zero mean.

`hillL2TracePeriodDirection_is_action_hamiltonian` and
`existsUnique_hillRealGapAction_hamiltonian_direction` identify the actual
contour tangent as the uniquely determined physical action Hamiltonian
vector, at every real source including closed selected gaps. The weak
identity is a definition of the physical differential relation; its
existence, actual action agreement and uniqueness are proved.

## Mixed physical identities and local angle orientation

`fderiv_hillRealAction_action_hamiltonian_eq_zero` proves actual action
involution. `fderiv_hillAbelianCoordinate_action_hamiltonian` proves

```text
D z_n[X_(I_m)] = i delta_(m,n) z_n.
```

The direction is characterized by the proved physical weak identity;
the identities are not consequences of a hypothesized abstract action
model. They cover every differentiable matching coordinate/action
extension and arbitrary closed selected and other gaps.

`exists_hillActionOrientedAbelianAngle` constructs a genuine local
complex analytic angle at each real source with open selected gap. It is
real on nearby real sources, its actual phase is `exp(-i theta_n)`, and

```text
D theta_n[X_(I_m)] = -delta_(m,n).
```

It is minus the previously constructed raw Abelian angle. This proves
the mixed action-conjugate orientation compatible with the previously
verified positive Fourier time exponent. It does not identify a particular
book sheet/gauge or prove all angle-angle or coordinate-coordinate brackets.

## Reuse and validation

The canonical `AbsoluteContinuousCoefficients` helper is reused byte-identically
from `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`, selected before every selected
transitive consumer and strictly compiled at default heartbeats. Its record
is `CANONICAL_HAMILTONIAN_TESTS_REUSE.json`. All 996 baseline selected sources
and all 22 prior provenance records remain unchanged. No branch source or
local variant was replaced.

Prior strict evidence for all 996 unchanged selected baseline sources; strict dependency-order compilation of one byte-identical canonical wave calculus helper and five new proof modules; then a fresh combined transitive axiom audit of all 1002 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1027 frozen source/checker/provenance hashes, 23 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1002-module rebuild is claimed.

Fresh audit: 9274 selected and 31820 imported NLS declarations, only
`propext`, `Classical.choice`, `Quot.sound`. Lean4.33.1/mathlib4.33.1,
warnings as errors, default200000heartbeats. No sorry, added axioms,
heartbeat overrides or linter exceptions.

## Remaining main-theorem obligations

The physical action Hamiltonian vector and mixed identities are proved.
An explicit real-vector declaration and further canonical angle/coordinate
brackets, exact Fourier differential at zero, full Banach-valued complex
analyticity and inverse, rough negative-regularity and W/chart compatibility
remain required. Actual Hamiltonian frequency identities (69)/(84), sharp
estimates, action descent and physical PDE realization remain open.
All eleven main theorem rows remain OPEN and the goal is incomplete.
