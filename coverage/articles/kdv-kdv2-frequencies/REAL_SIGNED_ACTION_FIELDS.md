# Real physical action fields and signed coordinate variation

## Actual real differentials and Fourier conjugation

`fderiv_hillRealAction_real_direction` proves that every differentiable
nearby-real physical action extension takes real period-one tangent
directions to real scalar derivatives. The proof follows genuine real
affine curves in the actual real potential space and applies the local
real-axis derivative theorem. No off-real reality of the extension is
assumed.

`fderiv_hillRealAction_conjugate_direction` complexifies those real
directions and proves

```text
D I_n[star(reflection v)] = conjugate(D I_n[v])
```

for every period-one complex tangent v. This uses physical conjugate
reflection, not coefficientwise reality. Both formerly private real-jet
proofs are now selected, combined-audited and published.

`UnitCurveConjugation` proves exact physical compatibility of the bounded
unit-interval Fourier analysis map with conjugation, and compatibility
with canonical even insertion into the period-two source. Conjugating an
actual unit wave or its actual normalized derivative reverses its frequency.

## Actual action Hamiltonian fields are real

The already proved weak Hamiltonian identity is tested on the verified
unit Fourier waves. It expresses each even coefficient of the action
Hamiltonian vector as a derivative of the actual action in the corresponding
actual wave-derivative direction. The conjugacy results above then give

```text
Y_m(-k) = conjugate(Y_m(k)),     all integer k.
```

Odd coefficients vanish by the proved even support. This proves
`hillL2TracePeriodDirection_isReal` for the literal normalized contour
vector at every real period-one L2 source, including arbitrary closed
selected gaps. `IsHillHamiltonianDirection.isReal_of_action_matching`
proves the same for every weak Hamiltonian vector matching the actual action.
Together with the proved zero mode, the vector is a genuine real mean-zero
physical tangent. No solution flow is claimed merely from this tangent
statement.

## Genuine negative-coordinate germs and signed variation

`fderiv_conjugate_of_real_line_eventuallyEq` proves that conjugate values
on a nearby real line determine conjugate complex source derivatives in
that direction. Its physical version follows actual real affine source
curves and applies to arbitrary differentiable nearby-real matching
extensions.

The negative scalar coordinate is the actual `z_-n=conjugate(z_n)` on real
data. A genuine complex differentiable matching extension through every
closed gap is constructed from the positive analytic extension Z by

```text
H(p) = conjugate(Z(star(reflection p))).
```

Complex differentiability follows from conjugating both source and target
and composing with the bounded Fourier reflection. On every actual real
source, the source involution fixes p, so one genuine physical matching
germ is retained. This step asserts differentiability; it does not assert
an unproved Banach power-series representation for H.

The real action Hamiltonian vector can be used in the physical conjugate
jet theorem. The already proved positive-mode law therefore yields

```text
D z_n[X_(I_m)]  = +i delta_(m,n) z_n,
D z_-n[X_(I_m)] = -i delta_(m,n) z_-n.
```

The negative identity is proved for every differentiable matching
extension and every actual weak action Hamiltonian vector, using its
proved uniqueness. Both selected and other gaps may be closed. These are
actual physical coordinate identities, not a supplied signed flow model
or an assumed frequency/PDE identification.

## Validation and reuse

The canonical `LocalRealAxisDerivative` helper is reused byte-identically
from `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`, selected before every selected
transitive consumer and strictly compiled at default heartbeats. Its record
is `CANONICAL_REAL_ACTION_JETS_REUSE.json`. All 1002 baseline selected sources
and all 23 prior provenance records remain unchanged. No branch source or
local variant was replaced.

Prior strict evidence for all 1002 unchanged selected baseline sources; strict dependency-order compilation of one byte-identical canonical real-axis calculus helper and five new proof modules; then a fresh combined transitive axiom audit of all 1008 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1034 frozen source/checker/provenance hashes, 24 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1008-module rebuild is claimed.

Fresh audit: 9295 selected and 31840 imported NLS declarations, only
`propext`, `Classical.choice`, `Quot.sound`. Lean4.33.1/mathlib4.33.1,
warnings as errors, default200000heartbeats. No sorry, added axioms,
heartbeat overrides or linter exceptions.

## Remaining main-theorem obligations

Power-series analyticity of the negative matching germs, full canonical
coordinate/angle brackets, the exact Fourier differential at zero, the full
Banach analytic Birkhoff map and inverse, and rough W/chart compatibility
remain required. Actual Hamiltonian frequency identities (69)/(84), sharp
estimates, action descent and physical PDE realization remain open. The
previous positive physical Fourier time convention is retained unchanged.
All eleven main theorem rows remain OPEN and the goal is incomplete.
