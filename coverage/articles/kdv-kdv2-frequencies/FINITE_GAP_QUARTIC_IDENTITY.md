# Exact physical quartic Hill contours at finite-gap potentials

This step proves the centered exterior-circle energy identity used at the
start of the proof of source Lemma 3.2, PDF page 26, preceding formula (69).
It also proves the actual real L2 finite-gap exterior consequence of source
Lemma 2.6(i), PDF page 15. It does not prove the angle–Poisson or Hamiltonian
frequency identity.

## Actual finite-gap exterior

`HillFiniteGapExterior.lean` defines `HillFiniteGap` by finiteness of the
noncollapsed positive gaps in the intrinsic real Hill characteristic labels:
`{n : ℕ | 1 ≤ n ∧ lambda_(2*n-1) ≠ lambda_(2*n)}`. These are the actual
monodromy characteristic labels, with analytic multiplicities retained.
Finiteness is proved equivalent to collapse of all sufficiently high gaps.
No finite-gap cutoff or exterior analytic domain is supplied as an assumption.

The actual high-pair localization proves that the upper band labels are
unbounded. This and finite real band coverage classify every sufficiently
large real energy. The finitely many possibly open positive gaps lie inside
one bounded disc; high collapsed points belong to the filled domain, and
energies below the ground state belong to the filled lowest cut. Nonreal
energies already belong to the actual cut domain.

Consequently one radius `R > 0`, chosen before every even exponent and both
contour radii, gives joint conclusions at each actual real L2 finite-gap input:

- Every even power `F^(2*m)` of the actual normalized primitive is analytic
  at every complex energy outside the disc.
- For all `m : ℕ` and all centered circle radii `r,s > R`, the literal
  counterclockwise integrals of `F^(2*m)` agree.

The annular Cauchy theorem is applied to the derived actual analytic exterior.
The primitive root signs and phases come from the existing normalized Hill
construction. The lowest cut and collapsed-gap removability are reused as
proved analytic facts, including all low indices and collisions.

## Exact physical energy coefficient

`HillFiniteGapQuarticEnergy.lean` combines this radius independence with the
previously proved actual smooth quartic contour limit. For every actual
`Q : C(AddCircle 2, ℂ)` which is real, smooth, period one, mean zero and
finite-gap in its intrinsic Hill spectral labels, it constructs `R > 0`
before every `r > R` and proves

`(2*pi*i)^(-1) * ∮_{|lambda|=r} F(lambda)^4 d lambda = -H1/4`.

Equivalently, the physical period-one Hamiltonian
`H1 = ∫₀¹ ((q')²/2 + q³)` is exactly `-4` times that normalized contour.
The actual Fourier parity and reality conditions are derived from the
physical function; they are not independent spectral hypotheses.

The argument proves eventual equality of the escaping physical circle
sequence to any fixed exterior period. Uniqueness of the already proved
physical limit then identifies that period. It does not assume a Laurent
coefficient, an energy identity, a contour-deformation equation or permission
to differentiate a pointwise limit.

## Shared reuse and scope

Ten dependency files are reused unchanged from the fixed estimates snapshot
`8bd9dcba2c439828221e11c08918ee632d16556e`. They give actual all-gap square
extensions, collapsed primitive removal, the filled ground square, intrinsic
gap-circle geometry and finite real band coverage. Seven compatible existing
local source variants are retained unchanged. The ninth provenance record,
`SHARED_FINITE_GAP_EXTERIOR_IMPORT.json`, records all source/local hashes.
No full branch merge, heartbeat override, warning or linter exception is used.

The statements retain a smooth physical potential hypothesis for the energy
identity, and a real L2 coefficient-space input for the exterior theorem.
They do not assert finite-gap regularity from rough data, all complex/global
source-neighborhood conclusions, general noncentered-loop identities, the
stronger displayed quartic remainder, angle brackets, physical frequency (69),
action descent, sharp weighted asymptotics, KdV2 frequency construction or
Birkhoff/PDE identification. All main theorem inventory rows remain open.

Validation reuses 509 unchanged previously checked selected sources, strictly
compiles ten unchanged selected shared imports and two new modules, then runs
a fresh combined transitive axiom audit of all 521 selected modules. This is
incremental validation, not a repeated full build. Matching checker/audit/
compilation-evidence/coverage selections, transitive dependency order, all
hashes, nine provenance records, private fresh outputs and unchanged clean
canonical main are verified before publication.
