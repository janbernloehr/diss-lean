# Actual local Hill resolvent and cubic frequency kernel

## Actual full-plane WKB columns

The genuine finite Riccati WKB vector and the actual IVP solution with
its own initial value differ by at most

```text
C/(2*||z||)^N * exp(abs(Im z)*t),        0<=t<=1,
```

on the ENTIRE complex frequency plane, at every truncation order.
The original potentials are smooth complex period-one functions. Constants
depend on the potentials and truncation order; no source-uniform Sobolev
ball claim is made here.

The canonical signed-swap symmetry exchanges actual solution components
under (a,b,z)->(-b,-a,-z). The canonical physical Hamiltonian phase identity
makes the two periodic endpoint multipliers exact reciprocals. These two
unchanged helpers are already transitively present at the baseline and
are now explicitly selected and strictly compiled; source and local bytes
are recorded in `CANONICAL_WKB_SWAP_PHASE_REUSE.json` against main c5bcf634.

Both initial WKB coordinates tend to zero. Their actual initial basis has
nonzero determinant and inverse determinant norm at most 2 on a common
large-frequency exterior. Exact first-row two-column algebra therefore
approximates the ACTUAL upper-right monodromy entry to every inverse
frequency order, retaining the natural exp(abs(Im z)) factor.

## Exact scalar Dirichlet normalization

For the actual constant-upper specialization (-1,-Q), the scalar change
of state gives the literal identity D(z^2)=i*M01(z). Thus both column
bounds yield an all-order estimate for the actual Dirichlet characteristic
of the physical Fourier potential Q. No reality or mean-zero assumption
is required for this Dirichlet estimate.

The approximation has the exact form

```text
D_model = g*(m-m^(-1)),
g = -s/(1+r*s),
r = actual_RiccatiApprox(-1,-Q,N,(2iz)^(-1),0),
s = actual_RiccatiApprox(Q,1,N,-(2iz)^(-1),0),
m = exp(actual_finite_Hamiltonian_phase).
```

The actual initial-basis bounds prove |g|<=1 on a common exterior.

## Actual root division and local coefficient

For real smooth period-one sources, the already proved actual primitive
F(z^2) is uniformly close to the actual finite Hamiltonian phase on the
chosen quarter frequency arcs. Squaring those arcs gives the upper energy
semicircles. The root R=2*sinh(F) is the ACTUAL real-cut root.

Free half-lattice sinh separation and proved weighted sinh difference
bounds give a uniform positive lower bound for exp(-Im z)*|R| and an
all-order bound for the weighted error R-(m-m^(-1)). Combining this with
the actual Dirichlet estimate justifies division by the actual root:
D/R is approximated by g with all-order inverse-frequency errors on
these arcs, including their closed endpoints.

The actual order-four Riccati polynomials have local inverse-frequency
jet g=-w+2Q(0)w^3+O(w^4), w=(2iz)^(-1). Its rational remainder is an
explicit polynomial divided by the controlled nonzero initial-basis
determinant. Compact bounds for that polynomial give the uniform estimate

```text
r^4 * |D(z^2)/R(z^2) - i/(2z) - i*Q(0)/(4z^3)| <= C.
```

Here r is the chosen frequency radius. No mean-zero or finite-gap
assumption is required for this local actual resolvent result. The root
matches the already constructed canonical energy-product root on their
actual common cut domain. This record does not assert a new full-circle
root matching statement at the ground-cut endpoint.

## Actual cubic frequency kernel

For a real smooth period-one source with mean zero, the verified physical
primitive expansion gives r^3*|F(z^2)+iz|<=C. Combining it with the actual
local resolvent estimate proves

```text
r * |F(z^2)^3 * D(z^2)/R(z^2) + z^2/2 + Q(0)/4| <= C
```

uniformly on the chosen upper energy arcs. Equivalently, with lambda=z^2,

```text
F(lambda)^3 * D(lambda)/R(lambda)
  = -lambda/2 - Q(0)/4 + O(|lambda|^(-1/2)).
```

All coefficients and errors follow from actual IVP, primitive and root
constructions. No diagonal-resolvent asymptotic, normalized leading
constant or prescribed spectral flow is supplied as an assumption.
The positive physical Fourier time convention is preserved.

## Validation

Prior strict evidence for all 1064 unchanged selected baseline sources; strict dependency-order compilation of ten additions (two unchanged canonical symmetry/phase helpers and eight new proof modules); then a fresh combined transitive axiom audit of all 1074 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1102 frozen source/checker/provenance hashes, all 25 unchanged provenance records plus one new verified two-file canonical WKB reuse record, private fresh outputs and clean unchanged canonical main verified. No repeated full 1074-module rebuild is claimed.

Fresh audit: 9731 selected and 32167 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, additional
axioms, heartbeat overrides or linter exceptions. All existing selected
sources and all 25 existing provenance records are unchanged. The two
canonical helper source files are unchanged baseline files, now explicitly
selected; the new record verifies their canonical bytes.

## Main obligations remain

The cubic estimate is the quantitative local input needed to compare the
already proved actual finite-gap Dirichlet velocity contour with the
article's F^3*psi_n/R contour. Full-circle integrability/reflection and
exterior/finite-hole contour comparison still need proof before claiming
the actual Hamiltonian frequency identity (69).

The quintic local coefficient, actual translation coefficient and mass
renormalization for (84), closed-frequency identification, full canonical
brackets, Fourier zero jet, full native Banach map and inverse, rough W
compatibility, sharp estimates, action descent and actual PDE flow
existence remain open. A closed coordinate jet does not determine its
frequency. Do not differentiate a finite-gap-only Hamiltonian VALUE
identity as an open L2 germ. All eleven main theorem rows remain OPEN.
