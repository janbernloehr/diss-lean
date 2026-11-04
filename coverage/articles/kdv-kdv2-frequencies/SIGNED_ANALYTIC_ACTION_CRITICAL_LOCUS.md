# Signed scalar analyticity and the actual action critical locus

## Genuine negative-coordinate complex analyticity

`ConjugateAnalytic.analyticAt_star_star` proves that conjugating both
source and target preserves complex Banach analyticity. The argument uses
an actual open neighborhood of analytic points. The two conjugate-linear
involutions reverse scalars twice, so the transported map is complex
Frechet differentiable throughout that neighborhood. The verified canonical
holomorphic calculus then supplies a convergent local power series.
Differentiability at a single point is not used to infer analyticity.

`exists_hillNegativeAbelianCoordinate_analytic_extension` applies this to
the actual positive scalar coordinate extension and bounded Fourier
reflection. At every real period-one L2 potential, including a closed
selected gap, it constructs an actual complex analytic H with a single
nearby-real physical matching germ

```text
H(p) = conjugate(z_n(p)).
```

This closes the negative scalar power-series gap recorded in
`REAL_SIGNED_ACTION_FIELDS.md`. It does not prove the full sequence-valued
map analytic, for which a common neighborhood and native-norm complex
bounds are still required.

## Actual action differential on every physical tangent

`fderiv_hillRealAction_eq_coordinate_product` proves, for every matching
differentiable extension A,Z,W of the actual action and signed coordinates,

```text
D A[v] = z_n D W[v] + z_-n D Z[v]
```

for every complex period-one tangent v. The equality uses actual nearby-real
matching, the exact normalization `norm(z_n)^2=I_n`, the product rule, and
the proved real-source uniqueness of physical complex derivatives. It
assumes no off-real product identity for the chosen extensions.

At a closed selected gap both actual signed coordinates vanish. Therefore
`fderiv_hillRealAction_closed_eq_zero` proves the action differential is zero
on the entire complexified physical tangent space, not merely on the
previously considered trace or contour directions.

## Critical and Hamiltonian zero loci

`IsHillHamiltonianDirection.eq_zero_of_action_closed` uses the full weak
Gardner test class and verified uniqueness to prove every actual action
Hamiltonian vector vanishes at its closed selected gap. The zero vector
satisfies the weak identity because every test derivative has the proved
physical even insertion and the action differential vanishes there.

Conversely, if the actual normalized contour vector Y_n vanishes, its
already proved physical coordinate variation `D z_n[Y_n]=i z_n` forces
`z_n=0`, hence the selected gap is closed. Thus
`hillL2TracePeriodDirection_eq_zero_iff_closed` proves

```text
Y_n = 0  iff  the n-th gap is closed.
```

The same weak uniqueness argument gives
`fderiv_hillRealAction_vanishes_iff_closed`:

```text
D I_n[v] = 0 for every physical complex tangent v
    iff the n-th gap is closed.
```

These are actual action and Fourier Hamiltonian-vector identities at every
real L2 source, including arbitrary other closed gaps. No flow construction
or physical Hamiltonian-frequency identity is supplied as a hypothesis.

## Validation and reuse

Sixteen canonical dependency sources are byte-identical to main commit
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. The complete reused holomorphic
calculus closure is selected before all transitive selected consumers,
strictly compiled privately at default heartbeats and combined-audited.
See `CANONICAL_CONJUGATE_ANALYTIC_REUSE.json`. All 1008 baseline selected
sources and all 24 prior provenance records are unchanged.

Prior strict evidence for all 1008 unchanged selected baseline sources; strict dependency-order compilation of sixteen byte-identical canonical holomorphic calculus dependencies and three new proof modules; then a fresh combined transitive axiom audit of all 1027 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order and audit reachability, 1054 frozen source/checker/provenance hashes, 25 provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1027-module rebuild is claimed.

Fresh audit: 9402 selected and 31847 imported NLS declarations. Only
`propext`, `Classical.choice`, `Quot.sound`; Lean4.33.1/mathlib4.33.1,
warnings as errors and default200000heartbeats. No sorry, added axioms,
heartbeat overrides or linter exceptions.

## Remaining main obligations

Full Banach-valued coordinate analyticity, full canonical coordinate and
angle brackets, the Fourier differential at zero, global inverse and
rough W/chart compatibility remain open. Actual Hamiltonian frequencies
(69)/(84), sharp estimates, action descent and physical PDE realization
remain required. In particular, the already proved finite-gap quartic
Hamiltonian value identity is not differentiated as if it held on an open
L2 source neighborhood. All eleven main theorem rows remain OPEN.
