# Actual Dirichlet kernels and interpolation exterior

## Entire filled kernels

`hillComplexDirichletGardnerKernel` is the literal moving divided difference
of the actual Dirichlet characteristic, divided by minus twice its energy
derivative at the moving Dirichlet root. The integral divided difference
fills the spectral diagonal. `analyticOnNhd_hillComplexDirichletGardnerKernel`
proves joint complex Banach analyticity on every actual simple-root chart.

`exists_hillDirichletGardnerKernel_joint_analytic_chart` constructs such a
chart near every real period-one L2 potential and every positive Dirichlet
index. It retains the genuine characteristic-zero branch and matches the
physical filled kernel at every spectral value for nearby real potentials.
`analyticOnNhd_hillDirichletGardnerKernel` proves that this physical kernel
is entire in its spectral argument, including zero energy and the diagonal
value -1/2. No global analytic square-root branch is selected.

## Weighted actual Dirichlet estimate

The actual scalar sine IVP has the full-plane error bound

```text
|D_q(z^2) - sin(z)/z| <= 4 exp(|Im z|) ||q|| / |z|^2,
provided z != 0 and 4 ||q|| <= |z|.
```

Here q is any complex L2 Fourier potential and D is its actual characteristic.
The proof first weights the actual continuous scalar solution by exp(-H*t).
The Duhamel weights at times t-s and s multiply to exp(H*t), so the genuine
Volterra smallness condition is potential mass divided by frequency, with
no additional imaginary-frequency exponential. A sup-norm argument gives
the actual solution bound and free error. Finite Fourier truncation and
actual characteristic continuity then give the rough L2 estimate.

`exists_hillL2Dirichlet_exterior_lower_bound` combines this with the verified
free sine bound. For every fixed positive distance from the free lattice,
one reciprocal constant works on every bounded complex L2 potential ball,
after one common frequency cutoff. The actual characteristic is nonzero
there and exp(|Im z|) is bounded by a constant times |z|*|D_q(z^2)|.

## Actual quotient and outer Cauchy decay

The exact free entire numerator identity is

```text
z ((n*pi)^2-z^2) psi_n,free(z^2) = 2 n pi sin(z).
```

`hillFreeAbelianPsi_frequency_identity` derives it from the verified actual
canonical product normalization, with no cut or zero-energy exception.
The weighted-product exterior bounds then give, for every complex Hilbert
numerator coordinate a and bounded complex L2 potential family,

```text
|psi_n,Hilbert(z^2,a) / D_q(z^2)|
  <= C exp(||a|| * hillExteriorWeightBound) / |z|^2.
```

`exists_hillAbelianSelectedGlobalPsi_dirichlet_exterior_bound` instantiates
this with the actual globally selected normalized numerator at every real
period-one L2 potential. Its quotient has inverse-energy decay on the full
separated exterior. No Dirichlet product formula or interpolation identity
is assumed; the actual Dirichlet IVP supplies the denominator lower bound.

`eventually_hillAbelianSelectedGlobalPsi_dirichlet_circle_bound` proves
actual zero-free expanding energy circles and the inverse-radius quotient
bound on them. `eventually_hillDirichlet_outerCauchy_small` proves that

```text
integral_circle psi_n(E) / D_q(E) / (E-w) dE
```

tends to zero uniformly for every bounded family of evaluation energies w.
These are the actual outer errors needed by the finite simple-pole Cauchy
formula, not errors of a model characteristic or a prescribed interpolation
series.

## Validation and reuse

Prior strict validation of all 870 unchanged selected sources; strict dependency-order compilation of one byte-identical canonical sine-exterior helper and five new proof modules; then a fresh combined transitive axiom audit of all 876 selected modules. The reused helper precedes every selected transitive consumer. Exact checker/audit/coverage/evidence selections, full transitive selected dependency order, source/provenance hashes, private fresh outputs and clean unchanged canonical main verified. No repeated full 876-module rebuild is claimed.

Fresh audit: 8376 selected declarations and 30953 imported NLS declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively.
Lean 4.33.1, mathlib v4.33.1, warnings as errors and default 200000 heartbeats;
no sorry, added axioms, heartbeat increases or linter exceptions.
Thirteen shared import records and both previous canonical reuse records
are unchanged. `CANONICAL_SINE_EXTERIOR_REUSE.json` records the unchanged
sine helper from canonical main. No new branch sources were imported.

## Remaining article scope

The actual finite-residue expansion and its limiting entire Dirichlet
interpolation identity still need to be assembled. Its zeros must be matched
to the gap-indexed Dirichlet labels, including the low spectral exterior.
The actual infinite sum of Abelian integrals, analytic convergence and source
differentiation, collapsed-gap contributions and canonical angle orientation
remain open. Thus the full angle/discriminant identity and physical frequency
identities (69)/(84) are not yet proved.

Full rough W and chart compatibility, exact leading scalar and sharp root/
moment bounds, weighted remainders and compact derivatives, action/Birkhoff
realization and PDE identification remain open. All eleven main inventory
rows remain OPEN. The finite-gap energy value identity alone does not justify
arbitrary Hamiltonian source differentiation.
