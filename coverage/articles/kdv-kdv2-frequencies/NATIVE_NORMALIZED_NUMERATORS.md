# Native normalized differential numerator family near zero

The actual Miura-normalized entire Hill differential numerators now have a single jointly complex analytic realization

    F : complex energy × PeriodOneHminusOne → Coeff 2

on one complex source ball around zero, before every positive output index. Its positive components are exactly the existing actual `hillHminusMiuraEnergyPsi`; its nonpositive components are zero. The free positive components are exactly `classicalHillFreePsi`.

The construction uses the already proved common analytic inverse of the actual period operator. If b(E,q) denotes the actual critical numerator Hilbert vector, then

    F(E,q) = transpose(R(q)) b(E,q),
    ||F(E,q)||_2 <= ||R(q)|| ||b(E,q)||_2.

The transpose is bilinear, with no complex conjugation in the coefficient pairing. The proof uses the canonical Hilbert cotangent isometry and bounded composition, so it establishes native Banach analyticity directly. It does not infer norm analyticity from separate scalar germs.

Near every energy-source point, a single neighborhood and positive constant bound the full Hilbert norm and every positive actual Miura numerator simultaneously. This local neighborhood can depend on the energy-source point; no bound uniform over unbounded energies or contour index is asserted.

For every positive contour index k and every complex source in the same source ball, the whole normalized one-form is genuinely Bochner integrable, and its literal frequency-circle integral satisfies

    (2*pi)^(-1) integral_circle (2*z/root(z^2,q)) * F(z^2,q) dz = e_k.

This is an equality in the full output Hilbert space. The nonpositive identity block of the actual period matrix and its inverse proves the zero extension, so no additional unconstrained output components are introduced.

The article declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_actual_native_normalized_numerators`. Shared constructions and proofs are in `HillHminusOneNormalizedNumeratorSequence`, `HillHminusOneNormalizedSequencePeriods`, and `HilbertMatrixTransposeAnalytic`.

This is a dependency toward the common-neighborhood estimates needed for the main theorems. It concerns normalized differential numerators. It does not identify this near-zero family with the globally selected physical differential at all real L2 sources, and it does not assemble the physical Abelian coordinates into a native complex analytic map. Uniform control of the regular phases, complex terminal divisor bounds, the full Sobolev scale, canonical brackets, global inverse, Hamiltonian/action-frequency identification and the remaining rough-frequency estimates are still required. All eleven main theorem rows remain OPEN.

## Validation

Prior strict evidence for all 1108 unchanged selected baseline sources; strict dependency-order compilation of twelve byte-identical canonical Hilbert-transpose dependencies and four new proof modules; then a fresh combined transitive axiom audit of all 1124 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1154 frozen source/checker/provenance hashes, 27 unchanged and one new verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1124-module rebuild is claimed.

Fresh audit: 10386 selected and 32558 imported NLS declarations. Four new modules, 11 explicit theorems and 1 definition; twelve unchanged canonical dependency sources selected with exact provenance. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
