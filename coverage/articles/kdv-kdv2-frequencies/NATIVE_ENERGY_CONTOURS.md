# Native physical normalized families on free energy contours

There are eta>0, C>0 and one jointly complex analytic native Hilbert-valued numerator family G on all energies times the complex period-one L2 ball of radius eta. For every complex source in that ball and every k>=1:

- On the complete closed energy disc centered at (k*pi)^2 with radius k, the full output-index norm of G is at most C/k.
- On its boundary, the actual source-continued root is defined and nonzero, and the full Hilbert density norm is at most C/k.
- The density is genuinely Bochner circle integrable and its integral divided by 2*pi is exactly the k-th Hilbert basis vector.

The source ball and constant precede all complex sources, contours, energies and output indices. The same G retains exact free positive components, zero nonpositive components and its original frequency-circle Bochner periods. At every real physical source in the ball, every positive component at every energy is the existing globally selected physical normalized numerator. On every radius-k energy circle the actual continued root equals the canonical physical root, and the whole circle lies in that source's physical cut domain. Means, the first mode, the own output/contour index and closed gaps are included.

The main declaration is `NLS.Articles.KdVKdV2Frequencies.exists_hillPhysical_native_energy_contours` in `PhysicalEnergyContours.lean`.

These radius-k circles are smaller than the old intrinsic free-gap circles, whose radii are `(2*k-1)*pi^2/4`. No equality of those radii is assumed.

## Proof

`HillHminusOneUniformAnnularRoot` extends the free sine separation and actual rough root coverage from individual frequency circles to complete closed frequency annuli, uniformly before all positive indices on one radial complex rough-source ball. It also gives an actual root upper bound from the trace bound.

`FreeEnergyCircleFrequencyBounds` puts the principal frequencies of every radius-k energy circle inside the pi/8 frequency disc and at distance at least 1/(4*pi) from its free center. `SquaredDiscNormBound` applies the Banach-valued maximum modulus principle to the entire energy numerator composed with squaring. `HillNativeEnergyDensityTransfer` combines this with the already proved pi/8 density bound and actual annular root bounds; another maximum-modulus step fills the entire energy disc. The existing physical family is retained, rather than normalized again.

`SquaredCircleAffineIntegral` gives the exact scalar squared-circle pullback whenever its actual smooth affine homotopy stays in the analytic domain. `HillFreeEnergyHomotopyGeometry` proves that the deformation between the radius-k energy circle and the square of the pi/16 frequency circle stays in the energy shell between k and pi^2*k/4. Its principal frequencies lie on the already covered annuli, including at the first mode.

`HillHminusOneEnergyPeriodTransfer` first shrinks the original pi/4 frequency circle through the actual covered annulus to pi/16, then applies that squared-circle homotopy. It proves the exact scalar period identity for any entire numerator at every complex rough source in one source ball, retaining the original root sheet, orientation and 2z Jacobian. Bounded coefficient evaluation commuting with genuine Bochner integrals transfers the complete native Kronecker vector period to the energy circle.

`HillRadiusEnergyCirclePhysicalRoot` proves that each radius-k circle lies in the full free physical cut domain. Source compatibility and indexed-band preservation then identify its actual rough/L2 root with the canonical physical root at every real source where continuation is defined. `PhysicalEnergyContours` assembles all properties on one common complex L2 ball by restricting the previously identified physical family.

## Remaining main obligations

This is a quantitative normalized-differential dependency near the zero L2 source. It does not prove a filled regular phase or native physical Abelian-coordinate analyticity. Next subtract the own unit-period term, prove uniform analytic filling and primitive estimates through each gap, and establish genuine complex divisor/amplitude sequence bounds. The full Sobolev-scale coordinate realization, canonicality, global Birkhoff inverse, Hamiltonian action frequencies, rough-W sharp estimates and infinite-gap/action/PDE-flow conclusions remain essential. All eleven main theorem rows remain OPEN.

## Validation

Prior strict evidence for all 1142 unchanged selected baseline sources; strict dependency-order compilation of nine new proof modules; then a fresh combined transitive axiom audit of all 1151 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1182 frozen source/checker/provenance hashes, all 29 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1151-module rebuild is claimed.

Fresh audit: 10488 selected and 32652 imported NLS declarations. Nine new modules, 16 explicit theorems including private helpers and 0 definitions; no new canonical or shared source imports. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
