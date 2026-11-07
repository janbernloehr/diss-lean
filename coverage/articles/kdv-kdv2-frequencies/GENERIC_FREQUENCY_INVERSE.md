# COMPLETE Corollary 1.4: actual real local frequency inverses

COMPLETE Corollary 1.4 is proved: for EVERY -1<s<-1/2, the ACTUAL KdV correction frequency has genuine REAL analytic two-sided local inverses on a relatively OPEN DENSE subset of the ENTIRE original nonnegative weighted ell(2s+1,1) action cone, containing ZERO. The complex extension is analytic near the whole cone. Its literal raw positive-frequency values agree there with ONE global weak scalar family chosen BEFORE all regularities and actions, with exact native Hamiltonian frequency recovery. The real inverse germs use the closed real subspace of the ORIGINAL weighted Banach space with its INHERITED norm. Both inverse identities hold on full real neighborhoods, including at zero and other boundary actions.

## Exact source match

Source Corollary 1.4 (PDF page 5) asserts, for every `-1<s<-1/2`, that `omega_1*:ell_+^(2s+1,1)->ell^(2s+1,1)` is a local diffeomorphism on an open dense subset containing zero. Its proof on PDF page 35 invokes Theorem 3.8(i)-(ii).

`NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData.corollary_1_4`

in `NLS/Articles/KdVKdV2Frequencies/Corollary14.lean` proves this COMPLETE statement, with genuine real analytic inverse germs and the literal original physical frequency values.

The one global weak scalar family G is chosen BEFORE all regularities and actions. It recovers the independently defined native Hamiltonian frequency minus `(2*n*pi)^3` at EVERY original real mean-zero H1 source and positive physical label. At every original nonnegative weighted action, the raw coefficient of the regularity-specific map equals G at the EXACT inclusion into the original weak action space. The same G calibrates every regularity. The frequency is real on the entire cone.

For each s there is ONE open complex domain containing the ENTIRE nonnegative action cone, with a genuinely Banach-analytic map into the SAME original weighted action space. The inverse locus is relatively open and dense in the WHOLE original cone and contains zero. At EVERY point of that locus, the real forward map is analytic and has a REAL analytic inverse with the exact center and both inverse identities on FULL real neighborhoods. Zero, closed coordinates and arbitrary infinite support are included.

## Original norms and real topology

`WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1))` is the original positive-frequency weighted ell1 Banach model, with literal raw positive labels. It is closed and complete. The normalized coefficient coordinates are a proved EXACT linear isometry. Nonpositive raw slots are fixed to zero.

`WeightedCoeff.PositiveSupportedActionCone` uses the original nonnegative cone with its SUBTYPE topology. `positiveActionConeHomeomorph` proves that its normalized cone is exactly the full nonnegative coefficient cone. Relative openness, density and zero transport through that homeomorphism.

`Coeff.coordinateRealSubmodule` is a CLOSED real subspace with the norm INHERITED from the original complex weighted action Banach space. `mem_positive_action_coordinateRealSubmodule_iff` proves that its elements are exactly the coefficientwise-real original actions. `coordinateReCLM` fixes every real action; `coordinateRestriction` agrees there with the original frequency after projection. Since the actual frequency is real on the full cone, that projection recovers its literal values at every original nonnegative action. Thus the inverse germs are actual REAL germs of the physical frequency map in the original norm.

`HasAnalyticInverse (𝕜 := ℝ)` means an actual map on this REAL Banach space, analytic at the image, recovering the original point, with `g(f(y))=y` and `f(g(z))=z` eventually on their FULL real neighborhoods. Together with the forward real analyticity this is the source local diffeomorphism assertion. No one-sided inverse or complex-only inverse is substituted.

## Exact origin normalization and Fredholm argument

For every intermediate order `-1<alpha<0`, the actual normalized intermediate frequency has value zero and FULL Frechet derivative `-6Id` at zero. This is derived from the actual physical Hilbert Hamiltonian Taylor formula through positive finite coordinate rays with their LITERAL original weights. A reusable basis derivative theorem identifies the full operator from these ray identities. It requires neither a bounded inverse inclusion nor equivalence between Hilbert and weighted ell1 norms, and covers the entire original intermediate range.

The already verified COMPLETE Theorem 1.2(ii) machinery supplies compactness of `dF+6Id` at EVERY original nonnegative intermediate action. The relative analytic Fredholm theorem applies to the preconnected full nonnegative cone, with the exact nonzero scalar shift `-6` and the invertible derivative at zero. Its derivative is analytic locally in the genuine Banach action topology. The resulting invertibility set is OPEN DENSE and contains zero; compactness is used exactly at the nonnegative parameters where it has been proved.

The canonical real cone inverse theorem supplies actual real inverses, including at boundary actions. It derives real preservation of both extension and inverse from cone reality. Linear conjugation transports these real germs and their two inverse identities to the ORIGINAL weighted coordinates. The actual original frequency map remains calibrated to G on the entire original cone.

## Modules

- `NLS/SequenceSpaces/WeightedRayZeroDerivative.lean`: A full ell1 Frechet derivative is determined from exact positive coordinate-ray agreement with an analytic Hilbert map having scalar derivative. Arbitrary nonzero literal weights are retained; no bounded Hilbert inverse inclusion is assumed.
- `NLS/Articles/KdVConvexity/NormalizedPhysicalTaylor.lean`: Exact norm-isometric reindexing of the actual physical Hamiltonian Taylor normalization: normalized gradient zero and FULL derivative -6Id at zero.
- `NLS/Articles/KdVKdV2Frequencies/IntermediateHilbertActionRays.lean`: Exact normalized weak-action compatibility for single coordinate rays at EVERY intermediate weight, and full nonnegativity of the corresponding actual Hilbert ray.
- `NLS/Articles/KdVKdV2Frequencies/IntermediateFrequencyOrigin.lean`: For the ACTUAL globally calibrated intermediate frequency at EVERY -1<alpha<0, F(0)=0 and its FULL complex derivative is -6Id. Physical Hilbert Taylor calibration and finite weighted coordinate rays give the result in the original range.
- `NLS/SequenceSpaces/CoefficientModulus.lean`: Unchanged canonical coordinate-modulus continuity and nonnegative sequence machinery needed by real cone extension.
- `NLS/SequenceSpaces/NonnegativeRealAnalyticExtension.lean`: Unchanged canonical proof that reality on the full nonnegative cone determines reality of the full nearby real analytic extension, including boundary points.
- `NLS/SequenceSpaces/RealDerivativeEntries.lean`: Unchanged canonical reality of full derivative matrix entries from the actual locally real analytic extension.
- `NLS/ComplexAnalysis/LocalInverseClosedSubspace.lean`: Unchanged canonical proof that the actual analytic local inverse preserves the closed real subspace on a full nearby target neighborhood.
- `NLS/SequenceSpaces/NonnegativeRealLocalInverse.lean`: Unchanged canonical genuine REAL analytic local inverses of cone-real analytic atlases, including both neighborhood inverse identities and cone recovery.
- `NLS/SequenceSpaces/CompactScalarConeLocalInverse.lean`: A cone-real analytic map with compact derivative minus a nonzero scalar identity on the full nonnegative cone, and the scalar derivative at zero, has a relatively OPEN DENSE real analytic two-sided inverse locus containing zero. Compactness only at original nonnegative parameters is required.
- `NLS/SequenceSpaces/WeightedPositiveActionCoordinates.lean`: The original positive-frequency weighted nonnegative cone has exact norm-isometric normalized coordinates. Its closed real coordinate subspace is precisely the raw coefficientwise-real subspace, with the original inherited weighted norm.
- `NLS/SequenceSpaces/RealConeInverseCoordinates.lean`: Transport of open dense real inverse loci, zero, analytic extensions and BOTH full-neighborhood REAL inverse identities to original Banach coordinates.
- `NLS/Articles/KdVKdV2Frequencies/IntermediateRealFrequencyInverse.lean`: At EVERY intermediate action regularity, the ACTUAL KdV frequency has a relatively open dense REAL analytic two-sided inverse locus containing zero. All compactness and exact -6Id normalization hypotheses are supplied by verified physical frequency factories.
- `NLS/Articles/KdVKdV2Frequencies/Corollary14.lean`: COMPLETE Corollary 1.4 is proved: for EVERY -1<s<-1/2, the ACTUAL KdV correction frequency has genuine REAL analytic two-sided local inverses on a relatively OPEN DENSE subset of the ENTIRE original nonnegative weighted ell(2s+1,1) action cone, containing ZERO. The complex extension is analytic near the whole cone. Its literal raw positive-frequency values agree there with ONE global weak scalar family chosen BEFORE all regularities and actions, with exact native Hamiltonian frequency recovery. The real inverse germs use the closed real subspace of the ORIGINAL weighted Banach space with its INHERITED norm. Both inverse identities hold on full real neighborhoods, including at zero and other boundary actions.

## Validation

All 3378 prior selected sources and all 53 prior provenance records remain byte-identical. The exact new import closure has fourteen modules: nine own modules containing fourteen explicit public theorems, and five newly selected canonical modules, already tracked and byte-identical to canonical main c5bcf6344cd2e2628ae537e98b85bb9ec1849dec and the previous article HEAD. One exact canonical reuse record brings provenance to 54 records. All fourteen new selections were strictly rebuilt in dependency order AFTER freezing 3449 selected-source/checker/provenance/pinned-Mathlib-source hashes. A fresh full transitive audit covers all 3392 selections and EVERY imported NLS declaration: 25997 selected and 48066 imported declarations. The ENTIRE audit loop, collectAxioms traversal, allowed axioms and imported-NLS scope remain byte-identical to baseline. The 3392-name bidirectional NameSet probe rejects insertion/deletion mismatches. Exact ordered selections, dependency order, reachability, 27 private chunks of at most 128 names, private fresh outputs, overlay targets, unchanged canonical main and pinned Mathlib are verified. Lean/mathlib 4.33.1, autoImplicit=false, warningAsError and DEFAULT heartbeat, recursion and kernel limits apply. Only propext, Classical.choice and Quot.sound are allowed. This is a fourteen-module incremental rebuild retaining all prior strict evidence, not a full 3392-module rebuild.

The exact new canonical reuse is recorded in `CANONICAL_REAL_FREQUENCY_INVERSE_REUSE.json`. No sorry, added axiom, raised limit or linter exception.

## Remaining main obligations

COMPLETE Theorem 1.1 and Corollary 1.4 are VERIFIED; the other nine COMPLETE main rows remain OPEN. Complete source clauses Theorem 1.2(ii) and (iv), and the regularity-dependent target clauses of (i), remain verified. Complete Theorem 1.2 still needs the SHARP locally uniform asymptotics(iii) and its consolidated full statement. Theorem 1.3 still needs global Hessian nonpositivity and generic uniform strict concavity. Physical asymptotic sharpness, smoothing, PDE conclusions, and KdV2 weighted moments, exact mass-renormalized physical frequency identification and global conclusions remain open.
