# The physical KdV Hamiltonian in the actual quartic Hill contour

`HillSmoothPhysicalQuartic.lean` and `HillSmoothQuarticEnergyCoefficient.lean` prove the smooth physical coefficient
used on PDF page 26 in the proof of source Lemma 3.2, formula (69). The primitive
is the independently constructed, normalized actual L2 Hill cut primitive.
The Hamiltonian is the physical period-one integral
`classicalHamiltonian q = ∫₀¹ ((q')²/2 + q³)`; the lower invariant is
`classicalQuadraticInvariant q = (1/2)∫₀¹ q²`.

For the actual Fourier coefficients of a real, smooth, period-one, mean-zero
function `Q : C(AddCircle 2, ℂ)`, the physical corollaries derive actual
Fourier parity and reality from the function assumptions. They prove:

- Every even power of the normalized cut primitive is integrable on every
  positive-radius centered circle, including its two real crossings.
- On the full energy circles of radius `R_N²`, a uniform remainder bound
  `R_N³ * |F(λ)^4 - λ² + H0 + H1/(4λ)| ≤ C` holds for all sufficiently large
  `N`. The constant and cutoff precede every point of each full circle.
- The literal counterclockwise quartic period
  `P_N = (2*pi*i)^(-1) * ∮ F(λ)^4 dλ` satisfies
  `|P_N + H1/4| ≤ C/R_N` for all sufficiently large `N`.
- `P_N → -H1/4`, and `-4*P_N → H1`.

The sign, factor four, spatial normalization and Hamiltonian are part of the
proved statements. No spectral coefficient or energy identity is assumed.
The remainder above is sufficient to identify the contour coefficient; it is
weaker than the source's displayed `O(λ^-2)` quartic remainder and is not
reported as that stronger asymptotic.

## Reused actual smooth trace development

The selected dependency closure is imported from the fixed verified shared
estimates snapshot `8bd9dcba2c439828221e11c08918ee632d16556e`. It provides the
actual physical full-circle squared-primitive estimate
`R_N⁵ * |F(λ)² + λ - H0/(2λ) - H1/(8λ²)| ≤ C`. Its proof uses actual Fourier
realization, real spectral labeling, normalized upper boundary values and
reflection, weighted WKB trace control and the physical Riccati coefficients.
This is a full-circle estimate, not a real-axis estimate promoted without proof.

Exactly 67 previously missing sources are imported. Two unchanged existing
sources, `RiccatiEnergy.lean` and `ClassicalTraceAsymptotics.lean`, are explicitly
compiled and selected. Six compatible local source variants are retained
unchanged, including local default-resource proofs. Only the final shifted-action
proof of the newly imported `ClassicalL2PrimitiveAgreement.lean` is adapted:
a linear primitive directly proves the constant circle integral is zero, so
no absent helper or replacement of the existing local action module is needed.
The eighth provenance record, `SHARED_PHYSICAL_ENERGY_COEFFICIENT_IMPORT.json`,
records every imported/adapted/retained file and its source and local hashes.
No full branch merge or source heartbeat override is imported.

## Reusable contour proofs

`UpperReflectionCircleIntegrability.lean` proves circle integrability from
continuity on the closed upper half-plane and conjugate reflection off the
real axis. Each closed semicircle has a continuous parametrization; its finite
boundary discrepancies do not affect integrability. The proof requires no
analytic continuation through the real cuts. Applied to even powers of the
actual primitive, this proves the integrability needed for the contour algebra.

`QuarticContourCoefficient.lean` proves the weighted scalar estimates and
extracts the quartic contour coefficient with an explicit inverse-frequency
error. It uses the exact identity
`v² - λ² + A + B/(4λ) = -2λ*(v+λ-A/(2λ)-B/(8λ²)) + (v+λ)²`,
the literal residue of `1/λ`, and the normalized circle integral norm bound.
The actual smooth theorem instantiates these results with `v=F(λ)²` and the
proved physical squared-primitive expansion.

`HillSmoothPhysicalQuartic.lean` proves conjugate-reflected Fourier reality
from pointwise physical reality and uses the proved parity of period-one
Fourier coefficients. Its remainder, error, coefficient-limit and Hamiltonian
recovery corollaries therefore require only reality, smoothness, period-one
periodicity and zero mean of the actual function. No independent spectral
reality or parity hypotheses remain in these physical statements.

## Remaining source obligations

This is the actual smooth physical contour **limit**. Exact contour independence
on the finite-gap exterior and its equality to each sufficiently large source
contour remain separate, as do the actual angle–Poisson identity
`2{theta_n,Delta}=psi_n`, Hamiltonian-frequency identification (69), finite-gap
approximation and action realization/descent. It does not assert a uniform
rough-potential Hamiltonian extension, the sharper displayed quartic remainder,
global source normalization, weighted frequency targets, compact derivatives,
KdV2 frequency construction or the physical PDE identifications. All main
statement inventory rows remain open.

Validation: 436 unchanged previously checked selected Lean sources, strict
compilation of 67 selectively imported sources, two unchanged existing sources
and four new proof modules, followed by a fresh combined transitive audit of
all 509 selected modules. This is incremental validation, not a repeated full
build. Dependency order, matching checker/audit/evidence/coverage selections,
all hashes, eight provenance records, private fresh outputs and unchanged
clean canonical main are verified before publication.
