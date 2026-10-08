# Introductory-result coverage

This is a focused map of the dissertation's introductory results to the
current public Lean API. It is not a completeness certificate for every
chapter or appendix. All paths below are relative to the repository root;
the named declarations are in `NLS.ZakharovShabat`.

| Source result | Public entry point | Scope |
| --- | --- | --- |
| Theorem 0.1; Theorems 23.1–23.2; Remark 23.3 | [`SourceSobolevCommonConstants.lean`](NLS/ZakharovShabat/SourceSobolevCommonConstants.lean), `exists_sourceBirkhoffMap_sobolev_common_constants` | One constructed map, every positive integer Sobolev order, common positive constants chosen before the potential, both Birkhoff bounds and both action bounds. |
| Theorem 0.2: analytic action Hamiltonian, sign, Hessian and local concavity | [`SourceHamiltonianActionConcavity.lean`](NLS/ZakharovShabat/SourceHamiltonianActionConcavity.lean), `exists_sourceHamiltonian_action_extension_with_concavity` | Actual source Hamiltonian on an open complex ℓ² domain containing all nonnegative summable actions; actual frequency gradient, Hessian −2 times Hilbert bilinear duality, quantitative local negativity. |
| Physical normalization of H* | [`SourceSobolevHamiltonianIdentification.lean`](NLS/ZakharovShabat/SourceSobolevHamiltonianIdentification.lean), `SourcePrimitivePowerAtlas.renormalizedHamiltonian_eq_sobolevPhysicalCorrection` | Identification with the H¹ energy correction on all real H¹ sources, beyond the finite-gap normalization. |
| Consequence after Theorem 0.2, printed p. 12: no C¹ extension for q > 2 | [`SourceHamiltonianNonextension.lean`](NLS/ZakharovShabat/SourceHamiltonianNonextension.lean), `exists_sourceHamiltonian_no_continuous_extension` | No continuous extension at zero relative to the nonnegative ℓ^q cone, hence no C¹ extension, for every finite q > 2. The same Hamiltonian retains actual source recovery and the physical H¹ identity. |
| Theorem 0.3; Theorem 18.1: frequency extensions | [`SourceFrequencyTheorem18_1Real.lean`](NLS/ZakharovShabat/SourceFrequencyTheorem18_1Real.lean), `exists_sourceFrequency_theorem18_1_real` | A common actual frequency on summable actions, real analytic values in every finite exponent above one, compatible higher-exponent complex extensions and locally uniform mixed remainders. |
| Local invertibility near zero; Corollary 18.2(i) | [`SourceFrequencyLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyLocalInverse.lean), `exists_sourceFrequency_localInverse` | Actual frequency derivative −2 times identity, both analytic local inverse identities, inverse derivative −1/2 times identity, and the Fredholm property throughout the action domain. |
| Remark after Theorem 0.3; Corollary 18.2(iv): generic local invertibility | [`SourceFrequencyGenericLocalInverse.lean`](NLS/ZakharovShabat/SourceFrequencyGenericLocalInverse.lean), `exists_sourceFrequency_genericLocalInverse` | Open dense set of points with two-sided analytic local inverses on a connected action domain containing all real-source actions and all nonnegative summable actions. |

## Nonextension proof and limits

The proof integrates the quantitative Hessian estimate along real radial
segments twice. Since H*(0) = 0 and its gradient vanishes at zero, this gives
`Re H*(I) ≤ -‖I‖₂²/2` on a small real Hilbert ball. A block of N+1 coordinates,
each equal to `c / sqrt(N+1)`, has ℓ² norm c and ℓ^q norm
`c (N+1)^(1/q-1/2)`. For finite q > 2 the latter tends to zero while the
Hamiltonian remains bounded above by `-c²/2`. Every block is nonnegative and
summable, so agreement with H* contradicts continuity at zero.

The formal statement allows an arbitrary ambient neighborhood U of zero
and requires agreement only for summable nonnegative actions lying in U.
Continuity and C¹ regularity are tested relative to the nonnegative cone.
No ℓ∞ endpoint is asserted in this milestone. Global analytic extension to
all of the nonnegative ℓ² cone, and global strict concavity, are not asserted.

## Accepted source corrections

The global replacement for Lemma 27.2 is
`sobolevOddHamiltonian_le_twice_weighted_action_remainder`. The original
unrestricted m=1 coefficient is unresolved and optional, not disproved.
The principal Sobolev estimates do not depend on recovering it. See
[`SOURCE_ERRATA.md`](SOURCE_ERRATA.md) for the precise scope of this and
other discrepancies in printed statements or proofs.
