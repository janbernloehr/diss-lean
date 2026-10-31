# Section 26: original action estimates and printed-sign correction

## Ordered source comparison

The [ordered Section 26 comparison](SECTION_26_ASSERTIONS.md)
covers 28 groups on pp. 112–115: 20 matched and eight corrected. No
partial or pending groups remain in this local ledger.

Original indexed actions, closed-gap samples, signed indices and exact
physical norms retain all permitted orders and threshold equality.
The comparison covers the actual lower-jet polynomial, finite support,
unit-interval integrals, interpolation exponents and Young absorption.

Direct corrections clarify the physical Hamiltonian sign, multiplicity
notation, strict supremum range, repeated-factor index and mass exponent.
The physical norm splitting uses 2^(2m-1); the final action bound
retains exactly 2^m with a constant before all real Hm sources.
No new Lean proof or refutation is added in this comparison.

The unchanged Lean snapshot reuses the successful full check at commit ad38fb1920ad267ac19c161ac7d941e8cc276cb9: 8,580 build jobs, 7,688 public examples and an axiom audit of 44,702 NLS declarations, with 21 inherited warnings and zero new. All 63 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: Section 27. The [broader completion qualifications](COMPLETENESS.md)
remain; these local ledger counts do not certify the whole dissertation.

Earlier entries retain their original implementation and validation scope.

## Positive norm splitting and the exact leading action constant

The [physical norm splitting](../NLS/ZakharovShabat/SourceSection26PhysicalNormSplit.lean)
at the end of the Lemma 26.3 proof now has a direct positive proof
with coefficient 2^(2m-1). It uses the exact weight 1+|2n*pi| and
admits every complex scalar Hm source, including order zero.

The [final action bound](../NLS/ZakharovShabat/SourceSection26ActionLeading.lean)
retains the literal leading coefficient 2^m times the squared
physical pair Hm norm. The real-pair factor two supplies the
required half-pair derivative bound. One nonnegative remainder
constant is chosen before all real Hm sources, for every m>=1.

Five positive theorems and four examples cover the corrected H1
coefficient, zero-order energy, real-pair normalization and the
even-order action bound with leading coefficient four. Existing
refutations remain unchanged; no new refutation is added.

The full check passed: 8,580 build jobs, 7,688 public examples and an axiom audit of 44,702 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The ordered Section 26 comparison remains in progress. The
[broader completion qualifications](COMPLETENESS.md) remain.

This audit covers Proposition 26.1 and Lemmas 26.2–26.3 on printed
pp. 112–115. The original indexed actions and independently defined
physical Hamiltonians retain their normalization. The alternating sign
in Lemma 26.2 is refuted by an actual source, including the full positive
remainder. The printed supremum endpoint in (5.11) is also refuted at
m=i=1. The verified supremum estimate uses strictly lower derivatives,
while the L² estimate includes the top derivative.

## Exact original estimates

For a real original Hᵐ source a, write ψ for its inclusion in L² and

    P = ‖sourcePiSobolevCoordinates m 1 hm a‖.

This is the exact physical pair norm with weight 1+|2nπ|, including
both components. The realization identities remove any additional
weighted-potential premise from the public statements.

[`SourceSection26Actions.lean`](../NLS/ZakharovShabat/SourceSection26Actions.lean)
proves Proposition 26.1 at every natural m, including m=0. The original
higher action at spectral power 2m represents printed level 2m+1.
The selected mean-value point lies in the actual closed gap and satisfies
the literal complex identity J=ζ^(2m)I and the exact quadratic radius.
The exterior estimate retains factors 2^(−m) and 4^m, with n≠0 and
8P²≤1+|n|. The central estimate retains (16π)^(2m)P^(4m) and allows n=0.
Collapsed gaps and equality at the exterior threshold are included.

[`SourceSection26Sum.lean`](../NLS/ZakharovShabat/SourceSection26Sum.lean)
proves absolute summability on every real Hᵐ source, m≥1, and

    ∑ ⟨2nπ⟩^(2m)|Iₙ| ≤ (1+16π)^(2m)(1+P)^(4m) ‖ψ‖²/2 + 2^m H₂ₘ₊₁.

The half-mass coefficient is stronger than the printed full-mass
remainder; a separate corollary retains the full printed remainder.
The Hamiltonian sign is positive at every order. At odd m the literal
printed alternating sign equals this positive sign, and
`sourceSection26_printed_estimate_of_odd` proves that case explicitly.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Proposition 26.1, mean-value formula | `sourceSection26_meanValue_complex` | All real H¹ sources, signed indices, m≥0, actual gap point, exact complex identity and radius. |
| Proposition 26.1, exterior comparison | `sourceSection26_exterior` | n≠0, inclusive quadratic threshold, exact powers and constants. |
| Proposition 26.1, central comparison | `sourceSection26_central` | Strict complementary threshold, actual complex-action norm, including n=0. |
| Lemma 26.2, corrected | `sourceSection26_action_estimate_half_mass`, `sourceSection26_action_estimate` | Original action summability and exact physical norms; positive Hamiltonian sign, half-mass and full-mass versions. |
| Lemma 26.2, printed odd-order case | `sourceSection26_printed_estimate_of_odd` | Every odd m≥1 and every real Hᵐ source. |
| Lemma 26.2, printed general claim | `section26_printedInequality_strict_counterexample` | Refuted at m=2 by a real H² source, with a summable original action sequence and strict reverse inequality. |
| Lemma 26.3 | `exists_sourceSection26_remainder_bounds` | One C≥0 before all real Hᵐ sources, for both the absolute physical remainder integral and the Hamiltonian norm. |
| H¹ norm splitting at the end of the Lemma 26.3 proof | `section26_printed_physicalNorm_split_counterexample` | Refuted for the exact physical weight by a single nonzero Fourier mode. |
| Formula (5.11), valid ranges | `sourceSection26_supremum_interpolate`, `sourceSection26_L2_interpolate` | Exact physical norm; i<m for the supremum estimate and i≤m for L², with explicit constants. |
| Formula (5.11), printed supremum endpoint | `section26_supremum_no_uniform_constant` | No uniform constant at m=i=1, even on real H² sources with continuous first derivative and scalar mass at least one. |

## Actual-source counterexamples

[`SobolevSourceFourierModes.lean`](../NLS/ZakharovShabat/SobolevSourceFourierModes.lean)
constructs real Sobolev sources whose two components have opposite
Fourier frequencies and conjugate amplitudes. It proves exact scalar
mass, physical derivative norms, physical weighted coordinates, and pair
norms at every integer order.

[`SourceSection26SignCorrection.lean`](../NLS/ZakharovShabat/SourceSection26SignCorrection.lean)
uses amplitude 1/n at frequency n≥1. The scalar L² norm is at most one,
the squared pair mass at most two, and the physical pair H¹ norm at most
2(1+2π), uniformly in n. The second-derivative norm is at least n.
The existing physical Hamiltonian coercivity estimate therefore makes
H₅ arbitrarily large while the printed positive remainder stays bounded.
For sufficiently large n, that remainder minus 4H₅ is negative.
The original action sum is nonnegative and summable, so the entire
printed inequality is false. This argument uses neither an abstract
action sequence nor an assumed spectral formula for the modes.

The norm-splitting counterexample is separate. At m=1, frequency one,
and unit scalar amplitude, the exact physical H¹ norm squared is
(1+2π)², while the physical derivative energy plus scalar mass is
(2π)²+1. Thus the printed coefficient 2^(m−1)=1 cannot hold for this
norm. The formal remainder proof uses the valid quantitative bound in
[`SobolevHighestJetEnergy.lean`](../NLS/ZakharovShabat/SobolevHighestJetEnergy.lean);
its constants are absorbed into C. Lemma 26.3 itself remains valid.
See [source discrepancies](../SOURCE_ERRATA.md).

## Physical remainder and one retained family

The remainder is the actual lower-jet polynomial field from Appendix H,
integrated over the original physical unit interval. Its finite monomial
decomposition, interpolation exponents, and Young absorption are proved
in [`SobolevMonomialInterpolation.lean`](../NLS/ZakharovShabat/SobolevMonomialInterpolation.lean)
and [`SobolevRemainderAbsorption.lean`](../NLS/ZakharovShabat/SobolevRemainderAbsorption.lean).
[`OddHamiltonianRemainderEstimate.lean`](../NLS/ZakharovShabat/OddHamiltonianRemainderEstimate.lean)
retains the arbitrary positive ε, the top physical derivative, and the
L²-only error C(1+‖ψ₁‖^(4m))‖ψ₁‖².

[`SourceSection26Original.lean`](../NLS/ZakharovShabat/SourceSection26Original.lean)
chooses one constant for both conclusions of Lemma 26.3 before every
source. `SourceSection26Data` extends the same Section 25 family and
keeps both U and T. `SourceSection25Data.section26` augments any retained
family; `sourceSection26_original` constructs one unconditionally.
Its `printed_counterexample` puts the strict counterexample in U∩T.
The original Theorem 23.2(i) action bounds remain available through the
inherited Section 23 package.

## Supremum endpoint in (5.11)

The printed range 0≤i≤m includes the top derivative in both estimates.
[`SourceSection26Interpolation.lean`](../NLS/ZakharovShabat/SourceSection26Interpolation.lean)
proves the valid ranges in the exact physical norm with weight 1+|2nπ|:

- Supremum estimate for i<m, with constant 4(2π)^i.
- L² estimate for i≤m, with constant (2π)^i.

These follow from the established interpolation results and the proved
comparison from the auxiliary Sobolev norm to the exact physical norm.
Lemma 26.3's monomial argument uses only i<m and remains valid.

[`SobolevSourceFourierSums.lean`](../NLS/ZakharovShabat/SobolevSourceFourierSums.lean)
proves exact finite-sum coefficients, weighted energies, and derivative
values. [`SourceSection26SupremumCorrection.lean`](../NLS/ZakharovShabat/SourceSection26SupremumCorrection.lean)
uses the scalar source

    ψ_N(x) = 1 + ∑_{n=1}^{N²} exp(2πinx)/(Nn),    N≥1.

Its L² norm is at least one, its physical H¹ norm is at most 2+2π, and
|ψ'_N(0)|=2πN. At the printed endpoint m=i=1, the proposed right-hand
side is C‖ψ_N‖_L²^(−1/2)‖ψ_N‖_H¹^(3/2), which is uniformly bounded
for each fixed C. The derivative supremum is unbounded. The constant
mode ensures the negative exponent never encounters zero.

`section26_supremum_real_counterexample` completes the scalar source
with its physical conjugate, giving an actual real H² source for every
proposed C≥0. Its first derivative has a continuous physical
representative. `section26_supremum_no_uniform_constant` refutes the
uniform assertion, and `SourceSection26Data.supremum_counterexample`
places the bounded-norm, nonzero-mass witness in every retained U∩T.
This already refutes the printed inclusive supremum range; the L²
endpoint and the strict supremum range are separately proved.

## Validation and next work

The action-estimate step added 25 public checks. This endpoint step adds
20 checks for signed finite supports, block boundaries, exact derivative
values, uniform H¹ bounds, nonzero mass, arbitrary proposed constants,
corrected interpolation ranges, and original-domain membership.
Full validation is recorded in [implementation status](../STATUS.md).
The original Sobolev-norm estimates, including the unrestricted m=1
coefficient, are proved in [Section 27](SECTION_27.md).
The separate [Section 14 qualifications](SECTION_14.md) remain; the
dissertation is incomplete.
