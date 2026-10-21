# Section 21: original moments and Hamiltonian

This audit covers printed pp. 96–98, including Lemmas 21.1–21.2,
Proposition 21.3, and the proof of Theorem 18.3 at the end of the section.
The public constructors are
[`sourceSection21_original_moments` and `sourceSection21_original`](../NLS/ZakharovShabat/SourceSection21Original.lean).
They construct the original Birkhoff family, primitive, moment atlases,
and domains before choosing any source or index.

## Common domains and the retained primitive

For every finite p > 1, `SourceSection21MomentData Q P T` retains the
original Section 20 package Q. The complex source domain T is open and
connected, contains the entire real FLᵖ source space, and lies inside
Q's domain U and P's moment domain. A connected component of the
intersection supplies T; connectedness of the real source space ensures
that all real sources remain. See
[`SourceSection21Domain.lean`](../NLS/ZakharovShabat/SourceSection21Domain.lean).

`moment_contours` represents every order at every index with one circle
family using the same ambient primitive B retained from Section 19.
The normalization is exactly Rₙ⁽ᵐ⁾ = −π⁻¹ ∮ Fₙᵐ dλ. These are the
primitive-power moments of Section 21, distinct from the psi-weighted
moments of Section 20. Neighborhood independence identifies the actual
contours, rather than assuming equality of independently supplied atlases.

At p = 4, `SourceSection21HamiltonianData Q P E T` further restricts the
common source neighborhood so that the action sequence lies in the
already chosen original Hamiltonian domain L. The constructor
`SourceSection21MomentData.exists_hamiltonian_domain` preserves the
supplied action Hamiltonian H, frequency F, and original package E.
Analytic uniqueness from real finite-gap sources identifies H(I(ψ)) with
the cubic sum throughout T. All indices and moment orders share T.

## Assertion map

| Source assertion | Public theorem or field | Formal scope |
| --- | --- | --- |
| Lemma 21.1(i): moment analyticity | `SourceSection21MomentData.lemma21_1` | Every integer index and natural moment order, on the same complex T. |
| Lemma 21.1(ii): even moments vanish | `lemma21_1` | Every even order, including zero, at every complex source in T. |
| Lemma 21.1(iii): local gap bound | `locally_uniform`, `lemma21_1` | One source neighborhood and C > 0 give ‖Rₙ⁽ᵐ⁾‖ ≤ Cᵐ ‖γₙ‖ᵐ⁺¹ for all n and m. A collapsed complex gap kills all orders. |
| Lemma 21.1(iv): real sign and zero set | `lemma21_1` | Every moment is real and nonnegative at real sources; an odd moment vanishes exactly when its gap does. |
| Lemma 21.1(v): first moment is action | `lemma21_1` | Equality on the full complex T, hence equality of full complex differentials there. |
| Lemma 21.2 / (4.13): finite-gap Hamiltonian | `SourceSection21MomentData.lemma21_2` | Retained primitive contours and H₃ − 2H₁² − ∑(2nπ)²Iₙ = −(4/3)∑Rₙ⁽³⁾ at every real finite-gap source. The printed positive sign is corrected. |
| Proposition 21.3: convergence and analyticity | `SourceSection21HamiltonianData.proposition21_3`, `hamiltonian_hasSum` | Absolute convergence at every complex source in T, locally uniform symmetric partial sums, and a complex analytic sum. |
| Proposition 21.3: real restriction | `real_analytic`, `real_sign` | Real analytic on the entire real FL⁴ space, real valued and nonpositive, with zero set exactly the zero source. |
| Physical meaning of H* | `physical_identity` | The same sum equals physical H¹ energy minus twice squared physical mass and the literal infinite weighted action sum, for every real H¹ source. |
| Theorem 18.3 proof: action gradient | `action_frequency`, `action_frequency_sequence` | The chosen action Hamiltonian's gradient equals the retained Section 20 frequency, coordinatewise and in ℓ², at every complex source in T. |
| Full source differential | `source_fderiv`, `source_derivative_series` | The actual complex derivative is the frequency/action-derivative pairing; its scalar series is absolutely convergent. |
| Theorem 18.3 proof: action sign, Hessian, concavity | Retained `SourceOriginalHamiltonianData.sign`, `.hessian_zero`, `.concavity` | The same H is nonpositive on L intersected with the nonnegative ℓ² cone, vanishes there only at zero, has Hessian −2 times complex bilinear duality at zero, and satisfies the quantitative local concavity bound. |

Moment assertions are implemented in
[`SourceSection21Moments.lean`](../NLS/ZakharovShabat/SourceSection21Moments.lean);
the common Hamiltonian and derivative assertions are in
[`SourceSection21Hamiltonian.lean`](../NLS/ZakharovShabat/SourceSection21Hamiltonian.lean).
The retained action package and its domain are described in
[the Section 18 audit](SECTION_18.md).

## Printed signs and formal witnesses

Equation (4.13) on p. 97 prints a positive cubic coefficient, although
its proof concludes with the negative coefficient. On p. 98, the proofs
of Proposition 21.3 and Theorem 18.3 each say “nonnegative” for H*, where
“nonpositive” is required. The proposition and theorem statements have
the correct sign.

[`SourceSection21SignCorrections.lean`](../NLS/ZakharovShabat/SourceSection21SignCorrections.lean)
constructs actual sources refuting these printed claims:

- `printed_lemma21_2_sign_counterexample` realizes a single nonzero
  action at index zero, proves that the only surviving cubic moment is
  strictly positive, and refutes the positive coefficient in (4.13).
- `printed_nonnegative_hamiltonian_counterexample` gives a real H¹
  source of physical mass one with strictly negative cubic Hamiltonian.
- `printed_nonnegative_action_hamiltonian_counterexample` places such a
  source's actions inside both the chosen L and the nonnegative cone,
  with strictly negative value of that same original H.

These witnesses quantify over the relevant actual atlas or original
Hamiltonian package. See [source discrepancies](../SOURCE_ERRATA.md).

## Validation and limits

Five new modules and 22 public examples check contour normalization,
zeroth and even orders, common bounds at different powers, collapsed
complex gaps, strict positivity at a negative index, full action
differentials, and reconstruction of physical H₃. An unconditional
constructor at p = 3/2 checks the below-two range. Quartic examples check
actual sums, locally uniform convergence, real analyticity, the original
frequency gradient, absolute derivative-series convergence, source and
action domain inclusions, and the complete H¹ identity. They also check
preservation of an already chosen H, complex bilinearity and the sign of
its Hessian, local concavity, all three printed-sign witnesses, and an
unconditional common-domain construction with a negative unit-mass source.
Full gate results are recorded in [implementation status](../STATUS.md).

Section 21 uses a common connected restriction T of the prior Section 20
domain U; it does not assert these new identities on all of the old U.
The action domain L contains all real-source actions and all nonnegative
summable actions. Extension to the whole nonnegative ℓ² cone and global
concavity are not asserted. Native fractional Sobolev analyticity and
analytic inverses are proved in [Section 14](SECTION_14.md); its precise
2014 construction comparison remains unverified. The subsequent original
phases and physical flows are audited in [Section 22](SECTION_22.md).

## The imaginary constant in the cube shift, printed p. 97

The proof of Lemma 21.2 expands F0 = Fn - i*pi*n, but prints the constant
term +(pi*n)^3 when cubing. The correct term is +i*(pi*n)^3. The PDF was
checked directly; this is separate from the already recorded overall
sign discrepancy in equation (4.13).

[SourceSection21CubeShiftCorrection.lean](../NLS/ZakharovShabat/SourceSection21CubeShiftCorrection.lean)
proves the corrected algebra and applies it to the actual primitive on
the full filled spectral domain of every retained Section 19 package.
It also refutes the printed identity at the actual zero source for every
spectral argument and every nonzero signed normalization index, at every
finite source exponent above one. No source or spectral witness is assumed.

The missing imaginary unit affects only a constant in the spectral
variable. Its circle integral is zero, so the existing
[original moment identity](../NLS/ZakharovShabat/SourceSection21Moments.lean)
and the corrected negative cubic Hamiltonian coefficient remain proved.
Two public examples check an unconditional original family at p=4 with
index -1 and the corrected identity on the entire stated spectral domain.
