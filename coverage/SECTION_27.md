# Section 27: original Sobolev norms from the actions

This audit covers formula (5.13), Lemmas 27.1–27.2, and the proof of
Theorem 23.2(ii) on printed pp. 115–116. The original indexed actions,
independently defined physical Hamiltonians, and exact physical Sobolev
norms are retained. The unrestricted printed m=1 coefficient in Lemma
27.2 remains qualified; its global replacement doubles the remainder.

For a real Hᵐ source a, write

    S_k = ∑ₙ ⟨2nπ⟩^(2k) |Iₙ|,   M = S_0,   S = S_1.

Here Iₙ is `sourceIndexedAction`, and the bracket is exactly 1+|2nπ|.
On real sources the original actions are nonnegative. The pair norms
include both components with this exact physical Fourier weight.

| Source assertion | Public entry point | Verified scope |
| --- | --- | --- |
| Formula (5.13) | `SourceSection26Data.section27_pair_top_jet_identity` | All real Hᵐ sources, m≥1; half the sum of both component derivative energies, positive 4ᵐ, actual original higher actions, and the physical remainder integral over [0,1]. |
| Higher-action trace used in Section 27 | `SourceSection26Data.section27_hamiltonian_hasSum` | The scaled original series has sum H₂ₘ₊₁; its absolute convergence is retained from Section 24. |
| Lemma 27.1, kinetic estimate | `sourceSection27_energy_action_bound`, `sourceSection27_kinetic_summable` | H₃−2H₁²≤∑(2nπ)²Iₙ on every real H¹ source, with absolute convergence and all signed indices. |
| Lemma 27.1, H₃ corollary | `sourceSection27_H3_action_mass_bound` | H₃≤S+2M² for the independently defined sharp odd Hamiltonian. |
| Lemma 27.1, physical H¹ norm | `sourceSection27_H1_norm` | P²/3≤S+M², retaining the literal pair norm and coefficient 1/3. |
| Lemma 27.2, m≥2 | `sourceSection27_hamiltonian_estimate` | H₂ₘ₊₁≤S_m+(64π)^(2m−2)(1+S)^(4m−3)S, with the printed coefficient and final weighted factor. |
| Lemma 27.2, m=1 on S≤2 | `sourceSection27_endpoint_of_small` | The literal bound H₃≤2S+S² on the closed weighted-action ball, including its boundary. |
| Lemma 27.2, unrestricted m≥1 variant | `sourceSection27_hamiltonian_estimate_all` | Twice the printed remainder; the unrestricted literal m=1 coefficient is neither proved nor refuted. |
| Last derivative estimate in the proof of Theorem 23.2(ii) | `exists_sourceSection27_derivative_bound` | m≥2, exact factor 1/4 on the pair derivative energy, coefficient one on S_m, and one source-independent C multiplying (1+S)^(4m−3)M. |
| Theorem 23.2(ii) | `exists_sourceSection27_sobolev_bound` | Every m≥1, one d before all sources, exact physical Hᵐ pair norm, and the unweighted final factor M. The retained Section 23 package also keeps its common positive constants and original Birkhoff map. |
| One original family | `SourceSection27Data`, `sourceSection27_original` | All orders and uniform constants on the same retained U and T; no new domain or independently chosen action family. |

## Original actions and physical energy

[`SourceSection27Actions.lean`](../NLS/ZakharovShabat/SourceSection27Actions.lean)
identifies the original indexed actions with the previously established
real contour actions. The kinetic series is proved absolutely convergent,
so its sum in Lemma 27.1 is a convergent series. The physical correction
from Proposition 21.3 is nonpositive, giving the kinetic inequality.
The quartic mass bound and the physical Fourier comparison then give the
exact H¹ norm coefficient 1/3.

`sourceSection27_H3_bridge` identifies the sharp Sobolev odd Hamiltonian
at m=1 with the independently defined H¹ Hamiltonian. This prevents a
normalization change when passing between Lemmas 27.1 and 27.2.
`sourceSection27_pair_jet_norm` proves that half the sum of both component
derivative energies equals the first component energy. It includes order
zero and is used to recover the literal pair factor in (5.13).

## Preserving coefficient one in the derivative estimate

[`SourceSection27DerivativeBound.lean`](../NLS/ZakharovShabat/SourceSection27DerivativeBound.lean)
strengthens the earlier bound with an unspecified constant on the entire
right-hand side. The displayed estimate in the source keeps coefficient
one on S_m; this is now proved explicitly.

The proof uses the existing action-moment comparison at an enlarged
frequency threshold L(1+S). For e=2(m−1), choosing L large enough makes
the central remainder at most

    S_m/2 + C_h (1+S)^(4m−3)M.

The unit-mass split M≤1 or M≥1 controls the physical H¹ factor. This
gives H₂ₘ₊₁≤3S_m/2+C_h(1+S)^(4m−3)M. The physical remainder estimate
with ε=1/4 then yields

    (‖∂ᵐa₁‖² + ‖∂ᵐa₂‖²)/4 ≤ S_m + C(1+S)^(4m−3)M.

Both constants are chosen before all potentials. The total action is
exactly the scalar L² energy, and M≤S absorbs its higher powers into the
same unweighted remainder. The proof does not divide by M, so zero
mass is included. The full physical Sobolev-norm estimate follows from
the previously proved norm comparison. Its m=1 branch uses Lemma 27.1
directly and does not require the unresolved coefficient in Lemma 27.2.

## Endpoint qualification and the retained family

The printed coefficient in Lemma 27.2 is proved for every m≥2. At m=1,
retaining the mass subtraction in the energy budget proves it on S≤2.
An all-order global statement with twice the remainder is available.
The scalar budget alone is insufficient to establish the printed bound
for all sizes; this does not constitute a counterexample potential.
See [the precise endpoint qualification](../SOURCE_ERRATA.md).

[`SourceSection27Original.lean`](../NLS/ZakharovShabat/SourceSection27Original.lean)
retains the Section 26 family and both original domains. Its physical
identity uses the actual reduced polynomial field integrated over the
unit interval, not a formal remainder symbol. The scaled higher-action
series has the independently defined Hamiltonian as its `HasSum` value.
`SourceSection26Data.section27` augments any existing family;
`sourceSection27_original` constructs one without an extra premise.
The inherited Section 23 package supplies the same positive constants
for all Birkhoff and action estimates on that original map.

## Validation and next work

The 25 new public checks cover kinetic convergence, signed Fourier
normalization, both components, the endpoint S=2, the zero-action case,
exact m=2 and m=3 powers, both mass regimes of the cutoff argument,
uniform derivative constants, the physical integral identity, scaled
higher-action convergence, and the unchanged original domains.
Full validation is recorded in [implementation status](../STATUS.md).

Next: Section 28's original weighted action and gap estimates. The
separate [Section 14 qualifications](SECTION_14.md) and unrestricted
printed m=1 coefficient of Lemma 27.2 remain explicit. The dissertation
is incomplete.
