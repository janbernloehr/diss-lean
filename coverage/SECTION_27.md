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
| Lemma 27.2, closed zero gap | `sourceH1_energy_le_lemma272_of_zero_gap` | Literal H3<=2S+S² for every real H1 source whose central gap is closed, with no smallness restriction; the stronger H3<=S-M+S²/2 is proved. |
| Lemma 27.2, open-gap representation criterion | `sourceH1_energy_le_lemma272_of_zero_gap_kernel_representation` | A precise positive exterior-kernel formula for the actual zero-gap profile implies the literal bound. The actual integrable kernel candidate is now constructed below; equality with the original profile remains unproved. |
| Lemma 27.2, explicit actual-kernel criterion | `sourceH1_energy_le_lemma272_of_actual_zero_gap_identity` | Only the identity with the constructed spectral correction remains a hypothesis; the actual H1 source supplies summability, integrability and the moment atlas. |
| Lemma 27.2, finite-gap identity criterion | `sourceH1_energy_le_lemma272_of_finiteGap_zero_profile_identity` | Only the actual zero-profile identities for finite-gap FL4 sources are required. Density, continuity, action summability and the moment atlas are supplied internally; the identities remain unproved. |
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
The later zero-mode argument below also proves it for every source with
a collapsed central gap, without restricting S.
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

## The zero mode and the remaining sharp cubic input

[`SourceH1ZeroModeActionBound.lean`](../NLS/ZakharovShabat/SourceH1ZeroModeActionBound.lean)
proves that every nonzero frequency has bracket weight at least two.
Absolute summability then gives 2*M-I_0<=S. With I_0=0 the original physical
energy satisfies H3<=S-M+S²/2. A collapsed zero gap gives I_0=0 and hence
the literal endpoint for arbitrary action size. The actual action summands
are also identified exactly under the inclusion from H1 into FL4.

[`SourceH1ZeroModeMomentCriterion.lean`](../NLS/ZakharovShabat/SourceH1ZeroModeMomentCriterion.lean)
uses the exact energy identity and nonnegative cubic moments. The single
condition R_0>=(3/4)*I_0² suffices for H3<=S-M+S². This is a sufficient
condition, not a claimed equivalence or a proved lower bound at every source.

[`SineCorrectedCubicIntegral.lean`](../NLS/ComplexAnalysis/SineCorrectedCubicIntegral.lean)
proves 3*A²<=2*pi*B for
A=integral(sin²(theta)*(1+V(theta))) and
B=integral(sin⁴(theta)*(1+V(theta))³) over [0,pi], assuming V is continuous,
nonnegative and its linear correction integral is nonnegative.
[`SineExteriorKernelCorrection.lean`](../NLS/ComplexAnalysis/SineExteriorKernelCorrection.lean)
proves that correction condition for kernels 1/|s-cos(theta)| with |s|>1
on either side of the gap, including finite positive mixtures.
[`SineIntegralKernelCorrection.lean`](../NLS/ComplexAnalysis/SineIntegralKernelCorrection.lean)
extends this to positive kernel integrals. Measurability and integrability
of c/(|s|-1) give continuity and justify Fubini; these requirements are
explicit in the statements.

[`SourcePrimitivePowerSharpCubic.lean`](../NLS/ZakharovShabat/SourcePrimitivePowerSharpCubic.lean)
connects these scalar bounds to the actual arcosh gap profile when that
profile equals r*sin(theta)*(1+V(theta)), with r the half-gap length.
The original action is 2*r²*A/pi and the cubic moment is 2*r⁴*B/pi, giving
R_n>=(3/4)*I_n² with no changed normalization.
[`SourceH1ZeroModeKernelCriterion.lean`](../NLS/ZakharovShabat/SourceH1ZeroModeKernelCriterion.lean)
constructs the moment atlas and proves the printed endpoint from the
specified actual zero-gap representation and its integrable majorant.

The motivating exterior-kernel identity is equation (2.15) of
[Korotyaev, *Hamiltonian and small action variables for periodic dNLS*](https://arxiv.org/pdf/0911.5235).
Its applicability to the actual source profile is not imported as an axiom.
The integrable majorant has now been constructed from actual spectral data
as detailed below. Equality with the actual profile remains the spectral
obligation; the unrestricted literal m=1 estimate is still unproved and
unrefuted. The previously proved Theorem 23.2(ii) is unaffected.

## The explicit actual-kernel candidate

[`SourceRealGapSeparation.lean`](../NLS/ZakharovShabat/SourceRealGapSeparation.lean)
applies the ordered-interval argument of
[`OrderedGapSeparation.lean`](../NLS/ComplexAnalysis/OrderedGapSeparation.lean)
to the actual periodic endpoints. For each fixed gap n, the two neighboring
bands give delta>0 separating all other gaps from both endpoints and from
the central interval. No uniformity in n or the potential is asserted.

[`SourceGapAngularDensity.lean`](../NLS/ZakharovShabat/SourceGapAngularDensity.lean)
defines d_m(theta)=gamma_m/(2*pi)*sin(theta)*f_m(theta) on [0,pi], and zero
outside. Here gamma_m is the real gap length and f_m is the actual arcosh
profile in cosine coordinates. This density is nonnegative, integrable,
and has integral I_m/2. The actual action trace therefore proves joint
integrability over all m different from n and all real angles.

[`SourceExteriorGapKernel.lean`](../NLS/ZakharovShabat/SourceExteriorGapKernel.lean)
uses t equal to the exterior gap's cosine point, r the selected half-width,
and c its center. Its normalized pole is s=(t-c)/r and its coefficient is
d_m/(r*sqrt(abs((t-L_n)*(t-R_n)))). Separation proves abs(s)>1 and bounds
the majorant by d_m/delta². Measurability and action summability discharge
the integrability premise of the scalar kernel theorem. The normalization
lemma retains equality with the original real-gap kernel, including r.

[`SourceExteriorGapCorrection.lean`](../NLS/ZakharovShabat/SourceExteriorGapCorrection.lean)
defines V_n(theta) as the integral of these actual kernels over exterior
indices and angles. For open selected gaps and summable actions, it is
nonnegative and continuous. The sharp cubic bound follows if the actual
profile equals r*sin(theta)*(1+V_n(theta)).
[`SourceH1ActualGapCriterion.lean`](../NLS/ZakharovShabat/SourceH1ActualGapCriterion.lean)
supplies action summability by the H1-to-FL4 comparison and constructs the
moment atlas, so this explicit identity at n=0 is its only hypothesis.
The identity is still unproved; the candidate's existence and integrability
alone do not establish it.

## Analytic quotient and finite-gap reduction

[`SourceFilledGapQuotient.lean`](../NLS/ZakharovShabat/SourceFilledGapQuotient.lean)
constructs the actual normalized quotient Q_n=-i*F_n/root_n using its local
analytic filling on the selected gap. The exact real profile satisfies
f_n(theta)=r_n*sin(theta)*Re Q_n(c_n+r_n*cos(theta)), including both endpoints.
On every exterior gap the actual upper and lower boundary values differ by
-2*i*v_m/root_n; their index constants cancel.

[`StandardRootInfinity.lean`](../NLS/ZakharovShabat/StandardRootInfinity.lean)
proves root_n(z)/z tends to -1. With the existing finite-gap inversion
expansion, [`SourceFilledGapQuotientInfinity.lean`](../NLS/ZakharovShabat/SourceFilledGapQuotientInfinity.lean)
proves F_n(z)/z tends to -i and Q_n(z) tends to one in every complex direction.
[`CauchyFiniteHoles.lean`](../NLS/ComplexAnalysis/CauchyFiniteHoles.lean)
proves (2*pi*i)*f(x) equals the outer Cauchy contour minus the sum of the
inner contours for analytic f on a closed disc with finitely many disjoint
circular holes. [`CauchyOuterLimit.lean`](../NLS/ComplexAnalysis/CauchyOuterLimit.lean)
proves that the outer integral tends to 2*pi*i when f tends to one and is
continuous on sufficiently large circles. The signs and constants are
proved for the repository's original root and contour conventions.

[`SourceSharpCubicFiniteGapReduction.lean`](../NLS/ZakharovShabat/SourceSharpCubicFiniteGapReduction.lean)
proves continuity of all actual moments on the real source space. Density
of finite-gap sources therefore makes the sharp cubic inequality for all
real sources equivalent to the finite-gap case, for every finite p>1.
Finite-gap support also gives absolute summability of the actual actions.
Only the explicit zero-profile identity for finite-gap FL4 sources is now
needed for the unrestricted H1 endpoint. The atlas is constructed internally.

The remaining obligation is to identify each exterior contour with its
weighted arcosh-profile integral and then with the constructed positive
kernel. Neither the finite-gap profile identity nor the unrestricted
literal m=1 inequality is proved by these analytic and density reductions.
An infinite-gap profile representation is not necessary for that inequality.
