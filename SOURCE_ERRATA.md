# Source discrepancies

## Section 23, p. 105: interpreting the Abel-strip description

The displayed Abel weight is indexed by the period-two Fourier frequency,
while a physical period-one mode has index 2n on p. 103. Consequently its
exponential weight is exp(2*a*|n|). With these literal conventions, the
printed strip condition |Im z|<a/(2*pi) with H^s boundary traces does not
characterize the Abel space. This observation does not refute a forward-only
interpretation of the source sentence.

At a=log(2), s=0, the function 1/(1-exp(2*pi*i*z)/3) is holomorphic across
the printed closed strip and has smooth periodic square-integrable boundary
traces. Its actual Fourier coefficients are (1/3)^n on nonnegative modes,
while the original weight at 2n is 4^n. The weighted coefficients are
therefore unbounded.
[The original-source witness](NLS/ZakharovShabat/SourceAbelStripCounterexample.lean)
proves that (0,f) lies outside the original normalized Abel-weight image.
The [Section 23 audit](coverage/SECTION_23.md) records the precise distinction.
The corrected half-width a/pi equivalence, with Sobolev norm traces,
and the forward assertion on the printed strip are now proved in
[SourceAbelStripCharacterization.lean](NLS/ZakharovShabat/SourceAbelStripCharacterization.lean).

## Lemma 21.2 proof, p. 97: the cube of the normalization shift

The expansion of (Fn-i*pi*n)^3 prints +(pi*n)^3 as its constant term.
It requires +i*(pi*n)^3. The PDF display was checked directly.
[SourceSection21CubeShiftCorrection.lean](NLS/ZakharovShabat/SourceSection21CubeShiftCorrection.lean)
proves the corrected identity for the actual primitive throughout its
filled spectral domain. At the actual zero source, the printed identity
fails for every nonzero signed normalization index and every spectral
argument, for every finite source exponent above one.

The discrepancy is constant in the spectral variable and integrates to
zero around the circle. The already proved corrected moment formula is
unchanged. See the [Section 21 audit](coverage/SECTION_21.md).

## Lemma 20.2 proof, p. 93: the copied momentum coefficient

The cubic expansion at the start of the proof prints +3H2/4 as its constant
term. Corollary 19.3 on p. 91 instead gives the correct coefficient -3iH2/4.
The PDF displays were checked directly. The difference is the constant
-(3/4)(1+i)H2 and cannot be absorbed by O(lambda^-2) when H2 is nonzero.

[SourceFiniteGapNonzeroMomentum.lean](NLS/ZakharovShabat/SourceFiniteGapNonzeroMomentum.lean)
constructs an actual real finite-gap source with nonzero physical momentum,
using H1 finite-gap density near a signed Fourier mode.
[SourceSection20CubeConstantCorrection.lean](NLS/ZakharovShabat/SourceSection20CubeConstantCorrection.lean)
proves failure of the p. 93 remainder at such a source in every retained
original domain. The correct expansion in
[SourceSection19Laurent.lean](NLS/ZakharovShabat/SourceSection19Laurent.lean)
holds at that same source. Lemma 20.2's frequency identity remains proved;
the changed constant contributes zero to its circle integral.
See the [Section 20 audit](coverage/SECTION_20.md).

## Proposition 17.3 proof, pp. 79–80: power constant and enumeration cutoff

The coordinate-power inequality on p. 79 requires factor two for
1<p<=2. The printed factor 2^(p/2) is false for 1<p<2.
[SourceActionPowerConstant.lean](NLS/ZakharovShabat/SourceActionPowerConstant.lean)
constructs an actual original source with balanced single-mode Birkhoff
image. Its coordinate-power sum is two and its original action-power
sum is one. [SourceActionPowerSum.lean](NLS/ZakharovShabat/SourceActionPowerSum.lean)
proves convergence and the corrected full bound for every real source
in the stated exponent range.

The subsequent cutoff on p. 80 also conflates enumeration position with
absolute spectral index. In the ordering 0,-1,1,-2,2,..., the first 2N+1
positions cover |m|<=N.
[Section17EnumerationCutoff.lean](NLS/ZakharovShabat/Section17EnumerationCutoff.lean)
proves the corrected initial-block and exact tail identities.
[SourceActionCutoffCounterexample.lean](NLS/ZakharovShabat/SourceActionCutoffCounterexample.lean)
constructs an actual source with action one at mode +1 and zero elsewhere.
Its |m|>1 tail is zero, while its tail after the first enumeration position
is one, and the first selected action is already zero.

These corrections preserve Proposition 17.3. The existing proof uses
explicit finite action reductions and a valid small-norm criterion.
The corrected factor still permits the original 4 epsilon target budget.
See the [Section 17 audit](coverage/SECTION_17.md).

## Lemma 11.1 proof, p. 61: an interior zero of the integrand

The proof's recentered integrand contains the factor
lambda-critical_n. The actual critical point is strictly inside every
open real gap, so the assertion of strict positivity at every interior
point is false there. The denominator is strictly positive at this point.

[SourceActionIntegrandCriticalZero.lean](NLS/ZakharovShabat/SourceActionIntegrandCriticalZero.lean)
proves the zero and refutes the literal pointwise assertion for every
finite p>1 and every open real gap. An example constructs an actual real
source with such a zero at any prescribed signed index. The strict
positivity of the action in Lemma 11.1 remains proved by the existing
arcosh integral argument; this correction concerns the intervening
pointwise sentence. See the [Section 11 audit](coverage/SECTION_11.md).

## Section 7: the real collapsed-gap locus has codimension two

The paragraph after (2.3) on printed p. 46 calls the squared-gap zero set
Z_n a real analytic submanifold of real Hilbert space with codimension
one. The original PDF was visually checked. The correct real codimension
is two: gap collapse is exactly x_n=y_n=0 in the globally bi-analytic
physical Birkhoff coordinates.

The formalization identifies the tangent space with all velocities of
local differentiable curves in the literal squared-gap zero set. It also
constructs a global real analytic curve in the set for every tangent
direction. The real quotient by that tangent space has dimension two.
The zero physical potential belongs to every Z_n, so the printed value
one fails there for every spectral index.

[PhysicalClosedGapTangents.lean](NLS/ZakharovShabat/PhysicalClosedGapTangents.lean)
proves the tangent characterization and the explicit negation of the
codimension-one value. The [Section 7 audit](coverage/SECTION_7.md)
records the bounded coordinate insertion and the full global chart.
This correction concerns real codimension; no complex-variety
codimension assertion is inferred.

## Section 7: the overview psi product repeats the wrong denominator index

The unnumbered psi product on printed p. 46 places pi_n in every factor
indexed by m≠n. The original PDF was visually checked. The denominator
inside the product must be pi_m; the outer factor -2/pi_n is retained.

At the free potential, n=0 and lambda=0, the literal printed symmetric
cutoffs have norms at least 2*4^N. Those norms tend to infinity, so the
product converges to no complex value. This is a limit counterexample,
not merely a discrepancy at a finite cutoff. Under the corrected
mode-dependent normalization, every cutoff at that point equals -2.

[SourceSection7PsiNormalization.lean](NLS/ZakharovShabat/SourceSection7PsiNormalization.lean)
proves the literal specialization, norm growth, divergence and corrected
finite values. The [Section 7 audit](coverage/SECTION_7.md) records the
relationship to the later normalized psi construction.

## Section 24: higher actions do not all detect open gaps

Printed p. 106 asserts that every action at level k≥2 vanishes if and
only if the corresponding gap is closed. This fails already at level
two and at a real source. For every retained original Section 24 domain
U and every c>0, `SourceSection24Data.exists_levelTwo_zero_of_action_pos`
constructs a real finite-gap source in U with I₀=c, an open central gap,
and J₀,₂=0. `section24_levelTwo_zero_counterexample` supplies an
unconditional actual source with c=1.

The proof uses central-action reduction and the physical momentum bracket
at index zero: the level-two action stays constant and is zero at gap
collapse. This is a counterexample for the original contour-defined action.
`SourceSection24Data.not_higherAction_zero_iff_gap_zero` formally negates
the printed equivalence on each retained domain.

The valid statements retained here are that odd printed levels detect
open gaps at real sources, and that collapsed complex gaps contribute
zero at every level. At the constructed source the level-three action
is nonzero. No general complex-source converse is asserted.

Implemented in
[`SourceSection24ZeroDetectionCorrection.lean`](NLS/ZakharovShabat/SourceSection24ZeroDetectionCorrection.lean).
See [the Section 24 audit](coverage/SECTION_24.md) for exact domains and
the independently proved higher-action asymptotic.

## Section 23: the higher-action trace needs all integer indices and a positive sign

The outline on printed p. 105 writes a sum over n≥1 with coefficient
(−1)^(m+1)/4ᵐ. Both features fail for the physical Hamiltonians used by
the source. Theorem 24.1 on p. 107 instead has the full integer sum and
positive coefficient 1/4ᵐ at odd levels.

`section23_positiveIndex_trace_counterexample` constructs an actual
source with only I₀=1. Every positive-index higher-action sum is zero,
whereas its physical H₃ is at least one. Thus the restricted sum is
wrong independently of the sign issue.
The introductory trace display on printed p. 14 repeats the same n≥1
restriction and is refuted by this same source. Its positive coefficient
is correct; the index set must include all integers.

`section23_alternating_trace_counterexample` constructs an actual
finite-gap source with H₅>0. Even after including every integer index,
the level-five sum is H₅/16 and is not −H₅/16. The two counterexamples
use the original indexed higher actions, not a model sequence.

Implemented in
[`SourceSection23TraceCorrections.lean`](NLS/ZakharovShabat/SourceSection23TraceCorrections.lean).
The corrected original-domain traces and their precise Sobolev scope
are in [the Section 24 audit](coverage/SECTION_24.md).

## Section 23: the weight-growth bound needs the value at index one

After Theorem 23.4, printed p. 105 claims w(m) ≤ w(0)^|m|.
The normalized M₁ weight w(n) = 1 + |n| has w(1) = 2 and w(0) = 1,
so the printed inequality fails already at m = 1.
`SpectralWeight.section23_printed_geometric_bound_counterexample`
constructs this actual weight and proves the failure.

`SpectralWeight.le_geometric` proves the corrected bound
w(n) ≤ w(0) * w(1)^|n| for every integer n. Submultiplicativity gives
the natural-index induction and symmetry handles negative indices.
The prefactor includes zero even when w(0) > 1, which the source's
weight assumptions allow. The conclusion of at most exponential
growth survives, and the named weighted estimates are unchanged.

Implemented in
[`SpectralWeightGrowth.lean`](NLS/SequenceSpaces/SpectralWeightGrowth.lean).
See [the Section 23 audit](coverage/SECTION_23.md) for the original-map
estimates and the completed trace-outline comparison.

## Section 22: the physical complex phases have the opposite signs

With zₙ = (xₙ − iyₙ)/√2 and wₙ = (xₙ + iyₙ)/√2, the original source
Hamiltonian rotation (−yₙ,xₙ) has velocities (−izₙ,+iwₙ). Equation (4.14)
on printed p. 98 and the coordinate law in Remark 22.3 on p. 101 instead
use exp(+itωʳₙ)zₙ and exp(−itωʳₙ)wₙ. The physical solution uses
exp(−itωʳₙ)zₙ and exp(+itωʳₙ)wₙ. The ordinary NLS flow requires the
same orientation, with its physical mass correction restored.

`SourceSection20Data.equation4_14_printed_sign_counterexample` constructs,
for every nonzero integer index and finite p > 1, an actual real finite-gap
source with positive frequency and both complex amplitudes nonzero.
Both printed trajectories fail to have their source-Hamiltonian velocities.
The construction uses the original local inverse on its open image and
also applies above two without assuming surjectivity.

`printed_flows_not_physical_solutions` proves that, for 1 < p ≤ 2, both
printed-sign source flows fail the all-smooth-approximation solution
definition on ℝ at the same actual finite-gap source. The corrected flows
satisfy that definition. `renormalized_solution_iff_coordinates` proves
the corrected Remark 22.3 in this range, on any time set containing zero;
`ordinary_solution_iff_coordinates` gives its ordinary analogue.
`SourceSection20Data.remark22_3` now proves the full renormalized
characterization for every finite p > 1 on compact symmetric time
intervals, with the original approximation-solution definition.
The analytic and group properties of the coordinate phases survive the
time reversal.

Implemented in
[`SourceSection22SignCorrection.lean`](NLS/ZakharovShabat/SourceSection22SignCorrection.lean)
and [`SourceSection22Solutions.lean`](NLS/ZakharovShabat/SourceSection22Solutions.lean),
with the full characterization in
[`SourceSection22Characterization.lean`](NLS/ZakharovShabat/SourceSection22Characterization.lean).
See [the Section 22 audit](coverage/SECTION_22.md) for exact domains,
physical trajectory analyticity, higher-exponent solutions, and nonextension.

## Section 21: equation (4.13) requires the negative cubic coefficient

Lemma 21.2 on printed p. 97 gives +4/3 times the cubic moment sum.
Its proof concludes with −4/3, consistent with Proposition 21.3 and the
normalization Rₙ⁽ᵐ⁾ = −π⁻¹ ∮ Fₙᵐ dλ. The formal
`SourceSection21MomentData.lemma21_2` proves the corrected identity
using the original Section 19 primitive.

`SourcePrimitivePowerAtlas.printed_lemma21_2_sign_counterexample`
constructs an actual real finite-gap source with I₀ = 1 and every other
action zero. All other cubic moments vanish, while R₀⁽³⁾ is strictly
positive. Hence the printed positive coefficient gives a different
value of the Hamiltonian correction.
The introduction on printed p. 14 also gives +4/3 for the cubic sum.
The same finite-gap witness refutes that sign; the coefficient is −4/3.

## Section 21: the two Hamiltonian proof claims must say nonpositive

The proofs of Proposition 21.3 and Theorem 18.3 on printed p. 98 say
that H* is nonnegative. The statements have the correct sign:
nonpositive, with equality only at zero.

`SourcePrimitivePowerAtlas.printed_nonnegative_hamiltonian_counterexample`
constructs a real H¹ source of physical mass one whose cubic Hamiltonian
is strictly negative.
`SourceOriginalHamiltonianData.printed_nonnegative_action_hamiltonian_counterexample`
places such a source's original actions in both the chosen Hamiltonian
domain L and the nonnegative ℓ² cone, with a strictly negative value of
that same Hamiltonian. The domain is not replaced by the whole cone.

All three witnesses are implemented in
[`SourceSection21SignCorrections.lean`](NLS/ZakharovShabat/SourceSection21SignCorrections.lean).
See [the Section 21 audit](coverage/SECTION_21.md) for the common original
moment, source-Hamiltonian, action-gradient, and concavity package.

## Section 18: the full Hamiltonian Hessian includes the mass-square term

The expansion on printed p. 83 includes 2H₁², but the next display gives
∂Iₙ∂IₘH(0)=−2δₙₘ. Restoring the mass contribution gives 4−2δₙₘ instead.
`SourceOriginalHamiltonianData.restored_frequency_derivative` proves this
formula for the original frequency. The diagonal is +2.

This discrepancy is checked against actual physical sources:
`exists_realSobolev_single_action` realizes any nonnegative single action
as a real finite-gap H¹ potential, with its physical mass and weighted
spectral sum. `single_action_physical_energy` identifies the full energy
on each such action axis. `full_hessian_diagonal` and
`full_hessian_ne_printed` prove its second derivative at zero is +2 and
cannot be the printed −2. The −2 diagonal belongs to H*, whose full Hessian
is −2 times the bilinear Hilbert pairing. The identical introductory
full-Hamiltonian display has the same correction.

## Section 18: H* requires the weighted linear action subtraction

The paragraph before Theorem 18.3 on printed p. 84 writes H*=H−2H₁²,
omitting the term ∑(2πn)²Iₙ that appears in the earlier definition.
`SourceOriginalHamiltonianData.physical_identity` retains the complete
formula on every real H¹ source. `printed_subtraction_counterexample`
constructs an actual real H¹ source with I₁=1 and every other action zero.
Its weighted sum is 4π², so omitting this term changes the value.
H−2H₁² is instead the renormalized PDE Hamiltonian Hʳ.

Both corrections are implemented in
[`SourceSection18HamiltonianCorrection.lean`](NLS/ZakharovShabat/SourceSection18HamiltonianCorrection.lean).
They preserve Theorem 18.3 and Remark 18.4 for the correctly normalized H*.

## Section 18: the renormalized gauge phase is exp(4 i mass t)

Printed p. 85 gives exp(i ‖u₀‖₂ t). The phase consistent with equation (4.5)
is exp(4 i ‖u₀‖₂² t). `SmoothNLSData.renormalized_phase` proves the exact
conversion for the constructed smooth classical trajectories, using the
physical integral mass. `original_gauge_printed_phase_counterexample`
constructs the constant initial datum one, whose physical mass is one,
and proves that the printed exp(i t) gauge fails the renormalized PDE.
This unit-mass witness refutes the factor independently of the missing
square. Theorem 18.5 uses the corrected trajectories.

Implemented in
[`SourceSection18GaugeCorrection.lean`](NLS/ZakharovShabat/SourceSection18GaugeCorrection.lean).
See [the Section 18 audit](coverage/SECTION_18.md) for the common original
Hamiltonian, frequency, and wellposedness packages.

## Proposition 17.1: normalized canonical images swap the gradient labels

The first display in the proof on printed p. 78 writes A K bₘ±=−d₋ₘ±.
For the actual coordinate gradients and the exact Fourier normalization,
the identities are A K bₘˣ=−d₋ₘʸ and A K bₘʸ=−d₋ₘˣ. The source's next
pairing display already switches to bₘ∓. The formal theorem
`SourceSection16OriginalData.normalizedJacobian_hamiltonian_coordinates`
proves both corrected identities for every real source and p≥2.
`normalizedJacobian_hamiltonian_x_ne_printed` proves the unswapped x
formula is false throughout that range. Proposition 17.1 itself holds
for all finite p>1; below two the proof uses Hilbert kernel transport
and the compact Fredholm alternative.

## Equation (3.9): both angle-flow components must point inward

The display on printed p. 80 has +xₖ/(xₖ²+yₖ²) in the x-component and
−yₖ/(xₖ²+yₖ²) in the y-component. The actual original theta Hamiltonian
has a minus in both components, consistent with the selected action
having derivative −1.

`SourceSection16OriginalData.equation3_9` identifies the actual Jacobian
image with the inward radial vector. For every original Hilbert package,
`equation3_9_printed_sign_counterexample` constructs a real source with
x₀=1 and y₀=0 using the proved global inverse. The true x₀ velocity is −1,
whereas the printed expression is +1. Its positive actual action also
proves that the selected gap is open. Lemma 17.4 holds with the corrected
vector, including uniqueness on the full pre-collapse interval and
continuous displacement in every finite exponent above one. See
[the Section 17 audit](coverage/SECTION_17.md).

## Section 16: inverse-series sign and free-mode witness

The inverse Fourier series and equation (3.4) on printed p. 77 use a plus
before the y-gradient term. With the actual free gradients on p. 76 the
inverse requires a minus. `sourceBirkhoffFourierInverse_single` proves the
exact inverse on arbitrary pairs of single modes, and
`sourceBirkhoffFreeYGradient_ne_fourierInverse_y_mode` proves the printed
positive y term is different. `SourceSection15OriginalData.freeJacobian_y_mode`
checks the sign using the actual original map's derivative at zero.
The same correction applies to the displayed remainder and finite cutoffs.

The second error formula in the proof of Lemma 16.2 on p. 77 also prints
an unscripted ∂zₙ where ∂yₙ is needed. The numbered Lemma 16.2 is unaffected.
Both actual sequence-coordinate gradients satisfy its stated estimates.

## Section 16: the leading minus in the auxiliary product

The displayed ζₙ on printed p. 76 is minus the literal product over m≠n
of (σₘ−λ)/wₘ(λ). `hasProd_sourceSingleRootQuotient_subtype` identifies this
literal product with Q=A/P, where A is the deleted numerator and P the
omitted standard-root product. The actual psi numerator is −2A.

For the original root family, `printed_auxiliary_product_free` proves
−Q=−1 at every free center, contradicting the free leading value +1 used
in the subsequent asymptotic argument. `printed_auxiliary_quotient_zero`
proves that the printed quotient at the zero center is +1/2. Using positive
Q instead gives Q/ψₙ=−1/(2P), the auxiliary required by equation (3.3).

`sourceGapWeightedEtaAuxiliary` uses this corrected expression. It is
analytic throughout the original angular W, equals the actual quotient
at every real source, and has the signed ℓᵖ asymptotic there. Equation
(3.3) is proved at every real collapsed gap. Both moving-terminal terms
are under the same sign in the printed equation; that grouping is correct.
Complex quotient identification requires the psi numerator to be nonzero.
The analytic extension itself requires no such additional premise on W.

## Section 16: the general-p Fourier norm equality needs a bound

The compactness proof on printed p. 77 equates a source p-norm power with
the sum of p-powers of its coefficients in the free gradient basis. The
source norm on p. 22 is the genuine two-component p-norm. At p=4,
`sourceBirkhoffFreeXGradient_norm_fourth` proves that a single free x-gradient
has norm to the fourth power 1/2, whereas its single reconstruction
coefficient has fourth-power sum 1. Thus this coefficient norm equality
cannot be used as a general identity. The witness concerns the norm
identity, not realization of a particular nonlinear remainder.

`sourceBirkhoffNormalizedJacobianCutoff_error_le` instead retains the
bounded inverse Fourier operator factor and the two ℓᵖ majorant tails.
These tails tend to zero, which proves the required operator-norm
convergence and compactness. All-real compactness then uses finite-gap
density and closedness of compact operators. See
[the Section 16 audit](coverage/SECTION_16.md) for exact scopes and APIs.

## Section 15 opening formula: the y-coordinate needs an exponential difference

The first display in Section 15, printed p. 74, writes the y-coordinate as
`ξₙ γₙ / (√8 i) * (exp(iθₙ) + exp(-iθₙ))`, with a plus between the
exponentials. This does not rewrite equation (3.1), whose y-coordinate is
`ξₙ γₙ / √2 * sin θₙ`. The correct exponential form has a minus:
`ξₙ γₙ / (√8 i) * (exp(iθₙ) - exp(-iθₙ))`.

This is a discrepancy in the algebraic rewrite: at θ=0 and ξγ=1 the
printed plus form is nonzero, whereas the sine form is zero. This scalar
check does not assert a potential realizing those particular parameters.
The PDF page was visually checked; the plus is not a text-extraction error.

`sourceBirkhoffY` uses the exponential difference.
`SourceLemma12_12Data.birkhoffXY_original_formula` and
`SourceSection14OriginalData.rectangular_formula` now identify it with the
positive sine of the original integral-defined theta, as in equation (3.1).
The canonical mixed bracket consequently retains the source's -δₙₘ sign.

## Section 15 collapsed limits: the two signs must be distinguished

The narrative on printed p. 74 says the collapsed limit is nonzero when
the Dirichlet root lies outside its periodic gap. The original PDF was
visually checked. The exact identity z_n+ z_n- = gamma_n^2 forces at least
one sign to vanish at a collapsed gap. Both vanish exactly when mu_n=tau_n;
otherwise exactly one is nonzero.

There are actual original-source witnesses: for every finite p>1, every
retained angular domain W, and every neighborhood of zero, some nonzero
constant triangular source (a,0) in W has both central periodic endpoints
zero and a nonzero central Dirichlet root. It belongs to F_0. An explicit
sequence of constant potentials with open central gaps, entirely in W,
converges to this source. Along that sequence the two original signed
phase expressions converge, with exactly one limit zero and the other
nonzero.

[SourceCollapsedOriginalEtaWitness.lean](NLS/ZakharovShabat/SourceCollapsedOriginalEtaWitness.lean)
constructs the witness and sequence and formally refutes simultaneous
nonvanishing of both signs. This is an unconditional source counterexample
within the proved original angular construction, replacing the earlier
conditional interpretation. See [the Section 15 audit](coverage/SECTION_15.md).

## Lemma 12.11: both individual sine asymptotics have a minus sign

Printed p. 70 (visually checked) puts +sin λ in the leading terms of
both ∏ₘ(σₘ−λ)/πₘ and ∏ₘwₘ(λ)/πₘ. The source's convention is π₀=1
and πₘ=mπ for m≠0; its notation table on p. 145 explicitly gives
sin λ=−∏ₘ(mπ−λ)/πₘ. Thus both p. 70 leading terms must be −sin λ.
Products with factors individually divided by πₘ use the symmetric
cutoff convention; the quotient of root factors has an unconditional
product because its factor errors are absolutely summable.

The formal entire single product includes a factor 2, so the first
literal product is `entireSingleSpectralProduct (displacedRoots a) z/2`.
The canonical root includes a factor 2i, so the second is
`sourceCanonicalRoot hp hp1 ψ z/(2*I)`. The theorems
`eventually_centralCircle_sourcePsiNumerator_sine_sign` and
`eventually_centralCircle_sourceStandardProduct_sine_sign` show that
each divided by sin z tends uniformly to −1 on the outer circles.

`sourcePsi_free_product_sineSigns` gives exact −sin z values at the
free source, including at sine zeros. On every half-integer circle sine
is nonzero; `sourcePsi_free_positiveSine_error` proves that each printed
positive-sine normalized error is exactly 2. These are actual products
with the source's zero-mode convention, not a branch-choice ambiguity.

The two missing minus signs cancel in their quotient. The literal
quotient product still tends uniformly to 1, and `sourceLemma12_11`
proves the unchanged conclusion +2π for positively winding original
cycles on exactly the complex domain and root family of Lemma 12.10.


## Lemma 12.10: the order of the local-uniformity quantifiers matters

Printed p. 69 (visually checked) says Qⁿ→Q* in operator norm locally
uniformly on Ωᵖ. The formalization proves the following precise version:
for every ε>0 and every point x∈Ωᵖ, there are a neighborhood U of x in
Ωᵖ and an index cutoff N such that the norm error is below ε for all
y∈U and |n|≥N. This is mathlib's `TendstoLocallyUniformlyOn`. It suffices
for continuity of Q* and uniform convergence on every compact subset.

The stronger order, choosing one neighborhood before all error
tolerances, is false here. At the free source, let a=δeₙ with real
0<δ<π/4. In the original tail disks this is a valid real root input.
The actual Qⁿ ignores its omitted root coordinate, whereas Q* uses all
roots. At row and column n+1 the exact difference is

    [(Qⁿ(δeₙ,0)−Q*(δeₙ,0))eₙ₊₁]ₙ₊₁ = 2δ/π.

Hence the operator-norm error is at least 2δ/π, independently of n.
Choose a fixed δ small enough for any prescribed ball about zero and
move its index to infinity. The inputs remain in that ball and in the
original Ωᵖ, so convergence cannot be uniform there. The theorem
`originalOmega_free_no_uniform_neighborhood` rules out every fixed
relative neighborhood; `sourceLemma12_10_no_fixedUniformNeighborhood`
also constructs an existing original isolating family, for every finite
p>1. The proof concerns the literal original operators, with diagonal
fill 2 at the omitted coordinate.

This is a quantifier clarification of the source's convergence sentence,
not a negation of mathlib's weaker local-uniform statement. The positive
result `sourceLemma12_10_normLimit` proves that statement on every
original real Ωᵖ while retaining Proposition 12.9 and the same W.
Original-domain invertibility and common local complex inverse bounds
are now proved, as is the common analytic solution extension on the
original domains. Lemma 12.10 is complete with this quantifier clarification
and the source-only estimate correction below.

## Lemma 12.10: independently varying roots require a root-distance term

Printed p. 69 states an estimate of the form

    ‖Qⁿ(ψ,t)−Qⁿ(φ,s)‖ ≤ C ‖ψ−φ‖

on a joint source/root neighborhood. If t and s vary independently,
this is false even with ψ=φ=0. Every root ball about zero contains a
nonzero real spike placed in the original disks which changes at least
one actual full Jacobian Qⁿ. The source difference is zero, so no finite
constant can bound that nonzero operator difference by the displayed
right-hand side. The same obstruction holds for the actual deleted blocks.

`original_free_spike_limit_ne_zeroRoot` first proves that the spike changes
Q*. Operator-norm convergence then forces at least one Qⁿ to change.
`original_free_root_variation_on_every_ball` supplies such inputs in every
ball, and `original_free_no_sourceOnly_bound` and
`original_free_no_sourceOnly_deleted_bound` negate the proposed bounds.
`sourceLemma12_10_no_sourceOnly_deleted_bound` constructs an existing
original isolating family for every finite p>1, so the counterexample is
not conditional on hypothetical disk data.

The proved replacement controls the joint distance of roots and sources,
uniformly in n on a common complex ball. It gives the common inverse
bounds used in the formalization. The common analytic extension itself
is proved by `sourceLemma12_10`, with exact agreement on the original
real solutions and placement in the original disks on smaller source
neighborhoods. This counterexample does not rule out source-only estimates
along a prescribed Lipschitz solution graph, where the root difference
can be controlled by the source difference.

## Lemma 12.5: the nonvanishing sentence names the wrong gap

Printed p. 66 (visually checked) obtains a mean-value point μ∈Gₘ and
then says ζₘⁿ does not vanish on Gₙ. The interval needed in that argument
is Gₘ. Every other numerator root lies in its own separated disk, so
ζₘⁿ is nonzero on the selected gap Gₘ, including a collapsed gap.

`SourceIsolatingNeighborhoods.originalZeta_ne_zero_on_gap` proves that
statement for the literal double-omitted product on the original disks.
`SourceLemma12_4Data.originalJacobianEntry_diagonal_meanValue` uses an
actual μ∈Gₘ, and `.originalJacobianEntry_diagonal_ne_zero` concludes the
printed nonzero diagonal assertion. The index correction introduces no
new hypothesis and does not change the statement of Lemma 12.5.

## Lemma 12.4: arbitrary root inputs need not remain in the isolating disks

Printed p. 64 writes σₖ∈Uₖ after (2.24), while Lemma 12.4 allows every
input in the deleted ℓᵖ space. The finite coordinates of such an input
can put a root outside its disk or make two numerator roots coincide.
The later domain Ωᵖ imposes a root-location restriction; the mapping
assertion of Lemma 12.4 does not.

The formalization preserves the unrestricted mapping assertion. It fills
only the unused root with a fixed point in its own original disk, which
does not change the deleted numerator. Compactness of all these fills
and quantitative disk separation yield a bound uniform in the deleted
index. No assumption about the other root locations is introduced.
Public checks include a shift of 100i with exact equation response 200i,
and a shift by π that makes the first and second retained roots coincide.
The local map remains analytic at that collision.

The precise asymptotic (2.26) is now also proved with the same repair.
The unused coordinate is replaced by the fixed base midpoint. One
neighborhood controls all replacements of an arbitrary full input;
contractive coordinate deletion and compact base insertions preserve
the local sequence bounds. The reciprocal-distance error and the actual
disk-supremum ℓᵖ error are separately bounded, uniformly in the unused
index, on the original disks at every complex base in W.

The literal double-omitted product must also be distinguished from the
ratio iQₘ/(σₙ−z) at σₙ=z. The ratio identity has an explicit avoidance
condition. At zero source, n=0, m=1, s₀=i and z=i, the literal ζ₁⁰ and
the contour integrand both equal −1. Lean's totalized quotient at its
zero denominator equals zero instead. Public checks verify both values
and that z=i lies off every free gap. The new product factorization is
valid on the full gap complement, including this point and retained-root
collisions. No division by a possibly vanishing numerator factor is used.

Finally, the printed assertion sup_{n≠m}|Fₘⁿ|=ℓᵖₘ is proved as an actual
supremum sequence: for each full input a, evaluate Fⁿ on its coordinate
deletion. A common ℓᵖ majorant controls every n before taking that
supremum. Uniform bounds on the norms of separate sequences alone would
not justify this assertion.

## Lemma 12.3: the numerator's analytic domain must allow the contour deformation

Source: [dissertation, printed p. 64](https://janbernloehr.de/Download/fs16/diss.pdf#page=64),
visually checked. The stated neighborhood contains the gap and its
circuit. If this is read as an arbitrary open set containing just those
two sets, it does not exclude poles between them. Such poles invalidate
both the bound and the real mean-value conclusion.

`SourceLocalContourDomain.lean` proves an explicit counterexample for
every finite p>1. At zero potential G₀={0} and w₀(z)=−z. Take the positive
unit circle and f(z)=z/(z−1/2). The open set ℂ\{1/2} contains G₀ and the
circle, f is analytic there and real on the real axis, and f(0)=0. But

    ∮ f(z)/w₀(z) dz = −2πi,
    (2πi)⁻¹ ∮ f(z)/w₀(z) dz = −1,
    |(2π)⁻¹ ∮ f(z)/w₀(z) dz| = 1 > 0 = max_{G₀}|f|.

The numerator's pole at 1/2 supplies the extra residue. The circle itself
avoids every free periodic gap, as proved by
`sourceLocalContourPole_circle_rootDomain`. The counterexample is about
the numerator's domain, not a failure of the standard-root branch or
contour orientation.

This clarifies the admissibility convention for the intended local
theorem: the contour must be deformable to the gap inside the numerator's
analytic region. For the current original-circle proofs, analyticity on
a neighborhood of the filled contour disk is an explicit sufficient
condition. An entire numerator meets it automatically. The local argument
is now proved by shrinking ellipses for complex noncollapsed gaps and by
small Cauchy circles at collapse. `sourceLemma12_3_local` constructs an
admissible winding-one contour inside every supplied analytic gap
neighborhood. Original-circle and original-circuit versions explicitly
require the filled-disk condition. Lemma 12.2 also has an adapted local
contour, with reality required only on the gap.

The same rational counterexample now has a verified adapted contour with
normalized period zero. This does not change its unit-circle period −1:
no conclusion is inferred for an arbitrary loop merely contained in a
possibly punctured analytic domain. A general deformation must remain
inside the analytic region, as the clarification requires.

## Equation (2.18): the omitted-disk domain uses the union index

Source: [dissertation, printed p. 62](https://janbernloehr.de/Download/fs16/diss.pdf#page=62),
visually checked. The sentence after (2.18) places the closed disk U_n
under a union indexed by m≠n. The deleted product defining χ_n instead
ranges over m≠n, and Corollary 10.6 removes the corresponding other
closed disks U_m. The consistent domain is therefore
`(ℂ ∖ ⋃_{m≠n} closure(U_m)) × V_φ`.

`SourceEquation2_18Data.fixed` proves analyticity on this corrected
fixed domain for every original isolating family, and `.disk` proves
analyticity throughout U_n×V_φ. The stronger `.joint` assertion holds
on the full moving complement of the other gap segments. The original
source domain and disks are unchanged. This records the index correction;
it does not assert the printed domain with U_n in the union.

## Lemma 10.5 proof: paired indices and absolute convergence

Source: [dissertation, printed p. 57](https://janbernloehr.de/Download/fs16/diss.pdf#page=57),
visually checked. One intermediate estimate prints a_k a_{-m}, although
m is not bound there. The next sentence and the displayed regrouping both
use a_k a_{-k}; this is the pair required by the proof. The existing
`standardRootRelativeError_pair_factor` gives the exact algebraic factor
1+a_k+a_{-k}+a_k a_{-k} for the two actual normalized roots. This local
proof-index typo does not change the statement of Lemma 10.5.

The proof's absolute convergence is understood for its explicitly paired
blocks. `summable_norm_sourceStandardRootOmittedPairedFactor_sub_one`
proves their absolute summability, and the literal symmetric cutoffs
converge to the corresponding product with the factor 1/π_n retained.
This convention must not be replaced by absolute summability of the
individual factor errors. At zero potential the positive-index error
has norm |z|/(π(k+1));
`not_summable_norm_sourceStandardRootRelativeError_zero_source` proves
that its series diverges for every z≠0. The point z=i lies in the actual
free omitted domain, so the distinction persists on the claimed analytic
domain. This is a clarification of the source's explicit regrouping,
not a correction to the paired convergence assertion.

## Lemma 10.4: the selected gap determines the root index

Source: [dissertation, printed p. 56](https://janbernloehr.de/Download/fs16/diss.pdf#page=56),
visually checked. Both the statement and its proof print w_m in the
denominator of an integral along G_n, although m is unbound. The proof's
substitution uses equation (2.12), which gives the side values of w_n:

```
w_n(τ_n + (r ± i0)γ_n/2) = ∓i (γ_n/2) sqrt(1-r²).
```

Consequently the denominator must be w_n for the displayed substitution.
`sourceStandardRootSideIntegral_eq_weighted` proves that substitution
using the actual selected root's boundary trace and affine Jacobian.
`sourceLemma10_4` proves the bound with this consistent index, for every
complex source with a noncollapsed selected gap and every finite p>1.

The index difference has a formal diagnostic. For real-type sources,
`sourceStandardRoot_wrongIndex_midpoint_kernel_im` proves that
(γ_n/2)/w_m(τ_n) has imaginary part zero when m≠n: the half-gap is real,
and w_m is real on the entire distinct real gap G_n. It therefore cannot
equal either +i or -i, the kernel values at r=0 in the printed proof.
`sourceLemma10_4_printed_kernel_counterexample` supplies actual real
sources with γ_n≠0 witnessing this failure, at every finite p>1 and every
n. Nontriviality follows from the existing actual Floquet gap-opening
witness, not from assuming the existence of an open gap.

This formal result refutes the wrong-index substitution. It does not
claim that every possible interpretation of the wrong-index integral
inequality is false. The formalized replacement uses the selected index
n and retains both sides, every endpoint, the original continuity
hypothesis, and the sharp constant one.

## Lemma 10.1: the domain must be a neighborhood of real-type sources

Source: [dissertation, printed p. 54](https://janbernloehr.de/Download/fs16/diss.pdf#page=54),
visually checked. The statement prints an open connected neighborhood of
FL_c^p. The preceding paragraph, the proof's base potentials, and its final
union all use FL_r^p. The printed all-complex version is false.

`sourceCollisionPotential` is the constant source (iπ,iπ), with just the
zero Fourier coefficient in each component. Period doubling preserves it
exactly. On raw frequency k, the actual coefficient operator has block

```
[ -π k   iπ ]
[   iπ   π k ],
```

whose square vanishes when k=+1 or -1. All four component modes at those
two frequencies belong to the second periodic root space and are linearly
independent. `four_le_sourceCollisionMultiplicity` therefore gives actual
algebraic multiplicity at least four at zero, for every finite exponent.
This argument uses the operator and its domain, without a guessed
constant-potential discriminant formula.

`periodicMultiplicity_le_two_of_disjoint_clusters` shows that any disjoint
sets containing all actual indexed periodic pairs force each spectral
multiplicity to be at most two. Hence
`sourceCollisionPotential_not_isolatable` rules out an isolating family
for this source even if disk shape and real centering are dropped.
`not_sourceLemma10_1_all_complex` formally refutes a neighborhood covering
all complex sources at every finite p>1; openness and connectedness are
not needed for the contradiction.

The proved replacement is FL_r^p. `sourceLemma10_1` constructs an open
connected complex neighborhood of that entire locus, with one common
real-centered disk family on each local open connected neighborhood,
including the infimum-distance comparison (2.7) and the exact free tail.
This correction preserves complex perturbations throughout the resulting
domain; it does not restrict all nearby potentials to be real.

## Following Lemma 9.1: exchanged auxiliary monodromy labels

Source: [dissertation, printed p. 53](https://janbernloehr.de/Download/fs16/diss.pdf#page=53),
visually checked against the endpoint domains on p. 33. Those domains are
f₋+i f₊=0 for D* and f₋−i f₊=0 for N*, at both endpoints.
With these labels, their sine-normalized monodromy characteristics are

```
actual D*: (m₄ - m₁ - i(m₃+m₂))/(2i),
actual N*: (m₄ - m₁ + i(m₃+m₂))/(2i).
```

Page 53 prints the plus expression under D* and the minus expression
under N*. `sourceLemma9_1_printed_starredDirichlet` and
`sourceLemma9_1_printed_starredNeumann` identify these expressions with
the opposite actual canonical products at every finite source exponent.
`sourceAuxiliaryCharacteristic_eq_l2_monodromy` proves the domain-consistent
formulas for every physical Hilbert source, with no continuous-representative
assumption. Thus the labels on the monodromy expressions must be exchanged
for them to match the products of the correspondingly labeled eigenvalues.

The swap has mathematical content: `sourceLemma9_1_starred_labels_distinct`
uses the smooth constant potential (1,0) and λ=i to distinguish the two
actual characteristics. `sourceLemma9_1_starred_labels_distinct_source`
proves the same inequality for the actual source products at every finite
p>1, using the single zero Fourier mode in the first component.

The displayed algebraic identity δ=χ_D*−χ_N* remains correct if χ_D*,χ_N*
denote the displayed expressions. In the endpoint-domain labels, the
same anti-discriminant is actual N* minus actual D*. The existence,
analyticity, real-type continuity, and interlacing assertions hold for
both actual auxiliary spectra and are proved in `SourceLemma9_1Auxiliary.lean`.
This correction does not change the valid endpoint signs in Lemma 5.1.

## Lemma 8.6: sign of the midpoint factorization

Source: [dissertation, printed pp. 51–52](https://janbernloehr.de/Download/fs16/diss.pdf#page=51),
visually checked. The proof begins with

```
Δ(λ)^2 - 4 = +4 ((τ_n - λ)^2 - γ_n^2/4) Δ_n(λ),
Δ_n(λ) = (1/π_n^2) ∏_{m≠n} ((λ_m^+ - λ)(λ_m^- - λ))/π_m^2.
```

With this literal deleted-product normalization, the prefactor must be
**-4**, consistent with the full product in Lemma 8.1(iv).
`sourceDeletedPeriodicProduct_formula` identifies the actual deleted
product as the limit of these symmetric cutoffs on the entire spectral
plane. `sourceDiscriminant_midpoint_factorization` proves the corrected
identity for every original source, every index, and every spectral value.

`sourceLemma8_6_printed_factorization_false` refutes the printed identity
at zero potential, n=0, λ=π/2: the left side is -4 and the printed right
side is +4. This is independent of the parity-product normalization
issue in Lemma 8.1.

The sign correction leaves the squared-gap conclusion of Lemma 8.6
unchanged: after differentiation at a critical point the nonzero overall
factor cancels. `sourceLemma8_6` proves that conclusion on a common
original open convex neighborhood, with a uniformly bounded actual ℓp
tail coefficient and a denominator bounded away from zero.

## Equation (2.4) and Lemma 8.1: incompatible parity-product prefactors

Source: [dissertation, printed p. 48](https://janbernloehr.de/Download/fs16/diss.pdf#page=48),
visually checked. The displayed periodic and antiperiodic products have
prefactors -2 and 2, respectively, with the source's zero-mode convention.
At zero potential and λ=0, every finite periodic cutoff is zero and every
printed antiperiodic cutoff is 2. Thus the two proposed discriminants
f+2 and g-2 have the incompatible values 2 and 0.

`SpectralProductSourceAudit.lean` proves this already at finite cutoffs,
refutes the simultaneous limiting identities, and proves that the free
values force prefactors -1 and 4. The proof's periodic cutoff on the same
page does use -1, consistent with the correction. The full product's
prefactor -4 is unchanged.

`exists_sourceDiscriminant_printed_parity_limits` now identifies the literal
printed products for every finite p>1 source: their limits are 2(Δ-2) and
(Δ+2)/2. These functions remain jointly analytic, so part (i)'s analyticity
survives. Part (ii)'s shifted identities require the corrected factors.
The two scaling constants cancel in fg, so the full product in part (iv)
retains its correct normalization.
`sourceLemma8_1` constructs those corrected identities, with literal actual
root products and the original spectral zeros and multiplicities.

## Lemma 8.1(iii): cosine zeros in the stated exterior domain

Source: [dissertation, printed p. 48](https://janbernloehr.de/Download/fs16/diss.pdf#page=48),
visually checked. The displayed quotient Δ/(2 cos λ)-1 is bounded over
the exterior of the open π/4 disks centered at nπ. That exterior includes
λ=(n+1/2)π for arbitrarily large n, where the denominator vanishes.

`FreeCosineZeroAudit.lean` proves separation from every excluded disk,
escape to infinite norm, and vanishing of the free cosine discriminant.
With Lean's totalized division the displayed error is exactly one for any
numerator, so no threshold can give the requested bound for ε=1/2.
With ordinary division that literal quotient is undefined there.
`sourceLemma8_1_printed_cosine_quotient_false` specializes the obstruction
to the actual original-source discriminant. This audits the literal
quotient domain; it does not claim failure on every domain that omits
the denominator zeros, or rule out other interpretations of a removable ratio.

The corrected trace asymptotic uses the additive error divided by
exp(|Im λ|). `exists_uniform_sourceDiscriminant_exterior` proves it and
the additive derivative error and valid derivative sine quotient, on one
original source neighborhood and with one positive spectral threshold.
The whole original exterior is retained. A separate cosine quotient
estimate holds under an explicit positive lower bound relative to
exp(|Im λ|). These results and their scope are indexed in
[the Section 8 audit](coverage/SECTION_8.md).

## Unnumbered finite-gap regularity sentence: complex sources need a qualification

Source: dissertation, printed p. 21, immediately before Corollary 1.6.
The source defines finite-gap potentials by finitely many nonzero gaps,
then says they are smooth and real analytic. The following density
assertion explicitly concerns real type, but the regularity sentence
itself states no such restriction. The unrestricted complex reading is
false. This audit does not infer that the author intended the unrestricted
reading; it records the qualification needed when formalizing it.

For any finite p>1 take the original period-one source `phi=(u,0)` with

```
u_n = 1/(1+|n|),  n in Z.
```

The formal construction `roughTriangularSource hp hp1` lies in `CoeffPair p`
by the exact reciprocal Sobolev-weight summability theorem. It is not of
real type, since its second component is zero and its first coefficient
at index zero is one.

`TriangularPeriodicSpectrum.lean` works directly with the actual
coefficient-space operator and its original one-derivative domain.
For any triangular potential, `T=V*R_0` satisfies `T^2=0`, so the two-term
expression `R_0*(1+T)` supplies both inverse identities at every point
off the free lattice. The negative signed modes remain eigenvectors at
every point of the free lattice. Thus the entire periodic spectrum is
exactly `pi*Z`, with no smoothness or smallness assumption. Applying the
period-one source embedding gives `roughTriangularSource_spectrum`.
The singleton-strip criterion for the actual canonical endpoint labels
then proves `roughTriangularSource_finite_gap`: the set of nonzero
canonical indexed gaps is finite. Identifying every central label is
unnecessary for this literal finite-gap property.

The same coefficients are not in l1, by the exact harmonic threshold.
The Fourier coefficients of every smooth periodic function are in l1.
`roughTriangularCoefficients_no_smooth_representative` therefore excludes
every smooth period-one representative preserving the original Fourier
coefficients. `roughTriangularCoefficients_no_analytic_representative`
excludes every spatially real-analytic periodic representative as well.
`not_every_complex_finiteGap_source_smooth` explicitly negates the
unrestricted all-source assertion at every finite p>1.

These are complex counterexamples, not counterexamples to real-type
finite-gap regularity. `SourceFiniteGapSmoothRealization.lean` already
proves the coefficient-preserving smooth realization for real-type
finite-gap sources, and Corollary 1.6's real-type density remains valid.
`SourceFiniteGapAnalyticRealization.lean` now proves the real-type spatial
real-analyticity claim as well. Its theorem
`sourceFiniteGap_exists_analytic_representative` preserves period one and
every original Fourier coefficient at every finite p>1. The proof uses
the analytic finite-dimensional reconstruction, the same canonical gap
tail under translation, and bounded Sobolev evaluation of the original
physical Fourier sums. Thus the qualified real-type regularity assertion
is proved, while the unrestricted complex assertion remains refuted.
The free periodic spectrum of this rough complex example gives no height
violation; the separate dyadic construction below refutes the all-exponent
printed periodic height.

## Proposition I.4: reversed signs in the displayed Schur block

Source: dissertation, printed page 140, checked in the rendered PDF.
The proof displays Id-A+B*(Id+D)^(-1)*C. For the decomposition of
Id+T, the correct Schur block is Id+A-B*(Id+D)^(-1)*C, as in I.1.

Take A=D=0 and B=C=Id on C. The printed block is 2*Id and has nonzero
determinant. The full operator sends (x,y) to (x+y,x+y), so it is singular,
even though norm(D)=0<1. `sourceI4_printedSchur_false_positive` proves
this false positive, and `sourceI4_correctSchur_zero` proves that the
corrected block is zero. This is an error in the proof formula, not a
counterexample to Proposition I.4's generic local-invertibility statement.

The source domain is relatively open in the nonnegative sequence cone,
which includes zero and other boundary points. The new density argument
uses that relative topology and local analytic extensions of the original
cone map. Compactness is required only at cone parameters. No global
complex extension or ambient interior assumption has been inserted.
Derivative and local-inverse loci are independent of the extension atlas.

The current theorem supplies ambient complex local inverses on the original
weighted spaces, together with their left-inverse identity on the original
cone map, at all points of a relatively open dense locus. This now covers
every positive weight and every real Sobolev order at finite exponent.
The inverses now restrict to actual weighted real sequence spaces for all
these weights and exponents, with both real analytic inverse identities.
The real inverse locus is relatively open and dense from a real local
inverse seed; a differentiable real left inverse suffices under the
compactness hypothesis. Reality follows from the original cone values,
and the real inverse locus is independent of the extension atlas.

The real-analytic representation bridge is now proved.
`SourcePropositionI4RealAnalytic.lean` constructs local complex extensions
from actual real-analytic germs, identifies their derivatives with the
complexification of the original real derivatives, and proves the real
inverse conclusion for those original germs. The power-series construction
has a 2^n coefficient bound and retains at least half the radius. Thus I.4's
statement is covered with the usual real-neighborhood extension meaning of
analyticity and local diffeomorphism at cone boundary points; the density
conclusion uses the relative cone topology. This interpretation and the
weighting transport are not recorded as source errors. The displayed Schur
sign error above is unchanged.

## Lemma I.3: finite exponents and the cutoff convention

Source: dissertation, printed page 140, checked in the rendered PDF.
The statement is proved without a correction for every finite exponent
1<=p<infinity, including p=1. `Coeff.sourceLemmaI3` uses a symmetric head
|n|<=N and the complementary tail |n|>N, with N>=1. This complement equals
the existing boundary-retaining Fourier tail at N+1; the exact identity
and both signed boundary modes are checked. Enlarging a finite head gives
the required symmetric head, so the quantifier over all positive errors
is preserved.

The formal examples also check the hypotheses. The unit vectors are
pointwise bounded but not totally bounded, so the uniform-tail condition
cannot be dropped. At p=infinity the singleton containing the constant-one
sequence is compact, while every symmetric tail has norm at least one;
thus the finite-exponent restriction cannot be dropped. These are boundary
checks, not counterexamples to the printed statement.

The weighted theorem uses raw coefficients for pointwise boundedness and
the exact weighted norm for tails. The compact-operator consequence gives
small full output tails in operator norm, as needed at the start of I.4.
The relative-cone density argument, displayed signs, and real analytic
inverse restriction are audited above. The real inverse restriction
and weighted transport are proved with the stated neighborhood convention.

## Lemma I.1: missing lower-block invertibility hypothesis

Source: dissertation, printed page 139, checked in the rendered PDF.
The statement asserts that invertibility of Id+T implies invertibility of
both Id+D and the Schur complement. The first of these conclusions is false
without an extra assumption, even for bounded operators on C times C.

Take A=D=-Id and B=C=Id. The full operator Id+T maps (x,y) to (y,x), hence
is its own bounded inverse. Its lower-right block Id+D is zero and is not
invertible. `sourceI1_swap_operator`, `sourceI1_swap_isUnit`, and
`sourceI1_lower_not_isUnit` prove these facts; `sourceLemmaI1_printed_false`
refutes the printed biconditional. This counterexample precedes any use of
the inverse of Id+D and does not depend on defining a singular inverse.

The corrected statement assumes Id+D invertible and then asserts that
Id+T is invertible if and only if S=Id+A-B*(Id+D)^(-1)*C is invertible.
`sourceLemmaI1_corrected` proves this for arbitrary complex Banach blocks;
`sourceLemmaI1_sufficient` retains the valid sufficient direction of the
printed version. The direct-sum transfer theorem applies the result to the
original operator on Z through its bounded linear coordinate equivalence.

Corollary I.2 needs no correction: norm(D)<1 supplies the lower inverse,
and the nonzero finite-dimensional Schur determinant gives invertibility.
`sourceCorollaryI2` and `sourceCorollaryI2_on_decomposition` prove the printed
sufficient condition. The norm bound is strict: with A=B=C=0 and D=-Id,
the Schur expression is Id and has determinant one, but Id+T kills the
second coordinate. `sourceCorollaryI2_boundary_counterexample` formalizes
this boundary example; it is not a counterexample to the printed I.2.

I.4's later displayed Schur formula has a separate sign error, audited above.

## Corollary H.2: physical interpretation on the entire H^m source

Source: dissertation, printed page 139. The displayed formula holds at
the stated regularity without a correction. The highest derivative is
represented almost everywhere by the derivative of the penultimate H1
jet; its square is integrable. All lower jets used by the polynomial have
continuous representatives. `sourceCorollaryH2` retains the printed
quantifier order, with one polynomial chosen before every real H^m input,
as well as the stated homogeneity and equal field counts.

`integral_sq_sobolevTopJetPhysical` identifies the leading term with the
actual unit-period integral. The weak-derivative chain is proved using
Mathlib's actual tempered-distribution derivative, and the smooth
comparison recovers the classical mth derivative. The physical Hamiltonian
is the unique continuous extension from the smooth complex hierarchy.
This is an endpoint-regularity verification, not an erratum.

## Lemma H.1: the highest derivative at the printed Sobolev regularity

Source: dissertation, printed page 139, checked in the rendered PDF.
The hypothesis is phi in H^(k-1), while the displayed leading term is
minus the kth derivative of phi_+. Thus at this regularity the leading
derivative is an H^-1 distribution. For k>=2, every remainder jet has
order at most k-2 and a continuous representative; for k=1 the remainder
is zero. This is a weak-derivative interpretation, not a counterexample
or a correction to the printed formula.

`weakSobolevRiccatiDensity` extends the actual derivative-plus-convolution
recurrence to this H^-1 endpoint. Its classical coefficient agreement and
`weakSobolevRiccatiDensity_unique` identify it as the unique continuous
H^-1 extension of the independently defined smooth hierarchy.
`sourceLemmaH1` proves the exact leading-term coefficient formula on all
complex H^(k-1) sources, and `sourceLemmaH1_polynomial` retains the printed
homogeneity, field balance, and derivative bounds.

`sourceLemmaH1_weak` states equality in H^-1.
`sourceLemmaH1_distribution` uses the actual tempered-distribution
derivative after the exact period-one insertion of coefficients. The
remainder's coefficients are the actual Fourier integrals of its
continuous lower-jet polynomial field. The endpoint k=1 and the first
nonlinear case k=2 are both explicitly checked.

## Lemma G.7: an extra pi in the Dirichlet half-wave reference

Source: dissertation, printed page 138, checked in the rendered PDF.
The statement subtracts (e^+_(-2*n*pi)+e^-_(-2*n*pi))/2 from the Dirichlet
eigenvalue gradient. Under the preceding definition
e_alpha(x)=exp(i*pi*alpha*x), the subscripts must instead be -2*n.
The midpoint assertion has no such reference and remains unchanged.

`classicalDirichletNormalizedGradient_free_lattice` proves that the actual
free normalized gradient is (wave(2*n),wave(-2*n))/2, where
wave(m)(s)=exp(i*pi*m*s). The canonical eigenvalues at zero are n*pi,
and `fderiv_canonicalDirichletRoot_zero_eq_free` identifies their actual
derivative with the free functional h |-> (h.fst(-n)+h.snd(n))/2.
The zero H1 source is real and belongs to every complex source neighborhood
used in the corrected result, because each contains the full real locus.

The first component of the printed error is
(exp(2*pi*i*n*s)-exp(2*pi^2*i*n*s))/2. Its Fourier coefficient at mode n
is (1-c_n)/2; G.6's real-frequency integral bound gives |c_n|<=1/2 for
nonzero n. `quarter_le_norm_sourceG7PrintedDirichletErrorCoefficients`
therefore gives a lower bound 1/4 on both signed tails.
`not_eventually_sourceG7PrintedError_majorant` rules out any l2 majorant
even after deleting finitely many spectral indices.
`not_memlp_sourceG7Printed_pair_norms` gives the same failure in the exact
source signed pair norm, regardless of the second component.

`sourceLemmaG7_corrected_with_coefficients` proves both estimates for
finite p>=2 and conjugate q on one common complex neighborhood containing
the real source locus, using the original H1 source. The Dirichlet
Fourier-integral identities explicitly subtract the corrected half waves;
the signed-coordinate isometry and energy identity identify the exact
source norm. The actual corrected derivative error vanishes at zero.
This proves the corrected assertion and does not reinstate its printed
wave normalization.

## Corollary G.6: an extra pi in the anti-discriminant wave index

Source: dissertation, printed page 138, checked in the rendered PDF.
The preceding definition is e_alpha(x)=exp(i*pi*alpha*x), with
e^-_alpha=(e_(-alpha),0) and e^+_alpha=(0,e_alpha).
The second assertion subtracts (-1)^n times
(e^+_(-2*n*pi)-e^-_(-2*n*pi)). Under this definition, its wave frequencies
contain pi twice. The correct subscripts are -2*n.

At zero potential and nu_n=n*pi, the actual i times anti-discriminant
gradient is (-1)^n times (-exp(2*pi*i*n*s),exp(-2*pi*i*n*s)).
The first component of the printed error is therefore (-1)^n times
(exp(2*pi^2*i*n*s)-exp(2*pi*i*n*s)). Its Fourier coefficient at mode n
is (-1)^n times (c_n-1), where c_n is the coefficient of the first
exponential. `sourceG6PrintedWave_diagonal_le_half` bounds |c_n| by 1/2
for every nonzero integer n, using the exact exponential integral and
the frequency-gap bound. Thus the actual inner l2 norm is at least 1/2
at every nonzero n.

`not_memlp_sourceG6PrintedAntiError_norms` and
`not_eventually_sourceG6PrintedError_majorant` prove failure of outer
l2 summability, even after removing any finite spectral head.
`sourceG5_zero_admissible` supplies the original zero H1 source and both
frequency hypotheses. `not_memlp_sourceG6Printed_pair_norms` transfers the
obstruction to the exact source signed pair norm, for any second component.
This refutes the literal second assertion already at p=2.

`sourceCorollaryG6_antiDiscriminant_corrected` proves the estimate after
removing the extra pi. `sourceCorollaryG6_discriminant` proves the first
assertion unchanged. Both hold for every finite 2<=p<infinity with the
printed conjugate exponent, uniformly on exact Chapter 5 H1 source-norm
balls and in the exact finite-exponent output norm of equation (1.2).
The signed Fourier-coordinate and coefficient-energy identities explicitly
identify this output norm. These results do not reinstate the printed
reference. G.7's corresponding wave-index audit is recorded above.

## Lemma G.5: swapped free-reference components and the infinity endpoint

Source: dissertation, printed page 137, checked in the rendered PDF.
Immediately above the lemma, e^-_alpha=(exp(-i*pi*alpha*x),0) and
e^+_alpha=(0,exp(i*pi*alpha*x)). The statement's upper off-diagonal
reference is -e^+_(-2*nu_n/pi), while its lower one is e^-_(-2*nu_n/pi).
However, the proof gives M2 star M2 = e^-_(-2*nu_n/pi) plus errors and
M1 star M1 = e^+_(-2*nu_n/pi) plus errors. Thus the statement swaps the
two superscripts relative to its own proof. The same swap occurs in the
second formula with the lattice reference.

The actual unconjugated potential derivative confirms this discrepancy:
i times the free upper-entry gradient is
(-exp(-i*z)*exp(i*z*s)^2,0), and i times the lower-entry gradient is
(0,exp(i*z)*exp(-i*z*s)^2). `sourceG5_actual_i_free_upper` and
`sourceG5_actual_i_free_lower` prove these identities using the actual
free-gradient representation of the endpoint derivative.

At zero potential and nu_n=n*pi, both source hypotheses hold exactly.
The two printed references coincide, and the first component of the
upper-entry error is -(-1)^n exp(2*pi*i*n*s). Its actual Fourier coefficient
at n has modulus one. `not_memlp_sourceG5PrintedUpperError_norms` proves
failure of the printed outer p=2 assertion; the inner exponent p'=2 is
also exactly the printed conjugate exponent. The majorant and eventual
majorant theorems propagate this obstruction to any full-matrix norm
dominating the component and show that deleting a finite head cannot
help. This is a literal-reference counterexample, not a failure of the
finite-p estimate after exchanging the two superscripts.

There is also a separate failure at p=infinity, p'=1, already established
by `ClassicalGradientInfinityCounterexample.lean`. The smooth period-one
source phi=(1,0) and nu_n=n*pi+i/(2*(abs(n)+1)) satisfy both displacement
conditions. A diagonal gradient component has unequal endpoint traces
and hence is not in Fourier l1, at every spectral index. Its free
reference is zero, so this obstruction survives the off-diagonal
correction. `sourceG5_triangular_coefficients` and
`sourceG5_not_eventually_fourier_l1` explicitly transfer it to the original
period-one H1 source. Multiplication by i does not change Fourier
summability. The proof's strict inequality p'>1+1/p also fails at this
endpoint, where both sides equal one.

The supported correction is upper e^- and lower e^+ in both displayed
references, with the outer range restricted to finite 2<=p<infinity.
`SourceLemmaG5.lean` now proves both corrected finite-p assertions for the
full gradient, uniformly on balls in the exact Chapter 5 source H1 norm.
`classicalHermitianGradientError_eq_correctedReference` identifies the
assembled operator with the actual gradient minus the explicit corrected
reference, and `classicalHermitianCorrectedFreeGradientMatrix_lattice`
checks the (-1)^n phase and signed waves in the second formula. The
Fourier coefficients are actual gradient-valued Bochner integrals, using
the induced operator norm from Hermitian potential directions to Hermitian
matrix operators. This proves the corrected statement; it does not
restore either refuted feature of the printed version.

## Lemma G.3 proof: missing remainder hat in the derivative bound

Source: printed page 136, verified in the rendered PDF. After estimates for
`partial_t (M-E)`, the proof displays `||partial_t M||_lambda = O(1)` uniformly
in abs(lambda)>=1 and t in [0,1], on bounded H1 source sets. That displayed
line is false for M itself. At zero potential and time zero,

    partial_t M(0,z) = diag(-i*z, i*z),
    ||partial_t M(0,z)|| = abs(z).

`norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero` proves this
exact Hermitian operator norm for the actual fundamental matrix.
`sourceG3_printed_full_derivative_false` rules out the claimed uniform bound,
even for real spectral parameters and the singleton zero-potential set.
The exponential weight equals one there.

The estimate needed by the surrounding argument is for `M-E`.
`sourceLemmaG3_weighted_remainder_derivative` proves it on the exact original
periodic H1 source ball of radius M, with explicit constant
`4*(8+pi)*(2*M)*exp(4*(2*M))`, for every nonzero complex z and all t in [0,1].
This is a correction to an intermediate proof line. The stated remainder
conclusions of G.3 retain their existing proofs; the separate epsilon
qualification below also remains in force.


## Lemma G.3: the epsilon range in the printed exponent

Source: dissertation, printed page 136. The wording "any epsilon > 0"
accompanies 1+epsilon <= q <= 2 and exponent (q-1-epsilon)/(1-epsilon).
For epsilon > 1 the q interval is empty. For epsilon = 1 its only possible
point is q=2, where the displayed exponent is 0/0. Thus the meaningful
nonempty range of the printed formula is 0 < epsilon < 1.

`sourceLemmaG3_fourier_decay` and `sourceLemmaG3_shiftedFree_decay` retain
that formula on this range, including q=1+epsilon and q=2. The theorems
`sourceLemmaG3_l2_decay` and `sourceLemmaG3_shiftedFree_l2_decay` state
O(1/|n|) at q=2 without any epsilon parameter, obtained by choosing the
regular value epsilon=1/2. They do not interpret the source's undefined
0/0 using Lean's totalized division. This is a parameter qualification,
not a counterexample to either decay conclusion.


## Lemma G.2: arbitrary-time first inequality under the integral H1 convention

Source: dissertation, printed page 135. This is a **norm-qualified** failure,
not a refutation of every possible interpretation of the unspecified interval
norm. Define the local H1 norm as the square root of the integral of the
squared magnitudes of both potential components and both derivatives.

For the smooth period-one constant potential phi=(1,0), t=1/4 and z=2*pi,
that norm is 1/2. The actual weighted Hermitian first Born operator norm is
1/(2*pi). The first displayed G.2 right side, using this local norm, equals
5/(16*pi), which is strictly smaller. `lemmaG2_firstBorn_integralNorm_counterexample`
proves the strict inequality, while `g2IntegralNormTestPotential_admissible`
checks smoothness, periodicity, and the nonzero spectral parameter. The exact
original oscillatory kernel is evaluated by
`oscillatoryIntegral_const_quarter_period`; no numerical approximation is used.

Consequently this local integral convention cannot validate the printed
first inequality for all nonnegative times. A different interval norm
convention or a change in the estimate would need separate justification.
We do not select such a correction here. The second, unit-interval remainder
bound **does hold** in this same integral H1 norm: it is independently proved
by `l2HermitianRemainder_le_unit_H1`, using a combined endpoint estimate and
G.1. Its factor 3/(2*abs(z)) and coefficient 1+norm(phi)_2 exp(norm(phi)_2)
are unchanged. The same unit-interval consequence is now also proved in
Chapter 5's exact periodic Fourier norm by `sourceLemmaG2_remainder_unit`,
using a constant-one comparison with the integral norm. That theorem does
not select a norm convention for the arbitrary-time local statement.

The new arbitrary-length calculation makes the obstruction quantitative.
For every t>0, the same potential at the real frequency z=pi/(2t) has local
integral norm sqrt(t) and actual weighted first Born norm 2t/pi. Therefore
any estimate B(t)/(2|z|) times this integral norm must have
B(t)>=2/sqrt(t). `lemmaG2_integralNorm_length_necessary` proves this, and
`lemmaG2_integralNorm_no_uniform_numerator` rules out a fixed numerator.

A proved correction candidate is now available:

    ||F(t,z)||_z <= sqrt(1/t+t)/|z| * ||phi||_{H1[0,t]},  t>0.

More generally, the same coefficient with t replaced by T bounds every
intermediate time in [0,T]. The zero-time operator vanishes.
`intervalHermitianFirstBornOperator_weighted_le_local_H1` and
`intervalHermitianFirstBornOperator_weighted_le_interval_H1` prove these
statements for genuine AC/H1 inputs in the Hermitian operator norm.
The sufficient numerator 2*sqrt(1/t+t) divided by the necessary 2/sqrt(t)
is sqrt(1+t^2), with right-hand limit one at zero; both the identity and
limit are proved. No finite-time optimality claim is made.

This correction has not been adopted as the source's intended statement.
The interval norm convention remains unresolved. The public
[2013 Grébert–Kappeler manuscript](https://www.math.uzh.ch/preprint?key1=2013)
has now been inspected: Theorem 2.3, printed p. 13 (PDF p. 19), bounds the
weighted remainder on [0,1] using the global periodic H1 norm and coefficient
3*(1+norm(phi)*exp(norm(phi)))/abs(lambda), for abs(lambda)>=1. This does
not justify the arbitrary-time local norm in G.2. The exact inspected
version is recorded in [the Section 14 audit](coverage/SECTION_14.md).
The [published 2014 reference](https://ems.press/books/elm/205) remains a
separate source version. The verified unit-interval consequence is unchanged.

## The proof of Lemma F.2: a common-path coefficient and a real majorant

Source: dissertation, printed page 134, visually checked in the PDF.
These issues concern intermediate formulas in the proof. The analyticity
statement of F.2 is proved unchanged by identifying actual endpoint
integrals with the already constructed joint analytic primitive.

In (F.3), the common integral from tau_n to nu has coefficient 1/(2*i).
Both endpoint integrals contain that same common path. Averaging therefore
retains its full coefficient 1/i=-i; only the two short endpoint pieces
are halved. `appendixF_shared_path_normalization` proves the exact splitting
algebra, and `appendixF_half_coefficient_ne` proves that the printed half
coefficient differs whenever the common integral is nonzero. The actual
free endpoint average has value -i*nu+i*pi*n, checked nontrivially at n=0,
nu=i, where its value is 1.

The displayed majorant g_k(t)=sqrt(t+|epsilon_k|)/sqrt(t-|epsilon_k|) is
not a real-valued expression for 0<t<|epsilon_k|. It therefore cannot
justify the claimed estimate on all of [0,1] as written. Under Lean's
totalized real square root and division it is zero on that interval.
`appendixF_printed_majorant_counterexample` uses epsilon=i/2, t=1/4,
and w=sqrt(5/16): w^2=t^2-epsilon^2, the actual normalized quotient t/w
has strictly positive norm, while the printed majorant is zero. Thus no
finite constant repairs that pointwise bound under this interpretation.
The imaginary epsilon also avoids a real-parameter root singularity in
the example. An absolute value in the denominator and a treatment of the
moving singularity would be needed for a real-majorant repair; such a
repair is not used or claimed by the formalization.

The formal route constructs finite polygonal integrals, proves their
improper endpoint limits and agreement with admissible C1 curve integrals,
and identifies both endpoint values with the analytic primitive. This
supplies F.2 directly, including complex collapsed gaps.

## Lemma E.2: the neighborhood must meet the real space

Source: dissertation, printed page 131 (visually checked in the PDF).
E.2 calls U an open connected "neighborhood" without specifying its base
point. The proof begins near u in U intersect X_R, so that intersection
must be nonempty. If "neighborhood" means a neighborhood of a real point,
this is the intended condition, not a change to that interpretation.
Both applications in the dissertation use neighborhoods of real-type
potentials and satisfy it.

The reading as an arbitrary nonempty open connected complex domain is
false. `sourceLemmaE2_realSlice_condition_needed` proves the counterexample
X_R=R, X=C, U the ball of radius 1/2 about i, and f identically one.
U is open and connected and its real slice is empty, so f vanishes there
vacuously, but f(i)=1. Nonemptiness of U alone is insufficient.

`sourceLemmaE2` proves the identity with the necessary nonempty real slice
explicit. `sourceLemmaE2_of_real_point` gives the equivalent real-neighborhood
formulation. Neither theorem adds convexity or a contraction condition on
the real and imaginary projections. The general statement uses continuous
complexification coordinates and includes the source's Banach-space case.

## Lemma E.1: the cardinal product must omit the diagonal index

Source: dissertation, printed pages 130-131. The displayed interpolation
formula on page 130 (visually checked in the PDF) writes the product over
m in Z of (sigma_m-z)/(sigma_m-sigma_n). Its factor at m=n has denominator
zero. The residue calculation on page 131 explicitly uses m != n, and
solving that identity gives the omitted-index cardinal product.

`appendixE_all_index_cutoff_eq_zero` proves that every symmetric cutoff
containing n is zero if the all-index formula is interpreted using Lean's
totalized division. This cannot be treated as the intended cardinal
product. `tendsto_appendixEInterpolationKernel` instead proves convergence
of the literal omitted-index cutoffs. The kernel equals one at its own
root and zero at every other root, with the exact derivative normalization.

`sourceLemmaE1_literal` proves the resulting interpolation formula for
all 1 <= p < infinity, including p=1, with the printed circle-supremum
hypothesis. Both infinite operations are specified as symmetric cutoff
limits, as supplied by the source circle proof; no unconditional sum or
absolute convergence is asserted. A focused nonzero example reconstructs
sinc(0)=1 from the simple lattice with its zero-index root moved to i.

## Remark D.3: the subtracted linear term must be the complex sum

Source: dissertation, printed pages 126–127 (visually checked in the PDF).
D.1 defines `A = |sum_m a_m|`, `B = sum_m |a_m|^2`, and `S = sum_m |a_m|`.
D.3 then writes `|prod_m (1+a_m)-1-A| <= |A|^2 exp(S)/2 + B exp(S+S^2)`.
Literal reuse of D.1's nonnegative A in that subtraction is false.

`ProductEstimateNotation.lean` supplies the admissible integer sequence
`a_0=-1/4`, with all other terms zero. It is absolutely summable and every
coefficient has norm at most 1/2. Its product is 3/4, so the literal left
side is 1/2. The right side is `exp(1/4)/32 + exp(5/16)/16`, less than
9/32 since both exponentials are less than 3. The theorem
`printed_D3_absolute_linear_term_fails` verifies the contradiction in Lean.

Taking A to be the **complex sum** in D.3 gives the valid Taylor refinement.
`norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` in
`SignedProductEstimates.lean` proves that interpretation, retaining the
printed 1/2 and `B exp(S+S^2)` constants. The same module proves D.1 with
its printed absolute sum and both inequalities of D.2. No redefinition is
silently applied to the literal source statement.

## Appendix C.1: ordinary Hilbert transform is not an isomorphism

Source: dissertation, Lemma C.1, printed page 125. The operator is
`(Hx)_n = sum_{m != n} x_m/(m-n)`. The isomorphism assertion is false for
every finite 1<p<infinity, extending the earlier exponent-two obstruction.

[`HilbertKernelFactorization.lean`](NLS/Fourier/HilbertKernelFactorization.lean)
proves h(n)=t(n)+t(n-1), with t in every lp space above one and h(n)=-1/n
(zero on the diagonal). For a_N(k)=(-1)^k on 0,...,N,
[`HilbertNotIsomorphismLp.lean`](NLS/Fourier/HilbertNotIsomorphismLp.lean) proves

    norm(a_N)^p = N+1,
    H a_N = t + (-1)^N shift_(N+1) t,
    norm(H a_N) <= 2 norm(t).

`HilbertLpObstruction.not_bounded_below` rules out every nonnegative C with
norm(a)<=C*norm(Ha) for all inputs. Its `no_left_inverse` theorem excludes
continuous linear left inverses. These apply to every bounded operator
agreeing with the printed finite-input formula, independently of construction.
The Banach inverse theorem then excludes bijectivity at every finite p>1.

[`AppendixCSourceTransform.lean`](NLS/Fourier/AppendixCSourceTransform.lean)
proves `sourceLemmaC1_not_bijective`, `sourceLemmaC1_no_isomorphism`, and
`sourceLemmaC1_no_linearEquiv`. The last result also excludes an algebraic
linear equivalence satisfying the original convergent series: its coefficient
formulas would force equality with the already bounded Hilbert operator.
No nonzero-kernel claim or separate failure-of-surjectivity claim is inferred.

The corrected assertion is boundedness, with absolutely convergent rows
for all lp inputs. `sourceLemmaC1_bounded` packages this together with
uniqueness and its norm bound. Existing library proofs use this valid part.
C.2 remains proved with its full two-lattice hypotheses, exact pi factor,
omitted diagonal, and uniform dependence on the specified norms; its source
package is `sourceLemmaC2`. See [the Appendix C audit](coverage/APPENDIX_C.md).

## Theorem 1.1: printed height proved through four; all-exponent assertion refuted

Source: dissertation, printed p. 17 (statement), especially clauses (ii)
and (iii), and p. 27 (proof). The central box uses the original source
height `(1+8||phi||_p)^p`, and this box together with the quarter-pi disks
must contain every periodic eigenvalue.

`SourcePeriodicHeightCounterexample.lean` now proves a counterexample
for every integer P>=100000000. The theorem
`sourcePeriodicPrintedHeight_counterexample` supplies a single original
source psi with equal component norms and `||psi||<=1/16`, an actual
periodic spectral point `z=i*2^P`, and nonmembership in the union of the
printed-height box and high disks for **every** cutoff N. Thus no
neighborhood/cutoff pair can satisfy the printed exhaustion at this
source. `not_sourceTheorem1_1_printed_exhaustion` explicitly negates the
all-source exhaustion assertion at the concrete finite exponent 100000000.
This is an operator-spectrum counterexample, not merely failure of a
sufficient resolvent estimate. The threshold is sufficient, not optimized.
The behavior of each individual exponent between four and this threshold
is not determined by this result.

The construction and its proved constants are:

1. At J=2P, the upper real profile U is the sum, for j=2,...,J, of
   `(4*4^j)` times the tent on `[2^(-j),2^(1-j)]` minus its reflection
   across 1/2. `DyadicTentSum.lean` proves that its original lP coefficient
   norm is at most 640 and its weighted interaction
   `A=integral_0^1 U(x) exp(-2H*x) dx` at H=2^P is at least (P-2)/4.
2. `LowerDyadicTent.lean` puts a tent V of area one on `[1-epsilon,1]`,
   epsilon=2^(-2P). Its original mean is one. Uniform and quadratic-tail
   Fourier bounds, after removing the mean, give an lP coefficient norm
   at most nine. Its interaction
   `B=integral_0^1 V(x) exp(2H*x) dx` is at least
   `exp(2H(1-epsilon))`.
3. `OrderedDyadicSource.lean` proves coefficient/physical compatibility,
   ordered support, and positivity of A and B. The complex interaction
   primitives are iA and -iB. The exact monodromy normalization multiplies
   U by `kappa=-(exp(H)-1)^2/(A*B)`, placing iH in the actual periodic
   spectrum at every finite target exponent p>=2.
4. `DyadicNormalizationBound.lean` proves
   `abs(kappa)<=12/(P-2)`. Indeed the numerator is at most exp(2H),
   the lower interaction cancels that exponential up to
   `exp(2H*epsilon)<=exp(1)<3`, and A>=(P-2)/4.
5. Diagonal similarity balances the component norms while preserving
   the actual spectral point. The original pair norm is exactly
   `2^(1/P) sqrt(abs(kappa)*norm(U_hat)*norm(V_hat))`, hence at most
   `2 sqrt(69120/(P-2))`. For P>=100000000 this is at most 1/16.
   The unchanged printed height is therefore at most `(3/2)^P<2^P`.
   The imaginary part also exceeds pi/4, excluding every disk centered
   on the real free lattice, independently of N.

The original finite-exponent pair norm is the P-th root of the combined
component coefficient energies from equation (1.2). The construction does
not replace it by a maximum norm or a physical-space norm. It uses genuine
continuous piecewise linear profiles and their original Fourier integrals;
no numerical truncation or Galerkin spectral assertion is involved.
The proof uses the existing actual monodromy/discriminant correspondence,
exponent compatibility, and domain-preserving diagonal similarity.

The verified positive results remain valid. `PrintedHeight.lean` gives
the printed height through p=2; `RefinedReciprocalNorm.lean` and
`PrintedHeightFour.lean` extend it through p=4.
`exists_source_periodicCounting_printed_height_up_to_four` in
`SourcePrintedHeightFourCounting.lean` retains the common open convex
source neighborhood, all larger cutoffs, central and distant algebraic
multiplicities, periodic/antiperiodic parity, spectral exhaustion, and
actual analytic moving rectangular projections for 1<=p<=4.
`periodicSpectrum_im_eq_zero_of_realType` retains spectral reality at all
finite exponents. The counterexample sources cannot be of real type.
Equal component norms alone do not imply real type.

At every finite exponent the height-N counting theorem
`exists_uniform_periodicCountingData` still gives one common neighborhood,
all sufficiently large cutoffs, full multiplicities and parity, and
exhaustion. Thus this erratum concerns the specified quantitative height,
not spectral discreteness or the existence of a central counting box.
The known sufficient height `(1+8pM)^p` and the component-product height
`(1+8p sqrt(norm(phi_1)*norm(phi_2)))^p` are separate proved alternatives.
No correction is adopted here.

Earlier estimates remain useful but are logically weaker evidence:
`reciprocal_power_coefficient_four_fails_at_five` refutes a sufficient
power-sum test, and `FreeResolventHeightNecessity.lean` rules out a
uniform free lp-to-l1 resolvent coefficient. Neither alone was a spectral
counterexample. The actual dyadic source above resolves the all-exponent
printed-height obligation negatively.

The necessary exponent dependence is now quantified in
`SourcePeriodicHeightNecessity.lean`. For every integer P>=3, any
nonnegative C_P giving the original-source strip bound
`abs(Im z)<=(1+C_P*norm(psi))^P` for all source spectra must satisfy
`P-2<=276480*C_P^2`. The same conclusion holds if only exhaustion by
a source-dependent central box and the high disks is required.
`sourcePeriodicHeightCoefficient_necessary` and
`sourcePeriodicCountingHeightCoefficient_necessary` prove these two
statements. The corresponding `not_exists_uniform_sourcePeriodic...`
theorems exclude every fixed nonnegative coefficient for all integer
exponents. These bounds follow from the actual balanced dyadic family;
they are not free-resolvent norm obstructions.

`SourcePeriodicExplicitHeight.lean` proves the separate proposed
correction `(1+8pM)^p` in the original source norm, for all finite p>=1.
`mem_resolventSet_of_sourcePeriodicExplicitHeight` includes both horizontal
edges and the entire closed exterior strip.
`sourcePeriodicSpectrum_abs_im_lt_explicit_height` gives strict exclusion
for spectral points. `sourceTheorem1_1_proposed_height` retains one open
convex source neighborhood, every larger cutoff, full central and distant
counting data and parity, central multiplicity 4N+2, exhaustion, equality
with the central cluster projection, and analyticity of the actual moving
rectangular integral. It specializes a general source counting transfer
for any nonnegative coefficient with a proved resolvent bound; the
existing printed-height API remains the coefficient-eight specialization.
No replacement has been adopted. The necessary square-root growth and
sufficient linear growth do not establish an optimal growth rate.

## Theorem 1.4: the all-p printed boundary height is false

Source: dissertation, printed p. 20 (statement) and p. 32 (proof).
The printed box has height `(1+8||phi||_p)^p` in the original period-one
source norm. Clause (iii) asserts that the box and quarter-pi disks contain
all Dirichlet and Neumann eigenvalues. Lean now proves a finite Fourier
counterexample to this assertion, already at p=1024.

For any natural P>=1024, put H=2^P and define

```
S = {n in Z : H <= n < 2^P*H},
A = sum_{n in S} pi*n/(H^2+(pi*n)^2),
a = 1/A,
u_n = a for n in S, u_{-n} = -a for n in S, and zero otherwise.
phi = (u,0), with u(t) = sum_n u_n exp(2*pi*i*n*t).
```

The following chain is verified with the original source and spectrum:

1. The classical triangular equation at z=iH has initial vector (1,1).
   Its solution satisfies the Dirichlet endpoint condition when
   `sum_n u_n/(H-i*pi*n)=2i`. The finite ordinary characteristic agrees
   with the classical one at every finite p>1. Thus this equation gives
   membership in the actual `BoundaryCondition.spectrum .dirichlet` of
   `periodOneBoundaryPotential`; no substitute spectrum is introduced.
2. Pairing the positive and negative coefficients gives `2i*a*A=2i`.
   On n>=H the kernel is at least 1/(6n), so each dyadic block contributes
   at least 1/12. There are P such blocks, hence A>=P/12>0.
3. There are at most 8^P signed coefficients, each of magnitude a. The
   original coefficient-pair norm at exponent P is therefore at most
   `8a <= 96/P <= 3/32`. No reflected-potential norm appears in this bound.
4. The printed height is at most `(7/4)^P < 2^P = H`. Also H>=2>pi/4,
   so iH belongs to none of the quarter-pi disks centered on the real
   free frequencies. This holds for every cutoff N, however large.

The files `TriangularFourierBoundary.lean`, `TriangularOddFourier.lean`,
`TriangularDyadicKernel.lean`, and `TriangularNormalizedBand.lean` prove
these ingredients without enumerating the finite band.
`SourceBoundaryHeightCounterexample.lean` supplies
`sourceBoundaryPrintedHeight_counterexample` for every natural P>=1024
and every N. `not_sourceTheorem1_4_printed_exhaustion` explicitly negates
`forall phi, exists N, spectrum subset printed-box union high-disks` at
p=1024. Since a neighborhood of phi contains phi itself, this also refutes
the stronger neighborhood assertion in the source. The exponent threshold
1024 is a convenient verified choice, not an optimality claim.

The proof on p. 32 applies periodic localization to the reflected
potential `phi^dir`. Lemma 4.3 supplies boundedness of the extension;
the available general estimate includes `intervalExtensionBound hp1 hp`.
Dropping that dependence and using the original source norm does not
follow from the periodic result. The new counterexample settles failure
of the printed all-p statement itself, beyond this gap in the proof.

At p=2 the extension is contractive, and `sourceTheorem1_4_two` still
proves every clause with the exact printed height and original norm.
The finite-p discreteness, reality, height-N counts, and Theorem 1.5's
locally uniform full-sequence bounds remain valid. This counterexample
concerns complex triangular sources and makes no claim against the
real-type spectrum. It does not refute Theorem 1.1's periodic height,
which remains proved through p=4 and is now separately refuted as an
all-exponent assertion by the dyadic construction above. No replacement
boundary height is adopted; other exponents not covered here remain to
be investigated.

### Proved proposed correction and an obstruction to every fixed constant

`SourceBoundaryExplicitHeight.lean` supplies a separate all-p statement
with height

```
H_p(M) = (1 + 8*p*E_p*M)^p,
E_p = BoundaryCondition.intervalExtensionBound hp1 hp
    = 2 * Fourier.halfIntervalBound hp1 hp.
```

E_p is the finite positive bound constructed from the half-interval map
and its discrete Hilbert-transform estimate. It depends on p, not the
source potential. The input M is a bound for the original source norm;
`norm_periodOneBoundaryPotential_le` proves the reflected maximum pair
norm is at most E_p*M. No inverse change-of-pair-norm factor is needed.
The explicit periodic Neumann estimate then gives the actual reflected
resolvent and both ordinary boundary resolvents on `|Im z|>=H_p(M)`.
Every boundary eigenvalue lies strictly inside this strip.

`sourceTheorem1_4_proposed_height` proves both central counts 2N+1,
simple high-disk roots, and exhaustion on one open convex source
neighborhood containing the base source and zero, for every larger cutoff.
The old printed-height transfer theorem is preserved as the coefficient-eight
specialization of `exists_source_boundaryCounting_height_of_bound`.
This is a proved proposed correction, not a proof of the false source
formula or an adopted replacement for it. No optimality is asserted.

There is also a stronger necessary condition. For every integer P>1,
`triangular_height_gt_coefficient` puts the earlier family's eigenvalue
above `(1+C*||phi||_P)^P` whenever C>=0 and 96*C<P.
`sourceBoundaryCountingHeightCoefficient_necessary` proves P<=96*C for
any coefficient that supplies exhaustion for every source at this
exponent, even if each source has its own cutoff.
`not_exists_uniform_sourceBoundaryCountingHeightCoefficient` therefore
rules out every fixed nonnegative replacement for eight at all exponents.
The corresponding global-strip necessity is proved separately. This is
an actual spectral obstruction, and it does not apply to the periodic
spectrum in Theorem 1.1.

## Lemma 26.2: sign of the higher Hamiltonian

Source: [dissertation, Lemma 26.2](https://janbernloehr.de/Download/fs16/diss.pdf#page=113).
The statement and proof contain the factor `(-1)^(m+1) 2^m H_(2m+1)`.
However, [Theorem 24.1, equation (5.4)](https://janbernloehr.de/Download/fs16/diss.pdf#page=107)
states `sum_n J_(n,k) = H_k / 2^(k-1)`. At `k = 2m+1` this gives

```
8^m sum_n J_(n,2m+1) = 2^m H_(2m+1).
```

The additional sign agrees at odd `m` and disagrees at even `m` unless
`H_(2m+1) = 0`. The repository retains the physical Hamiltonians from
Appendix H; it does not absorb this sign into their definition.

Formal results:

- `eight_pow_mul_tsum_realHigherActions` proves the positive trace equality
  on the real H^m source space.
- `printed_even_trace_identity_iff_zero` proves the precise obstruction
  to the printed equality at every even order.
- `classicalNLSHamiltonian_constant_one_five` independently checks the
  Appendix H recurrence: the constant real-type potential `(1,1)` has
  physical `H_5 = 2`.
- `sourceWeightedAction_summable_and_le_half_mass` proves absolute
  summability and the trace-consistent estimate
  `sum_n ⟨2nπ⟩^(2m) |I_n| ≤ C(P,m) ‖ψ‖²/2 + 2^m H_(2m+1)`, where
  `C(P,m) = (1+16π)^(2m) (1+P)^(4m)` and `P` is the norm of an exact
  π-normalized H¹ realization of the period-one source potential.
- `sourceWeightedAction_le_mass` weakens the half-mass factor to the
  full squared pair norm appearing in the printed remainder.

The original-source formulations in
[`SourceSection26Sum.lean`](NLS/ZakharovShabat/SourceSection26Sum.lean)
remove the auxiliary weighted-realization premise and retain the exact
physical norm. The literal printed estimate is valid at odd m.

The entire printed inequality is now formally refuted at m=2 in
[`SourceSection26SignCorrection.lean`](NLS/ZakharovShabat/SourceSection26SignCorrection.lean).
Real Fourier-mode pairs with amplitude 1/n have uniformly bounded H¹
norm and pair mass, but their second-derivative norm is at least n.
The physical Hamiltonian coercivity bound makes H₅ grow without bound.
Thus `section26_printedRhs_negative` makes the full printed positive
remainder minus 4H₅ negative. The original action sum is nonnegative.
`section26_printedInequality_strict_counterexample` proves its absolute
summability and the strict reverse inequality. The witness is an actual
real H² source, and `SourceSection26Data.printed_counterexample` places
it in every retained original U and T.

## Lemma 26.3 proof: physical Sobolev norm splitting

At the end of the proof on printed p. 115 the source uses
`‖ψ‖²_Hm ≤ 2^(m−1)(‖∂^m ψ‖²_L2 + ‖ψ‖²_L2)`.
For the exact physical weight `1+|2nπ|`, this is false already at m=1.
A unit scalar mode at frequency one has weighted norm squared
`(1+2π)²`, whereas the derivative energy plus mass is `(2π)²+1`.
`section26_printed_physicalNorm_split_counterexample` proves this strict
inequality in the same correction module.

Lemma 26.3 itself remains valid. The formal proof uses the quantitative
bound `norm_sobolev_sq_le_highestJet` and absorbs its constant into the
arbitrary ε and source-independent remainder constant. The actual
physical remainder and Hamiltonian conclusions share one constant in
`exists_sourceSection26_remainder_bounds`.

## Formula (5.11): the printed supremum endpoint

The supremum range 0≤i≤m on printed p. 114 is false at m=i=1.
[`SourceSection26SupremumCorrection.lean`](NLS/ZakharovShabat/SourceSection26SupremumCorrection.lean)
constructs a counterexample for every proposed nonnegative constant.
The scalar Fourier source has constant coefficient one and coefficients
1/(Nn) at frequencies 1 through N². Its L² norm is at least one,
its physical H¹ norm is at most 2+2π, and its first derivative at zero
has norm 2πN. The printed right-hand side
`C ‖ψ‖_L²^(−1/2) ‖ψ‖_H¹^(3/2)` is therefore bounded for fixed C,
while the derivative supremum grows without bound.

`section26_supremum_real_counterexample` gives an actual real H² source
with nonzero mass and continuous first derivative.
`section26_supremum_no_uniform_constant` refutes the uniform estimate.
`SourceSection26Data.supremum_counterexample` retains membership in
every original U and T. The argument does not rely on assigning a norm
to an undefined derivative or on a zero norm with negative exponent.

[`SourceSection26Interpolation.lean`](NLS/ZakharovShabat/SourceSection26Interpolation.lean)
proves the valid ranges using the exact physical Hᵐ norm: i<m for the
supremum estimate and i≤m for the L² estimate. Lemma 26.3's monomial
argument uses only i<m and remains valid. See
[the Section 26 audit](coverage/SECTION_26.md).

## Lemma 27.2: the endpoint proof gap is resolved

Source: [dissertation, Lemma 27.2, page 116](https://janbernloehr.de/Download/fs16/diss.pdf#page=116).
The literal estimate is now proved for every m>=1, including m=1 without
smallness or closed-gap restrictions. At m=1 it reads H3<=2*S+S², where
S=sum_n <2*n*pi>² I_n. The proof retains the original indexed actions and
the independently defined physical Hamiltonian.
[`SourceSection27SharpEndpoint.lean`](NLS/ZakharovShabat/SourceSection27SharpEndpoint.lean)
provides `sourceSection27_hamiltonian_estimate_literal` for every order and
the corresponding theorem on the same retained SourceSection27Data family.

The original scalar proof gap is still a valid diagnostic. Its final
estimate H3<=S+2*M², or even H3<=S-M+2*M², does not imply the endpoint from
0<=M<=S alone. [`Lemma272EndpointArithmetic.lean`](NLS/ZakharovShabat/Lemma272EndpointArithmetic.lean)
shows that the maximum of S-M+2*M² is max(S,2*S²), which lies below
2*S+S² exactly for S<=2. The scalar values M=S=3 permit 18 while the target
is 15. No potential attaining those scalar data and energy was asserted,
and this is not a counterexample to the lemma.

The missing spectral input is now supplied by
[`SourceFiniteGapProfileIdentity.lean`](NLS/ZakharovShabat/SourceFiniteGapProfileIdentity.lean).
For actual finite-gap sources, the analytically filled quotient
Q_n=-i*F_n/root_n equals one plus the explicit positive exterior correction.
Cauchy's formula, the actual weighted arcosh integrals, the signs of the
standard roots, and the exact -2*pi*i contour normalization prove the
identity without importing an external representation formula as an axiom.
[`SourcePrimitivePowerGlobalCubic.lean`](NLS/ZakharovShabat/SourcePrimitivePowerGlobalCubic.lean)
uses it to prove R_n>=(3/4)*I_n², then extends this inequality by continuity
and finite-gap density to every real source at every finite p>1.

[`SourceH1SharpEndpoint.lean`](NLS/ZakharovShabat/SourceH1SharpEndpoint.lean)
combines the sharp zero-mode bound with 2*M-I_0<=S and the actual physical
energy identity. It proves H3<=S-M+S² and hence the literal endpoint.
The closed-zero-gap estimate H3<=S-M+S²/2 remains a stronger bound on that
special class. The former conditional kernel criteria and twice-remainder
bound also remain valid; they are no longer substitutes for the unrestricted
statement. An infinite-gap profile identity is not claimed and is not
needed for the completed estimate.

Theorem 23.2(ii), Theorem 23.1, and Remark 23.3 keep their previously proved
constants. [`SourceSection27DerivativeBound.lean`](NLS/ZakharovShabat/SourceSection27DerivativeBound.lean)
retains coefficient one on the top weighted-action sum and the final
unweighted mass factor. The original family and the full proof are mapped
in [the Section 27 audit](coverage/SECTION_27.md).

For comparison, [the cited paper, Lemma 16, page 27](https://arxiv.org/pdf/1403.1369#page=27)
uses the different remainder `(64π)^(2m) (1+M)^(2m-1) S^(2m-1)`.
Its coefficient does not disappear at m=1. This comparison explains why
that paper's bound alone did not establish the dissertation's endpoint;
the new proof establishes the dissertation's literal statement directly.

## Lemma 28.1: the final scalar comparison at n=N

Source: [dissertation, proof of Lemma 28.1, page 118](https://janbernloehr.de/Download/fs16/diss.pdf#page=118).
The displayed final comparison is

```
(n+N+2/5)/(n-N+3/10) ≤ 4/3+2N ≤ 2⟨N⟩,
```

under `n ≥ N`, with `⟨N⟩=1+N` for a nonnegative integer cutoff.
At `n=N=1`, the ratio is 8, exceeding `2⟨N⟩=4`.
The subsequent scalar comparison to `2048(1+‖φ‖H¹²)` also fails for
admissible scalar cutoff data: with `n=N=10` and `Q=‖φ‖H¹²=21/16`,
`N < 8Q ≤ N+1` holds, but

```
128 (n+N+2/5)/(n-N+3/10) = 8704 > 4736 = 2048(1+Q).
```

Formal results in `Lemma281BoundaryArithmetic.lean` prove both numerical
counterexamples. They also prove:

- for `n ≥ N+1`, the ratio is at most `2(N+1)`, recovering the scalar
  constant 2048 when `N ≤ 8Q`;
- for `n ≥ N`, the ratio is at most `8(N+1)`, giving an inclusive scalar
  constant 8192 under the same cutoff condition.

This audit concerns the printed scalar implication and supplies no
potential whose actual spectral factor violates the claimed norm bound.
The corrected scalar comparisons alone do not prove the spectral claim.

The actual real-source scalar bound is now proved independently in
`SourceH1ActionGapEstimate.lean`. The central product has squared norm at
most `8(N+1)`, using critical-point membership in ordered real gaps.
Combined with the exterior constant 128, this gives
`‖χ_n‖_gap ≤ 2048(1+P²)` even at the inclusive boundary. Public examples
recover the bound 4736 for the actual real gap factor at n=±10 under the
norm assumption above. This does not validate the false ratio chain.
The real-source version of Proposition 28.2 follows, with the stronger
constant 1536 (and hence the printed 4608).

The complex action estimate of Proposition 28.2 is now proved independently
in `SourceProposition28_2.lean`, on a connected L²-open neighborhood of the
entire real L² locus. It uses the real-type projection and uniform continuity
of the normalized actions; it does not rely on a complex version of the
false ratio chain.

The complex scalar gap-factor bound of Lemma 28.1 is now also proved
independently in `SourceLemma28_1.lean`, including the entire closed gap
and the inclusive cutoff. A sharper real constant 1024 provides room for
a uniform comparison to the real-type projection on finitely many gaps;
a separate uniform complex tail bound of 3 handles all distant gaps.
The neighborhood is connected and L²-open, contains the entire real L²
locus, and can be shared with Proposition 28.2. The actual complex bound
4736 at n=±10 and P²=21/16 is checked publicly. None of these results
validates the printed intermediate scalar comparison disproved above.

## Lemma 28.1: the literal signed-index ratio

Source: printed page 117, checked in the rendered PDF. The hypothesis
uses ⟨n⟩≥⟨N⟩, but the first rational bound uses signed n directly:

```
|χ_n| ≤ 128(n+N+2/5)/(n−N+3/10).
```

At the actual zero source and n=−1, N=1, the selected gap is collapsed,
the deleted product at its midpoint is exactly one, and the proposed
right-hand side is −512/17. The physical H¹ norm is zero and the printed
cutoff holds. Thus this is an actual source counterexample to the first
inequality, distinct from the scalar-only positive-boundary failures above.

[`SourceSection28SignedIndex.lean`](NLS/ZakharovShabat/SourceSection28SignedIndex.lean)
proves the counterexample, the exact physical cutoff, and its presence in
every retained original U and T. The proof's later restriction to n≥N
and instruction to treat n≤−N similarly requires reflecting the index;
it does not validate the signed formula as printed.

The final χ bound 2048 and action bound 4608 remain proved on a common
connected L²-open restriction of the same original family. The factor-nine
step gives 9·2048=18432 for 4|I_n|/|γ_n|²; division by four gives 4608 for
|I_n|/|γ_n|². The implementation keeps this factor explicit. See
[the Section 28 audit](coverage/SECTION_28.md) for the original-action,
continuity, and uniformity statements.

## Section 2: norm convergence at the infinity endpoint

Source: dissertation, printed page 21, checked in the rendered PDF.
After defining Fourier-Lebesgue spaces for every real s and 1<=p<=infinity,
the source asserts that the Fourier series converges in the same norm.
There is no finite-exponent restriction on that sentence. It is false at
p=infinity.

`InfinityTruncation.lean` proves the exact endpoint criterion: finite
Fourier sums converge in a positive weighted infinity norm if and only if
the weighted coefficients tend to zero outside finite sets. For every
positive weight w, the coefficients 1/w(n) have norm one and every finite
truncation has error exactly one. Thus universal convergence holds exactly
at finite Banach exponents, including p=1.

`SourceSectionTwoConvergence.lean` realizes this counterexample as an actual
period-two tempered distribution with coefficients 1/(1+abs(n))^s for every
real s. Its Fourier sums still converge distributionally. Period two is a
valid instance of the source's arbitrary positive period, so this is an
actual source counterexample, not merely a defect in a coefficient model.

The valid alternatives are norm convergence at finite exponents; norm
convergence for weighted c0 inputs at infinity; or distributional convergence
at every Banach exponent. The last is already proved on the full real Sobolev
scale and remains unchanged. See `coverage/SECTION_2.md` for the precise scope;
the remaining Section 2 duality and gradient assertions are still being audited.

## Section 2: missing frequency reversal in scalar bilinear duality

Source: dissertation, printed pages 21–22, checked in the rendered PDF.
The scalar coefficients use the usual negative Fourier wave in their
extraction. On page 22 the source defines the unconjugated pairing as
sum_n u_n*v_n and calls it a natural extension of distributional action.
The corresponding physical pairing instead uses sum_n u_n*v_(-n).

`SourceSectionTwoPairingAudit.lean` gives an exact smooth period-one
counterexample: u=v=exp(2*pi*i*x). Its actual normalized coefficients have
only the value one at index one. The printed same-index sum is one, whereas
the physical integral of u*v over the unit period is zero. The theorem
`sourceSectionTwo_printed_bilinear_pairing_false` refutes the assertion even
when both inputs are smooth and periodic.

`ArbitraryPeriodBilinearParseval.lean` proves the corrected identity for
all positive periods L and all square-integrable physical inputs, retaining
the factor 1/L. Reversal may be placed in either factor by reindexing.
It separately preserves the ordinary sesquilinear formula with equal
indices and complex conjugation. Physical conjugation reverses the Fourier
index, which explains why the corrected bilinear formula is consistent
with the source's relation to the sesquilinear product.

`SobolevBilinearPairing.lean` constructs the corrected bounded bilinear map
on FL^(s,p) times FL^(-s,q), with absolute convergence and the exact product
of the original norms for every real s and every conjugate Banach pair,
including (1,infinity) and (infinity,1). `SobolevDistributionPairing.lean`
identifies it with normalized actual distributional action on Schwartz
periodizations. `SmoothPeriodicTestLift.lean` lifts every smooth period-two
test without an additional growth hypothesis, and
`SmoothPeriodicDistributionPairing.lean` proves the action identity for all
such tests and arbitrary periodic distributions with the stated coefficients.

Abstract same-index `Coeff.dualPairing` remains valid as coefficient
duality. Its physical interpretation inserts frequency reflection, as the
existing source-gradient constructions already do. The source's signed
pair basis does not remove this discrepancy in its preceding scalar formula.
Arbitrary-positive-period distribution transport is now proved in
`ArbitraryPeriodDistribution.lean` and `ArbitraryPeriodDistributionPairing.lean`.
The normalized coefficient tests periodize to (1/L) times the original
negative Fourier wave; the zero-mode window periodizes to exactly 1/L.
Inverse dilation preserves each raw coefficient, gives unique weighted
Fourier representation, and proves the corrected smooth-test pairing for
every positive period, every real regularity and both conjugate endpoints.
Full scalar duality, including p=1, is now proved with the corrected pairing
in `SobolevFullDuality.lean`; its representative has the exact operator norm.
`SobolevScalarGradient.lean` proves analytic scalar gradients and the Hessian
identity. `SobolevPairGradient.lean` now proves unique analytic pair-gradient
representation for every finite source exponent, including p=1, in the
original pair norms. The infinity-source restriction is detailed below.


## Section 2 gradient paragraph: the source exponent must remain finite

Printed page 21 explicitly restricts the scalar full-dual identification to
1<=p<infinity. That statement is proved, including p=1. The gradient
paragraph on page 22 does not repeat the restriction after introducing
pair spaces at all exponents. If that paragraph is read as asserting a
coefficient gradient for arbitrary analytic functionals on an infinity
source space, the extension is false.

`InfinityDuality.lean` constructs a bounded complex functional on linfinity
that annihilates every finitely supported sequence and is nonzero on the
constant-one sequence. The construction separates the constant sequence
from the closed finite-support subspace by Hahn-Banach on the quotient.
Every l1 coefficient representative would have all coefficients zero,
contradicting the nonzero value. The functional is everywhere analytic and
has no coefficient-gradient representation at any base point.
`Coeff.dualPairing_surjective_iff` proves the exact source-exponent scope:
full coefficient representation is onto the continuous dual if and only if
the source exponent is finite.

`SobolevInfinityDuality.lean` proves the obstruction at every real Sobolev
order and for the exact source weighted infinity pair norm
sup_n w(n)(|a(n)|+|b(n)|). It uses the corrected physical pairing, so changing
the erroneous scalar frequency convention does not remove this obstruction.
The first-component signed-frequency conversion preserves the pairing.

The positive statement is retained in full at finite source exponents.
`SobolevPairGradient.lean` proves unique bounded linear recovery and analytic
pair gradients in both the finite conjugate norm and the separate infinity
pair norm required when p=1. Equal endpoint components have exactly twice
the scalar norm; no maximum-norm replacement is made.

Consequently, the automatic Poisson-regularity sentence at the end of page
22 needs a finite-source restriction for each analytic functional, or an
additional assumption that an infinity-source differential is represented
by the required coefficient gradient. Analyticity alone cannot imply that
assumption. The positive interior statement is now proved by
`SobolevCommonBracket.lean`: full gradients give an absolutely convergent,
analytic bracket on the entire common-state intersection for finite
conjugate source exponents and every real Sobolev order. The intersection
represents the same actual distribution pair on every positive period.
`SobolevEndpointBivector.lean` proves bounded, absolutely convergent pairing
in the original endpoint pair norms when represented gradients are supplied.
Thus the bracket remains valid on these regular functionals.
`SobolevSourceCompatibility.lean` now proves agreement with the existing
physical bracket on the order-zero finite-conjugate overlap.
`SobolevBracketSwap.lean` proves antisymmetry after exchanging the actual
ambient domains and shared state, and both product rules are available.
`SobolevZeroBracket.lean` proves Jacobi on the order-zero Hilbert domain.
These results do not claim closure under nested brackets on every reciprocal
Sobolev intersection or remove the infinity-source obstruction.


## Section 2 sesquilinear convention: the original same-index formula is retained

The scalar discrepancy above concerns the unconjugated physical product.
The printed sesquilinear sum with equal indices is valid.
`SobolevSesquilinearPairing.lean` proves this distinction for all real orders
and both conjugate endpoints: physical conjugation conjugates and reverses
coefficients, so applying it in the second factor of the corrected bilinear
pairing gives the same-index sesquilinear sum.

`SobolevPairSesquilinear.lean` retains the original finite pair norms and
the separate frequencywise sum-norm infinity space in both endpoint
orientations, with constant-one bounds. The full scalar sesquilinear Riesz
map in `SobolevSesquilinearDuality.lean` is conjugate linear in the functional,
not complex linear. This agrees with linearity of the product in its first
argument and conjugate linearity in its second. The previous bilinear
gradient convention is unchanged. The infinity-source analytic obstruction
is also proved in the sesquilinear convention.

The smooth-test distributional identity and normalized L2 integral formula
hold at every positive period in `SobolevSesquilinearDistributionPairing.lean`.
The broader locally integrable-function action is now proved separately in
`PeriodicL1Functional.lean`, `PeriodicL1Pairing.lean`, and
`PeriodicL1Distribution.lean`. These use only interval integrability of the
input and smoothness and periodicity of the test, retaining the exact 1/L
normalization. The unique actual periodic distribution has the normalized
physical Fourier coefficients, and the opposite-index product series is
absolutely convergent. This closes the page-21 normalized action obligation
without inferring it from the L2 special case. The source qualifications
above remain unchanged.

## Proposition 3.1: full period-two scope and the same printed-height discrepancy

Printed page 23 states Proposition 3.1 for every period-two potential at
all finite exponents. Its central box repeats Theorem 1.1's height
`(1+8*norm(phi))^p`. `PeriodTwoPrintedHeightCounting.lean` now proves the
unchanged height and all counts on the entire period-two source space for
1<=p<=4, using the original component-sum norm. It does not assume even
support; the period-one parity clauses are conditional.

`Proposition3_1.lean` assembles the statement and transfers the existing
counterexample through the isometric period-one pair embedding. The
result `proposition3_1_printed_height_counterexample` preserves the norm
bound 1/16, equal component norms, even support, and the actual escaped
spectral point for every cutoff. `not_proposition3_1_all_p` negates all
printed clauses at once at exponent 100000000 through the failed
exhaustion clause. Consequently Proposition 3.1 cannot be certified as
printed for every finite p. Discreteness and real-type reality still hold
at every finite p, as does the separate height-N counting theorem. No
proposed height correction is adopted.

## Lemma 3.2(ii): the original p-to-one pair norm bound is false

Printed pages 23–24 use the source component-sum norm for both the p input
and l1 output, while the proof first estimates each component separately.
Combining those component estimates requires the factor 2^(1-1/p).
The pre-existing `HeightResolvent.lean` theorem explicitly uses the
maximum norm on pairs and remains valid in that norm.

`SourceFreeResolventCounterexample.lean` supplies an actual free-resolvent
counterexample in the original norms at p=2 and lambda=i/10000. Each input
component has only its zero Fourier coefficient, equal to one. The input
norm is sqrt(2), the output norm is 20000, and the printed bound
8/sqrt(abs(Im(lambda)))+1/abs(Im(lambda)) is exactly 10800. Since
20000/sqrt(2)>10800, the printed operator inequality fails. This uses
smooth finite data and a nonreal parameter off the free lattice; it is
neither an infinity-endpoint issue nor a failure merely of a proof estimate.

`PairComponentHolder.lean` proves the component factor and its attainment
by equal components. `SourceFreeResolvent.lean` proves the full corrected
height estimate with that factor, as well as the operator lower bound
2^(1-1/p)/abs(lambda) from the two zero modes. At p=1 the original printed
height bound still holds. No replacement is silently adopted for the
false general assertion.

Clauses (i) and (iii) are valid in the original norms: compactness on l1
is proved by conjugating the actual free resolvent, and the strip estimate
even holds with 4p/r in place of 8p/r. The downstream Corollary 3.3 region
has now been verified in the original norms in `SourceCorollary3_3.lean`.
The contractive conversion of the original potential norm implies the
valid maximum-product Neumann condition with exactly the printed
numerical region. `SourceResolvent.lean` transports the actual inverse,
its two identities, compactness, analyticity, and spectrum to the original
base and one-derivative domain norms. Thus Corollary 3.3 survives the
failure of Lemma 3.2(ii); no extra component factor is needed in its
sufficient region. Nonzero imaginary part is explicit, as required for
the finite denominators in the printed expression.

## Lemma 3.4: the unspecified constant accommodates the source norm

`SourceDoubleResolvent.lean` verifies the sandwich estimate in the original
p-to-one pair norms with c_p=64p². The older maximum-product estimate has
constant 32p². The output conversion to the original l1 component-sum
norm costs at most two; input and potential conversions are contractive.
The source only requires a constant depending on p, so this is a proved
instance of its claim, not a correction to its statement. The proof uses
the existing exact source Fourier remainder, including its boundary
modes. The zero strip is bounded by the full potential remainder, with
the reciprocal frequency term zero under Lean's totalized division.
`sourceLemma3_4` quantifies the constant before every potential and strip;
no period-one restriction or p>1 restriction is added.

## Corollary 3.5: original topology and exact boundary conventions

`SourceCorollary3_5.lean` verifies the printed region for every finite
Banach exponent in the original source topology. No numerical correction
is needed: the box uses height N, with strict real-part and non-strict
imaginary-part bounds, and the high disks are open with abs(n)>N.
The vertical-edge argument retains strips with abs(n)=N. Horizontal
boundary points lie inside the printed box, so their separate resolvent
admissibility is retained in `exists_source_uniform_height_and_strips`.
The neighborhood can be open and convex, containing both the source and
zero, and can serve every larger cutoff. This does not adopt either of
the proposed corrections to the different norm-dependent heights in
Theorems 1.1 and 1.4.

## Equation (1.4): actual integrals and full boundary admissibility

`SourceResolventContours.lean` defines actual normalized operator-norm
circle and rectangle integrals of the original-norm resolvent, and proves
their equality with conjugated maximum-product contour operators on
admissible contours. The proof does not assert that the two norms are
isometric. `sourceEquation1_4` puts the central rectangle and all distant
circles on one common original-norm neighborhood for every finite p.
Horizontal central edges, which belong to the printed box, are proved
admissible separately; exterior resolvent inclusion is insufficient for
them by itself. No change to the printed contour formula is required.

## Lemma 3.6: retain the period-one hypothesis

The source proof explicitly assumes that the potential is period one,
which is even support in period-two Fourier coordinates. `sourceLemma3_6`
implements that assumption through `periodOnePair`, on the original
one-derivative domain and at every finite Banach exponent. The alternate
entry point accepts even support directly. The explicit odd potential
`lemma3_6OddPotential` maps `lemma3_6EvenInput`, proved to lie in the even
domain, outside the even base subspace. This is a check that the hypothesis
is necessary, not an erratum or a weakening of the source statement.

## Equation (1.5): the correct parameter topology and actual restrictions

`SourceEquation1_5.lean` verifies the displayed restricted projectors on
an open neighborhood in period-one potential coordinates, as printed.
`SourceParityRestriction.lean` constructs continuous linear endomorphisms
of the parity subspaces and proves equality with the actual circle and
central rectangular integrals there. The period-one assumption ensures
commutation and is retained throughout. No correction to equation (1.5)
is required. These statements do not change the earlier qualifications
for the separate norm-dependent heights in Proposition 3.1 and Theorems
1.1 and 1.4.

## Rank calculations after equation (1.5): retain the height-N region

`SourcePeriodicCounting.lean` proves the actual original-norm ranks and
algebraic counts for the height-N central box from Corollary 3.5. The
central count is 4N+2, with parity ranks 2N+2 and 2N; each high disk has
rank and algebraic count two, entirely in the index's parity. The exact
contour formulas and original operator-domain eigenfunctions are retained.
The results hold at every finite Banach exponent. They neither remove
the qualification on the different printed norm-dependent height nor
adopt its proposed correction. Positive cutoffs and boundary admissibility
exclude the degenerate central rectangle at N=0.

## Lemma 3.7: preserve the half-squared-gap normalization

`SourceContourTrace.lean`, `SourceContourReduction.lean`, and
`SourceLemma3_7.lean` verify the original-norm midpoint and trace identities.
The centered-square trace is gamma_n squared divided by two, both on the
intrinsic contour range and on a fixed reference range under analytic
transport. No correction is needed, and no diagonalizability assumption
is added at a coincident pair. The source functions are traces of the actual
original-domain restriction, with coefficient-space equality proved by
conjugation. All finite Banach exponents, including p=1, are covered.

## Section 4: the potential map is not the normalized vector matrix

On printed page 29, the displayed assertion `phi = T(q,p)` uses
`T = (1/sqrt(2)) [[1,i],[1,-i]]`. With that normalization, the simultaneous
identity `L_AKNS(q,p) = T⁻¹ L(phi) T` is false. The potential term is scaled
by `1/sqrt(2)`. Printed page 19 already gives the correct relation:
`phi = (q+i*p,q-i*p) = sqrt(2) T(q,p)`.

The normalized vector transformation and both endpoint-domain formulas are
unchanged. `aknsPotential_eq_sqrt_two_smul` proves the correct potential
relation and `aknsAction_intertwining` proves conjugation with that map.
`aknsPotential_ne_vectorMap` distinguishes the two maps at `(q,p)=(1,0)`.
`aknsAction_printed_normalization_false` proves failure of the printed
conjugation at that potential with value `(1,0)` and derivative zero.
`physicalOperator_printed_akns_normalization_false` realizes the failure using
actual derivatives of constant smooth functions (the vector satisfies the
AKNS Dirichlet endpoint condition). These are proofs, not numerical tests.

The original physical L² unitary, physical H¹ norm, dense endpoint domains,
and actual operator conjugation are established using the page 19 potential
map in `AKNSPhysicalNorms.lean` and `AKNSIntervalOperator.lean`. No isometry
of the maximum component norm is asserted. The cached PDF page 29 was
visually checked; the discrepancy is present in the display itself.

## Lemma 4.1: the potential uses the same reflection in both boundary cases

`AKNSReflection.lean` and `SourceLemma4_1.lean` preserve the printed signs:
q is extended evenly and p oddly, and the ZS potential is Dirichlet-reflected
for both problems. Dirichlet and Neumann change only the eigenfunction
reflection. The page 29 potential-normalization correction above remains
in effect in the coordinate identification; no additional correction is
needed for Lemma 4.1. Actual periodic H¹ regularity and the physical and
original-norm operator equations are proved. Spectral exhaustion is stated
as an equality of sets of eigenvalues, without an added multiplicity claim.

## Equations (1.8)–(1.9): normalization and convergence scope

`SourceBoundaryFourier.lean` verifies the printed factor one half, the
sesquilinear physical interval pairing, both boundary signs, and the
reversed frequency in the first component. No correction is needed.
The actual series converges in the original component-sum coefficient
norm and normalized physical L² norm; its sum is the signed reflection.
The page 30 input is arbitrary interval H¹ data, with no endpoint-domain
condition. Its reflection can have jumps, so no uniform or H¹ convergence
is asserted under those hypotheses. The formal result also covers every
original L² input and preserves the original interval L² energy exactly.

## Boundary spaces and Lemma 4.2: original norms and series interpretation

`SourceBoundarySpaces.lean` verifies the closed direct-sum assertions after
(1.9) and Lemma 4.2 without a correction. The scalar-amplitude maps have
exact norm factors 2^(1/p) for finite p and 2 for the source's coupled
supremum norm. They are continuous linear equivalences, not isometries in
these original norms. The infinity norm uses signed source coordinates;
its first component has reversed scalar Fourier frequency.

`SourceBoundarySeries.lean` realizes the printed series as actual periodic
tempered distributions at all Banach exponents and as norm-convergent
series for finite p. This preserves the Section 2 endpoint qualification:
an arbitrary infinity-space series need not converge in that norm.
Lemma 4.2 is proved with the actual physical H¹ interval domain, actual
signed extension, and restriction on the closed unit interval.

## Lemma 4.3: missing half and incorrect odd-kernel constant in the proof

Source: printed page 31, verified against the rendered PDF. The statement
that signed extension is bounded and analytic for 1<p<infinity is valid.
The displayed formulas in its proof do not retain the normalization of
(1.8)–(1.9). Write a^-_k and a^+_k for the input's signed coefficients,
and epsilon=1 for Dirichlet, -1 for Neumann. The correct formulas are

```
c_(2n)   = (a^+_n + epsilon*a^-_n)/2,
c_(2n+1) = (i/pi) * sum_k (a^+_k - epsilon*a^-_k)/(2k-2n-1).
```

For finite Fourier inputs these are `sourceLemma4_3_even_signed` and
`sourceLemma4_3_odd_signed`. The full completed map also has the corrected
even formula and a bounded shifted-Hilbert representation at odd indices.
The printed Dirichlet even formula omits 1/2. The two-sided constant
(1,1) has amplitude 1 at index zero, not 2. The printed odd formula uses
2i in place of i/pi. The one-sided constant (0,1) has amplitude -i/pi
at index one, not -2i. Both inequalities are formally proved as
`sourceLemma4_3_printed_even_counterexample` and
`sourceLemma4_3_printed_odd_counterexample`.

The proof also refers to the input FL¹ norm while proving an FLᵖ-to-FLᵖ
bound; such an FL¹ estimate alone would not establish the stated result.
The formal theorem uses the original FLᵖ norm and proves the needed bound
for all 1<p<infinity. Its p=2 map preserves the original norm and is
identified with actual reflection for arbitrary physical L² interval
pairs. These corrections do not resolve the separate all-p printed-height
failure in Theorem 1.4.

## Lemma 4.4 and the following spectrum definitions (page 32)

The original-norm audit confirms the printed free action m*pi and the
potential-action series: positive Dirichlet sign, negative Neumann sign,
and mode index k-m. Both series converge unconditionally for finite p.
Both operators use the same Dirichlet-reflected potential. No correction
to these formulas is needed. A sufficient explicit bound includes the
factor 2^(1/p) when transferring the auxiliary maximum-norm estimate;
this is not asserted to be optimal or a printed numerical constant.

The spectra defined by actual restricted-pencil bijectivity agree with
the earlier auxiliary spectra and, after the completed interval extension,
with the spectra exhausted by the canonical source labels. This step does
not establish a new original-norm Riesz rank formula or repair the separate
all-exponent printed-height assertion in Theorem 1.4.

## Theorem 1.4 proof: original Riesz restrictions and counts (page 32)

The original-norm audit proves the Riesz argument for both boundary signs
on a common open convex connected neighborhood of the potential and zero.
The actual circle restrictions have rank one; the central rectangular
restrictions have rank 2N+1. Their ranges lie in the original one-derivative
boundary domain, so the displayed restriction of the input to that domain
leaves the ranges and ranks unchanged. Every Jordan-chain step is preserved,
and the ranks count full original algebraic multiplicities.

No correction to these rank formulas is needed for admissible contours
with positive central cutoff. The uniform statement uses the already
established central boxes of height N. It does not repair or reassert the
separate all-exponent norm-dependent height claim in the printed theorem.
In particular, neither a new numerical height nor the degenerate N=0
central rectangle is silently introduced into the counting argument.

## Lemma 4.5: trace normalization and the p=1 endpoint (page 33)

Visual inspection confirms that the printed lemma allows 1<=p<infinity.
The original contour trace requires no normalization correction: it is the
trace of the actual original operator on the rank-one boundary Riesz range,
and equals its enclosed eigenvalue. The domain lift and identification with
the typed boundary range are proved, including preservation of the trace
under the continuous change of norms.

The interval-extension construction of Lemma 4.3 covers 1<p<infinity and
alone does not supply a period-two p=1 realization. The endpoint analytic
conclusion is nevertheless proved by an additional argument. Original p=1
coefficients give a continuous physical potential. Their bounded inclusion
into p=2 is proved to give exactly its physical unit-interval coefficients,
and the completed Hilbert reflection gives the same classical interval
boundary eigenvalue set. Pullback of the Hilbert trace branches establishes
analyticity in the original p=1 norm. This does not assert bounded reflection
into the p=1 space or a p=1 reflected-operator trace. The multiplicity in the
endpoint statement is explicitly that of the original Hilbert boundary
realization. No correction to the printed analytic conclusion is needed.


## Lemma 5.1: auxiliary endpoint signs and the reflected potential (page 33)

Visual inspection confirms the endpoint equations f₋+i f₊=0 for D* and
f₋−i f₊=0 for N*, and the reflected pair (−i f₊, i f₋). The N* extension
uses the negative of that pair. Both extended equations use φneu. The
formal physical phase computation agrees with these signs, including the
potential transformation (i φ₋, −i φ₊). No correction is required for
(1.10), these reflection formulas, or either part of Lemma 5.1.

The physical theorem uses actual periodic H¹ representatives and the
original differential equation almost everywhere. It requires no extra
integrability assumption on the potential; only the separate original-norm
coefficient realization invokes an L² potential. The subsequent Fourier
expansions (1.11)–(1.12) are outside this milestone and are audited next.


## Equation (1.11): ordinary mode in the auxiliary expansion (pages 33–34)

The second line of (1.11) prints E_m^dir as the synthesis vector, although
the pairing uses E_m^d* and the same line defines E_m^d*=i e_m^+ + e_m^−.
The synthesis vector must also be E_m^d*. This is a substantive equality
failure as printed, not a normalization convention: the two zero modes
have physical values (1,1) and (1,i).

`sourceEquation1_11_printed_ordinary_mode_false` proves that, for the
constant original function (1,i), the printed ordinary-mode series does
not have the actual auxiliary reflected coefficients as its sum. Its proof
uses uniqueness of sums and the zero-frequency coefficient. The corrected
series in `sourceEquation1_11_1_12_coefficients` uses the auxiliary mode;
`sourceEquation1_11_1_12` also proves the physical L² sum and exact energy.
The first line's component formula, the half-pairing normalization, and
(1.12)'s N* mode are correct. The later subspace decomposition on page 34
is a separate audit and is not silently included in this correction.


## Page 34: repeated auxiliary D* summand in the direct sum

The displayed decomposition following (1.12) repeats FL_d* as both summands.
The second summand must be FL_n*. The repeated-summand statement is false:
D* contains a nonzero weighted zero mode, so its intersection with itself
is nonzero. `not_isCompl_sourceWeightedAuxiliaryDirichlet_self` proves
this for the original finite-exponent spaces at every real Sobolev order;
`not_isCompl_sourceWeightedAuxiliaryDirichletInfty_self` proves it for the
separate signed coupled-supremum source space.

`isTopCompl_sourceWeightedAuxiliarySubspaces` and its `Infty` counterpart
prove the corrected closed topological D* ⊕ N* decomposition. The amplitude
norm factors are 2^(1/p) and 2 respectively. Finite-exponent mode series
converge in the original norm; the infinity series is proved distributionally,
without adding an infinity-norm convergence claim. This is separate from
the ordinary-mode typo in (1.11).


## Page 34: completed auxiliary maps and spectral scope

The bounded extension and operator-invariance assertions are now proved in
the original spaces without a new sign correction. Bounded interval
completion is proved for 1 < p < ∞, while invariance and restricted pencils
also cover p=1 for already Neumann-reflected potentials. The same ordinary
Neumann-reflected potential is used for both auxiliary boundary signs.
The original extension bound is sufficient; optimality is not claimed.

The actual restricted spectrum is closed, discrete, finite in bounded
regions, and equals the classical physical auxiliary eigenvalue set at p=2.
These results do not settle Proposition 5.2's uniform multiplicities,
reality, or printed norm-dependent height. In particular, they introduce
no replacement for that numerical height claim.


## Proposition 5.2 proof: auxiliary N count 2N−1 on page 35

The proof's final paragraph prints 2N−1 auxiliary N eigenvalues in the
central box. Proposition 5.2(ii) and the preceding zero-potential rank
display on page 34 both give 2N+1 for each auxiliary boundary condition.
The final N count must also be 2N+1.

`exists_sourceAuxiliaryZero_printedBox_count` formally refutes the final
2N−1 count at zero original input, for every sufficiently large cutoff.
The theorem uses the literal printed height (1+8‖0‖)^p = 1, not just the
separate height-N box. Reality proves that these boxes contain the same
free central cluster. The count is the sum of dimensions of full original
auxiliary Jordan root spaces. The physical p=2 multiplicity correspondence
is proved independently through actual physical root spaces.

The general original counting theorem proves 2N+1 in height-N boxes.
For real-type input any nonnegative central height gives the same cluster
and exhaustive localization. The norm-dependent printed height for general
complex input remains a distinct unresolved source claim here; neither
the count correction nor the reality result silently changes that bound.


## Proposition 5.2 proof: actual auxiliary contour ranks

The contour-rank argument is now proved for the actual original auxiliary
restrictions, including their one-derivative domain input, uniform analytic
dependence, and full Jordan multiplicity interpretation. Both central ranks
are 2N+1; both high-disk ranks are one. This confirms the page-35 count
correction without a further phase or normalization correction.

These central contour theorems use rectangles of height N. They do not
settle the separate norm-dependent height printed in Proposition 5.2 for
general complex input. Real-type prescribed-height results and the literal
zero-input count counterexample from the previous milestone remain valid.


## Proposition 5.2: unrestricted printed auxiliary height is false (page 34)

The printed central box has imaginary height (1+8‖φ‖_p)^p for every
1<p<∞. The exhaustive localization assertion fails with this height for
general complex potentials, already at p=1024.

`sourceAuxiliaryPrintedHeight_counterexample` gives, for every natural
P≥1024, the inverse phase rotation of the finite triangular Fourier input.
`sourceAuxiliaryPotentialPhase_symm_ofFinsupp` identifies its finite
coefficients explicitly, and `norm_sourceAuxiliaryHeightCounterexample_le`
bounds its original component-sum norm by 3/32. Its actual auxiliary D*
spectrum contains i·2^P. The printed height is at most (7/4)^P, which is
strictly smaller, and this eigenvalue also lies outside every quarter-pi disk
about a real free frequency. Increasing the real cutoff N cannot repair
exhaustion. `not_sourceProposition5_2_printed_exhaustion` states the formal
negation of universal exhaustion at p=1024.

The exact source phase is an isometry, and the completed Neumann reflection
is proved to correspond to the ordinary Dirichlet reflection at the rotated
input. Thus this transfers the established boundary counterexample without
changing the norm, potential realization, or meaning of spectrum.

At p=2, `sourceProposition5_2_two` proves the unchanged printed height,
uniform full algebraic counts, high-disk simplicity, and exhaustive
localization. The height-N counts for 1<p<∞ and original contour ranks remain valid,
as do prescribed-height results for real-type input.
No replacement numerical height is adopted, and the optimal exponent range
for the printed formula is not asserted. This failure is distinct from
the final 2N−1 count typo on page 35.

## Proposition 6.1 and Lemma 6.9: the printed displacement budget fails locally at zero

Source: printed pages 35 and 43. At p=2 the printed right-hand side is

```
C (‖φ‖²/N + ‖R_(N/2) φ‖²)(1+‖φ‖²)‖φ‖².
```

The earlier `RootDisplacementSourceAudit` proved a reduced-determinant
counterexample. `SourcePeriodTwoDisplacementCounterexample` now connects
that witness to the actual period-two operator and its original domain and
norm. Unit weighting preserves every coefficient and the component-sum norm;
it does not restrict the input to period-one potentials.

For small equal amplitudes t at the two resonant frequencies, the squared
original norm is 2t² and the roots are nπ±t. The printed budget is at most
24C t⁴. Choosing t sufficiently small and n beyond any proposed cutoff
violates even the bound for one actual root in every open neighborhood of
zero. The earlier `not_sourceProposition6_1_printed_pair_sum` refutes the
full signed pair sum. The literal page-35 range n≥N is now refuted by
`not_sourceProposition6_1_printed_positive_pair_sum` in
[SourcePositiveDisplacementTail.lean](NLS/ZakharovShabat/SourcePositiveDisplacementTail.lean),
for any labels covering the actual distant positive disk spectra.
The printed ceiling-half-cutoff budget is included, so rounding does not repair it.
This is a failure of the claimed locally uniform cutoff at zero; no failure
for every individually chosen cutoff at a fixed input is asserted.

The qualitative ℓᵖ asymptotics remain valid.
`sourceProposition6_1_asymptotics` gives actual distant pairs, original-pencil
spectral equivalence, ℓᵖ displacements, and locally uniform small signed
power tails for every finite p>1. The proved corrected quantitative budget
adds the leading Fourier-tail power outside the nonlinear factors. It uses
the discrete convention floor(N/2) in the earlier API. The subsequent
`sourceProposition6_1_corrected_ceilingHalf` and full-cutoff theorem prove
stronger corrected estimates. See `coverage/SECTION_6.md` for exact scope.

`not_sourceLemma6_9_printed_pair_sum` negates the Hilbert budget for the
full signed sum of both labels satisfying `SourceResonantRootPair`. These
are actual original determinant roots with exact scalar analytic orders.
The page-43 display literally sums over n≥N and repeats the ξ⁺ displacement
twice; its exact formulation still requires a separate proof. The existing
signed two-root theorem does not by itself establish that literal claim.
The corrected `sourceLemma6_9`
combines their count, original spectral equivalence, localization, factor-six
gap bound, and corrected displacement sum on one original neighborhood.
No new counterexample or stronger fixed-input failure is inferred here.

## Corollary 6.2: period-two scope resolved by actual restriction

On printed page 35 the preceding paragraph discusses a one-periodic potential,
whereas Corollary 6.2 names the period-two input space. This is not recorded
as a source error. `periodTwoToUnit` constructs the bounded restriction and
unit-period re-expansion for 1<p<∞, retaining the odd input modes through a
shifted Hilbert transform. It agrees with physical Fourier integrals on every
finite input and with actual restriction on arbitrary L² data.

`sourceCorollary6_2` now proves the displayed period-two scope for the original
pair norm: all four complete canonical boundary spectra have locally uniformly
bounded displacement power sums. Separate theorems identify actual spectral
membership and full original Jordan multiplicities. See `coverage/SECTION_6.md`.

## Proposition 6.3: the printed weighted gap estimate fails locally at zero

On printed page 36 the overall potential-norm factor again makes the p=2
right-hand side quartic near zero. This cannot control the actual squared
gap of two resonant modes. `SourceWeightedGapCounterexample` independently
identifies the actual roots nπ±t and their intrinsic squared gap 4t²,
using the counted periodic spectral pair and the spectral equivalence of the
reduced determinant. The original weighted pair norm is retained throughout.

For unit weight, every open neighborhood of zero and every proposed cutoff
contain such a witness exceeding the printed bound. Both natural half-cutoff
roundings fail. `not_sourceProposition6_3_printed_pair_sum` rules out the
printed budget for the full signed sum of actual counted high-pair gaps.
The literal page-36 range n≥N is now handled in
[SourcePositiveGapTail.lean](NLS/ZakharovShabat/SourcePositiveGapTail.lean).
`not_sourceProposition6_3_printed_positive_gap_sum` and
`not_sourceProposition6_3_printed_positive_pair_sum` refute the intrinsic and
labeled positive-index sums using that actual positive-gap witness.
The assertion for all weights therefore already fails at unit weight and
p=2. No failure for every individually chosen cutoff at a fixed input is asserted.

`sourceProposition6_3_corrected` retains an additive leading Fourier-tail
term. `sourceProposition6_3_small_tails` and `sourceProposition6_3_gap_mem`
prove locally small weighted tails and the qualitative weighted ℓᵖ conclusion
for 1<p<∞. The earlier corrected bound uses floor(N/2); the subsequent
`sourceProposition6_3_corrected_ceilingHalf` and full-cutoff theorem prove
stronger corrected bounds. See `coverage/SECTION_6.md` for the exact formula
and central-index qualifications.

## Lemma 6.7(ii): diagonal reality needs the hypothesis used in its proof

Source: dissertation, printed pp. 40–41. The displayed part (ii) states
`a_n(conj λ)=conj(a_n(λ))` before introducing `φ*=±φ` for the b_n⁺ identity.
The source's proof of part (ii) begins by assuming `φ*=±φ` and uses this
assumption for the diagonal as well. The unrestricted complex reading of
the displayed diagonal clause is false.

`SourceResonantCoefficients.lean` identifies the coefficients with actual
original-source corrected potential entries and restores the printed basis
order. `sourceResonantA_constant_center` computes, for constant components
`φ=(a,b)` and n≠0,

```
a_n(nπ) = ab/(2πn).
```

For the single fixed original potential `φ=(1,i)`, this is `i/(2πn)`, which
is nonreal at every positive index where the correction is defined.
`exists_large_nonreal_sourceResonantA` constructs such an index beyond
**every** proposed cutoff, together with the actual source half-contraction
bound `‖T_n²‖≤1/2`. This works for each finite 1≤p<∞, including p=1.
`not_sourceLemma6_7_printed_diagonal` formally refutes the existence of an
individual cutoff making the printed unconditional diagonal identity true
on all subsequent strips. The issue cannot be repaired by enlarging that
cutoff or attributing the failure to a nonconvergent inverse.

The corrected `sourceLemma6_7_ii` assumes `φ*=εφ`, `ε²=1`, for **both**
the diagonal and signed off-diagonal identities. It includes the real-type
and imaginary-type cases and holds locally uniformly on the entire closed
strips. This is a sufficient correction, not a claim that these are the only
potentials having diagonal reality. Lemma 6.7(i), equality of the two
correction diagonals for arbitrary complex potentials, remains unchanged.

## Lemma 6.8(ii): the display differs from the concluding estimate

Printed page 41 sums w(2n)|b_n^±−φ_2n^±|_{U_n} without p-th powers,
and its first inner norm is that of the positive component. The concluding
estimate on printed page 43 instead has p-th powers on both weight and
remainder and uses the full weighted pair norm. These are different
quantitative statements.

`sourceLemma6_8_quantitative` proves the p-power, full-pair form for the
actual original coefficient functions, with all signed indices, genuine
bounded full-strip images, and a common neighborhood and cutoff. It uses
the explicit floor(N/2) tail, including the boundary, and strict 1<p<∞.
The diagonal part agrees with the displayed norm structure. Constants depend
only on p, and exact unit-weight transport introduces no norm comparison loss.

The missing-power issue is now formally refuted under the locally uniform
neighborhood-and-cutoff interpretation. `sourceCubicPotential` has physical
coefficients φ_−(2n)=a and φ_+(0)=b, with all other coefficients zero.
The actual positive remainder at the center is ab²/(2πn)². At a=b=t>0,
p=2, its original squared norm is 2t², while even an enlarged budget using
the full inner pair norm is at most 16C t⁶. The actual remainder is cubic.

`exists_sourceRemainder_exceeding_unpowered_budget` constructs a witness
inside every original open neighborhood of zero, beyond every proposed
common cutoff, with small correction and bounded distant full-strip images.
`not_sourceLemma6_8_printed_sum` refutes the full unpowered signed-tail
estimate for any tail-cutoff function κ(N), including floor and ceiling
half-cutoffs. `not_sourceLemma6_8_unpowered_sum` shows that replacing only
the inner norm with the full pair cannot repair the absent powers.

These are local uniform counterexamples, not a claim that one fixed
finite-support potential violates every individual potential-dependent
cutoff. The previously proved p-power/full-pair estimate remains valid.

The component factor is now independently refuted with the left-hand
powers restored. `sourceReverseCubicPotential` has physical coefficients
φ_−(0)=1 and φ_+(−2n)=t. Its source distance to the same constant background
(1,0) is t; every positive cutoff removes that background. The actual
negative squared remainder at the center is t²/(2πn)^4, whereas the printed
positive-component budget is at most 2C t⁴.

`exists_sourceRemainder_exceeding_component_budget` gives witnesses in
every original open neighborhood of that background, beyond every common
cutoff, with small correction and bounded distant strip images.
`not_sourceLemma6_8_positive_component_sum` formally negates the correctly
squared full signed-tail bound with that budget, for every κ(N)≥1 when
N≥2, including both half-cutoff roundings. This failure is separate from
the absent-power issue: restoring just the powers is insufficient.

The second counterexample is again locally uniform, not a single fixed
perturbation violating all its individual cutoffs. The full pair norm is a
proved sufficient replacement; no uniquely necessary replacement or optimal
constant is asserted.

## Lemma 10.8: original-topology local uniformity fails in general (pages 58–59)

The printed uniformity assertion on ℓp × V_φ is formally false at p=4,
q=1. This resolves the earlier open audit item; it is an actual quotient
counterexample, not just a failure to bound the stronger input norm.

At zero source, choose a_m=b for 1≤m≤L and zero otherwise, so the
midpoint offset is exactly a and belongs to ℓ1. At each free center nπ
outside the block, the quotient equals ∏_(1≤m≤L)(1−b/(π(n−m))).
For 2L<n≤3L and 0≤b≤π, its error from one is at least b/(6π).
Consequently any ℓ2 majorant has norm at least sqrt(L)b/(6π).
Setting L=k⁴ and b=δ/(2k) gives input norm ||a||₄=δ/2 and output
majorant norm at least δk/(12π). These bounds hold for the actual
infinite quotient on its omitted-root domain.

Every actual isolating disk at the free source contains its center.
Its literal supremum therefore dominates the center error. The printed
ℓ1+ℓ2+ℓ(1+) decomposition with locally bounded component norms would
provide a uniformly bounded ℓ2 majorant, a contradiction. It suffices to
bound the ℓ(1+) component's ℓ2 projection; the formal negation therefore
also rules out simultaneous bounds in all its projection exponents.
The counterexample is realized in a genuine open Lemma 10.8 neighborhood,
and a separate theorem proves individual ℓ2 membership of each summable
free-source perturbation's disk supremum.

Implemented in `SourceQuotientBlockRoots.lean`,
`SourceQuotientBlockLowerBound.lean`, and
`SourceQuotientUniformityCounterexample.lean`. A sufficient replacement is
uniformity on explicitly bounded ℓq midpoint-offset families, as already
proved. The original ℓp topology works for q≥p, including infinity.
No assertion is made that every pair q<p fails.

The separate free-sine consequence is now proved without restricting q.
`sourceLemma10_8_freeSine_refined` gives the stronger literal disk-supremum
decomposition ℓ(p/2)+ℓ(1+), locally uniformly in the original source
topology. The ℓq summand in the printed display can therefore be zero.
This result uses the fixed free numerator; it does not contradict the
counterexample above, which varies arbitrary numerator displacements.

The missing estimate comes from transposing the actual nonlinear diagonal
remainder through Young convolution at exponent 2p. Two retained
reciprocal rows have ℓp majorants, giving an ℓ(p/2) product. Combining this
with the quadratic diagonal estimate and the midpoint-center comparison
yields the refined actual midpoint displacement and then the full-disk
free-sine estimate. The construction includes central disks, repeated
roots, and the filled free center. The endpoint remains ℓ(1+), not ℓ1.
See `coverage/SECTION_10.md` for the precise theorem and quantifiers.

## Remark 10.9: the printed remainder class fails for actual real sources

The display on printed p. 59 subtracts

    S_n = sum_(m≠n) γ_m²/(m−n)²

from the midpoint-numerator quotient minus one, and places the literal
disk-supremum remainder in ℓ(p/4)+ℓ(1+). This is false as printed.
`sourceRemark10_9_printed_decomposition_counterexample` proves that at
p=8 every open neighborhood of zero contains an actual real source and
a constructed original isolating-disk family for which no such
decomposition exists. In fact the supremum sequence is outside ℓ².

The proof uses the already verified local inverse Birkhoff chart, not an
assumption that arbitrary spectral gaps can be realized. Scaled real
coordinates |n|^(-1/4) belong to ℓ⁸ but their squares do not belong to ℓ².
The action-radius identity, exact action-gap factorization, and a common
bound on normalized-action roots transfer this obstruction to the
actual squared gaps of arbitrarily small real source potentials.

For these sources the signed lattice sum equals its nonnegative absolute
row. Small midpoint displacement implies that the exact Taylor term

    L_n(z) = sum_(m≠n) γ_m²/[8(τ_m−z)²]

has |L_n(nπ)| ≤ S_n/8. If the printed remainder suprema were in ℓ², the
verified exact Taylor remainder in ℓ(8/4)=ℓ² would force S into ℓ² on
the tail. The finite central head does not change membership. Since the
row at m+1 dominates |γ_m|², this contradicts the constructed gaps.
Each printed supremum is proved bounded above on its full original disk,
so the result does not exploit the totalized value of an unbounded sSup.
The conditional obstruction applies to any isolating family containing
the source; the existential theorem supplies such a family near zero.

Implemented in `QuarterPowerWitness.lean`,
`SourceSquaredGapNonSummability.lean`, `SourceRemark10_9LatticeTerm.lean`,
and `SourceRemark10_9Counterexample.lean`. The corrected statement is
`sourceRemark10_9_exactTaylor`: subtract L_n(z) and retain a locally
uniform ℓ(p/4) supremum remainder for every finite p>1 and every original
disk, including central indices and quasi-normed exponents.

The separate p/2 optimality assertion is now proved in full by
`sourceRemark10_9_halfExponent_optimal`. For every finite p>2, every
r<p/2, and every original-source neighborhood of zero, one actual real
potential has squared gaps, the signed lattice row, and the literal
midpoint-quotient suprema in ℓ(p/2) but outside ℓr. The original isolating
disks are constructed and retained, including all central indices.
The proof uses inverse-chart sequence witnesses, positivity of the
exact Taylor sum, and an intermediate exponent above both one and p/4.
It covers r≤1 and the finite-support endpoint. Optimality is existential;
it is not a claim about every source, and the free source is smoother.
This settles the optimality assertion without reinstating the false
printed remainder display. See `coverage/SECTION_10.md`.

## Section 20: the diagonal auxiliary factor has a pole (page 92)

After (4.9), the text asserts analyticity of both ζₖ and ζₖⁿ on the
isolating disk Uₖ for every k. Formula (4.10) defines the auxiliary
factor by ζₖⁿ=−i ζₖ/(τₙ−λ), with the unused numerator root σₙⁿ filled
by τₙ. The assertion about ζₖⁿ is false on the diagonal k=n.

[`SourceSection20Factors.lean`](NLS/ZakharovShabat/SourceSection20Factors.lean)
defines the literal negative product and the printed quotient without
changing the diagonal case. For the actual zero source in any original
family, the filled root sequence is zero displacement, and the convergent
quotient product is one near nπ. Thus ζₙ=−1 there and the printed ζₙⁿ is
i/(nπ−λ) away from the center. The theorem
`SourceSection20Data.printed_diagonal_auxiliary_not_continuous` proves
that this function is not continuous at nπ. Lean's totalized division
at the center does not remove the punctured-neighborhood obstruction.

The corrected analytic domain for the printed auxiliary quotient is the
selected omitted-gap domain with τₙ excluded, as proved by
`SourceSection20Data.auxiliary_analytic`. On the original isolating disk
the auxiliary-factor claim is used only for k≠n. The regular ζₙ itself
is analytic across the selected gap and supplies the diagonal factor
−i ζₙ/wₙ in (4.9). The off-diagonal factorization and literal convergent
product in (4.9)–(4.10) are also proved. The moment and frequency theorems
do not require the false diagonal auxiliary-factor claim.

See [the Section 20 audit](coverage/SECTION_20.md) for the common original
family, exact formulas, and remaining scope.

## Appendix A.8: the constant-one product estimate (A.4) fails (page 124)

The continuous embedding FL^{1,p} → FL1 for finite p is valid, but the
printed product bound omits the inverse-weight Hölder norm from its proof.
The displayed constant one is false even for finite trigonometric polynomials.
With θ = 2πx/L, take

    u(x) = 2 + exp(iθ),    v(x) = sum_(k=0)^4 exp(ikθ).

Using the Section 2 coefficient weight (1+|n|), their squared norms are
‖u‖_{FL^{1,2}}² = 8 and ‖v‖_{FL2}² = 5. Their product has coefficients
2, 3, 3, 3, 3, 1 at frequencies zero through five, so
‖uv‖_{FL2}² = 41 > 8*5. These identities and the strict failure are proved
for the original distributions at every positive physical period in
[`SobolevProductCounterexample.lean`](NLS/Fourier/SobolevProductCounterexample.lean).
The witnesses and their product are identified with integration against the
actual continuous polynomials. At L=2 the proof's weight (1+|2n/L|) equals
(1+|n|), so the source's alternative normalization does not repair (A.4).

The corrected estimate is

    ‖uv‖_{FLp} ≤ C_p ‖u‖_{FL^{1,p}} ‖v‖_{FLp},
    C_p = ‖((1+|n|)^(-1))_n‖_{ℓ^{p'}},    C_p ≤ 2p.

[`PeriodicSobolevEmbedding.lean`](NLS/Fourier/PeriodicSobolevEmbedding.lean)
proves this bound, the continuous injective inclusion, and preservation of
the entire original distribution. The generalized Young estimate (A.3)
retains its sharp constant one. No constant-one claim is made for (A.4).

## Appendix B.3: zero auxiliary exponents are undefined (page 125)

The printed conditions include gamma>=p1>=beta>=0 and p2,p3>=alpha>=0.
The same formula divides by alpha and beta and uses the power ratios
beta/alpha and gamma/beta. At zero these ordinary real expressions are
undefined; the source states no endpoint convention.

[`AppendixBSourceInequalities.lean`](NLS/SequenceSpaces/AppendixBSourceInequalities.lean)
proves the finite positive interpretation, retaining all printed orderings,
the reciprocal identity, and the exact bound one. Every nested sum converges;
input exponents below one are included. Unit modes prove the constant sharp.

[`MixedYoungZeroExponent.lean`](NLS/SequenceSpaces/MixedYoungZeroExponent.lean)
separately diagnoses the zero cases. Its `TotalizedMixedYoungConditions`
explicitly uses Lean's totalized division and is not a mathematical definition
of the source formula at zero. Under that transcription, both exponent tuples
(0,1,1,1,2,2) and (1,0,1,1,2,2) satisfy the displayed conditions.

Take b(n)=c(n)=(1+|n|)^(-1), both in l2. For alpha=0, the unit sequence a
at zero gives nonzero inner products at k=l=0, and the row of their zeroth
powers consists of ones. For beta=0 and alpha=1, take a(n)=(1+|n|)^(-2)
in l1. Every inner sum is proved finite and strictly positive, but the
middle row of zeroth powers again consists of ones. Both divergence claims
are formalized without relying on 0^0 or the totalized value of a divergent
sum. They do not refute the well-defined positive-exponent estimate.

B.2 retains all infinity endpoints. B.3's current theorem is finite positive;
no infinity convention for its nested power expression is asserted.
See [the Appendix B audit](coverage/APPENDIX_B.md).

## Theorem 23.4 proof, p.119: cutoff boundary and missing norm factor

The first weighted-tail display in the proof uses |n|>=N in its action
sum, |n|>N in its gap sum, and coefficient 4608*||phi||H1^2. These are
separate defects, verified against the rendered PDF.

[SourceSection28TailCounterexample.lean](NLS/ZakharovShabat/SourceSection28TailCounterexample.lean)
constructs an actual real H1 source with I_0=t=1/1000000 and every other
action zero. Its exact physical norm P satisfies 0<P^2<=3*(t+t^2), so
N=0 satisfies the printed cutoff 0<8*P^2<=1. With the original H1 weight,
the printed left side is t while its strict gap tail is zero.

Restoring |n|=0 on the right does not repair the missing 1+ factor:
the actual gap-action bound gives gamma_0^2<=4*t, and hence the resulting
4608*P^2 times the inclusive weighted gap sum is still strictly below t.
Both counterexamples lie in every retained Section 28 source domain.

[SourceSection28TailEstimate.lean](NLS/ZakharovShabat/SourceSection28TailEstimate.lean)
proves the corrected tail with a common inclusive cutoff and coefficient
4608*(1+||a||^2), including absolute summability. Here ||a|| is the exact
original weighted norm; its H1 specialization is the physical norm P.
The independently proved final Theorem 23.4 constants remain unchanged.

## Appendix H: phase of the unreduced remainder

Source: [the intermediate display between H.1 and H.2, page 139](https://janbernloehr.de/Download/fs16/diss.pdf#page=139).
If q_(2m) retains its definition from H.1, the odd-Hamiltonian formula
must read

```
H_(2m+1) = integral |psi^(m)|^2 + (-1)^(m+1) * integral psi*q_(2m).
```

The factor follows from the definition H_k=(-i)^(k+1)*integral(phi_minus*u_k).
[`SourceAppendixHRemainderPhase.lean`](NLS/ZakharovShabat/SourceAppendixHRemainderPhase.lean)
proves the corrected real-source formula, and proves that at even m the
unphased expression is equal exactly when the unreduced remainder integral
vanishes. For the smooth periodic real potential (1,1), the actual H5 is
2 while the unchanged q4 integrates to -2. Its top derivative is zero,
so this is a concrete counterexample to the unphased reuse of q4.

One can absorb the phase by redefining the polynomial in that intermediate
display. H.1 and H.2 themselves need no change: the existential polynomial
p_(2m) in H.2 can include the scalar, and the implemented reduction already
does so. This is separate from the sign correction in Lemma 26.2 and from
the now-resolved endpoint proof gap in Lemma 27.2.
