# Section 18: original frequencies, Hamiltonian, and wellposedness

Source: printed pp. 83–86. Theorems 18.1 and 18.3 and Corollary 18.2 use
the original Section 17 Birkhoff family. The Hamiltonian and frequency
share a domain and gradient identity; Remark 18.4 concerns that same
Hamiltonian. Theorem 18.5 uses the original all-smooth-approximation
solution definition. Three normalization errors in the overview are
corrected below.

## One frequency and its domains

`sourceSection18_original_frequencies` constructs a single original Hilbert
frequency on summable actions. It has analytic realizations in every
target exponent r>1, including infinity, on one common open connected action domain. The domain
contains every original real-source action and the whole nonnegative ℓ¹
cone. Each realization also has a real-valued analytic extension on the
real preimage of this domain, agreeing with the frequency on that cone.

[`SourceFrequencyOriginalHilbertTop.lean`](../NLS/ZakharovShabat/SourceFrequencyOriginalHilbertTop.lean)
supplies the infinity target by composing the existing ell^2 realization
with the bounded inclusion into ell-infinity. Both real and complex
realizations preserve every coordinate and the original domain.
`memℓp_all` gives membership for the literal common sequence throughout
that domain. This endpoint concerns the target space; it does not extend
the frequency to all bounded action sequences.

For every finite p>2 and every independently constructed original Section 17
family, the theorem constructs one frequency F:ℓ^(p/2)→ℓ^(p/2). Its
`SourceOriginalFrequencyData` retains the analytic map, original spectral
recovery, refined corrections, and locally uniform mixed remainder.
All four Corollary 18.2 conclusions are proved for this same F on this
same domain. They are not separate existential maps whose equality must
be assumed.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Theorem 18.1, common Hilbert frequency | `SourceOriginalHilbertFrequencyData.realizations_all` | Every r>1, including infinity; complex and real analytic realizations on one common domain; real values on nonnegative summable actions |
| Higher-exponent extensions | `SourceSection17OriginalData.exists_frequency_asymptotic` | Every finite p>2 and the original family supplied to the theorem; action exponent q=p/2 |
| Extension of the same Hilbert values | `SourceOriginalFrequencyData.eq_hilbert_on_positive` | Entire nonnegative summable cone; arbitrary independent atlases and original families |
| Analytic refined correction | `E.refined` | F(I)+2I analytic into every finite ℓʳ with r>1 and r≥p/3 |
| Locally uniform mixed asymptotic | `E.mixed` | One neighborhood and decomposition into ℓ^(p/3)+ℓ^(1+), chosen before all ℓ^(1+) projection exponents; uniform bounds on that neighborhood |
| Exact origin value and derivative | `E.map_zero`, `E.derivative_zero` | F(0)=0 and dF(0)=−2Id |
| Corollary 18.2(i) | `E.local_inverse` | Analytic inverse at zero with both local identities and derivative −½Id |
| Corollary 18.2(ii) | `E.compact_derivative` | dF(I)+2Id compact at every complex point of the action domain |
| Corollary 18.2(iii) | `E.fredholm` | Fredholm derivative with equal finite kernel and cokernel dimensions throughout the domain |
| Corollary 18.2(iv) | `E.generic_local_inverse` | Open dense subset with actual two-sided analytic local inverses and exact inverse derivatives |
| Real-valued higher extension | `E.real_extension` | Analytic real map agreeing with F on every nonnegative action in its domain |
| Original physical normalization | `E.physical_finiteGap`, `H.physical_finiteGap` | On every real finite-gap source, F=physical frequency−4·physical mass−free dispersion |
| Exponent and atlas compatibility | `E.eq_of_coefficients` | All real sources represented by equal Fourier coefficients at two exponents |

Here E denotes `SourceOriginalFrequencyData` and H denotes
`SourceOriginalHilbertFrequencyData`.

[`SourceOriginalActionDomains.lean`](../NLS/ZakharovShabat/SourceOriginalActionDomains.lean)
supplies `E.positive_domain`: the positive part of this exact U is open
and dense relative to the nonnegative action cone. Its finite exponent
follows from the original finite source exponent. The same map, domain,
source recovery, and mixed remainder are retained.

## Original action image

`SourceSection17OriginalData.actionSequence_eq` proves that the complete
action sequences for two normalized families agree on the intersection
of their complex map domains. Each coordinate is the original analytic
spectral action, so agreement is stronger than agreement merely on real
potentials or finite-gap sources.

`exists_connected_action_image` starts with any open action neighborhood
containing all original real-source actions. Complex inverse charts and
the openness of the quadratic action map supply an open neighborhood
realized inside the original complex source domain V. Intersecting the
two action neighborhoods and taking the component of zero retains all
real-source actions, because the real source space is connected and the
original action map is continuous. Hilbert realization also retains the
whole nonnegative summable cone.

The final U is exactly the image of an open source neighborhood Y⊆V
containing the full real locus. Every point of U has an actual original
complex source representative in Y. The original family and its original
domain V are retained; no equality between U and the action image of the
entire V is asserted. This is the neighborhood restriction used for the
Section 18 extensions, including their generic inverse statement.

## Remainders and inverse arguments

The mixed remainder keeps the literal ℓ^(p/3) term even for 2<p<3, when
that exponent is below one. It does not assume a Banach-space structure
on that component. The ℓ^(1+) component is one sequence belonging to every
finite ℓʳ with r>1; the neighborhood and decomposition are fixed before
the projection exponent is chosen.

To prove compactness, choose a Banach exponent strictly between one and
q=p/2 that is at least p/3. The derivative of the refined correction
factors through that stronger sequence space, and Pitt's theorem gives
compactness. The compact perturbation of −2Id is Fredholm of index zero.
The actual moment formula gives dF(0)=−2Id, so the analytic inverse theorem
applies at zero. Analytic Fredholm density on the connected domain then
gives the open dense set of invertible derivatives and actual local
inverses there.

The physical finite-gap identity uses the independently constructed
physical frequency and mass, with the exact factor four. Moment
compatibility proves equality across independently chosen atlases and
exponents. This milestone does not infer physical agreement from an
arbitrary coordinate flow.

## One original Hamiltonian and its nonextension

[`SourceHamiltonianOriginal.lean`](../NLS/ZakharovShabat/SourceHamiltonianOriginal.lean)
constructs `SourceOriginalHamiltonianData D T F H` for the original p=4
family D. `E.exists_original_hamiltonian` can start with any existing
original frequency E and retain its F. The Hamiltonian is recovered from
the actual cubic moments and agrees with the full physical correction
on every real H¹ source, not only on finite-gap potentials.

The domain T is the component of zero in the intersection of the original
frequency and Hamiltonian domains. It contains every original real-source
action and every nonnegative summable action. Analytic uniqueness from
nonnegative actions identifies F with the gradient of H throughout T.
`SourceFrequencyOriginalRestriction` preserves the original source-image
representation, refined remainders, and mixed estimates on this domain.
Thus all four inverse and Fredholm conclusions remain available for F.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Theorem 18.3(i), source extension | `Q.source_extension`, `Q.source_sign` | Open complex FL⁴ neighborhood of the entire real locus; real nonpositive values, vanishing exactly at zero |
| Physical H¹ recovery | `Q.physical_identity` | H*=physical H−2mass²−∑(2πn)²Iₙ for every real H¹ source; the literal weighted series is absolutely summable |
| Theorem 18.3(ii), action extension and sign | `Q.analytic`, `Q.sign` | One open connected complex ℓ² domain T, nonpositive and zero only at zero on its nonnegative cone |
| Same frequency gradient | `Q.gradient_eq`, `Q.frequency` | F=∇H* throughout T, retaining the complete original frequency package |
| Origin Hessian and local concavity | `Q.hessian_zero`, `Q.concavity` | Hessian −2 times unconjugated Hilbert pairing at zero; one positive ball in T with d²H*(J,J)≤−‖J‖₂² for every real direction J |
| Remark 18.4 | `Q.no_continuous_extension_all` | No continuous, hence no C¹, extension at zero relative to the nonnegative ℓ^q cone for every q>2, including infinity |

Here Q denotes `SourceOriginalHamiltonianData`. The unconditional
`sourceSection18_original_hamiltonian` constructs D, T, F, H, and Q.

`Q.real_summable_extension` constructs a real analytic function on the real
ell^1 inverse image of T, agreeing with H at every nonnegative summable
action. Its values are nonpositive and vanish exactly at zero.
`Q.positive_domain` proves relative openness and density for the positive
part of this unchanged Hilbert action domain.

[`SourceHamiltonianOriginalNonextension.lean`](../NLS/ZakharovShabat/SourceHamiltonianOriginalNonextension.lean)
integrates this Hamiltonian's Hessian estimate twice to obtain
Re H*(I)≤−‖I‖₂²/2 near zero. Nonnegative finite blocks of fixed small ℓ²
norm converge to zero in ℓ^q for q>2. Agreement on summable nonnegative
actions then contradicts continuity. The extension can be arbitrary away
from those actions. The infinity endpoint is now included by
[`SourceHamiltonianOriginalNonextensionTop.lean`](../NLS/ZakharovShabat/SourceHamiltonianOriginalNonextensionTop.lean).
Its `no_continuous_extension_all` theorem uses the same Q and H.
The abstract endpoint argument in
[`HilbertHamiltonianNonextensionTop.lean`](../NLS/SequenceSpaces/HilbertHamiltonianNonextensionTop.lean)
restricts any alleged infinity-norm extension along the continuous,
coefficient-preserving inclusion from ell^3. The inverse image of its
neighborhood is a neighborhood of zero, and the inclusion preserves
the nonnegative cone, contradicting the finite-exponent theorem.
This result does not assert global concavity.

## Full energy on weighted actions

[`SourceWeightedActionHamiltonian.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonian.lean)
constructs the full energy H*(I) + 2(sum I)^2 + sum (2 pi n)^2 I_n on
native weighted ell^1 actions. Both series converge absolutely. The
complex analytic domain is the inverse image of the original T and
contains the entire nonnegative weighted cone.

[`SourceWeightedActionHamiltonianPhysical.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianPhysical.lean)
places the actual action sequence of every real H1 source in this space,
identifies its action sum with physical mass, and proves
`Q.full_action_physical_identity` for its actual physical energy. No
finite-gap or preselected action representative is assumed.

[`SourceWeightedActionHamiltonianReal.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianReal.lean)
gives a real analytic realization on the native real subspace with exact
complex values at every nonnegative action.
[`SourceWeightedActionHamiltonianDerivative.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianDerivative.lean)
proves the coordinate derivative F_n + 4 mass + (2 pi n)^2 throughout
the original complex domain, retaining the same F and H*.

The physical weight here is (1+2 pi |n|)^2. The introduction uses the
standard weight (1+|n|)^2.
[`SourceWeightedActionHamiltonianNorm.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianNorm.lean)
constructs a bounded complex linear equivalence preserving every raw
coefficient, with norm_standard <= norm_physical <= (2 pi)^2 norm_standard.
[`SourceStandardActionHamiltonian.lean`](../NLS/ZakharovShabat/SourceStandardActionHamiltonian.lean)
then proves complex and real analyticity, the whole positive cone in the
open domain, actual physical recovery, and literal coordinate derivatives
in the exact standard ell^(2,1) topology. It does not identify the norms.

## Theorem 18.5 and the original solution definition

[`SourceSection18Wellposedness.lean`](../NLS/ZakharovShabat/SourceSection18Wellposedness.lean)
provides the unconditional `source_theorem18_5 hp hp1` for every finite p>1.
A solution is continuous, takes its prescribed initial value, and is the
pointwise source-norm limit of the actual renormalized classical trajectories
for **every** smooth initial-data sequence converging to that initial value.
The classical solutions are constructed, not supplied as an assumption.

| Source assertion | Package field | Scope |
| --- | --- | --- |
| Part (i) | `global` | Global real analytic wellposedness on all FLᵖ for 1<p≤2 |
| Part (ii) | `local_wellposed` | Local real analytic wellposedness for every finite p>1, including the printed 2<p<∞ range |
| Part (iii) | `small_global` | Global real analytic wellposedness on an open neighborhood containing a positive ball about zero for every finite p>2 |
| Part (iv) | `ordinary_nonextension` | For finite q≥p>2 and every T>0, no map agreeing with ordinary smooth classical NLS into C([−T,T],FL^q) is continuous at any source outside L² |
| Uniqueness after the solution definition | `unique` | Any two solutions agree on their common time domain |

Analytic dependence is in the uniform norm on the continuous trajectory
space for each compact time interval. Local existence uses one time
interval and one open neighborhood for each datum. Global existence uses
one trajectory for all real times and analytic restrictions for every
positive compact time horizon.

## Certified normalization corrections

[`SourceSection18HamiltonianCorrection.lean`](../NLS/ZakharovShabat/SourceSection18HamiltonianCorrection.lean)
realizes every single nonnegative action as a genuine real finite-gap H¹
source, retaining its physical mass and weighted action sum.

* On p. 83 the full Hamiltonian expansion contains 2mass², so its frequency
  derivative is 4−2δₙₘ. `Q.restored_frequency_derivative` proves this formula.
  `Q.single_action_physical_energy` identifies the restored energy with
  the actual physical H¹ energy along every nonnegative action axis;
  `Q.full_hessian_diagonal` proves its second derivative at zero is +2.
  `Q.full_hessian_ne_printed` refutes the displayed −2 diagonal.
  The Hessian −2δₙₘ is correct for H*, not the full H.
* The paragraph before Theorem 18.3 on p. 84 drops the weighted linear
  action subtraction. `Q.printed_subtraction_counterexample` constructs
  an actual source with I₁=1 and other actions zero, whose omitted term
  is 4π². The corrected H* includes that subtraction; H−2mass² is Hʳ.
* The gauge phase on p. 85 must be exp(4 i mass t), with mass equal to the
  squared L² norm. `SmoothNLSData.renormalized_phase` proves the corrected
  conversion, and `original_gauge_printed_phase_counterexample` uses an
  actual smooth constant initial datum of mass one to refute the printed
  phase directly in the renormalized PDE. See
  [`SourceSection18GaugeCorrection.lean`](../NLS/ZakharovShabat/SourceSection18GaugeCorrection.lean).

These corrections preserve the numbered results. Details are also recorded
in [the source discrepancy log](../SOURCE_ERRATA.md).

## Validation and next work

The first integration added five modules and 21 public frequency checks,
including p=5/2 with its quasi-normed p/3<1 remainder. The Hamiltonian and
wellposedness integration adds six modules and 22 public checks: original
construction and recovery, common-domain frequency retention, full H¹
normalization, sign, concavity, nonextension, all wellposedness cases, and
actual-source correction witnesses. Full gate results are recorded in
[the implementation status](../STATUS.md).

The subsequent [Section 19 audit](SECTION_19.md) integrates the original
abelian integrals, and [Section 20](SECTION_20.md) covers their frequency
and contour-moment applications. Native fractional Sobolev analyticity
and analytic inverses are proved in [Section 14](SECTION_14.md); its
precise 2014 construction comparison remains unverified.
