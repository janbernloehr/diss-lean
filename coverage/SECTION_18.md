# Section 18: original frequency audit

Source: printed pp. 83–86. This milestone integrates Theorem 18.1 and
Corollary 18.2 with the original Section 17 Birkhoff family. The Hamiltonian
and wellposedness assertions later in this overview remain to be audited
and integrated; existing results for them are listed below as next work.

## One frequency and its domains

`sourceSection18_original_frequencies` constructs a single original Hilbert
frequency on summable actions. It has analytic realizations in every finite
target exponent r>1 on one common open connected action domain. The domain
contains every original real-source action and the whole nonnegative ℓ¹
cone. Each realization also has a real-valued analytic extension on the
real preimage of this domain, agreeing with the frequency on that cone.

For every finite p>2 and every independently constructed original Section 17
family, the theorem constructs one frequency F:ℓ^(p/2)→ℓ^(p/2). Its
`SourceOriginalFrequencyData` retains the analytic map, original spectral
recovery, refined corrections, and locally uniform mixed remainder.
All four Corollary 18.2 conclusions are proved for this same F on this
same domain. They are not separate existential maps whose equality must
be assumed.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Theorem 18.1, common Hilbert frequency | `SourceOriginalHilbertFrequencyData.realizations` | Every finite r>1; complex and real analytic realizations on one common domain; real values on nonnegative summable actions |
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

## Validation and remaining Section 18 work

Five new modules and 21 public checks cover the original action image,
mixed remainders, all four inverse assertions, real-valued extensions,
physical normalization, and exponent compatibility. Unconditional
constructions include p=2 and p=5/2; the latter explicitly checks p/3<1.
Full gate results are recorded in [the implementation status](../STATUS.md).

Next, audit and integrate these statements for the same original quantities:

| Remaining source item | Existing starting points | Required integration |
| --- | --- | --- |
| Theorem 18.3 | `SourceHamiltonianActionConcavity`, `SourceSobolevHamiltonianIdentification` | One Hamiltonian with the physical H¹ identity, original-family action recovery, sign, and local Hessian bound |
| Remark 18.4 | `SourceHamiltonianNonextension` | Retain that same Hamiltonian in the nonextension assertion; the existing obstruction is stronger than failure of C¹ extension |
| Theorem 18.5 | `GlobalAnalyticNLSSolutions`, `HigherExponentAnalyticNLSSolutions`, `SmoothClassicalNLSNonextension` | Audit all-smooth-approximation solutions, analytic compact-time maps, and all four numbered cases |
| Introductory normalization formulas | `ClassicalRenormalizedNLSGauge`, physical Hamiltonian identities | Check the printed full-Hamiltonian Hessian, omitted linear-action subtraction, and gauge phase; these candidates are not certified by this milestone |

Section 14's precise external Hilbert-map identification and full
fractional-smoothness qualifications remain. The dissertation is incomplete.
