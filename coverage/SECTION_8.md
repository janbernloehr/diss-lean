# Section 8: discriminant

Lemma 8.1 is stated on printed p. 48. The source space is `CoeffPair p`
with its original component-sum norm and physical period-one realization
`periodOnePotential`. All statements below cover every finite 1<p<∞.
The source PDF was visually inspected; the prefactor and denominator
issues are recorded in [SOURCE_ERRATA.md](../SOURCE_ERRATA.md).

## Lemma 8.1(i): literal products and joint analyticity

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Corrected parity products | `exists_sourceDiscriminant_parity_products` | Actual counted roots in both parity sectors; locally uniform convergence on all of ℂ, with prefactors -1 and 4. |
| Printed parity products | `exists_sourceDiscriminant_printed_parity_limits` | The literal -2 and 2 products converge to 2(Δ-2) and (Δ+2)/2. |
| Corrected joint analyticity | `SourceLemma8_1Data.parity_analytic` | Spectral parameter and original potential together. |
| Printed joint analyticity | `SourceLemma8_1Data.printed_analytic` | The printed scalar rescalings are analytic too; the defect is their compatibility and normalization. |

The two printed scaling constants cancel in their product fg; the full
product in part (iv) retains its -4 normalization.

The returned `CompletePeriodicParityPairs` retain central algebraic
multiplicities, actual distant pairs, and ℓp displacement sequences.
Central parity labels are not obtained by taking even and odd indices
of the globally lexicographic complex periodic spectrum. Such an
identification would generally be false. Intrinsic product identities
make the limit independent of every admissible counted labeling; no
analytic individual root labeling is assumed.

## Lemma 8.1(ii): compatibility, physical agreement, and uniqueness

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Corrected identities | `SourceLemma8_1Data.compatibility` | Δ=f+2=g-2 and Δ²-4=fg with prefactors -1 and 4. |
| Joint analytic discriminant | `SourceLemma8_1Data.discriminant_analytic` | Entire in the spectral parameter and analytic jointly with the original potential. |
| Exact classical finite-source trace | `sourceDiscriminant_finite_eq_classical` | Every finite ambient exponent, by exponent compatibility. |
| Physical Hilbert agreement | `sourceDiscriminant_eq_l2_of_two_le`, `sourceDiscriminant_eq_l2_of_le_two` | Extension for p≥2, restriction for p≤2; actual physical L² monodromy trace. |
| Unique extension | `sourceDiscriminant_unique_continuous`, `sourceDiscriminant_unique_joint_continuous` | Uniqueness already among continuous candidates agreeing on finite Fourier input. |
| Printed incompatibility | `sourceLemma8_1_printed_products_incompatible` | At zero potential and λ=0 the shifted printed values are 2 and 0. |

The uniqueness statement is stronger than uniqueness among analytic
extensions agreeing with Hilbert data. The public check explicitly derives
the finite-source condition from agreement on every included Hilbert source.
Below two, the Hilbert function is restricted along the opposite inclusion;
there is no claim that all Hilbert sources belong to the smaller source space.

## Lemma 8.1(iii): the full exterior and the cosine zeros

`exists_uniform_sourceDiscriminant_exterior` supplies one open convex
source neighborhood U, containing both the base potential and zero, and
one positive threshold R. For every ψ in U and every λ of norm at least R
outside all open π/4 disks about πℤ, it bounds simultaneously:

- |Δ(λ,ψ)-2 cos λ| by ε exp(|Im λ|).
- |Δ′(λ,ψ)+2 sin λ| by ε exp(|Im λ|).
- |Δ′(λ,ψ)/(-2 sin λ)-1| by ε.

The printed trace quotient includes λ=(n+1/2)π, where cos λ=0 and the
spectral norm tends to infinity. `sourceLemma8_1_printed_cosine_quotient_false`
refutes that literal bound: under Lean's totalized division the error is
exactly one; with ordinary division it is undefined. This counterexample
does not claim failure of every modified quotient that excludes those points.

`exists_uniform_sourceDiscriminant_cosine_quotient` proves the valid
quotient bound under the additional assumption
`c * exp(|Im λ|) ≤ ‖2 cos λ‖`, for any fixed c>0. The full-exterior additive
estimate needs no such assumption. The valid derivative quotient remains
on the entire original exterior, where sine has no zeros.

## Lemma 8.1(iv): exact full product, zero set, and multiplicity

`sourceDiscriminant_ordered_product` uses the actual canonical left and
right endpoints, in their global lexicographic order, with the literal
full cutoff and prefactor -4. Its limit is Δ²-4 locally uniformly on all of
ℂ, including lattice points and repeated eigenvalues. It is identified
with the intrinsic full product without an unspecified entire factor.

`SourceLemma8_1Data.spectrum` identifies the zeros with the actual periodic
spectrum of `periodOnePotential φ` and each analytic zero order with its
original spectral algebraic multiplicity. The product is therefore more
than a characteristic function with the correct zero set.

## Lemma 8.1 combined theorem

`sourceLemma8_1` constructs `SourceLemma8_1Data` without assuming product
compatibility, classical agreement, or any of the exterior bounds.
Public checks include p=3/2, exact Hilbert agreement, extension uniqueness,
simultaneous estimates, actual orders, cutoff normalization, and both
printed counterexamples.

Lemma 8.2 and its following real-gap characterization are audited below.
Later Section 8 results and the remaining dissertation are not certified
complete by this audit.


## Lemma 8.2(i): continuity at real type under complex perturbations

The source statement appears on printed p. 49. Its continuity is at a
real-type base point within the full complex source space. No simplicity,
noncollapsed-gap, or restriction to real perturbations is imposed.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Original coordinate continuity | `SourceLemma8_2Data.continuous_left`, `.continuous_right` | Every integer index, including central and repeated endpoints, under arbitrary complex source perturbations. |
| Exact sequence decomposition | `sourcePeriodicLeftDisplacement_eq_midpoint_sub_half_gap`, `sourcePeriodicRightDisplacement_eq_midpoint_add_half_gap` | Actual endpoint displacements equal the midpoint displacement minus/plus half the actual gap. |
| Full sequence-norm continuity | `continuousAt_sourcePeriodicEndpointDisplacements_of_realType` | Both endpoint displacement sequences in ℓp, at every real-type source. |
| One neighborhood for all indices | `exists_uniform_sourcePeriodicEndpoint_neighborhood` | A common original open neighborhood bounds both coordinate errors at every signed integer index, for any positive tolerance. |

The coordinate proof uses the existing stable spectral counts and real
barriers, with imaginary-part control for nearby complex roots. The
stronger sequence statement uses the already constructed uniform ℓp tails
of the midpoint and gap sequences. Neither assertion claims that the
lexicographic labels are globally continuous at arbitrary complex base
points; the source explicitly illustrates their possible discontinuity.

## Lemma 8.2(ii) and equation (2.5): strict gap separation

`SourceLemma8_2Data.real_endpoints` proves that the endpoints are real,
and `.spectral_endpoints` records their membership in the actual periodic
spectrum of `periodOnePotential φ`. The chain in `.interlacing` is

```
right(n-1) < left(n) ≤ right(n) < left(n+1).
```

Its weak middle inequality permits collapsed gaps. Its strict outer
inequalities apply to every index, including the central cluster.
`.disjoint_gaps` gives disjoint closed intervals for any distinct indices.

`sourcePeriodicEndpoints_signed_discriminant` and `.endpoint_levels`
prove the literal normalization `(-1)^n Δ(left(n)) = 2` and the same identity
at the right endpoint. The exponent is an integer, including negative
indices. These prescribed opposite levels separate neighboring gaps.

## The following unnumbered real-gap characterization, printed p. 50

`sourceRealPeriodicGap hp hp1 φ n` is the closed interval between the real
parts of the actual canonical endpoints. Its spectral interpretation here
is asserted for real-type φ, where endpoint reality is proved.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Signed inequality on a gap | `SourceLemma8_2Data.gap_sign` | `(-1)^n Re Δ(x) ≥ 2` for every x in the nth closed gap. |
| All closed gaps | `SourceLemma8_2Data.closed_gaps` | Their union is exactly the real set where the complex modulus of Δ is at least two. |
| All open gap interiors | `SourceLemma8_2Data.open_gaps` | Their union is exactly the real set where that modulus is greater than two. |
| Exact endpoint set | `SourceLemma8_2Data.endpoint_set` | Modulus two holds exactly at a canonical endpoint; coincident endpoints are allowed. |
| Unique gap index | `SourceLemma8_2Data.existsUnique_gap` | Every point of the closed-gap union belongs to exactly one indexed gap. |
| Free collapsed gaps | `sourceRealPeriodicGap_zero` | The nth gap at zero potential is exactly the singleton {nπ}. |

`sourceLemma8_2` constructs all fields for every finite 1<p<∞ in the
original component-sum source norm. It does not assume interlacing,
endpoint levels, continuity, or the gap characterization as additional
data. Public checks exercise the range below two, arbitrary complex
approximating sequences, uniform control over all indices, negative-index
levels, unique gap membership, and the completely collapsed free example.

Continue with Lemma 8.3: locally uniform critical-root counts for Δ′,
exhaustion of its zeros, and their reality at real type.
