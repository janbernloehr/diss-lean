# Section 8: discriminant

Lemma 8.1 is stated on printed p. 48. The source space is `CoeffPair p`
with its original component-sum norm and physical period-one realization
`periodOnePotential`. All statements below cover every finite 1<p<∞.
The source PDF was visually inspected; the prefactor and denominator
issues are recorded in [SOURCE_ERRATA.md](../SOURCE_ERRATA.md).

## Ordered opening and finite determinants

The corrected Section 8 finite products now have a direct original-source
determinant interface. It constructs one open convex neighborhood, a common
cutoff and separately ordered actual parity roots with full multiplicities.
The even determinant has prefactor -1 at circle index 2M; the odd formula
has prefactor 4 and retains its extra positive boundary pair. Both literal
products converge locally uniformly to the corresponding discriminant levels.

Validation: `./scripts/check.sh` passes with 8,503 build jobs, 7,570
public examples and a transitive axiom audit of 44,226 NLS declarations.
The 21 inherited warnings are unchanged; the new module and examples introduce none.
The source-review integrity and documentation-link checks also pass.

The first fifteen groups in the [ordered Section 8 ledger](SECTION_8_ASSERTIONS.md)
are compared: eight matched, six corrected and one partial. S8-014 retains
the exact lower-strip sine constant; the derivative asymptotic is proved.
The remaining 21 groups await ordered comparison. Section 7's physical NLS
Dirichlet motion and unrestricted psi uniqueness, the source-wide inventory,
exact cited 2014 construction and Appendix G.2 norm interpretation remain open.
Corrected constants are proved directly, without additional refutations.

[SourceSection8ParityDeterminants.lean](../NLS/ZakharovShabat/SourceSection8ParityDeterminants.lean)
combines actual counted roots, separate lexicographic ordering, common source
geometry, exact finite determinants and whole-plane convergence. The source
existence theorem constructs the resolvent contours and roots internally.
The odd finite formula retains the pair indexed by 2M+1. The examples at
p=3/2 derive the difference four between the limiting products and convergence
of the original even contour determinants to Delta-2.

The existing named-statement audits below retain their proof scope. Historical
constant refutations remain available; this milestone adds positive corrections
only. The ordered review does not infer source-wide completeness from them.

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
Subsequent Section 8 results are audited below; the remaining dissertation
is not certified complete by this audit.


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

Lemma 8.3 is audited below.


## Lemma 8.3: original critical-root counts and reality

The statement and proof on printed p. 50 were checked against the PDF.
`sourceLemma8_3` constructs `SourceLemma8_3Data` for arbitrary complex
original sources and every finite 1<p<∞. It gives a positive N and one
open convex neighborhood U in the original component-sum norm, with both
the given source and zero in U. All conclusions below use this same U.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Distant root | `SourceLemma8_3Data.distant` | For every ψ in U and signed index with |n|>N, the actual canonical critical coordinate lies in D_n, is a simple zero of Δ′, and is the only zero even in the closed disk. |
| Distant count | `.distant_counts` | Count one with analytic multiplicity, and a zero-free quarter-pi boundary. |
| Central count | `.central_counts` | For every ψ in U and every K≥N, exactly 2K+1 zeros with analytic multiplicity, and a zero-free central boundary. |
| Actual central labels | `.central_labels` | The canonical coordinates indexed by [-K,K], as a multiset, equal `centralCriticalRoots`; repeated roots are retained. |
| Central size and membership | `.central_roots` | The multiset has cardinality 2K+1 and contains exactly the Δ′ zeros in the open central disk. |
| Pointwise multiplicities | `.central_multiplicity` | Each point's number of occurrences among the central canonical labels is its analytic zero order inside the disk, and zero outside. |
| Exhaustion | `.exhaustive` | Every derivative zero lies in the central open disk or a distant D_n with |n|>K, for every K≥N. |
| Reality | `.real_roots` | For each real-type ψ in U, every zero of Δ′ has zero imaginary part, including central roots. |

### Central geometry

The explicit radius `centralCircleRadius K = K*π + π/2` is the radius of
the circular region used in the source proof. Open and closed disks give
the same roots because the boundary is zero-free. The source statement
calls the central region B_N; the preceding sections also use B_N for
central boxes. The formalization supplies the circle result and the
following comparison with the height-K box of Corollary 3.5:

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Uniform imaginary bound | `.imag_bound` | Every critical root of every ψ in U satisfies |Im z|<N. |
| Disk/box selection | `.central_box_selection` | For a derivative zero, membership in the central open disk is equivalent to membership in `centralSpectralBox K`, for all K≥N. |
| Box count | `.central_box_count` | The height-K box also contains exactly 2K+1 zeros counted with multiplicity. |

This comparison uses the height-K box, not the separate norm-dependent
height bound discussed in the earlier source audits. The count does not
assert that central roots are distinct or simple.

### Proof and validation scope

The existing sine-quotient exterior estimate gives a common Rouché
inequality, hence the counts and exhaustion. The theorem pulls that
neighborhood and the canonical-label neighborhood back along the
continuous complex-linear `periodOnePotential` map. Their intersection
preserves openness, real convexity, and membership of both source and
zero. Enlarging one cutoff accommodates the uniform canonical ℓp bound,
which also controls every imaginary part. The reality argument uses the
proved real-rooted full-product derivative theorem and the exact identity
`(Δ²-4)′ = 2ΔΔ′`; complex conjugation symmetry alone is not used to conclude
that roots are real.

The public examples check the range below two at arbitrary complex base
points, a common original norm ball for all larger cutoffs, negative
indices, central multiplicities, the box count, exhaustion, off-real
nonvanishing for real-type sources, and the exact free central multiset.

Lemma 8.4 is audited below.


## Lemma 8.4: sampled discriminant and derivative errors

The statement and proof on printed p. 51 were checked against the PDF.
`sourceLemma8_4` constructs the result for every finite 1<p<∞ in the
original `CoeffPair p` space, with arbitrary complex base points.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual value-error sequence | `sourceDiscriminantSampleError` and its `_apply` theorem | The coefficient at n is exactly Δ(z_n)-2 cos(z_n), and the entire sequence is in ℓp. |
| Actual derivative-error sequence | `sourceDiscriminantDerivativeSampleError` and its `_apply` theorem | The coefficient at n is exactly Δ′(z_n)+2 sin(z_n), with the source's sign and normalization. |
| Literal value formula | `sourceLemma8_4_value` | Δ(z_n)=2 cos(z_n)+a_n for the actual ℓp error a. |
| Literal derivative formula | `sourceLemma8_4_derivative` | Δ′(z_n)=-2 sin(z_n)+b_n for the actual ℓp error b. |
| Whole-disc bounds | `SourceLemma8_4Data.disc_majorants` | For each nearby source, one A in ℓp controls every value error on every quarter-pi disk; (4/π)A controls every derivative error. |
| Uniform sample norms | `.sampled_norms` | The actual sequences have norms at most K and 4K/π, for all nearby sources and all samplers. |
| Exact free case | `sourceDiscriminantSampleError_zero`, `sourceDiscriminantDerivativeSampleError_zero` | Both actual sequences are zero for every admissible sampler. |

### Quantifiers and proof

The theorem returns one original open convex neighborhood U containing
the base point and zero, and one K≥0. For every ψ in U it supplies a
majorant A with norm at most K before quantifying over n and the point
in its disk. Thus A can depend on ψ but is independent of the sampling
sequence; K and U are independent of both. The same K controls any two
nearby potentials with any two admissible samplers.

Every index is included, without discarding a finite central block. The
theorem allows the closed-disk bound |z_n-nπ|≤π/4 and therefore includes
the source's assertion for samples in the open D_n. Sample choices may
depend arbitrarily on ψ; no continuity or analyticity of a sampler is
required or asserted.

The proof uses the existing actual parity-product ℓp majorants on the
larger half-pi disks. Cauchy's estimate on the concentric quarter-pi disks
gives the factor 1/(π/2-π/4)=4/π. Coefficientwise domination then bounds
the actual sampled sequences in the same finite ℓp space. Pulling the
common neighborhood back along `periodOnePotential` preserves openness,
convexity, and the original source topology. This supplies local uniform
norm bounds; the theorem does not assert continuity of an arbitrarily
chosen sampler.

Public checks exercise p=3/2 at arbitrary complex bases, arbitrary
potential-dependent samplers, common bounds for different samplers and
sources, open-disk membership in ℓp, nonreal samples on every closed-disk
boundary, all signed indices, and the free identities.

Lemma 8.5 and the following real-extremum assertions are audited below.


## Lemma 8.5 and equation (2.6): canonical critical roots and the derivative product

The statement, formula, and following paragraph on printed p. 51 were
checked against the PDF. `sourceLemma8_5_data` constructs the pointwise
result for every finite 1<p<∞ and arbitrary complex original source.
`sourceLemma8_5` supplies the common original source neighborhood and
locally uniform bound on the full ℓp displacement norm.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual ordered roots | `SourceLemma8_5Data.ordered`, `.roots` | Canonical coordinates indexed by all integers, in lexicographic order, enumerating exactly all zeros of Δ′. |
| Exact analytic multiplicities | `.multiplicity` | The number of occurrences of each value in the canonical sequence equals its analytic zero order. Complex repeated roots are retained. |
| Literal ℓp asymptotics | `.displacement` | The nth coordinate is nπ plus the nth coefficient of the actual `sourceCriticalDisplacement`, an element of ℓp. |
| Locally uniform norm bound | `sourceLemma8_5` | One open convex U containing the base and zero, and one R≥0, bound the complete displacement sequence for every ψ in U. |
| Literal product (2.6) | `SourceLemma8_5Data.product` | Symmetric cutoffs over [-M,M], prefactor 2, denominator 1 at n=0 and nπ otherwise; locally uniform convergence on all of ℂ to the actual derivative. |

The product uses the actual canonical roots with their multiplicities,
including central roots. The limit is proved on the entire spectral plane,
including free lattice points and zeros. The cutoff M is a natural number;
this is convergence of symmetric products, not a claim about an unordered
infinite product. Product convergence is locally uniform in the spectral
variable for each fixed source. The source-neighborhood assertion bounds
the displacement norm uniformly over U.

### Continuity at real type

`sourceLemma8_5_real` constructs `SourceLemma8_5RealData` at every
real-type source, with the ambient domain still the full complex original
source space.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Coordinate continuity | `SourceLemma8_5RealData.continuous` | Every signed coordinate, under arbitrary complex source perturbations, including at collapsed gaps. |
| Stronger coordinate analyticity | `.analytic` | Each fixed canonical critical coordinate is complex analytic at the real-type base point. |
| Full sequence-norm continuity | `.norm_continuity` | The complete actual critical displacement varies continuously in ℓp. |
| Simultaneous coordinate control | `.exists_uniform_coordinate_neighborhood` | For any positive tolerance, one original open neighborhood bounds the error at every signed index. |

The coordinate continuity rests on the existing spectral-count and
real-barrier argument. Simplicity of real-type critical roots then gives
coordinate analyticity by the implicit-root theorem. The full ℓp
continuity uses the existing uniform-tail argument. These assertions do
not claim global continuity of lexicographic labels at arbitrary complex
base points.

### The following real-gap interlacing and strict extrema

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Real critical coordinates | `.real_coordinates` | Every canonical critical coordinate is real at real type. |
| Indexed interlacing | `.interlacing` | λ_n^-≤λ_n^•≤λ_n^+, expressed as membership in the actual `sourceRealPeriodicGap`. |
| Unique critical root per gap | `.unique_critical` | Each indexed real gap contains exactly one critical root. |
| Strict local extremum | `.strict_extremum` | Strict minimum or maximum of x↦Re Δ(x) on a punctured real neighborhood of the canonical critical coordinate. |
| Unique local extremum per gap | `.unique_extremum` | Exactly one real local extremum in each indexed gap, including singleton collapsed gaps. |
| Exhaustive extremum characterization | `.all_extrema` | Every real local extremum is a canonical critical coordinate, and conversely. |

At real type Δ is real on the real axis, so the real-part formulation is
the source's real discriminant. Strictness is asserted in a real
neighborhood, not merely relative to the gap; it therefore has content
even when a gap is a singleton. The proof uses nonzero second derivative
at each real-type critical root and the real second-derivative test,
together with global gap interlacing and critical-root exhaustion.

Public checks include p=3/2, the zero-index factor, the full free product
at π/2 with limit -2, ℓp convergence under complex perturbations, uniform
control of all indices, repeated complex-root multiplicities, exhaustion,
and the collapsed free gap at index -1.

## Lemma 8.6: the squared-gap midpoint-offset estimate

The statement and proof are on printed pp. 51–52. `sourceLemma8_6`
covers every finite 1<p<∞ and every complex original base potential φ.
It constructs N>0, an original open convex neighborhood U containing
both φ and zero, and K≥0. These choices precede ψ∈U and the signed index
n with |n|>N; the same choices work for every such ψ and n.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Actual ℓp coefficient | `sourceCriticalGapTailCoefficient` | Deleted-product derivative divided by 4 times the offset coefficient on the tail, with central coefficients set to zero. |
| Exact coefficient formula | `sourceCriticalGapTailCoefficient_apply` | Exposes the quotient and cutoff at every signed index. |
| Uniform full norm | `SourceLemma8_6Data.coefficient_norm` | The complete actual masked sequence has norm at most K for every ψ∈U. |
| Uniform denominator bound | `.denominator_lower_bound`, `.denominator_ne_zero` | The offset coefficient has norm at least one, hence the full quotient denominator is nonzero on the common tail. |
| Exact squared-gap identity | `.offset` | λ_n^•−τ_n=γ_n² a_n for the actual critical point, midpoint, gap, and masked coefficient. |
| Complex collapsed gaps | `.collapsed_gap` | If γ_n=0 then λ_n^•=τ_n, without a real-type assumption. |
| Quadratic norm bound | `.norm_offset_le` | The actual offset norm is at most K times the squared gap norm. |
| Free coefficient | `sourceCriticalGapTailCoefficient_zero` | The entire actual sequence is zero at the free source for every cutoff. |

The common neighborhood is the pullback, under `periodOnePotential`,
of the intersection of the existing ambient neighborhoods for the
squared-gap coefficient and its denominator lower bound. Increasing the
cutoff and setting central terms to zero can only decrease the ℓp norm.
There is no local boundedness assertion for the unmasked quotient at
central indices, where its denominator may vanish. The tail identity
uses no division by the gap and makes no simplicity assumption on a
collapsed pair. It makes no assertion that all complex labels are
continuous or analytic at arbitrary base points.

The underlying estimate differentiates the deleted-pair factorization
at the actual critical root. Local ℓp bounds on the deleted-product value
and derivative, together with the critical displacement, force the
offset coefficient to approach two and give its uniform lower bound.
The coefficient then belongs to ℓp with a locally uniform norm bound.

### Literal deleted product and corrected proof identity

`sourceDeletedPeriodicProduct_formula` expands the product over
[-M,M] with n removed and the outer factor 1/π_n², where π_0=1 and
π_m=mπ otherwise. Its limit is the actual entire deleted product,
locally uniformly on all of ℂ for each fixed source. This includes the
removed roots and repeated roots; it is not merely a quotient formula
away from those roots. No locally uniform source dependence of the
ordered deleted products is asserted here.

`sourceDiscriminant_midpoint_factorization` proves
Δ²−4=−4((τ_n−λ)²−γ_n²/4)Δ_n(λ). The printed +4 is false already
at zero potential, n=0, λ=π/2, as formally proved by
`sourceLemma8_6_printed_factorization_false`. The common nonzero factor
cancels from the differentiated critical-point identity, so the lemma's
stated squared-gap estimate survives. See [the erratum](../SOURCE_ERRATA.md).

Public checks cover p=3/2 and arbitrary complex bases, negative distant
indices, complex collapsed gaps, an explicit bound K/100 when the gap
norm is at most 1/10, the free coefficient sequence, zero-index product
normalization, the value one at every removed free double root, and the
printed-sign counterexample.

The subsequent ordinary and auxiliary characteristic results are audited in
[Section 9](SECTION_9.md).

## Complex endpoint labels can be discontinuous, printed p. 49

The unnumbered paragraph and Figure 2.1 preceding Lemma 8.2 explain why
lexicographically ordered periodic eigenvalues need not be continuous at
complex sources. The original PDF was visually checked. The formalization
now supplies actual source witnesses for both canonical central labels.

[ConstantPeriodicSpectrum.lean](../NLS/ZakharovShabat/ConstantPeriodicSpectrum.lean)
computes the actual periodic spectrum of a constant complex potential
(a,b), with a nonzero. A complex number z belongs to that spectrum exactly
when z^2=(pi*k)^2+a*b for some integer k. The converse constructs a nonzero
single-mode eigenvector in the original one-derivative domain.

[SourceConstantPeriodicSpectrum.lean](../NLS/ZakharovShabat/SourceConstantPeriodicSpectrum.lean)
identifies this operator parameter with both the original period-two
source and the embedded period-one source. The original constant source
is the value of a bounded complex linear map of its two amplitudes.

[SourceConstantCentralPair.lean](../NLS/ZakharovShabat/SourceConstantCentralPair.lean)
uses the existing common isolating discs and complete spectral exhaustion.
On one open source neighborhood of zero, any two distinct small roots
z and -z of z^2=a*b are exactly the actual canonical central pair, sorted
in the prescribed lexicographic order.

[SourcePeriodicLabelDiscontinuity.lean](../NLS/ZakharovShabat/SourcePeriodicLabelDiscontinuity.lean)
proves that, for every finite p>1 and every source neighborhood of zero,
some positive r gives a constant source (r,-r) in that neighborhood at
which both canonical central endpoint maps fail to be continuous.
Along the continuous original-source curve

```
time ↦ (r, (time+i*r)^2/r),
```

the two central roots are time+i*r and its negative. For negative time
the first root has smaller real part. At time zero the imaginary-part
tie-break reverses the ordering. Their one-sided limits therefore differ
from their actual labeled values.

This verifies the source's general-complex discontinuity assertion. It
does not assert discontinuity at every complex source or at zero itself.
Lemma 8.2's continuity at real sources and the analyticity of symmetric
spectral coordinates remain valid. Five public examples include actual
nonreal spectral points, the original source curve, witnesses in every
source ball at p=3/2, and global discontinuity consequences at p=4.
