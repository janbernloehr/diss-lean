# Section 9: ordinary and auxiliary characteristic functions

Lemma 9.1 and the following auxiliary assertions appear on printed p. 53.
The PDF page was visually inspected. All source statements below use
`CoeffPair p` with the original component-sum norm, for every finite
1<p<∞. The auxiliary monodromy label discrepancy is recorded in
[SOURCE_ERRATA.md](../SOURCE_ERRATA.md).

## Lemma 9.1(i): ordinary products, analytic extension, and spectra

`sourceLemma9_1` combines all three ordinary assertions.
`sourceLemma9_1_data` constructs `SourceLemma9_1Data` for both
boundary conditions, without assuming the product or spectral identities.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Joint analyticity | `SourceLemma9_1Data.analytic` | Spectral parameter and arbitrary complex original source jointly. |
| Literal product | `.product` | Symmetric cutoffs over [-M,M], prefactor -1, denominator 1 at index zero and nπ elsewhere. |
| Exact actual spectrum | `.spectrum` | Zeros equal the spectrum of the proved ordinary interval realization of the source. |
| Exact multiplicities | `.multiplicity` | Each analytic zero order equals the actual restricted operator's algebraic multiplicity, including repeated complex roots. |
| Hilbert agreement above two | `sourceBoundaryCharacteristic_eq_l2_of_two_le` | The characteristic extends the physical Hilbert function along the source inclusion. |
| Hilbert agreement below two | `sourceBoundaryCharacteristic_eq_l2_of_le_two` | The characteristic is the restriction of the physical Hilbert function to the stronger source space. |
| Unique continuous extension | `sourceBoundaryCharacteristic_unique_continuous` | Agreement on finite Fourier inputs determines the actual normalized function. |

Products use every canonical root, including central roots and their
multiplicities. They converge locally uniformly on the whole complex
spectral plane for each fixed source, including eigenvalues and lattice
points. This is symmetric-product convergence, not an unordered-product
claim or joint local uniformity of lexicographically labeled cutoffs.
Joint analyticity concerns the resulting intrinsic characteristic.

The spectrum is that of the completed interval extension and restricted
operator established earlier. At Hilbert sources, the exact physical
monodromy formula fixes its normalization, not merely its zero set.
Below p=2 there is no assertion that all Hilbert sources belong to the
smaller source space. Uniqueness is already proved among continuous
functions for each fixed spectral parameter.

## Lemma 9.1(ii–iii): continuity and real interlacing

`sourceLemma9_1_real` constructs `SourceLemma9_1RealData` at every
real-type source. Perturbations still range over the full complex
original source space.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Coordinate continuity | `SourceLemma9_1RealData.continuous` | Every signed Dirichlet and Neumann coordinate, under arbitrary complex perturbations. |
| Full sequence continuity | `.norm_continuity` | The complete actual displacement sequence varies continuously in ℓp, for either boundary condition. |
| Real coordinates | `.real` | Every ordinary boundary coordinate has zero imaginary part at real type. |
| Literal interlacing | `.interlacing` | λ⁺_(n−1)<λ⁻_n≤μ_n,ν_n≤λ⁺_n<λ⁻_(n+1). No ordering between μ_n and ν_n is imposed. |
| Signed discriminant level | `.signed_level` | 2≤(-1)^n Re Δ at either boundary root, with an integer exponent also for negative indices. |
| Uniform coordinate control | `.exists_uniform_coordinate_neighborhood` | One original open neighborhood controls both conditions at every signed index, for any positive tolerance. |

The full sequence continuity comes from the previously proved common
analytic domain containing the real-type source locus. This is stronger
than the coordinate continuity stated in the lemma. It does not assert
global continuity of lexicographic labels at arbitrary complex sources.
The indexed interlacing includes collapsed gaps. The existing
`canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap` identifies either
boundary coordinate with the common endpoint in that case.

## Following auxiliary assertions

`sourceLemma9_1_auxiliary` proves the corresponding assertions for the
actual auxiliary restrictions with the endpoint-domain labels on p. 33.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Joint analyticity and literal products | `SourceLemma9_1AuxiliaryData.analytic`, `.product` | Both actual auxiliary products, with the same -1 and zero-mode normalization, on the full complex source space. |
| Actual auxiliary spectra and orders | `.spectrum`, `.multiplicity` | Exact zeros and generalized multiplicities of the auxiliary restricted operators. |
| Coordinate and full sequence continuity | `SourceLemma9_1AuxiliaryRealData.continuous`, `.norm_continuity` | Arbitrary complex perturbations of a real-type base; full actual ℓp displacements. |
| Reality and interlacing | `.real`, `.interlacing`, `.signed_level` | Both auxiliary sequences in the original indexed periodic gaps, including strict neighboring separation. |
| All four sequences at once | `sourceLemma9_1_uniform_coordinate_neighborhood` | One original open neighborhood controls every signed coordinate of both ordinary and both auxiliary sequences. |

`sourceAuxiliaryBoundaryDisplacement` is the ordinary displacement of
the phase-rotated source, identified coordinatewise with the actual
auxiliary root minus nπ. Phase conjugation preserves the original
periodic spectrum and its algebraic multiplicities; ordered-label
uniqueness preserves the original periodic gap indices. The auxiliary
interlacing therefore uses the same gaps as the ordinary statement.
Collapsed auxiliary gaps are covered by
`canonicalAuxiliaryPeriodOneRoots_eq_of_collapsed_gap`.

### Exact auxiliary normalization and the printed labels

`sourceAuxiliaryCharacteristic_finite_eq_classical` identifies the actual
auxiliary product with the classical monodromy formula on finite Fourier
sources at every finite exponent. Density and joint continuity give
`sourceAuxiliaryCharacteristic_eq_ordinary`, expressing each auxiliary
characteristic as the average of the ordinary pair minus its signed
anti-discriminant term. `sourceAuxiliaryCharacteristic_eq_l2_monodromy`
then gives the exact domain-consistent physical formula for every Hilbert
source, without a continuous-representative hypothesis.

The printed p. 53 expressions exchange the endpoint-domain D* and N*
labels. `sourceLemma9_1_printed_starredDirichlet` identifies the printed
plus expression with the actual Neumann product;
`sourceLemma9_1_printed_starredNeumann` identifies the minus expression
with the actual Dirichlet product. Their nonidentity is proved for the
smooth constant potential (1,0) at λ=i, and transferred to the actual
source products at every finite p>1. Under domain-consistent labels the
anti-discriminant is actual N* minus actual D*. The printed algebraic
difference remains valid when its symbols denote its displayed formulas.

## Lemma 9.1 verification

Public checks include p=3/2, the exceptional zero cutoff, free product
limits for both ordinary and auxiliary conditions, full sequence-norm
convergence under complex perturbations, one neighborhood for all four
sequences, negative-index interlacing consequences, collapsed ordinary
gaps, exact repeated auxiliary-root multiplicities, both Hilbert inclusion
directions, extension uniqueness, the exact physical D* monodromy sign,
and the label counterexample at p=3/2.


## Lemma 9.2(i): the normalized analytic anti-discriminant

The statement is on printed p. 53 and its proof on p. 54; both pages
were visually inspected. `sourceLemma9_2` constructs `SourceLemma9_2Data`
for every finite 1<p<∞ and arbitrary complex original source base.
The established function `sourceAntiDiscriminantCandidate` is the actual
normalized extension, despite its legacy name.

| Assertion | Entry point | Scope |
| --- | --- | --- |
| Joint analyticity | `SourceLemma9_2Data.analytic` | Spectral parameter and arbitrary complex original source jointly. |
| Physical agreement above two | `sourceAntiDiscriminant_eq_l2_of_two_le` | Extension of the physical Hilbert monodromy off-diagonal sum. |
| Physical agreement below two | `sourceAntiDiscriminant_eq_l2_of_le_two` | Restriction to the stronger source space along the opposite inclusion. |
| Unique extension | `sourceAntiDiscriminant_unique_joint_continuous` | Jointly continuous functions agreeing with the classical finite Fourier data coincide with the normalized anti-discriminant everywhere. |

The original-domain auxiliary definition is actual N* minus actual D*.
The preceding label audit identifies this with the printed difference
of monodromy expressions and the actual off-diagonal sum. There is no
new sign correction in Lemma 9.2. Physical agreement fixes the exact
function, not only its square, zeros, or an unspecified scalar factor.
Below two, only the included source inputs are used; the smaller space
is not asserted to contain all Hilbert sources.

## Lemma 9.2(ii): the identity at Dirichlet zeros

`sourceLemma9_2_identity` proves Δ(z)²−4=δ(z)² at every zero of the
actual ordinary Dirichlet characteristic. `SourceLemma9_2Data.identity`
expresses it at every canonical signed Dirichlet coordinate, using the
actual value sequence. Both statements include multiple zeros.

This strengthens the printed simple-eigenvalue statement. The existing
global identity Δ²−4=δ²−4χ_Dχ_N is first extended from finite Fourier
sources to every original source by density and joint continuity.
Substitution at a Dirichlet zero removes the product term. The proof
therefore needs no simplicity assumption, locally analytic root branch,
or continuity of the lexicographic labels at complex base points.

## Lemma 9.2(iii): actual full sampled sequences

`sourceDirichletAntiDiscriminantSamples` and
`sourceDirichletAntiDiscriminantDerivativeSamples` are elements of ℓp,
with literal evaluation lemmas at every signed index. Their values are
δ(μ_n) and the spectral derivative δ′(μ_n), respectively.

For every arbitrary complex base φ, `sourceLemma9_2` produces an original
open U containing φ and K≥0. These are chosen before ψ∈U. The fields
`.value_norm` and `.derivative_norm` bound the norms of the complete
actual sequences by that same K for every such ψ. This is local
uniformity in the original source norm, not just pointwise membership.
The returned full-sample neighborhood is not asserted to contain zero
or to be convex; neither property is required by the printed assertion.

The central block is essential. The underlying theorem
`exists_local_uniform_sampled_sourceAntiDiscriminant_at_dirichletRoots`
uses a common spectral cutoff. Tail roots lie in their quarter-pi disks
and are controlled by the ℓp disk majorant. The finitely many central
roots stay in a fixed bounded spectral box. Joint analyticity bounds
δ uniformly on a slightly larger compact ball over one source
neighborhood, and Cauchy's estimate bounds δ′ on the smaller ball.
Finite-block norm estimates combine these central bounds with the tail
bound. This argument does not assume continuity of central complex labels.

Both actual sample sequences vanish entirely at zero potential by
`sourceDirichletAntiDiscriminantSamples_zero` and its derivative analogue.

### One majorant before choosing samples

On the same U and with the same K, `SourceLemma9_2Data.disc_majorant`
provides, for each ψ∈U, an A∈ℓp with norm at most K, chosen before n and z.
For every signed index it controls:

- |δ(z)| by |A_n| throughout the closed disk of radius π/2 about nπ.
- |δ′(z)| by (4/π)|A_n| throughout the closed disk of radius π/4 about nπ.

The larger value disk supports the Cauchy estimate on the derivative
disk. Boundary points, central indices, and negative indices are included.
The existing `exists_uniform_sampled_sourceAntiDiscriminant` therefore
also allows arbitrary potential-dependent samplers in all closed
quarter-pi disks, with norm bounds K and (4/π)K; no regularity of the
sampler is assumed. The full Dirichlet sample estimate separately handles
central roots that need not lie in their free quarter-pi disks.

## Lemma 9.2 verification and remaining scope

Public checks cover arbitrary complex bases at p=3/2, arbitrary Dirichlet
zeros without simplicity, central and negative-index pointwise bounds
from the full norms, both zero-potential sequences, potential-dependent
samplers, nonreal boundary points at every signed index, exact physical
off-diagonal normalization, both Hilbert inclusion directions, and joint
continuous-extension uniqueness.

Next: Lemma 10.1, common isolating neighborhoods and their global connected
domain near real-type sources. The printed domain must also be audited.
This document does not certify the remaining dissertation complete.
