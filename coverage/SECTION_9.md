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

## Verification and remaining scope

Public checks include p=3/2, the exceptional zero cutoff, free product
limits for both ordinary and auxiliary conditions, full sequence-norm
convergence under complex perturbations, one neighborhood for all four
sequences, negative-index interlacing consequences, collapsed ordinary
gaps, exact repeated auxiliary-root multiplicities, both Hilbert inclusion
directions, extension uniqueness, the exact physical D* monodromy sign,
and the label counterexample at p=3/2.

Next is Lemma 9.2: the anti-discriminant extension, its identity at
Dirichlet roots, and locally uniform sampled ℓp bounds. This audit does
not certify the remaining dissertation complete.
