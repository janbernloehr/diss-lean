# Section 3: periodic spectrum

This audit covers the operator setup, Proposition 3.1, Lemmas 3.2, 3.4,
3.6 and 3.7, Corollaries 3.3 and 3.5, and equations (1.4)–(1.5) on printed
pages 23–27.
It retains the original period-two space, its finite-exponent component-sum norm, and the
conditional period-one parity clauses. It is not a completeness certificate
for Section 3 or the dissertation.

## Complete Section 3 assertion inventory

The entire Section 3 text on printed pp.23–27 was read in order and all
five rendered pages were inspected. The 38 ordered groups in the evidence
record distinguish proved assertions, definitions, formal refutations,
explicit interpretations and contextual citations. Each group points to
its precise earlier comparison groups and resolved Lean declarations.

| Passage | Assessment retained by the inventory |
| --- | --- |
| Operator setup | Actual dense one-derivative domain, physical analytic approximation and infinitesimal relative bound; closedness and relative boundedness use alternative proofs. |
| Proposition 3.1 | Full printed package for 1<=p<=4; unrestricted printed height refuted. Height-N counts, discreteness and reality remain valid for every finite p. |
| Lemma 3.2 and Corollary 3.3 | Actual finite-rank compactness proof, scalar Holder estimates and direct Neumann inverse. Missing pair factor and both endpoint sign errors remain refuted. |
| Lemma 3.4 | Main bound with one constant 64*p^2, exact signed component sums and Holder steps; both intermediate uniform-radius estimates remain refuted. |
| Corollary 3.5 and projections | Original-norm square bounds, one neighborhood for all larger exact exteriors, compact segment and actual analytic contour integrals. |
| Parity, ranks and reality | Native period-one parameter topology, full-domain invariance, algebraic counts and real-type pairings at all finite exponents. |
| Lemma 3.7 | Intrinsic rank-two traces, full-domain lifts and local analytic transport for each fixed contour, including repeated roots. |

The high-height prose uses the operator-norm or unit-ball reading, and
height formulas use nonzero imaginary part so their denominators are
finite. Large-parameter decay is used on the stated admissible strips
and exterior. The period-one hypothesis in Lemma 3.6 and fixed-contour
locality in Lemma 3.7 are retained. The two references to Kato and the
printed proof labels are contextual. Earlier implementation checkpoints
below remain historical; their pending-work sentences do not supersede
this qualified inventory.

Section3AssertionInventorySourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records 38 ordered assertion groups,
88 reviewed module hashes and 299 resolved declaration references.
This inventory covers Section 3 and preserves the qualifications of its
earlier evidence; it does not certify the whole chapter or dissertation.
Its Lean sources match the full validation
at `cb7317a`; this documentation update does not rerun Lean.

## The p=1 proof inequalities on printed p. 24

The two endpoint sentences in the proof of Lemma 3.2 print lower bounds
for the reciprocal supremum. Both signs are reversed; the rendered PDF
was checked directly.

[SourceLemma32EndpointProof.lean](../NLS/ZakharovShabat/SourceLemma32EndpointProof.lean)
defines the literal supremum over every signed Fourier index and
identifies it with the existing p=1 reciprocal-symbol norm.

| Printed assertion | Formal counterexample | Proved correction |
| --- | --- | --- |
| Supremum >= sqrt(2)/abs(Im lambda) | At lambda=i the supremum is 1, strictly below sqrt(2). | Supremum <= 1/abs(Im lambda) for nonzero imaginary part. |
| Supremum >= 1/r on Vert_n(r) | At lambda=pi*i, n=0, r=pi/4, the supremum is 1/pi < 4/pi. | Supremum <= 1/r for every stated strip, including real parameters. |

The same upper bounds hold for the actual p=1 free resolvent in the
original component-sum norm. At lambda=i*y, for every nonzero real y,
its norm equals 1/abs(y); the zero Fourier modes attain the bound.
Public examples check y=-2 and the real parameter lambda=1/2.

These proof corrections preserve the valid endpoint and strip clauses.
They are separate from the missing pair factor in the general-p
Lemma 3.2(ii) estimate below. The remaining Section 3 proof assertions
still need their chronological assessment.

Lemma32EndpointProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records the inspected
source and exact declarations.

Validation passes: 8,431 build jobs, 7,466 public examples and a
transitive axiom audit of 42,820 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Radius dependence in the proof of Lemma 3.4, printed p. 25

[SourceLemma34Proof.lean](../NLS/ZakharovShabat/SourceLemma34Proof.lean)
defines the literal near and far double sums with the printed real
half-widths. Their displayed upper bounds cannot have constants depending
only on p. Fixed scalar sequences at p=2 and n=1 suffice:

| Subsum | Signed potential and input modes | Exact value | Printed upper bound for these unit sequences |
| --- | --- | --- | --- |
| Far | potential +1, input +1; only (l,m)=(0,1) contributes | 1/(r*(r+1)) | C/(r+1)^(1/2) |
| Near | potential +2, input +1; only (l,m)=(1,1) contributes | 1/r^2 | C/r |

For every C>=0, the proofs construct a radius 0<r<=pi/4 where the
corresponding inequality fails. The near potential tail retains its
unit norm. These are exact finite-support evaluations of the full sums.

The actual first signed coefficient formula reflects the raw potential
at -(l+m). The near example therefore uses raw potential mode -2 and
input second mode +1, both with original pair norm one. At lambda=pi+i*r
in Vert_1(r), its first output coefficient at -1 has norm 1/r^2. This
also bounds the original pair operator norm from below. The public
examples check both subsums and this operator at r=1/4.

The main [Lemma 3.4 theorem](../NLS/ZakharovShabat/SourceLemma3_4.lean)
remains valid with C_p=64*p^2. Its existing convolution-window proof
retains r^-2 on both terms. These refutations concern the two intermediate
proof displays; no optimality of that constant or new general scalar
subsum upper bounds is asserted.

Lemma34ProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records the precise
source, declarations and retained qualifications.

Validation passes: 8,432 build jobs, 7,468 public examples and a
transitive axiom audit of 42,847 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Uniform squared-Neumann proof of Corollary 3.5

[SourceUniformSquareProof.lean](../NLS/ZakharovShabat/SourceUniformSquareProof.lean)
formalizes the squared inverse on p.25 and the uniform-neighborhood proof
on p.26, using the original finite-p pair norms throughout.

| Source step | Public entry point | Retained scope |
| --- | --- | --- |
| Full-domain inverse | `sourceSpectralPencil_factorization`, `mem_sourceResolventSet_of_square_norm` | Smallness of the actual operator square suffices; first-power norm smallness is unnecessary. |
| Inverse and series | `sourceResolvent_squared_formula`, `hasSum_sourceResolvent_squared`, `isCompactOperator_sourceResolvent_from_square` | The actual resolvent uses (1+T)(1-T^2)^(-1); paired even/odd terms converge in operator norm, and compactness follows from R0. |
| Uniform neighborhood | `sourceFrequencyNeighborhood`, `exists_uniform_sourceFrequencyNeighborhood`, `exists_uniform_sourcePotentialFreeResolvent_square` | A full-norm ball intersected with a Fourier-tail ball is open and convex, contains the potential and zero, and controls all sufficiently large signed indices. |
| Printed quarter/half bounds | `exists_source_quarter_half_strips` | Quarter bound at the given potential and half bound throughout one connected neighborhood, with strict absolute-index inequality. |
| Exact exterior | `exists_source_square_uniform_height_and_strips`, `exists_source_spectralExterior_square_bound`, `sourceCorollary3_5_from_square` | One positive cutoff and one neighborhood work for every larger cutoff, preserving the strict real box edge, included horizontal edge and open disks. |
| Compact segment | `sourcePotentialSegment_compact_in_neighborhood` | The real segment from zero to the potential is a continuous image of the compact unit interval and is contained in the same convex neighborhood. |

The source estimate uses the valid main Lemma 3.4 constant 64*p^2.
The refuted intermediate radius bounds are not used. Existing analytic
dependence on the full source resolvent set supplies analyticity once
the squared inverse establishes membership in that set.

Four examples distinguish the retained cutoff frequencies +2 and -2 from
the next cutoff, test strict neighborhood membership at original l1 norm
seven, exhibit an actual perturbation of norm at least two with square
zero and a two-term resolvent, and control a negative-index circle
boundary at p=3 on one common neighborhood.

Cor35UniformProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records six focused groups.
All earlier source corrections and qualifications remain. This does not
certify every assertion in Section 3.

Validation passes: 8,440 build jobs, 7,498 public examples and a
transitive axiom audit of 42,983 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Direct Neumann proof of Corollary 3.3

[SourceNeumannProof.lean](../NLS/ZakharovShabat/SourceNeumannProof.lean)
formalizes the potential-composition estimate, inverse formula, Neumann
series and compactness inference printed on p.25.

| Source step | Public entry point | Retained scope |
| --- | --- | --- |
| Composition estimate | `norm_sourcePotentialFreeResolvent_le_scalar`, `norm_sourcePotentialFreeResolvent_le_height` | The exact factor-one height bound in the original finite-p pair norm, including p=1. |
| Strict smallness | `norm_sourcePotentialFreeResolvent_lt_one` | The printed numerical region, with nonzero imaginary part so its denominators are defined. |
| Inverse and series | `sourceResolvent_neumann_formula`, `hasSum_sourceResolvent_neumann` | The actual source resolvent equals R0 times the geometric inverse and the operator-norm sum of its Neumann series. |
| Compactness | `isCompactOperator_sourceResolvent_from_neumann` | Follows from the explicit finite-cutoff compactness proof for R0 and the bounded geometric inverse. |
| Pair-norm regression | `sourceNeumann_survives_pairCounterexample` | At p=2 and z=i/10000, the standalone p-to-l1 norm exceeds 10800, while every potential composition is bounded by 10800 times its potential norm. |

The direct estimate applies Young's inequality to each off-diagonal
component and sums their p-powers. It therefore proves the composition
bound without the factor needed for the standalone map into l1 pairs.
No additional source correction is needed for this Corollary 3.3 step.

Four examples use both nonzero components at p=1 and z=30i, small
potentials at the p=2 counterexample parameter, p=3 at z=-i, and the
actual series for the nonzero p=1 potential. The existing analytic
dependence and discreteness results are retained with their previous proofs.

Cor33NeumannProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records three focused groups.
All earlier source corrections and qualifications remain. This does not
certify every assertion in Section 3.

Validation passes: 8,439 build jobs, 7,494 public examples and a
transitive axiom audit of 42,948 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Finite-rank proof of Lemma 3.2(i)

[SourceFreeResolventCutoff.lean](../NLS/ZakharovShabat/SourceFreeResolventCutoff.lean)
exposes the Fourier-series and finite-rank closure argument printed on p.24.
All input and output spaces use the original finite-p pair norm, including
l1 as stated in the dissertation.

| Source step | Public entry point | Retained scope |
| --- | --- | --- |
| Actual signed Fourier expansion | `sourceFreeResolvent_fst_apply`, `sourceFreeResolvent_snd_apply`, `hasSum_sourceFreeResolvent_signed` | A convergent series with common signed denominator z-pi*m; the first raw frequency is -m. |
| Explicit finite-rank operators | `sourceFreeResolventCutoff`, `finiteDimensional_sourceFreeResolventCutoff`, `finrank_sourceFreeResolventCutoff_le` | Arbitrary finite sets of raw frequencies; the range injects into two finite coefficient lists and has dimension at most 2*card(s). |
| Operator-norm closure | `tendsto_sourceFreeResolventCutoff`, `exists_sourceFreeResolventCutoff_norm_sub_lt` | One approximation for every positive tolerance; every z outside the free lattice, including real z. |
| Compactness | `isCompactOperator_sourceFreeResolventCutoff`, `isCompactOperator_sourceFreeResolvent_from_cutoffs` | Compact finite-rank approximants converge to the actual original-norm free resolvent. |

The convergence proof uses the uniform reciprocal-symbol tails in both
integer directions and continuous conjugation between equivalent norms.
It does not identify the original pair norm with the auxiliary maximum norm.
The four examples check output l1 norm seven after deleting nonzero modes,
output norm three from an asymmetric cutoff of two resonant signed modes,
a negative-center signed series at p=3, and an approximation of error
less than 1/100 at the real point pi/2.

Lemma32CompactProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records three focused groups.
The pair-norm correction in part (ii) and the endpoint counterexamples remain.
This does not certify every assertion in Section 3.

Validation passes: 8,438 build jobs, 7,490 public examples and a
transitive axiom audit of 42,940 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Scalar calculations in the proof of Lemma 3.2

[SourceLemma32ScalarProof.lean](../NLS/ZakharovShabat/SourceLemma32ScalarProof.lean)
proves the displayed scalar estimates on p.24 using the actual signed
components and their original norms.

| Source step | Public entry point | Retained scope |
| --- | --- | --- |
| Signed component formulas and exact l1 sums | `sourceFreeResolvent_signed_fst`, `sourceFreeResolvent_snd_scalar`, `sourceFreeResolvent_fst_norm_sum`, `sourceFreeResolvent_snd_norm_sum` | First raw frequency is reflected; second is unchanged. Every finite p, including one. |
| Literal Hölder display | `summable_scalarFreeL1Bound_moment`, `scalarFreeL1Bound_moment`, `sourceFreeResolvent_fst_le_moment`, `sourceFreeResolvent_snd_le_moment` | Finite p>1, z outside the free lattice; the powered series converges. |
| Centered denominator geometry | `complex_norm_ge_l1_div_sqrt_two`, `centered_real_gap_sqrt_two`, `centered_denominator_sqrt_two` | Exact sqrt(2) constants, closed half-width pi/2, every signed pair of indices. |
| Punctured reciprocal series | `punctured_centered_reciprocal_sum` | Exact 2p/alpha^(q-1), positive alpha and arbitrary signed center. |
| Both scalar height comparisons | `scalarFreeL1Bound_height_moment`, `height_moment_numerical`, `scalarFreeL1Bound_height_moment_chain` | Exact intermediate moment and 4p/abs(Im z)^(1/p)+1/abs(Im z); nonzero imaginary part. |
| Scalar strip display | `scalarFreeL1Bound_moment_le_verticalStrip` | Exact 4p/r, 0<r<=pi/4; no nonzero-imaginary-part hypothesis. |

The existing `sourceLemma34_denominator_lower` also supplies the identical
strip denominator inequality printed in this passage. The strip moment
proof uses the established stronger scalar estimate 2p/r.
The six examples check a half-strip boundary, a puncture at -3, the exact
output l1 norm 7 of two signed modes at -2*pi+i, the infinite reciprocal
moment at i against 9, unequal conjugates 3 and 3/2, and a negative strip
center with bound 16.

The scalar height calculation does not remove the factor
`CoeffPair.l1Factor p` when combining the two original components.
Both reversed endpoint lower bounds remain formally refuted.
Lemma32ScalarProofSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records five focused groups;
these do not certify every assertion in Section 3.

Validation passes: 8,437 build jobs, 7,486 public examples and a
transitive axiom audit of 42,911 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Hölder displays and endpoint estimates in Lemma 3.4

[SourceLemma34Holder.lean](../NLS/ZakharovShabat/SourceLemma34Holder.lean)
proves the two first Hölder displays before their separately refuted
uniform radius simplifications.

| Source step | Public entry point | Retained scope |
| --- | --- | --- |
| Literal denominator powers | `lemma34Holder_weight_eq` | The reciprocal product power is exactly the printed product of powered denominators. |
| Selected-set Hölder inequality | `lemma34_masked_holder` | Finite p>1, 0<r<=1, arbitrary integer-pair subsets; both powered sums are summable. |
| Numerator reduction | `summable_lemma34NumeratorMoment`, `lemma34NumeratorMoment_eq`, `lemma34MaskedNumeratorMoment_le` | Full moment equals the product of original scalar norm powers; selected roots are bounded with constant one, for all finite p>=1. |
| Far display | `lemma34ProofFarSum_le_holder` | Exact strict far disjunction and its reciprocal moment. |
| Near display and tail | `lemma34ProofNearSum_le_holder_tail` | Exact closed near set and symmetric remainder retaining abs(k)=abs(n). |
| Endpoint modification | `lemma34MaskedSum_le_one`, `lemma34ProofNearSum_le_one`, `lemma34ProofFarSum_le_one` | Original l1 norms; near factor 1/r^2 and far factor 2/(r*(r+abs(n))), including zero and negative centers. |

The examples check a cubic numerator moment of 216, the fixed p=2 far
witness against the valid Hölder bound, a negative p=1 near mode attaining
4 at r=1/2, and an infinite-support l1 far bound with coefficient 8/7.
The previous actual signed-component majorizations apply to these scalar
bounds. The general-p radius-free far estimate and r^(-2/p) near estimate
retain their existing counterexamples. No new source refutation is claimed.

Lemma34HolderSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups.
They do not certify every proof assertion in Section 3.

Validation passes: 8,436 build jobs, 7,480 public examples and a
transitive axiom audit of 42,890 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Absolute double-sum majorization in Lemma 3.4

[SourceLemma34Majorization.lean](../NLS/ZakharovShabat/SourceLemma34Majorization.lean)
proves the valid steps surrounding the separately refuted subsum bounds.
[SandwichAbsoluteSum.lean](../NLS/SequenceSpaces/SandwichAbsoluteSum.lean)
provides the underlying absolutely convergent positive double series.

| Source assertion | Public entry point | Retained scope |
| --- | --- | --- |
| Denominator geometry, p.25 | `sourceLemma34_denominator_lower`, `sourceLemma34_denominator_product` | Literal r/sqrt(2)+abs(n-m) bound and factor two, all signed integers and 0<r<=pi/4, including boundaries. |
| Convergence of the majorant | `summable_lemma34ProofTerm` | Every finite Banach exponent, with bounded conjugate symbols at p=1; infinite-support data allowed. |
| Component norm estimates | `norm_sourceDoubleResolvent_fst_le_absolute_sum`, `norm_sourceDoubleResolvent_snd_le_absolute_sum` | Actual source resolvent, exact signed reflections and original scalar l1 output norms. |
| Original pair norm | `norm_sourceDoubleResolvent_le_absolute_sums` | Sum of the two actual l1 component norms, with no maximum-norm substitution. |
| Near/far partition | `not_lemma34ProofNear_iff`, `lemma34Proof_absolute_sum_eq_far_add_near` | Exact strict/non-strict boundary and real half-width abs(n)/2; both masked series converge. |
| Near-region potential tail | `lemma34ProofNear_frequency_lower`, `lemma34ProofNearSum_fourierTail` | Exact symmetric remainder with abs(k)>=abs(n), including zero and negative centers. |

The four examples exercise r=pi/4 at a strip edge, a reflected negative
p=1 mode giving an actual component bound 2/r^2, a negative cutoff mode
whose near sum is 4/9, and infinite-support reciprocal coefficients at p=3.

The component and convergence arguments include the p=1 endpoint and the
second component mentioned at the end of the proof. The later printed
uniform far and near estimates retain their formal counterexamples.
The main lemma's independent r^-2 estimate remains valid.
Lemma34MajorizationSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records five focused groups;
they do not certify every proof assertion in Section 3.

Validation passes: 8,435 build jobs, 7,476 public examples and a
transitive axiom audit of 42,878 NLS declarations. The 21 inherited
warnings are unchanged; the new modules and examples introduce none.

## Direct source-norm setup and resolvent estimates

[SourceSection3Setup.lean](../NLS/ZakharovShabat/SourceSection3Setup.lean)
adds direct statements on the original source operators and norms:

| Source assertion | Public entry point | Retained scope |
| --- | --- | --- |
| Closed, densely defined operator, p.23 | `sourceUnboundedOperator_isClosed`, existing `sourceUnboundedOperator_dense_domain` | Every finite Banach exponent and arbitrary period-two potential; actual full one-derivative domain. |
| Actual graph | `mem_sourceUnboundedOperator_graph`, `mem_sourceUnboundedOperator_graph_iff_inverse` | Included domain vector and its image, characterized by a bounded inverse in the base norm. |
| First resolvent identity, p.23 | `sourceResolvent_comp_one_sub_potentialFreeResolvent` | Both actual inverse assumptions; no smallness requirement. |
| Young inequality (1.3) | `norm_sourcePotentialFromL1_apply_le`, `sourceEquation1_3` | Constant one in the original finite p and l1 pair norms. |
| High-height smallness | `exists_sourceFreeResolventToL1_uniform_small` | One height for both half-planes and all parameters, in the original p-to-one operator norm. |
| Second signed coefficient, p.25 | `sourceDoubleResolvent_signed_snd_apply` | Exact integer reflection of the input first component. |
| Square estimate, p.26 | `norm_sourcePotentialFreeResolvent_sq_le` | Original potential norm times original double-resolvent norm, without conversion factors. |

The existing physical analytic approximation and infinitesimal relative
bounds remain available. Closedness uses an actual bounded spectral
inverse; it does not follow merely from continuity on the stronger domain.
The p=3 graph-limit example assumes convergence only in the base norm.

The high-height sentence in the source is read as an operator-norm or
unit-ball statement. No bound independent of arbitrary input scaling is
asserted. The public p=1 example makes the unit-ball quantifier explicit.
The general Young helper also works for the legacy maximum infinity pair
norm; that additional instance is not the distinct original infinity norm.

Other examples attain the constant-one Young bound at p=3 and recover
the exact second coefficient 1/(lambda-pi)^2 from reflected endpoint modes.
Section3SetupSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records six focused groups;
it does not certify every assertion in the section.

Validation passes: 8,433 build jobs, 7,472 public examples and a
transitive axiom audit of 42,858 NLS declarations. The 21 inherited
warnings are unchanged; the new module and examples introduce none.

## Operator setup

The remaining-scope comparison also connects the opening dense-domain, analytic
approximation and arbitrarily small relative-bound assertions to their original-norm
proofs. Relative boundedness is proved using resolvent decay and closedness
using a bounded inverse; these establish the assertions by different arguments
from the printed perturbation sketch. Compact-resolvent discreteness is traced
through the reciprocal spectral transformation and finite bounded spectral
parts. The comparison preserves the exact strip boundaries and nonzero-imaginary-part
interpretation of the height region. It retains the restricted exponent range
for the printed Proposition 3.1 height, the missing Lemma 3.2 pair factor,
the uniform constant 64*p^2 in Lemma 3.4 and the valid p=1 and second-component
modifications. The later radius refutations remain separate.

Section3RemainingScopeSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records 8 focused groups,
32 reviewed module hashes and 60 resolved declaration references.
This comparison preserves the earlier qualifications and does not certify
every assertion in Section 3. Its Lean sources match the full validation
at `cb7317a`; this documentation update does not rerun Lean.

`Operator.lean` defines the full one-derivative coefficient domain and the
Zakharov–Shabat operator for every finite Banach exponent.
`sourceUnboundedOperator_dense_domain` and `sourceUnboundedOperator_isClosed`
now state density and closedness directly in the original source norm,
without restricting the potential size. The corresponding maximum-coordinate
closedness theorem remains in `ClosedOperator.lean`. Both components use scalar Fourier modes;
the first component is reflected relative to the signed convention in
(1.2). Index reflection preserves the source coefficient norm.

The operator infrastructure uses maximum-norm product coordinates.
`NLS.CoeffPair.toMax` is the continuous linear equivalence from the source
component-sum norm to those coordinates, and `norm_toMax_le` is the
contractive comparison. The new height formulas retain the norm before
this conversion. The parameter is not restricted to the image of
`periodOnePotential`; odd Fourier coefficients are allowed.

## Proposition 3.1

| Printed requirement | Public entry point | Verified scope |
| --- | --- | --- |
| Discreteness | `proposition3_1_discreteness_and_reality` | Every finite p, every period-two source. |
| One neighborhood and a positive cutoff | `exists_proposition3_1_up_to_four` | 1<=p<=4; one open convex neighborhood containing the source and zero, valid for all larger cutoffs. |
| (i) Two eigenvalues in each high quarter-pi disk | `Proposition3_1Data.disk_multiplicity` | Algebraic multiplicities sum to two; a double value is allowed. |
| (i) Conditional periodic/antiperiodic eigenfunctions | `Proposition3_1Data.disk_parity`, `disk_eigenvector_unit_translation` | Under even potential support, the entire root space has the index parity; the eigenfunction has the actual pointwise unit-translation phase at every finite exponent. |
| (ii) Central count in the printed-height box | `Proposition3_1Data.central_multiplicity` | Algebraic multiplicity 4N+2 using exactly `(1+8*norm(phi))^p` in the source norm, proved for 1<=p<=4. |
| (ii) Conditional central parity counts | `Proposition3_1Data.central_parity` | Dimensions of the periodic/antiperiodic sectors of the actual rectangular projection: 2N+2 in the matching parity and 2N in the other. |
| (iii) No other eigenvalues | `Proposition3_1Data.exhaustion` | Printed box plus high disks, in the proved exponent range. |
| (iv) Real-type reality | `proposition3_1_discreteness_and_reality` | Every finite p, without a printed-height assumption. |
| Actual moving projections | `exists_periodTwo_periodicCounting_printed_height_up_to_four` | The printed-height rectangular integral equals the central spectral projection and is analytic on the same neighborhood. |
| All-finite-p qualitative counting | `exists_periodTwo_periodicCountingData` | The established height-N central box, full counts, conditional parity, and exhaustion in the original period-two source topology. This is separate from the printed quantitative height. |
| Refutation of the unrestricted printed claim | `proposition3_1_printed_height_counterexample`, `not_proposition3_1_all_p` | Balanced sources with norm <=1/16, already of period one, have an actual spectral point outside every printed-height box/high-disk union at explicit large finite exponents. |

All unqualified entry points in this table lie in `NLS.ZakharovShabat`.
The all-exponent height discrepancy already recorded for Theorem 1.1
therefore also applies to Proposition 3.1. No proposed height correction
has been adopted, and nothing here asserts the printed formula for every
p>4. Discreteness, reality, and the height-N counting result remain valid.

## Lemma 3.2

The printed operator norm has the original source p-norm on the input and
the original component-sum l1 norm on the output. These are not the same
operator norms as the existing maximum-product estimates.

| Printed requirement or correction | Public entry point | Verified scope |
| --- | --- | --- |
| Actual operator in the source norms | `sourceFreeResolvent`, `sourceFreeResolventToL1` | Coefficient-preserving conjugation by `CoeffPair.toMax`; all finite Banach exponents. The target-one coefficients are exactly the original reciprocal symbols. |
| (i) Compactness on the l1 source space | `isCompactOperator_sourceFreeResolvent`, `sourceFreeResolventToL1_one` | Every parameter off the free lattice; base-space compactness also holds for every finite p. |
| Exact component comparison | `NLS.CoeffPair.componentNormSum_le`, `l1Factor_mul_norm_diagonal` | Factor 2^(1-1/p), attained by equal components, with factor one at p=1. |
| Corrected height estimate | `norm_sourceFreeResolventToL1_le_height` | The printed expression multiplied by the component comparison factor; all finite p and nonzero imaginary part. |
| Necessary pole factor | `l1Factor_div_norm_le_sourceFreeResolventToL1` | The actual original-norm operator norm is at least 2^(1-1/p)/abs(lambda), from the two zero modes. |
| (ii) Printed estimate at p=1 | `norm_sourceFreeResolventToL1_one_le_height` | The component comparison factor is exactly one. |
| (ii) Refutation in general | `lemma3_2_printed_height_bound_false`, `not_lemma3_2_ii_original_norms` | A concrete p=2 counterexample at lambda=i/10000, off the free lattice and with nonzero imaginary part. |
| Exact counterexample data | `lemma3_2Counterexample_input_norm`, `lemma3_2Counterexample_output_norm`, `lemma3_2Counterexample_printed_rhs` | Input norm sqrt(2), output norm 20000, printed operator bound 10800; both input components are the constant Fourier mode. |
| (iii) Printed strip bound | `norm_sourceFreeResolventToL1_le_verticalStrip` | Original p-to-one pair norms, all finite p, radius 0<r<=pi/4. |
| Stronger proved strip bound | `norm_sourceFreeResolventToL1_le_verticalStrip_four` | Constant 4p/r, hence the printed 8p/r follows. |

Except for the explicitly qualified component lemmas, these entry points
lie in `NLS.ZakharovShabat`. The corrected height bound is separate from
the false printed clause (ii). The maximum-product estimate remains valid;
a change of norms without its quantitative factor cannot establish the
printed original-norm assertion.

## Corollary 3.3

The printed region retains the original potential norm. Its denominators
require nonzero imaginary part, made explicit in the formal definition.
All results below hold on the entire period-two space for 1<=p<infinity,
including p=1 and with no even-support restriction.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Actual source operator and pencil | `sourceOperator`, `sourceSpectralPencil_eq` | Original component-sum norms on both the base and one-derivative domain; pencil equals lambda times inclusion minus operator. |
| Full resolvent set | `sourceResolventSet_eq`, `isOpen_sourceResolventSet` | Exact equality with the established maximum-product resolvent set and openness. |
| Both actual inverse identities | `sourceSpectralPencil_sourceResolventToDomain`, `sourceResolventToDomain_sourceSpectralPencil` | Throughout the full source resolvent set, with the original one-derivative domain norm. |
| Base-space versus domain-valued inverse | `sourceResolvent_eq_inclusion_comp` | Coefficient-preserving domain inclusion composed with the domain-valued inverse. |
| Printed numerical region | `sourceHeightNeumannRegion_subset_resolventSet` | Exactly the printed sufficient inequality measured with the original potential norm, using the valid maximum-product Neumann estimate. |
| Openness and nonemptiness | `isOpen_sourceHeightNeumannRegion`, `sourceHeightNeumannRegion_nonempty` | Every finite Banach exponent and every source. |
| Uniform height | `exists_uniform_sourceHeightNeumannRegion` | One height works for every potential in an original-norm ball and both signs of the imaginary part. |
| Compactness and analyticity | `isCompactOperator_sourceResolvent`, `analyticOnNhd_sourceResolvent` | Compact analytic inverse on the full source resolvent set, hence on the printed region. |
| Discrete spectrum | `discreteTopology_sourceResolventSet_compl` | The complement of the actual source resolvent set has discrete subspace topology. |
| Free compatibility | `mem_sourceResolventSet_zero_of_notMem`, `sourceResolvent_zero_eq_free` | At zero potential, every parameter off the free lattice, including real parameters. |
| Assembled corollary | `sourceCorollary3_3` | Open nonempty numerical region, compact analytic inverse, both identities, and discrete spectrum in the original norms. |

These entry points lie in `NLS.ZakharovShabat`. The failure of the
original p-to-one estimate in Lemma 3.2(ii) does not invalidate this
corollary: contractivity of the potential conversion gives the sufficient
Neumann condition before transporting the inverse to the original norms.

## Lemma 3.4

The operator has the original p norm on its input and the original l1
component-sum norm on its output. The source leaves c_p unspecified;
the proved choice c_p=64p² depends only on p and works for every finite
Banach exponent. No claim of optimality is made.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Actual sandwich | `sourceDoubleResolvent_eq_comp` | R0 Phi R0 as the composition of the original-norm free resolvent and potential convolution. |
| Both component formulas | `sourceDoubleResolvent_fst_apply`, `sourceDoubleResolvent_snd_apply` | Exact convergent-sum coefficient formulas in the raw scalar Fourier convention, for all parameters off the free lattice. |
| Norm conversion | `norm_sourceDoubleResolvent_le_max` | Original p-to-one operator norm is at most twice the maximum-product operator norm. |
| Explicit strip estimate | `norm_sourceDoubleResolvent_le_verticalStrip` | c_p=64p², every period-two potential, 1<=p<infinity, 0<r<=pi/4, and every punctured strip. |
| Constant quantified independently of the potential | `sourceLemma3_4` | One positive c_p precedes every potential, radius, strip index, and spectral parameter; strip membership supplies existence of the free inverse. |
| Actual source remainder | `sourceFourierTail_fst`, `sourceFourierTail_snd` in `SourceFourierTail.lean` | Retains precisely the modes with abs(j)>=N, including boundary modes, in both original components. |
| Remainder at zero and contraction | `sourceFourierTail_zero`, `norm_sourceFourierTail_le` | Cutoff zero gives the full potential; every cutoff is contractive in the original finite pair norm. |
| Remainder monotonicity and convergence | `norm_sourceFourierTail_antitone`, `tendsto_sourceFourierTail` in `SourceFourierTail.lean` | Existing original-norm results reused by the new estimate. |
| Vanishing numerical bound | `tendsto_sourceDoubleResolventBound_zero` | The frequency term and original-norm remainder both vanish as the absolute cutoff grows. |
| Uniform smallness on high strips | `exists_sourceDoubleResolvent_small` | For every positive epsilon and fixed admissible radius, one cutoff works for both signs of the strip index and every spectral parameter in those strips. |

These entry points lie in `NLS.ZakharovShabat`. The factor two in the
comparison comes from the l1 output norm; the base and potential maps to
the maximum norm are contractive. It changes the admissible unspecified
constant, without changing the printed assertion. At index zero, the
full potential remainder controls the strip; Lean's totalized division
sets the frequency term to zero. No use is made of the false original-norm
height estimate in Lemma 3.2(ii).

## Corollary 3.5

All results use the full period-two source space with its original finite
component-sum norm. The central box retains strict real-part bounds and
non-strict imaginary-part bounds. Only open quarter-pi disks at indices
abs(n)>N are removed. There is no printed norm-dependent height here.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Common neighborhood and cutoff | `sourceCorollary3_5` | Every finite Banach exponent and period-two potential; one positive cutoff and an open, convex, connected source neighborhood containing both the potential and zero. |
| Exact exterior region | `spectralExterior`, `centralSpectralBox`, `highSpectralDisks` in `SpectralLocalization.lean` | Exactly the printed mixed-boundary box and open quarter-pi disks with abs(n)>N. |
| Actual resolvent inclusion | `sourceCorollary3_5` | Every exterior point belongs to `sourceResolventSet` for every source in the same neighborhood; this supplies both inverse identities from `SourceResolvent.lean`. |
| Compact analytic source resolvent | `sourceCorollary3_5` | The actual original-norm resolvent is analytic near every exterior point and compact there. |
| Spectrum enclosure | `sourceCorollary3_5` | The complement of the full source resolvent set lies in the stated central box and high-disk union. |
| Same neighborhood for larger cutoffs | `sourceCorollary3_5_all_larger` | All conclusions hold for every N>=N0 on one common neighborhood. |
| Horizontal boundary and strips | `exists_source_uniform_height_and_strips` | Includes abs(Im(lambda))=N and every punctured strip with abs(n)>=N; the radius may be any 0<r<=pi/4. |
| Vertical boundary case | `spectralExterior_height_or_strip` in `SpectralLocalization.lean` | The exact real-part edge may use abs(n)=N, so the non-strict strip cutoff is retained. |

The new entry points are in `SourceCorollary3_5.lean`, in the Lean
namespace `NLS.ZakharovShabat`. Neighborhoods
are pulled back through the coefficient-preserving continuous linear
equivalence, and the full resolvent-set identity connects them to the
actual original-norm inverse. Convexity includes the whole real line
segment from zero to the potential, including at p=1. The horizontal
boundary belongs to the box; its admissibility comes from the stronger
height-and-strips result, rather than exterior inclusion alone.

## Equation (1.4): actual Cauchy-Riesz projectors

The renewed proof comparison covers equation (1.4), the intervening parity
definitions and Lemma 3.6, and equation (1.5). On each fixed compact circle,
pointwise pencil invertibility gives a unit in the Banach algebra of
continuous operator-valued functions. Analytic inversion in the uniform
norm and bounded normalized integration give analytic actual projections.
The signed parity masks are closed topological complements; frequency
doubling is an isometry of the base space onto the entire even subspace.
The operator proof retains the full one-derivative domain and period-one
potential hypothesis. Restricted-projector openness is in the native
period-one potential topology. The existing odd-potential counterexample
confirms the necessity of that hypothesis; it is not a source erratum.

Section3ProjectionParitySourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups,
10 reviewed module hashes and 33 resolved declaration references.
This comparison preserves the earlier qualifications and does not certify
every assertion in Section 3. Its Lean sources match the full validation
at `cb7317a`; this documentation update does not rerun Lean.

The normalized integrals use the actual original-norm resolvent as their
integrand. The central rectangle retains all four boundary edges, and the
distant circles have radius pi/4 and positive orientation. Every finite
Banach exponent and every period-two source are included.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Actual normalized circle integral | `sourceResolventCircleIntegral` | Operator-norm integral of `sourceResolvent`, with factor (2*pi*i)^(-1). |
| Actual rectangular and central integrals | `sourceResolventRectangleIntegral`, `sourceCentralRectangleIntegral` | Four oriented edges; central corners are exactly those of the height-N box. |
| Circle and rectangle integrability | `circleIntegrable_sourceResolvent`, `rectangleIntegrable_sourceResolvent` | The entire contour lies in the actual source resolvent set. |
| Coefficient-preserving conjugation of the actual integrals | `sourceResolventCircleIntegral_eq_conj`, `sourceResolventRectangleIntegral_eq_conj`, `sourceCentralRectangleIntegral_eq_conj` | Bounded linear conjugation commutes with integration on admissible contours. |
| Evaluation on source vectors | `sourceResolventCircleIntegral_apply`, `sourceResolventRectangleIntegral_apply` | Evaluation of the operator integral equals the integral of the evaluated resolvent. |
| Projection identities | `sourceResolventCircleIntegral_idempotent`, `sourceCentralRectangleIntegral_idempotent` | Idempotence on the entire original-norm base space. |
| Compactness | `isCompactOperator_sourceResolventCircleIntegral`, `isCompactOperator_sourceCentralRectangleIntegral` | Compactness of the actual contour operators. |
| Finite rank | `finiteDimensional_range_sourceResolventCircleIntegral`, `finiteDimensional_range_sourceCentralRectangleIntegral` | The range of each compact idempotent is finite-dimensional. |
| Circle analytic dependence | `analyticAt_sourceResolventCircleIntegral` | Analytic in the original potential norm wherever the fixed circle is admissible. |
| Common central neighborhood | `exists_uniform_sourceCentralRectangleIntegral` | Every larger central rectangle is admissible and gives an analytic projector on one original-norm neighborhood. |
| Full simultaneous equation (1.4) package | `sourceEquation1_4` | One positive cutoff and open convex connected neighborhood containing source and zero; every larger central rectangle and every distant quarter-pi circle is admissible and yields an analytic compact finite-rank projection on that same neighborhood. |

The entry points lie in `NLS.ZakharovShabat`, in `SourceResolventContours.lean`
and `SourceEquation1_4.lean`. Analyticity here concerns the potential, as
stated after equation (1.4). The common neighborhood includes p=1 and has
no period-one restriction. The entire central boundary is proved admissible,
including its horizontal edges; exterior inclusion alone would not cover
those edges. The actual integrals are defined first, then identified with
the conjugated maximum-product operators under the stated contour hypotheses.

The original-norm parity subspaces and Lemma 3.6 are verified below.


## Parity subspaces and Lemma 3.6

The source's period-one hypothesis is explicit in the proof of Lemma 3.6.
The following results concern the original finite-exponent component-sum
norms and the original one-derivative operator domain.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Even and odd coefficient conditions | `mem_sourceParitySubspace_zero_iff`, `mem_sourceParitySubspace_one_iff` | Both components vanish at every 2m+1 or every 2m, respectively, including negative frequencies. |
| Closed base and domain subspaces | `isClosed_sourceParitySubspace`, `isClosed_sourceDomainParitySubspace` | Closedness in the original norms. |
| Direct sum and topological complement | `isCompl_sourceParitySubspaces`, `isTopCompl_sourceParitySubspaces` | The two subspaces span the entire base space and have trivial intersection; the splitting is continuous. |
| Bounded parity masks | `sourceParityProjection`, `sourceDomainParityProjection` | Exact coefficient masks on the original base space and domain. |
| Contractive base projections | `norm_sourceParityProjection_apply_le` | Every finite Banach exponent. |
| Period-one identification | `sourcePeriodOneEquiv` | Linear isometric equivalence onto the even subspace; the inverse reads the even coefficients. |
| Lemma 3.6 | `sourceLemma3_6` | Every finite Banach exponent, including p=1, for potentials embedded canonically from period one. |
| Explicit support version | `sourceOperator_mem_sourceParitySubspace` | Every even-supported potential preserves each parity on its operator domain. |
| Domain/base intertwining | `sourceOperator_domainParityProjection` | Applying the domain mask before the operator equals applying the base mask after it. |
| Resolvent commutation | `sourceParityProjection_commute_resolvent` | The actual original-norm resolvent, throughout its full resolvent set, for even-supported potentials. |
| Circle integral commutation | `sourceParityProjection_commute_circleIntegral` | The actual normalized circle integral on every admissible circle, for even-supported potentials. |
| Necessity of period one | `lemma3_6EvenInput_mem`, `lemma3_6_even_support_needed` | An explicit odd potential sends a verified even domain vector outside the even subspace. |

Entry points lie in `NLS.ZakharovShabat`, in `SourceParity.lean` and
`SourceLemma3_6.lean`. The necessity example confirms the source hypothesis;
it does not identify a source error. Equation (1.5) is verified below.


## Equation (1.5): actual restrictions and period-one analyticity

The two projection families are continuous linear endomorphisms of the
original-norm parity subspaces. The common neighborhood is in period-one
potential coordinates, embedded into the period-two operator by `periodOnePair`.
All finite Banach exponents, including p=1, are covered.

| Printed requirement or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Bounded operation on operators | `sourceParityCompression` | Maps each ambient operator to a continuous linear endomorphism of the chosen parity subspace. |
| Actual restriction | `sourceParityCompression_apply` | For a commuting ambient operator, the output is exactly its value on the input vector. |
| Exact restricted range | `mem_range_sourceParityCompression_iff` | For a commuting idempotent, membership in the restricted range is equivalent to ambient range membership of the underlying vector. |
| Analytic restriction construction | `analyticAt_sourceParityCompression` | The bounded operation is analytic in the ambient operator. |
| Rectangle and central commutation | `sourceParityProjection_commute_rectangleIntegral`, `sourceParityProjection_commute_centralIntegral` | Even-supported potentials; full admissible rectangular boundary. |
| Typed circle and central projections | `sourceParityCircleProjection`, `sourceParityCentralProjection` | Domain and codomain are both the chosen parity subspace. |
| Agreement with actual integrals | `sourceParityCircleProjection_apply`, `sourceParityCentralProjection_apply` | Exact vector equality on admissible contours for even-supported potentials. |
| Projection identities | `sourceParityCircleProjection_idempotent`, `sourceParityCentralProjection_idempotent` | Idempotence on the parity subspace itself. |
| Finite rank | `finiteDimensional_range_sourceParityCircleProjection`, `finiteDimensional_range_sourceParityCentralProjection` | The restricted range injects into the finite-dimensional ambient range. |
| Local circle analyticity | `analyticAt_sourceParityCircleProjection` | Original period-one potential coordinates at any source with an admissible circle. |
| Full equation (1.5) package | `sourceEquation1_5` | One positive cutoff and open convex connected neighborhood containing source and zero; both parities, every larger central cutoff, and all abs(n)>N quarter-pi circles. Analyticity, actual restriction identities, idempotence, and finite rank all hold on the same neighborhood. |

Entry points lie in `NLS.ZakharovShabat`, in `SourceParityRestriction.lean`
and `SourceEquation1_5.lean`. The operator definitions extend by compression
to arbitrary potentials; their interpretation as the source's restrictions
is proved under even support and contour admissibility. `sourceEquation1_5`
supplies those hypotheses automatically in period-one coordinates. Earlier
fixed-height qualifications are unchanged.

The rank calculations following equation (1.5) are verified below.


## Rank calculations and periodic counts following equation (1.5)

The renewed comparison follows the deformation argument and its free
normalization. Finite-rank projections less than one apart in operator
norm have equal rank; connectedness transports the rank to zero. The
full free generalized eigenspace has exactly two signed modes. Central
counts use a sufficiently large comparison circle and exact spectral
selection, with every signed free index included in the parity count.
The resulting totals count algebraic multiplicity, including collisions.
The real-type argument uses conjugate frequency reflection and absolutely
convergent coefficient pairings on the full one-derivative domain. Positive
energy gives real eigenvalues, and compact-resolvent spectral equivalence
gives reality of the entire spectrum at every finite exponent. The
height-N result remains separate from the printed norm-dependent height.

Section3RankRealitySourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups,
25 reviewed module hashes and 36 resolved declaration references.
This comparison preserves the earlier qualifications and does not certify
every assertion in Section 3. Its Lean sources match the full validation
at `cb7317a`; this documentation update does not rerun Lean.

Printed page 27 obtains the central and distant-disk counts from contour
ranks, then gives parity, exhaustion, and reality conclusions. The actual
source integrals and typed restrictions now have those ranks at every
finite Banach exponent. The central region is the height-N box from
Corollary 3.5; the separate norm-dependent height qualification remains.

| Printed conclusion or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Conjugation preserves range dimensions | `NLS.ConjugatedRanges.rangeEquiv`, `rangeInfEquiv` | Linear equivalences for ranges and their intersections with corresponding subspaces; no isometry of the converted norms is asserted. |
| Exact typed restricted range | `sourceParityCompressionRangeEquiv` | Linear isometric equivalence within the original norm, from the typed range to the ambient range intersection. |
| Actual source rank transfer | `finrank_range_sourceResolventCircleIntegral`, `finrank_range_sourceCentralRectangleIntegral` | The actual normalized integrals have the same ranks as the established coefficient-space projectors on admissible contours. |
| Typed restriction rank transfer | `finrank_range_sourceParityCircleProjection`, `finrank_range_sourceParityCentralProjection` | Their ranks equal the appropriate coefficient-space range intersection dimensions. |
| Complete source counting data | `SourcePeriodicCountingData` | Full central rank 4N+2, high-disk rank two, central parity ranks 2N+2 and 2N, disk parity ranks two and zero. |
| Algebraic multiplicities | `SourcePeriodicCountingData.central_multiplicity`, `disk_multiplicity` | Uses the established coefficient-operator algebraic multiplicity definition after coefficient-preserving norm conversion. Totals count multiplicity, not distinct values. |
| Actual high-disk range parity | `SourcePeriodicCountingData.disk_range_parity` | Every vector in the actual source circle range has the parity of its signed disk index, for even-supported potentials. |
| Actual domain eigenvector parity | `SourcePeriodicCountingData.disk_eigenvector_parity` | The eigenvalue equation uses `sourceOperator` and `sourceDomainInclusion` on the original one-derivative domain. |
| Physical unit translation | `SourcePeriodicCountingData.disk_eigenvector_unit_translation` | Both continuous Fourier components satisfy translation by one with phase +1 for even n and -1 for odd n, including p=1. |
| Exhaustion and exterior analyticity | `SourcePeriodicCountingData.spectrum_subset`, `mem_spectrum_iff_central_or_disk`, `analyticOnNhd_exterior` | Every source spectral value belongs to the central cluster or exactly one high disk; the complement has the actual analytic source resolvent. |
| Real-type spectrum | `sourcePeriodicSpectrum_im_eq_zero_of_realType` | Every finite exponent, full period-two source spectrum; no even-support requirement. |
| Common period-two neighborhood | `exists_uniform_sourcePeriodicCountingData` | One positive cutoff and open convex connected original-norm neighborhood containing source and zero; all larger cutoffs, complete counting data, and analytic actual central/circle projectors. |
| Common period-one neighborhood | `exists_uniform_sourcePeriodOneCountingData` | All counts together with analytic typed parity restrictions, on one open convex connected neighborhood in period-one coordinates. |

The source entry points are in `NLS.ZakharovShabat`, in
`SourceContourRanks.lean` and `SourcePeriodicCounting.lean`. The generic
range equivalences are in `NLS/FunctionalAnalysis/ConjugatedRanges.lean`.
The data retain a positive cutoff; no rank formula is asserted for a
degenerate, inadmissible central rectangle. The parity formulas use integer
residues and therefore include negative disk indices.

Lemma 3.7 in the original source norms is verified below.


## Lemma 3.7: intrinsic traces and analytic symmetric eigenvalue functions

The renewed proof comparison tracks the actual operator through its
full-domain contour lift and restriction to the spectral range. The two
trace formulas use the original midpoint and half the squared gap; their
finite-dimensional proof permits repeated roots and nontrivial Jordan
blocks. The explicit transport QP+(1-Q)(1-P) identifies nearby ranges,
with analytic inverse and reduced operator, and intertwines the original
domain action. Each fixed contour has a local transport neighborhood.
This yields scalar analyticity throughout the common admissible
neighborhood without requiring one transport chart for infinitely many
contours at once.

Section3TraceSourceComparison-2026-10-27 in the
[source-review index](source-review-index.json) records four focused groups,
18 reviewed module hashes and 30 resolved declaration references.
This comparison preserves the earlier qualifications and does not certify
every assertion in Section 3. Its Lean sources match the full validation
at `cb7317a`; this documentation update does not rerun Lean.

The two printed functions are the midpoint and half the squared gap. They
are defined from traces of the actual source operator on the actual source
contour range. Every finite Banach exponent is included, and the formulas
remain valid at a double eigenvalue without diagonalizability assumptions.

| Printed conclusion or supporting identification | Public entry point | Verified scope |
| --- | --- | --- |
| Original-domain contour lift | `sourceContourLift`, `sourceResolventCircleIntegral_eq_sourceInclusion`, `sourceInclusion_contourLift_range` | Inclusion of the bounded domain lift equals the actual integral; a range vector lifts to that exact original-domain representative. |
| Actual intrinsic operator | `sourceContourOperator`, `sourceContourRestriction`, `sourceContourRestriction_apply` | The finite-dimensional endomorphism acts by the actual `sourceOperator` on the domain lift. |
| Conjugation and trace identification | `sourceContourRangeEquiv`, `sourceContourRestriction_conjugate`, `sourceContourTracePower_eq` | Proved linear conjugation and trace invariance; no isometry of the converted norms is asserted. |
| Intrinsic source definitions | `sourceContourTracePower`, `sourceContourMidpoint`, `sourceContourSquaredGap`, `sourcePeriodicMidpoint`, `sourcePeriodicSquaredGap` | Functions are defined by traces on the actual source range. The periodic functions use the quarter-pi disk at pi*n. |
| Centered-square formula | `sourceContour_centeredSquare_trace` | At rank two the centered second trace equals the squared gap divided by two, exactly as printed. |
| Identification with the eigenvalue pair | `sourceContourMidpoint_squaredGap_eq_pair`, `SourcePeriodicCountingData.midpoint_squaredGap_eq_pair` | Midpoint (a+b)/2, squared gap (a-b)^2, centered trace (a-b)^2/2, including a=b. |
| Local intrinsic analyticity | `analyticAt_sourceContourTracePower`, `analyticAt_sourceContourMidpoint_and_halfSquaredGap` | Original potential topology on every admissible circle. |
| Actual transport and range equivalence | `sourceContourTransport`, `sourceContourRangeTransport`, `sourceContourRangeTransport_apply` | The concrete range isomorphism is induced by invertible ambient projection transport. |
| Original-domain intertwining | `sourceInclusion_contourLift_transported`, `sourceContourTransport_reduced_apply` | The lift represents the transported vector and the reduction intertwines its actual original-domain operator action. |
| Local analytic reduction | `exists_local_sourceContourReduction` | One open neighborhood with analytic transport, inverse transport, and fixed-range operator, with admissible contours and isomorphic ranges. |
| Fixed-range trace formulas | `sourceContourTracePower_eq_reduced`, `sourceContourMidpoint_halfSquaredGap_eq_reduced` | All intrinsic power traces agree with the reduction; both displayed rank-two formulas retain the exact factor one half. |
| Full Lemma 3.7 package | `sourceLemma3_7` | One positive cutoff and open convex connected original-norm neighborhood containing source and zero; both printed analytic functions for every high index, actual counting data, pair identification, and algebraic multiplicities. |
| Printed period-one topology | `sourceLemma3_7_periodOne` | Both analytic functions on a common original-norm period-one parameter neighborhood. |
| Free-potential normalization | `sourcePeriodicMidpoint_squaredGap_zero` | Midpoint pi*n and squared gap zero for every integer n, including negative indices. |

The entry points lie in `NLS.ZakharovShabat`, in `SourceContourTrace.lean`,
`SourceContourReduction.lean`, and `SourceLemma3_7.lean`. The finite-dimensional
trace formulas concern the actual restriction of the original operator;
coefficient-space trace equality is proved afterward. The common neighborhood
includes p=1. Earlier qualifications, including the distinct norm-dependent
height issue, remain unchanged.

Section 4, equation (1.6) and the AKNS representation of the classical
Dirichlet/Neumann domains, are audited in [SECTION_4.md](SECTION_4.md).

## Infinitesimal relative bound in the opening paragraph

The unnumbered paragraph on p.23 states that potential multiplication has
arbitrarily small relative bound with respect to the free differential
operator. Closedness of the full operator already has a separate proof
through an actual bounded spectral inverse. The relative-bound assertion
now has a direct public statement as well.

[`SourcePotentialRelativeBound.lean`](../NLS/ZakharovShabat/SourcePotentialRelativeBound.lean)
proves that for every finite Banach exponent, every potential norm bound B,
and every epsilon>0, one positive constant C works for all original
period-two potentials of norm at most B and every original one-derivative
domain vector f:

    norm((L(phi)-L(0))f) <= epsilon*norm(L(0)f) + C*norm(f).

Both output norms and the base norm use the original component-sum
convention. The proof makes the potential composed with a sufficiently
high free resolvent small, then applies the actual free inverse identity
to the domain vector. Transport from the internal maximum norm retains
its exact factor 2^(1/p), absorbed by choosing the smaller relative
coefficient first. No finite-gap, real-type or even-support premise is
imposed.

A per-potential corollary gives relative bound zero. Taking epsilon=1/2
also gives both graph comparisons with coefficient two, uniformly on
bounded potential sets. This proof uses a resolvent argument. The analytic-decomposition assertion
in the same paragraph is formalized below.

Three public examples check an asymmetric pair of odd complex modes at
p=1, a uniform original-norm ball at p=3/2, and both graph directions at
p=4. The full repository verification results are recorded in the
implementation status.

## Analytic decomposition in the opening paragraph

The same paragraph on printed p.23 decomposes an arbitrary original
period-two potential into a real-analytic part and a remainder of
arbitrarily small norm. This assertion is now separately proved in
[`SourceAnalyticApproximation.lean`](../NLS/Fourier/SourceAnalyticApproximation.lean).

`exists_source_analytic_decomposition` gives finite coefficient data a
and an original source remainder r with phi=ofFinsupp(a)+r and norm(r)<epsilon.
It retains every finite Banach exponent, including p=1, and the original
component-sum norm. Both components of the approximant have explicit
entire Fourier-polynomial representatives. Their real restrictions are
real analytic and physically period two. Every signed normalized Fourier
integral is the corresponding coefficient of a, and integration against
every Schwartz test equals the actual synthesized distribution.

The proof uses the established density of finite Fourier pairs and
identifies their physical representatives with continuous synthesis.
There is no real-type, finite-gap or even-support restriction. No density
claim at the infinity endpoint is made.

Three public examples check the p=1 decomposition and its actual
distribution, two asymmetric odd Fourier modes, and entire approximation
at p=3/2. The relative-bound theorem above has an independent resolvent
proof; this step supplies the literal approximation used by the source.
