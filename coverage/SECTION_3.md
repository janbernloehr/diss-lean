# Section 3: periodic spectrum

This audit covers the operator setup, Proposition 3.1, Lemmas 3.2 and
3.4, Corollaries 3.3 and 3.5, and equation (1.4) on printed pages 23–26.
It retains the original period-two space, its finite-exponent component-sum norm, and the
conditional period-one parity clauses. It is not a completeness certificate
for Section 3 or the dissertation.

## Operator setup

`Operator.lean` defines the full one-derivative coefficient domain and the
Zakharov–Shabat operator for every finite Banach exponent.
`domainInclusion_denseRange` proves density, and
`NLS.ZakharovShabat.unboundedOperator_isClosed` in `ClosedOperator.lean`
proves closedness without
restricting the potential size. Both components use scalar Fourier modes;
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

Next: Lemma 3.7 in the original source norms.
