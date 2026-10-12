# Section 3: periodic spectrum

This audit covers the operator setup, Proposition 3.1, Lemma 3.2, and
Corollary 3.3 on printed pages 23–24. It retains the original period-two
space, its finite-exponent component-sum norm, and the conditional
period-one parity clauses. It is
not a completeness certificate for Section 3 or the dissertation.

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

Next: Lemma 3.4, auditing the sandwich-resolvent estimate in the original
p-to-one pair norms and tracking its component constants.
