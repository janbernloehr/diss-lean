# Section 3: periodic spectrum

This audit starts with the operator setup and Proposition 3.1 on printed
page 23. It retains the original period-two space, its finite-exponent
component-sum norm, and the conditional period-one parity clauses. It is
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

Next: Lemma 3.2, including its exact operator norms in the original source
pair spaces. Existing maximum-product estimates alone do not certify
those numerical source bounds.
