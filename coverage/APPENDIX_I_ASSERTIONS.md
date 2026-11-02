# Appendix I ordered assertion comparison

The eighteen ordered Appendix I groups comprise thirteen matched, three directly corrected and two contextual passages. No partial or pending group remains within this local comparison. The Schur equivalence assumes lower-block invertibility, and its expression has the signs Id+A-B(Id+D)^(-1)C. The lower block acts on the tail space Y. The exact weighted I.3 tails give quarter-to-half operator bounds, one cutoff near compact parameter sets and a common cutoff for the constructed complex germs of the real source atlas. The final relative density theorem uses local compact decompositions, local Schur determinants and analytic uniqueness on the nonnegative cone; one globally chosen holomorphic extension or pathwise determinant is not asserted. Actual real inverse maps and both inverse identities are retained. The precise 2014 reference comparison and broader dissertation completeness remain separate. Historical refutations are unchanged; no new refutations are added.

Source: printed pp.139–140, text lines 11429–11540. Line numbers count newline characters and preserve form feeds. The rendered pages were inspected.

| Group | Text lines | Source passage | Status |
| --- | --- | --- | --- |
| I-001 | 11431–11436 | The original Banach-space operator is represented in bounded direct-sum coordinates. | matched |
| I-002 | 11439–11444 | Assuming Id+D invertible, Id+T is invertible exactly when Id+A-B(Id+D)^(-1)C is invertible. | corrected |
| I-003 | 11446–11450 | For a finite-dimensional first block, det S nonzero and norm(D)<1 imply invertibility. | matched |
| I-004 | 11452–11453 | Compactness is equivalent to total boundedness and completeness. | contextual |
| I-005 | 11463–11464 | I.3 retains arbitrary sets, raw pointwise bounds, finite p>=1 and one symmetric tail cutoff for every positive error. | matched |
| I-006 | 11470–11479 | I.4 starts with a real-analytic cone map and compact complexified derivative minus identity at its source points. | matched |
| I-007 | 11481–11481 | One actual local real inverse provides the seed. | matched |
| I-008 | 11483–11483 | The set of local diffeomorphism points is relatively open and dense. | matched |
| I-009 | 11486–11493 | Compactness of the unit-ball image yields an operator-norm output tail at most one quarter. | matched |
| I-010 | 11495–11499 | Continuity improves the center quarter bound to a half bound on a complex neighborhood. | matched |
| I-011 | 11502–11509 | A common cutoff works along a compact path and on neighborhoods of its points. | matched |
| I-012 | 11512–11514 | The proof introduces finite-head and complementary-tail block coordinates. | contextual |
| I-013 | 11516–11518 | The lower block acts on the tail space Y and its norm is at most the full output-tail norm. | corrected |
| I-014 | 11522–11525 | A nonzero finite-dimensional Schur determinant detects invertibility of the derivative. | matched |
| I-015 | 11527–11530 | The Schur expression is Id+A-B(Id+D)^(-1)C. | corrected |
| I-016 | 11530–11532 | The corrected Schur complement and its finite determinant are analytic. | matched |
| I-017 | 11532–11534 | Analytic uniqueness propagates nonvanishing into every nonempty relatively open source set. | matched |
| I-018 | 11534–11535 | The derivative-invertible locus is open and dense and equals the real local-inverse locus. | matched |

## Compared passages

### I-001: The original Banach-space operator is represented in bounded direct-sum coordinates.

A bounded linear equivalence to the product identifies the original Id+T with its two-by-two block operator. The first block need not be finite dimensional at this stage.

Public declarations:

- `NLS.SchurComplement.block`
- `NLS.SchurComplement.block_apply`
- `NLS.SchurComplement.one_add_block`
- `NLS.SchurComplement.source_operator_isUnit_iff`

### I-002: Assuming Id+D invertible, Id+T is invertible exactly when Id+A-B(Id+D)^(-1)C is invertible.

Adopt lower-block invertibility as a premise of the equivalence. The sufficient direction retains the source hypotheses. Historical counterexamples remain unchanged; this comparison adds no refutation.

Public declarations:

- `NLS.SchurComplement.sourceSchur`
- `NLS.SchurComplement.sourceSchur_apply`
- `NLS.SchurComplement.sourceLemmaI1_corrected`
- `NLS.SchurComplement.sourceLemmaI1_sufficient`
- `NLS.SchurComplement.sourceLemmaI1_on_decomposition`

### I-003: For a finite-dimensional first block, det S nonzero and norm(D)<1 imply invertibility.

The strict norm bound gives invertibility of Id+D by the Neumann argument. Under that bound the determinant criterion is also necessary, in the original Banach-space coordinates.

Public declarations:

- `NLS.SchurComplement.source_lower_isUnit_of_norm_lt_one`
- `NLS.SchurComplement.sourceCorollaryI2_iff`
- `NLS.SchurComplement.sourceCorollaryI2`
- `NLS.SchurComplement.sourceCorollaryI2_on_decomposition`

### I-004: Compactness is equivalent to total boundedness and completeness.

This is the standard metric-space compactness criterion. In the complete coefficient spaces the specialized statements use closedness; they also characterize the compact closure of an arbitrary unweighted set.

Public declarations:

- `NLS.Coeff.sourceLemmaI3_compact`
- `NLS.Coeff.sourceLemmaI3_compactClosure`
- `NLS.WeightedCoeff.sourceLemmaI3_compact`

### I-005: I.3 retains arbitrary sets, raw pointwise bounds, finite p>=1 and one symmetric tail cutoff for every positive error.

The head is exactly |n|<=N, the tail |n|>N, and N>=1. Coefficient bounds may depend on n; no global norm bound is supplied. Every positive weight preserves the exact norm and raw coefficient interpretation.

Public declarations:

- `NLS.Coeff.sourceI3Projection`
- `NLS.Coeff.sourceI3Tail`
- `NLS.Coeff.sourceI3Tail_apply`
- `NLS.Coeff.sourceI3Tail_eq_fourierTail`
- `NLS.Coeff.sourceLemmaI3`
- `NLS.WeightedCoeff.sourceLemmaI3`
- `NLS.WeightedCoeff.norm_sourceI3Tail`

### I-006: I.4 starts with a real-analytic cone map and compact complexified derivative minus identity at its source points.

The domain is relatively open in the nonnegative cone. Local real analytic extensions define analyticity at its boundary. Their complex germs and derivative compatibility are constructed. Compactness is assumed only at cone points. Arbitrary positive weights cover every real Sobolev order.

Public declarations:

- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.toComplex`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.toComplex_restriction`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.toComplex_derivative`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.complexifiedDerivative_eq`

### I-007: One actual local real inverse provides the seed.

The seed is an inverse germ of the original real extension, with both inverse identities. The separately proved weaker seed is a differentiable real left inverse; it does not strengthen the printed hypotheses.

Public declarations:

- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.localInversePoints`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.toComplex_realLocalInversePoints`
- `NLS.WeightedCoeff.sourcePropositionI4_real_analytic_of_differentiable_seed`

### I-008: The set of local diffeomorphism points is relatively open and dense.

The theorem uses preconnectedness, which is weaker than path connectedness. It gives actual real analytic inverses on ambient real neighborhoods, both identities, and recovery of the original cone map near the center. The inverse locus is independent of the atlas.

Public declarations:

- `NLS.WeightedCoeff.sourcePropositionI4_real_analytic`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.exists_localInverse`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.localInversePoints_eq_of_atlas`

### I-009: Compactness of the unit-ball image yields an operator-norm output tail at most one quarter.

The weighted operator is the exact I.3 tail. All input columns remain present. The cutoff works for every larger N and for any positive error, including 1/4.

Public declarations:

- `NLS.Coeff.exists_sourceI3Tail_comp_norm_le`
- `NLS.Coeff.tendsto_sourceI3Tail_comp`
- `NLS.WeightedCoeff.appendixI_tailOperator`
- `NLS.WeightedCoeff.appendixI_tailOperator_apply`
- `NLS.WeightedCoeff.appendixI_compact_tail_cutoff`

### I-010: Continuity improves the center quarter bound to a half bound on a complex neighborhood.

The complex neighborhood belongs to the constructed local extension of the original real map. The norm is the original weighted operator norm. Compactness is not assumed on that ambient complex neighborhood.

Public declarations:

- `NLS.WeightedCoeff.appendixI_local_tail_cutoff`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.appendixI_local_derivative_cutoff`

### I-011: A common cutoff works along a compact path and on neighborhoods of its points.

The compact-family theorem gives one cutoff on an open neighborhood whenever a continuous ambient family is given. For the actual source atlas, one cutoff gives a relative quarter bound near any compact subset and a complex half-bound neighborhood for each of its germs. The final density proof uses these intrinsic local germs and local Schur determinants; it does not assert a single globally chosen holomorphic extension along the whole path.

Public declarations:

- `NLS.WeightedCoeff.appendixI_norm_tailOperator_comp_antitone`
- `NLS.WeightedCoeff.appendixI_compact_family_tail_cutoff`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.appendixI_compact_derivative_cutoff`

### I-012: The proof introduces finite-head and complementary-tail block coordinates.

The printed cutoff notation is compared with the exact symmetric projections. The canonical final Fredholm argument constructs a finite-dimensional invariant summand and a closed invertible complement at each point. This is an alternative local decomposition, not a claim that its summands equal the printed Fourier head and tail.

Public declarations:

- `NLS.Coeff.sourceI3Projection`
- `NLS.Coeff.sourceI3Tail`
- `NLS.SchurComplement.sourceLemmaI1_on_decomposition`
- `NLS.CompactSpectrum.exists_invertible_complement_compact_shift`

### I-013: The lower block acts on the tail space Y and its norm is at most the full output-tail norm.

Use L(Y_N), correcting the displayed L(X_N). The positive theorem constructs D on the actual range of the tail projection and proves the bound with constant one. Combining it with the half bound gives the strict premise of I.2.

Public declarations:

- `NLS.WeightedCoeff.appendixI_tail_block_norm`

### I-014: A nonzero finite-dimensional Schur determinant detects invertibility of the derivative.

The determinant is the actual determinant of the finite block. Lower-block invertibility is established before applying the criterion; no determinant of an infinite-dimensional operator is used.

Public declarations:

- `NLS.SchurComplement.sourceCorollaryI2_iff`
- `NLS.SchurComplement.isUnit_block_iff_det_ne_zero`
- `NLS.CompactSpectrum.exists_local_determinant_of_invertible_complement`

### I-015: The Schur expression is Id+A-B(Id+D)^(-1)C.

Adopt the signs from I.1 directly in the adjacent proof display. The analytic formula is composed from the same blocks and the inverse of the invertible lower block. No new false-positive example is proved.

Public declarations:

- `NLS.SchurComplement.sourceSchur`
- `NLS.SchurComplement.sourceSchur_apply`
- `NLS.SchurComplement.analyticAt_expression`

### I-016: The corrected Schur complement and its finite determinant are analytic.

Local analytic inversion gives the lower-block inverse near the center. Polynomial determinant composition gives a scalar analytic criterion. The final proof allows different local determinants at different centers.

Public declarations:

- `NLS.SchurComplement.analyticAt_expression`
- `NLS.SchurComplement.exists_local_analytic_determinant`
- `NLS.CompactSpectrum.exists_local_analytic_determinant`

### I-017: Analytic uniqueness propagates nonvanishing into every nonempty relatively open source set.

The cone need not have ambient interior. Agreement on its relatively open part determines the ambient analytic germ, including boundary points. A connectedness argument propagates local nonvanishing criteria without requiring one global determinant.

Public declarations:

- `NLS.ComplexAnalysis.subset_closure_of_local_analytic_nonvanishing`
- `NLS.Coeff.eventuallyEq_of_nonnegative_agreement`
- `NLS.Coeff.subset_closure_of_nonnegative_local_analytic_nonvanishing`
- `NLS.WeightedCoeff.eventuallyEq_of_nonnegative_restriction`

### I-018: The derivative-invertible locus is open and dense and equals the real local-inverse locus.

Openness follows from operator-norm continuity and openness of the units. Relative density follows from the local analytic criteria, and the real inverse theorem supplies both actual inverse identities. The conclusion includes cone boundary points.

Public declarations:

- `NLS.Coeff.open_dense_isUnit_of_nonnegative_analytic_compact_shift`
- `NLS.WeightedCoeff.open_dense_isUnit_of_nonnegative_analytic_compact_shift`
- `NLS.WeightedCoeff.NonnegativeAnalyticAtlas.localInversePoints_eq`
- `NLS.WeightedCoeff.sourcePropositionI4_real_analytic`
- `NLS.WeightedCoeff.NonnegativeRealAnalyticAtlas.exists_localInverse`

## Evidence and validation

The [weighted cutoff proofs](../NLS/SequenceSpaces/AppendixIUniformCutoff.lean) retain the exact tail, source norm and quarter-to-half bounds.
The [Schur criterion](../NLS/FunctionalAnalysis/SourceSchurComplement.lean) uses the corrected premise and signs.
The [weighted I.3 criterion](../NLS/SequenceSpaces/WeightedSourceLemmaI3.lean) retains raw coefficient bounds and the original norm.
The [real source theorem](../NLS/SequenceSpaces/SourcePropositionI4RealAnalytic.lean) gives actual local inverses on the nonnegative cone.
The [local determinant construction](../NLS/FunctionalAnalysis/CompactAnalyticDeterminant.lean) and
[relative analytic uniqueness](../NLS/SequenceSpaces/NonnegativeAnalyticDensity.lean) supply the alternative local proof.

The comparison records 26 complete module bodies and 58 declaration references, reconciling the earlier source comparison and the weighted-cutoff proof publication.
It does not claim a fresh review of every transitive proof. The previous named reviews retain their historical scope.

The unchanged Lean snapshot reuses the successful full check at commit 7f0cc3a7d585a7296d162abe47eb178b80afc596: 8,646 build jobs, 7,729 public examples and an axiom audit of 45,015 NLS declarations. The check has 21 inherited warnings and no new warnings. All 58 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: reconcile the whole-dissertation ledger. The [broader completion qualifications](COMPLETENESS.md) remain.
