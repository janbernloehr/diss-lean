# Appendix I: a generic local diffeomorphism property

## Ordered source comparison

The [ordered Appendix I comparison](APPENDIX_I_ASSERTIONS.md) covers 18 groups on pp.139–140: thirteen matched, three directly corrected and two contextual. No partial or pending groups remain in this local ledger.

The Schur equivalence assumes lower-block invertibility and uses Id+A-B(Id+D)^(-1)C. The lower block acts on the tail space Y. The exact weighted I.3 tail gives the quarter bound at each compact source and the half bound on a neighborhood, with one cutoff along compact source sets.

The real-analytic source atlas constructs the complex germs and identifies their derivatives. Relative openness and density follow from local Schur determinants and analytic uniqueness on the nonnegative cone. The original weighted norms and actual real inverse maps with both inverse identities are retained. One global holomorphic extension is not assumed.

This documentation step adds no Lean proof or refutation.

The unchanged Lean snapshot reuses the successful full check at commit 7f0cc3a7d585a7296d162abe47eb178b80afc596: 8,646 build jobs, 7,729 public examples and an axiom audit of 45,015 NLS declarations. The check has 21 inherited warnings and no new warnings. All 58 declaration references, source and module hashes, the review index and local documentation links are checked again. These checks do not certify complete formalization of the dissertation.

Next: reconcile the whole-dissertation ledger. The [broader completion qualifications](COMPLETENESS.md), including the precise 2014 construction comparison, remain.

Earlier entries retain their historical scope; the adopted corrections above govern this comparison.

## Appendix I weighted uniform cutoffs

The [weighted uniform cutoff proofs](../NLS/SequenceSpaces/AppendixIUniformCutoff.lean) use the exact tail |n|>N in the original weighted norm. Compactness gives a quarter bound at a source point, and continuity gives a half bound on a neighborhood, with the same cutoff valid for every larger N.

One cutoff works near a compact parameter set. For the actual real-analytic source atlas it gives a relative quarter bound and an ambient complex half-bound neighborhood for every germ along that set. The complex germs and their derivatives come from the existing real-atlas construction. Compactness is assumed only at the source points.

The lower block acts on the tail space Y_N and has norm at most the full output tail, with constant one. This adopts the corrected space in the proof display directly.

Eight positive theorems and one bounded tail-operator definition add no new examples or refutations.

The full check passed: 8,646 build jobs, 7,729 public examples and an axiom audit of 45,015 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

Publish the reviewed eighteen-group ordered Appendix I comparison, retaining the corrected Schur premise, signs and lower-block space, and the local analytic proof on the original nonnegative cone. Then reconcile the whole-dissertation ledger and its remaining qualifications.
The [broader completion qualifications](COMPLETENESS.md) remain.

## Previous source review

The following records retain their historical scope; the adopted corrections above govern the current proof step.

This compares printed pages 139–140 with the canonical Lean statements.
I.2–I.4 are implemented in the scopes below. The unrestricted equivalence
in I.1 is false; its corrected form and a counterexample are formalized.
The real-analytic interpretation in I.4 is made explicit at cone points.

| Source assertion | Public entry points | Verified scope |
| --- | --- | --- |
| Corrected I.1 | `sourceLemmaI1_corrected`, `sourceLemmaI1_on_decomposition` | Assuming Id+D invertible, Id+T is invertible exactly when Id+A-B(Id+D)^(-1)C is invertible. The result transfers to the original Banach space through its bounded direct-sum coordinates. |
| Printed I.1 obstruction | `sourceLemmaI1_printed_false` | Coordinate exchange on C² gives invertible Id+T with singular Id+D. |
| I.2 | `sourceCorollaryI2`, `sourceCorollaryI2_on_decomposition` | A finite-dimensional first block, nonzero Schur determinant, and the strict norm bound norm(D)<1 imply invertibility. Under that norm bound, the determinant criterion is also necessary. |
| I.3 | `Coeff.sourceLemmaI3` | Total boundedness is equivalent to pointwise boundedness and uniformly small symmetric tails for arbitrary subsets and every finite p>=1. The cutoff satisfies N>=1. |
| Weighted I.3 | `WeightedCoeff.sourceLemmaI3` | The same criterion in every positive weighted space, with raw coefficient bounds and the exact weighted tail norm. |
| I.4 | `WeightedCoeff.sourcePropositionI4_real_analytic` | On a relatively open, preconnected domain in the nonnegative cone, compactness of the complexified real derivative minus identity at cone points and one local inverse imply a relatively open dense local-inverse locus. |
| Weaker seed for I.4 | `sourcePropositionI4_real_analytic_of_differentiable_seed` | A differentiable real left inverse at one point suffices. The conclusion gives analytic local inverse germs. |
| Literal inverse maps | `NonnegativeRealAnalyticAtlas.exists_localInverse` | Analytic real inverse, both inverse identities on ambient real neighborhoods, and recovery of the original cone map near its center. |

The Schur results and counterexamples are in
[`SourceSchurComplement.lean`](../NLS/FunctionalAnalysis/SourceSchurComplement.lean)
and [`SourceLemmaI1Audit.lean`](../NLS/FunctionalAnalysis/SourceLemmaI1Audit.lean).
The tail criteria are in
[`SourceLemmaI3.lean`](../NLS/SequenceSpaces/SourceLemmaI3.lean)
and [`WeightedSourceLemmaI3.lean`](../NLS/SequenceSpaces/WeightedSourceLemmaI3.lean).
The real-analytic interface and final result are in
[`WeightedRealAnalyticAtlas.lean`](../NLS/SequenceSpaces/WeightedRealAnalyticAtlas.lean)
and [`SourcePropositionI4RealAnalytic.lean`](../NLS/SequenceSpaces/SourcePropositionI4RealAnalytic.lean).

## Exact hypotheses and topology

I.3 keeps precisely the head |n|<=N and the complementary tail |n|>N.
It assumes pointwise boundedness, not a supplied global norm bound.
Closedness adds the compactness criterion, while the unweighted result
also states compactness of the closure. All finite Banach exponents,
including p=1, are covered.

In I.4, analyticity on the cone means local extension to the ambient
real weighted Banach space. `NonnegativeRealAnalyticAtlas` records those
real germs and agreement with the cone map. Their holomorphic
extensions are constructed from real power series; compatibility of
the complex derivative with the original real derivative is proved.
No single global holomorphic extension is assumed.

The derivative-minus-identity compactness assumption is required only
at points of the cone domain. Preconnectedness is weaker than the
printed path-connectedness hypothesis. Openness and density use the
relative cone topology, so points with zero coordinates are included.
The inverse locus and complexified derivative do not depend on the
chosen atlas. Arbitrary positive weights include every real Sobolev
order in the source statement.

## Corrections and boundary cases

I.1 cannot infer invertibility of the lower diagonal block from that of
the full operator. Its sufficient direction remains valid, and I.2's
strict norm bound supplies the missing lower-block invertibility.
The norm-one counterexample in `sourceCorollaryI2_boundary_counterexample`
shows why that strict bound cannot be replaced by a non-strict one;
it does not refute I.2 as printed.

The Schur expression in I.4's proof has reversed A and BC signs.
The implementation consistently uses Id+A-B(Id+D)^(-1)C from the
correct Schur complement. These source issues are recorded in
[source discrepancies](../SOURCE_ERRATA.md).

## Verification evidence

Existing examples check the two-dimensional swap counterexample, the
strict-norm boundary, p=1 and weighted tail criteria, and the failure
of uniform tails for moving coordinate unit vectors. I.4 checks use
real inverse germs, a differentiable seed, arbitrary weights, and an
explicit real quadratic example. Current full-build and transitive
axiom-audit totals are recorded in [status](../STATUS.md).
