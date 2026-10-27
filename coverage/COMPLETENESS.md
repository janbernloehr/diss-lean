# Current completion assessment

The dissertation formalization is not yet certified complete. The public
source-comparison snapshot contains comparisons for every named heading
in its reviewed heading index, along with selected unnumbered definitions,
displays and proof assertions. That is useful evidence, but does not prove
that every substantive unnumbered assertion has been assessed.

This assessment preserves the original objective: work through the whole
dissertation, retaining its mathematical objects, norms, domains and
quantifiers, and commit and push each validated step. A formally refuted
printed assertion must remain identified as such, alongside any proved
correction. It cannot be counted as a proof of the literal printed claim.

| Requirement | Current evidence | Remaining work |
| --- | --- | --- |
| Named mathematical statements | [Source comparisons](source-review-index.json), linked section and appendix audits, and current public Lean proofs; 161 named comparisons retain their qualifications. | Preserve exact scope and corrections in the overall assessment; the count is not a completion percentage. |
| Unnumbered definitions, equations and substantive assertions | Selected source ranges have explicit comparisons, including the introductory energy, spectral outline and mixed-frequency estimate. | Build and inspect a source-wide assertion inventory. Matching ranges or headings alone does not certify their contents. |
| Original objects and quantifiers | The focused audits record physical operators, original distributions, full multiplicities, actual integrals, norms and common-neighborhood quantifiers. | Reconcile each remaining assertion against these specific interfaces, rather than infer agreement from similar names. |
| Literal source discrepancies | [Source discrepancies](../SOURCE_ERRATA.md) separates refutations, proved corrections and qualified interpretations. The auxiliary-height history now reflects the proved p=2 case and unrestricted counterexample. | Retain all distinctions; do not silently replace an unresolved interpretation with a candidate correction. |
| The cited 2014 Birkhoff construction | [Section 14](SECTION_14.md) records the inspected 2013 manuscript and independently proved physical coordinate formulas. | The exact construction in the cited 2014 edition still needs comparison. The different edition and public contents are insufficient evidence. |
| Appendix G.2 interval norm | [Appendix G](APPENDIX_G.md) records the proved unit-interval result, a formal counterexample for the usual local integral norm, and an arbitrary-time correction candidate. | The source's intended arbitrary-time norm remains unspecified; the candidate correction has not been adopted as that interpretation. |
| Lean validation and publication | [Current status](../STATUS.md) records the build, all public examples, transitive axiom audit and documentation checks for each milestone. | Every implementation change must pass its required checks and be committed and pushed. Passing checks does not establish source completeness. |

## How the next assessment proceeds

Both abstracts now have a [consolidated mathematical comparison](INTRODUCTION.md)
covering their seven paired claim groups. It retains the exact exponent and
gap restrictions, renormalization, solution sense and norms, together with
the unresolved external-construction qualification. Novelty and historical
priority are outside that assessment. The introduction now also has a
37-group ordered assertion inventory, preserving its four refuted formulas
and all earlier scope qualifications. The [complete spectral overview](SPECTRAL_OVERVIEW.md)
now has 27 ordered groups, preserving both unrestricted height refutations
and the complex finite-gap regularity correction. The complete Section 2
text has been reconciled with its existing twelve-group comparison and
three corrections. Section 3 now also has two endpoint-inequality corrections
in Lemma 3.2's proof and formal refutations of two radius-dependent
intermediate estimates in Lemma 3.4's proof. The main Lemma 3.4 remains
proved. Direct original-norm setup proofs now also cover closedness,
equation (1.3), the first resolvent identity, height decay and the square
estimate, with both signed coefficient formulas. Literal denominator geometry,
absolute double-sum majorization for the actual components, the near/far
partition and the cutoff-retaining Fourier-tail identity are also proved.
The literal Hölder displays, exact scalar norm factorization and explicit
p=1 near/far radius bounds are now proved as well.
The literal Lemma 3.2 scalar Hölder formulas, centered denominator geometry,
punctured-series bound, height moment chain and strip moment are also proved.
Lemma 3.2(i)'s signed Fourier expansion, explicit finite-rank cutoffs,
rank bound and original-norm closure argument are also proved.
The direct Corollary 3.3 composition bound, actual Neumann inverse and
series, and compactness inference are now proved in the original norm;
the standalone pair-norm counterexample remains valid.
Corollary 3.5's squared inverse, original-norm quarter/half bounds, compact
segment and common neighborhood for all larger exact spectral exteriors
are also proved, with the compact analytic resolvent and spectrum enclosure.
Four focused proof groups now also compare the actual Cauchy–Riesz
projections, parity decomposition, full-domain invariance and analytic
period-one restrictions in equations (1.4)–(1.5) and Lemma 3.6.
Four further groups compare the deformation to free contour ranks,
algebraic and parity counts, spectral exhaustion and real-type symmetry
on the full domain. The central height-N conclusion retains the separate
qualification on the printed norm-dependent height.
Lemma 3.7 and its intrinsic trace formulas, actual domain lifts, local
analytic range transport and scalar analyticity now have four focused
proof comparisons, including repeated roots and the exact factor one half.
Eight further Section 3 passage groups now reconcile the opening operator
setup, compact-resolvent discreteness, exact sufficient regions, quantified
Lemma 3.4 and endpoint modifications, retaining all formal refutations.
Relative boundedness and closedness use alternative proofs of the source
assertions; the cited external perturbation argument is not independently audited.
The complete Section 3 text now has a 38-group ordered assertion inventory,
checked against all five rendered pages. It preserves six formally refuted
printed bounds, valid clauses and corrections, explicit interpretations,
and contextual citations. Each group links its exact prior proof evidence.
Section 4 now also has literal sine/cosine Fourier-series proofs for
Lemma 4.2, exact AKNS coefficient formulas, and continuous equivalences
onto both full classical boundary domains via the established physical
restriction maps. Its scalar restriction statements retain their separate
comparison scope.
Continue through Section 4, then later sections in source order.
Classify each substantive
claim as proved with exact scope, formally refuted with a separately stated
correction, contextual or outside-work attribution, or unresolved. Each
classification needs the source location and its actual proof evidence.
A range inventory is navigation for this review, not a semantic validator.
Previous selected comparisons can be reused with their stated scope and
verified module hashes; they must not be relabeled as exhaustive reviews.

The exact 2014 identification and G.2 interpretation remain open throughout
that work. Existing unchanged questions and unavailable-source attempts
need not be repeated without new information.

## Declaration reference clarification

A preparatory inventory matched every recorded declaration reference to
an actual imported NLS declaration. Two short suffixes had multiple matches:

- In Appendix F, `NLS.ZakharovShabat.sourceLemmaF2` constructs the common
  domain. `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.sourceLemmaF2`
  is the separately cited family-level boundary theorem.
- In Section 2, `NLS.WeightedCoeffPair.sobolevSesquilinearPairing_physical`
  handles the finite pair spaces, while
  `NLS.WeightedCoeffPairInfty.sobolevSesquilinearPairing_physical` handles
  the distinct infinity-pair norm. The reversed endpoint uses
  `NLS.WeightedCoeffPair.sobolevSesquilinearOneInfinity_physical`.

This resolves reference ambiguity only. It does not replace inspection of
the mathematical statements or certify the source comparison by name.
