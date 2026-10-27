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

The strict-concavity clauses of both abstracts now have an explicit
[comparison and Jensen interface](INTRODUCTION.md). Continue with their
remaining claims, then read the introduction and remaining source assertions
in order. The frequency clauses now also have an explicit normalization
comparison and an ordinary action-frequency nonextension theorem there.
These selected comparisons do not complete the abstract assessment.
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
