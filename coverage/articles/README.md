# Article verification and shared proofs

The seven articles listed on the [author's publications page](https://janbernloehr.de/academia/publications)
are separate verification tasks in this repository. The completion criterion
for each article is initially its main theorems, with their precise domains,
normalizations and quantifiers. On 2026-11-06 the user expanded the
`dnls-estimates` task to every mathematical assertion in its pinned paper,
including intermediate results, proof steps, unnumbered claims and appendices.
Its broader task remains incomplete until the full-paper coverage ledger is closed. A coverage report or a conditional theorem whose essential
mathematical hypotheses remain unproved is not completion.

The dissertation's main theorems have a separate, completed
[verification record](../MAIN_THEOREMS.md). None of the article tasks is
automatically verified by that result. Each must identify its own theorem
statements and demonstrate the exact reuse or prove what is missing.

## One repository and one library

Keep the existing repository, pinned Lean/mathlib versions and `NLS` library.
Reuse generic results from `NLS/SequenceSpaces`, `NLS/Fourier`,
`NLS/ComplexAnalysis`, `NLS/FunctionalAnalysis`, `NLS/Poisson`,
`NLS/Dynamics` and `NLS/DifferentialPolynomial` directly. The current namespace
does not require the reused mathematics to be specific to NLS.

Keep existing imports stable. Add Hill/KdV-specific developments under
`NLS/KdV` and mKdV-specific developments under `NLS/MKdV`. Put article-facing
theorem statements and identifications in `NLS/Articles/<Article>/`, and
source inventories, verification records and progress in
`coverage/articles/<slug>/`. Existing dNLS proofs stay in place.

The intended dependency direction is generic analysis, then equation-specific
spectral and Hamiltonian theory, then article interfaces. Import specific
modules; importing the aggregate `NLS` from a module later imported by
`NLS.lean` would create a cycle. Generalize a theorem when an actual second
consumer requires it, preserving the existing specialization. Avoid copying
proofs or reorganizing thousands of established modules as a preliminary step.

## Tasks and initial reuse map

Each task begins by pinning its source PDF and reading its main statements.
Entries explicitly marked verified link their source-to-theorem comparison
and validation record. The remaining entries are initial reuse hypotheses
based on the abstracts and existing library.

| Article task | Source | Initial reuse and responsibility |
| --- | --- | --- |
| `dnls-estimates` — New estimates of the nonlinear Fourier transform for the defocusing NLS equation | [arXiv:1403.1369v2](https://arxiv.org/abs/1403.1369v2) | **Full-paper verification in progress.** Theorems 1–3 and Corollary 1 remain verified; the expanded scope includes all intermediate statements and appendices. [Full-paper ledger](dnls-estimates/FULL_PAPER.md) and [main-theorem milestone](dnls-estimates/README.md). Own `NLS/Articles/DNLSEstimates/`. |
| `kdv-estimates` — On two-sided estimates for the nonlinear Fourier transform of KdV | [arXiv:1502.04550v1](https://arxiv.org/abs/1502.04550v1) | Reuse sequence, analytic and tame-estimate infrastructure. Lead the shared `NLS/KdV` Hill operator, spectral labels and Birkhoff foundation needed by the other KdV articles. Own `NLS/Articles/KdVEstimates/`. |
| `kdv-convexity` — On the convexity of the KdV Hamiltonian | [arXiv:1502.05857v1](https://arxiv.org/abs/1502.05857v1) | Reuse generic action-space, analytic inverse and concavity arguments. Consume the shared KdV foundation; own KdV action-Hamiltonian and convexity developments and `NLS/Articles/KdVConvexity/`. KdV-specific conclusions do not follow merely from analogous dNLS theorems. |
| `mkdv-nls-hierarchies` — The mKdV and NLS hierarchies revisited | [arXiv:1601.07580v1](https://arxiv.org/abs/1601.07580v1) | Reuse the existing Riccati, differential-polynomial, Sobolev Hamiltonian and hierarchy trace modules. Lead `NLS/MKdV` hierarchy restrictions and the NLS-to-mKdV identification. Own `NLS/Articles/MKdVNLSHierarchies/`. |
| `kdv-kdv2-frequencies` — On the wellposedness of the KdV/KdV2 equations and their frequency maps | [arXiv:1605.06690v1](https://arxiv.org/abs/1605.06690v1) | The linked preprint is titled "On the extension of the frequency maps of the KdV and the KdV2 equations". Reuse generic frequency-extension and flow arguments, consume the KdV and action-Hamiltonian foundations, and own `NLS/Articles/KdVKdV2Frequencies/`. |
| `mkdv-below-l2` — On the wellposedness of the defocusing mKdV equation below L2 | [arXiv:1606.07052v1](https://arxiv.org/abs/1606.07052v1) | Consume the hierarchy restriction; reuse Fourier-Lebesgue, frequency and solution machinery where their hypotheses match. Own mKdV frequency/flow development and `NLS/Articles/MKdVBelowL2/`. |
| `kdv-pseudomeasures` — On the wellposedness of the KdV equation on the space of pseudomeasures | [arXiv:1610.00278v1](https://arxiv.org/abs/1610.00278v1) | Consume the KdV foundation. Own weak-star and pseudomeasure/Wiener endpoint results and `NLS/Articles/KdVPseudomeasures/`. Preserve the paper's weak-star topology; finite-exponent norm-topology theorems do not establish this endpoint. |

The linked preprints are the initial accessible sources. Record their version,
SHA-256, theorem labels and pages. If comparing a journal formulation, record
any change in statement separately. A filename or matching title does not
establish mathematical equivalence between formulations.

## Cooperation and integration

Each article uses its own branch and checkout. Keep article-specific edits in
its assigned directories. Before adding shared results, search this repository
and the other article branches. Shared-foundation owners should publish small,
validated commits early, with stable declarations and explicit remaining
requirements. Consumers can read those branches and reuse the same commits;
avoid independent competing implementations of the Hill operator or hierarchy.

Commit and push validated steps to the article branch. Do not push concurrent
article work directly to `main`, force-push, or rewrite another task's branch.
Integration into `main` should be sequential: shared dependencies first, then
their consumers. Resolve aggregate imports and validation records on the
combined state. Do not overwrite the dissertation's recorded validation with
counts from a partial article build.

Other article branches can be inspected with Git. Separate chat messages
require the user's authorization; do not assume a repository coordination
rule authorizes sending messages between chats.

## Validation and working files

Preserve the existing no-`sorry`, no-new-axioms policy. Prove corrected
constants directly; do not spend extra effort producing refutations merely
to justify a correction. Keep the mathematical input, norm, regularity and
quantifier order visible in each article's main statements.

Use focused module checks while developing, then the appropriate build,
examples and transitive axiom audit before publishing a verified milestone.
All new declarations should remain under `NLS` so the existing axiom audit
covers them once imported. Main-theorem reports must distinguish imported
proved facts, newly proved facts, and outstanding dependencies.

Reuse the pinned toolchain and dependency cache. Keep each checkout's mutable
`.lake/build` separate; do not point several writing builds at the same build
directory. Avoid blindly duplicating the entire existing build cache into
every checkout. Serialize expensive full builds with a common build lock
when several article chats are active; source reading and proof design can
proceed concurrently. Keep downloaded PDFs, extracted text and scratch checks
outside tracked source files unless their publication is explicitly needed.
