# Full-paper verification: in progress

The user expanded this task on 2026-11-06 from the main theorems to **every
mathematical assertion of the pinned paper**, including intermediate lemmas,
unnumbered statements, proof passages and Appendices A and B. The earlier
main-theorem milestone remains valid, but **the expanded task is incomplete**.

The source is the 38-page arXiv:1403.1369v2 PDF, SHA-256
`6862e6c30dffaa55f4a73b48155576310682c78e154ffcc1dbeeaf3eb0dd277b`.
[full-paper-claims.json](full-paper-claims.json) records all 27 named results
and 350 mechanical paragraph blocks before the references, with source line
spans and text hashes. These blocks have not all been decomposed and reviewed
as individual assertions. The ledger also records 82 explicitly compared
auxiliary groups from the setup, Sections 3–6 and both appendices, with direct corrections
and exact shared declarations. These groups are not asserted to exhaust their
source spans. A checked theorem does not automatically certify
every displayed intermediate claim in its printed proof.

## Checked statement milestone

The table describes statement-level correspondence. It is not a claim that
the associated proof passages or the whole paper are fully covered. There are
24 checked named statements (including the four earlier main statements) and
three checked corrected statements. Each keeps its explicit qualification.
Full declaration names and exact qualifications are in the JSON ledger.

| Statement | PDF page | Current statement coverage | Article declarations |
| --- | --- | --- | --- |
| Theorem 1 | 3 | Main milestone checked | `theorems_one_two` |
| Theorem 2 | 3 | Main milestone checked | `theorems_one_two` |
| Theorem 3 | 4 | Main milestone checked | `theorem_three` |
| Corollary 1 | 4 | Main milestone checked | `corollary_one` |
| Theorem 4 | 10 | Statement checked | `theorem_four`, `exists_theorem_four_domain` |
| Lemma 2 | 10 | Statement checked | `lemma_two_domain`, `lemma_two_joint` |
| Lemma 3 | 12 | Statement checked | `proposition_twenty`, `lemma_three_spectral` |
| Lemma 4 | 14 | Checked with explicit nonsmooth spectral extension | `exists_complex_finiteGap_extended_hamiltonian_domain`, `finiteGapArticleHamiltonian_eq_hierarchy` |
| Theorem 5 | 15 | Statement checked | `theorem_five`, `theorem_five_spectrum` |
| Lemma 5 | 16 | Statement checked | `lemma_five` |
| Lemma 6 | 17 | Statement checked | `lemma_six` |
| Lemma 7 | 18 | Statement checked | `lemma_seven` |
| Lemma 8 | 19 | Statement checked | `lemma_eight` |
| Lemma 9 | 20 | Statement checked | `lemma_nine` |
| Lemma 10 | 20 | Statement checked | `lemma_ten` |
| Proposition 11 | 22 | Statement checked | `proposition_eleven_tail`, `proposition_eleven_global` |
| Proposition 12 | 23 | Statement checked | `proposition_twelve_mean_value`, `proposition_twelve_exterior` |
| Lemma 13 | 23 | Statement checked | `lemma_thirteen` |
| Lemma 14 | 24 | Statement checked | `lemma_fourteen` |
| Lemma 15 | 26 | Statement checked | `lemma_fifteen` |
| Lemma 16 | 27 | Statement checked | `lemma_sixteen` |
| Lemma 17 | 29 | Corrected statement checked | `lemma_seventeen`, `lemma_seventeen_ratio` |
| Proposition 18 | 30 | Corrected statement checked | `proposition_eighteen`, `complex_action_domain` |
| Lemma 19 | 32 | Statement checked | `lemma_nineteen` |
| Proposition 20 | 33 | Statement checked | `proposition_twenty`, `primitive_domain` |
| Lemma 21 | 35 | Statement checked | `lemma_twenty_one_polynomial`, `lemma_twenty_one_evaluation` |
| Corollary 22 | 36 | Statement checked | `corollary_twenty_two`, `corollary_twenty_two_integral` |

All declarations are under `NLS.Articles.DNLSEstimates`. Their family and
domain hypotheses are discharged by existing constructions: the common
complex domains are chosen before potentials, indices, orders and weights.
The original spectral actions and the independently defined physical Riccati
Hamiltonians are retained. Convergence is explicit in trace and weighted-sum
statements; no result relies on a default value of a divergent Lean sum.

## New mathematical work

Sixteen modules extend the original [MainEstimates](../../../NLS/Articles/DNLSEstimates/MainEstimates.lean)
interface:

- [HigherActions](../../../NLS/Articles/DNLSEstimates/HigherActions.lean):
  the original higher actions, complex analyticity, collapsed-gap implication,
  real positivity and valid odd-level zero detection, actual gap mean-value
  point, all-order trace and all three conclusions of Lemma 15.
- [SpectralEstimates](../../../NLS/Articles/DNLSEstimates/SpectralEstimates.lean):
  Theorem 5, Lemmas 5–10 and Proposition 11 with the original endpoint labels,
  physical norms, shifted operator norms, full strips and root multiplicities.
- [ActionEstimates](../../../NLS/Articles/DNLSEstimates/ActionEstimates.lean):
  Proposition 12 and Lemma 13, including the nonzero exterior condition and
  the strict central condition.
- [Hierarchy](../../../NLS/Articles/DNLSEstimates/Hierarchy.lean):
  Lemma 14, Lemma 21 and Corollary 22. Lemma 21 includes the actual weak H^-1
  identity on complex H^(k-1); Corollary 22 includes the highest weak derivative
  in one physical integral on all real H^m inputs. Lemma 14 retains precisely
  the factor `1+L^(4*m)`, with one constant for its two estimates. One graded polynomial is
  selected before every source.
- [ConverseEstimate](../../../NLS/Articles/DNLSEstimates/ConverseEstimate.lean):
  a new proof of the exact Lemma 16 with remainder
  `(64*pi)^(2*m)*(1+M_0)^(2*m-1)*M_1^(2*m-1)`. At index zero and physical H¹
  norm P<=1/4, the entire gap lies in [-1/2,1/2] and the first action dominates.
  Otherwise the central third-action comparison uses the quadratic factor
  P² without an added one. Summation and Lemma 15 then preserve the paper's
  separate mass and weighted-moment exponents.
- [Primitive](../../../NLS/Articles/DNLSEstimates/Primitive.lean):
  Lemma 2, Lemma 19 and Proposition 20, plus the filled spectral domain,
  simultaneous continuous endpoint extension, signed arcosh limits, the principal-logarithm formula near every point of the closed gap and
  exact zero-potential value from Lemma 3.
  Discreteness of the actual spectrum controls approach through other endpoints.
- [ComplexActions](../../../NLS/Articles/DNLSEstimates/ComplexActions.lean):
  corrected complex versions of Lemma 17 and Proposition 18, the positive
  intermediate ratio, filled normalized-action bounds, local ℓ² asymptotics,
  uniform H¹-ball bounds and weighted action-sum continuity.
- [FiniteGap](../../../NLS/Articles/DNLSEstimates/FiniteGap.lean):
  the real finite-gap part of Lemma 4, coefficient conversion to the article's
  raw hierarchy convention and the cubic asymptotic used in Lemma 15.
  The real-type premise is visible; it does not establish the printed
  all-complex finite-gap statement.

- [ComplexFiniteGap](../../../NLS/Articles/DNLSEstimates/ComplexFiniteGap.lean):
  a direct complex proof of exterior analyticity and a convergent normalized
  Laurent expansion. Collapsed factors cancel before taking the finite product.
  The closed-circle integral eliminates a logarithmic term, and actual collapsed
  tail endpoint values fix the additive constant. Matching Fourier coefficients
  identify every coefficient with the physical Riccati Hamiltonians at smooth
  complex sources. The common neighborhoods and complex discriminant identity
  are constructed. The nonsmooth extension is supplied separately below.
- [SpectralCurve](../../../NLS/Articles/DNLSEstimates/SpectralCurve.lean):
  the actual affine curve in C², analytic local uniformizers at unramified and
  simple branch points, two branches with distinct tangents at double spectral
  points, the actual ambient Jacobian, and nonsingularity exactly when the
  entire periodic spectrum is simple. The simple-spectrum curve has infinitely
  many distinct regular branch points.
- [SpectralSurface](../../../NLS/Articles/DNLSEstimates/SpectralSurface.lean):
  an actual Mathlib `ChartedSpace` and complex analytic `IsManifold` of dimension
  one, on the original subspace topology, for simple periodic spectrum. The
  proof constructs open charts, both inverse identities, continuity and analytic
  transitions. Surjectivity of the spectral projection proves noncompactness.
  Connectedness and the converse at nodes are supplied below; infinite genus
  remains unproved.

- [NonsmoothHamiltonians](../../../NLS/Articles/DNLSEstimates/NonsmoothHamiltonians.lean):
  an explicit all-order spectral extension at rough complex finite-gap sources,
  defined by finite traces of the original higher action contours, independently
  of Laurent coefficients. Finite-hole contour decomposition and exterior Cauchy
  coefficients prove the actual convergent series. The extension agrees exactly
  with the independently defined physical Riccati Hamiltonians on every admissible
  complex Sobolev domain. The article phase, positive H1, exceptional first minus
  sign and powers of 2i are checked. At rough inputs this is a spectral extension;
  it does not assign classical derivatives or assert uniqueness of arbitrary extensions.
  Odd-order agreement is also proved on the sharp complex H^m domain.
- [SpectralConnectedness](../../../NLS/Articles/DNLSEstimates/SpectralConnectedness.lean):
  the actual projection is continuous, open and proper. Every nonempty clopen part
  projects onto C, and the singleton fiber above a zero proves connectedness.
  This applies to all affine spectral curves, including nodal curves.
- [SpectralNodes](../../../NLS/Articles/DNLSEstimates/SpectralNodes.lean):
  a punctured complex disc is connected, but the two punctured local branches at
  a node have opposite continuous discrete labels. Both occur in every neighborhood,
  ruling out any topological complex chart there. On the paper's isolating domains,
  existence of a complex analytic surface structure in the inherited topology is
  equivalent to simplicity of the full periodic spectrum.
- [RootDomains](../../../NLS/Articles/DNLSEstimates/RootDomains.lean):
  closing the original isolating discs preserves disjointness, separation and the
  exact free tail. The canonical root is spectrally analytic on the complement of
  only the noncollapsed cuts at each complex source. The literal joint complement
  of the fixed closed discs uses the same constructed local neighborhoods.

- [Gevrey](../../../NLS/Articles/DNLSEstimates/Gevrey.lean):
  the actual classical derivative-growth meaning of the Fourier weights. Stretched
  exponential decay gives a smooth periodic representative with bounds
  `C*R^k*(k!)^(1/sigma)`; optimizing the integer derivative order gives a positive
  Fourier decay radius conversely. The union over positive radii is exactly the
  classical Gevrey class with any fixed polynomial Sobolev factor. The paper's
  even-frequency weight and physical 2pi derivative convention are explicit.

These reuse established equation-specific and generic proofs. The zero-mode
repair in `ConverseEstimate`, simultaneous endpoint continuity, complex finite-gap
inversion and the spectral-curve geometry are new proofs in the article layer. No existing generic analysis
module or dissertation verification record has been changed.

## Corrections and source qualifications

- Page 5's introductory trace sum is printed over n>=1; use all n in Z, as
  in Theorem 4 and the original action trace. The rendered page was inspected.
- For the Abel weight sampled at w(2n), the exact physical strip width is
  a/pi with Sobolev boundary traces. The printed a/(2*pi) strip is retained
  as a forward implication. Its full equivalence requires this width correction.
- Formula (1), p. 9, omits the square on `(tau_n-lambda)` in the standard-root
  radicand denominator. Use `4*(tau_n-lambda)^2`. This was confirmed in the
  rendered PDF. The normalized-root definition and its squared endpoint-factor identity
  supply the checked correction.
- The unrestricted higher-level zero-detection converse on p. 9 is qualified:
  collapsed complex gaps give zero at every level; the converse is retained
  for real sources at every odd printed level.
- Appendix B's `u_1=-phi_plus` and raw integral would give negative H1, contrary
  to the positive mass in Section 2. Use positive H1 and keep the actual raw
  Riccati means at higher orders. The library phase and the printed
  `(-1)^(m+1)` odd-Hamiltonian sign are converted explicitly, with smooth
  physical-integral agreement proved independently of actions.
- Lemma 16's printed central argument needs the small zero-index case above.
  The exact final statement is proved with its original constant and exponents.
- Lemma 17 uses chi constant 2048 in place of 512; Proposition 18 uses 4608
  in place of 2048. The replacement rational bound is
  `128*(abs(n)+N+2/5)/(abs(n)-N+3/10)` and includes the boundary cutoff.
  The source remains complex H¹ on a constructed neighborhood of the real locus.

- At nonsmooth complex finite-gap inputs in Lemma 4, use the explicit spectral
  extension from finite traces of the original higher action contours. Every
  Laurent coefficient is identified, and agreement with the independently defined
  physical hierarchy is proved throughout its complex Sobolev domains. Classical
  derivative products at rough inputs and finite-gap-implies-smoothness are not claimed.

- The unreduced display before Corollary 22 needs the factor `(-1)^(m+1)`
  on its remainder integral when `q_(2m)` keeps the definition from Lemma 21.
  The positive physical identity and article phase conversion supply this correction.
  Corollary 22's final reduced polynomial absorbs the phase and is unchanged.

Existing physical norm and Fourier conventions from the
[main milestone](README.md) remain in force. Any narrower source domain or
changed constant must remain explicit. No new refutations were added.

## Outstanding work

1. **Spectral-curve infinite genus on p. 9:** prove genuine infinite topological
   genus of the simple-spectrum surface. Connectedness, noncompactness, the actual
   complex manifold and its converse on the isolating domains, and infinite regular
   ramification are checked. Counting branch points is not a proof of genus.
2. **Unnumbered setup and background:** finish the assertion-by-assertion review
   of the remaining setup text. The classical Gevrey characterization, physical Poisson
   gradients, the NLS energy variations and scalar real-form restriction now have
   explicit comparisons with their actual domains. Closed-disc isolation and filled
   complex spectral-root analyticity are checked. The compared groups do not exhaust
   every setup paragraph.
3. **All proof passages:** finish the assertion-by-assertion semantic inventory.
   The JSON retains pending blocks explicitly, including proof-only inequalities
   that need not follow from a different proof of the named result.

## Validation and publication

The 2026-11-07 validation passed all seventeen final article module compilations
and the final aggregate with zero warnings. Both final transitive audits passed:
278 article declarations and 45,524 imported NLS declarations.
All 259 exact shared declaration references and all 350 source-block hashes
passed integrity checks. The ledger contains 82 compared auxiliary groups;
292 paragraph blocks remain pending semantic review.

All 7,729 existing public examples passed on the initial sixteen-module
aggregate. The independent Gevrey module and three additional compatibility
theorems were added afterward; they change no existing declaration, instance,
simp attribute or example source. All final modules and the aggregate were then
compiled again and both transitive audits rerun. This records one public-example
run, with its original source hashes preserved, and does not claim a second
example run on the final aggregate. These checks do not certify complete source
coverage. The validation record explicitly says `full_paper_complete: false`.

The new record is [full-paper-validation.json](full-paper-validation.json),
with separate expanded [article](full-paper-axiom-audit.log) and
[whole-NLS](full-paper-full-axiom-audit.log) audit logs. The historical
[main-theorem validation](validation.json) and its counts remain unchanged.
The current source imports all seventeen article modules in `NLS.lean` and in
`scripts/CheckDNLSEstimates.lean`.

Validation compiles the article modules and aggregate with pinned Lean 4.33.1
and `autoImplicit=false`, runs the existing public examples, and audits all
transitive axiom dependencies. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted; neither `sorryAx` nor any new project axiom is
allowed. This run imports the unchanged compiled dependency snapshot and does
not claim a fresh rebuild of every dependency. Mutable outputs are confined
to the separate article worktree. The shared validation lock serializes the
expensive checks.

Validated work is published on `articles/dnls-estimates`. The original
main-theorem PR #2 was merged; this expansion is later work. Full-paper
completion may only be reported after all outstanding obligations are closed.
