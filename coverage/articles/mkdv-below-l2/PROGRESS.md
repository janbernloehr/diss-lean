# Progress on 2026-11-02

Main Theorems 1.1–1.3 remain unverified. This commit adds actual proved
supporting constructions, not conditional main-theorem wrappers.

## Physical Birkhoff adapter — Theorem 1.2 dependencies

`PhysicalBirkhoff.lean` defines the input as pairs of original period-one
Fourier–Lebesgue distributions. `physicalCoefficients_apply` proves exactly
which physical test mode is evaluated. Transport through the existing
spectral construction and the established rectangular-to-complex linear
change gives a holomorphic map on an open physical domain, and
`physicalBirkhoff_action` proves its coordinate product equals the actual
spectral action of the transported potential.

On the physical NLS real form, `physicalRealCoefficients` is a homeomorphism
to the established real source. The real rectangular Birkhoff map is an
open embedding with dense image, and is onto at p=2 (indeed at all 1<p≤2).
Its complex output is a same-index conjugate pair. Both complex analyticity
and real geometry have existence theorems constructing their source data.

Still required for the full article theorem: one compatible family across
exponents on complex domains, a Banach real-analytic physical-input
interface, canonical bracket transport, exact accepted Hilbert-map
identification, and all normalization identifications. The physical mKdV
real diagonal is smaller than this NLS real form. Its reflection symmetry
and hierarchy restriction remain assigned to the hierarchy task.

## H₄ candidate convergence — Theorem 1.3 dependencies

`FourthMomentSummability.lean` constructs the moment atlas and a connected
open neighborhood of the whole real source on which every weighted row
∑ k |k Ω⁽²⁾ₙₖ| converges, for 1<p≤3. In particular, it includes the p=2
base case needed by the article. The proof uses the existing refined
moment factorization, cubic gap summability (with norm bound ||γ³||₁≤||γ||ₚ³),
and the estimate |k/(n-k)|≤|n|+1 for k≠n. It handles the diagonal separately
without dividing by n, and works at collapsed gaps.

`exists_fourthFrequencyCandidate` constructs the candidate -12∑k kΩ⁽²⁾ₙₖ
and proves a HasSum statement without assuming moment convergence or a
moment atlas from the caller. `fourthFrequencyCandidate_eq_of_coefficients`
proves cross-exponent agreement from the established physical coefficient
compatibility of the moments.

Still required: local uniform convergence, analyticity of the weighted
sum, the ℓ^(-1,r)/ℓ^(-1,p/2) sequence-map bounds, and the refined remainder
ω*ₙ+12πnIₙ. The currently reused off-diagonal coefficient estimate lies in
ℓ^(p/2)+ℓ^(1+); the article's Lemma 5.3 has the sharper ℓ^(1+) row needed
for its all-finite-p weighted sum argument. The present p≤3 proof does not
supply that sharper estimate. Physical identification with the H₄ action
Hamiltonian derivative is also outstanding; the symbol “candidate” is
intentional.

## Validation and checkout

The four proof modules passed direct Lean 4.33.1 checks without diagnostics.
All 30 new declarations passed a transitive axiom audit permitting only
propext, Classical.choice and Quot.sound. There are no new axioms, sorry
proofs or disabled linters. The reproducible focused check script is
`check.sh`; `validation.txt` records the output.

The ordinary Git worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-mkdv-below-l2/work/checkouts/mkdv-below-l2`,
on branch `articles/mkdv-below-l2`. The app's managed creation tool rejected
the unregistered canonical source folder, so the approved ordinary Git
worktree fallback was used. Commands explicitly target this path. The
canonical main checkout and its build products were not edited. All compiler
outputs remain separate; no full build or aggregate NLS import was added.
