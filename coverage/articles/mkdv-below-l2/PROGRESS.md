# Progress on 2026-11-02

The first checkpoint below left all main theorems open. The third checkpoint
implements Theorem 1.2; Theorems 1.1 and 1.3 remain open. Validation status is
recorded in the current README and theorem-1.2.json.

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


## Third checkpoint — Theorem 1.2 and consumed physical fourth-flow bridge

Theorem 1.2 now has direct article statements in `Theorem12.lean`:
`theorem1_2_at_exponent`, `theorem1_2_compatible`, `theorem1_2_hilbert` and
`theorem1_2_hilbert_globalInverse`. The fixed family is constructed from
original spectral charts, then pulled back to original period-one
distributions. Domain shrinking to real-centered ball cores makes the
cross-exponent compatibility true on full complex intersections. The real
source and conjugate-pair target have explicit complete real Banach structures.
The statement includes actual analytic local inverse maps and a global
bi-real-analytic Hilbert inverse for the same family.

The canonical clause is proved on the entire complex domain by analytic
continuation of the verified real canonical identities. Full coordinate
differentials have regular Hilbert Fourier witnesses. The complex mixed
bracket is exactly -i delta; `physicalFLBracket_eq_integral_bracket` proves
that the physical Fourier bracket is the existing integral bracket in the
Hilbert case. `compatibleBirkhoff_eq_intrinsic` identifies the p=2 family
member with the accepted intrinsic action-angle map.
`physicalHilbertRealization_coefficients` verifies each input distribution's
actual unit-period Fourier coefficients in that comparison.

Reusable scalar restriction, complex coordinate inclusion, conjugate-pair
coordinates, canonical cotangent algebra and real-core uniqueness proofs
live in FunctionalAnalysis, Dynamics, Poisson and ZakharovShabat modules.
They are imported by the article rather than redefined inside a main theorem.

The shared hierarchy commits `9b664f9` and `09fa657` were merged intact,
preserving their ownership and proof provenance. The new
`ClassicalRenormalizedFourthFlow.lean` consumes their physical Hamiltonian
first-variation/field construction. Subtracting the common 6M translation
generator yields exactly the smooth renormalized mKdV velocity, while
retaining the physical Gardner energy-gradient identity. This does not
identify the low-regularity sequence flow with physical solutions.

Theorems 1.1 and 1.3 remain open. The H₄ candidate still has only the earlier
1<p≤3 absolute-convergence proof; its physical frequency identification,
all-finite-p estimates and analytic sequence bounds remain outstanding.
Theorem 1.1 additionally needs the diagonal Birkhoff invariance,
smooth-approximation identification, and fixed-time nonextension proof.

Strict validation for the third checkpoint passed: all 22 modules compiled with
warnings treated as errors, and all 120 audited declarations used only the
three permitted standard axioms. Theorem 1.2 is marked verified under the
accepted manuscript reference in `theorem-1.2.json`; Theorems 1.1 and 1.3 are
explicitly unverified. `validation.json` stores every audited declaration.
