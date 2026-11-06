# dNLS Fourier estimates: verification milestones

The required scope was expanded on 2026-11-06 to every mathematical assertion
in the paper. **Full-paper verification is in progress**, tracked in
[FULL_PAPER.md](FULL_PAPER.md) and `full-paper-claims.json`. The main-theorem
result below is a completed milestone and does not complete the expanded task.

Theorems 1–3 and introductory Corollary 1 of arXiv:1403.1369v2 are verified
under the accepted Birkhoff-map reference and the conventions below. Each
source statement was compared individually with its existing spectral proof.
`NLS/Articles/DNLSEstimates/MainEstimates.lean` records the article interfaces,
constructs the common family from proved data, and adds normalization lemmas.
The module is imported by the aggregate `NLS` library.

## Pinned source

- [Article abstract](https://arxiv.org/abs/1403.1369v2) and
  [versioned PDF](https://arxiv.org/pdf/1403.1369v2), 38 pages.
- Retrieved 2026-11-02; SHA-256
  `6862e6c30dffaa55f4a73b48155576310682c78e154ffcc1dbeeaf3eb0dd277b`.
- The actual served binary carries the v2 banner dated 6 October 2015 and a
  June 1, 2021 footer. The digest pins the binary used, independently of that footer.
- Printed and PDF page numbers agree here. Pages 3 and 4 were rendered and
  visually inspected; in particular, the endpoint is **at least one**.
- PDF, extracted text, rendered pages and scratch files remain in the originating chat's
  private `work/sources/` and are excluded from the integration patch.

## Exact source correspondence

Write P_k for the physical source norm, Q_k for its original Birkhoff image
norm, and M_k for the action moment with weight (1+|2nπ|)^(2k).

| Source | Exact estimate | Existing proof / article interface |
| --- | --- | --- |
| Theorem 1, p. 3 | Q_m ≤ c(P_m+(1+P_1)^(2m)P_0); P_m ≤ d(Q_m+(1+Q_1)^(4m−3)Q_0). | `SourceSection23SobolevBounds.birkhoff_upper` and `.birkhoff_lower`; `theorems_one_two`. |
| Theorem 2 and remark, p. 3 | M_m ≤ c²(P_m²+(1+P_1)^(4m)P_0²); P_m² ≤ d²(M_m+(1+M_1)^(4m−3)M_0). **The same positive c,d** work in both theorems. | The same bounds object's `.action_upper`, `.action_lower`, `.action_summable`; `theorems_one_two`. |
| Theorem 3, p. 4 | Σ w(2n)²\|I_n\| ≤ c_w² w[16P_w²]² P_w² on a complex weighted neighborhood; Q_w ≤ c_w w[16P_w²]P_w on the real weighted space. | `section23_weighted_neighborhood`; `theorem_three`, with c_w=2048. |
| Corollary 1, p. 4 | M_r ≤ c_r²(1+P_r)^(4r)P_r² on a complex H^r neighborhood; Q_r ≤ c_r(1+P_r)^(2r)P_r on the real space. | `section23_realSobolev_neighborhood`; `corollary_one`, with c_r=2048(1+17π)^r. |

Theorem 1 and 2 hold for every integer m≥1. Corollary 1 holds for every
real r≥1, including r=1. The exponents `4*m-3` are natural subtraction,
which agrees with the printed exponent when m≥1. Constants are chosen
before the potential. The constructor `exists_main_estimate_family`
chooses one original family before every order and weight; the interfaces'
family hypotheses are therefore discharged by an existing construction.

Theorem 3 quantifies over **all** weights in M¹, including exponential ones.
`SpectralWeight` has exactly the lower-bound, symmetry, submultiplicativity
and monotonicity conditions. It does not impose w(0)=1. `HasLinearFactor`
records the literal factorization w(n)=(1+|n|)v(n) with v in M.
`realExtension` is the required piecewise linear interpolation.

The weighted and real-order neighborhoods are open in normalized weighted
Hilbert coordinates. Their decoders divide coefficient n by w(2n), so
`norm(a)` is the physical weighted norm, as proved by
`normalizedWeightedSource_physical_norm`. This is the **weighted norm
topology**, not the ambient unweighted topology. Each neighborhood contains
the entire real subspace and decodes into the retained original complex
domain. No action estimate on complex inputs is replaced by a real-only one.
Target membership is constructive: `m1Coordinates` and
`realSobolevCoordinates` are actual Hilbert sequence pairs.

## Normalizations and new proof consequences

The physical circle has period one; its Zakharov–Shabat periodic boundary
problem uses [0,2]. The input and target use component-sum Hilbert norms.
The paper writes the first component with the negative Fourier exponential,
whereas the library synthesizes both components with the positive one.
The theorem `paper_weighted_source_norm_sq` proves that reflecting
the first index preserves the exact energy for every even spectral weight.
Thus this convention change does not alter any norm in the estimates.

The action is I_n=(x_n²+y_n²)/2, not the full rectangular radius squared.
The theorem `actionMoment_eq_half_birkhoff_norm_sq` checks that M_k=Q_k²/2;
`actionMoment_zero` checks M_0=P_0²/2. `actionMoment_summable` supplies actual
convergence at every lower order k≤m, so the total sums used in the estimates
are not merely Lean's default value for a nonsummable series.

Physical source identification is already supplied by
`SourcePhysicalL2Equiv`, and identification of original coordinate families
with the intrinsic physical map is supplied by
`PhysicalBirkhoffIntrinsicProperties`. The accepted manuscript conventions
in `coverage/ACCEPTED_REFERENCE.md` remain the reference for that existing
construction; no edition-identity requirement is reopened.

## Validation

`validation.json` records the module and aggregate compilations, the public
examples, the focused article audit, and the whole imported NLS axiom audit.
The dedicated reproducible audit source is `scripts/CheckDNLSEstimates.lean`;
its complete output is retained in `axiom-audit.log`. Every article declaration
and the original existence constructor permit only `propext`,
`Classical.choice`, and `Quot.sound` transitively. No new axioms, admitted
proofs or disabled linters were introduced. The article module imports a
specific NLS module and does not import the aggregate `NLS` module.

The source baseline is `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. No generic
analysis or equation-specific source changed. The new module and aggregate
were compiled directly with the pinned Lean executable against the unchanged
compiled dependency snapshot; public examples and both audits then ran on
that new aggregate. This validation does not claim a fresh recompilation of
every unchanged dependency. Expensive validations held the shared
`/tmp/diss-lean-article-build.lock`. All new build outputs are isolated in the
article worktree; the canonical `.lake` tree was read only.

The article is implemented on `articles/dnls-estimates`. Integration into
`main` remains a separate sequential repository operation. No essential
mathematical hypotheses remain unproved in this main-statement interface.
The dissertation verification record is unchanged.
