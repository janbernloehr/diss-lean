# Section 19: the original abelian integral

This audit covers the definition and assertions on printed pp. 87–91.
For every finite 1<p<∞, `sourceSection19_original` constructs an original
Section 17 Birkhoff family and `SourceSection19Data` on an open connected
source neighborhood U inside that family's original complex domain V.
The entire real-source locus lies in U. An already chosen original family
can be retained using `D.exists_section19`.

The primitive throughout is `sourceFullAbelianPrimitive hp hp1 W n` of the
actual canonical discriminant and canonical root. The local Cauchy families,
joint differential, endpoint integrals, and gap bounds belong to the same
ambient neighborhood W and source domain U. The construction transfers the
joint differential by proved neighborhood independence of the canonical
primitive; it does not assume agreement between independently chosen models.

## Assertion map

Here Q denotes `SourceSection19Data`, C a local Cauchy family from
`Q.local_models`, and M its `SourceAbelianMixedGapData`.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Definition of Fₙ, p. 87 | `Q.endpoint_integrals` | Either original improper endpoint integral and their average equal the same normalized primitive |
| Admissible-path independence | `Q.endpointPath_integral`, `Q.endpointPiecewisePath_integral` | Actual truncated integrals converge with independent endpoint parameters; every interior C¹ path and finite piecewise interior C¹ path with admissible corners has the same improper value |
| Lemma 19.1(i), joint analyticity and gradient | `Q.analytic`, `Q.differential`, `Q.source_derivative` | Open moving-cut joint domain; the source differential is the actual discriminant cotangent divided by the canonical root |
| Lemma 19.1(i), spectral analyticity | `Q.spectral_analytic` | Complement of noncollapsed gaps, with every collapsed gap filled |
| Lemma 19.1(ii), normalization | `Q.index_shift` | Fₙ=F₀+inπ on the complement of noncollapsed gaps |
| Lemma 19.1(ii), endpoint extension | `Q.endpoint_limit`, `Q.endpointExtension_eqOn`, `Q.endpointExtension_value` | One extension agrees with the filled primitive and has value iπ(n−j) at either endpoint of gap j, continuously relative to the spectral domain with that endpoint adjoined |
| Lemma 19.1(iii) | `Q.uniform_gap_bounds`, `M.uniform_boundary_sup` | Locally uniform bounded literal supremum over both sides of the whole closed gap; bound B‖γₙ‖ for every index, with no tail cutoff |
| Lemma 19.1(iv) | `Q.square_analytic` | Fₙ² analytic off all noncollapsed gaps; its analytic continuation also fills the selected gap |
| Lemma 19.1(v) | `Q.real_gap_boundary` | Exact signed arcosh profile on every real closed gap, for arbitrary approach from either open half-plane |
| Lemma 19.1(vi) | `Q.zero` | Exact free formula Fₙ(λ,0)=−iλ+inπ=i wₙ(λ,0) |
| Lemma 19.2 | `Q.laurent` | Convergent Laurent series with the actual physical Hamiltonians for every real finite-gap source, at every finite p>1 |
| Corollary 19.3 | `Q.cube_asymptotic`, `Q.cube_isBigO` | Exact cubic Laurent part, exterior analyticity, quantitative O(|λ|⁻²) bound in all complex directions, and the literal big-O statement |
| Lemma 19.4 | `M.bounded`, `M.mixed_displacement` | Literal two-sided error supremum γₙ(gₙ+hₙ), with one locally bounded ℓ^(p/2)+ℓ^(1+) decomposition chosen before every auxiliary exponent |
| Collapsed and zero-potential clauses | `C.gapErrorSup_eq_zero_of_collapsed`, `Q.zero` | Exactly zero error on collapsed gaps and the exact free primitive identity |

## Actual improper integrals

[`SourceAbelianAdmissibleIntegrals.lean`](../NLS/ZakharovShabat/SourceAbelianAdmissibleIntegrals.lean)
integrates the actual differential Δ′/√ᶜ(Δ²−4). The primitive derivative
and endpoint limits give convergence as the two truncation parameters tend
independently to zero and one. Finite piecewise paths use the values at their
vertices and a telescoping sum. No separate absolute-integrability or
path-independence hypothesis is supplied. Path interiors and intermediate
corners must avoid every cut; the initial spectral endpoint is allowed.

The chosen endpoint integral and its two-endpoint average are identified
with these values using the existing
[`SourceAbelianEndpointIntegrals.lean`](../NLS/ZakharovShabat/SourceAbelianEndpointIntegrals.lean).
The new statements allow arbitrary admissible interior C¹ paths, including
ones whose derivatives need not extend continuously to their endpoints.

## Literal suprema and quantifiers

[`SourceAbelianGapSupremum.lean`](../NLS/ZakharovShabat/SourceAbelianGapSupremum.lean)
defines `C.gapErrorSup` as the real supremum of the magnitudes of Fₙ−i wₙ,
using the cosine parametrization of the entire closed gap and both side
choices. Existing side-limit theorems identify these profiles with the
actual canonical primitive and root. The cosine parametrization covers
the whole segment. For collapsed gaps the filled primitive and error are
exactly zero.

The range is proved nonempty and bounded above, so the real `sSup` is not
being used with an unbounded set. The first factorization uses ‖γₙ‖. A
bounded phase multiplier then gives the literal complex γₙ factorization,
preserving the locally uniform sequence bounds. At γₙ=0 the supremum
vanishes, so no nonzero-gap assumption is hidden in this conversion.

Both sequence-valued functions g and h are chosen before the auxiliary
exponent q. The first belongs to ℓ^(p/2), including its quasi-normed range
when 1<p<2. The second is one sequence in every finite ℓ^q for q>1;
each projection has a uniform bound on the same neighborhood. The bounds
also imply the literal supremum estimate of Lemma 19.1(iii) for all indices.
No analyticity of these chosen bounding sequences is asserted.

## One domain and the physical Laurent coefficients

[`SourceSection19Domain.lean`](../NLS/ZakharovShabat/SourceSection19Domain.lean)
constructs the common domain inside any given open neighborhood of the
whole real locus. Taking the component of zero after intersecting the
local-model and differential domains preserves every real source, because
the real locus is connected. Every complex source in U has a local family
on W with the same mixed estimates.

[`SourceSection19Primitive.lean`](../NLS/ZakharovShabat/SourceSection19Primitive.lean)
collects Lemma 19.1 and the original path integrals on that domain. The
endpoint extension is a single relative-limit function fixed before the
endpoint index is selected. Its continuity theorem explicitly states the
domain with the selected endpoint adjoined. The printed Lemma 19.1(iv)
requires only analyticity away from all gaps; the selected-gap square
continuation is stronger than that printed assertion.

[`SourceSection19Laurent.lean`](../NLS/ZakharovShabat/SourceSection19Laurent.lean)
retains the actual physical Hamiltonians of the smooth representative
constructed for every real finite-gap source. It assumes neither that
representative nor a discriminant-identification formula. For each source,
one exterior radius works for all normalization indices; the shifted cube
also has one quantitative remainder constant for all indices. The result
is exterior analyticity and a Laurent expansion at infinity, not global
meromorphic continuation across open gaps.

[`SourceSection19Original.lean`](../NLS/ZakharovShabat/SourceSection19Original.lean)
attaches this package to the original Birkhoff family, retaining its
original map while restricting the source neighborhood inside its domain.

## Validation and next work

This step adds six modules and 29 public examples, including the literal
joint derivative, independently truncated paths with corners, endpoint
normalization, both side limits, the two suprema, physical Laurent
coefficients, and p=3/2 with a quasi-normed p/2=3/4 component. Gate results
are recorded in [the implementation status](../STATUS.md).

The original Section 20 frequency and contour-moment package now retains
this primitive; see [the Section 20 audit](SECTION_20.md) for its exact
scope and remaining work.
Section 14's external Hilbert-map identification and full fractional
smoothness qualifications remain. The dissertation is incomplete.
