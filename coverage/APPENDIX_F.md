# Appendix F: analyticity of the primitive

## Positive path, branch and quantitative proofs

The [boundary integral identities](../NLS/ZakharovShabat/AppendixFBoundaryIntegral.lean)
retain actual endpoint and connecting integrals, the full shared-path
coefficient, and the exact four-path decomposition. One source ball
works for all signed indices and boundary pairs.

The [local endpoint branches](../NLS/ZakharovShabat/AppendixFOpenGapBranches.lean)
cover complex noncollapsed gaps with their actual unordered pair and
any prescribed positive tolerance. No continuous endpoint labels
are required. The [straight-spoke geometry](../NLS/ComplexAnalysis/AppendixFSpokeGeometry.lean)
keeps explicit quarter-gap and quarter-spoke tolerances. The segment
stays in the closed isolating disc and avoids the selected gap except
at its starting endpoint.

The [scalar estimates](../NLS/ComplexAnalysis/AppendixFProofEstimates.lean)
retain the half-gap remainder constant and positive base radicand.
The [short-piece bound](../NLS/ZakharovShabat/AppendixFShortPiece.lean)
is pi*M times the gap norm and gives vanishing at collapse, with
the common regular-factor bound M stated explicitly. The
[independent uniform bound](../NLS/ZakharovShabat/AppendixFUniformShortPiece.lean)
derives one local constant from compactness of the fixed inner disc
and the joint Cauchy quotient, with no extra regular-factor hypothesis.
It holds at every complex point of the source ball, for all angles
and both sides, and gives vanishing as gap norms tend to zero.

The [positive moving majorant](../NLS/ComplexAnalysis/AppendixFPositiveMajorant.lean)
uses the absolute lower distance. It bounds every complex square-root
branch off the moving singleton, is integrable on the whole unit
interval, and has L1 error at most 4*sqrt(2e), tending to zero.

Seven modules add twenty-five positive theorems and four examples.
No new refutation is added.

The full check passed: 8,601 build jobs, 7,718 public examples and an axiom audit of 44,835 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The 31-group ordered Appendix F comparison remains open, including
the common-neighborhood spoke construction and source-path limit details. The
[broader completion qualifications](COMPLETENESS.md) remain.

This compares printed pages 131–134 with the canonical Lean statements.
F.1–F.3 have implementations for every finite exponent p>1, including
complex collapsed gaps. The two corrections below concern F.2's proof;
its analyticity conclusion is proved unchanged.

| Source assertion | Public entry points | Verified scope |
| --- | --- | --- |
| F.1(i) | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_i` | At every complex collapsed gap in the constructed domain, an open source neighborhood has the printed half-gap bound. |
| F.1(ii) | `SourceCriticalGapAnalyticDomain.sourceLemmaF1_ii` | At every real source, one complex neighborhood has the printed constant-one bound for every signed index, including collapsed finite-head gaps. |
| Common F.1 domain | `sourceLemmaF1` | Both assertions hold on one connected open domain containing the real source locus. |
| Actual primitive | `sourceAbelianDifferential`, `sourceAbelianEndpointIntegral`, `sourceAbelianEndpointAverage` | The canonical discriminant differential, actual improper endpoint integrals, and their literal half-sum. |
| F.2 | `SourceFullAbelianUniformCauchyFamily.sourceLemmaF2`, `sourceLemmaF2` | At every complex point of one connected almost-real domain, a common source neighborhood works for every gap and every point of its isolating boundary. |
| Endpoint identification | `endpointIntegral_eq`, `endpointAverage_eq`, `endpointCurveIntegral_eq` | The improper integrals equal the constructed primitive and every integrable admissible C1 path integral. The endpoint approach filters are nontrivial. |
| F.3 | `sourceCorollaryF3`, `endpointToEndpointIntegral_eq` | For either endpoint in gap n and either endpoint in gap m, the double improper integral is i*pi*(n-m), hence analytic. Pointwise endpoint choices need no continuity. |
| Admissible endpoint paths | `endpointToEndpointCurveIntegral_eq` | Every integrable C1 path with interior in the canonical root domain agrees with the improper definition. |

The main statements are in
[`SourceLemmaF1.lean`](../NLS/ZakharovShabat/SourceLemmaF1.lean),
[`SourceLemmaF2.lean`](../NLS/ZakharovShabat/SourceLemmaF2.lean), and
[`SourceCorollaryF3.lean`](../NLS/ZakharovShabat/SourceCorollaryF3.lean).
The underlying integral definitions and their primitive identification are in
[`SourceAbelianEndpointIntegrals.lean`](../NLS/ZakharovShabat/SourceAbelianEndpointIntegrals.lean).

## Domain and endpoint details

The domain in the source is an almost-real neighborhood chosen during
the construction. The formal statements construct such a domain; they
do not claim analyticity on every possible larger complex potential
domain. F.1's domain can be chosen inside a prescribed open set
containing the real locus.

The endpoint integrals are relative limits of actual finite polygonal
curve integrals. F.3 takes a second endpoint limit. Convergence,
nontrivial approach filters, and equality with conventional admissible
paths are proved. This avoids substituting an arbitrary endpoint value
for the singular differential. Lexicographic endpoint labels need not
be continuous, and neither theorem assumes the selected gap is open.

## Corrections inside F.2's proof

In the displayed formula (F.3), the shared path integral must retain
coefficient 1/i=-i. Averaging the two endpoint integrals halves their
short endpoint pieces but retains their shared path in full. The
printed 1/(2*i) loses a factor of two.

The displayed real majorant sqrt(t+|epsilon|)/sqrt(t-|epsilon|) is
undefined as an ordinary real expression when 0<t<|epsilon|.
Under Lean's totalized square root and division it is zero there,
while the actual quotient can have positive norm.
[`AppendixFProofAudit.lean`](../NLS/ComplexAnalysis/AppendixFProofAudit.lean)
checks both obstructions. The formal proof establishes F.2 by equality
with the already constructed joint analytic primitive, without using
that majorant. See [source discrepancies](../SOURCE_ERRATA.md).

## Verification evidence

Existing examples cover p=3/2 and p=3, collapsed complex gaps,
nonzero real sources, all boundary points on one neighborhood,
nonconvex path domains, and improper endpoint limits. Free-source
checks retain -i*nu+i*pi*n for the endpoint average and i*pi*(n-m)
between gaps, including negative indices, equal gaps, and endpoint
choices that switch by an arbitrary predicate. Current full-build and
axiom-audit totals are recorded in [status](../STATUS.md).
