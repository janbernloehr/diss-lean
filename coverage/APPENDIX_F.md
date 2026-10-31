# Appendix F: analyticity of the primitive

## Uniform branches and analytic endpoint integrals

The [uniform radicand bounds](../NLS/ZakharovShabat/AppendixFUniformRadicand.lean)
keep the endpoint denominator and principal-root factor away from zero
on one source neighborhood for every path parameter in [0,1]. The
factors are jointly continuous and analytic in the source, including
for complex reference endpoints.

The [weighted integral proofs](../NLS/ComplexAnalysis/AppendixFWeightedIntegral.lean)
use the exact substitution t=s^2 to remove the inverse-square-root
weight. Continuous regular factors yield integrable weighted integrands,
and jointly analytic factors yield analytic parameter integrals.

The [literal endpoint integral](../NLS/ZakharovShabat/AppendixFEndpointAnalytic.lean)
retains the actual normalized-root branch and coefficient -i*(nu-rho1).
On one source neighborhood its integrand is integrable and its value
is analytic. Analytic endpoint and critical branches and regular-factor
analyticity along the paths are explicit.

Three modules add nine positive theorems and two examples.
No new refutation is added.

The full check passed: 8,626 build jobs, 7,726 public examples and an axiom audit of 44,913 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The 31-group ordered Appendix F comparison remains open. Actual
source-family path verification, identification with the improper
polygonal integral and collapsed-gap convergence remain. The
[broader completion qualifications](COMPLETENESS.md) remain.

## Full deleted-product domain and actual source geometry

The [deleted-pair product](../NLS/ZakharovShabat/AppendixFDeletedPair.lean)
is jointly analytic on the whole spectral plane times the unchanged
source domain. Its spectral derivative has the same joint regularity,
and its zeros are exactly the endpoints at other indices. The literal
normalization and original isolating family are retained.

On one source neighborhood, compactness supplies a positive lower
product bound and a positive upper derivative bound throughout the
original closed disc. At a collapsed complex source the neighborhood
can be restricted to impose norm(gap)*r <= s with the same bounds.
This uses squared-gap analyticity without continuous endpoint labels.

The [actual source midpoint spokes](../NLS/ZakharovShabat/AppendixFSourceSpokes.lean)
share one point on the original disc boundary for any countable
source family. Every punctured spoke stays in the closed disc and
avoids every actual gap, including at its terminal point.

The [endpoint-spoke root formula](../NLS/ZakharovShabat/AppendixFEndpointRoot.lean)
retains the actual principal square-root branch at every nonnegative
parameter, including the initial endpoint. The base radicand is
exactly the positive real expression used in the scalar estimate.

Three modules add eleven positive theorems and three examples.
No new refutation is added.

The full check passed: 8,623 build jobs, 7,724 public examples and an axiom audit of 44,888 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The 31-group ordered Appendix F comparison remains open. Remaining
branch assertions, source-family convergence and improper-path
substitutions still require completion. The
[broader completion qualifications](COMPLETENESS.md) remain.

## Common boundary points and collapsing path limits

The [common boundary point](../NLS/ComplexAnalysis/AppendixFCommonBoundary.lean)
works for every selected gap in any countable family. The punctured
midpoint spokes avoid those gaps and remain in the closed isolating disc.

The [standard-root path formulas](../NLS/ZakharovShabat/AppendixFRootPath.lean)
retain the actual normalized root, arbitrary nonzero complex terminal
displacements and positive path parameters. They give the root, quotient
and regular-factor integrand limits as the gap collapses.

The [moving-majorant convergence theorem](../NLS/ComplexAnalysis/AppendixFMovingDominated.lean)
normalizes the integrand to a fixed bound and controls the remaining
integral error by the majorant's L1 error. The
[explicit interval application](../NLS/ZakharovShabat/AppendixFPositiveIntegral.lean)
uses the corrected positive weight to prove the actual normalized-root
path integral limit. Measurability, pointwise regular-factor limits and
one common bound are explicit; eventual normalized-gap smallness follows
from gap convergence. Null endpoints and moving singletons are handled
almost everywhere.

Four modules add seventeen positive theorems and three examples.
No new refutation is added.

The full check passed: 8,620 build jobs, 7,721 public examples and an axiom audit of 44,870 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The 31-group ordered Appendix F comparison remains open. Full
source-family assembly, other-gap exclusion and improper-path
substitutions remain to be completed. The
[broader completion qualifications](COMPLETENESS.md) remain.

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
