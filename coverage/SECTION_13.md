# Section 13 original-domain audit

Source: printed p. 72 of the dissertation. This audit distinguishes the
literal angle definitions and their original common domain from earlier
library packages that construct other neighborhoods. Historical angle
modules remain available; this audit follows the retained Section 12 data.

| Source assertion | Current original-domain evidence | Remaining work |
| --- | --- | --- |
| One common W and actual psi family | `sourceSection13OriginalDomain` retains Lemma 12.12 and constructs original disks containing the Dirichlet roots at every complex source | None for domain and terminal geometry |
| Beta does not depend on the admissible path or root continuation | `beta_original_dirichlet_path_independent`, including different original disks and collapsed complex gaps | Construct integrable endpoint paths and identify their values with the analytic beta functions on the same W |
| A periodic terminal makes beta zero on either sheet | `beta_original_periodic_terminal_zero`; collapsed paths also have proved integrability | Integrability at noncollapsed singular endpoints remains explicit in the general comparison |
| Eta is independent modulo 2π of the admissible path | `eta_original_dirichlet_path_periods` for every original disk and open gap, including periodic terminals | Construct endpoint values and discharge actual/model integrability for those chosen paths |
| Theorem 13.1(i): analytic beta and literal uniform bound | Earlier analytic/bound packages need comparison with the retained domain and actual endpoint values | Audit and prove the complete same-domain assertion |
| Theorem 13.1(ii): eta analytic modulo π | Earlier complex-angle charts need identification with the retained eta integrals | Audit and prove the complete same-domain assertion |
| Theorem 13.1(iii): locally uniform beta series and o(1) | Existing summation tools remain available | Apply to the same-domain beta family and its bound |
| Theorem 13.1(iv): real theta and analytic extension modulo π | Existing theta packages remain available | Identify the literal sum of the preceding same-domain angles |
| Corollary 13.2: three Poisson bracket identities | Existing bracket machinery remains available | Audit identities for the same literal action/angle family and all finite p>1 |

## Verified path comparison step

`sourceSection13OriginalDomain` retains exactly Lemma 12.12's W₀, W,
and psi root family. The earlier spectral results supply endpoint data
at every complex source. Actual original disk neighborhoods contain all
gaps and Dirichlet terminals simultaneously; no additional intersection
or replacement root atlas is used.

The original periods construct off-diagonal primitives and diagonal
model-remainder primitives on the full cut complement of every supplied
original disk. Their periodic endpoint values agree. Prescribed-sheet
primitives extend through cut interiors. At collapsed gaps, the actual
numerator cancels the selected root and gives a removable extension;
its normalized sheet data satisfy the same interface as open gaps.

For beta, any two integrable C¹ admissible paths with continuously
continued roots give the same integral when normalized at the actual
Dirichlet anti-discriminant. They may use different original disks, and
neither path must stay inside its terminal root chart. At periodic
terminals either sign gives zero, including collapsed gaps. For collapsed
beta gaps, integrability of every such C¹ path is also proved. For eta,
two admissible paths in any supplied original disk agree modulo 2π on
open gaps, with either sign permitted at a periodic terminal.

The general path comparisons explicitly require curve integrability;
the eta comparison requires it for both the actual and model integrands.
This step proves invariance of these integrals. It does not yet construct
every endpoint integral or identify the analytic angle functions on the
retained W. These remaining obligations are recorded in the Section 13
audit, before Theorem 13.1's estimates and series assertions.

Nineteen public checks cover the retained domain and family, actual
Dirichlet containment, full original-disk primitives, continued roots,
comparisons across disks, periodic terminals, collapsed complex and free
gaps, and exponents 3/2 and 4.

Next: construct and identify the endpoint integral values on this same W,
then audit Theorem 13.1 and Corollary 13.2. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 7066 build jobs, the complete
public example suite, and the transitive axiom audit of 33524 NLS
declarations. The seven new modules and nineteen new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 176 checked local Markdown file links resolve,
and `git diff --check` passes.

| Module | Verified scope |
| --- | --- |
| [SourceAngularOriginalDomain](../NLS/ZakharovShabat/SourceAngularOriginalDomain.lean) | Retained integration interface and endpoint spectral data throughout W |
| [SourceAngularOriginalPrimitives](../NLS/ZakharovShabat/SourceAngularOriginalPrimitives.lean) | Off-diagonal and diagonal remainder primitives on every original cut disk |
| [SourceAngularBetaAdmissiblePath](../NLS/ZakharovShabat/SourceAngularBetaAdmissiblePath.lean) | Continued roots evaluated from signed primitive limits and terminal charts |
| [SourceAngularOriginalCollapsedPrimitive](../NLS/ZakharovShabat/SourceAngularOriginalCollapsedPrimitive.lean) | Full-disk removable primitives and prescribed-sheet data for collapsed gaps |
| [SourceAngularOriginalBetaPaths](../NLS/ZakharovShabat/SourceAngularOriginalBetaPaths.lean) | Beta path and disk independence, periodic-terminal zeros, and collapsed-path integrability |
| [SourceAngularOriginalEtaPaths](../NLS/ZakharovShabat/SourceAngularOriginalEtaPaths.lean) | Eta path invariance modulo 2π and actual Dirichlet containment |
| [SourceSection13OriginalDomain](../NLS/ZakharovShabat/SourceSection13OriginalDomain.lean) | Actual all-index disk neighborhoods and the unconditional retained-domain construction |
