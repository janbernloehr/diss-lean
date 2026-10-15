# Section 13 original-domain audit

Source: printed p. 72 of the dissertation. This audit distinguishes the
literal angle definitions and their original common domain from earlier
library packages that construct other neighborhoods. Historical angle
modules remain available; this audit follows the retained Section 12 data.

| Source assertion | Current original-domain evidence | Remaining work |
| --- | --- | --- |
| One common W and actual psi family | `sourceSection13OriginalDomain` retains Lemma 12.12 and constructs original disks containing the Dirichlet roots at every complex source | None for domain and terminal geometry |
| Beta does not depend on the admissible path or root continuation | `beta_original_improper_limit` and `beta_original_improperIntegral_eq_value` apply to every admissible interior C¹ path, including different disks and collapsed gaps | Proved with independent improper endpoint limits |
| A periodic terminal makes beta zero on either sheet | `beta_original_periodic_terminal_improper_limit` applies at open and collapsed gaps without a sign prescription | Proved for arbitrary admissible interior C¹ paths |
| Eta is independent modulo 2π of the admissible path | `eta_original_admissible_improper_limit` and `eta_original_improperIntegral_spec` prove convergence and identify every admissible interior C¹ path with the same original eta class | Proved across original disks, including periodic terminals |
| Theorem 13.1(i): analytic beta and literal uniform bound | `sourceTheorem13_1_original_beta` gives uniqueness, complex analyticity, and the locally uniform estimate; `beta_original_im_eq_zero` proves reality on the real-type locus | Constructed endpoint integrals, analyticity, reality, and estimate proved on the retained domain |
| Theorem 13.1(ii): eta analytic modulo π | `sourceTheorem13_1_original_eta` constructs literal eta values and real analytic local representatives on the same W; every normalized admissible interior C¹ path has the same phase | Original-domain analytic identification proved |
| Theorem 13.1(iii): locally uniform beta series and o(1) | `beta_original_series` gives absolute/local uniform convergence, analyticity, and absolute/correction decay on W | Proved on the retained domain |
| Theorem 13.1(iv): real theta and analytic extension modulo π | `sourceTheorem13_1_original` and `sourceAngularOriginalTheta` identify the literal sum, analytic local representatives, reality, and its phase differential | Proved for the literal family and its arbitrary-path improper interpretation |
| Corollary 13.2: three Poisson bracket identities | `sourceCorollary13_2_original`, `originalActionCotangent`, and `theta_original_regularCotangent_representative` identify the original actions and literal theta differentials for every finite p>1 | All three canonical identities and absolute Fourier pairings proved |

## Verified arbitrary-path improper integrals

The original angular integrals now exist along every admissible path
whose parameterization is C¹ on the open unit interval and whose root
continuation is continuous on the closed interval. Both endpoint cutoffs
vary independently. No absolute-integrability assumption or endpoint
C¹ assumption is required.

`beta_original_improper_limit` identifies the actual truncated beta
integrals with `sourceAngularBeta` on the retained Lemma 12.12 domain.
It includes collapsed gaps and regular terminals in the cut. At either
periodic terminal, `beta_original_periodic_terminal_improper_limit`
gives zero on either sheet. The value therefore agrees between different
original isolating disks.

`eta_original_admissible_improper_limit` proves existence at every open
gap and identifies every limit with `sourceAngularOriginalEta` modulo 2π.
The proof lifts the model's nonvanishing logarithmic coordinate along
the whole parameter interval, and evaluates the normalized remainder
by its primitive endpoint limits. It compares an arbitrary path with a
constructed integrable path in the same disk, then uses the established
cross-disk comparison. At a periodic terminal no root sign prescription
is needed. `eta_original_improperIntegral_spec` exposes both convergence
and the 2π class of the limit-defined integral.

Twelve public checks cover joint endpoint limits, beta equality and eta
periods across different disks, periodic terminals, the actual eta and
theta phases, reality, the same local analytic representative modulo π,
and agreement with ordinary curve integrals when they are integrable.
The statements apply to every finite p>1. The previous convergence,
analyticity, and canonical-bracket results consequently apply to this
arbitrary-path interpretation of the angle definitions.

The remaining Section 13 path obligation is discharged for the stated
interior C¹ class. No claim of absolute integrability for all such paths
is made. Next: audit Section 14's rectangular coordinates (3.1) against
these original actions and angles, then the five assertions of Theorem
14.1 and their proofs in Sections 15–17. The dissertation is not complete.

Validation: `./scripts/check.sh` passes: the full build completes 7,099
jobs, all public examples pass, and the transitive axiom audit checks 33,665
NLS declarations. The nine new modules, extended primitive-integral module,
and twelve new checks introduce no warnings; the 21 existing warnings
remain. The source inventory verifies all 156 candidate labels, all 209
checked local Markdown file links resolve, and `git diff --check` passes.

## Previous original series, theta, and canonical brackets

`sourceTheorem13_1_original` retains the same W₀, simply connected W,
and normalized psi family from Lemma 12.12. The literal beta correction
series converges absolutely at every source and locally uniformly on a
neighborhood common to every deleted index. Its sum is complex analytic
on W. Both the absolute sum and the correction tend to zero as the signed
index tends to either infinity. At real-type sources the correction is real.

`sourceAngularOriginalTheta` is exactly the constructed eta integral plus
this beta series. Changing the eta integral changes theta by an integer
multiple of 2π. Local analytic representatives agree with the literal sum
modulo π, are real at real-type sources, and have exactly the existing
phase differential. The complete angular interface is constructed with
W in all three domain slots, preserving the original root family.

`sourceCorollary13_2_original` supplies all three canonical identities for
every finite p>1. The action/action bracket needs no open-gap hypothesis;
the theta/theta bracket requires the two angle gaps to be open; the mixed
bracket requires only the angle gap. A collapsed action gap is allowed.

The action comparison is explicit: the original indexed action and the
earlier complex action have equal complex germs near every real source,
hence equal Fréchet derivatives. `originalActionCotangent` has the indexed
action's actual derivative as its underlying functional. The angle's
regular cotangent is likewise the derivative of a local representative of
the literal theta sum. Their square-summable coefficients give the actual,
absolutely convergent Fourier pairing with frequency reversal and sign -i,
including below exponent two.

Fourteen public checks cover the common-neighborhood quantifier order,
absolute convergence, decay in both directions, real values, integral-choice
periods, actual local differentials, all three brackets, collapsed action
gaps, and the literal Fourier sum. Unconditional checks at exponents 4 and
3/2 retain the original domain and verify the canonical mixed identity.

Remaining Section 13 work: extend the general path comparison from supplied
curve-integrable C¹ paths to arbitrary admissible C¹ paths whose endpoint
integrals are interpreted as improper limits. Constructed paths already
have absolute integrability and independent endpoint limits. No blanket
absolute-integrability assertion for arbitrary C¹ paths is made. After
that source-definition audit, proceed to Section 14. The dissertation is
not complete.

Validation: `./scripts/check.sh` passes: the full build completes 7,089
jobs, all public examples pass, and the transitive axiom audit checks 33,629
NLS declarations. The six new modules and fourteen new checks introduce no
warnings; the 21 existing warnings remain. The source inventory verifies
all 156 candidate labels, all 199 checked local Markdown file links resolve,
and `git diff --check` passes.

## Previous original-domain eta integrals and analyticity

`sourceTheorem13_1_original_eta` retains the same W₀, simply connected W,
and normalized psi family from Lemma 12.12. At every complex open gap,
`sourceAngularOriginalEta` is chosen from actual normalized endpoint
integrals. The fallback in its definition is never used on this domain.

Two original disks admit a shared transverse path in their open convex
intersection. Comparing each given path with this common path proves
that all normalized integrable eta values differ by an integer multiple
of 2π, even across different disks and at periodic terminals. No nesting
of the disks or nonzero terminal anti-discriminant is required.

The original annulus charts construct local analytic representatives
on the unchanged W. Every original-disk eta integral differs from these
representatives by an integer multiple of π. Consequently the phase
`exp(2i eta)` is a single nonzero complex analytic function throughout
the open-gap domain. The representatives and actual eta integrals are
real at real-type sources. The original off-diagonal beta values are
also proved real there, including collapsed gaps.

The chosen eta is a joint improper integral: both endpoint truncations
converge independently to its value. Actual and model integrability are
constructed for the chosen paths. General comparisons of other supplied
paths retain their C¹ and curve-integrability hypotheses.

Twelve public checks cover a noncircular convex intersection, common paths
in different disks, the stronger 2π period, literal integral phases,
real-type values, independent endpoint truncations, and periodic terminals
without a sign condition. Unconditional checks at exponents 4 and 3/2
construct the original domain and integral values or local representatives.

Next: prove locally uniform convergence and decay of the beta series on
this same W, then identify the literal theta sum and audit Corollary 13.2.
The remaining Section 13 assertions and the dissertation are incomplete.

Validation: `./scripts/check.sh` passes with 7,083 build jobs, the complete
public example suite, and the transitive axiom audit of 33,603 NLS
declarations. The five new modules, two extended construction modules,
and twelve new checks introduce no warnings; the 21 existing warnings
remain. The source inventory verifies all 156 candidate labels, all
193 checked local Markdown file links resolve, and `git diff --check` passes.

## Previous endpoint integral construction

`SourceLemma12_12Data.original_dirichlet_integral_path` constructs a
smooth path and continuously continued square root in every supplied
original disk containing its actual Dirichlet terminal. The root equals
the actual terminal anti-discriminant, including when it vanishes. The
same path realizes every off-diagonal beta numerator. No path or curve
integrability assumption is supplied by the caller.

The geometric construction uses a quadratic Bézier arc inside the
convex disk. Its interior stays strictly on one side of the selected
gap's line. Distances to both periodic endpoints have a common positive
lower bound proportional to `t(1-t)`. The construction also covers a
collapsed segment and a closed path with coincident endpoints.

For an open gap, the quadratic root gives an inverse-square-root bound
at each endpoint. The pulled-back actual angular one-forms and the eta
model are integrable under the weight `sqrt(t(1-t))`. The full root is
continued from the canonical interior root, with its global sign chosen
to match the prescribed terminal value. At zero endpoints, convergence
of the square proves convergence of the root. Collapsed-gap beta
integrability uses the original removable extension.

`beta_original_exists_improper_integral` identifies every beta with the
joint limit of ordinary parameter integrals as both truncation endpoints
approach independently. Thus the previously proved analytic beta and
uniform estimate now apply to constructed literal endpoint integrals.
At every open gap, the diagonal eta integral and its model also exist.
General path comparisons retain explicit integrability for other paths.

Twelve public checks cover collapsed closed paths, prescribed zero and
nonzero roots, independent endpoint truncations, one path for all beta
numerators, periodic-terminal zeros, open-gap eta/model integrability,
and exponents 3/2 and 4. The exponent-4 check constructs the original
domain, disks, paths, and integral values without any supplied witnesses.

Next: identify the eta integral class with the analytic eta charts on
the same W, then prove the remaining beta-series and theta assertions.
The full Corollary 13.2 audit and the dissertation remain incomplete.

Validation: `./scripts/check.sh` passes with 7,078 build jobs, the complete
public example suite, and the transitive axiom audit of 33,571 NLS
declarations. The six new modules and twelve new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 188 checked local Markdown file links resolve,
and `git diff --check` passes.

## Previous beta analyticity and estimate step

`sourceTheorem13_1_original_beta` constructs the same W₀, W, and psi root
family retained by Lemma 12.12. Every off-diagonal beta has a unique
normalized primitive value at every complex source in W. Every integrable
C¹ admissible path in an original disk, with the actual Dirichlet terminal
normalization when nonzero, evaluates to that beta. Periodic terminals
and collapsed gaps are included.

Each beta is complex analytic throughout this unchanged W. Original
isolating disks supply local annuli around the periodic segment and
Dirichlet terminal. The proof uses stability of the whole segment and
analyticity of the terminal, without assuming analyticity of the ordered
periodic endpoints or dividing by the gap length.

The literal Theorem 13.1(i) estimate is now locally uniform in both
indices at every complex source:

`‖β_m^n‖ ≤ C (‖γ_m‖ + ‖μ_m − τ_m‖) / |n − m|`.

One neighborhood and positive constant work for all `m ≠ n`. The original
all-disk chi majorant controls each selected central chart uniformly in
the deleted index. Analyticity of the boundary displacement sequences
in their full sequence norm supplies the small Dirichlet tail at complex
sources. Fixed tail annuli then give a bound uniform in both indices;
a finite intersection handles the remaining selected gaps.

Twelve public checks cover value uniqueness, path evaluation, original
chart geometry, fixed tail annuli, sequence analyticity, the order of the
uniform quantifiers, periodic-terminal zeros, and exponents 3/2 and 4.

The analytic and estimate assertions for these beta values are proved.
Constructing integrable admissible paths at open singular endpoints is
still required for the complete literal integral construction. The eta
identification, beta-series assertions, theta assertions, and the full
same-domain Corollary 13.2 audit remain unfinished.

Next: construct the remaining endpoint paths and identify eta on this W,
then apply the beta estimate to the series. The dissertation remains incomplete.

Validation: `./scripts/check.sh` passed: 7072 build jobs, the complete
public example suite, and the transitive axiom audit of 33546 NLS
declarations. The six new modules and twelve new checks are warning-free;
the 21 existing warnings remain. The source inventory verifies all 156
candidate labels, all 182 checked local Markdown file links resolve,
and `git diff --check` passes.

## Previous path comparison step

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

| New module | Verified scope |
| --- | --- |
| [SourceAngularOriginalBetaValues](../NLS/ZakharovShabat/SourceAngularOriginalBetaValues.lean) | Unique primitive values and equality with every integrable normalized admissible path |
| [SourceAngularOriginalAnnulus](../NLS/ZakharovShabat/SourceAngularOriginalAnnulus.lean) | Original annular charts and beta analyticity at every complex source |
| [SourceAngularOriginalAnnulusTail](../NLS/ZakharovShabat/SourceAngularOriginalAnnulusTail.lean) | Sequence-norm boundary analyticity and fixed annuli near every complex source |
| [SourceAngularOriginalBetaSelectedBound](../NLS/ZakharovShabat/SourceAngularOriginalBetaSelectedBound.lean) | Original chi bounds and one beta constant for all deleted indices on each selected chart |
| [SourceAngularOriginalBetaBound](../NLS/ZakharovShabat/SourceAngularOriginalBetaBound.lean) | One local beta constant for all off-diagonal pairs throughout W |
| [SourceTheorem13_1OriginalBeta](../NLS/ZakharovShabat/SourceTheorem13_1OriginalBeta.lean) | Unconditional retained-domain beta uniqueness, analyticity, and uniform estimate |

| Endpoint-construction module | Verified scope |
| --- | --- |
| [QuadraticBezierAdmissible](../NLS/ComplexAnalysis/QuadraticBezierAdmissible.lean) | Smooth disk paths avoiding a segment, with quantitative separation from both endpoints |
| [CanonicalRootPathExtension](../NLS/ComplexAnalysis/CanonicalRootPathExtension.lean) | Continuous continuation with any valid terminal root, including zero |
| [TwoEndpointSquareRootIntegrability](../NLS/ComplexAnalysis/TwoEndpointSquareRootIntegrability.lean) | Integrability at both branch endpoints and independent two-parameter truncation limits |
| [SourceAngularAdmissiblePathConstruction](../NLS/ZakharovShabat/SourceAngularAdmissiblePathConstruction.lean) | Actual original-disk paths with prescribed Dirichlet normalization |
| [SourceAngularTransversePathIntegrability](../NLS/ZakharovShabat/SourceAngularTransversePathIntegrability.lean) | Actual angular and eta-model integrability at every open complex gap |
| [SourceAngularOriginalEndpointIntegrals](../NLS/ZakharovShabat/SourceAngularOriginalEndpointIntegrals.lean) | One constructed path for all off-diagonal beta values and their literal improper integral limits |

| Original eta module | Verified scope |
| --- | --- |
| [SourceAngularOriginalEtaComparison](../NLS/ZakharovShabat/SourceAngularOriginalEtaComparison.lean) | Shared integrable paths and eta periods across different original disks |
| [SourceAngularOriginalEtaAnalytic](../NLS/ZakharovShabat/SourceAngularOriginalEtaAnalytic.lean) | Original-domain analytic charts, nonzero phase, beta reality, and a phase-realizing integral |
| [SourceAngularOriginalEtaValues](../NLS/ZakharovShabat/SourceAngularOriginalEtaValues.lean) | All normalized integrable original paths agree with local analytic representatives modulo π |
| [SourceAngularOriginalEtaIntegral](../NLS/ZakharovShabat/SourceAngularOriginalEtaIntegral.lean) | A chosen literal eta integral, its 2π class, reality, and joint improper limit |
| [SourceTheorem13_1OriginalEta](../NLS/ZakharovShabat/SourceTheorem13_1OriginalEta.lean) | Unconditional retained-domain statement for every finite p greater than one |

| Original series and canonical module | Verified scope |
| --- | --- |
| [SourceAngularOriginalBetaSeries](../NLS/ZakharovShabat/SourceAngularOriginalBetaSeries.lean) | Actual correction series, local uniform convergence, analyticity, reality, and decay |
| [SourceAngularOriginalTheta](../NLS/ZakharovShabat/SourceAngularOriginalTheta.lean) | Literal eta-plus-beta sum, 2π integral-choice periods, phase, and analytic real representatives |
| [SourceAngularOriginalThetaDomain](../NLS/ZakharovShabat/SourceAngularOriginalThetaDomain.lean) | Complete angular data with W in every domain slot and the same normalized family |
| [SourceAngularOriginalCanonicalDifferentials](../NLS/ZakharovShabat/SourceAngularOriginalCanonicalDifferentials.lean) | Actual local theta differentials and the indexed-action regular cotangent |
| [SourceTheorem13_1Original](../NLS/ZakharovShabat/SourceTheorem13_1Original.lean) | Unconditional retained-domain theorem for the constructed literal angles |
| [SourceCorollary13_2Original](../NLS/ZakharovShabat/SourceCorollary13_2Original.lean) | All three canonical identities for every finite p greater than one |

| Improper-integral module | Verified scope |
| --- | --- |
| [ImproperPrimitivePathIntegral](../NLS/ComplexAnalysis/ImproperPrimitivePathIntegral.lean) | Joint parameter-integral limits from primitive endpoint limits |
| [ImproperCurveIntegral](../NLS/ComplexAnalysis/ImproperCurveIntegral.lean) | Agreement with ordinary absolutely integrable curves |
| [ImproperLogarithmicIntegral](../NLS/ComplexAnalysis/ImproperLogarithmicIntegral.lean) | Continuous logarithm lifts and actual improper logarithmic integrals |
| [ImproperQuadraticRootPathIntegral](../NLS/ComplexAnalysis/ImproperQuadraticRootPathIntegral.lean) | The quadratic-root model with only interior C¹ regularity |
| [SourceAngularBetaImproperPath](../NLS/ZakharovShabat/SourceAngularBetaImproperPath.lean) | Signed primitive evaluation along arbitrary admissible root continuations |
| [SourceAngularOriginalBetaImproper](../NLS/ZakharovShabat/SourceAngularOriginalBetaImproper.lean) | Original beta limits at all complex gaps and zero periodic-terminal values |
| [SourceAngularEtaImproperModel](../NLS/ZakharovShabat/SourceAngularEtaImproperModel.lean) | Model convergence, endpoint exponential identity, and 2π periods |
| [SourceAngularEtaImproperRemainder](../NLS/ZakharovShabat/SourceAngularEtaImproperRemainder.lean) | Joint limit of the actual-minus-model truncation difference |
| [SourceAngularOriginalEtaImproperRemainder](../NLS/ZakharovShabat/SourceAngularOriginalEtaImproperRemainder.lean) | One normalized remainder for every original disk and all its admissible paths |
| [SourceAngularOriginalEtaImproper](../NLS/ZakharovShabat/SourceAngularOriginalEtaImproper.lean) | Arbitrary-path existence and agreement with the original eta modulo 2π |
