# Current completion assessment

The dissertation formalization is not yet certified complete. The public
source-comparison snapshot contains comparisons for every named heading
in its reviewed heading index, along with selected unnumbered definitions,
displays and proof assertions. That is useful evidence, but does not prove
that every substantive unnumbered assertion has been assessed.

This assessment preserves the original objective: work through the whole
dissertation, retaining its mathematical objects, norms, domains and
quantifiers, and commit and push each validated step. A formally refuted
printed assertion must remain identified as such, alongside any proved
correction. It cannot be counted as a proof of the literal printed claim.

| Requirement | Current evidence | Remaining work |
| --- | --- | --- |
| Named mathematical statements | [Source comparisons](source-review-index.json), linked section and appendix audits, and current public Lean proofs; 161 named comparisons retain their qualifications. | Preserve exact scope and corrections in the overall assessment; the count is not a completion percentage. |
| Unnumbered definitions, equations and substantive assertions | Selected source ranges have explicit comparisons, including the introductory energy, spectral outline and mixed-frequency estimate. | Build and inspect a source-wide assertion inventory. Matching ranges or headings alone does not certify their contents. |
| Original objects and quantifiers | The focused audits record physical operators, original distributions, full multiplicities, actual integrals, norms and common-neighborhood quantifiers. | Reconcile each remaining assertion against these specific interfaces, rather than infer agreement from similar names. |
| Literal source discrepancies | [Source discrepancies](../SOURCE_ERRATA.md) separates refutations, proved corrections and qualified interpretations. The auxiliary-height history now reflects the proved p=2 case and unrestricted counterexample. | Retain all distinctions; do not silently replace an unresolved interpretation with a candidate correction. |
| The cited 2014 Birkhoff construction | [Section 14](SECTION_14.md) records the inspected 2013 manuscript and independently proved physical coordinate formulas. | The exact construction in the cited 2014 edition still needs comparison. The different edition and public contents are insufficient evidence. |
| Appendix G.2 interval norm | [Appendix G](APPENDIX_G.md) records the proved unit-interval result, a formal counterexample for the usual local integral norm, and an arbitrary-time correction candidate. | The source's intended arbitrary-time norm remains unspecified; the candidate correction has not been adopted as that interpretation. |
| Lean validation and publication | [Current status](../STATUS.md) records the build, all public examples, transitive axiom audit and documentation checks for each milestone. | Every implementation change must pass its required checks and be committed and pushed. Passing checks does not establish source completeness. |

## How the next assessment proceeds

The [ordered Section 20 ledger](SECTION_20_ASSERTIONS.md) classifies
56 groups on pp. 91–96: 46 matched, eight corrected or clarified and two
contextual, with no partial or pending groups in that ledger. The positive
[quarter-exponent remainder](../NLS/ZakharovShabat/SourceActionGapQuarter.lean)
closes S20-052. The new [full-disc auxiliary proof](../NLS/ZakharovShabat/SourcePsiRefinedFullDisc.lean)
closes S20-030: every original open isolating disk has a fixed p/2 plus
OnePlus supremum bound, locally uniform in the complex source and uniform
in the deleted index. A common connected neighborhood can be restricted
inside the original source domain while preserving all real sources.

The [ordered Section 21 ledger](SECTION_21_ASSERTIONS.md) now compares
34 groups on pp. 96–98: 27 matched, five corrected and two contextual,
with no partial or pending groups in that ledger. It retains exact
primitive-power moments, the H1 physical correction and FL4 extension,
common domains, convergence, the action gradient and complex bilinear
Hessian. The opening dummy index is normalized directly; existing sign
and cube-constant corrections remain. No new proof or refutation is added.

The [positive Section 22 phase estimate](../NLS/ZakharovShabat/SourceSection22PhaseEstimate.lean)
now supplies the exact component-sum pair norm, `2^p` tail constant and
`2*epsilon` consequence for the actual original physical trajectories.
The repeated scalar time variable is corrected directly, with no new
refutation. The complete ordered Section 22 comparison remains in progress,
while the [cutoff and uniform estimates](../NLS/ZakharovShabat/SourceSection22UniformEstimates.lean)
are now proved. One original complex coordinate neighborhood supports
the mixed frequency/exponential bounds and full analytic trajectories
bounded by `exp(R*C) * M`, with the neighborhood and constants chosen
before every horizon. The [phase-separation estimates](../NLS/ZakharovShabat/SourceSection22PhaseSeparation.lean)
now also give the literal successive-frequency construction, amplitude-minus-error
bound and eventual half-amplitude separation. The independent Hilbert-energy
lemma covers arbitrary pointwise approximations. The
[Hilbert coordinate extension](../NLS/ZakharovShabat/SourceSection22HilbertCoordinates.lean)
now also retains arbitrary Hilbert approximations in the original-family
application, with exact physical mass normalization, ordinary frequency
compatibility, divergence and eventual actual image inverse. The full
ordered comparison is still pending.
The direct contour corrections, original action-image scope and alternate
convolution proof remain explicit. These local ledger counts do not
certify complete formalization of the dissertation. No new refutation
is added.

Lemma 4.3 now also has a direct map on the original periodic distribution
pairs with their exact finite-p norms. The full signed source and reflected
series converge, the physical modes determine the map uniquely, and both
corrected coefficient formulas hold for every rough input with 1<p<infinity.
The endpoint and normalization qualifications remain unchanged.

Both abstracts now have a [consolidated mathematical comparison](INTRODUCTION.md)
covering their seven paired claim groups. It retains the exact exponent and
gap restrictions, renormalization, solution sense and norms, together with
the unresolved external-construction qualification. Novelty and historical
priority are outside that assessment. The introduction now also has a
37-group ordered assertion inventory, preserving its four refuted formulas
and all earlier scope qualifications. The [complete spectral overview](SPECTRAL_OVERVIEW.md)
now has 27 ordered groups, preserving both unrestricted height refutations
and the complex finite-gap regularity correction. The complete Section 2
text has been reconciled with its existing twelve-group comparison and
three corrections. Section 3 now also has two endpoint-inequality corrections
in Lemma 3.2's proof and formal refutations of two radius-dependent
intermediate estimates in Lemma 3.4's proof. The main Lemma 3.4 remains
proved. Direct original-norm setup proofs now also cover closedness,
equation (1.3), the first resolvent identity, height decay and the square
estimate, with both signed coefficient formulas. Literal denominator geometry,
absolute double-sum majorization for the actual components, the near/far
partition and the cutoff-retaining Fourier-tail identity are also proved.
The literal Hölder displays, exact scalar norm factorization and explicit
p=1 near/far radius bounds are now proved as well.
The literal Lemma 3.2 scalar Hölder formulas, centered denominator geometry,
punctured-series bound, height moment chain and strip moment are also proved.
Lemma 3.2(i)'s signed Fourier expansion, explicit finite-rank cutoffs,
rank bound and original-norm closure argument are also proved.
The direct Corollary 3.3 composition bound, actual Neumann inverse and
series, and compactness inference are now proved in the original norm;
the standalone pair-norm counterexample remains valid.
Corollary 3.5's squared inverse, original-norm quarter/half bounds, compact
segment and common neighborhood for all larger exact spectral exteriors
are also proved, with the compact analytic resolvent and spectrum enclosure.
Four focused proof groups now also compare the actual Cauchy–Riesz
projections, parity decomposition, full-domain invariance and analytic
period-one restrictions in equations (1.4)–(1.5) and Lemma 3.6.
Four further groups compare the deformation to free contour ranks,
algebraic and parity counts, spectral exhaustion and real-type symmetry
on the full domain. The central height-N conclusion retains the separate
qualification on the printed norm-dependent height.
Lemma 3.7 and its intrinsic trace formulas, actual domain lifts, local
analytic range transport and scalar analyticity now have four focused
proof comparisons, including repeated roots and the exact factor one half.
Eight further Section 3 passage groups now reconcile the opening operator
setup, compact-resolvent discreteness, exact sufficient regions, quantified
Lemma 3.4 and endpoint modifications, retaining all formal refutations.
Relative boundedness and closedness use alternative proofs of the source
assertions; the cited external perturbation argument is not independently audited.
The complete Section 3 text now has a 38-group ordered assertion inventory,
checked against all five rendered pages. It preserves six formally refuted
printed bounds, valid clauses and corrections, explicit interpretations,
and contextual citations. Each group links its exact prior proof evidence.
Section 4 now also has literal sine/cosine Fourier-series proofs for
Lemma 4.2, exact AKNS coefficient formulas, and continuous equivalences
onto both full classical boundary domains via the established physical
restriction maps. The scalar R_cos and R_sin statements now also have
explicit continuous linear equivalences on actual periodic and interval
functions with exact physical H1 norms and closed-interval values. Their
product realizes the entire original Dirichlet domain. This resolves the
earlier missing separate scalar-map scope without claiming an independent
audit of textbook reference [54].
The complete Section 4 passage now has a 38-group ordered assertion
inventory covering its six printed pages, with 60 reviewed proof modules
and 236 resolved declaration references. It preserves three local formula
refutations, the original infinity norm, separate p=1 classical realization,
and the inherited height and product-constant qualifications.
Section 5 now also has native auxiliary distribution maps with exact
finite-p norms, physical Fourier identification, full signed-input series,
uniqueness and p=2 isometry. Its complete passage now has a 17-group
ordered assertion inventory covering printed pp.33–35, with 43 reviewed
module bodies. A combined theorem supplies one neighborhood for the
full exterior resolvent and both auxiliary projection families at every
larger cutoff. All four printed refutations, finite/infinite-norm distinctions
and general height-N versus literal p=2 height qualifications remain.
Section 6 now also has a formal refutation of the final equality in the
Lemma 6.5 proof, together with the valid original-domain inequality chain
for every finite Banach exponent. The main lemma remains valid. This is a
four-group focused comparison; the 47-group ordered inventory remains open.
Four further focused groups now cover the p.42 proof-series weight,
original-source joint sum and analytic coefficient, with a locally uniform
cutoff counterexample and both simultaneous half-contraction bounds.
Four additional groups compare the p.44 intermediate power inequality:
actual p=4 witnesses refute its printed factor, and the corrected estimate
holds for original counted roots on one common neighborhood and cutoff.
The final weighted gap sum is now proved with C_p=2^(3*p-2), preserving the
actual original canonical pair, full signed coefficient sums and common local
cutoff for every larger cutoff. The original weighted pair norm and additive
leading Fourier tail remain in the Lemma 6.8 budget. This supplies a valid
corrected constant without requiring a refutation of the printed factor.

The [ordered Section 6 ledger](SECTION_6_ASSERTIONS.md) now reconciles all
47 passage groups: 37 matched, nine corrected and one interpreted. The literal
single reciprocal Fourier series and Holder–Young proof retain the original
weighted l1 representative, domain coefficients, opposite shifts and Hilbert
constant two. The double-series proof retains the exact remainder, selected
near/far moments and the corrected final inequality. Earlier spectral,
normalization and quantitative-budget qualifications remain in force.

This completes that ordered comparison, not the source-wide inventory or a
transitive semantic audit of all dependencies. Counts are navigation, not a
completion percentage. Constant corrections need a proved valid replacement;
additional counterexamples are not required. Continue with Section 7, then
later sections in source order.

All 21 groups in the [ordered Section 7 ledger](SECTION_7_ASSERTIONS.md)
have now been compared: eighteen matched, one corrected and two partial.
The corrected product, constructed angle path sum and actual real rough
source have direct interfaces. S7-002 retains the physical NLS motion clause;
S7-013 retains uniqueness of psi among all stated entire products without
the real-root placement premises of the existing uniqueness theorem.
Its corrected product and exact periods are proved. The corrected real
codimension in S7-014 is two. These remaining clauses prevent treating
Section 7 as fully resolved.

The [ordered Section 8 ledger](SECTION_8_ASSERTIONS.md) now compares all
36 groups: 28 matched and eight corrected. The exact full-exterior sine
constant resolves its previous partial group. The literal sinc integral,
root-count and continuity proofs, critical product and squared-gap offset
are reconciled with the source, retaining full multiplicities and collapsed
gaps. The neighboring-band endpoint is corrected to n+1 and the midpoint
factorization uses -4. No additional constant refutation was added. This
section-level result does not settle the broader source inventory or
Section 7's two unresolved clauses.

The [ordered Section 9 ledger](SECTION_9_ASSERTIONS.md) compares all fifteen
groups: twelve matched and three corrected occurrences of the existing
auxiliary-label discrepancy. The missing local implicit-function construction
is now proved at arbitrary complex simple boundary roots, including actual
operator simplicity. Full sample bounds retain the central block. The
Section 7 and broader qualifications above remain open.

The [ordered Section 10 ledger](SECTION_10_ASSERTIONS.md) compares all
52 groups: 44 matched and eight corrected occurrences. The final complex
boundary integrals, endpoint integrability and signed doubled-circle formula
retain every original disk and the common W. Actual improper endpoint-path
integrals use independent truncation, including finite piecewise paths and
collapsed endpoints. This completes that section's ordered comparison;
continue in source order with Section 11's action construction. It does not
settle the wider unresolved clauses or certify dissertation completeness.

The [ordered Section 11 ledger](SECTION_11_ASSERTIONS.md) now compares all 22
groups: twenty matched and two corrected occurrences. The final tail limit has
an explicit positive proof, with the tolerance chosen before the complex
neighborhood and signed cutoff. This is Mathlib's locally uniform convergence
statement and also gives uniform convergence on every compact real source set.
The actual filled indexed quotient is strictly positive on the real locus;
the factor four, squared collapsed-root identity and common-domain principal-root
conclusions are retained. The ordered Section 12 comparison follows below. Earlier
corrections and all wider qualifications remain; these comparisons do not
certify source-wide completeness.

The [ordered Section 12 ledger](SECTION_12_ASSERTIONS.md) has 67 groups,
all now compared: fifty-five matched and twelve with estimate, scope,
gap-reference or sign corrections. Lemma 12.12 retains the unchanged
common complex domain, all signed omitted indices and collapsed gaps.
Its original-disk estimates, actual coefficient suprema and both
substitutions give the literal squared-gap factorization and uniform
p-power bounds. The review distinguishes the independent atlas
construction from the original-disk proof replay that reuses it.
Earlier corrections and wider qualifications retain their scope.
This closes Section 12's ledger, not the dissertation-wide semantic audit.

The [ordered Section 13 ledger](SECTION_13_ASSERTIONS.md) has fourteen
groups, all matched against the original-domain proofs. The review checks
the actual angular integrals, analytic representatives, uniform beta
bound, convergent beta series and the three canonical brackets for every
finite p>1. It preserves the interior-C1 improper-path convention, the
open-gap domain of each angle, convergence for each fixed index on a
common neighborhood, and pointwise index decay. The canonical brackets
use actual differentials with absolutely convergent Fourier pairings;
exponent compatibility explicitly includes the range below two.
Existing proofs suffice, with no new correction or refutation. The exact
cited edition of [23] remains unaudited; the wider qualifications below remain in force.

The [ordered Section 14 ledger](SECTION_14_ASSERTIONS.md) classifies all
eighteen overview groups: thirteen matched, one explicit common-domain
restriction, one partial external comparison and three contextual remarks.
The actual original-family map has all five Theorem 14.1 properties on the
constructed compatible complex neighborhood V inside the preceding W.
The review does not identify V with an arbitrarily fixed earlier W.
Native weighted proofs cover the positive-smoothness extension. The proof
outline records the actual local-inverse, finite-gap, Fredholm and flow
arguments. The exact 2014 [23] comparison remains unresolved, and the
historical open-problem and heuristic remarks are not promoted to theorems.
Later Chapter 3 arguments and the wider dissertation qualifications remain
to be reviewed.

The [ordered Section 15 ledger](SECTION_15_ASSERTIONS.md) now compares all
fifteen passage groups: twelve matched and three with explicit corrections
or a sufficient estimate replacement. The opening sine difference and
exactly-one-nonzero classification at complex collapsed gaps are retained.
The sequence-analyticity argument uses the proved local beta bound and
rectangular constant; it does not certify fixed-neighborhood uniform beta
decay. Lemma 15.1 retains the original angular W, while equation (3.2) and
Theorem 15.2 use the common Chapter 3 V. The canonical identities use the
actual coordinate derivatives at all real sources and finite p>1. Existing
proofs supply these results, with no new refutation. The exact external
edition comparison remains unresolved.

The [ordered Section 16 ledger](SECTION_16_ASSERTIONS.md) now records
all 27 groups: 20 matched and seven corrected. Two new positive
theorems establish the intermediate x/y gradient estimates of Lemma 16.2
in source operator norms and physical Holder-conjugate pair norms for
actual sequence entries, at every real finite-gap source and finite p>1.
The corrected product sign, Fourier reconstruction sign and bounded
inverse norm in the cutoff estimate are retained directly.

Two further positive theorems prove the separate quotient-product and psi
numerator asymptotics at their own Dirichlet roots for every real source.
The common actual-gap majorant is chosen before both indices, so diagonal
sampling retains lp summability for the original n-dependent root family.
The full-complex auxiliary estimate retains its separate proof on W.
This completes the ordered Section 16 comparison with explicit corrections;
it does not resolve the wider dissertation qualifications.

The [ordered Section 17 ledger](SECTION_17_ASSERTIONS.md) classifies all
31 groups: 21 matched, eight corrected, one partial external comparison
and one contextual attribution. Existing proofs establish local analytic
inverses and global injectivity for all finite p>1, surjectivity for p<=2,
the full original pre-collapse theta flow, its continuous displacement in
every finite exponent above one, and the stated isospectral images.
Corrected canonical labels, selected indices, factor two, the matching
2N+1 enumeration cutoff and inward signs are retained directly.

S17-007 remains partial only for the exact cited 2014 [23] construction
comparison; the internal Hilbert inverse is proved. The attribution to
[36] is recorded as contextual. No new refutation is added.

The [ordered Section 18 ledger](SECTION_18_ASSERTIONS.md) classifies all
39 groups on pp. 83–87: 28 matched, five corrected, one partial external
comparison and five contextual groups. The same original Hamiltonian and
frequency retain their common action domain, physical normalization,
uniform Taylor remainders, inverse and Fredholm results, sign and local
concavity. Corrected full-Hessian, subtraction and gauge formulas are
retained directly, together with the restricted action-image neighborhood
and the mass notation H₁.

The solution results use all smooth approximations and compact-time uniform
norms: global for 1<p≤2, local for finite p>2, and small-data global above
two. Sobolev analytic dependence holds for every real nonnegative order.
The external 2014 comparison remains partial in S18-003, and the historical
literature discussion is not counted as independently verified mathematics
or current research status. No new refutation is added.

The [ordered Section 19 ledger](SECTION_19_ASSERTIONS.md) classifies all
48 groups on pp. 87–91: 35 matched, eight corrected or clarified, and five
contextual groups. The main abelian-integral, physical Laurent, cubic and
mixed-gap statements concern the same canonical primitive on a common
original source domain. The positive gap bound retains π; normalization
and index corrections are recorded directly, without new refutations.

The [positive real calculations](../NLS/ZakharovShabat/SourceSection19RealCalculation.lean)
close S19-015 and S19-032. The companion expression attains a strictly
positive minimum on the closed real gap, including collapsed gaps. The
signed discriminant is strictly increasing on the closed real band with
exact levels −2 and 2; no critical point lies in its interior. The results
hold at all finite p>1 and all signed indices. No Section 19 group remains
partial or pending under this comparison's stated scope.

The physical Laurent proof uses internal WKB asymptotics, a local sinh
inverse estimate and half-integer sampling. Individual principal-arcsine
displays and the external [23] convention footnote are not separately
claimed formalized. The subsequent Section 20 comparison and its
completed positive auxiliary estimates are recorded above.

Classify each substantive
claim as proved with exact scope, corrected with a proved valid replacement,
contextual or outside-work attribution, or unresolved. Retain existing refutations. Each
classification needs the source location and its actual proof evidence.
A range inventory is navigation for this review, not a semantic validator.
Previous selected comparisons can be reused with their stated scope and
verified module hashes; they must not be relabeled as exhaustive reviews.

The exact 2014 identification and G.2 interpretation remain open throughout
that work. Existing unchanged questions and unavailable-source attempts
need not be repeated without new information.

## Declaration reference clarification

A preparatory inventory matched every recorded declaration reference to
an actual imported NLS declaration. Two short suffixes had multiple matches:

- In Appendix F, `NLS.ZakharovShabat.sourceLemmaF2` constructs the common
  domain. `NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily.sourceLemmaF2`
  is the separately cited family-level boundary theorem.
- In Section 2, `NLS.WeightedCoeffPair.sobolevSesquilinearPairing_physical`
  handles the finite pair spaces, while
  `NLS.WeightedCoeffPairInfty.sobolevSesquilinearPairing_physical` handles
  the distinct infinity-pair norm. The reversed endpoint uses
  `NLS.WeightedCoeffPair.sobolevSesquilinearOneInfinity_physical`.

This resolves reference ambiguity only. It does not replace inspection of
the mathematical statements or certify the source comparison by name.
