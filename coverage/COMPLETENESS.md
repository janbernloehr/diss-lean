# Current completion assessment

The accepted completion criterion is verification of the dissertation's three main theorems, **0.1–0.3**. That criterion is satisfied: the source statements, quantified interfaces and existence constructions were checked against the current Lean library. The [main-theorem verification](MAIN_THEOREMS.md) gives the precise results and proof entry points; its [verification record](main-theorems-verification.json) pins the evidence.

The broader [source inventory](WHOLE_DISSERTATION.md) remains useful navigation through 41 units and 1,229 groups. Its lack of partial or pending entries is not the basis for the main-theorem conclusion, and neither its counts nor source-line accounting certify every substantive claim in the PDF. An exhaustive whole-dissertation semantic audit is outside the accepted completion criterion.

## Accepted scope and retained qualifications

- The supplied Grébert–Kappeler manuscript is the [accepted reference](ACCEPTED_REFERENCE.md). Its construction conventions, Theorem 19.3 and Sobolev Theorem 20.2 are compared with the existing physical and weighted maps. S14-010, S17-007 and S18-003 are matched under that reference choice. Identity with the published 2014 edition is outside scope.
- The user accepted the precise smooth-solution interpretation of [S7-002](SECTION_7_ASSERTIONS.md). The proved velocity formula retains its additional real multiplier and smoothness hypotheses. Differentiability for arbitrary rough L2 solutions is not asserted.
- The [positive constant corrections](SECTION_3.md) retain the literal near coefficient 4*p^2/r^2, far coefficient 64*p^2/r^2 and exact Fourier remainder, for all finite Banach exponents, signed centers and 0<r<=1. Lemma 3.2 uses the proved factor 2^(1-1/p); corrected spectral heights and contour arguments remain adopted.
- [Appendix G.2](APPENDIX_G.md) uses the explicit integral H1 norm and proved length factor sqrt(t^(-1)+t). The source leaves its local norm unspecified; the implemented convention is explicit. Other finite-exponent, endpoint, domain and infinity-norm qualifications remain in their source comparisons.
- Contextual attributions and historical open questions are recorded as context. They are not additional mathematical theorems certified by this project. Earlier refutations are preserved; this completion update adds none.

## Validation and publication

The unchanged Lean and dependency snapshot passed 8,662 build jobs, all 7,729 public examples and the transitive axiom audit for 45,245 NLS declarations. Its 21 inherited warnings are unchanged. This reference and scope reconciliation adds no Lean declarations and reuses that exact validated snapshot.

The final integrity checks verify the [source review index](source-review-index.json), all source-inventory evidence references, current document hashes, documentation links and unchanged Lean snapshot. Every historical proof-evidence row is retained. The source line accounting, scope decisions and proof validation are distinct checks.

Each completed implementation step is committed and pushed. No further implementation or audit is required to satisfy the accepted main-theorem criterion. Earlier statements below about waiting for the exact 2014 edition or the Section 7 interpretation describe previous scope and are superseded by the accepted choices above.

## Historical assessments

The entries below preserve earlier milestones and their then-current next steps. Statements below about pending publications or unfinished source navigation are historical; the current requirements are stated above.

The [positive constant corrections](SECTION_3.md) adopt the corrected bounds in section_3-007, section_3-023 and section_3-024. The new subsum proofs include p=1 and every signed center while preserving the exact original scalar norms and Fourier remainder. Earlier evidence and the separate interpretation and reference-edition qualifications remain.

The [corrected-height contour arguments](SECTION_4.md) now adopt the positive corrections in section_3-034, section_4-027, section_4-033, section_4-035 and section_5-015. The ordinary and auxiliary packages retain the original spaces, full ambient and restricted analytic families, shared neighborhoods and original-domain ranks. All earlier evidence and the separate interpretation and reference-edition qualifications remain.

The [periodic and ordinary-boundary height corrections](SPECTRAL_OVERVIEW.md) are adopted directly in spectral-11, spectral-21 and section_3-003. The new period-two package retains every finite Banach exponent, including p=1, and arbitrary input. These positive corrections preserve all earlier evidence and the separate interpretation and reference-edition qualifications.

The [auxiliary spectral-height correction](SECTION_5.md) now gives the explicit (1+8*p*E_p*norm(phi))^p bound at every finite p>1, with both exact central counts and exhaustive localization in the original source norm. This adopts the correction directly and adds two positive proofs. The remaining source qualifications are unchanged.

The [whole-dissertation source index](WHOLE_DISSERTATION.md) now accounts for every nonblank extracted source line. This completes the navigation reconciliation, not every mathematical requirement. The precise 2014 construction comparison and other recorded interpretation qualifications remain. Earlier entries below retain their then-current scope.

The [Section 7 physical NLS velocity](SECTION_7.md) proofs add 24 checked positive theorems. Continue the general Hilbert-space direction interpretation in S7-002 and the whole-dissertation source reconciliation. Retain the exact cited 2014 construction qualification. Correct constants directly and commit and push each completed step. The broader completeness qualifications below remain.

The [bibliographic source context](BIBLIOGRAPHY.md) records all 67 attributions separately from mathematical reviews. This documentation step leaves the exact 2014 edition comparison, rough physical sheet-sign direction clause and whole-source reconciliation open.

The [notation-page comparison](NOTATIONS_ASSERTIONS.md) maps all 38 notation groups with their explicit domains and qualifications. It reconciles the native distribution conjugation, psi product and original Hamiltonian integral publications. The whole-source reconciliation, contextual bibliography and previously recorded unresolved comparisons remain.

The [native periodic conjugation](SECTION_2.md) proofs add 14 checked positive theorems. Publish the reviewed notation-page comparison after reconciling the now-published proof queue, then finish the whole-dissertation source reconciliation and its remaining qualifications. Correct constants directly; add no new refutations. The broader completeness qualifications below remain.

The [Section 7 unrestricted psi uniqueness](SECTION_7.md) proofs add 8 checked positive theorems. Continue the whole-dissertation reconciliation. The rough sheet-sign direction-of-motion clause in S7-002 and the precise cited 2014 construction comparison remain open. Retain the recorded source qualifications, correct constants directly, and commit and push each completed step. The broader completeness qualifications below remain.

The [Section 28 complex central products](SECTION_28.md) proofs add 14 checked positive theorems. Continue the broader dissertation reconciliation, including the Section 7 rough sheet-sign clause and unrestricted psi uniqueness. Correct constants directly and commit and push each completed step. The broader completeness qualifications below remain.

The [Section 28 complex enclosing-root ratio](SECTION_28.md) proofs add 7 checked positive theorems. Continue the remaining whole-dissertation reconciliation, retaining S28-006, S28-014 and S28-015, the Section 7 rough sheet-sign clause and unrestricted psi uniqueness, and the recorded broader qualifications. Correct constants directly and commit and push each completed step. The broader completeness qualifications below remain.

The [Section 7 physical Dirichlet motion](SECTION_7.md) proofs add 12 checked positive theorems. Continue the remaining whole-dissertation reconciliation. Retain the unresolved rough sheet-sign direction clause in S7-002 and unrestricted entire-product uniqueness in S7-013, together with the other recorded source qualifications. Correct constants directly and commit and push each completed step. The broader completeness qualifications below remain.

The [ordered Appendix I ledger](APPENDIX_I_ASSERTIONS.md) compares 18 groups: thirteen matched, three corrected and two contextual. The direct corrections retain lower-block invertibility, the Schur signs and the tail-space domain. Uniform weighted cutoffs connect the actual real source atlas to its complex local germs. The final density proof uses local Schur determinants and cone uniqueness, with actual real inverse maps. The exact 2014 reference comparison and the final whole-dissertation reconciliation remain open.

The [Appendix I weighted uniform cutoffs](APPENDIX_I.md) add 8 checked positive theorems. Publish the reviewed eighteen-group ordered Appendix I comparison, retaining the corrected Schur premise, signs and lower-block space, and the local analytic proof on the original nonnegative cone. Then reconcile the whole-dissertation ledger and its remaining qualifications. The broader completeness qualifications below remain.

The [ordered Appendix H ledger](APPENDIX_H_ASSERTIONS.md) compares 14 groups: twelve matched, one corrected and one contextual. The literal Hamiltonian integrals retain the original H^(k-1) regularity; H.1 keeps the weak derivative and canonical graded remainder. The direct phase correction is absorbed in the reduced H.2 polynomial, chosen before all real H^m sources. The exact 2014 reference comparison remains open. Appendix I is next.

The [Appendix H physical Hamiltonian integrals](APPENDIX_H.md) add 3 checked positive theorems. Publish the reviewed fourteen-group ordered Appendix H comparison, retaining the direct phase correction, the weak H.1 derivative and the input-independent H.2 polynomial on its full H^m domain. Continue Appendix I afterward. The broader completeness qualifications below remain.

The [ordered Appendix G ledger](APPENDIX_G_ASSERTIONS.md) compares 41 groups: 26 matched, 13 corrected and two contextual. The explicit interval norm and corrected constants are adopted directly. Actual physical gradients, finite exponent ranges and common-neighborhood quantifiers are retained. The alternative gradient proof uses cubic stability and time interpolation. G.7 remains pointwise source summability. The exact source local-norm convention is not identified; the 2014 reference comparison remains open. Appendix H is next.

The [Appendix G free-mode and gradient formulas](APPENDIX_G.md) add 7 checked positive theorems. Publish the reviewed forty-one-group ordered Appendix G comparison, then continue with Appendix H and the broader outstanding source ledger. The broader completeness qualifications below remain.

The [Appendix G whole-sequence remainder bounds](APPENDIX_G.md) add 4 checked positive theorems. Publish the seven free-mode Fourier and pointwise gradient-algebra proofs, then the ordered Appendix G comparison. The broader completeness qualifications below remain.

The [Appendix G Born and Volterra derivatives](APPENDIX_G.md) add 12 checked positive theorems. Publish the four whole-sequence H1 and uniform-time bounds, then the seven free-mode and gradient-algebra proofs and the ordered Appendix G comparison. The broader completeness qualifications below remain.

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
| Appendix G.2 interval norm | [Appendix G](APPENDIX_G.md) adopts the proved correction using the explicit integral H1 norm and interval-length constant sqrt(t^(-1)+t); the original unit-interval consequence is proved. | The source does not specify its local norm. The adopted correction fixes the implemented convention without claiming to identify the intended one. |
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
refutation. The [cutoff and uniform estimates](../NLS/ZakharovShabat/SourceSection22UniformEstimates.lean)
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
compatibility, divergence and eventual actual image inverse.
The [ordered Section 22 ledger](SECTION_22_ASSERTIONS.md) now compares
37 groups on pp. 98–101: 23 matched, ten corrected and four contextual,
with no partial or pending groups in that local ledger. It preserves the
original physical flow and approximation-solution definitions, full norms,
common domains, arbitrary-Hilbert estimates and precise nonextension scopes.
The remaining domain notation is corrected directly. No new proof or
refutation is added.

The [positive endpoint comparisons](../NLS/ZakharovShabat/SourceIndexedHigherActionEndpointAsymptotic.lean)
now retain both original periodic endpoints and every periodic-gap sample
in Section 23's higher-action asymptotic. They include closed gaps,
both signed tails and all natural spectral powers, with the printed
odd-level convention intact.
The [ordered Section 23 ledger](SECTION_23_ASSERTIONS.md) now compares
38 groups on pp. 103–106: 33 matched, three corrected and two contextual,
with no partial or pending groups in that local ledger. It retains the
original map, literal norms, common constants, weighted neighborhoods,
smoothing scope and physical higher-action outline. The constant label
and weight scope are corrected directly; prior formula corrections remain.
No new proof or refutation is added in this comparison.

The [positive Section 24 primitive formula](../NLS/ZakharovShabat/SourceHigherActionPiecewisePrimitive.lean)
now retains arbitrary original piecewise C1 circuits, including corners,
the exact factor -1/pi, all natural powers and every finite p>1. The
chosen original family, primitive and source domain are unchanged.
The [all-order Hamiltonian display](../NLS/ZakharovShabat/SourceSection24HamiltonianPolynomial.lean)
also retains the exact phase and one canonical polynomial before all
smooth complex sources, including even Hamiltonian orders and mass.
The [ordered Section 24 ledger](SECTION_24_ASSERTIONS.md) now compares
20 groups: 14 matched, two corrected and four contextual, with no partial
or pending groups in that local ledger. It retains the full original
complex trace domains, physical Hamiltonians and closed-gap cases.
The real-source mass and odd-level zero-detection corrections keep
their precise scope. No new proof or refutation is added in this
comparison. The external book-normalization footnote is contextual;
the exact 2014 edition qualification remains. Section 25 now has a direct [component-product correction](../NLS/ZakharovShabat/SourceSection25DiagonalProduct.lean)
in the proof of Lemma 25.3, preserving the final constants one and eight.
The [orthogonal P/Q splitting](../NLS/ZakharovShabat/SourceSection25OrthogonalSplit.lean)
and [unique simple diagonal root](../NLS/ZakharovShabat/SourceSection25DiagonalRoot.lean)
are also proved at the exact weighted norms and quadratic threshold.
The [ordered Section 25 ledger](SECTION_25_ASSERTIONS.md) compares 37 groups:
28 matched, seven corrected and two contextual, with no partial or pending
groups in that local ledger. It retains exact physical norms, closed strips,
quadratic thresholds, signed indices and canonical multiplicities. Direct
proof corrections preserve the final localization and gap constants. The
complex global bound uses one common neighborhood before all weights and
sources. No new refutation is added.

Section 26 now has a direct [physical norm splitting](../NLS/ZakharovShabat/SourceSection26PhysicalNormSplit.lean)
with coefficient 2^(2m-1) and the [exact leading action bound](../NLS/ZakharovShabat/SourceSection26ActionLeading.lean)
with coefficient 2^m, using the real-pair factor two. The constant
precedes all real Hm sources and covers every m>=1. Five positive
theorems and four examples add no new refutation. The
[ordered Section 26 ledger](SECTION_26_ASSERTIONS.md) now compares 28 groups:
20 matched and eight corrected, with no partial or pending groups in
that local ledger. It retains original indexed actions, exact physical
norms, finite polynomial support, all permitted orders and source-independent
constants. The intermediate sign, index and exponent corrections are
recorded directly. No new refutation is added.

The [Section 27 quarter-energy estimate](../NLS/ZakharovShabat/SourceSection27QuarterEnergy.lean)
now retains the complete remainder C*(1+M^(2m))*M. Its constant
precedes all real Hm sources, for each m>=1. The existing final
Sobolev and derivative estimates keep their original scope. One
positive theorem and two examples add no new refutation. The
[ordered Section 27 ledger](SECTION_27_ASSERTIONS.md) now compares 18 groups:
14 matched, three corrected and one contextual, with no partial or pending
groups in that local ledger. It retains the original physical trace, exact
H1 norm constant, unrestricted m=1 endpoint and coefficient-one final
derivative estimate. The full remainder, zero-index split and final
constant budget are corrected directly.

The [Section 28 small-ball estimate](../NLS/ZakharovShabat/SourceSection28SmallBall.lean)
now bounds the full original weighted action sum by 2^20 times the
squared weighted source norm, on the closed ball 8*norm(a)^2<=1.
It includes every M1 weight and admissible complex source. This
direct norm correction preserves the final real and complex
estimates. One positive theorem and two examples add no new
refutation. The [ordered Section 28 ledger](SECTION_28_ASSERTIONS.md)
compares 30 groups: 19 matched, nine corrected and two contextual, with no partial or pending groups.
The named final constants 2048, 4608, 2^20 and 2^21 remain proved. The
complex enclosing-root ratio, adjacent-distance comparison and central
telescoping product are proved on one common neighborhood. The literal chi
bound uses corrected absolute indices and includes the cutoff boundary and N=0.
The independent final 2048 proof and corrected inclusive arithmetic remain.
The new product proofs establish the intermediate bounds directly.

The [ordered Appendix A ledger](APPENDIX_A_ASSERTIONS.md) compares
32 groups: 27 matched, four corrected and one contextual. It retains
the original distribution spaces, physical normalization and all
stated exponent ranges. Direct corrections preserve weighted-c0
convergence at infinity, chirp period rescaling, the Holder product
factor C_p <= 2p and the exact Section 2 weight. No new refutation
is added.

The [Appendix B proof steps](../NLS/SequenceSpaces/AppendixBProofSteps.lean)
now expose both directions of the intermediate exponent conditions.
The convergent outer sum is bounded by the gamma-th power of the
input norm product; taking its positive gamma-th root yields B.3.
This direct proof-normalization correction retains constant one and
all finite positive input exponents allowed by the statement, including
those below one. Three positive theorems and two examples add no
new refutation. The [ordered Appendix B ledger](APPENDIX_B_ASSERTIONS.md)
compares 12 groups: eight matched, two corrected and two contextual.
It retains both B.1 bounds, full B.2 Banach endpoints and the finite
positive B.3 formula. All three nested sums converge, and the proof
outer sum is correctly the gamma-th power of the stated left side.
The zero auxiliary exponents and an unstated infinity/supremum
convention remain excluded.

The [separate Appendix C corrections](../NLS/Fourier/ModifiedHilbertSeparateCorrections.lean)
now implement F and G with their actual convergent rows. The direct
label correction gives A = H + F - G. Individual bounds and powered
sums retain the separation constant c and its power c^p explicitly.
The correction operators include both Banach endpoints; the full
transform remains finite 1 < p < infinity. Six definitions, fourteen
positive theorems and three examples add no new refutation.
The [ordered Appendix C ledger](APPENDIX_C_ASSERTIONS.md)
compares nine groups: six matched, two corrected and one contextual.
It retains actual convergent operators, the corrected boundedness
statement, direct F/G label correction and explicit c and c^p.
Only the correction operators include the Banach endpoints.
Historical refutations and broader qualifications remain unchanged.
The [positive Appendix D proof steps](APPENDIX_D.md)
now provide exact paired identities and convergence, the factor-four
exterior estimate, a uniform signed-index cutoff, the positive
product inequality and the square-row bound with explicit c^p.
One definition, eleven positive theorems and six examples add no
new refutation. The [additional Appendix D proof details](APPENDIX_D.md)
supply the actual far/near sum estimate, the finite modified discs and
the literal product supremum inequality. Explicit constants include
8*(4*p+1), the finite-head separation parameter and the conjugate-kernel
Holder constant. The half-radius tail and displayed inequality are
corrected directly. Three definitions, fifteen positive theorems and
six examples add no new refutation. The [squared factor-supremum estimate](APPENDIX_D.md)
now retains c^p and the p norm in the literal half-exponent energy,
including p<2. The nearest real lattice index is selected before all
factors and includes exterior boundaries. Three positive theorems
and three examples add no new refutation. The [ordered Appendix D ledger](APPENDIX_D_ASSERTIONS.md)
compares thirty groups: nineteen matched, ten corrected and one contextual.
It retains literal products, original quantifiers, exact roots and
multiplicities, local uniformity, actual disc suprema and independent
sampling. Direct corrections keep the half-radius tail, signed sums,
separation constants, c^p and the p norm explicit. Historical refutations
and broader qualifications remain unchanged. The [Appendix E local assertions](APPENDIX_E.md)
now prove zero germs, all complex iterated derivatives and every local
power-series diagonal at real points. The alternative complex-line
argument requires no connectedness locally. Three positive theorems
and two examples add no new refutation. The [ordered Appendix E ledger](APPENDIX_E_ASSERTIONS.md)
compares eleven groups: seven matched, three corrected and one contextual.
It retains symmetric interpolation, diagonal-omitted products, actual
circle suprema, at-most-simple poles, the nonempty real slice and physical
Fourier coefficients. The local Taylor assertions use the alternative
complex-line argument. Historical refutations and broader qualifications
remain unchanged.

The [ordered Appendix F ledger](APPENDIX_F_ASSERTIONS.md)
compares 31 groups: 27 matched, three corrected and one contextual.
It retains actual improper endpoint integrals, original isolating discs,
unordered analytic branches and constructed source neighborhoods. The
finite-p tail estimate, full common-path coefficient and positive moving
majorant are corrected directly. The explicit majorant bound retains
0 <= e <= 1, derived eventually. Source-specific integral limits,
fixed-boundary transport and mixed-sequence continuity are proved.
The half-gap conclusion and final analytic theorem retain their
independent squared-gap and joint-primitive proofs. No partial or pending
groups remain in this local ledger. Earlier implementation milestones
and their validation remain in the appendix audit. Historical refutations
and broader qualifications remain unchanged. Appendix G is next.

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
have been compared: eighteen matched, two corrected and one partial. S7-002 retains
the actual all-Hilbert signed-sheet parameterization and physical Dirichlet
nonconservation in the precise approximation-solution sense. The direction
explanation has the proved smooth physical velocity -delta*P/chi_prime
and sign multiplier sign(-P/Re(chi_prime)). It imposes no differentiability
claim on arbitrary rough Hilbert trajectories; its general Hilbert-space
interpretation remains unresolved. S7-013 proves the corrected
product and normalized periods uniquely characterize the entire function
among arbitrary complex lp products at real sources for finite p>1. The
real codimension correction in S7-014 is two. The exact cited 2014
construction comparison and wider source reconciliation remain separate.

The [ordered Section 8 ledger](SECTION_8_ASSERTIONS.md) now compares all
36 groups: 28 matched and eight corrected. The exact full-exterior sine
constant resolves its previous partial group. The literal sinc integral,
root-count and continuity proofs, critical product and squared-gap offset
are reconciled with the source, retaining full multiplicities and collapsed
gaps. The neighboring-band endpoint is corrected to n+1 and the midpoint
factorization uses -4. No additional constant refutation was added. This
section-level result does not settle the broader source inventory or
the remaining Section 7 direction clause.

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

The exact 2014 identification remains open. Appendix G.2 adopts the proved
correction with the explicit integral norm; the unspecified source convention
is retained as a qualification. Existing unavailable-source attempts need
not be repeated without new information.

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
