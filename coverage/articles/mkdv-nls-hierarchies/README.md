# The mKdV and NLS hierarchies revisited — verification coverage

Status: **Whole-paper verification is in progress. All main theorems are proved with the documented source corrections.
Theorems 1 and 2 hold on their original complex Sobolev domains (with the
matrix correction in Theorem2(ii)). Theorem3 holds at every order on the
full real H^(m-1) domain, including closed actions, with the corrected
positive frequency sign. Theorem4 holds on the original full real H1
domain, with mean squared in its reverse clause. Its final independent
angle-sum factorization now holds for arbitrary support and all terminal
configurations.**

One common open complex native physical-action/signed-mean domain and one
holomorphic l1-valued factor recover all original signed NLS actions for
every original real H1 profile. The converse physical-action and corrected
mean-squared factors are proved. The printed converse signed-mean claim
is false and is replaced by mean squared.
The actual Cartesian map is globally bijective in every native integer
real H^s class, s>=1; native action data have exactly one preimage among
all physical L2 sources, and arbitrary native nonnegative action data
with signed mean are realized. The global inverse is now real analytic
in every integer native H^s norm, s>=1; complex analytic local inverse
charts exist at every real profile. Every independent K_m is conserved
by each complete physical action flow on the exact real H^(m-1) domain,
including the L2 mass endpoint. Every K_m now has one global holomorphic
normal form on a common open complex native physical-action/signed-mean
domain containing all real H^(m-1) data. Its positive action derivatives
are independent of the chosen normal form for every m>=1, even at closed
actions. The original NLS S_(2m) frequency now equals the independent K_m action
derivative on ALL real H^(m-1) profiles, for every m>=1. The NLS frequency
is uniquely specified by its actual original angle bracket and continuous
sharp-domain continuation. A common open complex H^(m-1) neighborhood
holomorphically extends each frequency through all closed actions. At m=1
both frequencies equal +2*pi*n, and a checked zero-profile counterexample
refutes the printed (-1)^m factor. The final independent angle-sum clause is now proved.
The independent full spectral conjugate now has its exact negative
Kronecker generators and complete physical action-flow rotation at every
real time, through all terminal configurations and with arbitrary support.
Its full product with the actual NLS unit phase factors through the entire
physical action sequence and literal signed mean. No negative NLS angle
enters the independent phase definition. No extra analyticity of the
angle-sum factor is asserted. See the final milestone and validation below.

Prepared 2026-11-02 against canonical commit
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`.


## Whole-paper scope (2026-11-06)

The completion target now includes **every mathematical assertion** in the assigned
version: all 18 named statements, all 25 numbered equations, unnumbered setup
and background claims, mathematical remarks, proof intermediates and both
appendices. Citing a reference does not remove an invoked claim from this target.

[`full-paper-coverage.json`](full-paper-coverage.json) captures every nonblank
passage in the mathematical body by source lines, PDF page and hash. Its initial
semantic inventory records named statements, numbered equations and additional
prose/proof obligations. Passage decomposition and correspondence review are
explicitly **incomplete**. A pending passage cannot be silently treated as proved.
The source locator convention and exact private-source hashes are in the ledger.

The main theorems remain proved with the earlier corrections, but important
whole-paper work remains: full Lemma 10 and nonlocal Proposition 11(iii);
the native interval H2-to-AC source bridge in Lemma 2; remaining printed proof intermediates;
printed proof intermediates; and background claims including independent
cross-mode mKdV Cartesian canonicity. Theorem 6, Corollaries 8–9 and Lemma 13
now have the corrected source interfaces described in the later milestones.
Analytic zero orders do not certify geometric multiplicities.

The P and pure T clauses of Theorem 6(i)–(iii) now have source interfaces
for the actual discriminant, spectral derivative and full Fréchet cotangent
on every complex finite exponent p>1, including the original L2 domain.
Pure T is implemented without component exchange. Pointwise gradient
identification and the other Theorem 6 clauses remain separate obligations.

`python3 scripts/check_mkdv_nls_coverage.py` checks the inventory structure.
With `--source-text` it also verifies exact source passage hashes and coverage;
with `--require-complete` it rejects any unfinished inventory. This structural
check does not replace mathematical correspondence review or Lean checking.

The current progress validation is in [`full-paper-validation.json`](full-paper-validation.json):
28 new theorems and one definition; fresh strict compilation of all five new
modules and the combined aggregate; targeted audit of 9,799 declarations and
combined audit of 61,298. Imported compiled sources are hash-verified against
the validated incoming-main checkout. No fresh full repository source rebuild
is claimed.

Additional checked corrections:

- Page 2: the physical NLS energy gives `i*v_t = -v_xx +/- 2*|v|^2*v`.
  Both printed scalar reductions omit the factor two. Constant profiles refute
  coefficient one. `IntroductionCorrections.lean` exports the exact reductions
  and counterexamples.
- Page 4: the mKdV Cartesian equations are `x_dot = eta*y`,
  `y_dot = -eta*x`. The printed second equation repeats `y`. The actual rotation
  derivative, action preservation and a counterexample are checked.
- Appendix B: Lemma 14 explicitly requires a nonempty real slice.
  `AnalyticIdentity.lean` proves the general Banach-space statement and a
  counterexample when the complex domain misses its real form.

Other issues remain audit obligations: scalar nonlocal integrals subtracted from
vector gradients in Corollary 9(ii), Lemma 10(iii) and Proposition 11(iii); the
spectral domain in Corollary 9; high-energy Hill neighborhoods and mean shifts;
and the separate operator-convention adapter. The nonlocal sign is resolved below.
The generic-entry assertion
now has a checked complex triangular counterexample and a division-free replacement.
No corrected formula for these is counted as proved until its actual
mathematical statement and original domain have been validated.

## 2026-11-07 — Original-domain symmetries and division-free spatial equation

Proposition 11(i) is now fully checked on the exact complex H^(k-1) domain,
including pure midpoint T, for every k>=1. The Riccati recurrence proves
`rho_n(Ta,Tb)(x) = (-1)^n*rho_n(a,b)(1-x)`; literal integral substitution,
smooth density and the actual Frechet derivative then give the L2 gradients.

Theorem 6(ii) and (iv) are complete for the original spectral functions,
including every real phase, every complex spectral parameter and the exact
root signs. The original signed endpoint slots are also checked under all
three symmetries. The proof permits every nonzero complex reciprocal scaling
and every finite source exponent p>1, so it includes the original L2 domain.
Theorem 6 as a whole is still partial: see the detailed ledger.

The actual physical L2 discriminant gradient now has its spatial equation on
the whole real line, including negative times and all period seams. The
actual fundamental-matrix continuation agrees with the Frechet gradient on a
unit period. Determinant-one Floquet transport proves period-one gradient and
scalar coefficient. The scalar integral follows from genuine absolute
continuity, not merely an assumed a.e. derivative. No nonzero monodromy entry
or generic spectral parameter is required.

There is a checked nonzero constant smooth H1 potential `(0,1)` whose
upper-right monodromy entry is identically zero for all spectral parameters.
Thus the unrestricted generic-entry assertion in the page-14 proof is false.
The replacement proof avoids it. The physical convention gives
`xi = M11-M22 - 2*i*integral(R*phi dot grad Delta)`, with R=diag(i,-i).
At that milestone the printed plus sign was still a source-convention review
obligation. The following milestone resolves it; full xi covariance remains open.

This increment adds 73 theorems and 12 definitions in 17 modules. Its strict
compilation, aggregate import and transitive-audit evidence is recorded in
[`symmetry-validation.json`](symmetry-validation.json). Whole-paper coverage
remains **in progress**, including the unfinished passage decomposition.

## 2026-11-07 — Nonlocal sign resolved on the original H0 domain

For the literal Section 2 operator, the identity-normalized fundamental matrix
and the actual unconjugated Frechet gradient G=grad Delta, the correct formula is

`xi(x) = M11-M22 - 2*i*integral_0^x (R*phi dot G)`, `R=diag(i,-i)`.

The minus sign is now proved and the printed plus-sign spatial equation is
formally refuted even almost everywhere in the original complex H0 space.
Take the periodic L2 class of `phi(x)=(-2*i,i/(1+x^2))` on [0,1], at lambda=0.
The actual normalized ODE gives
`M(1)=[[2,1+pi/2],[1,1+pi/4]]`.
The actual xi derivative at zero is `2-pi`, while the printed definition gives
`pi-2`. The proof extends the obstruction to a positive-measure set and
transfers it through the physical/Fourier L2 equivalence. The periodic source
is not claimed to be H1; no endpoint smoothness is assumed by Theorem 6(v).

For normalized actual gradients g=G/root, the correctly typed residual is
`Dg - 2*lambda*R*g + 2*i*J*phi*integral_0^x(R*phi dot g)`.
It equals `(M11-M22)/root * J*phi` almost everywhere. At pure T-even or
T-odd sources the quotient is even in lambda, proving the corrected
Corollary 9(ii) identity for these normalized actual discriminant gradients.
At this milestone, identifying them with the original primitive F gradients
was still open. The next milestone closes that interface and corrected part(ii);
full Corollary 9 and Proposition 11(iii) remain open.

Actual endpoint monodromy matrix symmetries are also proved for every original
complex H0 source under P, pure T, combined PT and all nonzero complex
reciprocal scalings. They include arbitrary real phases and imply the exact
boundary quotient parity used above. All-real-x fundamental-matrix symmetries
and the separate p5/Appendix-vs-Section2 operator adapter remain open.

Eight new modules add 42 theorems and 9 definitions. Current main is integrated
with the exact union of aggregate imports. Validation is recorded in
[`nonlocal-sign-validation.json`](nonlocal-sign-validation.json).
The ledger has 108 assertion records and all 241 source passages; semantic
decomposition and whole-paper coverage remain **in progress**.

## 2026-11-07 — Corrected Corollary 9(ii) for the actual full primitive

The constructed full Abelian primitive now has exactly the normalized physical
field `grad F = grad Delta/root` as its actual Frechet gradient. The integral
formula holds for every original complex Hilbert direction. A separate
uniqueness proof shows that every continuous periodic representative of that
cotangent equals this field pointwise, including all period seams.

One common open complex H0 neighborhood contains every real source and covers
the entire moving cut complement. At any pure T-even or T-odd source in that
neighborhood, negating lambda preserves the complete cut complement. The
corrected typed nonlocal reflection identity is therefore proved for both
actual primitive gradients throughout their proper spectral domain. No
primitive-gradient hypothesis is assumed in the final existence theorem.

This completes **corrected Corollary 9(ii)**: the scalar nonlocal integral
multiplies `J*phi` and has a positive sign on the residual's left side, and
lambda is restricted to the domain where the primitive gradient exists.
At that milestone, part(i) and xi covariance were still open; the next
milestone closes both. Other ledger obligations remain open.
Four strictly checked modules add 9 theorems and 2 definitions; validation is
recorded in [`primitive-nonlocal-validation.json`](primitive-nonlocal-validation.json).
The ledger now has 110 assertion records and 241 source passages. Whole-paper
semantic decomposition and proof coverage remain **in progress**.

## 2026-11-07 — Pointwise symmetries, corrected spatial statement and full Corollary 9

The actual physical discriminant gradients now have every P, pure T and
arbitrary real phase identity at every original complex H0 source, every
complex spectral parameter and every real spatial point. These are pointwise
fields representing the actual Frechet derivative, not only cotangent maps.
The actual whole-line xi also has all three exact symmetries. Its checked
periodicity, corrected minus-sign integral and spatial equation therefore
complete corrected physical Theorem 6(v) in the literal Section 2 convention.
Theorem 6(iii) is complete on the original H0 domain as well.

Both corrected Corollary 9 clauses now hold for the same constructed full
primitive on one common open complex H0 neighborhood containing every real
source. The entire moving cut complement is covered, with exact spectral
negation invariance under either source constraint. Every Hilbert direction
identifies the actual primitive gradient; continuous periodic representatives
are unique. Part(ii) uses the positive nonlocal residual with J*phi, and both
parts use the spectral domain where the primitive gradient exists.

The actual full fundamental matrices on the whole unit interval also have
original H0 P/PT/reciprocal-scaling symmetries. Their all-real-x full matrix
continuation and the separate Appendix operator adapter remain open. Other
remaining claims include Theorem 6(i)'s invariant-neighborhood/gap interfaces,
Corollary 8, full Lemma 10, Proposition 11(iii), Lemma 2's matrix clause,
Lemma 3's geometric multiplicities, and the pending background assertions.

Eight new modules add 28 theorems and 6 definitions. Strict aggregate and
transitive audit evidence is in
[`pointwise-symmetry-validation.json`](pointwise-symmetry-validation.json).
Whole-paper coverage remains in progress, with 114 assertion records and all
241 source passages; semantic decomposition remains incomplete.

## 2026-11-07 — Complete corrected Theorem 6 and Corollary 8 with explicit domains

Theorem 6's remaining gap-segment and invariant-neighborhood clauses now check.
Literal closed segments have the exact P/T/reflected-index and phase identities.
Inside any given open complex source neighborhood containing all real sources,
a compact-circle phase core and its zero connected component give an open
connected P/T/all-phase invariant neighborhood. It retains the entire real
locus and all inherited setup properties. Actual root joint analyticity and
full primitive differential data coexist on one such domain. This completes
the named Theorem 6 in the literal Section 2 convention, with the documented
minus-sign xi correction. Its separately recorded proof intermediates and the
p5/Appendix operator adapter are still reviewed individually.

Corollary 8's actual primitive-value identities now hold on the original full
complement of noncollapsed cuts, including all collapsed spectral points.
The proof uses the actual full joint differential, connected vertical spectral
fibers over a connected open source neighborhood, and the actual zero-source
normalization. No value symmetry or new logarithm branch is assumed. Spectral
continuity extends the identities through every collapsed cut.

The actual source-gradient identities hold on the full open joint complement
of all moving cuts, in every original Hilbert direction, with a unique
continuous periodic physical representative. This domain qualification is
explicit: at source 0, lambda=0 is in the filled fixed-source spectral domain,
but the fixed-lambda source slice is formally not a neighborhood of 0. Small
diagonal constant potentials put 0 inside an open central cut. This does not
assert nondifferentiability of every possible extension; no further gradient
continuation through closed cuts is claimed. The larger domain is retained
for primitive values.

Twelve strictly checked modules add 53 theorems and 5 definitions. Evidence is
in [`invariant-primitive-validation.json`](invariant-primitive-validation.json).
The ledger has 118 assertion records and all 241 source passages. Four further
complete source passages have explicit correspondence reviews. Whole-paper
semantic decomposition and proof coverage remain in progress, including
Lemmas 2,3,10,13, Proposition 11(iii), proof intermediates and background claims.

## 2026-11-07 — Full real-line Lemma 13 and explicit Appendix operator correction

All full fundamental-matrix identities now hold at every real spatial point,
including negative periods and every seam, on the original complex H0 space.
This includes the original real-type H0 domain without a smoothness or generic
spectral-parameter hypothesis. Exact invertible Floquet transport extends the
actual unit-interval identities. The true determinant-one inverse monodromy,
literal J and PJ conjugacies, half-phase matrix and explicit entries are checked.

The page 5 and Appendix displays put phi2 in the upper off-diagonal position;
Section 2 puts phi1 there. Their operator is exactly the Section 2 operator at
P*phi, with actual physical source fields. The fundamental-matrix adapter
reflects lambda and conjugates by J; signed integer labels reverse n and
exchange their +/- slots. Retaining the literal local Appendix operator reverses
the phase factor, while its P and T matrix forms remain true. Both complete
versions are proved, without silently changing operator conventions.

An actual original real-type H0 witness from the smooth constant physical
profile(1,1), at lambda=0, x=1 and alpha=pi/2, formally refutes combining the
literal Appendix operator with the printed positive phase. Its actual
upper-right monodromy is +sinh(1), while the printed formula predicts -sinh(1).
Thus either the local operator component order or its phase formula must be
corrected. All-real-x Lemma 13 and the operator convention adapter are now
covered with that explicit correction and counterexample.

Eight new strict modules add 41 theorems and 8 definitions. Exact evidence is
in [`whole-line-matrix-validation.json`](whole-line-matrix-validation.json).
Three complete mathematical passages and one bibliographic metadata passage
have additional correspondence reviews. The ledger has 120 assertion records
and all 241 source passages. Whole-paper semantic decomposition and proof
coverage remain in progress, including Lemmas 2,3,10, Proposition 11(iii),
printed proof intermediates and remaining background claims.

## 2026-11-07 — Independent physical Miura matrices and arbitrary AC eigenfunctions

Lemma 2's full physical matrix conjugacies are now proved at every original
complex period-one H1 input, each point of the closed unit interval and every
nonzero spectral parameter. The Hill columns come from the independent scalar
IVP, with actual position/derivative initial data, AC position and derivative,
the physical u'+u^2 equation and determinant one. The matrix is not defined by
conjugating the ZS matrix. The exact printed A matrix has determinant -2*lambda,
is invertible exactly for lambda nonzero, and is period one. Its endpoint
conjugacy therefore uses A(0) on both sides.

The scalar intertwining now holds for arbitrary componentwise absolutely
continuous physical eigenfunctions, with no constructed-solution or periodic
boundary assumption on f, and includes lambda=0. AC uniqueness identifies the
actual IVP; local derivative equality transfers both the vector second-derivative
identity and the scalar equation. The exact transformed derivatives and actual
Y=A*M identity are checked. The proof paragraph's scalar energy lambda must be
lambda^2; det(Y)=-2*lambda also records the precise invertible-basis restriction.

Five strict modules add 28 theorems and 6 definitions. Seven more source
passages have complete correspondence reviews. The exact native interval
H2-to-AC input-space bridge is tracked separately: the universal physical AC
theorem is proved, but that standalone Sobolev source-space identification is
not claimed. The ledger retains partial status for the entire named Lemma 2
until this bridge is certified. Whole-paper proof coverage and semantic
decomposition remain in progress. Validation is recorded in
[`physical-miura-validation.json`](physical-miura-validation.json).

## 2026-11-07 — Full geometric eigenspace multiplicities in Lemma 3

Lemma 3 is now complete, including its geometric multiplicity clause at every
positive index and both signed endpoints. An explicit linear equivalence
compares the entire original Dirac H1 eigenspace with the actual Hill H2
eigenspace. The weak Miura potential is identified with the unchanged actual
L2 potential coefficient by coefficient, and every weak eigenvector gains
the full H2 domain. This proves dimensions and the existence of two independent
eigenfunctions; equality of discriminant zero orders is not used as a substitute.

The comparison actually holds for every complex H1 source and every nonzero
frequency. On the original real H1 domain, strict positivity supplies the
nonzero condition for both endpoints at every n>=1, including closed gaps
and zero-mean sources. The existing ground endpoint, indexed square-image
and collapse identities finish the named statement. No zero-frequency
eigenspace equivalence is asserted.

Three strict modules add 10 theorems and 4 definitions. Four further complete
source passages, including the entire Lemma 3 proof, have correspondence
reviews. The exact validation evidence is in
[`geometric-multiplicity-validation.json`](geometric-multiplicity-validation.json).
Whole-paper semantic decomposition and proof coverage remain in progress.

## Pinned source

- Authors: Jan-Cornelius Molnar and Yannick Widmer.
- Assigned version: [arXiv:1601.07580v1](https://arxiv.org/abs/1601.07580v1),
  submitted 27 January 2016; the PDF itself is dated 29 January 2016.
- [PDF download](https://arxiv.org/pdf/1601.07580v1), 20 pages;
  printed and PDF page numbers agree.
- PDF SHA-256:
  `df935943f7c35bec35b6dd2e79e89eb7e3cc144e76fdb2d26fe3a051021f87ca`.
- Private source files: `work/source/1601.07580v1.pdf` and
  `work/source/1601.07580v1.txt`, relative to this chat's working folder.
  Neither file belongs in the repository patch. The rendered theorem pages
  3 and 4 were also inspected to confirm subscripts, matrices and inequalities.

## Conventions to preserve

The circle has period one. Physical spatial differentiation has Fourier
symbol `2*pi*i*n`; the library's doubled source encoding does not change this.
Complex scalar sources use `ScalarSobolev s`, with weight `(1+|n|)^s`;
the induced norm topology is equivalent to the standard integer H^s topology.
Pairs use `SobolevSource s`. The diagonal is `(u,u)` for **complex** u, without
imposing the real-type condition. Real and purely imaginary u give the
defocusing and focusing reductions respectively.

The article has `S1 = integral(a*b)`,
`S2 = (i/2)*integral(b*a' - a*b')`,
`S3 = integral(a'*b' + a^2*b^2)`, and
`S4 = i*integral(a*b''' - 3*a^2*b*b')` (p. 2).
The existing Riccati normalization is
`H_(n+1) = (-i)^(n+2)*integral(a*u_n)`, starting with `u_0=-b`.
The first three existing calibration lemmas match S1–S3 exactly; no additional
order-dependent factor is introduced by the candidate modules. The S4
identification and its variational derivative now have checked adapters.
`hasDerivAt_classicalNLSHamiltonian` additionally certifies the physical
variational gradient at every order on smooth complex periodic fields.
The article's p. 2 footnote must be kept in mind when importing results from
its reference [4].

An explicit spectral convention adapter is also required before applying the
library's trace to the article's spectral actions: the article's p. 5 operator
has upper-right potential phi2, whereas `classicalODECoefficient` has
upper-right coefficient `i*phi.1`. Field ordering, spectral reflection and
the integer gap labels must be reconciled together. Matching the first
Hamiltonians and trace denominator alone does not settle this identification.

The mKdV conventions are `K1=(1/2)*integral(u^2)` and
`K2=(1/2)*integral((u')^2+u^4)`, with Gardner vector field
`Y_K=partial_x grad K`. NLS uses `X_S=-i*J*partial S`,
`J=((0,1),(-1,0))`. The NLS Birkhoff mixed bracket is **-1** and the
mKdV mixed bracket is **+1**. On p. 4 the superscript 2 after -1 is a
footnote marker, not a factor 1/2. Actions in both systems are
`(x_n^2+y_n^2)/2`; NLS indices range over Z and mKdV over positive integers.
The higher-action trace has factor `1/2^(k-1)` at Hamiltonian order k.

## Main statements and current correspondence

| Source statement | Domain and quantifier order | Current proved correspondence | Remaining work |
| --- | --- | --- | --- |
| Theorem 1, p. 3 | For each integer m>=1, all complex u in H^m: `X_(S_(2m))#=(Y_(K_m),Y_(K_m))` and `S_(2m)#=0`. | **Proved** by `theorem1`, with the actual native Frechet gradient and Gardner distribution derivative. `smoothMiuraSpectralHamiltonian` extracts K_m from the independent physical Hill discriminant through recursive coefficient limits on all smooth complex profiles. Its unique continuous extension to the complete complex H^(m-1) domain exists and is entire analytic; `miuraSpectralHillHamiltonian_eq_native` identifies it with the independent scalar Riccati hierarchy. `proposition6` gives the full native factor-two identity, including the L2 mass endpoint. | None for Theorem 1. The source's actual finite-gap primitive Laurent series also has exactly these spectral Hamiltonians as its coefficients. |
| Theorem 2(i), p. 3 | For every k>=1, every pair phi in H^(k-1), every real alpha: swap and phase-gradient identities, then the induced vector-field covariance. | **Proved.** `theorem2_i_swap_gradients`, `theorem2_i_phase_gradients`, `theorem2_i_swap_vector_fields` and `theorem2_i_phase_vector_fields` give all four printed identities on exactly H^(k-1), including H0 when k=1. The analytic L2 gradient represents the actual physical Hamiltonian's Frechet derivative. | None. |
| Theorem 2(ii), p. 3 | For each m>=1 and pair in H^(2m-1), assuming `P phi=R_alpha phi` for some real alpha, the even/odd gradient recurrence. | **Proved with the matrix corrected to R=diag(i,-i).** `theorem2_ii_corrected` uses Mathlib's actual distribution derivative of the physical period-one L2 fields; its value is represented by the certified even L2 gradient. `theorem2_ii_corrected_coefficients` gives the equivalent 2*pi*i*j Fourier identity. Both retain the exact complex source domain and phase hypothesis. | None for the corrected assertion; the printed matrix typo is recorded below. |
| Theorem 3, p. 4 | For every n>=1 and m>=1, equality of the restricted original NLS frequency and independent mKdV frequency on ALL real H^(m-1), including collapsed actions by analytic extension; the printed parity factor is false. | **COMPLETE with corrected positive sign.** `FrequencyIdentification.lean`: `theorem3_corrected` and `theorem3_corrected_for_any_original_frequency_extension`; `theorem3_original_bracket_agreement` identifies the actual original S_(2m) angle bracket before sharp continuation. `theorem3_original_frequency_extension_certificate` proves unique continuous extension; `theorem3_frequency_holomorphic_extension` supplies one common open complex neighborhood containing all real profiles. The mass benchmark and printed-parity counterexample are checked separately. | None for corrected Theorem 3. The final independent angle-sum clause of Theorem 4(iii) is also complete. |
| Theorem 4(i), p. 4 | For all real u in H^1: central NLS action zero iff mean zero; for each n>=1, restricted I_n zero iff J_n zero; restricted I_(-n)=I_n. | **Proved** by `theorem4_i` on the full real H1 domain, including collapsed gaps and zero mean. The mKdV action is the literal inverse-energy-weighted integral of the independent physical Hill primitive on a proved isolating contour; its equality with a positive real-gap integral and contour independence are checked. | None for part (i). Parts (ii) and (iii) are complete with the documented correction to the reverse mean clause. |
| Theorem 4(ii), p. 4 | On real H^1, each I_n# is analytic in the mKdV actions and mean; conversely each J_n and the printed mean are analytic in NLS actions alone. | **Proved with the converse mean corrected to mean squared.** `theorem4_ii_nls_actions_of_mkdv_actions_mean` supplies one common global holomorphic l1-valued forward factor on an open complex native action/mean domain containing every original real H1 profile. `theorem4_ii_mkdv_actions_of_nls_actions` and `theorem4_ii_mean_square_of_nls_actions` supply the global converse factors, including zero mean and closed gaps. | None for the corrected statement. The printed global signed-mean converse is false; its obstruction is checked. |
| Theorem 4(iii), p. 4 | For all positive n,m and every original real H1 profile, the angle-action Gardner bracket is delta_mn where its own angle is defined; the full angle sum depends only on all physical actions and signed mean. | **COMPLETE.** `theorem4_iii_angle_action` proves the actual restricted NLS angle bracket. `IndependentAbelianAngleSum.lean`: `theorem4_iii_independent_angle_sum` and `theorem4_iii_angle_sum_representatives` prove the full independent angle sum modulo exactly 2*pi. `independent_full_phase_complete_action_rotation` and `independent_full_phase_actual_action_generator` give the actual negative independent generators on arbitrary support, including all terminal configurations. | None. Only the selected own action must be open. No extra analytic angle-sum factor is asserted. |

The main dependencies singled out by the article are Theorem 5 (p. 9,
Miura/Hill versus diagonal ZS discriminants), Proposition 6 (p. 12,
`K_m=S_(2m-1)#/2` and even vanishing), Lemma 7 (p. 12, action comparison),
Theorem 6 (pp. 13–14, discriminant symmetries), Lemma 10 (pp. 16–17,
action-gradient identities) and Proposition 11 (pp. 17–18, hierarchy gradients).
All of these are now independent completion targets under the expanded whole-paper scope. The prior main-theorem milestone does not certify their full statements.

## Proof-development checkpoints

The following notes preserve the successive proof checkpoints. Statements
about work remaining at an earlier checkpoint are superseded by the current
coverage table and the final completion milestone.

The all-order Riccati resolvent bridge proving Theorem 2(ii) is now checked.
`constructed_riccati_resolvent_identities` proves its coupled coefficient
recurrences, and `riccati_resolvent_coefficient_variation` proves the variation
formula modulo an explicit total spatial derivative. The diagonal coupling
has zero even coefficients. Its canonical Riccati input is proved equal to
the existing NLS hierarchy polynomials. Independent variation jets now prove
the actual physical integral variation, and Fourier test uniqueness identifies
both components with the certified Euler gradients. Smooth density extends
the diagonal recurrence to the exact Sobolev domain. Reciprocal phase scaling
and the actual distribution derivative give the corrected part (ii).

The independent scalar Hill/Miura hierarchy now has an all-order smooth
comparison. Its Riccati seed is `rho_0=-(u'+u^2)`, with scalar quadratic
coefficient one. `differentialRiccatiSeries_miura` proves the exact gauge
identity with the diagonal NLS series, and
`derivation_logarithmicPrimitiveCoefficient` constructs each correction as a
finite polynomial total derivative. Thus
`classicalNLSHamiltonian_odd_diagonal_eq_miuraHill` proves the factor-two
integral identity at every order. These scalar Hamiltonians are defined by
the scalar recurrence, independently of the NLS restriction; their first two
members equal the previously specified physical mKdV mass and energy.
`hasDerivAt_classicalMiuraHillHamiltonian` certifies their actual first
variations. `theorem1_smooth_miura_hierarchy` then proves both flow equality
and even vanishing at every smooth complex periodic order. The full H^m weak flow identity for this independent hierarchy is now proved
as described below; its source spectral identification remains open.

The scalar clause of Theorem 1 is now proved on its full complex H^m domain.
`sobolevPolynomialL2_eq_classical_of_jetOrder` realizes densities with jets
through m and at most 2m-1 total derivatives: at most one top L2 factor can
occur. Integration by parts supplies such a reduced density for S_(2m).
`sobolevEvenHamiltonian` integrates that actual L2 field and is entire
analytic. `sobolevEvenHamiltonian_eq_original` proves compatibility with the
existing physical hierarchy on every previously admissible input, and smooth
agreement uniquely determines this extension. Component-swap antisymmetry
then proves `theorem1_even_vanishing_sharp` for every complex H^m diagonal.
The new shared `fderiv_sobolevPolynomialL2Mean` also certifies the bounded
partial-jet covector as the actual Frechet derivative on all endpoint inputs
and directions. This supplies the variational foundation used by the full H^m weak
vector-field comparison below.

`theorem1_sharp_miura_hierarchy` now gives both clauses on every complex
H^m input for the independent Hill/Miura hierarchy. The scalar densities
are reduced directly, monomial by monomial, and their actual L2 means define
analytic Hamiltonians on H^m. Full Sobolev duality turns their actual Frechet
derivatives into unique opposite-order gradients. Smooth first variations
identify their Fourier integrals with the already certified physical
classical gradients; density gives the flow coefficient identity on every
nonsmooth input. `periodOneSobolevDistribution_derivative_eq` identifies the
multiplier with Mathlib's actual derivative, with exact physical period one.
In particular the scalar derivative is represented by each even NLS field
at order -m, and is not merely a formal Fourier sequence. The native extension is now proved as described below; the full source
spectral primitive-sheet/action identification remains an essential obligation.

The native scalar extension is now constructed directly on complex H^s as
`nativeMiuraHillHamiltonian s`, corresponding to K_(s+1). Removing the
linear total derivative from the scalar Hill Riccati coefficient lowers its
maximum total derivative count from 2s+1 to 2s. A single reduced scalar
polynomial then has jets through s, with at most two top L2 factors.
`sobolevPolynomialEndpointMean` constructs the bounded physical mean using
bilinear Parseval for those factors and continuous lower factors. The L2
mass is constructed separately when s=0. Every native Hamiltonian is analytic,
uniquely extends the independent classical hierarchy, and agrees with the
previous H^(s+1) construction. Its full actual Frechet gradient is represented
in H^(-s), and `theorem1_native_miura_hierarchy` uses that native gradient.

`exists_physicalMiuraDiscriminant_hamiltonian_error_bound` also proves an
all-order estimate for the independently constructed physical Hill trace at
energy r^2. Its phase is `-i*r + i*sum 2*K_m/(2*r)^(2m-1)`, with error bounded
by C/(2*|r|)^(2N) after N coefficients. This verifies actual operator trace
calibration rather than only a formal recurrence. A chosen free-normalized
spectral primitive and its source gap/action labels are still to be identified.

Theorem 5 is now proved as
`NLS.Articles.MKdVNLSHierarchies.theorem5_discriminant_identity`, for every
original complex H¹ input and every complex spectral parameter, including zero.
Its independently constructed Hill columns have the actual initial conditions
`(g(0),g'(0))=(1,0)` and `(0,1)`. The shared library proves absolute continuity
of each column and its derivative, the physical equation
`-g''+(u'+u²)*g=mu*g` almost everywhere, and uniqueness in that physical IVP
class. The discriminant is the literal sum `g1(1)+g2'(1)`. The period-one Fourier
representative and the `2*pi*i*n` derivative normalization are retained by the
existing even-insertion map. No Hill/ZS discriminant equality is an input to
the construction. The Hilbert operator spectrum, gap labels, action integrals
and Birkhoff identification required by Theorem 4 are still separate obligations.

## Source corrections and remaining qualifications

These observations prevent incorrect formal targets. The printed frequency
parity now has an explicit checked Lean counterexample.

1. Theorem 2(ii) and Proposition 11(ii) print `-i*J` in their recurrence,
   while the summation proof on p. 18 yields `R*partial S_(2m) =
   partial_x partial S_(2m-1)`, with `R=diag(i,-i)` defined on p. 13.
   The subsequent proof of Theorem 1 uses precisely this R identity, followed
   by multiplication by P. The corrected R recurrence is now proved at every
   order on the full printed complex Sobolev domain, with the actual derivative
   and no additional smoothness or real-type hypothesis.
2. Theorem 3 prints the factor `(-1)^m`. Its proof on p. 18 ends with
   `eta_(n,m)=omega_(n,2m)#` using the stated angle brackets and Theorem 1.
   `theorem3_m1_corrected` now proves the positive-sign equality on the
   full original real L2 domain. The original S2 differential is the actual
   physical momentum cotangent, and its original angle bracket is +2*pi*n.
   Every global independent K1 normal form has the same +2*pi*n raw action
   derivative, including at closed actions. `theorem3_printed_parity_counterexample`
   refutes the printed factor already at the zero profile, m=1 and n=1.
   The corrected comparison is now proved for EVERY m>=1 on the exact
   original real H^(m-1) domain, with unique continuation of the actual
   original NLS angle bracket through all closed actions.
3. The signed mean in the converse of Theorem 4(ii) needs a branch restriction
   or an appropriate sign-invariant replacement. The p. 13 proof recovers it
   from an inverse cosh. NLS spectral actions are unchanged by the phase
   rotation sending diagonal u to -u, whereas the signed mean changes sign.
   `theorem4_ii_mean_square_of_nls_actions` proves the global mean-squared
   correction, including zero mean, using the continued central primitive
   square at zero energy. No global signed-mean recovery is claimed.

## Existing proofs reused

- `NLS/ZakharovShabat/SobolevNLSHamiltonianHierarchy.lean`: original physical
  Hamiltonians, entire analyticity, mass and momentum calibration.
- `NLS/ZakharovShabat/SobolevNLSHierarchyTrace.lean`: physical all-order
  higher-action trace, including a common open complex neighborhood and
  absolute convergence. This trace identity does not identify the independent
  mKdV Hamiltonians.
- `NLS/ZakharovShabat/NLSRiccatiHierarchy.lean`: the exact differential
  recurrence and its uniqueness; its polynomial realization is in
  `NLSRiccatiPolynomials.lean`.
- `NLS/ZakharovShabat/SobolevRiccatiClassicalAgreement.lean`: actual Fourier
  coefficients and equality with classical smooth Hamiltonians.
- `NLS/ZakharovShabat/SobolevHamiltonianRescaling.lean` and
  `SobolevHamiltonianReflection.lean`: physical reciprocal rescaling and
  signed-swap parity on full complex Sobolev domains.
- `NLS/ZakharovShabat/SobolevOddHamiltonian.lean` and
  `SourceCorollaryH2.lean`: the sharper H^r construction of H_(2r+1),
  with independent reduced differential polynomials and physical integrals.
  This avoids needlessly rebuilding odd Hamiltonians.
- `NLS/DifferentialPolynomial/JetAlgebra.lean` and
  `IntegrationByPartsReduction.lean`: generic jet differentiation and
  graded integration by parts, available for the remaining variational work.

The accepted reference and the dissertation's completed 0.1–0.3 record were
read and left unchanged. The only local and remote branch present at initial
inspection was main; no alternative article proof was found to duplicate.

## New checked files and limits

- `NLS/ZakharovShabat/SobolevHierarchySymmetries.lean`: unsigned swap,
  simultaneous negation and covector symmetries. Reciprocal scaling itself
  is imported from the existing library rather than proved twice.
- `NLS/MKdV/HierarchyRestriction.lean`: complex diagonal inclusion,
  analyticity, all even-order vanishing in the current H^(2m-1) range,
  exact first mass, and the smooth K1/K2 physical factor-two identities.
- `NLS/Articles/MKdVNLSHierarchies/InitialChecks.lean`: article-facing
  statements with the exact current domains and explicit limitations.

The first phase added no aggregate NLS import, axiom, admitted proof, disabled
linter or essential unproved assumption. A conditional analogue is not being substituted
for a main theorem. There are 22 public declarations in these three modules,
15 theorems and 7 definitions. The transitive axiom audit additionally covers
generated auxiliaries; its initial audit passed for 35 declarations and allows only
`propext`, `Classical.choice` and `Quot.sound`.

The subsequent physical smooth m=2 identification, independent H¹ Hill/ZS
discriminant identity, all-order smooth physical first variations and expanded validation are
recorded in [the progress log](PROGRESS.md). Theorem 2 is now proved with its
matrix correction; the other main theorems remain incomplete.

## Worktree integration and reproduction

The user authorized separate worktrees on 2026-11-02. The article worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-mkdv-nls-hierarchies/outputs/dnls`,
on branch `articles/mkdv-nls-hierarchies`. The canonical main checkout remains
unchanged. App-managed creation rejected the canonical path because it was not
a registered workspace; attachment rejected the standard Git worktree as
unmanaged. Commands therefore use the explicit worktree path.

The earlier private staging validation is preserved in `validation.json` as a
historical first-phase record; its absolute paths refer to that private bundle.
The integrated files have additionally been focused-checked in this worktree
using `scripts/check_mkdv_nls.py`, with `autoImplicit=false` and warnings as
errors. `scripts/CheckMKdVNLSHierarchiesAxioms.lean` checks the new declarations
and all their transitive dependencies.

Set `ELAN_HOME` and `PATH` explicitly to the pinned toolchain. Invoke:

```sh
python3 scripts/check_mkdv_nls.py --imports-from /path/to/canonical/dnls
```

The checker uses an overlay of cached read-only imports. Every writable output
is inside this worktree's `.lake/build`; it neither copies the full cache nor
invokes a writing build in the canonical checkout. By default it checks the
article modules and their transitive axiom audit. Use `--full-audit` to compile
the aggregate and run a combined NLS/article transitive axiom audit under
`/tmp/diss-lean-article-build.lock`. `--module-only PATH` performs a focused
module check and can be repeated in dependency order. A focused check is not a
fresh full repository build. The article imports are explicit; additions to
the aggregate `NLS.lean` are deferred to sequential main integration.

The initial patch passed `git apply --check` before integration. Subsequent
commits and validation milestones are recorded in the article progress log.
Integration into main remains sequential, with shared foundations first.


Previous milestone: the independent all-order smooth scalar Hill/Miura
Hamiltonian and flow comparison. All 59 article/shared modules and the NLS
aggregate compiled; the targeted audit passed for 570 declarations and
auxiliaries and the combined audit for 45,750 NLS declarations, allowing only
the three standard axioms. The current inventory is 298 theorem/definition
declarations (230 theorems, 68 definitions). This used pinned cached imports,
not a rebuild of the entire dependency tree. Full details and remaining
Sobolev/spectral obligations are in [the progress log](PROGRESS.md).


Previous milestone: the scalar clause of Theorem 1 is proved on its exact
complex H^m domain, using the analytic physical even Hamiltonian extension.
The full endpoint Frechet first variation is also certified. All 63
article/shared modules and the NLS aggregate compiled; the targeted audit
passed for 639 declarations and auxiliaries and the combined audit for
45,820 NLS declarations, allowing only the three standard axioms. The public
inventory contains 330 theorem/definition declarations (256 theorems,
74 definitions). This used pinned cached imports, not a rebuild of the
entire dependency tree. The full vector-field and spectral obligations are
recorded in [the progress log](PROGRESS.md).


Previous milestone: both Theorem 1 clauses hold on every original complex H^m
input for the independently constructed scalar Hill/Miura hierarchy, with
actual Frechet gradients and the genuine physical distribution derivative.
All 71 article/shared modules and the NLS aggregate compiled. The targeted
transitive audit passed for 720 declarations and auxiliaries, and the
combined audit for 45,903 NLS declarations, allowing only the three standard
axioms. The public theorem/definition inventory is 369 declarations
(285 theorems, 84 definitions; aliases excluded). This used pinned cached
imports, not a rebuild of the entire dependency tree. Source spectral
identification, native scalar extension, and the remaining main-theorem
obligations are in [the progress log](PROGRESS.md).


Previous milestone: the scalar hierarchy is independently constructed on its
native complex H^(m-1) domains, including the L2 mass endpoint. The native
Proposition 6 identity holds there; the Theorem 1 comparison uses its native
gradient on all complex H^m inputs. The literal physical Hill trace has
all-order estimates with odd phase
coefficients 2*K_m. All 80 article/shared modules and the NLS aggregate
compiled. The targeted audit passed for 854 declarations and auxiliaries;
the combined audit passed for 46,038 NLS declarations, allowing only the
three standard axioms. The public inventory contains 424 theorem/definition
declarations (326 theorems, 98 definitions; aliases excluded). Validation
used pinned cached imports, not a rebuild of the entire dependency tree.
Remaining source primitive/action and main-theorem obligations are in
[the progress log](PROGRESS.md).


Previous milestone: the actual free-normalized Hill root and primitive equal
the original NLS canonical root and abelian primitive for real C1 periodic
Miura profiles at nonreal frequencies with Re z>0. Physical IVP uniqueness
identifies the independent Hill constructions, including zero energy for
the discriminant. The root sign and logarithm period are fixed by continuity
from the free potential along the quadratic Miura image of s*u.
The checked shared Hill primitive developments are reused unchanged from
`articles/kdv-convexity` at `d12831411f4ad00777304b6623dbb3226730b4eb`.
The full Sobolev and labeled gap/action extensions remain open; see
[the progress log](PROGRESS.md).

All 104 article/shared modules and the NLS aggregate compiled with Lean
4.33.1, autoImplicit=false and warnings as errors. The targeted transitive
axiom audit passed for 1,122 declarations and generated auxiliaries; the
combined audit passed for 46,306 NLS declarations. Only propext,
Classical.choice and Quot.sound are allowed. The public theorem/definition
inventory contains 598 declarations (470 theorems, 128 definitions; aliases
excluded), with SHA256 hashes for all 104 checked sources and both checker
files. Validation uses read-only pinned cached imports and private build
outputs; the entire dependency tree was not rebuilt from source. Canonical
main remains clean at c5bcf6344cd2e2628ae537e98b85bb9ec1849dec.


Previous milestone: the independent physical Hill root and primitive agree
with the original NLS functions on the full real H1 coefficient domain at
nonreal frequencies with Re z>0. This removes the C1 restriction on the
profile. Both sheets are constructed from the independent quasi-Hill IVP
discriminant, and agree with the shared scalar construction on C1 profiles.
The physical H1 trace and energy derivative and complex H1 source
analyticity on the admissible continuation domain are proved. Real-band,
gap/action and frequency identifications remain open.

All 110 article/shared modules and the NLS aggregate compiled with Lean
4.33.1, autoImplicit=false and warnings as errors. The targeted transitive
axiom audit passed for 1,250 declarations and generated auxiliaries; the
combined audit passed for 46,434 NLS declarations. Only propext,
Classical.choice and Quot.sound are allowed. The public theorem/definition
inventory contains 662 entries (514 theorems, 148 definitions; aliases and
structure declarations excluded), with 112 SHA256 source/checker hashes.
The checker can resume a failed run with --resume-from, requiring private
outputs for the previously checked prefix while retaining the complete
aggregate and axiom audits. This validation checked the unchanged prefix,
repaired an H1 adapter elaboration, then resumed there; both complete
audits passed. Validation uses pinned cached imports, not a rebuild of the
entire dependency tree.


Previous milestone: the actual H1-to-L2 Miura potential and shared physical
H2 Hill operator are identified with the original ZS periodic spectrum.
The discriminant comparison holds on every complex H1 input at every
complex energy. Multiplicities are preserved away from zero, with exact
ramification factor two at zero. Real H1 profiles have intrinsic ordered
nonnegative Hill labels with their exact characteristic multiplicities.
The 41 checked L2 Hill modules are reused unchanged from
`articles/kdv-estimates` at `5da8934e019a8a08f314988c311661754b89e925`.
Fixed endpoint indices, geometric multiplicity and action/frequency
identifications remain open.

All 156 article/shared modules and the NLS aggregate compiled with Lean
4.33.1, autoImplicit=false and warnings as errors. The final targeted
transitive axiom audit passed for 2,025 declarations and generated
auxiliaries; the combined audit passed for 47,204 NLS declarations. Only
propext, Classical.choice and Quot.sound are allowed. The public theorem/
definition inventory contains 1,082 entries (860 theorems, 222 definitions;
aliases and structure declarations excluded), with 158 SHA256 source/checker
hashes. The complete run used pinned read-only cached imports; the final
targeted prefix inventory was expanded and audited again independently.
The entire dependency tree was not rebuilt from source. Canonical main
remains clean at c5bcf6344cd2e2628ae537e98b85bb9ec1849dec.


Previous milestone: every intrinsic Miura Hill endpoint now equals the square
of the corresponding original canonical NLS endpoint on the full real H1
domain. The central Hill label is the square of either central NLS
endpoint. For every positive index the full closed Hill gap is exactly the
square image of the NLS gap, and the gaps collapse simultaneously.

The proof uses shared ordered-enumeration uniqueness, exact signed NLS
reflection, and analytic multiplicities, including the factor two at zero.
The Hill labels are constructed independently from the physical L2 Hill
operator; they are not defined by squaring the NLS endpoints. See
`GapIdentification.lean` in the article directory for the four source
exports. Geometric eigenspace multiplicity, real-band sheet extension and
spectral action/frequency identities remain open. Theorems 1, 3 and 4
remain incomplete.

All 163 article/shared modules and the NLS aggregate compiled with Lean
4.33.1, autoImplicit=false and warnings as errors. The targeted transitive
axiom audit passed for 2,130 declarations and generated auxiliaries; the
combined audit passed for 47,309 NLS declarations. Only propext,
Classical.choice and Quot.sound are allowed. The public theorem/definition
inventory contains 1,133 entries (906 theorems, 227 definitions; aliases and
structure declarations excluded), with 165 SHA256 source/checker hashes.
The complete sequential run used pinned read-only cached imports under the
shared build lock; the entire dependency tree was not rebuilt from source.
Canonical main remains clean at c5bcf6344cd2e2628ae537e98b85bb9ec1849dec.


Previous milestone: two actual action clauses of Theorem 4(i) are proved on
the full original real H1 domain. The central restricted NLS action
vanishes exactly when the literal physical mean vanishes, and the
restricted NLS actions at signed indices n and -n are equal. These are the
existing source contour actions, including collapsed gaps. At every
positive index their zero set is exactly collapse of the independent
physical Hill gap. The remaining comparison with the article's
contour-defined mKdV J_n is still open, so Theorem 4(i) remains partial.

The independent physical zero-energy trace is exactly 2*cosh(mean u) for
all complex H1 profiles. The proof solves the actual continuous-profile
ZS IVP explicitly and computes its monodromy trace. A reusable theorem
identifies the existing indexed NLS action with its real-gap cosine
integral; fixed-index endpoint reflection then proves action reflection.

Validation covers 169 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. Every source hash of the 163
unchanged modules matches the prior complete run; their private validated
outputs were reused. The six new modules and NLS aggregate compiled, and
the complete audits passed for 2,164 targeted declarations and auxiliaries
and 47,343 combined NLS declarations. Only propext, Classical.choice and
Quot.sound are allowed. The public inventory contains 1,157 entries
(929 theorems, 228 definitions; aliases and structures excluded), with
171 SHA256 source/checker hashes. The checks use pinned cached imports;
the entire dependency tree was not rebuilt from source.


Previous milestone: Lemmas 4 and 5 hold on the entire original real H1
right-half-plane cut complement, including real spectral bands. The full
Hill sheets are constructed as nonreal-energy limits of the independent
physical quasi-Hill sheets. The definitions contain no NLS root or
primitive. Checked NLS comparisons prove existence and analyticity of the
limits at every point of the physical labeled gap complement.

The actual Hill domain removes the ground half-line and every intrinsic
positive closed gap. Squaring matches it exactly with the original NLS
right-half-plane cut complement. The extended sheets retain the physical
L2 Hill trace, the exact energy derivative, the first-band branch sign
in (10), zero ground-endpoint normalization, and the actual path integral
in (11). They agree with the earlier independent source-continuation
constructions wherever those are admissible. The source real-H1 sheet
assertions are complete; weighted action contours, spectral Hamiltonians,
complex-source action neighborhoods and main Theorems 1, 3 and 4 remain open.

Validation covers 175 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. Every source hash of the 169
unchanged modules matches the previous validated milestone; their private
outputs were reused. The six new modules and NLS aggregate compiled, and
the complete audits passed for 2,223 targeted declarations and auxiliaries
and 47,402 combined NLS declarations. Only propext, Classical.choice and
Quot.sound are allowed. The public inventory contains 1,201 entries
(967 theorems, 234 definitions; aliases and structures excluded), with
177 SHA256 source/checker hashes. The checks use pinned cached imports;
the entire dependency tree was not rebuilt from source.


Previous milestone: **all three clauses of Theorem 4(i) are proved on the
full original real H1 domain** by `theorem4_i`. The actual NLS central
action vanishes exactly at zero physical mean; the positive NLS and mKdV
actions have identical zero sets; and I_(-n)#=I_n# at every signed index.
Zero mean and collapsed gaps are included throughout.

The mKdV actions are the literal source (13) integrals of F_Hill(mu)/mu
with factor -1/(4*pi). Actual isolating energy contours exist for every
positive index, lie in the physical gap complement, wind once about the
correct intrinsic Hill gap, and have winding zero about other positive
gaps and zero. All integer levels transform with the exact Jacobian
2*z, giving 2*J_(n,k)=I_(n,2k-2). Arbitrary close piecewise circuits satisfy
the actual winding formula; their winding-one values are independent of
the checked family. The positive real-gap formula is proved from these
integrals, not used to define the action. A mean-value point in the
positive frequency gap gives J_n=I_n/(2*zeta_n), without dividing by a
gap length or action.

Complex-source analytic action extensions, action factorization, angles,
frequency identities and spectral Hamiltonian calibration remain open.
Theorem 4(i) is complete; Theorems 1, 3 and 4(ii)-(iii) remain incomplete.

Validation covers 186 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. Every source hash of the 175
unchanged modules matches the previous validated milestone; their private
outputs were reused. The eleven new modules and NLS aggregate compiled,
and the complete audits passed for 2,581 targeted declarations and
auxiliaries and 47,549 combined NLS declarations. The targeted prefixes
include the reusable piecewise-contour and Cauchy-family developments.
Only propext, Classical.choice and Quot.sound are allowed. The public
inventory contains 1,269 entries (1,021 theorems, 248 definitions; aliases
and structures excluded), with 188 SHA256 source/checker hashes. The
checks use pinned cached imports; the entire dependency tree was not
rebuilt from source.


Previous milestone: the **actual physical Hill primitive has the convergent
source Laurent series with the independent native K coefficients at every
real finite-gap H1 source**. `equation12_finiteGap_native_laurent` proves

```text
F_Hill(z^2) + i*z = sum_(k>=0) i*(2*K_(k+1))/(2*z)^(2*k+1)
```

for every sufficiently large complex z with Re z>0. The normalization is
exact, and collapsed exterior gaps are filled by the independent
nonreal-energy limit. This does not assume primitive asymptotics,
smoothness, finite Fourier support or nonzero mean. The original physical
Hill labels define finite-gap; this is proved equivalent to finite support
of the contour-defined mKdV actions and to finite-gap of the original
diagonal NLS source. Its checked smooth Fourier representative preserves
every original coefficient and lies in every native scalar Sobolev domain.
`proposition6_finiteGap_native` gives the physical odd factor-two identity
and even vanishing at every order, including the L2 mass endpoint.

The proof reuses the checked NLS finite-gap bootstrap and convergent
physical Hamiltonian Laurent expansion, then groups the odd coefficients
and compares the filled primitive sheets. Extending/uniquely identifying
the source spectral Hamiltonians on the complete original complex native
Sobolev domains remains an essential Theorem 1 obligation. Theorems 1, 3
and 4(ii)-(iii) remain incomplete.

Validation covers 189 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 186 unchanged prefix module
source hashes match the previous f606044 milestone; their private outputs
were reused. The three new modules and NLS aggregate compiled, and the
complete targeted and combined audits passed for 2,614 and 47,582
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,288 entries
(1,037 theorems, 251 definitions; aliases and
structures excluded), with 191 SHA256 source/checker hashes.
The checks use pinned cached imports; the entire dependency tree was not
rebuilt from source.


Previous milestone: **Lemma 7 is complete**, including its ambient complex
L2 analytic-extension clause. `lemma7` chooses one open subset of the full
complex L2 pair-source space containing the entire real L2 diagonal before
any index or level is chosen. Every positive index n and every integer
level k has the analytic NLS extension I_(n,2k-2), with exact restriction
to 2*J_(n,k) on every original real H1 input. Zero mean and closed gaps are
included. The noncentral restriction is retained; no Laurent-weight claim
is made for a central contour enclosing zero.

The construction glues literal fixed-circle primitive integrals. Their
real-gap formula proves compatibility on real sources in each overlap;
real-form analytic uniqueness then proves compatibility on the full
complex overlap. The domain is a union of real-diagonal-centered source
balls, with each ball chosen once for the entire infinite contour family
and all integer levels. It is not an infinite intersection of local
neighborhoods. Different atlases agree on their complex overlaps, and
positive levels agree with the existing NLS higher actions there.

Four checked component-swap modules are integrated unchanged from
`articles/mkdv-below-l2` at `40d1959bf83cadfd29557cf1a3035bec7db6028c`.
Their exact signed endpoint reflection proves zero lies in the central
cut of every real L2 diagonal, so every noncentral isolating disc excludes
zero. The generic Laurent construction works at every finite source
exponent p>1. The induced mKdV extensions are complex analytic on a common
H1 neighborhood of all real H1 profiles; their actual Frechet derivative
retains the physical factor 1/2 and literal coefficient diagonal.

Action factorization, mKdV angles and frequency/bracket identifications
remain open. The source spectral Hamiltonian still needs its full native
Sobolev extension/uniqueness identification. Theorems 1, 3 and 4(ii)-(iii)
remain incomplete.

Validation covers 200 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 189 unchanged prefix module
source hashes match the previous 35c0200 milestone; their private outputs
were reused. Eleven added modules (four unchanged shared integrations and
seven new modules) and the NLS aggregate compiled. The complete targeted
and combined audits passed for 2,770 and 47,739 declarations respectively.
Only propext, Classical.choice and Quot.sound are allowed. The public
inventory has 1,376 entries (1,107 theorems and 269 definitions; aliases
and structures excluded), with 202 SHA256 source/checker hashes. The
checks use pinned cached imports; the entire dependency tree was not
rebuilt from source.


Previous milestone: **the angle-action bracket clause of Theorem 4(iii) is
proved on its full original real H1 angle domain** by
`theorem4_iii_angle_action`. For all positive m,n, whenever the angle's own
physical mKdV action J_m is nonzero, the actual restricted NLS angle has
Gardner bracket +delta_mn with J_n. No open-gap condition is imposed on
the action index n. Zero mean is included. The final assertion about the
independent mKdV angle plus this restricted NLS angle factoring through
actions and mean remains open, so Theorem 4(iii) as a whole is incomplete.

The scalar action is the complex L2 extension of the previously independent
physical Hill contour. Its actual Frechet derivative supplies its bilinear
L2 gradient. The gradient's spatial derivative is proved square summable
and identified with the actual period-one tempered distribution derivative.
This literal Gardner direction is proved to have diagonal equal to the
original NLS Hamiltonian direction of I_n-I_(-n), with the original signs.
The angle differential is constructed from the actual normalized NLS phase
and proved to be its pullback; it is not prescribed by the bracket identity.

The proof first differentiates the genuine integer-level Laurent contours,
then integrates the physical discriminant-gradient recurrence at every
Fourier mode. The 2*pi*i*m multiplier and the action's factor 1/2 remain
explicit. The resulting transfer holds for every actual bounded source
cotangent. Original NLS canonical identities give the angle bracket, and
original NLS action commutation shows that every signed restricted NLS
action, including I_0, commutes with every J_n under the Gardner bracket.
This invariance is a dependency of Theorem 4(ii); its normal-form
factorization still needs proof.

Four further checked component-swap modules are integrated unchanged from
`articles/mkdv-below-l2` at `9a2d23c9f2cf513921eb89cdb69b9a57eed3a3fc`.
They supply the actual reflected action differential and anti-Poisson sign,
including closed gaps. Theorem 1's source spectral Hamiltonian extension/
uniqueness step, mKdV angle/action factorizations, corrected mean recovery
and frequency identification remain essential open obligations.

Validation covers 216 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 200 unchanged prefix module
source hashes match the previous 01cdacc milestone; their private outputs
were reused. Sixteen added modules (four unchanged shared integrations and
twelve new modules) and the NLS aggregate compiled. The complete targeted
and combined audits passed for 2,905 and 47,874 declarations respectively.
Only propext, Classical.choice and Quot.sound are allowed. The public
inventory has 1,452 entries (1,171 theorems and 281 definitions; aliases
and structures excluded), with 218 SHA256 source/checker hashes. The
checks use pinned cached imports; the entire dependency tree was not
rebuilt from source.


Previous milestone: **The converse action clause of Theorem 4(ii) is proved** by
`theorem4_ii_mkdv_actions_of_nls_actions` on every original real H1 input.
Each positive physical mKdV action J_n is a holomorphic, hence real
analytic, function of the complete original signed NLS action sequence
in complex ℓ¹. The action-space domain is open and contains the action
image of the entire real L2 diagonal. Its neighborhood may depend on n.
Zero mean and every collapsed gap are included. The stronger shared
result gives such a factor for every integer physical action level
J_(n,k), retaining the contour normalization 2*J_(n,k)=I_(n,2k-2).

`theorem4_ii_mean_square_of_nls_actions` proves the sign-invariant
correction of the printed converse mean claim: the literal mean squared
is also analytic in the original NLS actions, including at zero mean.
The actual central primitive square is continued through its central
cut and evaluated at zero energy. A Cauchy formula in symmetric endpoint
coordinates proves ambient source analyticity through endpoint collision.
Its real arcosh formula and the independent trace identity
Delta(0)=2*cosh(mean) identify its value with the zero Fourier mode
squared. This does not recover the signed mean without a sign branch.

The reusable descent theorem applies to a scalar analytic function on
an arbitrary open source domain. It requires invariance only between
real sources inside that domain. Actual inverse charts and real lifts
stay inside it. Real action invariance supplies complex tail sign
symmetries and rotation stationarity, and quadratic descent includes
collapsed tail actions. Real representatives in each nonnegative action
ball give compatibility on complex overlaps and uniqueness of the glued
factor. No artificial extension or invariance outside the source domain
is assumed. For Laurent actions, equal canonically labelled spectral
data give literally equal real-gap integrands; the checked NLS inverse
spectral theorem identifies action fibers with isospectral sets.

The forward assertion that each restricted NLS action factors through
physical mKdV actions and mean remains essential. Independent mKdV
angles and the final angle-sum factorization, the full native-domain
source spectral Hamiltonian identification in Theorem 1, and corrected
frequency comparison in Theorem 3 remain open. Theorems 1, 3 and
4(ii)-(iii) as whole statements are still incomplete.

Validation covers 224 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 216 unchanged prefix module
source hashes match the previous 055b907 milestone; their private outputs
were reused. Eight added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 2,924 and 47,895
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,468 entries (1,187 theorems and
281 definitions; aliases and structures excluded), with 226 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


Latest milestone: **Theorem 1 is complete on its original complex Sobolev domains** in
`theorem1`. At every integer m>=1 and every complex H^m input, the
restricted even NLS vector field equals the diagonal Gardner vector field
of the physical spectral mKdV Hamiltonian, and the even Hamiltonian
vanishes. The scalar Hamiltonian is constructed on the entire native
complex H^(m-1) domain, including the L2 mass endpoint. Its actual Frechet
derivative supplies the native Sobolev bilinear gradient, and Gardner
differentiation is the actual period-one tempered distribution derivative.
`proposition6` gives the odd factor-two identity on the entire native
domain and even vanishing on H^m.

The remaining spectral identification is supplied by literal coefficient
limits of the independent physical Hill discriminant. At frequencies
r_j=pi*(j+1/2), the free cosine vanishes and its hyperbolic sine carrier
has norm one. Dividing the actual trace by that carrier and applying one
fixed analytic inverse of sinh at zero extracts an actual small phase.
All-order physical monodromy estimates recover every phase coefficient
by a recursive scaled limit after subtracting the previous coefficients.
Every limit is proved to exist for every smooth complex periodic profile,
including infinitely many open gaps. No convergent exterior Laurent
series is assumed in this general smooth argument.

The scalar spectral K_(s+1) is -i/2 times coefficient number 2*s, giving
exactly the source normalization. It agrees with the independent scalar
Hill/Riccati hierarchy on all smooth complex profiles. Smooth density
then constructs and uniquely identifies its continuous extension on the
complete native complex H^s space. This extension exists, is entire
analytic, and equals the independent native scalar Hamiltonian. The
spectral extension, its analyticity and its gradient are constructed,
not caller-supplied assumptions. No diagonal finite-gap density premise
is needed. `equation12_spectral_native_laurent` also identifies precisely
these spectral Hamiltonians in the original ground-normalized finite-gap
physical Hill primitive's convergent Laurent series.

Theorems 1 and 2, Theorem 4(i), the converse J_n clause of Theorem 4(ii)
and its corrected mean-squared recovery, and the angle-action clause of
Theorem 4(iii) are proved. The forward factorization of restricted NLS
actions through mKdV actions and mean, the independent mKdV angles and
final angle-sum factorization, and the corrected full frequency comparison
in Theorem 3 remain essential open obligations. The overall goal remains
incomplete.

Validation covers 230 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 224 unchanged prefix module
source hashes match the previous 1fd6953 milestone; their private outputs
were reused. Six added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 3,016 and 47,987
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,513 entries (1,221 theorems and
292 definitions; aliases and structures excluded), with 232 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


## Complete physical action flows toward the remaining normal forms

`theorem4_complete_action_flows` constructs the complete commuting
2*pi-periodic Gardner flows of every physical J_n on the full original
real H1 space, including closed gaps and zero mean. Their actual L2
Gardner equation, intrinsic uniqueness, conservation of every physical
J_m and signed original NLS I_m, and conservation of the signed mean
are proved. A closed selected action gives a stationary trajectory.
The construction uses opposite NLS rotations at n and -n; analytic ODE
uniqueness proves independence of the chosen normalized NLS coordinate
family and preservation of the actual equal-component diagonal.
The native weighted lifts are continuous in every original integer H^s
norm, including L2, and retain the original Fourier coefficients.

This is necessary action-torus machinery, not a completed independent
mKdV Birkhoff chart. The forward action factorization, independent mKdV
angles, final angle-sum factorization and corrected frequency comparison
remain open. Signed-mean conservation along each connected orbit does
not assert signed-mean recovery from NLS actions.

Validation covers 242 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 230 unchanged prefix module
source hashes match the previous d85907d milestone; their private outputs
were reused. Twelve added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 3,161 and 48,131
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,606 entries (1,300 theorems and
306 definitions; aliases and structures excluded), with 244 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


## Exact global angle transport and regular action strata

`theorem4_iii_global_angle_transport` integrates the checked angle-action
bracket along the complete physical Gardner group. The actual spectral
phase exp(2*i*theta_m) is multiplied by exp(2*i*t) along J_m and is
constant along every other J_n. This holds for every real time on the
full original real H1 angle domain J_m!=0; the action index n may have
a closed gap. The selected angle domain is preserved by isospectrality.
The general source result permits independent choices of the normalized
angular family and the Birkhoff family used to construct the flow.

The physical Gardner vectors for all open actions are linearly
independent. A vector vanishes exactly when its physical action closes.
Every finite linear combination of the open physical action Frechet
differentials and the literal mean differential has unique coefficients,
both for the ambient complex L2 extensions and on the original H1
domain. Other gaps may close and zero mean is included. These results
supply regularity needed for action coordinates. The global independent
mKdV chart, forward action factorization, final angle-sum factorization
and corrected frequency comparison remain open.

Validation covers 248 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 242 unchanged prefix module
source hashes match the previous ba19069 milestone; their private outputs
were reused. Six added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 3,182 and 48,152
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,626 entries (1,320 theorems and
306 definitions; aliases and structures excluded), with 250 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


## Constructed finite local physical action sections

`theorem4_finite_action_submersion` proves that any finite collection of
open physical actions and the literal mean has a surjective actual
Frechet derivative on the complex H1 space at every original real H1
base point. `theorem4_finite_action_sections` constructs a holomorphic
section through that point. It realizes every nearby selected complex
action and mean value exactly and stays inside any prescribed H1
neighborhood. Its actual derivative is a constructed bounded linear
right inverse. At the base point its action values equal the independent
physical Hill contour actions. Zero mean and arbitrary omitted closed
gaps are included.

These finite local complex sections are now complemented by the real-preserving
sections described below. The global inverse action-coordinate geometry, collapsed selected-action
coordinates and independent global mKdV chart remain open, together with forward
factorization, final angle-sum factorization and corrected frequency comparison.

Validation covers 253 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 248 unchanged prefix module
source hashes match the previous 96c107c milestone; their private outputs
were reused. Five added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 3,201 and 48,171
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,639 entries (1,331 theorems and
308 definitions; aliases and structures excluded), with 255 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


## Real-preserving local physical action sections

`theorem4_real_finite_action_sections` constructs real analytic sections
on the full original real H1 space through any base point, including
zero mean. Any finite collection of its open physical actions and the
literal signed mean can be prescribed independently nearby. The section
stays inside any chosen real H1 neighborhood and keeps each selected
action positive. Its actual derivative is a constructed bounded real
right inverse; `theorem4_real_finite_action_submersion` proves actual
real derivative surjectivity.

The real space consists of Fourier coefficients with conjugate index
reflection, with the original H1 norm. The physical real projection,
closed Banach real form, action-value reality and actual derivative
reality are proved. The real analytic inverse theorem supplies the
section on a constructed affine slice. No real chart or inverse is an
extra hypothesis. The independent global mKdV chart, inverse action-coordinate
geometry and collapsed selected-action coordinates, forward factorization,
final angle-sum factorization and corrected frequency comparison remain
open; the main-theorem goal remains incomplete.

Validation covers 259 article/shared modules with Lean 4.33.1,
autoImplicit=false and warnings as errors. All 253 unchanged prefix module
source hashes match the previous 9af5306 milestone; their private outputs
were reused. Six added modules and the NLS aggregate compiled. The
complete targeted and combined audits passed for 3,242 and 48,212
declarations respectively. Only propext, Classical.choice and Quot.sound
are allowed. The public inventory has 1,662 entries (1,349 theorems and
313 definitions; aliases and structures excluded), with 261 SHA256
source/checker hashes. The checks use pinned cached imports; the entire
dependency tree was not rebuilt from source.


## Full native weighted action sequence

The entire action sequence is now constructed in its native norm:
`miuraSobolevActionSequence s` takes values in weighted complex l1 with
weight (1+n)^(2s+1) on positive indices. One open complex H^s neighborhood
of the whole physical real form carries this analytic map for every
integer s>=0. Coordinatewise analyticity is upgraded to actual Banach
analyticity using a locally uniform weighted l1 bound. Central and
negative entries are zero solely to encode the positive-index target
inside Z.

On every original real H1 input, `miuraH1ActionSequence_physical` identifies
every positive coordinate with the independently defined physical Hill
contour action. The weight is exactly (1+n)^3. The literal weighted
absolute series is summable, and the whole action sequence together with
the signed mean has one complex H1 analytic extension. The complete
physical Gardner action flows conserve this entire weighted action/mean
map. Zero mean and arbitrary collapsed gaps are included.

The full native action map and its topology are therefore available.
Global inverse action-coordinate geometry and the independent mKdV
Birkhoff chart, forward factorization, final angle-sum factorization and
corrected frequency comparison remain open.

The exact paper weight is also supplied. `miuraPaperSobolevActionSequence s`
uses 1+|n|^(2s+1), with a coefficient-preserving continuous linear
equivalence to the normalized spectral-estimate weight. The checked
comparison constants are 1 and 2^(2s). Thus the full action-map result
retains the original topology, including the action target associated
with the paper's h^s_* model.

Validation: all 259 unchanged prefix source hashes match c1ee709; their private outputs were reused. The ten added modules and NLS aggregate compiled with warnings as errors. Targeted and combined transitive audits passed for 3,333 and 48,303 declarations respectively, using only propext, Classical.choice and Quot.sound. The public inventory is 1,707 declarations (1,382 theorems and 325 definitions; aliases and structures excluded), with 271 frozen mathematical source/checker hashes. Pinned cached imports were used; the entire dependency tree was not rebuilt from source.


## Physical mass trace and the zero-action fiber

On every original real H1 profile, the actual native mass Hamiltonian
satisfies

    K1(u) = [u]^2/2 + sum_(n>=1) 2*pi*n*J_n(u).

Every J_n is the independent physical Hill contour action, and the
series converges. `physical_actions_mean_determine_L2_norm` identifies
the resulting scalar L2 norm exactly. Zero mean and arbitrary closed
gaps are included. The proof differentiates the actual Banach analytic
weighted action map, identifies its nonconstant cotangent with the
physical mass cotangent, and integrates along original fixed-mean H1
affine lines. Constants have zero positive actions by the actual
angle-momentum bracket, without assuming an endpoint labeling there.

The original source Birkhoff Jacobian sends physical translation to
the signed 2*pi*n rectangular rotations, including collapsed selected
gaps. Its bounded inverse transports the unconditional Hilbert mode
expansion. Pairing signed modes and using the checked Gardner transfer
then gives an unconditional L2 sum of the positive physical action
fields equal to the original scalar spatial derivative.

`physical_zero_action_fiber_unique` proves that each fixed-mean leaf
has one zero-action profile: its literal constant mean. This supplies
a global norm identity and zero-fiber rigidity for the remaining
action-coordinate construction. General nonzero-fiber inverse geometry,
the independent global mKdV chart, forward factorization, final angle-sum
factorization and the complete corrected frequency comparison remain
open. The overall main-theorem goal remains incomplete.

Validation: all 269 unchanged prefix module source hashes match 0e4eed8; their private outputs were reused. The twelve added modules and NLS aggregate compiled with warnings as errors. Targeted and combined transitive audits passed for 3,448 and 48,382 declarations respectively, using only propext, Classical.choice and Quot.sound. The public inventory is 1,748 declarations (1,419 theorems and 329 definitions; aliases and structures excluded), with 283 frozen mathematical source/checker hashes. Pinned cached imports were used; the entire dependency tree was not rebuilt from source.


## Original L2 endpoint action geometry

The full original L2 action sequence is complex analytic into weighted l1
of order one near the entire physical real form. Every positive coordinate
is the actual inverse-frequency Laurent extension, and on original real H1
it equals the independent physical Hill contour action. The signed mean
pairs with the full sequence. A direct unit-weight physical realization
avoids transporting the original L2 domain through a different model.

The mass trace now holds at the complete original L2 endpoint. Native K1,
the exact original scalar L2 norm and the convergent first action moment
are identified. The full native action/mean target norm controls the source
L2 norm, and convergence of that data prevents norm loss at a coefficient
limit. Real H1 symmetric Fourier density proves the endpoint extension.

`native_L2_action_mean_map_proper` proves properness of the actual real L2
action and signed-mean map. `native_L2_action_mean_fiber_compact` gives
compact complete fibers in original L2. The spectral input is proved:
actual canonical endpoints and discriminants converge under bounded
Fourier limits; the moving arcosh cosine profile converges uniformly on
compact parameter sets. Every positive diagonal gap stays strictly away
from zero, including collapsed gaps, so its inverse-frequency integral
converges as well. The mass trace upgrades subsequential coefficient
convergence to strong L2 convergence. No spectral-continuity premise or
independent mKdV chart is supplied by the caller.

Properness is a global compactness result. General nonzero-fiber inverse
geometry, surjectivity of the positive action cone, collapsed Cartesian
coordinates and the independent mKdV chart remain open, as do forward
factorization, final angle-sum factorization and full corrected frequency
comparison. No H1 compactness assertion is inferred from the L2 result.

Validation: all 294 article/shared modules have validated private outputs. The 281 unchanged prefix source hashes match d8b5061 and their outputs were reused; all 13 added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,533 declarations/auxiliaries and the combined audit for 48,467 NLS declarations, using only the standard allowed axioms. All 296 mathematical source/checker hashes match the frozen inputs. The public inventory is 1,797 declarations (1,459 theorems and 338 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source.


## Selected Cartesian coordinates through closed physical actions

The actual Laurent contour is factored by the squared canonical gap without
inverting a gap or action in the regularized contour. Rationalizing the
normalized root subtracts its zero-gap baseline tau-z; the baseline has
zero contour integral. The remaining fixed-circle factor is Banach analytic.
At a closed gap its value is the exact Cauchy residue -i/4 times the
holomorphic spectral weight and full Abelian quotient at the midpoint.

Real open-gap density identifies the level-one contour factor with the
independently normalized NLS action at closed gaps. The real-form identity
principle identifies their complex germs. A chart-independent normalized
inverse-frequency action is consequently analytic near every real diagonal.
The physical ratio J_n/I_n is real and strictly positive for every positive
index. Its closed-gap value is 1/(2*tau_n), retaining the actual midpoint
and the physical one-half normalization. Its principal root is analytic
through a closed selected action.

Multiplying the original NLS Cartesian pair by this root, with the second
coordinate negated, constructs an actual selected pair on original complex
L2. It is analytic near every physical profile, real on the physical locus,
and has squared radius exactly 2*J_n. On original H1 this J_n is the
independent physical Hill-contour action. A zero action is equivalent to
collapse of precisely its selected Cartesian pair. Zero mean and other
closed actions are unrestricted.

This proves selected-coordinate regularity through collapsed actions.
Infinite weighted Cartesian sequence analyticity, Gardner canonicity,
an independent global mKdV inverse, general nonzero-fiber geometry,
surjectivity, forward action factorization, independent angles/final
angle-sum factorization and full corrected frequency comparison remain
essential. The overall main-theorem goal stays active.

Validation: all 301 article/shared modules have validated private outputs. The 294 unchanged prefix source hashes match bcb9049 and their outputs were reused; all seven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,625 declarations/auxiliaries and the combined audit for 48,559 NLS declarations, using only the standard allowed axioms. All 303 mathematical source/checker hashes match the frozen inputs. The public inventory is 1,837 declarations (1,492 theorems and 345 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source.


## Full native complex L2 Cartesian sequence and properness

A single real-centered complex ball now supports every normalized Laurent
factor. Real open-gap density followed by holomorphic continuation on the
whole ball identifies all ordinary factors there; no infinite intersection
of index-dependent neighborhoods is used. The existing actual Laurent
bound can be cancelled at open complex gaps. At closed complex gaps the
exact midpoint formula gives the same inverse-frequency estimate.

The scaled physical ratios (1+|n|)*J_n/I_n form an actual bounded sequence
that is analytic in its full linfinity Banach norm. On a real diagonal,
the spectral mean-value formula and endpoint displacement estimate give
a common strictly positive real lower bound for every positive index.
Norm continuity of the sequence therefore gives one complex neighborhood
where all principal roots are analytic simultaneously. Their native
half-order weighted moduli are uniformly bounded, including at every
closed selected gap.

These estimates assemble the original selected Cartesian pairs into an
actual full sequence in the weighted Hilbert pair of order one half.
The map is complex Banach analytic near every original physical real L2
profile. Every positive raw coefficient equals its constructed pair;
nonpositive entries are zero solely to encode the positive-index target.
The weighted Hilbert product constructs the full continuous quadratic
radius map, which recovers exactly the entire actual weighted l1 action
sequence. With the literal signed mean, the full Cartesian map is proper
in original physical L2, so every complete Cartesian/mean fiber is compact.

This closes the full complex L2 sequence-analyticity dependency. It does
not prove Gardner canonicity or infinite-dimensional invertibility.
Higher native Sobolev Cartesian maps, general nonzero-fiber uniqueness,
surjectivity, forward action factorization, independent angles/final
angle-sum factorization and full corrected frequency comparison remain
essential. The overall main-theorem goal remains active.

Validation: all 310 article/shared modules have validated private outputs. The 301 unchanged prefix source hashes match 50c22c7 and their outputs were reused; all nine added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,685 declarations/auxiliaries and the combined audit for 48,619 NLS declarations, using only the standard allowed axioms. All 312 mathematical source/checker hashes match the frozen inputs. The public inventory is 1,874 declarations (1,521 theorems and 353 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source.


## Full native Cartesian maps on the integer Sobolev scale

The actual physical action roots times the half-order weight now form a
bounded complex Banach analytic symbol sequence. The independently checked
original weighted NLS map is pulled back along the actual scalar diagonal
at every integer Sobolev order. Its full normalized coordinate pair has
precisely the scalar source weight; original Fourier coefficients are
preserved by all native source transports.

Multiplying these actual normalized NLS sequences by the bounded symbol
gives the full Cartesian map H^s -> h^(s+1/2) for every integer s>=0.
Each map is complex Banach analytic on an open native source neighborhood
containing the entire physical real H^s subspace. Every raw coefficient
agrees with the original L2 family, and every output coordinate is real
on physical profiles. Closed selected actions, infinitely many other
closed actions, and zero mean are included without additional conditions.

The square of the Cartesian weight is exactly the actual native action
weight of order 2*s+1. The full analytic quadratic radius projection
therefore recovers the complete original weighted l1 action sequence at
every order. The original physical H1 space ScalarDomain 2 has its full
native order-three-halves map, complex Banach analyticity and exact
independent physical Hill-contour action radii.

This closes native Sobolev Cartesian sequence analyticity. Gardner
canonicity, an independent global inverse, general nonzero-fiber
uniqueness/surjectivity, forward action factorization, independent
angles/final angle-sum factorization and the full corrected frequency
comparison remain essential. Properness is currently proved only in
original L2. The overall main-theorem goal remains active.

Validation: all 316 article/shared modules have validated private outputs. The 310 unchanged prefix source hashes match 9cba64b and their outputs were reused; all six added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,741 declarations/auxiliaries and the combined audit for 48,675 NLS declarations, using only the standard allowed axioms. All 318 mathematical source/checker hashes match the frozen inputs. The public inventory is 1,908 declarations (1,547 theorems and 361 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source.


## Actual free Jacobian equivalence and nonlinear native L2 inverse chart

The exact free physical ratio is 1/(2*pi*n), and its positive root fixes
the Fourier scaling of the actual Cartesian derivative. The derivative
of the scaling contributes zero at the free profile because both original
NLS rectangular coordinates vanish there. Differentiating the actual map
therefore gives the signed and scaled scalar Fourier transform.

The positive-index target is now a closed complex Banach subspace of the
native half-order Hilbert space, paired twice and with the literal mean.
Its bounded projection keeps every physical coordinate. A uniform lower
bound for scaled physical ratios bounds the inverse scaling symbol at
every physical diagonal, including closed actions. The explicit free
inverse reconstructs the two signed Fourier coefficients from the positive
Cartesian pair, and reconstructs the zero mode from the signed mean.

Both operator inverse identities are proved on the entire original
complex L2 space and the entire natural native Cartesian/mean target.
They are not finite-mode identities or abstract invertibility hypotheses.
The actual free derivative is consequently a bounded complex linear
equivalence. A reusable inverse theorem for different native Banach
source/target spaces constructs the original nonlinear map's analytic
inverse on full open neighborhoods of zero, with both exact inverse
identities, image equality and bijectivity. The physical real L2 map into
the natural positive target is also globally proper.

The nonlinear inverse is currently a complex L2 local chart at the free
profile. Real-form and higher-Sobolev inverse restrictions, Gardner
canonicity and a global inverse at general profiles, general nonzero-fiber
uniqueness/surjectivity, global forward action factorization, independent
angles/final angle-sum factorization and full corrected frequency comparison
remain essential. The overall main-theorem goal remains active.

Validation: all 328 article/shared modules have validated private outputs. The 316 unchanged prefix source hashes match 809e52c and their outputs were reused; all 12 added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,876 declarations/auxiliaries and the combined audit for 48,810 NLS declarations, using only the standard allowed axioms. All 330 mathematical source/checker hashes match the frozen inputs. The public inventory is 1,964 declarations (1,588 theorems and 376 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source.


## Native nonlinear inverse charts at zero on every integer Sobolev space

The actual free positive Cartesian Jacobian is now identified with an
explicit bounded linear equivalence at every native integer Sobolev order.
Even source weights commute with the two signed Fourier modes, while the
Cartesian half-order weight factorization gives the exact target transport.
The literal signed mean is preserved. A generic Banach-equivalence lemma
keeps mean transport separate from concrete weighted-space instance data;
all proofs check under the existing kernel and heartbeat limits.

The actual nonlinear maps therefore have analytic inverse charts on full
open complex H^s and positive-index h^(s+1/2) times complex-mean neighborhoods
of zero, for every integer s>=0. Both inverse identities, image equality,
bijectivity and Banach analyticity of the forward and inverse maps are proved
in their complete native norms. The original complex H1 domain ScalarDomain 2
itself has the corresponding full order-three-halves inverse chart; its
actual derivative is the transported bounded free equivalence.

These are local inverse results at the free profile. Physical real-form
inverse restrictions, a global inverse and Gardner canonicity at general
profiles, general nonzero-fiber uniqueness/surjectivity, global forward
action factorization, independent angles/final angle-sum factorization and
full corrected frequency comparison remain essential. Global properness
remains an original physical real L2 result. The main-theorem goal stays active.

Validation: all 335 article/shared modules have validated private outputs. The 328 unchanged prefix source hashes match 9640ed7 and their outputs were reused; all seven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 3,937 declarations/auxiliaries and the combined audit for 48,871 NLS declarations, using only the standard allowed axioms. All 337 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,001 declarations (1,615 theorems and 386 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Physical real L2 inverse chart and globally unique small Cartesian data

The genuine physical real source is the closed conjugate-reflection form
of the original L2 space. A bounded real projection onto this form is now
proved. The genuine target is the closed real subspace of the positive
half-order Hilbert pair and the literal real signed mean: every raw
Cartesian coefficient and the mean have zero imaginary part.

The explicit free Fourier Jacobian and its bounded inverse preserve these
real forms. Their restrictions form an actual bounded real equivalence,
which is identified with the derivative of the original nonlinear real
Cartesian map. The map agrees exactly with the existing complex Cartesian
representatives after inclusion and is real Banach analytic at every
physical profile. It has an analytic inverse between full open real
source/target neighborhoods of zero, with exact inverse identities, image
equality and bijectivity. Every complex left inverse germ also preserves
physical reality on nearby real target data.

The actual real-target map remains globally proper. The original mass/action
trace proves its zero fiber consists only of zero. A reusable topological
lemma combines a singleton fiber, properness and a local chart to exclude
extra distant preimages near that fiber. Consequently, every point in a
full open real native target neighborhood of zero has exactly one preimage
in the entire physical real L2 space. Closed actions and zero mean are
included.

These results do not identify a global Gardner-canonical mKdV Birkhoff map.
Higher-Sobolev physical real inverse restrictions, the general-profile
Jacobian/inverse and Gardner canonicity, general nonzero-fiber geometry and
surjectivity, forward action factorization, independent angles/final
angle-sum factorization and full corrected frequency comparison remain
essential. The main-theorem goal stays active.

Validation: all 344 article/shared modules have validated private outputs. The 335 unchanged prefix source hashes match ff343bc and their outputs were reused; all nine added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,024 declarations/auxiliaries and the combined audit for 48,958 NLS declarations, using only the standard allowed axioms. All 346 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,038 declarations (1,644 theorems and 394 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Physical real inverse charts and regularity on the entire integer Sobolev scale

Positive symmetric weighting is now a bounded real equivalence of the
original conjugate-reflection source forms. The positive target weight
transport preserves and reflects coefficientwise Cartesian reality and
the literal real mean. Its preimage of the checked L2 real form is proved
to be exactly the closed native real Hilbert target, with the inherited
h^(s+1/2) norm, for every integer s>=0.

The actual nonlinear physical real map agrees after inclusion with the
existing complex native map and is real Banach analytic throughout the
physical source. Its actual free derivative is the transported bounded
real Fourier equivalence. Full open real native source/target neighborhoods
of zero admit an analytic inverse with both exact inverse identities,
image equality and bijectivity. The literal original real H1 domain has
its own full order-three-halves chart. Every native complex left inverse
germ preserves physical reality on nearby real native data.

Bounded source and Cartesian target inclusions preserve all raw Fourier
coefficients and the signed mean, and the actual nonlinear maps commute
with these inclusions. For each integer s>=0, a full open native real target
neighborhood therefore has an analytic H^s inverse which is the only
physical L2 preimage. This quantifies over every possible physical L2
preimage: small native target data force that preimage to have the native
Sobolev regularity. The proof uses the prior original L2 global uniqueness
near zero, not a general-profile global inverse assumption. The size of
the native neighborhood may depend on s.

The physical real higher-Sobolev zero-chart restriction is now closed.
General-profile Cartesian Jacobian/inverse and Gardner canonicity, global
nonzero-fiber geometry and surjectivity, forward restricted-NLS-action
factorization, independent angles/final angle-sum factorization and full
corrected frequency comparison remain essential. Global properness is
still an original physical real L2 result. The main-theorem goal stays active.

Validation: all 356 article/shared modules have validated private outputs. The 344 unchanged prefix source hashes match 2bcaf01 and their outputs were reused; all twelve added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,129 declarations/auxiliaries and the combined audit for 49,063 NLS declarations, using only the standard allowed axioms. All 358 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,098 declarations (1,689 theorems and 409 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Complete Cartesian action rotations and original mixed Gardner brackets

The actual diagonal Laurent actions, the regularized physical action ratio,
and its chosen principal square root are now proved invariant on every
actual real diagonal isospectral set at every finite exponent p>1. The
closed-gap branch uses the reciprocal of twice the actual spectral midpoint;
the open-gap branch uses the checked normalized action factorizations.
The result retains every signed index n!=0 and does not divide by a zero
action.

The original complex rectangular NLS map has an exact paired-action
transport identity. With the checked negative sign in the second physical
Cartesian coordinate, every positive physical pair rotates clockwise at
unit speed along its selected complete Gardner action orbit and stays
fixed along every other action orbit. This literal identity holds for all
real times and every integer Sobolev order s>=0, including all closed
actions. It is also proved for the actual full native positive target,
with the signed mean and the entire native weighted action sequence fixed.
Every original signed NLS action is invariant on these same complete
physical native orbits.

The zero-energy trace Delta(0)=2*cosh(mean) is extended from the original
complex H1 formula to all original complex L2 profiles by finite Fourier
density. Actual isospectrality fixes the physical real mean squared, and
continuity on each complete orbit fixes the signed mean, including zero
mean, at every native integer Sobolev order.

Differentiating the literal rotation on the original real H1 domain and
using the already identified actual Gardner trajectory proves
{X_m,J_n}=delta_mn Y_m and {Y_m,J_n}=-delta_mn X_m. Both sides use the actual
original L2 Frechet derivatives and actual scalar-gradient Gardner field.
These mixed Cartesian-action bracket identities require no open-action
hypothesis, in either selected index.

General Cartesian-Cartesian brackets and Gardner canonicity, the global
Cartesian inverse/Jacobian at general profiles, global nonzero-fiber
geometry and surjectivity, forward restricted-NLS-action factorization,
independent angles/final angle-sum factorization and the full corrected
frequency comparison remain essential. The main-theorem goal stays active.

Validation: all 366 article/shared modules have validated private outputs. The 356 unchanged prefix source hashes match 16879b3 and their outputs were reused; all ten added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,171 declarations/auxiliaries and the combined audit for 49,105 NLS declarations, using only the standard allowed axioms. All 368 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,131 declarations (1,720 theorems and 411 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Whole original NLS action sequence in a common Cartesian inverse chart

The genuine physical real L2 form now has an exact complex decomposition
by its bounded real-part projection. Transport by the actual free Fourier
equivalence gives an exact decomposition of the natural Cartesian/mean
target into its genuine real form and i times that form. A Banach-valued
holomorphic identity on this physical real slice therefore extends over
a connected open complex target domain.

Bounded one-mode Cartesian rotations and their actual velocity operators
are constructed in arbitrary positive weighted sequence targets. Their
raw-coordinate formulas retain the signed mean and have the checked
clockwise orientation. On the literal original physical real L2 space,
the complete action flow is continuous, preserves the entire original
NLS action sequence in l1, and is conjugated by the actual Cartesian map
to those bounded target rotations as a full native Banach-space equality.

A genuine nonlinear inverse chart over one full complex native target
ball is now chosen with both inverse identities, exact image equality,
physical real inverse preservation and a common analytic source domain
for the entire original signed NLS action sequence. In these inverse
coordinates the action sequence is l1-valued Banach analytic and recovers
every original signed action exactly. Conservation on each complete real
orbit proves that its derivative annihilates every positive Cartesian
rotation direction on the genuine real target slice. Holomorphic
uniqueness extends that identity to the whole common complex ball. The
radius precedes the action index and the output index; no selected or
unselected action is required to be nonzero.

The subsequent local quotient-descent milestone below proves a factor
through quadratic Cartesian radii and the signed mean near zero. The mean
is retained linearly, including at zero.
Global forward factorization, general Cartesian-Cartesian brackets and
Gardner canonicity, global inverse/Jacobian geometry at general profiles,
independent angles/final angle-sum factorization and the full corrected
frequency comparison remain open. The main-theorem goal stays active.

Validation: all 376 article/shared modules have validated private outputs. The 366 unchanged prefix source hashes match 9b30b88 and their outputs were reused; all ten added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,282 declarations/auxiliaries and the combined audit for 49,217 NLS declarations, using only the standard allowed axioms. All 378 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,187 declarations (1,764 theorems and 423 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Local forward action factorization with signed mean

The full restricted original NLS action sequence now has one analytic
factor near the free profile through the native physical mKdV action
sequence and the signed mean. The factor takes values in the whole
summable NLS action space; one pair of open complex neighborhoods works
for every signed output index. Its input action space is weighted l1 of
order one, paired with a complex mean. On the original real H1 domain,
every positive input coordinate is the independent physical Hill-contour
J_n and the mean is the literal zero Fourier coefficient. Zero mean and
arbitrary collapsed actions are included.

The shared descent keeps a finite head linear. Infinitesimal tail rotation
stationarity gives invariance on complete real equal-action fibers:
finite rotations avoid the head, all intermediate points obey one uniform
full-norm bound, and finite replacements converge in norm. Holomorphic
uniqueness then supplies independent tail signs of arbitrary support.
Tail squaring and tail summation give an analytic sequence-valued quotient
without squaring the head. Bounded linear normalized Cartesian parameters
and a right inverse identify its positive sums with twice the weighted
physical actions, retaining the signed mean linearly at zero.

This proves the local zero-profile forward factorization prerequisite.
Global forward factorization at general profiles, general Cartesian-
Cartesian Gardner brackets/canonicity, general-profile inverse geometry,
independent angles/final angle-sum factorization and the full corrected
frequency comparison remain essential. The main-theorem goal stays active.

Validation: all 387 article/shared modules have validated private outputs. The 376 unchanged prefix source hashes match 19abb67 and their outputs were reused; all eleven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,346 declarations/auxiliaries and the combined audit for 49,281 NLS declarations, using only the standard allowed axioms. All 389 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,227 declarations (1,797 theorems and 430 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Global Cartesian phase lifting at attained actions

At every physical original L2 profile, all simultaneous real native
Cartesian phase configurations having its physical actions and signed
mean now have actual original L2 preimages. The preimage can be chosen
to retain every original signed NLS action of the initial profile.
Precisely, the compact fiber fixing the whole physical action/mean map
and the whole original NLS action sequence maps onto the entire native
Cartesian phase fiber. Its image is proved exactly, and is compact.
This includes infinitely many open modes, arbitrary closed actions, and
zero mean, without a smallness hypothesis.

The shared proof uses norm density of finite rotations avoiding a fixed
head. A closed set invariant under these rotations contains every real
equal-action point with the same head. Real normalized Cartesian
parameters retain all positive native coefficients and the signed mean;
clockwise native rotations become standard rotations at the opposite
time. Compact original physical action fibers therefore supply all
infinite phase configurations by closure.

Equal original NLS actions also preserve every nonnegative real Sobolev
regularity. This is proved in the shared NLS library for every finite
Banach exponent p>1 using the exact source/Birkhoff Sobolev equivalence
and an action-torus weighted majorant. On the physical scalar diagonal,
it supplies coefficient-preserving native representatives of every joint
fiber point. Consequently the global Cartesian phase lift exists in each
actual native integer H^s space, preserving all original NLS actions.

The assertions concern action sequences already attained by a physical
profile. They do not prove realization of arbitrary nonnegative action
data, uniqueness of Cartesian preimages, or equality of the entire
physical action fiber with one joint NLS action fiber. General-profile
Cartesian Jacobians and global inverse/Gardner canonicity, global forward
action factorization, independent angles/final angle-sum factorization,
and the full corrected frequency comparison remain essential. The
main-theorem goal stays active.

Validation: all 398 article/shared modules have validated private outputs. The 387 unchanged prefix source hashes match 0806a62 and their outputs were reused; all eleven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,404 declarations/auxiliaries and the combined audit for 49,339 NLS declarations, using only the standard allowed axioms. All 400 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,266 declarations (1,831 theorems and 435 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Faithful global phase coordinates on zero-mean NLS action fibers

On every physical original L2 diagonal fiber of the full signed NLS
action sequence at zero mean, the actual Cartesian map is now globally
injective. Its previously proved phase-saturated compact image therefore
gives a genuine homeomorphism onto the complete native Cartesian phase
fiber, in the original source and target norm topologies. Every attained
zero-mean phase configuration has a unique preimage within that original
NLS action fiber. The unique phase lift lies in each native integer H^s
class of the initial profile, with no smallness or open-gap restriction.

The essential symmetry is proved dynamically: actual component exchange
conjugates each complete original NLS action flow to the reflected-index
flow at opposite time. ODE uniqueness proves this on the entire real L2
source, including collapsed actions. A shared closure argument for
rotations avoiding an arbitrary retained index set shows that fixed
points with the same actions and positive coordinate pairs have the same
negative pairs. Only the central plane remains. Its two possible fixed
configurations differ by exactly the actual central NLS half-turn.

On the physical scalar diagonal, equal original NLS actions fix the whole
native physical J sequence and the literal mean squared. Zero mean closes
the central NLS action on all original L2 profiles by mean-preserving
finite Fourier approximation. It therefore removes the central half-turn
ambiguity. The zero-mean joint physical/NLS action fiber is proved to be
the entire physical diagonal NLS action fiber, not merely a subset.

The restriction to a fixed original NLS action fiber is essential here.
The result does not identify different NLS action fibers at the same J
and mean, establish the general-profile Cartesian Jacobian, or prove
Gardner canonicity. At nonzero mean the remaining possible central
half-turn has not yet been excluded using the signed mean. Arbitrary
nonnegative action realization, global forward action factorization,
independent angles/final angle-sum factorization and the full corrected
frequency comparison remain essential. The main-theorem goal stays active.

Validation: all 411 article/shared modules have validated private outputs. The 398 unchanged prefix source hashes match 4c6dd57 and their outputs were reused; all thirteen added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,467 declarations/auxiliaries and the combined audit for 49,402 NLS declarations, using only the standard allowed axioms. All 413 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,307 declarations (1,868 theorems and 439 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Faithful phase coordinates at every signed mean

The central NLS half-turn ambiguity is now removed at arbitrary signed
mean. Its actual complete source flow preserves the physical diagonal
and every original signed NLS action. On that diagonal it reverses the
literal signed mean. Equality of the complete Cartesian/mean maps thus
rules out the half turn at nonzero mean; the proved zero-mean uniqueness
handles the remaining case.

Every compact joint physical-action/mean and original-NLS-action fiber
now maps homeomorphically onto its complete native Cartesian phase fiber.
The joint fiber is exactly the full physical diagonal NLS action fiber
restricted to its original signed mean. Phase lifts within this branch
are unique in every actual native integer H^s source class, including
zero mean, arbitrary closed gaps and infinitely many open modes. There
is no smallness hypothesis.

The sign reversal is proved rather than prescribed. Original-L2 zero-J
rigidity forces a constant profile at its literal mean. The actual central
half turn sends each real constant's mean to its negative: its actions
are unchanged and a nonzero constant's central action is open. A straight
physical-source path from any profile to its constant mean remains in the
same mean leaf. The half-turn mean is continuous there and has the same
square. Its verified value at the constant therefore determines the sign
on the whole path. The zero-mean case follows directly from the square.

Theorem 4(ii)'s printed global signed-mean recovery from NLS actions alone
is now explicitly refuted in Lean even for an arbitrary, nonanalytic
factor. A profile and its central half turn have identical entire signed
NLS action sequences and opposite nonzero means. The previously proved
analytic mean-squared replacement remains the global corrected clause.

This removes the central ambiguity within fixed original NLS action
fibers; it does not identify different NLS action fibers at the same
physical J and signed mean. General Cartesian Jacobians/global inverse,
Gardner canonicity, arbitrary nonnegative action realization, global
forward action factorization, independent angles/final angle-sum
factorization and the full corrected frequency comparison remain
essential. The main-theorem goal stays active.

Validation: all 419 article/shared modules have validated private outputs. The 411 unchanged prefix source hashes match db425d9 and their outputs were reused; all eight added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,524 declarations/auxiliaries and the combined audit for 49,459 NLS declarations, using only the standard allowed axioms. All 421 mathematical source/checker hashes match the frozen inputs. The public inventory is 2,348 declarations (1,905 theorems and 443 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## General-profile Cartesian derivative: compact remainder and Fredholm reduction

The actual Cartesian derivative now differs from its actual free bounded
linear equivalence by a compact operator at every physical real original-L2
profile. This is proved both for the ambient complex derivative into the
complete positive weighted Cartesian/mean target and for the genuine
physical real source and target. There is no smallness, finite-gap,
nonzero-mean or open-action hypothesis.

The regularized physical action ratio is the reciprocal of twice a point
between the canonical spectral endpoints. Their bounded displacements
prove that the scaled ratio tends to 1/(2*pi), and the scaled positive
root tends to sqrt(1/(2*pi)), also when the selected gap is closed.
The existing bounded-sequence analytic realization of all scaled roots
is reused. Its difference from the free symbol has vanishing tails and
therefore defines a compact diagonal multiplier.

The derivative of the normalized full Cartesian map splits into the
original NLS Jacobian times the bounded root symbol and the derivative
of that symbol times the fixed original NLS coordinate sequence.
The verified compact NLS Jacobian remainder handles the first part.
Multiplication by a fixed finite-exponent sequence is compact from
linfinity into that sequence space, so the second part is compact without
any derivative-tail assumption. A bounded retraction transports the result
back to the full native half-order target, including the signed mean.

The actual normalized complex Jacobian is identity plus compact.
The Fredholm alternative now proves that derivative bijectivity is
equivalent to derivative injectivity, in both the ambient complex and
physical real spaces. Under the explicitly stated injectivity premise,
the physical map has an actual analytic local inverse chart. The
injectivity premise is not proved by this reduction.

Essential remaining work includes general-profile derivative kernel
triviality, global inversion and comparison of distinct original NLS
action fibers at the same physical actions and signed mean, Gardner
canonicity, arbitrary action-data realization, global forward action
factorization, independent angles/final angle-sum factorization, and
the full corrected frequency comparison. This milestone proves original-L2
compactness; it does not assert compact remainders at every Sobolev order.

Validation: all 428 article/shared modules have validated private outputs. The 419 unchanged prefix source hashes match 6e8e2cf and their outputs were reused; all nine added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,606 declarations/auxiliaries and the combined audit for 49,541 NLS declarations, using only the standard allowed axioms. All 431 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,399 declarations (1,946 theorems and 453 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Actual Cartesian Gardner fields and the canonical bracket in each plane

For every original real H1 profile, every positive selected index and
every complex linear combination of its actual Cartesian pair, the
literal Frechet gradient has a square-summable period-one spatial
derivative. The actual Gardner direction is its genuine tempered
distribution derivative with an L2 representative. Zero mean and arbitrary
closed gaps are included; no smallness or finite-gap premise is used.

The checked convergent action-field trace and mixed Cartesian-action
brackets first give the exact spatial translation generator on each
pair. Differentiating this identity on the physical real H1 form gives
a bounded L2 extension of the cotangent applied to the spatial generator.
The real form spans all complex variations, and Fourier-mode tests
identify the differentiated gradient itself. This argument establishes
the Gardner domain rather than using the fallback in its definition.

All actual Cartesian-Cartesian Gardner brackets now have complex analytic
H1 extensions near every physical real H1 input and are skew symmetric
there. The literal brackets within each selected plane are
{X_n,X_n}=0, {X_n,Y_n}=1, {Y_n,X_n}=-1 and {Y_n,Y_n}=0,
including a closed selected gap. The exact physical action radius and
mixed brackets give X_n*({X_n,Y_n}-1)=0. The actual free Fourier derivative
proves X_n is not identically zero on the physical real H1 space.
Real analytic continuation on that connected space cancels the factor
and proves the value one everywhere, without dividing by an action.

Cross-mode zero brackets are not proved by the plane result. General
Cartesian derivative kernel triviality, the global inverse and comparison
of distinct NLS action fibers at equal physical actions and signed mean,
arbitrary action-data realization, global forward action factorization,
independent mKdV angles/final angle-sum factorization and the full corrected
frequency comparison remain essential. The main-theorem goal stays active.

Validation: all 438 article/shared modules have validated private outputs. The 428 unchanged prefix source hashes match 9ef985e and their outputs were reused; all ten added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,677 declarations/auxiliaries and the combined audit for 49,612 NLS declarations, using only the standard allowed axioms. All 441 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,438 declarations (1,978 theorems and 460 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## General real H1 basepoints: actual Cartesian Jacobian and local inverse

The actual ambient complex L2 Cartesian Jacobian into the complete native
positive half-order pair plus signed mean is now bijective at every original
physical real H1 profile. The genuine physical real derivative is a bounded
linear equivalence and the actual physical Cartesian map has analytic open
local inverse charts on these L2 spaces around each such basepoint. No
smallness, finite-gap, nonzero-mean or open-gap premise is imposed. In
particular, the earlier Fredholm reduction's injectivity premise is now
discharged at every original real H1 basepoint.

The proof uses the full target action-field covariance. At a closed action,
differentiating its stationary analytic field forces any continuous
annihilator of the Cartesian Jacobian to annihilate that modal rotation.
The checked canonical bracket within that plane kills both closed-mode
coefficients. At an open action, covariance forces the annihilator to be
radial. Mixed action-Cartesian brackets and skew symmetry cancel the other
modes. A norm-convergent expansion in the actual weighted half-order target
then kills every modal coefficient, and the actual source zero Fourier
variation kills the mean coefficient. Thus the normalized Jacobian has
dense range. Its previously checked compact free remainder gives
bijectivity by the Fredholm alternative. Differentiating the actual physical
inclusion and applying the real inverse theorem supplies the physical chart.

Article-facing declarations are
`physical_Cartesian_complex_Jacobian_bijective_general_H1`,
`physical_Cartesian_derivative_equivalence_general_H1` and
`physical_Cartesian_analytic_local_inverse_general_H1` in
`NLS/Articles/MKdVNLSHierarchies/GeneralCartesianLocalInverseIdentification.lean`.
The charts have original L2 source and native half-order target topologies;
this result does not yet give general-profile native higher-Sobolev charts
or invertibility at every rough real L2 basepoint.

Cross-mode Cartesian zero brackets/full Gardner canonicity, global inversion
and comparison of distinct NLS action fibers at equal physical J and signed
mean, arbitrary nonnegative action realization, global forward action
factorization, independent mKdV angles/final angle-sum factorization and the
full corrected frequency comparison remain essential. The main-theorem
goal stays active.

Validation: all 449 article/shared modules have validated private outputs. The 438 unchanged prefix source hashes match a283014 and their outputs were reused; all eleven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,744 declarations/auxiliaries and the combined audit for 49,679 NLS declarations, using only the standard allowed axioms. All 452 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,485 declarations (2,019 theorems and 466 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Global native Sobolev Cartesian bijection and original-action fiber identification

The actual physical Cartesian map, including the literal signed mean, is
now a global bijection from original real H^s onto the entire native
positive real Cartesian pair of order s+1/2 plus arbitrary real mean, for
every integer s>=1. Moreover, every such target datum has exactly one
preimage in the entire physical real original-L2 space. Arbitrary closed
gaps, infinite support and zero mean are included. No equality of the
original NLS action sequences is assumed for injectivity.

First, the bounded inverse spectral root symbol recovers the positive
original NLS coordinates with weight s from the Cartesian data with weight
s+1/2. The even diagonal NLS actions control both negative coordinates by
the corresponding positive radius; the zero coordinate is finite. The
checked original NLS Sobolev characterization then recovers the source
weight. Consequently the exact inverse image of the native Sobolev target
range is the native Sobolev source range, globally for every integer s>=0.
This regularity statement does not assume small data or a fixed action fiber.

For s>=1, all preimages of native data therefore lie at real H1 points
with the previously checked open L2 inverse charts. Properness gives a
closed range. Its pullback to the connected native target is also open by
the local charts, so the entire target is attained. Uniqueness is continued
from the checked singleton zero fiber: properness makes the singleton-fiber
locus open; two distinct regular preimages have disjoint chart neighborhoods,
so the multiple-fiber locus is open too. Connectedness rules out a change
in multiplicity. This argument does not assume a native-topology inverse
chart or an unproved covering theorem.

The earlier phase-saturation theorem now identifies different original NLS
action fibers: equal physical action sequences and signed mean on H^s,
s>=1, force equality of the whole original signed NLS action sequence.
Phase saturation supplies a point in the first NLS action fiber with the
second profile's full Cartesian data; global Cartesian injectivity identifies
that point with the second profile. This proves global determination by
physical actions and signed mean, but does not yet prove the required
analytic factorization on open action-space neighborhoods.

Article-facing declarations are
`physical_Cartesian_inverse_global_Sobolev_regularity`,
`physical_Cartesian_global_unique_preimage_nativeSobolev`,
`physical_Cartesian_global_bijection_nativeSobolev` and
`physical_NLS_actions_determined_by_mKdV_actions_mean` in
`NLS/Articles/MKdVNLSHierarchies/GlobalSobolevCartesianInverseIdentification.lean`.
The global bijection is a set-theoretic assertion between the full native
spaces. Native inverse continuity/analyticity, full Gardner canonicity and
cross-mode zero brackets remain to be proved. Global surjectivity or
injectivity for arbitrary rough L2 target data is not asserted here.
Independent mKdV angles/final angle-sum factorization and the full corrected
frequency comparison also remain essential. The main-theorem goal stays active.

Validation: all 457 article/shared modules have validated private outputs. The 449 unchanged prefix source hashes match 4f9bba0 and their outputs were reused; all eight added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,771 declarations/auxiliaries and the combined audit for 49,706 NLS declarations, using only the standard allowed axioms. All 460 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,506 declarations (2,040 theorems and 466 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Arbitrary native action realization and general holomorphic Cartesian action charts

Every nonnegative positive-index action sequence with weight 2s+1 and an
arbitrary real signed mean is now realized by an actual real original H^s
profile, for every integer s>=1. The coordinate sequence can have infinite
support and any set of collapsed actions. The shared quadratic lifting
lemma preserves the exact squared native weight: weighting the actions,
lifting in l2, and undoing the coordinate weight gives a real pair of order
s+1/2. Positive projection and the literal mean give native target data;
the checked global native Cartesian bijection supplies the profile.
For s=1, `physical_H1_Hill_action_data_realization` explicitly identifies
every positive entry with the independently defined original physical Hill
action on the coefficient-preserving original H1 profile. The action cone
is the weight-three l1 cone at this endpoint, not an unweighted substitute.

At every original physical real H1 profile, the full complex L2 Cartesian
map now has an actual holomorphic open inverse chart. Every complex left
inverse germ there preserves the physical real form on nearby real target
data, by agreement with the checked genuine physical real chart. One common
complex target ball carries the entire original signed NLS action sequence
as an l1-valued holomorphic function of the inverse Cartesian coordinates.
The radius is independent of the selected action index. Conservation on
the original complete physical action orbits proves rotation stationarity
on the real target slice; holomorphic uniqueness at the arbitrary real
basepoint proves it throughout that full complex ball. Closed actions,
zero mean and general nonzero profiles are included.

Shared sequence-space descent now also works at an arbitrary prescribed
basepoint of an open sign-invariant domain, retaining the finite head
linearly and quotienting the tail by its quadratic action radii. This
removes the zero-basepoint restriction from the previously checked local
tail-action factorization mechanism. Applying this general descent to the
arbitrary-center Cartesian chart, removing the finite open head variables,
and gluing the resulting action factors are still required before claiming
global forward analytic I(J,mean) factorization. Rotation stationarity
alone is not being reported as that factorization.

Article-facing declarations are `physical_mKdV_native_action_data_realization`,
`physical_H1_Hill_action_data_realization` and
`physical_NLS_actions_general_H1_Cartesian_chart` in
`NLS/Articles/MKdVNLSHierarchies/ActionRealizationGeneralCharts.lean`.
Native inverse continuity/analyticity, full Gardner canonicity, independent
mKdV angles/final angle-sum factorization, the forward analytic action factor
and the full corrected frequency comparison remain essential. The main
theorem goal stays active.

Validation: all 465 article/shared modules have validated private outputs. The 457 unchanged prefix source hashes match 1f4185e and their outputs were reused; all eight added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,828 declarations/auxiliaries and the combined audit for 49,764 NLS declarations, using only the standard allowed axioms. All 468 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,525 declarations (2,058 theorems and 467 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Forward analytic action dependence at every original real H1 profile

The whole original signed NLS action sequence now has a common holomorphic
factor through native physical mKdV actions and literal signed mean locally
at every original physical real H1 profile. The source neighborhood is open
in the original complex L2 space and contains the chosen literal H1 profile.
The action neighborhood is open in weight-one complex l1 physical actions
plus complex signed mean. Both neighborhoods and the l1-valued factor are
chosen before all action indices. Recovery holds for every physical real
L2 input in that source neighborhood. On original H1 inputs, each positive
input entry is explicitly the independent Hill action and the mean is the
literal zero Fourier coefficient. Zero mean, closed selected or other gaps,
and infinitely many open actions are all included.

The proof extends full sequence-valued quadratic-action descent to arbitrary
complex basepoints. A nearby finite truncation retains all necessary head
coordinates; translating by this head leaves tail rotation vectors unchanged.
The checked zero-centered tail-sign argument gives all tail sign symmetries
on a smaller ball around the finite center, with the original basepoint still
inside. Analytic descent handles the tail, while the checked finite head
section and action-preserving paths remove the retained nonzero pairs.

To retain signed mean without a branch restriction, a separate auxiliary
zero pair is (m+1/2,i*(m-1/2)). Its quadratic action is exactly m. This is an
entire affine section at every complex mean, including zero; it neither
recovers mean from NLS actions nor replaces it by mean squared. The positive
auxiliary entries remain the native weighted Cartesian variables. Their
full quadratic action sequence is exactly the weight-normalized physical
mKdV actions with the literal mean at zero and unused negative slots zero.
Every auxiliary rotation is stationary, including rotation of the auxiliary
zero pair. The complete holomorphic action descent therefore gives the
required factor, and the entire section pulls recovery back to the actual
Cartesian chart and original source.

Article-facing declarations are
`original_NLS_actions_local_action_mean_factor_general_H1` and
`original_H1_NLS_actions_local_physical_factor_general_H1` in
`NLS/Articles/MKdVNLSHierarchies/GeneralForwardActionFactorization.lean`.
Global determination by physical action/mean data was already proved, but
these local factors have not yet been glued to one common open complex
action domain with recovery for all original real H1 profiles. That common
extension remains the forward obligation of Theorem 4(ii). Native inverse
analyticity, independent canonical mKdV angles/full Gardner canonicity,
final angle-sum factorization and the corrected full frequency comparison
also remain essential. The main theorem goal stays active.

Validation: all 472 article/shared modules have validated private outputs. The 465 unchanged prefix source hashes match 47697d7 and their outputs were reused; all seven added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,886 declarations/auxiliaries and the combined audit for 49,822 NLS declarations, using only the standard allowed axioms. All 475 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,560 declarations (2,085 theorems and 475 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Corrected Theorem 4(ii): one global forward action/mean factor

The global forward clause is now proved by
`theorem4_ii_nls_actions_of_mkdv_actions_mean` in
`NLS/Articles/MKdVNLSHierarchies/GlobalForwardActionIdentification.lean`.
One open complex native action/mean domain contains the data of every
original physical real H1 profile. One holomorphic, hence real analytic,
l1-valued factor recovers every original signed NLS spectral action on
all of those profiles. The domain and factor precede the profile and
both action indices. Each positive input entry is explicitly identified
with the independent physical Hill action, and the mean with the literal
zero Fourier coefficient. Zero mean, arbitrary closed gaps and infinite
support are included.

This closes the forward obligation of Theorem 4(ii). Together with the
already proved converse `theorem4_ii_mkdv_actions_of_nls_actions` and the
sign-invariant correction `theorem4_ii_mean_square_of_nls_actions`, all
clauses of corrected Theorem 4(ii) are proved. The printed global recovery
of signed mean from NLS actions remains false, with the checked half-turn
obstruction already recorded; it is not claimed here.

The global step first strengthens each local factor: on a small open
action neighborhood it recovers the NLS actions of EVERY original H1
representative of those data, regardless of distance from the chart's
basepoint. Quantitative real quadratic-action lifts give nearby real
Cartesian values. Phase saturation puts such a value in the prescribed
original NLS action fiber. All its phase lifts retain H1 regularity, and
uniqueness among all L2 preimages of native Cartesian data identifies the
local inverse with that phase lift.

For gluing only, the signed mean c is encoded as the strictly positive
central auxiliary entry exp(c); positive auxiliary entries are the native
weight-normalized physical mKdV actions. The principal logarithm decodes
every real signed mean, including negative and zero means, on local
complex neighborhoods of these positive central values. The local
encoded factors agree on finite nonnegative data because those data have
actual original H1 representatives with the prescribed physical actions
and decoded mean. Finite nonnegative truncations retaining the central
entry converge in l1, so continuity gives agreement on all nonnegative
overlaps. The checked holomorphic nonnegative-action gluing theorem
produces one factor on the union of the encoded balls. Pullback by the
entire exponential encoding gives the common open physical action/mean
domain. The exponential is an auxiliary coordinate for gluing; the final
factor's argument is the original literal signed mean.

Theorems 3 and 4(iii)'s final angle-sum clause remain incomplete. Independent
canonical mKdV angles/full Gardner canonicity, needed native inverse
analyticity, and the full corrected frequency comparison on the original
Sobolev domains remain essential. The main theorem goal stays active.

Validation: all 480 article/shared modules have validated private outputs. The 472 unchanged prefix source hashes match 7c174c0 and their outputs were reused; all eight added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 4,935 declarations/auxiliaries and the combined audit for 49,871 NLS declarations, using only the standard allowed axioms. All 483 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,598 declarations (2,118 theorems and 480 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Global native analytic Cartesian inverses and exact-domain Hamiltonian conservation

The actual Cartesian map is now a real analytic homeomorphism from every
physical real integer H^s space, s>=1, onto its full positive native
h^(s+1/2) pair with the literal signed mean. Its global inverse is real
analytic everywhere in those native norms. At every physical real H^s
profile, the full complex map also has a genuine complex analytic local
inverse. These assertions include all closed gaps and every real mean.
`physical_native_Cartesian_analytic_homeomorph` is the article adapter.

The proof reuses the checked native weighted NLS compact Jacobian
remainder. Normalized scalar diagonal pullback preserves compactness.
For the scaled Cartesian map, derivatives of the bounded analytic root
symbol are multiplied by the fixed native NLS sequence; that multiplication
is compact. The remaining terms use the compact NLS remainder and the
vanishing root-symbol tail. Complex native germs commute with the
coefficient-preserving L2 inclusions, so the existing H1-basepoint L2
injectivity gives native derivative injectivity. The compact Fredholm
alternative supplies native complex and real bijectivity and local
analytic charts. The already proved global set bijection forces the
local real inverses to agree with the global inverse. The shared
`analyticOnNhd_inverse_of_local_charts` records this general argument.
One initial compatibility proof exceeded the unchanged kernel limit;
splitting its uniform coefficient-germ lemmas resolved that check without
increasing kernel, recursion or heartbeat limits.

`physical_native_Hill_hamiltonian_Cartesian_representation` now expresses
the independently defined physical spectral K_m, m>=2, as a real analytic
functional of these actual native Cartesian coordinates on its exact
H^(m-1) domain. This statement does not assume full Cartesian canonicity.

`physical_native_Hill_hamiltonian_action_flow_conservation` proves that
every K_m, m>=1, is constant along every complete physical action flow
on the full real H^(m-1) domain. All higher actions have exactly the same
real gap integrands on isospectral profiles, including collapsed gaps.
The checked sharp higher-action trace gives conservation of the actual
odd NLS Hamiltonian in the sharp H^s domain, and the independent factor-two
restriction gives conservation of K_(s+1). The original H0 mass trace
supplies m=1 separately, with no smoothness premise or extra regularity.

Theorem 3 remains incomplete: the physical Hamiltonians still need action
normal forms and independent frequency identification, including analytic
continuation at closed actions. Independent canonical mKdV angles/full
Gardner canonicity and the final angle-sum clause of Theorem 4(iii) remain
open. Native higher-Sobolev inverse analyticity is no longer an outstanding
dependency. The overall main-theorem goal stays active.

Validation: all 490 article/shared modules have validated private outputs. The 480 unchanged prefix source hashes match 08cf309 and their outputs were reused; all ten added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,011 declarations/auxiliaries and the combined audit for 49,947 NLS declarations, using only the standard allowed axioms. All 493 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,656 declarations (2,166 theorems and 490 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Global native action normal forms of the independent Hill hierarchy

`physical_native_Hill_global_action_normal_form` now gives a single
holomorphic normal form for every independent physical K_m, m>=1, on
one open complex native weight-(2m-1) summable action/mean domain
containing the data of EVERY original real H^(m-1) profile. The domain
and factor precede the profile and all action indices. Its arguments
are the actual independent Hill actions and the literal signed Fourier
mean. Real analyticity follows by restricting scalars. Closed actions,
infinite support, negative mean and zero mean are all included.

Native Cartesian weight equivalences transport the checked H^s inverse
charts into a fixed half-order target. Complex inverse germs preserve
physical reality by comparison with the global native real analytic
inverse. The exact complete action-flow covariance and conservation of
the independent K_(s+1) give real rotation stationarity; the checked
real-form identity principle extends it to full holomorphic stationarity.
The reusable `exists_local_miuraCartesian_action_factor` descends any
sequence-valued Cartesian invariant to actions and signed mean, using the
entire isotropic mean section; a scalar counterpart supplies the Hill
Hamiltonian factors. No square-root or sign branch of mean is chosen.

Equality of native physical actions and mean implies equality of the
original NLS action sequence, hence actual isospectrality. The sharp
higher-action trace and the independently identified factor-two
restriction then identify K_(s+1) on every native representative of the
data. Nearby real Cartesian lifts remove the source-neighborhood
restriction from each local factor. In the normalized native topology,
every nonnegative encoded l1 datum, even one with infinite support, has
a real H^s representative. Local factors therefore agree on all
nonnegative overlaps directly. The verified holomorphic nonnegative-action
gluing theorem supplies one factor; exponential mean decoding and the
bounded native action equivalence give the final physical action domain.
The shared `exists_analytic_factor_pullback` records the last argument.

The m=1 endpoint uses the full original real L2 mass trace directly:
K_1 = mean^2/2 + sum_n 2*pi*n*J_n. The action moment is a bounded linear
functional in the exact weight-one action norm. Its entire mass normal
form has derivative 2*pi*n in every raw selected action direction,
including at a collapsed selected action. No rough-L2 Cartesian inverse
is needed for this endpoint.

`MiuraNativeHamiltonianActionData` packages global native normal forms
without imposing any canonicity hypothesis. Its positive action
frequencies are actual Frechet derivatives along raw unit physical-action
directions; `frequency_analytic` proves they are holomorphic throughout
the common complex domain. For every m>=2,
`physical_native_Hill_action_frequency_intrinsic` proves that any two
normal forms give identical positive action derivatives at every physical
profile. Nonnegative one-sided increases of a selected action are
realized on the full native H^s domain, with literal mean fixed. Both
normal forms agree on these profiles; uniqueness of the derivative on
the real half-line gives equality even when that action starts closed.
The shared `fderiv_eq_of_nonnegative_ray_realization` is the general
analytic argument.

Theorem 3 still requires comparison of these independent Hill action
derivatives with the actual original even-order NLS frequencies on the
full real H^(m-1) domains, including the mass endpoint and closed-action
continuation, with the recorded physical normalization correction.
Independent canonical mKdV angles/full Gardner canonicity and the final
angle-sum clause of Theorem 4(iii) remain open. The overall main-theorem
goal stays active.

Validation: all 510 article/shared modules have validated private outputs. The 490 unchanged prefix source hashes match fe2097b and their outputs were reused; all twenty added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,153 declarations/auxiliaries and the combined audit for 50,089 NLS declarations, using only the standard allowed axioms. All 513 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,727 declarations (2,228 theorems and 499 definitions); new structures and generated projections/auxiliaries are additionally audited. Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Full L2 mass-frequency comparison and a checked parity counterexample

`theorem3_m1_corrected` proves the corrected first
case of Theorem 3 on EVERY original real L2 profile, including collapsed
actions. The original NLS S2 frequency equals the independent physical
K1 raw positive-action derivative, with positive period-one value 2*pi*n.
This holds for every global physical mass normal form, rather than just
the explicit mass formula. `theorem3_m1_corrected_native` states the same
comparison in the uniform native H^(m-1) normal-form framework.

The NLS frequency is identified independently. The checked original S2
Hamiltonian has exactly the physical momentum differential
(`fderiv_originalS2_eq_sourceMomentumCotangent`). One actually constructed
original NLS angle family has angle-momentum bracket +2*pi*n on its own
open-angle real H1 domain. Open-gap density first determines any continuous
extension throughout real H1. Original real-L2 finite-gap density and the
unchanged H1 reconstruction then determine it on ALL real L2 sources.
`theorem3_m1_original_NLS_frequency_certificate` packages the constructed
angle family and unique extension simultaneously for all signed indices.
The constant complex frequency candidate is entire. No mKdV action factor
is used to define or normalize this NLS frequency.

For the independent mass frequency, real H1 profiles realize every
one-sided raw positive-action ray in the L2 action topology, with mean
fixed. All global mass normal forms recover the same physical mass on
these rays. Uniqueness of the real one-sided derivative fixes their
selected action derivative. Analytic dependence on the original L2 source
and real H1 density extend the result to ALL original real L2 profiles,
including every closed action. Linear H0/L2 coefficient identification
transports any native mass normal form to this setting. Consequently
`native_Hill_frequency_unique_allOrders` proves positive-action frequency
choice independence at every m>=1. No nonlinear rough-L2 inverse or full
Gardner canonicity is assumed.

`theorem3_printed_parity_counterexample` gives a concrete refutation of
the printed (-1)^m factor: at the literal zero profile, m=1 and n=1, it
would equate -2*pi with +2*pi. Both selected actions are closed, and the
source explicitly includes their analytic frequency extensions. The
underlying original momentum normalization and independent mass action
normalization are both checked.

The m>=2 comparison with the original NLS S_(2m) frequencies remains
open. Independent canonical mKdV angles/full Gardner canonicity and the
final angle-sum clause of Theorem 4(iii) also remain open. The overall
main-theorem goal stays active.

Validation: all 518 article/shared modules have validated private outputs. The 510 unchanged prefix source hashes match 898aecf and their outputs were reused; all eight added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,257 declarations/auxiliaries and the combined audit for 50,193 NLS declarations, using only the standard allowed axioms. All 521 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,766 declarations (2,260 theorems and 506 definitions); new structures and generated projections/auxiliaries are additionally audited. Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. A concrete analytic pullback initially hit the default kernel limit; factoring the composition into an abstract bounded-linear constructor resolved it. Kernel, recursion and heartbeat limits were not increased.


## Corrected Theorem 3 at every order on the full original domain

`FrequencyIdentification.lean` completes corrected Theorem 3.
`theorem3_corrected` proves, for EVERY m>=1 and n>=1 and EVERY original
real H^(m-1) profile, that the restricted original NLS S_(2m) frequency
is the raw physical-action derivative of ANY independent K_m global
normal form. The mean direction is literally zero. Selected and unselected
actions may be closed; infinite support and arbitrary signed mean are
included. The sign is positive, consistent with the paper's concluding
proof and the separately checked mass counterexample to the printed sign.

The NLS frequency is specified by its own original Hamiltonian bracket.
`miuraOriginalEvenNLSAngleFrequency` is minus the actual S_(2m) differential
applied to the actual original NLS angle Hamiltonian vector on the real
H^m open-angle domain. The original physical S_(2m) is the already checked
sharp reduced-density Hamiltonian, identified with the original smooth
hierarchy and its higher-regularity representatives. The angle vector's
inclusion has precisely the original L2 Hamiltonian Fourier coefficients.
No Hill normal form occurs in this bracket's definition.

The actual original Birkhoff Jacobian sends that angle vector to one
finite-mode radial target. Its already verified weighted inverse therefore
lifts the original angle vector uniquely to EVERY native spectral weight,
without a finite-gap assumption. Exact half-scale weights give the original
integer H^m norms, retaining every raw coefficient. This removes the
previously missing regularity premise from the bracket comparison.

`fderiv_even_diagonal_eq_nativeHill_cotangent` proves the all-order
complex cotangent transfer: the original S_(2s+2) differential at an
H^(s+1) diagonal profile equals the independent native K_(s+1)
differential applied to i times the spatial difference of the variation's
two components. The actual period-one Fourier symbol and the checked
sharp gradient recurrence prove this identity. It precedes every angular
or frequency definition.

The transferred angle direction belongs to the required H^s space and
has the actual Gardner gradient-derivative coefficients. Gardner skew
symmetry and the original mixed angle-action bracket show that each
physical J_k has derivative -delta_nk in that direction; J_k may be
closed. `miuraThetaNativeActionMean_differential` identifies the FULL
weighted-summable action/mean differential with the negative raw selected
unit and zero mean. The proof identifies bounded coefficient projections,
so no infinite derivative sum or its exchange is assumed. Agreement of
independent Hill normal forms on the spanning physical real form identifies
their full complex differential, giving the genuine normal-form chain rule.
The actual open-angle NLS bracket consequently equals every Hill frequency.

The sharp continuation is specified without a Hill-side value in its
definition: `IsMiuraOriginalEvenFrequencyExtension` requires continuity
on ALL real H^s profiles and agreement with that original S_(2s+2) bracket
on real H^(s+1) open-angle profiles. The physical open-angle locus is dense
at every positive native order: the action coordinate is globally real
analytic, a realized positive action ray supplies a nonzero value, and
closed selected gaps force its action to vanish. Coefficient-preserving
physical real Sobolev inclusions have dense range, proved by finite Fourier
density and commuting real projections. These two density steps prove
uniqueness on the exact real H^s domain, including every closed action.
The checked open-angle comparison supplies existence.

`theorem3_original_frequency_extension_certificate` packages that unique
extension. `theorem3_corrected_for_any_original_frequency_extension` compares
ANY continuous realization of the original bracket, so the result does
not depend on our chosen representative. `theorem3_original_bracket_agreement`
exposes both the actual S_(2m) differential and original angle-vector
coefficients. The frequency certificate concerns the diagonal restriction
requested by Theorem 3. `theorem3_frequency_holomorphic_extension` supplies
one open complex H^(m-1) neighborhood containing EVERY real profile,
including closed-gap profiles, and one holomorphic function recovering
the original restricted frequency everywhere on that real domain.
`theorem3_m1_frequency_normalization` agrees with the separately normalized
+2*pi*n momentum/mass benchmark on the entire real L2 endpoint.

Corrected Theorem 3 is now COMPLETE. The remaining main-theorem obligation
is Theorem 4(iii)'s independent original mKdV angles and final angle-sum
factorization. Their required negative Gardner action brackets must be
identified independently. The current Cartesian map's same-plane and mixed
action relations do not identify a fully canonical angle family; its
cross-mode brackets remain unproved. Full cross-mode Cartesian canonicity
is a possible route to this dependency, rather than an extra source
conclusion. The overall main-theorem goal remains active.

Validation: all 534 article/shared modules have validated private outputs. All 518 unchanged prefix source hashes match pushed 8e99597 and their outputs were reused; all sixteen added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,392 declarations/auxiliaries and the combined audit for 50,328 NLS declarations, using only the standard allowed axioms. All 537 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,830 declarations (2,312 theorems and 518 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Actual H¹ Miura–Magri transfer and native action-flow tangents

The new shared Poisson adapter proves the actual complex H¹ Miura map
B(u)=u_x+u² is differentiable and pulls back physical Hill functionals
with H² gradients to actual H¹ Gardner gradients. Its transpose is
T_u* f=-f_x+2uf. For all complex H¹ u and H² test gradients f,g,
the pulled-back bracket is the independently defined weak Magri bivector

`<f_x,g_xx> + 2 <B(u), f g_x - f_x g>`.

The pairing is the complex bilinear physical Fourier pairing. Products,
L² multiplication, their transposes, the Leibniz rule and integration by
parts are proved at the stated rough regularity. No derivative of the L²
potential is assumed. `physical_Miura_Gardner_Magri_transfer` applies to
ANY actual H¹ gradient representatives, whose uniqueness is proved by
finite physical Fourier variations. The transfer is independent of the
Miura representative, including at zero mean. No Jacobi theorem for an
arbitrary weak bivector is asserted.

`physical_action_flow_native_Gardner_tangent` proves that every original
positive-index action flow has a derivative in each native H^s norm,
s>=1, at every real profile, including closed selected actions. The actual
Cartesian inverse chart lifts the finite-plane rotation derivative; its
L² inclusion is proved equal to the original physical Gardner action
field. `hasDerivAt_independent_functional_miuraActionFlow` then supplies
the actual chain rule for independent H¹ functionals with H¹ physical
gradients, without assuming they extend to L².

These are necessary analytic adapters for the remaining independent
mKdV angles. Theorem 4(iii)'s independent angle identification and final
angle-sum factorization remain OPEN. Theorem 3 remains COMPLETE at every
order on its corrected exact domain, as recorded in the preceding milestone.

Validation: all 548 article/shared modules have validated private outputs. All 534 unchanged prefix source hashes match pushed e655360 and their outputs were reused; all fourteen added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,544 declarations/auxiliaries and the combined audit for 50,463 NLS declarations, using only standard allowed axioms. All 551 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,879 declarations (2,350 theorems and 529 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Global full-phase descent from independent negative Gardner generators

`physical_complete_action_flow_invariant_factor` proves that EVERY
continuous scalar observable fixed by every actual positive-index
Gardner action flow factors through the complete native physical action
sequence and literal signed mean, for every integer Sobolev order s>=1.
The proof uses the genuine global normalized native Cartesian
homeomorphism. Continuous real parameter decoding intertwines positive
coordinate rotations with the opposite physical clockwise rotations;
negative encoding slots are ignored. Finite tail rotations are dense in
the full infinite action torus in its sequence norm, and a closed level
set of a continuous observable contains the whole fiber. The mean head
is fixed literally. Infinite support, arbitrary signed mean and closed
actions are included; finite-gap approximation is not an assumption.

`hasDerivAt_miuraActionFlow_native` translates the actual H^s derivative
at zero to EVERY real time by the physical group law. The corresponding
H¹ functional chain rule evaluates the actual physical Gardner field
at each orbit point. `independent_functional_action_rotation_of_Gardner_generator`
integrates an actual negative unit differential identity for an
independently specified H¹ functional, rather than assuming its flow law.

`miuraNativeNLSAngularCoordinate` is the first normalized Cartesian
coordinate minus i times the second. It is a positive real multiple of
the actual original scaled NLS Cartesian complex coordinate, rotates
at exp(i*t) under its selected action, and remains fixed under every
other action. Its zero set is proved EXACTLY the zero set of the
independent physical J_m. Its normalized unit phase has norm one on
that selected open-action domain. This uses full complex phases, not
their squares or an angle modulo pi.

`theorem4_iii_phase_sum_descent_of_independent_Gardner_phase` proves the
remaining global descent IMPLICATION on the exact selected open-action
domain: ANY independently supplied actual H¹ unit phase, with physical
H¹ gradient there and negative Gardner generators -i*delta_mn times
that phase, has a full phase-product factor with the actual restricted
NLS Cartesian phase. Its hypotheses prescribe neither phase values nor
action dependence. Actual chain rules integrate the generator along the
complete physical orbit. Only a bounded auxiliary is set to zero at
closed selected actions; multiplying it by the vanishing NLS amplitude
is continuous. Global action descent applies to that product and to
its invariant amplitude. Division recovers the full unit-phase product
on the original open-angle locus. Other actions may all be closed.
No continuous angular extension through the selected closed action is
assumed. The resulting factor is a function; no additional analyticity
claim for this general continuous factor is made.

Theorem 4(iii) is still INCOMPLETE. The original independent mKdV phase
must be constructed and proved to satisfy the actual negative Gardner
generator hypotheses, then the checked descent implication must be
instantiated with it. No arbitrary phase is defined as the negative
NLS angle, and no full cross-mode canonicity is inferred. Corrected
Theorem 3 remains complete at every order and its exact original domain.

Validation: all 560 article/shared modules have validated private outputs. All 548 unchanged prefix source hashes match pushed 04c3df4 and their outputs were reused; all twelve added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 5,604 declarations/auxiliaries and the combined audit for 50,521 NLS declarations, using only standard allowed axioms. All 563 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 2,913 declarations (2,378 theorems and 535 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Independent Hill separated-coordinate Magri geometry

Integrated the checked Dirichlet-energy and logarithmic Dirichlet-slope
proof closure from `articles/kdv-estimates` at immutable commit
`62da59c8f580fac3a84b5fbee140a857c240df87`: 71 shared modules, plus one
extracted continuous-family zero-count helper. The four imported
continuation/count modules were adapted to this branch's established
`16*norm(q)` cutoff instead of the source branch's improved `8*norm(q)`
cutoff. No existing mathematical prefix source was changed. The original
and integrated hashes are recorded in the validation provenance.

The imported results construct the actual independent Dirichlet energy
mu_n, its normalized squared-eigenfunction gradient, and the logarithmic
Dirichlet-slope cotangent. Their first Gardner brackets are already
proved: energy-energy and log-norming/log-norming vanish; the mixed
energy/log-norming bracket is -1/2 delta. These results concern the
original Hill IVP and are independent of the NLS angular coordinates.

New proofs give the actual rough scalar second equation
`y''=(q-mu)y` almost everywhere with q in L². Both actual independent
cotangents have absolutely continuous first derivatives and actual L²
second derivatives. Their endpoint values vanish. The energy cotangent's
first derivative vanishes at both ends; the log-norming cotangent's first
derivative equals ONE at both ends, by the actual Wronskian. Its trace
must not be set to zero.

`integral_scalarHillProductMagri_eq` proves the weak Lenard identity for
products of actual rough Hill solutions, retaining the full endpoint
term. The physical weak Magri formula is

`integral (-f'' g' + 2 q (f g' - f' g))`.

No spatial derivative of the rough potential is introduced. Vanishing
test endpoint values remove the retained endpoint term and give exactly
FOUR times the first energy times the first Gardner pairing. The actual
periodic first-derivative traces prove antisymmetry of this weak pairing.
The bracket definitions use the actual gradients and their independently
proved second derivatives; no desired bracket matrix is prescribed.

`independent_Hill_weak_Magri_spectral_brackets` packages the complete raw
separated-coordinate matrix on EVERY original real period-one L² Hill
potential: energy-energy=0, energy/log-norming=-2*mu_n*delta,
log-norming/energy=+2*mu_n*delta, and log-norming/log-norming=0.
Closed periodic gaps and arbitrary spectral support are included.
`hillLogEnergy_branch_fderiv` identifies the ACTUAL derivative of
(1/2) log(mu_n) on a positive-energy analytic branch. Its rescaled
cotangent has mixed Magri bracket -delta whenever mu_n is nonzero;
the logarithmic-energy/logarithmic-energy block vanishes. These are
independently specified spectral coordinates with the required sign.

Theorem 4(iii) remains INCOMPLETE. The independent global Abelian mKdV
phase is not yet constructed. The physical periodic cotangent regularity
must be connected to the coefficient-space Miura–Magri transfer, and the
normalized Abelian phase must be proved to have the negative Gardner
unit action generators. Then the previously checked full phase-product
descent implication can be instantiated. The separated-coordinate
matrix alone does not identify the final angle or assert full Cartesian
canonicity. Corrected Theorem 3 remains complete at every order.

Validation: all 646 article/shared modules have validated private outputs. All 560 unchanged prefix source hashes match pushed 0c3df18 and their outputs were reused; all eighty-six added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 6,286 declarations/auxiliaries and the combined audit for 51,200 NLS declarations, using only standard allowed axioms. All 649 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 3,304 declarations (2,703 theorems and 601 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## Native independent spectral Gardner geometry on all real H¹ profiles

The physical-to-coefficient cotangent bridge is now proved. Actual
unit-interval Fourier integrals lift every periodic AC curve with AC
first derivative and L² second derivative into the native H² space.
Both its profile and first derivative are recovered pointwise on the
closed interval. The exact physical multiplier is 2*pi*i*n. This applies
to the original Dirichlet-energy and log-norming gradients with their
checked periodic traces, including the log-norming derivative trace one.

Unconjugated unit-interval Parseval identifies the native reflected
Hilbert pairing with the physical integral. Periodic integration by
parts identifies the native weak Magri bivector with the original weak
integral, for arbitrary L² potentials. The scalar potential and the
actual lower-component variations of the first-order Hill realization
have precisely the halved even Fourier coefficients. Neither a sign
nor a period factor is inserted into the desired bracket matrix.

The actual complex L² Fréchet derivatives of the independent original
Dirichlet branches and logarithmic multipliers are represented by these
native H² gradients. The existing full H¹ Miura transpose and bracket
transfer therefore construct actual H¹ Gardner gradients of their
mKdV pullbacks. The branches exist at every real H¹ profile, and their
energy and log-norming values agree with the original independent
spectral data along every nearby continuous real H¹ family.

Every original Dirichlet energy on the real H¹ Miura image is strictly
positive. The bottom periodic energy is nonnegative, and the first
strict band inequality puts every Dirichlet energy strictly above it.
This includes closed periodic gaps and zero-mean profiles. Consequently
the actual half-logarithmic energy gradient is valid at every real H¹
profile, with no additional positivity assumption.

`independent_mKdV_spectral_Gardner_geometry` supplies original local
spectral branches unconditionally, and proves their actual raw Gardner
matrix: energy/energy=0, energy/log-norming=-2*mu_n*delta,
log-norming/energy=+2*mu_n*delta and log-norming/log-norming=0.
The half-log-energy/log-norming bracket is exactly -delta; its reverse
is +delta and the half-log-energy/half-log-energy block vanishes.
All positive indices, arbitrary spectral support, arbitrary signed mean
and all closed gaps are included. These are actual differential and
physical Gardner brackets, rather than prescribed algebraic values.

Theorem 4(iii) remains INCOMPLETE. The original independent global
Abelian mKdV phase and its negative Gardner generators for the original
physical actions still need construction and normalization. The checked
full phase-product descent implication must then be instantiated to
obtain the source's action-and-mean dependence. The local
separated-coordinate matrix by itself does not identify that phase.
Corrected Theorem 3 remains complete on every original stated domain.

Validation: all 662 article/shared modules have validated private outputs. All 646 unchanged prefix source hashes match pushed 87afbd4 and their outputs were reused; all sixteen added modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 6,448 declarations/auxiliaries and the combined audit for 51,362 NLS declarations, using only standard allowed axioms. All 665 mathematical source/checker/aggregate hashes match the frozen inputs. The public inventory is 3,373 declarations (2,757 theorems and 616 definitions). Pinned cached dependencies were used; the entire dependency tree was not rebuilt from source. Kernel, recursion and heartbeat limits were not increased.


## 2026-11-04 — independent Abelian divisor phase construction

Integrated 342 checked shared modules from `articles/kdv-estimates` at
immutable commit `62da59c8f580fac3a84b5fbee140a857c240df87`. They give the
actual globally normalized Hill Abelian differentials, their intrinsic
periods and complex L² analytic dependence, canonical deflated root
charts, sheeted Dirichlet terminals, and quadratic Abelian corrections
through closed gaps. Of these sources, 298 are byte identical and 44
retain this article branch's established `16*norm` high-energy cutoff.
The original elementary `8*norm` estimates are used by weakening the
stronger bound where appropriate. All 662 old mathematical prefix
sources remain unchanged. Original and integrated hashes are recorded.

Eight new construction modules specify the actual sheeted terminal from
the independent Hill Dirichlet energy, signed logarithmic multiplier and
canonical root. The regular Abelian term subtracts its normalized linear
angular part. Its value is independent of the chosen real angular lift,
and is exactly zero on a closed contributing gap. Every regular term
has a local complex L² analytic representative at every original real
Hill potential, including when its contributing gap is closed.

The terminal unit phase is locally complex analytic on its own open gap,
including when the Dirichlet point is a band endpoint. Each finite partial
Abelian phase is the actual terminal phase times the exponential of the
finite sum of those regular Abelian integrals. It has norm one on its own
open gap and a local complex analytic extension even when any or all of
the other gaps are closed. A value zero at the selected closed gap is
only a convention; no angular continuity across that selected gap is
claimed.

Pullback by the literal H¹ Miura map gives these independent partial
phases on every original real H¹ profile, with arbitrary signed mean
and arbitrary spectral support. Their own domain is proved to be exactly
the nonzero ORIGINAL physical mKdV contour-action locus. The local
representative is analytic in the full complex H¹ norm and agrees on a
neighborhood in the entire original real H¹ subspace, not only along a
selected curve.

On every finite-gap Miura profile, the support selected from the original
physical actions contains all open Hill gaps. All remaining regular
corrections vanish exactly. The series therefore converges and equals
any finite sum containing that support. The resulting unit phase is
independent of the chosen finite support set and equals the literal full
Abelian series. These definitions use the independent Hill divisor and
normalized integrals; they do not assign a negative NLS phase as its value.

Theorem 4(iii) remains INCOMPLETE. The full infinite-gap correction series
still requires locally uniform convergence and its corresponding original
H¹ extension. The independent Abelian phase must then be proved to have
the negative Gardner generators for the original physical actions. The
already checked full phase-product descent can then be instantiated to
prove the printed action-and-mean dependence. No canonical generator
identity is claimed from finite truncation, convergence or unit norm alone.
Corrected Theorem 3 and the other previously completed main clauses are
unchanged.

Validation: all 1,012 article/shared modules have validated private outputs. All 662 old prefix sources match pushed 0352e43. The 342 added shared modules passed focused compilation; their compiled outputs were hash-frozen and reused. All eight original construction modules and the aggregate compiled with warnings as errors. The full targeted audit passed for 8,984 declarations/auxiliaries and the combined audit for 53,872 NLS declarations, allowing only standard axioms. All 1,015 source/checker/aggregate hashes and all 342 frozen compiled output hashes match. The public inventory is 4,622 declarations (3,853 theorems and 769 definitions, including three abbreviations). The audit declaration literals were split into 48 blocks while preserving all 3,012 prefixes and their order. No kernel, recursion or heartbeat limit was raised. Pinned cached dependencies were used; the full dependency tree was not rebuilt.

## 2026-11-04 — full independent Abelian phase for infinite-gap profiles

The full independent phase is now constructed on EVERY original real H1
Miura profile. No finite-gap, mean or other open-action restriction is
imposed. Its own original physical action alone must be nonzero for a
unit phase. On that exact domain the phase is continuous; it is bounded
by one everywhere after the existing zero convention at its own closed
action. This removes the general convergence obligation left by the
preceding finite-gap milestone.

- `independent_mKdV_full_Abelian_phase_original_H1` proves actual correction
  summability, unit norm and convergence of the natural finite partial phases.
- `independent_mKdV_full_Abelian_phase_continuous_original_H1` proves
  continuity on precisely the original own-open-action H1 locus.
- `independent_mKdV_full_Abelian_phase_native` supplies continuity and the
  global unit bound in every native integer Hs source, s>=1, on exactly
  the domain used by the full phase-product descent.
- `miuraFullAbelianPhase_eq_finiteGap` identifies the full phase with the
  previously constructed independent finite-gap phase.

The reusable proof actually works at every original real period-one L2
Hill potential. On bounded potential sets, the free-contour numerator
bound and the inverse canonical-root estimate control the deflated
numerator by an inverse square in the gap index. The endpoint root grows
at most linearly, while the free spectral separation is quadratic. The
maximum modulus principle transfers this bound to the whole spectral
gap. An explicit local analytic Hilbert parameter and nonvanishing
normalization yield locally uniform bounds for the original normalized
differential. Each actual terminal path has length at most 2*pi. Thus the
actual regular corrections have locally uniform bounds C/(k+1)^2, even
through closed contributing gaps, and the tail from M>=N is at most
2*C/(M+1). Individual term continuity and these tails give continuity of
the full sum. The phase remains the literal independent Hill divisor
construction; no NLS phase is used to prescribe its values.

The negative physical-action generators or opposite complete-action-flow
rotation law remain unproved, even in the finite-gap case. The final
angle-sum clause of Theorem 4(iii) is therefore still incomplete. Once the
actual opposite rotation is proved, the existing full phase-product
descent applies directly to `miuraNativeFullAbelianPhase`. The printed
conclusion is a function of actions and literal signed mean; no extra
complex analytic extension of the infinite phase is claimed here.

Fifteen new modules add 47 public declarations (43 theorems and four
definitions). All 1,012 previous mathematical source files are unchanged.

Validation: all 1,027 article/shared modules have validated private outputs. The fifteen new modules and aggregate compiled under strict default limits with warnings as errors. All 1,012 old mathematical prefix sources and private compiled-output hashes match the frozen pushed 8af7d58 baseline. The full targeted transitive audit passed for 9,072 declarations/auxiliaries and the combined audit for 53,960 NLS declarations, with only propext, Classical.choice and Quot.sound allowed. All 1,030 frozen mathematical source/checker/aggregate hashes match. Public inventory: 4,669 declarations (3,896 theorems and 773 definitions). The audit preserves every old scope and adds 62 scopes in a 49th array block of at most 64; no limits or linters were weakened. Canonical HEAD remains c5bcf63; cached dependencies were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — original Dirichlet motion under the physical action flows

The independent original Dirichlet energy now has its actual generator
under every original physical mKdV action. The generator is a proved
spectral circle integral. Its equality with the derivative of the original
globally labeled energy holds at EVERY real time along every complete
native integer Hs action flow, s>=1. All original real H1 profiles,
infinite action support, closed gaps and arbitrary signed mean are included.

- `independent_Dirichlet_discriminant_physical_Gardner` identifies the
  actual H1 Miura-pullback gradient and its physical bracket with the
  independent Dirichlet gradient.
- `independent_Dirichlet_original_action_contour` gives the actual
  original physical-action generator as a spectral circle integral.
- `independent_Dirichlet_energy_complete_action_motion` gives that same
  formula as the all-time derivative of the original labeled energy,
  with no chosen local branch in its statement.

The trace cotangent is proved on the full complex L2 Hill potential and
energy domain. It is the scalar cosine/sine product expression for the
actual trace derivative, with periodic value and first-derivative traces,
actual L2 second derivative, and native H2 Fourier representative. The
full complex Frechet derivative pulls back to an actual original H1
Gardner gradient. Fourier uniqueness identifies its entire native
cotangent with the original source discriminant cotangent.

An endpoint term is essential. If f_m is the original Dirichlet gradient,
mu_m its energy, d_m its terminal slope and M_m its squared-state mass,
then the physical weak Magri pairing with g is

`4*mu_m*integral(f_m*g_prime)-2*(d_m^2*g(1)-g(0))/M_m`.

For the actual trace cotangent G_E, its matching endpoint value is the
Dirichlet characteristic s(1,E). A proved mixed-product identity gives
`2*(mu_m-E)*integral(f_m*G_E_prime)=(d_m^2-1)*s(1,E)/M_m`.
The endpoint contribution therefore converts the factor mu_m to the
running contour energy E: the actual Magri trace bracket is
`4*E*integral(f_m*G_E_prime)`. This identity includes coincident energies;
no division by their difference or by a gap length is needed.

The original action field is then obtained from its actual source
cotangent, rather than from a proposed divisor velocity. The independent
energy's physical-action generator is exactly
`-(2/pi)*circleIntegral(z*integral(f_m*G_(z^2)_prime)/R_ZS(z))`
on the certified zero-excluding Laurent circle. Local analytic branches
agree with the globally labeled original Dirichlet energy along the
complete real Hs flow, so the native chain rule proves its stated motion.

The negative rotation law of the full independent Abelian phase remains
unproved. The next step is the original-sheet and normalized Abelian
period/interpolation reduction of this actual divisor motion, followed
by the already checked full phase-product descent. Theorem 4(iii) is still
incomplete; the new contour generator is not asserted to be a canonical
angle generator by itself.

Seventeen new modules add 51 public declarations (39 theorems and twelve
definitions). All 1,027 earlier mathematical sources are unchanged.

Orientation qualification: the current independent spectral phase uses
`exp(+i*sum)`. Its unit norm and continuity do not identify its orientation
with the source canonical angle vartheta. The actual generator calculation
must fix that sign; conjugating the independently constructed Hill phase
may be necessary. No negative NLS phase is used to prescribe an angle.

Validation: all 1,044 article/shared modules have validated private outputs. Seventeen new modules and the aggregate compiled with warnings as errors under default limits. All 1,027 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed 3496ba0 baseline. The complete targeted audit passed for 9,183 declarations/auxiliaries and the combined audit for 54,068 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All 1,047 frozen source/checker/aggregate hashes match. Public inventory: 4,720 declarations (3,935 theorems and 785 definitions). All 3,074 old audit scopes are preserved and 68 new scopes added in two arrays of at most 64, for 51 blocks total. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — original Dirichlet characteristic, indexed divisor and entire product

The actual scalar Dirichlet characteristic now has its exact original
product on every real H1 Miura profile. Both the product and its first
energy derivative converge locally uniformly on the whole complex energy
plane, including zero and all divisor roots. Infinite action support,
closed periodic gaps and arbitrary signed mean are included.

The underlying IVP identity holds on the entire original complex H1 domain:
`chi_(sourcePhase(u,u))(z) = z*s_Hill(z^2)` for every complex z, including zero.
The scalar characteristic remains the independently constructed position
at time one of the physical scalar Dirichlet IVP. Smooth physical uniqueness,
continuity and H1 density prove its rough scalar/quasi-Hill agreement. The
fixed source phase and transformed ZS initial state then give the exact
factor z, with no division at zero.

Real source interlacing and scalar gap-root uniqueness preserve every original
index: `r_n^2 = mu_n`, `r_-n = -r_n` and `r_0 = 0`, for n>=1. The checked
source entire characteristic products can therefore be paired into the literal
scalar factors `(mu_n-E)/(pi*n)^2`. A shared maximum-principle argument transfers
locally uniform frequency convergence to locally uniform energy convergence,
including E=0. No global continuous square root is assumed. At a positive
Dirichlet frequency the original derivatives satisfy
`chi_prime(r_n)=2*mu_n*s_Hill_prime(mu_n)`. The scalar characteristic at zero is
nonzero, as follows from the actual simple central source root.

The article interface is `OriginalDirichletCharacteristic.lean`, with:

- `independent_Dirichlet_characteristic_original_complex_domain`;
- `independent_Dirichlet_divisor_original_indices`;
- `independent_Dirichlet_characteristic_entire_product`;
- `independent_Dirichlet_original_derivative_normalization`.

Nine new modules add 35 public declarations: 32 theorems and three definitions.
All 1,044 earlier mathematical sources are unchanged. This provides the actual
characteristic and residue normalization for the remaining finite-gap Abelian
interpolation. The independent phase's canonical orientation and actual
opposite physical-action rotation still require proof. In particular, the
current exp(+i*sum) convention has not been identified with the source's
vartheta; its sign must be determined from the actual contours. Final
Theorem 4(iii) remains incomplete.

Validation: all 1,053 article/shared modules have validated private outputs. Nine new modules and the aggregate compiled with warnings as errors under default limits. All 1,044 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed ae76b2f baseline. The complete targeted audit passed for 9,250 declarations/auxiliaries and the combined audit for 54,135 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All 1,056 frozen source/checker/aggregate hashes match. Public inventory: 4,755 declarations (3,967 theorems and 788 definitions). All 3,142 old audit scopes are preserved and 44 new scopes added in one array of at most 64, for 52 blocks total. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — actual finite-gap Abelian interpolation and physical sheet normalization

The independently normalized Hill Abelian numerator now satisfies its
actual finite Dirichlet interpolation on every original real H1 Miura
profile with a closed spectral tail. A cutoff K>=n contains all possibly
open gaps. The filled formula holds at EVERY complex energy, including
zero and every retained Dirichlet node, and includes closed contributing
gaps and arbitrary signed mean:

`sum_(k<K) psi(mu_(k+1))*dslope(s,mu_(k+1),E)/s_prime(mu_(k+1))=psi(E)`.

Here s is the actual original scalar characteristic and psi is the
independently normalized Abelian differential. Closed gaps identify the
actual selected numerator and Dirichlet roots. The numerator and scalar
characteristic products consequently share the whole closed tail.
Cross multiplication of finite products, followed by their checked limits,
removes that tail even at its zeros. The remaining numerator polynomial
has degree below K because its own index is omitted. Finite Lagrange
interpolation then applies. Differentiating the actual polynomial cross
identity derives its residue coefficients from the actual scalar
characteristic derivatives; no residue is prescribed.

The independent Hill canonical energy root product now equals the physical
Miura root on the COMPLETE original Hill real-cut domain, for arbitrary
support. Both first-band signs agree, and connectedness fixes the sign
over both nonreal half-planes and every real open band.

The actual sheet and mass normalizations also agree. If d is the original
terminal slope, R its original sheet root and M its squared-state mass,
then `d*R=d^2-1` and `M=s_prime(mu)*d`. Hence
`(d^2-1)/M=R/s_prime(mu)`, including closed gaps. The exact trace-gradient
pairing becomes

`2*(mu-E)*integral(f_mu*G_E_prime)=R(mu)*s(E)/s_prime(mu)`.

This branch-free energy identity includes coincident energies. On an
interior retained divisor, and away from the retained energies, finite
interpolation gives the actual contraction

`sum_(k<K) psi(mu_(k+1))*integral(f_(k+1)*G_E_prime)/R(mu_(k+1))=-psi(E)/2`.

The minus one half is checked. This contraction assumes every retained
sheet root is nonzero. It does not yet prove a phase derivative through
terminal divisors, nor the full physical action-flow rotation law. The
next step is the actual isospectral phase differentiation and action-circle
period evaluation, followed by terminal/closed-gap continuation and
approximation to arbitrary support. The phase's final canonical orientation
remains unproved. Final Theorem 4(iii) remains incomplete.

The article interface is `IndependentAbelianInterpolation.lean`. Eight new
modules add 37 public declarations: 33 theorems and four definitions.
All 1,053 earlier mathematical sources are unchanged. One existing pinned
mathlib source, `Mathlib.LinearAlgebra.Lagrange`, was absent from the artifact
cache; the checker verifies its source SHA-256 and compiles it only into
private outputs, using its upstream implicit-variable conventions and
warnings as errors. All new NLS proofs retain autoImplicit=false and
warnings as errors. No cached source or artifact is modified.

Validation: all 1,061 article/shared NLS modules have validated private outputs. Eight new NLS modules and the aggregate compiled with autoImplicit=false and warnings as errors under default limits. One existing SHA-pinned mathlib Lagrange module compiled privately with its upstream implicit-variable conventions and warnings as errors. All 1,053 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed 0a5080d baseline. The complete targeted audit passed for 9,327 declarations/auxiliaries and the combined audit for 54,212 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All 1,064 frozen source/checker/aggregate hashes and the additional pinned mathlib source hash match. Public inventory: 4,792 declarations (4,000 theorems and 792 definitions). All 3,186 old audit scopes are preserved and 45 new scopes added in one array of at most 64, for 53 blocks total. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — actual independent full-phase generator under physical actions

The independent Hill spectral data are now invariant along the original
complete NLS action flows on every native real Hs class, s>=1, at every
time and with arbitrary support. Actual source isospectrality fixes all
Hill periodic labels. The independent normalized-differential uniqueness
result then fixes the selected entire numerator, cosine differential and
regular primitive; no invariance of an arbitrary choice is assumed.

The full independent phase on an actual finite-gap orbit has its derivative
at each time with interior contributing divisors. Any finite set F containing
n-1 may contain the possibly open gaps; gaps outside F are closed. Holes and
other closed gaps between contributing indices are allowed. Local real
Dirichlet angle lifts, the actual cosine primitive FTC and the actual
isospectral Hill coefficient curve give the chain rule

`P' = i*P*sum_F psi(mu_k)*mu_k'/R_sheet(mu_k)`.

Here the velocities are those of the globally labeled original Dirichlet
energies along the physical action flow. Closed holes have zero normalized
numerator values. Finite interpolation therefore gives the trace contraction
on F without assuming all gaps below a cutoff are open. The actual physical
frequency contour avoids every Dirichlet energy, including closed gaps;
analytic trace kernels justify the finite sum/integral exchange. Substituting
the checked actual energy velocities proves

`P' = (i/pi)*P*integral_Cj z*psi(z^2)/R_ZS(z)`.

Cj is the original certified Laurent action circle, not a prescribed divisor
motion or an assumed Abelian normalization contour. The positive i/pi is
proved for the current exp(+i*sum) convention. Its period still needs to be
compared with the independent normalized Hill energy period. Once the sign
is fixed, the independently constructed spectral phase may need conjugation
to match the source's opposite-flow orientation.

This milestone does not assert a Kronecker rotation law. Extending the
calculation through terminal divisors and closed contributing gaps, passing
rotation to arbitrary support, and applying the checked full-phase descent
remain essential. Theorem 4(iii)'s final angle-sum factorization stays open.
The article interface is IndependentAbelianPhaseMotion.lean. Sixteen new
modules add 41 public declarations: 39 theorems and two definitions. All
1,061 earlier mathematical sources are unchanged.

Validation: all 1,077 article/shared NLS modules have validated private outputs. Sixteen new NLS modules and the aggregate compiled with autoImplicit=false and warnings as errors under default limits. The full audit was rerun after restoring one omitted old block reference; all 54 audit blocks are referenced exactly once. All 1,061 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed d25fdb5 baseline. The complete targeted audit passed for 9,400 declarations/auxiliaries and the combined audit for 54,285 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All 1,080 frozen source/checker/aggregate hashes and the additional pinned mathlib source hash match. Public inventory: 4,833 declarations (4,039 theorems and 794 definitions). All 3,231 old audit scopes are preserved and 57 new scopes added in one array of at most 64, for 54 blocks total. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — exact physical Abelian periods and source-oriented phase generators

The independent normalized Hill differential now has its exact period on
the ORIGINAL physical frequency circle for EVERY real H1 Miura profile:

`integral_Cj z*psi_n(z^2)/R_ZS(z) = pi*delta_(j,n)`.

This has arbitrary support and arbitrary signed mean. Both indices are any
positive integers. Collapsed indexed gaps and closed other gaps are included;
no finite-gap or interior-divisor hypothesis enters this period identity.
The circle may be any intermediate circle in an actual all-index physical
Cauchy family containing that source, including the original Laurent atlas
circle used in the checked action generator.

The enclosing original source disc and its exclusion of adjacent segments
put the squared real crossings in the two adjacent independent Hill bands.
The lower band at index one is included using the actual central gap and
its nonnegative right endpoint. Squaring the original frequency-circle path
and comparing it directly with the intrinsic energy-circle path gives a
smooth affine loop homotopy. Its imaginary part has the sign of the same
sine with a strictly positive coefficient. If that sine vanishes, cosine
is plus or minus one and the real interpolation lies in one open band.
Thus the entire homotopy stays in the full Hill real-cut domain. The already
checked independent canonical root agrees with the original physical root
there. The literal Jacobian2*z and the intrinsic (2*pi)^(-1) period yield
positive pi, with NO extra imaginary unit.

Consequently the original exp(+i*sum) full independent phase has actual
positive i*delta action generators at interior finite-gap divisors. Its
spectral conjugate, miuraNativeOppositeAbelianPhase, has the source-oriented
negative i*delta generators. It uses only the independent Hill spectral
construction. No NLS angle enters its definition. On every native real Hs
class, s>=1, it has norm at most one globally, unit norm on the exact own-open
angular domain, zero on its own closed domain and continuity on its own-open
domain, with arbitrary support.

The actual finite-gap full phase and its spectral conjugate are also now
DIFFERENTIABLE through every terminal and closed configuration along every
positive physical action flow. This follows from the local complex analytic
extension of the actual finite partial phase and the actual differentiable
rough Hill action curve. Isospectrality identifies the finite and full phases
along the entire finite-gap orbit. An own closed gap makes the full phase
zero on the entire orbit. No contributing sheet nonvanishing hypothesis is
needed for differentiability.

Differentiability alone does not prove the negative canonical derivative
value at terminals. Extending that value through terminal divisors and
closed contributing gaps, integrating the all-configuration finite-gap ODE,
passing rotation to arbitrary support and instantiating full phase-product
descent remain essential. Final Theorem4iii remains incomplete.

The article interface is IndependentAbelianPhasePeriods.lean. Ten new modules
add 28 public declarations: 27 theorems and one definition. All 1,077 earlier
mathematical sources are unchanged.

Validation: all 1,087 article/shared NLS modules have validated private outputs. Ten new NLS modules and the aggregate compiled with autoImplicit=false and warnings as errors under default limits. All 1,077 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed c941fe9 baseline. The complete targeted audit passed for 9,462 declarations/auxiliaries and the combined audit for 54,345 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All 1,090 frozen source/checker/aggregate hashes and the additional pinned mathlib source/private-output hashes match. Public inventory: 4,861 declarations (4,066 theorems and 795 definitions). All 3,288 old audit scopes are byte-preserved and 38 new scopes added in one array of at most 64, for 55 blocks total, each referenced exactly once. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — full-phase Lie continuity and actual terminal-translation geometry

The SOURCE-ORIENTED FULL independent Abelian phase now has a continuous
actual physical-action Lie derivative on every fixed finite-gap stratum,
in every native real Hs norm, s>=1. Its own action must be open; every other
action may be closed, every contributing Dirichlet point may be terminal,
and the finite set F may contain closed gaps. The Lie derivative is the
literal derivative at zero of the original complete J_j action flow.

The actual native action velocity has a local complex holomorphic extension
from the checked native Cartesian inverse charts. Uniqueness identifies it
with the original complete-flow velocity. Therefore the actual Lie derivative
of any locally analytically extended functional has its own local holomorphic
extension. Applying this to the original finite partial Abelian phase and
using full/finite equality along every orbit in a fixed closed complement
proves full-phase Lie continuity. Conjugation gives the source orientation.

The actual period-one Fourier translation is norm continuous in every native
real Hs class and preserves the original source spectrum and multiplicities.
The checked source-translation theorem then fixes EVERY indexed independent
Hill label. Thus the same finite-gap stratum is preserved by every translate.

The original physical whole-line L2 solution for a continuous periodic profile
now satisfies its continuous ODE at EVERY real time, including all integer
seams. Its original propagator conjugates the actual translated unit-interval
classical monodromy for arbitrary real shifts. The independent quasi-Hill
fundamental matrix is constructed from its actual Volterra columns and has
Wronskian/determinant one at every complex energy, including zero. Its literal
Miura basis matrix has determinant -2*z, intertwines the actual ZS matrices,
and gives conjugacy for z nonzero. The corresponding translated independent
quasi-Hill monodromy intertwines with the original monodromy through the
original whole-line propagator in that basis.

There is now an actual terminal-release formula. If the ORIGINAL quasi-Hill
monodromy at E=z^2, z nonzero, is the parabolic matrix [[epsilon,0],[c,epsilon]],
then its translated scalar Dirichlet characteristic equals

`-c*(original fundamental Dirichlet position at the shift)^2`.

The original Dirichlet position has derivative one at zero, so it is nonzero
at all sufficiently small positive shifts. If c is nonzero, the translated
characteristic is consequently nonzero at that endpoint. The actual-matrix
hypothesis is explicit: it has NOT yet been derived at every original open
Hill endpoint or counted as a completed density theorem.

For every actual real period-one L2 Hill potential, the original energy
trace has nonzero derivative at BOTH endpoints of EVERY positive open gap.
The checked all-index multiplicity formula makes these radicand zeros simple;
the original trace derivative cannot vanish there. No finite-gap or high-index
restriction is used.

The next bridge is to derive the nontrivial parabolic monodromy at every
actual open endpoint from determinant one, the original terminal data and
the now checked nonzero trace derivative. Then identify actual native Miura
translations with the continuous quasi-Hill coefficient translates. The
resulting actual interior-density statement, together with full-phase Lie
continuity, will give canonical terminal generator values. Integration of
the finite-gap ODE, rotation for arbitrary support and full phase-product
descent still remain. Final Theorem4iii is incomplete.

The article interface is IndependentAbelianTerminalGeometry.lean. Fourteen
new modules add 69 public declarations: 55 theorems and 14 definitions.
All 1,087 earlier mathematical sources are unchanged.

Validation: all1,101 article/shared NLS modules have validated private outputs. Fourteen new NLS modules and the aggregate compiled with autoImplicit=false and warnings as errors under default limits. All1,087 earlier mathematical source hashes and private compiled-output hashes match the frozen pushed49d2806 baseline. The complete targeted audit passed for 9,550 declarations/auxiliaries and the combined audit for 54,430 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All1,104 frozen source/checker/aggregate hashes and the additional pinned mathlib source/private-output hashes match. Public inventory:4,930 declarations(4,121 theorems and809 definitions). All3,326 old audit scopes are byte-preserved and83 new scopes added in two arrays of at most64, for57 blocks total, each referenced exactly once. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source.

## 2026-11-04 — final independent phase rotation and angle-sum theorem

The remaining clause of Theorem4(iii) is proved on the full original real
H1 domain. The independent source-oriented phase is the spectral conjugate
of the original full Hill Abelian phase, defined from actual Dirichlet data
and normalized Abelian integrals. It rotates by exp(-i*delta*t) under every
complete physical action flow, for every real time and arbitrary action
support. Its product with the actual restricted NLS unit phase is a function
of all physical actions and literal signed mean alone. Only its own angle
must be open; every other action may be closed. The full unit phases retain
angles modulo exactly 2*pi. No analytic angle-sum factor is assumed or claimed.

The endpoint argument is now unconditional at actual open Dirichlet
endpoints. Original energy-entire monodromy columns and determinant one
force the parabolic form. Scalar monodromy would force zero energy trace
derivative; actual simple open endpoints exclude it, proving that the lower
entry is nonzero. Literal Sobolev synthesis identifies native spatial
translation with the original coefficient translate. The translated actual
Dirichlet characteristic is nonzero at both fixed endpoints for every
sufficiently small positive shift. Finite intersections give simultaneous
interior divisors for all open contributing gaps. Closed contributors are
filtered out without changing the finite closed-gap complement.

Norm continuity of the actual full phase Lie derivative on that stratum
extends its checked negative Kronecker value to every finite-gap terminal.
The actual action group law and scalar ODE uniqueness give the complete
finite-gap rotation. Finite normalized Cartesian truncations decode to
actual finite-gap profiles and converge in native Hs. Conjugacy to a fixed
bounded Cartesian rotation gives continuity of the action flow in its
initial profile. Phase continuity on its exact own-open domain passes the
rotation law to arbitrary support. The checked full phase-product descent
is instantiated with this actual independent spectral phase.

The final article interface is IndependentAbelianAngleSum.lean:

- independent_full_phase_complete_action_rotation
- independent_full_phase_actual_action_generator
- theorem4_iii_independent_phase_sum (all native integer Hs, s>=1)
- theorem4_iii_independent_angle_sum (original full real H1 domain)
- theorem4_iii_angle_sum_representatives (any real phase representatives)

Twelve new modules add 43 public declarations: 40 theorems and three
definitions. All 1,101 earlier mathematical sources are unchanged. The
main source theorems are complete with the already documented corrections:
Theorem2(ii)'s matrix, the positive frequency sign in Theorem3, and mean
squared in the reverse clause of Theorem4(ii). There are no remaining
essential mathematical obligations. Full aggregate compilation and both transitive axiom audits passed; the
final evidence is recorded below.

Final validation: all1,113 article/shared NLS modules have validated private outputs. Twelve new NLS modules and the aggregate compiled with autoImplicit=false and warnings as errors under default limits. All1,101 earlier mathematical source hashes and private compiled-output hashes match the frozen pushedfdb5ac0 baseline. The complete targeted audit passed for 9,615 declarations/auxiliaries and the combined audit for 54,495 NLS declarations, allowing only propext, Classical.choice and Quot.sound. All1,116 frozen source/checker/aggregate hashes and the additional pinned mathlib source/private-output hashes match. Public inventory:4,973 declarations(4,161 theorems and812 definitions). All3,409 old audit scopes are byte-preserved and55 new scopes added in one array of at most64, for58 blocks total, each referenced exactly once. No limits or linters were weakened. Canonical HEAD remains c5bcf63; cached imports were read only. The entire dependency tree was not rebuilt from source. All main source claims are complete with the three documented corrections.

## 2026-11-04 — PR3 merge conflict resolved against main

Merged main 84370cf54a96 into the article branch. The only conflict
was the final import block in NLS.lean; the resolution preserves the exact
union of both parents' imports. No mathematical proof source changed. The
focused checker now also compiles the dNLS article module imported by main.

The additional dNLS module and merged aggregate compiled with strict
default options. All 1,113 existing article source/private-output hashes
were verified. Fresh transitive axiom audits passed for 9,615 article
declarations and auxiliaries and 54,506 NLS declarations. All 219 incoming
main modules were also imported together with the merged aggregate using
their source-hash-verified private outputs; that fresh compatibility audit
passed for 55,356 NLS declarations. Only propext, Classical.choice
and Quot.sound are allowed. All 1,117 frozen inputs and pinned import hashes
match. This reuses validated dependencies and is not a full source rebuild.

The main theorem coverage and the three documented source corrections are
unchanged. See merge-validation.json for exact parents, hashes and scope.
