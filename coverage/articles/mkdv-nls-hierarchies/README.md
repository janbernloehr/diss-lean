# The mKdV and NLS hierarchies revisited — verification coverage

Status: **Theorem 2 proved on its original complex Sobolev domains, with the
matrix correction in part (ii); Theorem 4(i) proved on the full original
real H1 domain; Theorem 4(iii)'s angle-action bracket clause proved on its
original real H1 angle domain. Theorem 4(ii)'s converse J_n clause and its
sign-invariant mean-squared correction are proved. Theorems 1, 3 and 4(ii)-(iii) as whole
statements remain incomplete**.
Prepared 2026-11-02 against canonical commit
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`.

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
| Theorem 1, p. 3 | For each integer m>=1, all complex u in H^m: `X_(S_(2m))#=(Y_(K_m),Y_(K_m))` and `S_(2m)#=0`. | **Scalar clause proved on the exact H^m domain** by `theorem1_even_vanishing_sharp`. `theorem1_native_miura_hierarchy` proves both clauses on every complex H^m input using independently constructed K_m on its full native H^(m-1) domain, with actual Frechet gradients and the genuine distribution derivative. `proposition6_native_miura` proves the odd factor-two identity on all complex H^(m-1), including the L2 mass endpoint. The literal Hill discriminant now has an all-order trace estimate with phase coefficients 2*K_m. | Finite-gap spectral Laurent calibration is now proved with the native K coefficients; complete the extension/uniqueness identification on the entire original native complex Sobolev domains. |
| Theorem 2(i), p. 3 | For every k>=1, every pair phi in H^(k-1), every real alpha: swap and phase-gradient identities, then the induced vector-field covariance. | **Proved.** `theorem2_i_swap_gradients`, `theorem2_i_phase_gradients`, `theorem2_i_swap_vector_fields` and `theorem2_i_phase_vector_fields` give all four printed identities on exactly H^(k-1), including H0 when k=1. The analytic L2 gradient represents the actual physical Hamiltonian's Frechet derivative. | None. |
| Theorem 2(ii), p. 3 | For each m>=1 and pair in H^(2m-1), assuming `P phi=R_alpha phi` for some real alpha, the even/odd gradient recurrence. | **Proved with the matrix corrected to R=diag(i,-i).** `theorem2_ii_corrected` uses Mathlib's actual distribution derivative of the physical period-one L2 fields; its value is represented by the certified even L2 gradient. `theorem2_ii_corrected_coefficients` gives the equivalent 2*pi*i*j Fourier identity. Both retain the exact complex source domain and phase hypothesis. | None for the corrected assertion; the printed matrix typo is recorded below. |
| Theorem 3, p. 4 | For every n>=1 and m>=1, equality of the restricted NLS frequency and mKdV frequency on real H^(m-1), including collapsed actions by analytic extension. | Existing NLS normal-form/frequency machinery can be reused after the mKdV side is identified. | Complete action factorization and independent mKdV angle/frequency identification with the recorded sign correction; the actual Gardner bracket transfer is proved. |
| Theorem 4(i), p. 4 | For all real u in H^1: central NLS action zero iff mean zero; for each n>=1, restricted I_n zero iff J_n zero; restricted I_(-n)=I_n. | **Proved** by `theorem4_i` on the full real H1 domain, including collapsed gaps and zero mean. The mKdV action is the literal inverse-energy-weighted integral of the independent physical Hill primitive on a proved isolating contour; its equality with a positive real-gap integral and contour independence are checked. | None for part (i). Parts (ii)-(iii) remain open; the common complex-source action extensions are now proved by Lemma 7. |
| Theorem 4(ii), p. 4 | On real H^1, each I_n# is analytic in the mKdV actions and mean; conversely each J_n and the printed mean are analytic in NLS actions alone. | **The converse J_n clause is proved**, with holomorphic factors on open complex ℓ¹ action neighborhoods. The corrected mean squared has such a factor even at zero mean. Every integer physical mKdV action level also factors. Actual restricted NLS actions commute with every J_n under the Gardner bracket. | Prove the forward factorization of I_n# through J and mean. Signed mean needs a sign branch; the global correction proved here is mean squared. |
| Theorem 4(iii), p. 4 | For all positive n,m, the angle-action Gardner bracket is delta_mn where the relevant angle is defined; angle sums then depend on actions and mean. | **The angle-action bracket clause is proved** by `theorem4_iii_angle_action` on every real H1 input where the angle is defined. The action index may have a closed gap. The actual Gardner distribution derivative and original NLS angle differential are identified. | Construct the independent mKdV angle and prove the final angle-sum factorization through J and mean. |

The main dependencies singled out by the article are Theorem 5 (p. 9,
Miura/Hill versus diagonal ZS discriminants), Proposition 6 (p. 12,
`K_m=S_(2m-1)#/2` and even vanishing), Lemma 7 (p. 12, action comparison),
Theorem 6 (pp. 13–14, discriminant symmetries), Lemma 10 (pp. 16–17,
action-gradient identities) and Proposition 11 (pp. 17–18, hierarchy gradients).
These are dependencies of the four main theorems, not extra completion targets.

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

These observations are recorded to prevent an incorrect formal target. No Lean
counterexample modules or refutations have been added.

1. Theorem 2(ii) and Proposition 11(ii) print `-i*J` in their recurrence,
   while the summation proof on p. 18 yields `R*partial S_(2m) =
   partial_x partial S_(2m-1)`, with `R=diag(i,-i)` defined on p. 13.
   The subsequent proof of Theorem 1 uses precisely this R identity, followed
   by multiplication by P. The corrected R recurrence is now proved at every
   order on the full printed complex Sobolev domain, with the actual derivative
   and no additional smoothness or real-type hypothesis.
2. Theorem 3 prints the factor `(-1)^m`. Its proof on p. 18 ends with
   `eta_(n,m)=omega_(n,2m)#` using the stated angle brackets and Theorem 1.
   A final target must use one consistent Hamiltonian/frequency convention;
   the candidate proofs have not inserted the printed factor into existing H_k.
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


Latest milestone: **The converse action clause of Theorem 4(ii) is proved** by
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
