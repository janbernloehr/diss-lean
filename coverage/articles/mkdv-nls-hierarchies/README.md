# The mKdV and NLS hierarchies revisited — verification coverage

Status: **Theorems 1 and 2 proved on their original complex Sobolev domains,
with the matrix correction in Theorem 2(ii); Theorem 4(i) proved on the full original
real H1 domain; Theorem 4(iii)'s angle-action bracket clause proved on its
original real H1 angle domain. Theorem 4(ii)'s converse J_n clause, its
sign-invariant mean-squared correction and its whole-sequence forward
factorization near zero are proved. Theorems 3 and 4(ii)-(iii) as whole
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
| Theorem 1, p. 3 | For each integer m>=1, all complex u in H^m: `X_(S_(2m))#=(Y_(K_m),Y_(K_m))` and `S_(2m)#=0`. | **Proved** by `theorem1`, with the actual native Frechet gradient and Gardner distribution derivative. `smoothMiuraSpectralHamiltonian` extracts K_m from the independent physical Hill discriminant through recursive coefficient limits on all smooth complex profiles. Its unique continuous extension to the complete complex H^(m-1) domain exists and is entire analytic; `miuraSpectralHillHamiltonian_eq_native` identifies it with the independent scalar Riccati hierarchy. `proposition6` gives the full native factor-two identity, including the L2 mass endpoint. | None for Theorem 1. The source's actual finite-gap primitive Laurent series also has exactly these spectral Hamiltonians as its coefficients. |
| Theorem 2(i), p. 3 | For every k>=1, every pair phi in H^(k-1), every real alpha: swap and phase-gradient identities, then the induced vector-field covariance. | **Proved.** `theorem2_i_swap_gradients`, `theorem2_i_phase_gradients`, `theorem2_i_swap_vector_fields` and `theorem2_i_phase_vector_fields` give all four printed identities on exactly H^(k-1), including H0 when k=1. The analytic L2 gradient represents the actual physical Hamiltonian's Frechet derivative. | None. |
| Theorem 2(ii), p. 3 | For each m>=1 and pair in H^(2m-1), assuming `P phi=R_alpha phi` for some real alpha, the even/odd gradient recurrence. | **Proved with the matrix corrected to R=diag(i,-i).** `theorem2_ii_corrected` uses Mathlib's actual distribution derivative of the physical period-one L2 fields; its value is represented by the certified even L2 gradient. `theorem2_ii_corrected_coefficients` gives the equivalent 2*pi*i*j Fourier identity. Both retain the exact complex source domain and phase hypothesis. | None for the corrected assertion; the printed matrix typo is recorded below. |
| Theorem 3, p. 4 | For every n>=1 and m>=1, equality of the restricted NLS frequency and mKdV frequency on real H^(m-1), including collapsed actions by analytic extension. | Existing NLS normal-form/frequency machinery can be reused after the mKdV side is identified. | Complete action factorization and independent mKdV angle/frequency identification with the recorded sign correction; the actual Gardner bracket transfer is proved. |
| Theorem 4(i), p. 4 | For all real u in H^1: central NLS action zero iff mean zero; for each n>=1, restricted I_n zero iff J_n zero; restricted I_(-n)=I_n. | **Proved** by `theorem4_i` on the full real H1 domain, including collapsed gaps and zero mean. The mKdV action is the literal inverse-energy-weighted integral of the independent physical Hill primitive on a proved isolating contour; its equality with a positive real-gap integral and contour independence are checked. | None for part (i). Parts (ii)-(iii) remain open; the common complex-source action extensions are now proved by Lemma 7. |
| Theorem 4(ii), p. 4 | On real H^1, each I_n# is analytic in the mKdV actions and mean; conversely each J_n and the printed mean are analytic in NLS actions alone. | **The converse J_n clause is proved**, with holomorphic factors on open complex ℓ¹ action neighborhoods. The corrected mean squared has such a factor even at zero mean. Every integer physical mKdV action level also factors. Actual restricted NLS actions commute with every J_n under the Gardner bracket. | The whole-sequence forward factor is proved near zero, including on the literal original H1 domain; prove global forward factorization at general profiles. Signed mean needs a sign branch; the global correction proved here is mean squared. |
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
