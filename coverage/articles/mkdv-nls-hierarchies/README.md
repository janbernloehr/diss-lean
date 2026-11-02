# The mKdV and NLS hierarchies revisited — initial verification

Status: **partial progress; no complete article main theorem is claimed**.
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
identification and its variational derivative still require a checked adapter.
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
| Theorem 1, p. 3 | For each integer m>=1, all complex u in H^m: `X_(S_(2m))#=(Y_(K_m),Y_(K_m))` and `S_(2m)#=0`. | `theorem1_even_vanishing_original_domain` proves scalar vanishing on H^(2m-1), including the exact H^1 endpoint m=1. `classicalNLSHamiltonian_one_diagonal` and `classicalNLSHamiltonian_three_diagonal` prove the physical factor-two identities for K1 and K2. `theorem1_m2_smooth` now proves both clauses on smooth complex periodic potentials. | All-order independent mKdV/Hill Hamiltonian identification; physical gradients and vector fields; the sharper H^m even-order extension for m>1. |
| Theorem 2(i), p. 3 | For every k>=1, every pair phi in H^(k-1), every real alpha: swap and phase-gradient identities, then the induced vector-field covariance. | `theorem2_i_swap_covectors` and `theorem2_i_phase_covectors` establish the corresponding **complex Frechet-covector** identities on precisely H^(k-1). They are unconditional identities of the existing physical Hamiltonians. | Identify the covectors with the printed L^2 gradients and transfer through the physical Poisson structure. Covector results alone are not reported as the full theorem. |
| Theorem 2(ii), p. 3 | For each m>=1 and pair in H^(2m-1), assuming `P phi=R_alpha phi` for some real alpha, the stated even/odd gradient recurrence. | Existing analytic Hamiltonians and new symmetries are available. | Resolve the matrix correction below and prove the physical gradient recurrence. No caller-supplied hierarchy-identification assumption is used as a substitute. |
| Theorem 3, p. 4 | For every n>=1 and m>=1, equality of the restricted NLS frequency and mKdV frequency on real H^(m-1), including collapsed actions by analytic extension. | Existing NLS normal-form/frequency machinery can be reused after the mKdV side is identified. | Construct/identify the mKdV actions, frequency and brackets; settle the printed sign against the adopted normalization. |
| Theorem 4(i), p. 4 | For all real u in H^1: central NLS action zero iff mean zero; for each n>=1, restricted I_n zero iff J_n zero; restricted I_(-n)=I_n. | Existing physical NLS actions are available, not an mKdV action identification. | Prove the Miura/Hill discriminant and action comparison with fixed gap labels. |
| Theorem 4(ii), p. 4 | On real H^1, each I_n# is analytic in the mKdV actions and mean; conversely each J_n and the printed mean are analytic in NLS actions alone. | No new analytic factorization is claimed. | Prove action factorization and specify the signed-mean branch/correction discussed below. |
| Theorem 4(iii), p. 4 | For all positive n,m, the angle-action Gardner bracket is delta_mn where the relevant angle is defined; angle sums then depend on actions and mean. | Existing NLS canonical identities are potential inputs only. | Construct mKdV angle domains, handle collapsed gaps correctly, and prove bracket transfer and analytic continuation. |

The main dependencies singled out by the article are Theorem 5 (p. 9,
Miura/Hill versus diagonal ZS discriminants), Proposition 6 (p. 12,
`K_m=S_(2m-1)#/2` and even vanishing), Lemma 7 (p. 12, action comparison),
Theorem 6 (pp. 13–14, discriminant symmetries), Lemma 10 (pp. 16–17,
action-gradient identities) and Proposition 11 (pp. 17–18, hierarchy gradients).
These are dependencies of the four main theorems, not extra completion targets.

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

## Source corrections still to resolve

These observations are recorded to prevent an incorrect formal target. No Lean
counterexample modules or refutations have been added.

1. Theorem 2(ii) and Proposition 11(ii) print `-i*J` in their recurrence,
   while the summation proof on p. 18 yields `R*partial S_(2m) =
   partial_x partial S_(2m-1)`, with `R=diag(i,-i)` defined on p. 13.
   The subsequent proof of Theorem 1 uses precisely this R identity, followed
   by multiplication by P. The corrected R recurrence is the candidate target;
   its all-order physical proof remains open.
2. Theorem 3 prints the factor `(-1)^m`. Its proof on p. 18 ends with
   `eta_(n,m)=omega_(n,2m)#` using the stated angle brackets and Theorem 1.
   A final target must use one consistent Hamiltonian/frequency convention;
   the candidate proofs have not inserted the printed factor into existing H_k.
3. The signed mean in the converse of Theorem 4(ii) needs a branch restriction
   or an appropriate sign-invariant replacement. The p. 13 proof recovers it
   from an inverse cosh. NLS spectral actions are unchanged by the phase
   rotation sending diagonal u to -u, whereas the signed mean changes sign.
   No global signed-mean analytic factorization is marked verified.

## Existing proofs reused

- `NLS/ZakharovShabat/SobolevNLSHamiltonianHierarchy.lean`: original physical
  Hamiltonians, entire analyticity, mass and momentum calibration.
- `NLS/ZakharovShabat/SobolevNLSHierarchyTrace.lean`: physical all-order
  higher-action trace, including a common open complex neighborhood and
  absolute convergence. This is a trace identity, not the missing gradient
  recurrence or an mKdV identification.
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
discriminant identity and expanded validation are
recorded in [the progress log](PROGRESS.md). The original full main theorems
remain incomplete.

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
