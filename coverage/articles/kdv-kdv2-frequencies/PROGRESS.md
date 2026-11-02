# KdV/KdV2 frequencies — branch progress

**Main-theorem status: not yet verified.**

The user authorized separate worktrees and publishing validated article
progress on 2026-11-02. The actual worktree is:

```text
/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-kdv-kdv2-frequencies/outputs/dnls
```

Branch: `articles/kdv-kdv2-frequencies`; base:
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. The app's managed-worktree API
rejects the canonical repository as an unregistered source workspace, so this
is an ordinary Git worktree, as subsequently authorized. The canonical main
checkout's files and branch remain unchanged. The path is also saved in the
private chat's `work/worktree.json` for future turns. Commands must explicitly
use this worktree directory.

## Checked mathematical progress

The initial validated patch has been applied and checked again in this
worktree. Its generic and signed-locus flow results are dependencies of
Appendix E.1(i)-(ii) and Theorem 4.14(i). Its mass-phase adapter is a
dependency of Theorem 1.12(v). These remain generic or explicitly conditional
adapters; they do not establish actual spectral KdV/KdV2 frequencies.

The new `NLS/Articles/KdVKdV2Frequencies/SmoothKdVIdentities.lean` proves
identities concerning the actual equations:

| Source correspondence | Proved content |
| --- | --- |
| Hamiltonians and Gardner bracket, PDF p. 2, equations (1)-(3), pp. 1-2 | The finite Euler-Lagrange expressions of the doubled densities are twice the explicit gradient polynomials. Applying the spatial jet derivation to these gradients gives exactly `-u_xxx+6u u_x` and `u_xxxxx-10u u_xxx-20u_x u_xx+30u² u_x`. The source factor `1/2` is retained by doubling both sides of the Euler-Lagrange identity. |
| Same equations, evaluated on smooth fields | The previously proved generic jet-evaluation derivative theorem yields genuine `HasDerivAt` statements for the evaluated gradients, with the literal PDE right sides as derivatives. Smoothness is an explicit hypothesis, not an assumption of spectral identities. |
| Nonzero-mean reductions in Remarks 3.7(ii) and 4.6(ii), pp. 32 and 44 | For every scalar field and constant `c`, `V1(c+u)=V1(u)+6c u_x` and `V2(c+u)=V2(u)+10c V1(u)+30c² u_x`. These are the physical vector-field identities needed before transferring the mean-zero result to other leaves. They are not assertions that the spectral frequency formulas have already been proved. |
| Mean preservation and mass level sets in Theorem 1.12, pp. 7-8 | For every smooth period-one field, `∫ V1(u)=∫ V2(u)=0` and `∫ u V1(u)=∫ u V2(u)=0`. Explicit total-derivative fluxes establish the quadratic mass balances using the existing periodic integration theorem. This is the spatial balance needed for conservation along smooth solutions; differentiating a time-dependent solution integral remains a separate analytic obligation. |

The smooth differential identities are proved over complex scalar fields,
so they cover real fields viewed in the complexification. The later physical
solution construction must still retain the real subspace and its native
Sobolev norms. No low-regularity multiplication of distributions is asserted.

## Validation and build isolation

Run from this article worktree:

```bash
bash scripts/check-kdv-kdv2-frequencies.sh
```

The checker uses pinned Lean 4.33.1/mathlib v4.33.1 and rejects warnings.
It compiles all four article-step modules and runs
`scripts/CheckKdVKdV2FrequencyCandidates.lean`, auditing their declarations
and all imported `NLS` declarations transitively. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. See `VALIDATION.md` for the
exact result and scope.

Mutable outputs live in this worktree's `.lake/build/lib/lean`. A separate
`.lake/article-imports` overlay points to read-only canonical compiled imports
and this worktree's own output files. The checker writes only to this
worktree's build directory. It does not run Lake against the overlay, copy the
21 GB cache or overwrite canonical build products. The explicit toolchain
paths are necessary because the existing `scripts/lake.sh` fallback is
relative to the original checkout. Expensive full validations still require
`/tmp/diss-lean-article-build.lock`.

## Next main-theorem requirements

The KdV foundation branches were inspected before this step and still pointed
to the shared article-plan base; no committed Hill/Birkhoff additions were
available to consume at that inspection. No cross-chat message was sent.

1. Consume the shared physical Hill/Birkhoff construction from
   `kdv-estimates` and action Hamiltonians from `kdv-convexity` when published.
2. Construct the actual KdV and KdV2 frequency moment formulas and establish
   their locally uniform analytic estimates. The action-frequency parameter
   in the generic flow theorem must be instantiated with these constructed
   functions, with compatibility across all stated regularities.
3. Prove the actual smooth PDE/Birkhoff flow identification with the source's
   Hamiltonian time orientation, then approximation by every smooth initial
   sequence in the native Sobolev norm. The polynomial identities here
   resolve the local differential algebra, not the spectral identification.
4. For Theorem 1.12(ii), establish analytic bounded frequency corrections on
   fixed-mass leaves and the stated bounded-set uniform estimates. For
   (iii)-(iv), construct physical separating pairs in every nonempty open
   set, preserving fixed mass where required.
5. For (v), prove divergence of physical mass along suitable smooth
   approximants to every non-L2 datum and transfer the checked phase
   obstruction through the actual Birkhoff map. Preserve the distinction
   between compact-time and fixed-time nonextension claims.

The detailed endpoint and quantifier inventory remains in `SOURCE_MAP.md`.
All actual article main theorems remain open; no unproved spectral or physical
assumption is counted as a verified main theorem.
