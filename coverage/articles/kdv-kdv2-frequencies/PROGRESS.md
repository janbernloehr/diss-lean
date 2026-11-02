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
It compiles the article modules and required shared sequence modules, and runs
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

The original inspection found no foundation commits beyond the shared plan.
A subsequent inspection found the Hill line through `0b58631` and the action
contour analytic-summation line through `be9eba0`. These do not yet supply
the physical Birkhoff map and actual spectral frequency identities needed
by the main theorems. No cross-chat message was sent.

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
5. For (v), transfer the now-proved signed endpoint mass-divergence and
   finite-truncation obstruction to actual physical smooth approximants
   through the constructed Birkhoff map. Preserve the distinction
   between compact-time and fixed-time nonextension claims.

The detailed endpoint and quantifier inventory remains in `SOURCE_MAP.md`.
All actual article main theorems remain open; no unproved spectral or physical
assumption is counted as a verified main theorem.


## Endpoint-mass milestone

`SignedMassDivergence.lean` now proves the exact positive-index mass/endpoint
regularity equivalence, mass divergence for every coefficientwise
endpoint-regular approximation, and signed finite-truncation construction
and native norm convergence. Its compact-time nonextension theorem no longer
assumes mass divergence or the existence of approximants: both are proved.
The remaining frequency-correction and physical phase identity inputs stay
explicit. See [the detailed source correspondence](MASS_NONEXTENSION.md).

The finite-partial-sum argument was generalized to
`NLS/SequenceSpaces/NonnegativeEnergyDivergence.lean`, and the existing
Hilbert energy-divergence theorem now calls it with its statement unchanged.
The seven-module focused checker passes with warnings rejected; the
transitive audit covers 139 candidate declarations and 1343 declarations
including imported NLS dependencies. No article main theorem is yet marked
verified.


## Fixed-time nonextension milestone

The fixed-time sequence-space obstruction of Theorem 4.14(v) is now proved,
with the actual spectral correction and phase agreement still explicit
requirements. The proof constructs two finite endpoint-regular families
converging to the same datum, with a fixed positive mass difference and
relative phase tending to pi at the specified positive time. It does not
infer a fixed-time result from the earlier compact-time obstruction.
See [the detailed theorem map](FIXED_TIME_NONEXTENSION.md).

All ten selected modules pass with `-DwarningAsError=true`; the transitive
axiom audit covers 191 selected-module declarations and 1489 declarations
including imported NLS dependencies. The earlier `-E warning` option was
replaced because it did not enforce the intended warning policy. No
main theorem for the actual equation is yet marked verified.


## Frequency-moment contour milestone

`NLS/KdV/FrequencyMoments.lean` now defines the literal source moments and
proves Banach analyticity on fixed-contour neighborhoods, odd-moment
cancellation and the analytic-removal criterion for positive moments.
`FrequencyContourDecomposition.lean` proves the cubic and fifth-power
single-gap calculations and finite-gap exterior-period decompositions
with the exact source coefficients. It uses the existing finite-hole
Cauchy theorem rather than assuming a deformation identity. See
[FREQUENCY_MOMENTS.md](FREQUENCY_MOMENTS.md) for the theorem-by-theorem map.

These are reusable KdV contour proofs. Actual spectral factors, zeroth
period normalization and physical Hamiltonian-frequency identities remain
unconstructed, as do the sharp estimates and infinite-series convergence
required by the main theorems. All twelve selected modules pass strict
checks; the transitive audit covers 218 selected-module declarations and
1593 declarations including imported NLS dependencies. Main-theorem
completion remains unset.
