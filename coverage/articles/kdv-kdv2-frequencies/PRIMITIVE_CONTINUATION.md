# Actual Hill primitive continuation at branch points

This milestone reuses the shared actual continuous-potential Hill
construction and proves the local branch-point dependencies of source
Lemma 2.6 (p. 15) and Lemma 3.1(iii) (pp. 25–26). **The global spectral
primitive and normalized psi functions are not yet constructed, and no
main theorem is marked verified.**

## Reused actual construction

The merge preserves the ancestry of `articles/kdv-convexity` through
`2135a680ab46ba7c476060e9a66db7d5753f8b29`. It imports the published actual
scalar Hill trace, joint energy/potential discriminant, local off-branch
primitive, and analytic squared-primitive chart at both branch signs.
These results are proved from constructed IVP solutions and their energy
symmetry, not supplied as axioms or substituted for an abstract spectral
function. The underlying equation is `-y''+q*y=lambda*y` on `[0,1]`.

The potential space is `NLS.LinearVolterra.Curve ℂ = C([0,1],ℂ)` with its
sup Banach norm. The results are not yet extensions to the source's rough
Fourier-Lebesgue neighborhoods `W_s,p`. No competing Hill construction is
introduced. The only change to the shared source is extraction of
`deriv_squaredCosh_sq_mul` from the proof of
`hasDerivAt_squaredCosh_zero`; that proof now reuses the public lemma.

## Constructed continuation and normalization

All new declarations are in `NLS/KdV/FrequencyPrimitiveContinuation.lean`,
namespace `NLS.KdV`. Set `C(w)=cosh(sqrt(w))`, whose entire analytic descent
and derivative `C'(0)=1/2` are proved by the shared construction.
The new identity `squaredCosh_radicand_factorization` proves

```text
(2*C(K))² - 4 = 16*K*C'(K)².
```

At an actual branch point `p=(lambda,q)` with `Delta(p)=2*sigma` and
`sigma²=1`, `exists_classicalHill_primitive_ratio_continuation` constructs
open joint neighborhoods and analytic functions K,H, with

```text
K(p)=0, H(p)=sigma/2,
C(K)=sigma*Delta/2,
H ≠ 0, K=H²*(Delta²-4).
```

For every small primitive value F satisfying `2*cosh(F)=sigma*Delta`,
and compatible nonzero root sheet `r=2*sigma*sinh(F)`, the same construction
proves `K=F²` and `H=F/r`. The matching is proved simultaneously for either
sign of F, so an analytic choice of F is not assumed. The root identity
`r²=Delta²-4` is separately proved by
`classicalHill_primitive_sheet_sq`. No simplicity or nonzero derivative
of Delta is assumed, so the result also applies at multiple branch points.

`tendsto_classicalHill_primitive_ratio_at_branch` proves the exact source
endpoint limit `F/r -> sigma/2 = 1/Delta(p)` on an arbitrary relative
approach domain, assuming `F -> 0` and the actual trace/sheet identities
there. It uses the constructed analytic continuation, with no application
of l'Hôpital to a possibly multiple spectral zero. For the source's
normalization `sigma=(-1)^k`, the constant is exactly `(-1)^k/2`.
Identification of the global source primitive and canonical sheet with
these identities remains a separate obligation.

## Odd moments and quantitative bounds

`exists_classicalHill_primitive_ratio_bound_chart` shrinks the joint
neighborhood so that `norm(F/r)<=1` wherever the small compatible
primitive/root identities hold. This estimate is uniform in both energy
and continuous potential, including a neighborhood of a collapsed gap.

`exists_classicalHill_positive_moment_bound_chart` proves for every m>=0
and counterclockwise circle of radius R>=0 in that chart:

```text
norm(integral F^(m+1)*psi/r) <= 2*pi*R*A^m*B,
```

provided `norm(F)<=A`, `norm(psi)<=B`, A,B>=0 and the small primitive and
sheet identities hold on the circle. The proof estimates the continued
ratio rather than dividing a uniform bound by a root that may vanish.
Sharp source bounds for F, psi and their mode-index dependence are still
required; this bound alone does not assert those spectral asymptotics.

`exists_classicalHill_odd_moment_chart` proves that every degree `2*l+1`
frequency moment vanishes if the whole closed circle disc stays in the
constructed chart and psi is analytic there. On the contour the integrand
is identified with `K^l * H * psi`, which is analytic across the disc;
Cauchy's theorem proves the vanishing integral. Analyticity of `F²` and
`F*psi/r` is derived from the actual discriminant charts, not taken as
an extra hypothesis. The matching with globally normalized gap primitives
and canonical roots on their isolating discs remains unproved.

## Validation and remaining main-theorem requirements

The focused checker now compiles the five imported classical Hill modules,
the new continuation module, and the previous fifteen selected modules.
It audits all their declarations, including private and generated constants,
and all imported NLS declarations transitively. See `VALIDATION.md` for
the final counts. The shared action/discriminant checker was also rerun
in this worktree after the public-lemma extraction: all fifteen shared
modules, the positive-index example, and its 199-declaration transitive
audit pass. Its separate output directory is private to this worktree.
Both expensive checks use `/tmp/diss-lean-article-build.lock` sequentially;
canonical sources and build products remain read-only.

The imported upstream coverage records remain historical snapshots of
that branch at `2135a68`; the integration validation and current source
hashes for the consumed modules are recorded in this article's
`source.json` and `VALIDATION.md`.

Still required: global gap labels and canonical root/primitive normalization;
normalized entire psi functions and their periods; rough-potential
compatibility; sharp locally uniform moment estimates; identification of
outer periods with Hamiltonian frequencies; action descent and weighted
frequency asymptotics/compact derivatives; and physical Birkhoff/PDE flow
identification. The main-theorem inventory remains open and unchanged.

The final focused audit passes for 334 selected-module declarations and
1918 declarations including all imported NLS dependencies. All 21 selected
modules pass with `autoImplicit=false` and `warningAsError=true`.
