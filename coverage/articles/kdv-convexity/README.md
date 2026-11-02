# KdV Hamiltonian convexity

**Theorems 1.1–1.3 are not yet verified.** The analytic summation and
Hilbert-to-weighted-action inclusion needed for the global extension are
proved, with the physical contour moments and their spectral estimates
retained as explicit missing inputs. The physical smooth KdV energy
coefficients, the actual scalar Hill solution bridge and its all-order real-axis trace estimates are also
proved. The actual discriminant is now jointly entire in energy and continuous
potential. Local primitive charts and analytic squared primitive charts at
both signs of the branch locus are constructed. The earlier local
concavity/inverse preparation is preserved.
This record does not reopen the completed dissertation verification.

## Source and conventions

Kappeler, Maspero, Molnar and Topalov, *On the convexity of the KdV
Hamiltonian*, [arXiv:1502.05857v1](https://arxiv.org/abs/1502.05857v1),
[PDF](https://arxiv.org/pdf/1502.05857v1), 48 pages, downloaded 2026-11-02.
SHA-256: `38ee7f287ee8b790b794865accc8ad51d1083e414b82a73c4a543147a7ec4688`.
The version label gives 20 February 2015; the downloaded PDF prints
March 8, 2022. The bytes are pinned without assuming the dates coincide.
The main statements on PDF/printed pages 3–5 were extracted and visually
checked. Source files remain outside the tracked repository.

The circle is R/Z; Fourier modes are exp(2*pi*i*n*x); potentials have
zero mean. The equation is u_t=-u_xxx+6*u*u_x. Physical energy is the
integral of (u_x)^2/2+u^3. The Gardner bracket has {x_n,y_n}=1.
Coordinates are z_n=(x_n-i*y_n)/sqrt(2), z_-n=conj(z_n), z_0=0;
I_n=z_n*z_-n=(x_n^2+y_n^2)/2 for n>=1. Weights use <n>=1+|n|.
H* subtracts only sum 8*pi^3*n^3*I_n from Hkdv. Its quadratic term is
-3*sum I_n^2, giving derivative -6*Id of its **bilinear** Hilbert gradient.
All boundary points and collapsed actions belong to the positive quadrant.

See `source-inventory.json` for statement domains, quantifiers and pages.

## Main theorem coverage

| Statement | Required content | Status |
| --- | --- | --- |
| Theorem 1.1, pp. 3–4 | A complex open extension around the entire nonnegative ell2 action quadrant; physical energy and frequency identifications; gradient zero and derivative -6*Id at zero; an analytic local inverse; a local Hessian bound <= -norm(J)^2 for every real ell2 direction. | Global analytic summation is proved **from explicit contour inputs**; those physical inputs are not yet constructed. Local analytic consequences are checked conditional lemmas. |
| Theorem 1.2, p. 4 | For each -1/2<=s<=0 and finite p>=2, the same global H^-1 physical KdV Birkhoff map restricts to a real analytic diffeomorphism L_0^(s,p) -> ell_0^(s+1/2,p). | Not verified. Consume the shared Hill/KdV construction; prove the Fourier-Lebesgue restriction, derivative invertibility and surjectivity. |
| Theorem 1.3, p. 5 | Global C0 well-posedness of physical KdV on every such real Fourier-Lebesgue space, with the solution notion referenced by the paper. | Not verified. Sequence phase-flow results alone do not establish this PDE assertion. |

For 1.1 the complex domain must contain every nonnegative ell2 action, not
just zero. One local radius is chosen before all actions and all real Hilbert
directions in the Hessian estimate. For 1.2–1.3 the finite exponent and
regularity are chosen before initial data. Infinity/weak-star endpoints are
not covered by these statements. Global strict concavity is not a main
assertion; the remarks on global semidefinite concavity use other papers.

## Proved global-extension dependencies

All new declarations are under `NLS.Articles.KdVConvexity`.

### Positive-index analytic summation

[`AnalyticSeries.lean`](../../../NLS/Articles/KdVConvexity/AnalyticSeries.lean)
defines `ActionSpace = lp (fun _ : N+ => C) 2`, the nonnegative quadrant,
and a bijection used only to reuse the existing integer-indexed sequence
library. `summable_norm_of_quadratic_bound` proves absolute summability
and sum |T_n(I)| <= C*norm(I)^2 from |T_n(I)| <= C*|I_n|^2.

`analyticOnNhd_seriesTerms` constructs an actual ell1-valued analytic
family from analytic scalar terms and local common quadratic bounds.
The zero fallback in the existing total constructor is excluded at every
point of the domain, and all original coefficients are recovered.
`analyticOnNhd_tsum_of_local_quadratic_bound` then composes with the
continuous linear ell1 summation map. Pointwise convergence is not used as
an unsupported inference of Banach-space analyticity. These results reuse
`Coeff.analytic_realization_of_local_bounds` and its bounded-coordinate
analyticity proof.

### One domain around the whole cone

[`GlobalExtension.lean`](../../../NLS/Articles/KdVConvexity/GlobalExtension.lean)
constructs `globalSeriesDomain` as the union of all admissible complex open
patches. The same literal sum is used on every patch, so overlaps agree.
`exists_global_analytic_sum_of_local_quadratic_bounds` proves that local
analytic/quadratic estimates around **every** cone point give an analytic
sum on one open neighborhood of the entire cone. Absolute convergence,
reality/nonpositivity inherited from the terms, and value zero are retained.
`hasFDerivAt_tsum_zero` additionally proves zero differential at zero from
the quadratic estimate, without assuming a Taylor coefficient identity.
In these generic lemmas the summand is the full weighted term
T_n=8*n*pi*R_n of the paper.

### Actual weighted action inclusion

[`ActionEmbedding.lean`](../../../NLS/Articles/KdVConvexity/ActionEmbedding.lean)
constructs an isometric positive-index reindexing and the bounded linear,
injective inclusion `baseActionInclusion` into the paper's weighted
ell^(-1,1) action space. Raw action coordinates are preserved. Its norm
is proved to be exactly sum |I_n|/(1+n). Square summability of (1+n)^-1
and the existing Holder product establish the inclusion. Positivity and
collapsed actions are preserved. `preimage_base_neighborhood` proves
that the preimage of an open neighborhood of the base positive cone is
an open neighborhood of the entire ell2 positive cone.

The auxiliary two-sided indexing of `BaseActionSpace` enumerates **positive
actions** via a bijection; it is not the two-sided physical Fourier index.
This distinction is explicit in its weight and raw-coordinate theorem.

### Composition with base contour moments

[`BaseContourSeries.lean`](../../../NLS/Articles/KdVConvexity/BaseContourSeries.lean)
retains the exact factor `8*n*pi` in `weightedContourTerm` and the literal
sum in `contourHamiltonian`.
`global_analytic_contour_sum_from_base_moments` proves analyticity on the
exact pulled-back open base domain, which contains the whole ell2 quadrant,
provided the actual R_n are analytic on the base domain and the local common
bounds |8*n*pi*R_n| <= C*|I_n|^2 hold there. These spectral hypotheses are
explicit arguments. The result neither constructs R_n nor asserts that an
arbitrary input family is the KdV Hamiltonian.

## Shared contour-moment and trace proofs

[`NLS/KdV/ActionHamiltonianMoments.lean`](../../../NLS/KdV/ActionHamiltonianMoments.lean)
defines the literal counterclockwise quantities
`primitiveAction F = -(1/pi)*integral F` and
`cubicMoment F = (1/pi)*integral F^3` from (4.8) and the integration by
parts preceding (4.12). It proves:

- `primitiveAction_eq_derivative_period`: equality to the original
  `(1/pi)*integral lambda*F'(lambda)` expression, using the existing
  closed-circle integration-by-parts theorem.
- `cubicMoment_eq_zero_of_analyticOnNhd`: zero moment when the primitive
  extends analytically through the enclosed gap.
- `norm_cubicMoment_le`: the explicit bound `|R| <= 2*r*A^3` from a
  primitive bound A on a radius-r circle.
- `norm_weighted_cubicMoment_le_action_sq`: if `r<=B*gamma`,
  `|F|<=A*gamma/n` on the contour and `gamma^2/n<=K*|I|`, then
  `|8*n*pi*R|<=16*pi*B*A^3*K^2*|I|^2`. The action may be complex.
- `analyticOnNhd_cubicMoment`: joint analyticity of the primitive on a
  neighborhood of one fixed contour throughout an open parameter
  neighborhood gives analytic cubic moments in the Banach parameter norm.

[`NLS/KdV/ActionHamiltonianTrace.lean`](../../../NLS/KdV/ActionHamiltonianTrace.lean)
proves vanishing of all even primitive periods from analyticity of the
square through the disc. `quartic_gap_contribution` then proves exactly
(4.12), including both normalization constants and the sign:

```text
-4/(2*pi*i) integral (F_n-i*n*pi)^4
  = (8*n^3*pi^3)*primitiveAction(F_n) + (8*n*pi)*cubicMoment(F_n).
```

[`NLS/KdV/ActionHamiltonianFiniteGap.lean`](../../../NLS/KdV/ActionHamiltonianFiniteGap.lean)
reuses the existing finite-hole Cauchy theorem.
`finite_gap_contour_identity` proves that the normalized exterior quartic
period is the finite sum of those linear action and nonlinear moment
terms. The analytic hypotheses concern the actual quartic function on a
perforated disc, disjoint/enclosed isolating circles, and the local
normalized primitives and their analytic squares. No contour deformation
identity or Hamiltonian trace conclusion is supplied as an assumption.

These are reusable KdV developments, rather than copies under the article
namespace. They discharge the contour calculations of (4.11)–(4.12) and
the analytic/norm step for the literal cubic integrals. They do **not**
construct the physical Hill primitive, prove its gap bounds or action
descent, or identify the exterior coefficient with physical energy. In
particular, Proposition 4.5 itself still needs the physical high-energy
expansion (4.7) and the physical action identification. The moment estimate
on a shrinking circle also needs an admissible deformation and spectral
bounds when applied to the actual primitive; a real cut estimate alone
has not been substituted for a complex-neighborhood estimate.

## Physical energy coefficients and the actual scalar trace

[`NLS/KdV/RiccatiEnergy.lean`](../../../NLS/KdV/RiccatiEnergy.lean)
reuses the existing NLS Riccati recurrence and the shared differential
polynomial evaluation/integration-by-parts proofs. For the constant-upper
specialization `(a,b)=(-1,-q)`, it calculates the first five physical
Hamiltonians from actual integrals, for every smooth periodic mean-zero
complex q:

```text
H_1 = 0, H_2 = 0, H_3 = 2*H_0(q), H_4 = 0, H_5 = 2*Hkdv(q),
H_0(q) = (1/2)*integral q^2,
Hkdv(q) = integral ((q')^2/2 + q^3).
```

The energy density is explicitly reduced by a total derivative:

```text
q'''' - 5*(q')^2 - 6*q*q'' + 2*q^3
  = (q')^2 + 2*q^3 + D(q''' - 6*q*q').
```

`classicalNLSHamiltonian_const_upper_first_five` assembles the five
identities. `classicalHamiltonian_ofReal` identifies the complexified
energy with the real integral in the article. These are coefficient
calculations on actual smooth potentials, not assumed spectral or
Hamiltonian identities.

[`NLS/KdV/ConstantUpperSpectralBridge.lean`](../../../NLS/KdV/ConstantUpperSpectralBridge.lean)
uses the existing constructed classical ZS solutions for the literal
potential `(-1,-q)`. The first component satisfies
`-y''+q*y=z^2*y` at every interior point of the period. The state map
`(v1,v2) -> (v1,-i*z*v1-i*v2)` has the explicit inverse
`(w1,w2) -> (w1,i*w2-z*w1)` for **all** z, including zero. The code proves
arbitrary prescribed scalar initial position/derivative, both directions
of Floquet boundary transfer, and equality of the normalized scalar trace
with the actual classical ZS discriminant. It adds no competing Fourier
Hill operator, spectral labels or Birkhoff construction. The diagonal
Miura transfer on the mKdV branch is a different specialization and was
inspected before implementing this constant-upper bridge.

[`NLS/KdV/ClassicalTraceAsymptotics.lean`](../../../NLS/KdV/ClassicalTraceAsymptotics.lean)
then applies the already proved all-order NLS discriminant theorem to
these actual scalar solutions. Its first five phase terms are exactly

```text
z - H_0(q)/(4*z^3) - Hkdv(q)/(16*z^5),    lambda = z^2.
```

`exists_constantUpperHillTrace_higher_error_bound` retains the higher
physical Hamiltonians as an explicit finite tail. For each N, a positive
constant is chosen before every real |r|>=1, and the trace error from
twice the cosine of that phase plus its higher tail is at most
`C/(2*|r|)^(N+5)`. Thus the energy coefficient is not extracted from an
error term of the same order. Its N=0 specialization is also checked.
These are real-spectral-axis estimates in the complex scalar norm; an
all-complex exterior Laurent expansion is not claimed here.

Next mathematical step for Lemma 4.4: construct the normalized analytic
inversion remainder of the actual finite-gap Hill primitive and prove
its hyperbolic-cosine trace identity. The existing generic theorem
`ZakharovShabat.exists_nlsHamiltonian_laurent_of_discriminant` in
`NLS/ZakharovShabat/NLSHamiltonianPrimitiveCoefficients.lean` then recovers
the convergent physical coefficients from this classical trace without
a real-type NLS restriction on the pair `(-1,-q)`. That lemma was inspected
in this step. Existence and normalization of the Hill inversion remainder
are still unproved here; no analogous dNLS primitive has been relabelled
as the KdV primitive.

## Joint energy analyticity and actual local primitives

[`NLS/KdV/ClassicalSpectralSymmetry.lean`](../../../NLS/KdV/ClassicalSpectralSymmetry.lean)
proves that the constructed classical discriminant for `(-1,-q)` depends
only on `z^2`. A constant triangular state transformation intertwines the
actual first-order equations at any two spectral parameters with the same
square; IVP uniqueness and the normalized solution columns give the trace
identity. This includes `z=0` and does not assume spectral symmetry.

[`NLS/KdV/ClassicalDiscriminant.lean`](../../../NLS/KdV/ClassicalDiscriminant.lean)
defines `classicalHillDiscriminant q lambda` using a total square-root
representative and proves independence from every choice of square root.
It equals the trace of the actual normalized scalar solutions.
`analyticOnNhd_classicalHillDiscriminant_joint` proves entire joint
analyticity in `(lambda,q)` for the sup-norm Banach space of continuous
complex potentials on `[0,1]`. The source embedding `q -> (-1,-q)` is an
explicit affine continuous-linear map. Even-family Cauchy descent handles
`lambda=0`; no analytic square-root selection is assumed there.

[`NLS/KdV/ClassicalLocalPrimitive.lean`](../../../NLS/KdV/ClassicalLocalPrimitive.lean)
defines the actual radicand `Delta^2-4`. At every point where it is nonzero,
`exists_classicalHill_local_primitive_of_radicand_ne_zero` constructs a
joint analytic root `r` and primitive `F` on an actual complex open
neighborhood. The prescribed-root version permits either sheet and proves:

```text
r^2 = Delta^2-4, exp(F) = (Delta+r)/2,
2*cosh(F) = Delta, 2*sinh(F) = r, dF/dlambda = Delta'/r.
```

The logarithm is constructed locally by normalizing the multiplier to one;
its base value may lie on the principal logarithm's cut. Thus this is an
existence proof from the actual discriminant, rather than a primitive
supplied as an input. It does not yet fix the paper's global normalization.

[`NLS/KdV/ClassicalBranchPrimitive.lean`](../../../NLS/KdV/ClassicalBranchPrimitive.lean)
constructs `squaredCosh`, the entire descent of `cosh(z)` through `z^2`,
proves its derivative at zero is exactly `1/2`, and constructs its analytic
inverse on open neighborhoods of zero and one. At every actual trace point
`Delta=2*sigma`, `sigma^2=1`,
`exists_classicalHill_local_squared_primitive` composes this inverse with
`sigma*Delta/2`. The resulting `K` is jointly analytic, vanishes at the base
point, and equals `F^2` for every sufficiently small branch satisfying
`2*cosh(F)=sigma*Delta`. No simple-zero assumption is imposed, so this local
construction also covers collapsed gaps and complex potential perturbations.

These results provide local spectral charts needed for Lemmas 4.3 and 4.6.
They do not construct a globally normalized Hill primitive on the full gap
complement, continue its square along a whole isolating disc, identify the
continuous-potential discriminant with the shared rough Fourier operator,
or descend moments to the weighted action space. In particular the global
analytic extension around the entire positive ell2 quadrant is still open.

## Earlier checked local consequences

[`LocalConsequences.lean`](../../../NLS/Articles/KdVConvexity/LocalConsequences.lean)
contains five preparation lemmas: scalar gradient scaling; determination
of the full gradient derivative from basis Hessians; local quantitative
concavity with derivative -6*Id; literal strict Jensen concavity on the
nonnegative real cone; and an analytic inverse on actual open neighborhoods.
The inverse lemma is generic and its positive-index ell2 specialization
is checked in `PositiveIndexExample.lean`.

The local concavity adapter still uses integer-indexed `Coeff 2`.
`actionReindex` now provides the forward isometry, but the full derivative,
real-cone and Hessian transport into the article's positive-index interface
remains to be proved. No dNLS Hamiltonian has been relabelled as KdV.

## Remaining essential KdV work

1. Continue and globally normalize the constructed local primitive charts,
   prove their endpoint values and compatibility across the actual gap
   complement, and construct the physical contour moments
   R_n=(1/pi)*integral Gamma_n F_n^3, F_n=F+i*n*pi (4.8), using the shared
   Hill discriminant and normalized primitive. The local discriminant and
   primitive/squared-primitive constructions above are now proved; global
   spectral labels, normalization and rough-operator identification remain.
   Prove analytic descent to
   the weighted actions on a common complex neighborhood (Lemma 4.6(ii)).
2. Prove their **complex-neighborhood** quadratic action bounds, including
   |R_n|=O(gamma_n^4/n^3) and gamma_n^2/n=O(I_n), with local constants
   uniform in n. Real-axis estimates alone cannot supply these hypotheses.
3. Apply the checked analytic reduction to those actual moments. Then prove
   the identification of the exterior quartic coefficient with the physical
   energy from (4.7). The contour decomposition and calculation in
   (4.11)–(4.12) are now proved in the shared KdV library; the physical
   inputs are not. Extend the resulting physical identity as in
   Corollary 4.8 (pp. 30–31), identifying the sum with H*.
4. Identify the gradient with the existing physical frequencies minus
   8*pi^3*n^3 on V intersect V0, and prove the KdV quadratic coefficients
   giving the full -6*Id derivative. Apply the checked local consequences
   after positive-index Hessian/real-cone transport.

The `kdv-estimates` branch was re-inspected through commit `99fa6ee`.
Its shared work now includes the actual periodic H2 weak Hill operator,
two-mode reduction, joint analytic determinant and high-strip two-zero
localization. Its coverage still leaves global spectral labels,
discriminant/actions/Birkhoff data unconstructed. The constant-upper
bridge here reuses classical IVP solutions for the energy calculation;
it does not replace that Fourier/Hill development. Its identification
with the shared operator and rough-distribution domain is still required.
No separate messages were sent to other article chats.

## Validation and worktree

The dedicated ordinary Git worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-kdv-convexity/work/checkouts/diss-lean`,
branch `articles/kdv-convexity`, based at
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Managed creation was rejected
because the canonical sourceRoot is not a registered folder in this chat;
the ordinary-worktree fallback was explicitly authorized.

All fifteen modules pass focused Lean 4.33.1/mathlib v4.33.1 checks with
`warningAsError=true`. The positive-index inverse example also passes.
`CheckAxioms.lean` imports all article and new shared KdV modules and audits
198 constants in their two namespaces, including generated declarations,
transitively. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no sorry or project axiom is allowed.
See `validation.json` for exact file hashes and scope.

Reproduce from this worktree:

```bash
export ELAN_HOME=/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/work/tooling/elan
export PATH="$ELAN_HOME/bin:$PATH"
export NLS_REFERENCE_CHECKOUT=/home/janbernloehr/Documents/Codex/2026-09-11/test-01-5-2-test-02/outputs/dnls
bash scripts/check-kdv-convexity.sh
```

The script uses the canonical compiled imports read-only and writes new
outputs to this worktree's `.lake/article-checks/kdv-convexity/`. This is a
standalone import cache, never a target for `lake build`. No canonical build
products are copied wholesale or modified. No full repository validation
is claimed, and the dissertation's existing record is unchanged. Shared
main integration and aggregate imports remain sequential; serialize any
future expensive full validations with `/tmp/diss-lean-article-build.lock`.
