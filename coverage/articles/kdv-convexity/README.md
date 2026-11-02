# KdV Hamiltonian convexity

**Theorems 1.1–1.3 are not yet verified.** The analytic summation and
Hilbert-to-weighted-action inclusion needed for the global extension are
proved, with the physical contour moments and their spectral estimates
retained as explicit missing inputs. The physical smooth KdV energy
coefficients, the actual scalar Hill solution bridge and its all-order real-axis trace estimates are also
proved. The actual discriminant is now jointly entire in energy and continuous
potential. A free-normalized primitive is now constructed on an explicit
joint open source-continuation domain. One cutoff and one complex potential
neighborhood now cover every high squared-frequency contour, and their
actual cubic moments form analytic families there. The high energy regions now
have actual two-root Hill pairs with exact analytic multiplicities and parity
trace levels, and analytic energy midpoints and squared gaps. For real continuous
potentials all actual unit-modulus Floquet energies are now proved real; the
primitive covers both complete nonreal energy half-planes, and the high pairs
are ordered. The actual half-plane sheets and reflected primitive are now
identified from the free normalization, giving reality of the actual high
cubic moments. Uniform high-disc approximation now fixes the shifted
primitive strip and its indexed limits at every actual high branch point,
including double roots. Joint analytic endpoint charts now agree with the
actual shifted primitive square and preserve physical multiplicities.
One bounded analytic square now covers a full energy disc containing
each complete high complex gap, on a common potential neighborhood.
The endpoint-deflated quotient is now analytic and nonvanishing, with
norm at most 4/(n*pi*r)^2. This gives the gap-length bound for the actual
primitive wherever admissible, and constructs analytic roots with the
same bound on the full local cut domain. Their physical sign is fixed
locally at any admissible regular anchor; global matching remains open.
The actual high cubic moments now satisfy the quartic gap bound on a
common complex potential neighborhood, by fixing one sign on a connected
small circle and deforming that circle. This does not require global
matching on every overlap component.
The endpoint-deflated square now also has its quantitative free-model
normalization and an analytic root close to i/(2*n*pi), on each complete
high disc. The exact endpoint-root period now gives the high Arnold-period lower
bound gamma^2/n <= 16*pi*|A_n| and the equivalence A_n=0 iff the
actual gap collapses. Consequently |8*n*pi*R_n| <= C*|A_n|^2 holds on
one common complex continuous-potential neighborhood, with both families
analytic there. Identification of these periods with global H^-1 Birkhoff
actions and analytic descent to action space remain open.
The analytic summation also allows a local finite spectral cutoff.
Analytic squared primitive charts at
both signs of the branch locus are also constructed. The earlier local
concavity/inverse preparation is preserved.
The original Arnold and cubic periods now agree exactly with the shared
L2 energy-circle periods. The actual L2 trace also admits uniform free
approximation on full high discs and source paths in complex L2 neighborhoods;
the corresponding quartic gap, Arnold-period comparison and quadratic
weighted moment bounds are now proved on complex L2 neighborhoods.
The high analytic square construction, complete actual L2 gap containment,
joint indexed branch limits and common high-moment analytic domains are
now proved in the L2 topology as well.
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

### Locally chosen spectral cutoffs

[`TailExtension.lean`](../../../NLS/Articles/KdVConvexity/TailExtension.lean)
proves that a quadratic estimate is needed only outside a finite set of
indices. The literal full series splits into a finite analytic head and an
analytic ell1 tail. `globalTailSeriesDomain` is the union of all such patches;
each patch may choose its own cutoff and bound. It contains the previous
all-index domain. `global_analytic_sum_of_local_tail_bounds` proves that
local tail estimates at every nonnegative action give one complex open
neighborhood of the entire positive ell2 quadrant, including all boundary
points, with absolute convergence there. Termwise reality and nonpositivity
pass to the sum. No vanishing or zero differential at the origin is inferred
from a tail bound alone, since the finite head can contribute.

`global_analytic_contour_sum_from_base_tail_bounds` in `BaseContourSeries`
proves the same conclusion on the exact pulled-back weighted base domain,
retaining the factor `8*n*pi`. Constructing the physical action-dependent
moments and their uniform complex tail estimate remains required.

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

Next mathematical step for Lemma 4.4: continue the constructed free-normalized
primitive from its source-continuation domain to the canonical finite-gap
cut complement, establish its exterior square, and construct its normalized
analytic inversion remainder. Its hyperbolic-cosine trace identity is now
proved on the source-continuation domain described below. The existing generic theorem
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
complement, handle the central square extensions, identify the
continuous-potential discriminant with the shared rough Fourier operator,
or descend moments to the weighted action space. In particular the global
analytic extension around the entire positive ell2 quadrant is still open.

## Free-normalized source continuation and actual contour moments

[`NLS/KdV/ClassicalFreePrimitive.lean`](../../../NLS/KdV/ClassicalFreePrimitive.lean)
computes the actual free Hill trace from IVP uniqueness and a scalar
integrating factor. The free scalar potential corresponds to the nonzero
triangular ZS pair `(-1,0)`, so the zero-ZS-potential formula cannot simply
be substituted. The checked trace is `Delta(0,lambda)=2*cos(sqrt(lambda))`.
It then defines `F0=-i*sqrt(lambda)` on the slit plane and its root
`r0=2*sinh(F0)`, proving `r0^2=Delta(0,lambda)^2-4` and the exact multiplier
identity `exp(F0)=(Delta(0,lambda)+r0)/2`.

[`NLS/KdV/ClassicalHillFlow.lean`](../../../NLS/KdV/ClassicalHillFlow.lean)
is reused unchanged from the `kdv-estimates` branch at `194ec4b`. It
constructs the scalar state flow directly, identifies it with this branch's
constant-upper solutions and discriminant, and proves weak AC uniqueness.
[`NLS/KdV/ClassicalHillSpectrum.lean`](../../../NLS/KdV/ClassicalHillSpectrum.lean)
then transfers the original monodromy determinant criterion for every
energy and multiplier. In particular `Delta^2-4=0` is equivalent to the
existence of a nonzero initial state whose actual scalar solution has
periodic or antiperiodic endpoint data. No simplicity assumption is made.

[`NLS/KdV/ClassicalSourcePrimitive.lean`](../../../NLS/KdV/ClassicalSourcePrimitive.lean)
defines one concrete open joint domain `classicalHillContinuationDomain`:
energy lies in the complex slit plane and the actual radicand remains
nonzero at every potential `s*q`, `0<=s<=1`. A proved equivalent condition
is the absence of actual periodic and antiperiodic scalar solutions along
that entire source segment. This domain is preserved by
taking initial subsegments of the same potential path. On it, the existing
`ParametricSourceLogDomain` library constructs an analytic source increment
`L` for the actual radicand. The actual continued root is

```text
r(lambda,q) = r0(lambda)*exp(L(lambda,q)/2).
```

Its square is proved equal to the actual radicand. A second source logarithm
continues `F0` through the multiplier `(Delta+r)/2`. The resulting
`classicalHillContinuedPrimitive` is jointly analytic and satisfies

```text
F(lambda,0) = -i*sqrt(lambda), exp(F) = (Delta+r)/2,
2*cosh(F) = Delta, 2*sinh(F) = r,
dF = r^(-1)*dDelta
```

for the complete joint Frechet differential, including arbitrary potential
directions. Continuous logarithm uniqueness proves compatibility with any
other branch on a connected overlap having the same sheet and one free
anchor value. Compact spectral sets give a single open complex potential
neighborhood by the existing tube lemma. No primitive or root is supplied
as a mathematical hypothesis in this construction.

[`NLS/KdV/ClassicalContourMoments.lean`](../../../NLS/KdV/ClassicalContourMoments.lean)
proves zero circle periods of the actual spectral derivative `Delta'/r`
inside this domain. It defines the literal cubic moment of `F+i*n*pi`,
with factor `1/pi`, and proves analytic dependence in the continuous
potential norm near every admissible fixed circle. All free moments
vanish on discs contained in the energy slit plane, including discs
through a free collapsed gap. The earlier local logarithm construction
now reuses `NormalizedLogChart` rather than duplicating its calculation.

The domain excludes energies at which the free radicand vanishes. The
high-contour coverage proved below supplies normalized primitives near a
whole tail of actual energy contours at every continuous complex potential.
The paper's finitely many central contours and exact gap labels still need
to be matched. Continuation
to the canonical cuts, endpoint values `-i*n*pi`, the rough Hill operator
identification, action descent, and uniform action bounds remain open.
The constructed contour moments have not been identified with the physical
action-indexed `R_n` on the paper's full weighted action neighborhood.

## Uniform high-contour coverage from the existing complex spectrum

[`NLS/ZakharovShabat/ContinuousPotentialL2Bound.lean`](../../../NLS/ZakharovShabat/ContinuousPotentialL2Bound.lean)
upgrades the established physical class map to a bounded complex-linear
map. It proves `norm(class(phi)) <= 2*norm(phi)` for the curve sup norm,
retaining the actual component-sum physical L2 norm. This allows the
existing spectral neighborhoods to be pulled back in the continuous
potential norm.

[`NLS/KdV/ClassicalSpectralEmbedding.lean`](../../../NLS/KdV/ClassicalSpectralEmbedding.lean)
defines the exact period-one Fourier realization of `(-1,-q)` through
`sourcePhysicalL2Equiv`. The existing classical/L2/canonical trace
comparison identifies its canonical discriminant with the actual scalar
Hill trace. The coefficient realization is now proved complex analytic.
It proves that `Delta(z^2,q)^2-4=0` if and only if `z` belongs
to the already constructed periodic complex ZS spectrum. The generic
complex spectral theorem is used; the pair `(-1,-q)` is not assumed to
satisfy the NLS real-type condition.

[`NLS/KdV/ClassicalContourCoverage.lean`](../../../NLS/KdV/ClassicalContourCoverage.lean)
pulls the existing `PeriodicCountingData` neighborhoods back to continuous
potentials. A finite subcover of a compact potential set gives one cutoff
and one common open neighborhood, with the full counting data valid at
every larger cutoff. Applying this to the entire segment `s*q`,
`0<=s<=1`, proves `exists_classicalHill_high_contour_neighborhood`:

```text
for each q, there exist N>0 and complex open V containing q such that
for every a in V, every n>N and every z on C(n*pi,pi/4),
(z^2,a) belongs to classicalHillContinuationDomain.
```

Thus contour avoidance along the whole source path is a proved conclusion
for every tail index on one potential neighborhood. The squared closed
frequency discs are also proved to lie in the energy slit plane.

[`NLS/KdV/ClassicalHighContourMoments.lean`](../../../NLS/KdV/ClassicalHighContourMoments.lean)
defines the actual energy contour as the image of that counterclockwise
frequency circle under `lambda=z^2`. Its moment has the exact formula

```text
(1/pi)*integral C(n*pi,pi/4) (F(z^2,q)+i*n*pi)^3*(2*z) dz.
```

`classicalHillHighContourMoment_eq_curveIntegral` proves equality with the
holomorphic one-form integral on the actual mapped energy path, reusing
the existing path-pullback theorem. `exists_analytic_classicalHillHighContourMoments`
proves analyticity for all `n>N` on the same complex open potential
neighborhood. Every free high-contour moment is proved zero by analytic
extension through its enclosed free collapsed point.

These results do not identify the source's exact gap labels or transfer
the moments to weighted action coordinates. The full physical Hill
operator on rough distributions, the central contours and endpoint
matching, and locally uniform quadratic bounds in the actions remain
essential inputs. In particular no global positive-ell2 Hamiltonian
extension is asserted by these contour-coverage results.

## Actual high energy pairs and analytic midpoint/gap data

The spectral embedding additionally proves that the natural analytic order
of `Delta(z^2,q)^2-4` is exactly the existing periodic spectral algebraic
multiplicity. At every nonzero frequency, the analytic-order composition
theorem transfers that order unchanged to the energy coordinate. The
high-disc geometry proves strictly positive real part and injectivity of
squaring on each closed high-frequency disc; no ramified zero-energy
argument is used for this transfer.

[`NLS/KdV/ClassicalHighGapPairs.lean`](../../../NLS/KdV/ClassicalHighGapPairs.lean)
defines the high energy region as the image of the open quarter-pi
frequency disc under squaring. `exists_classicalHillHighGapPair_of_counting`
uses the existing two-root spectral count to construct an actual pair
`l,r` of Hill radicand zeros there. The pair exhausts the zero set in that
energy region, and its multiset counts equal the actual analytic orders.
Thus two distinct simple zeros and a single double zero are both included.
Its midpoint and squared gap make the pair unique up to exchange.

Both endpoints have the exact trace level dictated by the high index:

```text
Delta(l,q) = Delta(r,q) = 2 when n is even, and -2 when n is odd.
```

This is derived from the actual periodic root-space parity and canonical
trace-level theorem. It holds for complex potentials, without imposing
the NLS real-type condition. It fixes the trace sign; the global primitive
limits `F -> -i*n*pi` at these high endpoints are now proved below from
both nonreal energy half-planes. The joint endpoint squared-primitive charts are now matched below.
The whole high-gap square construction is now proved below. Matching the
complete canonical cuts and central gaps remains required.

The energy midpoint and squared gap are constructed from the intrinsic
frequency midpoint `m` and squared gap `g` by the exact formulas

```text
energy midpoint = m^2+g/4 = (l+r)/2,
energy squared gap = 4*m^2*g = (l-r)^2.
```

`analyticAt_classicalHillHigh_symmetric` proves their complex analyticity
using the existing finite-rank contour trace invariants and the actual
analytic potential embedding. It does not select analytic individual roots.

[`NLS/KdV/ClassicalHighGapFamilies.lean`](../../../NLS/KdV/ClassicalHighGapFamilies.lean)
proves `exists_analytic_classicalHillHighGapFamilies`: at every continuous
complex potential, one positive cutoff and one complex open neighborhood
support every sufficiently high actual energy pair, its analytic symmetric
data, and the previously constructed analytic cubic contour moments.
The cutoff and neighborhood are chosen before all tail indices and before
all potentials in that neighborhood. These are scalar analytic functions
on a common domain, not yet a Banach-valued sequence estimate.

The high unordered pairs have not yet been integrated with a complete
globally ordered Hill spectrum and its central labels. Their comparison
with the rough Fourier Hill operator, global primitive normalization,
weighted action descent, and the required
uniform quadratic action estimates remain open.

## Actual spectral reality and global nonreal primitive coverage

[`ClassicalSolutionInjectivity.lean`](../../../NLS/ZakharovShabat/ClassicalSolutionInjectivity.lean)
uses the actual determinant-one fundamental matrix to prove injectivity of
state propagation at every point of the closed unit interval.
[`ClassicalHillGreen.lean`](../../../NLS/KdV/ClassicalHillGreen.lean)
transfers this to the scalar Hill flow. Every nonzero initial state has
strictly positive physical position mass `integral_0^1 |F|^2`. Differentiation
and the fundamental theorem of calculus prove the actual imaginary Green
identity

```
-lambda.im * integral_0^1 |F|^2 = Im(conj(F(1))*F'(1)) - Im(conj(F(0))*F'(0)).
```

Consequently every unit-modulus Floquet multiplier of a real continuous
potential has real energy, including periodic and antiperiodic solutions.
This uses no NLS real-type assumption for the pair `(-1,-q)`.

[`ClassicalHillReality.lean`](../../../NLS/KdV/ClassicalHillReality.lean)
proves that every branch point at real continuous q is real. Each scaled
potential `s*q`, 0<=s<=1, remains real, so the constructed free-normalized
primitive covers **both entire nonreal energy half-planes**, with analytic
dependence in energy and local joint analytic neighborhoods already supplied
by the source-domain construction. Its exponential is an actual scalar
Floquet multiplier, and its real part is nonzero at nonreal energies.

The actual high pairs can be chosen with real endpoints in increasing order,
including collapsed pairs. Real points of the n-th squared-frequency disc
lie strictly between `(n*pi-pi/4)^2` and `(n*pi+pi/4)^2`; thus pairs at different
high indices cannot cross. `exists_analytic_ordered_classicalHillHighGapFamilies`
combines this with one complex neighborhood and cutoff for all analytic
midpoints, squared gaps and cubic moments, at every real potential in that
neighborhood. The high endpoint limits are now proved below. Complete
central/global matching and the canonical cut construction remain unproved. These reality results concern
continuous potentials; no L2 or H^-1 extension of the Green proof is claimed.

## Physical primitive sheets, reflection and moment reality

[`ClassicalHillConjugation.lean`](../../../NLS/KdV/ClassicalHillConjugation.lean)
proves conjugation of the actual scalar flow by IVP uniqueness, and hence
Schwarz symmetry of the actual discriminant and radicand for real
continuous potentials. The free primitive and root have the exact reflected
signs on the energy slit plane.

[`ClassicalHillPrimitiveSheets.lean`](../../../NLS/KdV/ClassicalHillPrimitiveSheets.lean)
proves the free square-root sign directly. The imaginary Green identity
prevents the real part of the actual continued primitive from vanishing
along any real source path `s*q`. The intermediate value theorem then gives

```
Im(lambda) * Re(F(lambda,q)) > 0,  Im(lambda) != 0.
```

Thus `Re(F)>0` and the actual Floquet multiplier has norm greater than one
in the upper energy half-plane. In the lower half-plane both inequalities
reverse. The real potential may have arbitrary continuous norm; these are
actual sheet identifications, not assumed branch conventions.

[`ClassicalHillPrimitiveReflection.lean`](../../../NLS/KdV/ClassicalHillPrimitiveReflection.lean)
proves conjugation invariance of the entire source-continuation domain at
real continuous q. Connected source paths, the nonvanishing root and its
free anchor give `r(conj(lambda),q)=-conj(r(lambda,q))`. Continuous logarithm
uniqueness anchored at zero potential then proves
`F(conj(lambda),q)=-conj(F(lambda,q))` on that full domain, including
admissible real energies. At those real energies the primitive is purely
imaginary and its actual Floquet multiplier has unit modulus. This does
not assert that a real gap is already filled by a common boundary value.

[`ClassicalHillMomentReality.lean`](../../../NLS/KdV/ClassicalHillMomentReality.lean)
retains the exact shift `F_n=F+i*n*pi` and proves its anti-conjugate
reflection law. The existing real-circle reflection theorem reverses
orientation as well, proving that the literal normalized cubic moments
are real on admissible real-centered energy circles. The same calculation
applies to the actual squared-frequency contours, with the exact Jacobian
`2*z`. One cutoff and one complex open potential neighborhood support all
analytic high moments, real at every real potential in that neighborhood.
The high endpoint limits `F -> -i*n*pi` are now proved below. Nonpositivity,
the central endpoint construction, gap-scale bounds and weighted action
descent remain unproved. No L2 or H^-1 extension
of these primitive results is asserted here.

## High-band and endpoint normalization

[`ClassicalHillBandNormalization.lean`](../../../NLS/KdV/ClassicalHillBandNormalization.lean)
proves that the imaginary primitive at an admissible real energy never
meets an integer multiple of pi: such a value would force its actual
nonvanishing root to vanish. Continuity along `s*q` therefore preserves
both strict inequalities of the free imaginary band. The free energy
square root is also identified with every right-half-plane frequency.

[`ClassicalHillDiscAsymptotics.lean`](../../../NLS/KdV/ClassicalHillDiscAsymptotics.lean)
transfers the established complex ZS exterior trace estimates to the
actual Hill trace. The maximum-modulus principle gives arbitrarily small
uniform errors `|Delta(q,z^2)-2*cos(z)|` throughout **complete high discs**,
including their branch points. A compact-cover argument and source-domain
tube give one complex potential neighborhood and cutoff for every source
path. The constant-upper affine Fourier map is not assumed to send zero
to the zero ZS potential.

[`ClassicalHillHighTracePhase.lean`](../../../NLS/KdV/ClassicalHillHighTracePhase.lean)
uses these errors to prove `Re((-1)^n*Delta)>0` on all complete high discs
and all source paths of nearby complex potentials.
[`ClassicalHillHighPrimitiveStrip.lean`](../../../NLS/KdV/ClassicalHillHighPrimitiveStrip.lean)
then proves the exact strip

```
|Im(F(z^2,q)+i*n*pi)| < pi/2.
```

It applies at every admissible point of every sufficiently high disc,
with the cutoff and complex neighborhood chosen first. The parity trace
half-plane prevents crossing either strip boundary; the free primitive
selects the component. This part is valid for complex perturbations as
well as for real potentials.

[`ClassicalHillHighEndpointNormalization.lean`](../../../NLS/KdV/ClassicalHillHighEndpointNormalization.lean)
proves that the actual high radicand zero has trace `2*(-1)^n` from its
parity half-plane, without assuming a labeled trace value. Along an
admissible approach the root tends to zero by its squared radicand
identity. The shifted multiplier tends to one, and the proved strip
recovers the actual shifted primitive by `log(exp(F_n))=F_n`.
`exists_classicalHill_high_energy_endpoint_normalization` gives one
cutoff and complex open neighborhood such that, at **every real continuous
potential** in it and **every actual high energy radicand zero**,

```
F(mu,q) -> -i*n*pi as mu -> lambda through Im(mu) != 0.
```

Both energy half-planes are included in the same limit. Simple and double
zeros are treated identically. No value of the total source-domain formula
at an excluded branch point is asserted: the theorem constructs the
normalized boundary limit. The joint analytic squared-primitive matching is now proved below.
The whole high-gap squares are now constructed below. Continuous unsquared
endpoint filling, central endpoints, gap-scale estimates and the H^-1/action
identification remain required.

## Actual joint squared-primitive matching at high endpoints

The endpoint normalization is now strengthened to joint approaches in
energy and complex continuous potential. The endpoint need not move
analytically: `tendsto_classicalHillShiftedPrimitive_joint_at_branch` allows
any convergent joint parameter family satisfying the actual continuation
domain and the proved imaginary strip. Its proof retains the physical
root, multiplier and free-normalized logarithm.

[`ClassicalHillSquaredPrimitiveMatching.lean`](../../../NLS/KdV/ClassicalHillSquaredPrimitiveMatching.lean)
uses that limit to remove the earlier small-branch matching hypothesis.
`exists_classicalHill_high_squared_primitive_matching` chooses a cutoff and
complex potential neighborhood before every high index and every actual
branch point. At each such point it constructs a complex open joint patch
and an analytic function K with

```
K(lambda,q) = 0,
squaredCosh(K(mu,a)) = (-1)^n * Delta(a,mu)/2,
K(mu,a) = (F(mu,a)+i*n*pi)^2 on admissible parameters in the high region.
```

Thus the local inverse is identified with the actual squared primitive,
not an arbitrary cosh branch. This includes collapsed gaps and complex
potential perturbations. The equality is on an actual open joint patch
intersected with the constructed admissible high domain, not only along
one selected spectral sequence. The subsequent whole-disc construction
below identifies these germs with one square per entire high gap. A full
canonical unsquared cut complement remains to be constructed.

Normalized squared-primitive charts are unique as joint germs, including
on the branch locus, by the local squared-cosh inverse. Their exact full
joint derivative is `dK = (-1)^n * dDelta`. The energy analytic order of K
is proved equal to that of the actual radicand. In particular, the actual
high-pair multiplicity theorem transfers unchanged: a double collapsed
endpoint gives analytic order two for K. These conclusions impose no
nonzero energy derivative and do not assume simple zeros.

## Uniform analytic squares across complete high gaps

[`ClassicalCoshStripControl.lean`](../../../NLS/KdV/ClassicalCoshStripControl.lean)
proves a uniform implication on the canonical strip: for every epsilon>0,
one delta>0 ensures `|cosh(z)-1|<delta` implies `|z|<epsilon` whenever
`|Im(z)|<pi/2`. The proof uses the squared sinh identity and the fixed
logarithm strip, so the threshold applies to every point and every index.

[`ClassicalHillSmallDiscTrace.lean`](../../../NLS/KdV/ClassicalHillSmallDiscTrace.lean)
chooses one positive frequency radius, cutoff and complex potential
neighborhood putting `(-1)^n*Delta/2` in any chosen neighborhood of one
on all complete high discs and every straight source path.
[`ClassicalHillSmallGapCoverage.lean`](../../../NLS/KdV/ClassicalHillSmallGapCoverage.lean)
uses the uniform canonical periodic-product exterior estimate to prove
that all actual high roots lie in arbitrarily small discs about their own
free center. It applies to complex potentials and actual radicand zeros.

[`ClassicalHillWholeGapSquares.lean`](../../../NLS/KdV/ClassicalHillWholeGapSquares.lean)
constructs one inverse-based function K_n per high index, with the radius r,
cutoff N and complex open potential neighborhood V chosen before all
indices, potentials and roots. Writing c=n*pi, its exact domain is

```
E_n = closedBall(c^2, c*r),
K_n analytic on a neighborhood of E_n x V,
|K_n| < 1,
squaredCosh(K_n) = (-1)^n * Delta/2,
K_n = 0 iff Delta^2-4 = 0,
K_n = (F+i*n*pi)^2 wherever the actual source continuation is admissible.
```

The energy-to-frequency inclusion follows from the exact factored square
root denominator, using its nonnegative real part. Confining both actual
endpoints to a smaller frequency disc puts them strictly inside the energy
disc. Its convexity then contains the **entire straight complex gap
segment**. `exists_classicalHill_whole_gap_squares` also constructs the
actual two-root pair on the same V and cutoff, including a repeated endpoint.
Thus one joint analytic function covers both endpoints and the full gap;
no gluing of independently chosen endpoint branches is assumed.

The bound one is uniform throughout the entire tail. The endpoint factors
and resulting gap-length bounds are now proved as follows. This
construction concerns continuous complex potentials.

### Endpoint deflation, gap scale and analytic cut roots

[`TwoZeroDeflation.lean`](../../../NLS/ComplexAnalysis/TwoZeroDeflation.lean)
constructs the filled quotient Q=dslope(dslope(K,l),u). Exact orders give
Q nonzero, including at a collapsed pair, without analytic individual
endpoint labels. Its maximum-modulus estimate is local to the closed
disc, so no entire extension of Q is assumed.

[`ClassicalHillGapQuotients.lean`](../../../NLS/KdV/ClassicalHillGapQuotients.lean)
applies this to the actual Hill square on one common complex neighborhood:

```
K_n(z) = (z-l_n)*(z-u_n)*Q_n(z),
|Q_n(z)| <= 4/(n*pi*r)^2 on the complete energy disc,
Q_n(z) != 0 on its interior.
```

Both actual endpoints lie within radius n*pi*r/8. On the closed ball
centered at their midpoint with radius gamma=|l_n-u_n|,
[`ClassicalHillGapScaleBounds.lean`](../../../NLS/KdV/ClassicalHillGapScaleBounds.lean)
therefore proves |K_n|<=9*gamma^2/(n*pi*r)^2, and
|F+i*n*pi|<=C*gamma/n wherever source continuation is admissible,
with C=3/(pi*r) chosen before the whole tail.

[`AnalyticDiscSquareRoot.lean`](../../../NLS/ComplexAnalysis/AnalyticDiscSquareRoot.lean)
lifts a nonzero analytic function through the exponential on a disc and
uses local square-root uniqueness to prove analyticity.
[`AnalyticTwoZeroRoot.lean`](../../../NLS/ComplexAnalysis/AnalyticTwoZeroRoot.lean)
combines that unit root with the library's normalized endpoint root.
[`ClassicalHillGapCutRoots.lean`](../../../NLS/KdV/ClassicalHillGapCutRoots.lean)
thus constructs B_n analytic on the entire open energy disc minus the
straight gap, with B_n^2=K_n and |B_n|<=C*gamma/n on the gap-sized part.
At any admissible regular anchor one of its two signs agrees as a germ
with the actual shifted primitive. The same sign on all overlap
components remains unproved. The moment deformation and cubic bound are
now obtained by the circle normalization below. Central gaps, the
H^-1/action extension, nonpositivity and physical Hamiltonian identification
remain open.

### Actual high-contour deformation and the quartic gap bound

[`ClassicalHillAnnulusCoverage.lean`](../../../NLS/KdV/ClassicalHillAnnulusCoverage.lean)
confines all high roots uniformly along the compact straight source
segments of nearby complex potentials. The whole high annulus outside
any prescribed positive inner frequency radius belongs to the actual
source-continuation domain.
[`ClassicalHillMomentRadius.lean`](../../../NLS/KdV/ClassicalHillMomentRadius.lean)
then shrinks the original quarter-pi frequency contour without changing
the literal moment, including the exact energy Jacobian 2*z.

[`SquaredCircleHomotopy.lean`](../../../NLS/ComplexAnalysis/SquaredCircleHomotopy.lean)
deforms the squared frequency circle to the energy circle with center
c^2 and radius 2*c*rho. Its compact image stays between radii c*rho and
3*c*rho. The exact pullback integral, rather than a relabeling of the
frequency contour as an energy circle, is proved.
[`ClassicalHillMomentCutRoot.lean`](../../../NLS/KdV/ClassicalHillMomentCutRoot.lean)
fixes one sign on the connected frequency circle of radius r/4. It proves
the original high moment equals k^3 times the cut-root cubic moment on
the energy circle of radius n*pi*r/2, with k=1 or -1.

[`AnalyticCutContour.lean`](../../../NLS/ComplexAnalysis/AnalyticCutContour.lean)
supplies deformation between nested circles enclosing the same cut.
[`ClassicalHillCubicGapBounds.lean`](../../../NLS/KdV/ClassicalHillCubicGapBounds.lean)
uses it to shrink to the circle of radius gamma=|l-u| about the gap
midpoint. The primitive bound contributes gamma^3/n^3 and the circle
radius contributes gamma. If the gap collapses, the constructed root
extends analytically through it and the cubic moment vanishes. Thus

```
|classicalHillHighContourMoment n a| <= C*|l_n-u_n|^4/n^3,
|8*n*pi*classicalHillHighContourMoment n a| <= C'*(|l_n-u_n|^2/n)^2.
```

The constants, cutoff and complex open potential neighborhood are chosen
before all high indices and nearby complex potentials. Analyticity of
the literal moment and its weighted gap estimate hold on the same
neighborhood. The potential space is still C([0,1],C); identifying actual
global Birkhoff actions and descending analytically to the weighted action
space remain essential for Theorem 1.1. The Arnold-period version of
gamma^2/n<=C*|A_n| is now proved below in the continuous topology.

### Free-model normalization of the endpoint quotient

[`AnalyticLocalLipschitz.lean`](../../../NLS/ComplexAnalysis/AnalyticLocalLipschitz.lean)
supplies a two-point Lipschitz bound for the squared-cosh inverse.
The whole-disc square construction now permits any prescribed positive
norm bound. This allows the same inverse chart to compare the actual
square with the exact free model

```
K_free(lambda)=-(sqrt(lambda)-n*pi)^2.
```

[`ClassicalHillFreeSquareComparison.lean`](../../../NLS/KdV/ClassicalHillFreeSquareComparison.lean)
fixes r>0 before the error tolerance. On the full energy discs, the
actual square is arbitrarily close, with error epsilon*r^2, both to
K_free and to the polynomial

```
K_quad(lambda)=-(lambda-(n*pi)^2)^2/(4*(n*pi)^2).
```

The explicit free-model error is at most 5*r^3/(4*n*pi).
The local two-root comparison in
[`TwoZeroDeflation.lean`](../../../NLS/ComplexAnalysis/TwoZeroDeflation.lean)
requires analyticity near the closed disc; no entire quotient is assumed.
[`ClassicalHillGapQuotientAsymptotics.lean`](../../../NLS/KdV/ClassicalHillGapQuotientAsymptotics.lean)
combines it with actual endpoint confinement and proves

```
|4*(n*pi)^2*Q_n+1| <= epsilon,
H_n^2=Q_n,
|H_n-i/(2*n*pi)| <= epsilon/(2*n*pi).
```

Here Q_n is the actual filled endpoint quotient of K_n. The first bound
holds for 0<epsilon<=1; the analytic unit root H_n is constructed for
0<epsilon<1. Both estimates hold on the complete closed disc, including
the actual endpoints and collapsed gaps.
[`NormalizedSquareRootBounds.lean`](../../../NLS/ComplexAnalysis/NormalizedSquareRootBounds.lean)
uses a prescribed normalized root and proves the quantitative estimate
|sqrt(z)-1|<=|z-1|.

The radius is chosen before epsilon; the cutoff and complex potential
neighborhood may depend on epsilon. No single neighborhood for all
tolerances is asserted. The roots H_n are analytic in energy, with a
common estimate for all nearby complex potentials; joint potential
analyticity of this endpoint-deflated root is not yet asserted. The
exact endpoint-root period and comparison with the original Arnold period
are now proved below. Global Birkhoff action identification remains open.

### Agreement with the shared physical L2 primitive and Arnold periods

The dependency closure of the shared L2 primitive and contour moments
is imported exactly from `articles/kdv-estimates`, now pinned to commit
`80ac538`: 37 modules, including the actual Hill operator, monodromy trace,
characteristic equivalence, L2 spectral reality and source continuation.
Every existing import at the boundary was identical to that commit.
[`shared-imports.json`](shared-imports.json) records the exact files and
hashes; all are rechecked in this branch's private build.

[`TracePrimitiveFunctoriality.lean`](../../../NLS/ComplexAnalysis/TracePrimitiveFunctoriality.lean)
proves that a bounded complex linear source map preserving the actual
trace and free normalization preserves the continuation domain, root
and primitive. Connected source-path uniqueness removes both square-root
sign and additive logarithm-period ambiguities.
[`ClassicalL2PrimitiveAgreement.lean`](../../../NLS/KdV/ClassicalL2PrimitiveAgreement.lean)
applies this to the actual Fourier realization of a continuous circle
potential. The classical interval and L2 constructions have identical
admissible domains and exactly equal roots and primitives there.

For a period-one continuous potential and n>=max(1,8*norm(q)), the shared
level-zero L2 moment equals the literal classical primitive action on
the energy circle with center pi^2*n^2 and radius n. The same identity
holds with the exact indexed shift F+i*n*pi. The shared L2 integration by
parts theorem supplies the Arnold integrand lambda*Delta_prime/root
with factor 1/pi. These are checked contour identities and local L2
analyticity; they do not yet identify the global H^-1 Birkhoff action
coordinates. The quantitative comparison
is now proved directly in the L2 topology below.

## Actual Arnold periods and quadratic moment control

`QuadraticRootContourPeriod.lean` computes the counterclockwise endpoint-root
period exactly, for complex as well as real distinct endpoints:
integral endpointRoot(l,u) = (pi*i/4)*(l-u)^2 on the circle centered at
(l+u)/2 with radius |l-u|. The proof differentiates
(lambda-midpoint)*endpointRoot and uses the normalized inverse-root period.

`ClassicalHillHighContourActions.lean` defines A_n as the literal period
-(1/pi)*integral (F(z^2,a)+i*n*pi)*2*z dz on the original frequency circle
centered at n*pi with radius pi/4. Integration by parts identifies it with
the Arnold integrand (1/pi)*integral z^2*Delta_prime(z^2)/root(z^2)*2*z dz,
with no extra factor i. It proves analyticity of the entire high family on
one complex potential neighborhood and invariance under the checked
frequency-radius changes.

`ClassicalHillActionGapBounds.lean` compares the local cut-root action
with (l-u)^2/(8*c), where c=n*pi. A unit-root error epsilon/(2*c)
gives action error at most 3*epsilon*|l-u|^2/(2*c); for epsilon<=1/32 this
yields |l-u|^2/(16*c)<=|A|. A nested-circle deformation transfers the
estimate to the enclosing energy circle.

`ClassicalHillArnoldActionComparison.lean` applies these estimates to the
actual high Hill pairs and their constructed source-normalized periods.
For every continuous complex potential q, one positive cutoff N and one
complex open neighborhood V of q precede all n>=N and all a in V:

- The actual high gap satisfies |l-u|^2/n <= 16*pi*|A_n(a)|.
- A_n(a)=0 exactly when the actual pair collapses, l=u.
- Both R_n and A_n are analytic on the same V, and
  |8*n*pi*R_n(a)| <= C*|A_n(a)|^2 for one C>0.

The argument includes collapsed gaps, does not assume analytic individual
endpoint labels, and needs only equality up to a sign on a connected
contour. It does not establish real action positivity. The potential
topology is the complex sup norm on C([0,1],C). Uniform L2/H^-1 estimates,
global Birkhoff action identification, and analytic descent to the weighted
action neighborhood are still required before applying the global ell2
summation theorem to the physical Hamiltonian.

## Exact agreement with the L2 energy-circle periods

The shared `TracePrimitiveMoments.lean` and `HillL2ContourDeformation.lean`
are imported unchanged in the pinned `80ac538` snapshot. They supply all-level Arnold formulas
and invariance on the actual source annuli. The original 36-source closure and the additionally reused generic
phase barrier now match the pinned `80ac538` snapshot byte for byte.

`HillL2CubicContourMoments.lean` defines the actual cubic period
(1/pi)*integral (F(lambda,q)+i*n*pi)^3 on the energy circle centered at
pi^2*n^2 with radius n. It is analytic in the ambient complex L2 coefficient
space near each checked high-index input, vanishes at zero, and is invariant
under the checked annular radius changes.

`ClassicalL2ContourAgreement.lean` proves that the original frequency
contours defining both the Arnold action and cubic moment equal these L2
energy-circle periods. The intermediate frequency radius is 1/(4*pi),
and its squared contour deforms to the energy circle of radius n/2.
The deformation stays in the actual source annulus with energy distances
between n/4 and 3*n/4. The bound 16*|q|_L2<n ensures coverage, and the
exact differential 2*z*dz and indexed shift F+i*n*pi are retained.

For each complex continuous circle potential Q, one complex open
neighborhood U of Q and one positive cutoff precede every period-one A
in U and every high index. Both contour identities hold there. Consequently
the actual L2 energy-circle periods satisfy the previously proved gap
comparison, exact collapsed-gap zero locus, and quadratic bound

```
|8*n*pi*hillL2HighCubicContourMoment n q|
  <= C*|hillL2HighContourMoment n 0 q|^2.
```

This earlier comparison used the continuous sup norm. The same bound
for the actual periods is now proved directly on complex L2 neighborhoods
below, together with their common analytic domain. H^-1 extension,
canonical global labels, Birkhoff action identification and analytic
weighted-action descent remain open; the global ell2 Hamiltonian
extension is not yet asserted.

## Uniform high-disc trace control in the L2 topology

`HillL2DiscAsymptotics.lean` realizes the actual constant-upper L2 system
inside the canonical ZS trace, using physical interval restriction, the
source Fourier isometry and the existing period-one coefficient map.
This affine realization is continuous and complex analytic; its canonical
discriminant equals the actual Hill L2 discriminant at lambda=z^2 exactly.
It does not need to send the zero potential to the zero ZS pair.

For every q in the full complex L2 coefficient space, every 0<r<=pi/4,
and every epsilon>0, one positive cutoff N and one complex L2-open V
containing q precede all a in V, all integers |n|>=N, and all z in the
complete closed frequency disc of radius r about n*pi:

```
|hillL2Discriminant a (z^2)-2*cos(z)| <= epsilon.
```

The same theorem is proved uniformly near compact L2 sets and along all
straight source paths s*a, 0<=s<=1, on one neighborhood and cutoff. No
continuity or parity hypothesis on q is needed for these trace estimates.
The proof transfers the established exterior ZS estimate and applies the
maximum-modulus principle. This now supplies the full L2 gap-square
construction described below.
Uniform L2 endpoint-deflated unit-root, action-gap and quadratic moment
estimates are now proved below. The H^-1 extension remains open.

## Actual whole-gap squares and moment domains in L2

`HillL2TraceControl.lean` fixes the parity half-plane of the actual trace
on entire high frequency discs, including every straight source path.
`HillL2PrimitiveStrip.lean` uses the shared logarithmic phase barrier to
prove |Im(F+i*n*pi)|<pi/2 on all admissible high-disc points, with one
complex L2 neighborhood and one cutoff before the spectral index.

`HillL2WholeGapSquares.lean` constructs, for each B>0, one radius
0<r<=pi/4, a cutoff N, and a complex L2-open V around the input potential.
For every n>=N there is a function K_n jointly analytic near the full
closed energy disc centered at (n*pi)^2 with radius n*pi*r, times V.
It satisfies |K_n|<B, squaredCosh(K_n)=(-1)^n*Delta/2, and
K_n=0 exactly at the actual radicand zeros. At every source-admissible
point it equals the square of the actual shifted primitive F+i*n*pi.
Its energy multiplicities equal the actual radicand multiplicities.
The actual F tends jointly to -i*n*pi at every branch point in these
discs, through admissible nearby energies and L2 potentials. No simple
zero or continuous potential representative is assumed.

`HillL2HighGapPairs.lean` transfers actual high roots and multiplicities
from the checked first-order realization, including double endpoints.
The pair is unique up to exchange, has the exact parity trace level,
and its energy midpoint and squared gap are analytic L2 functions.
`HillL2SmallGapCoverage.lean` confines all high roots inside arbitrarily
small prescribed frequency discs uniformly in a complex L2 neighborhood.
`HillL2GapSquareFamilies.lean` combines these with the analytic squares:
the full straight segment joining each actual complex pair lies strictly
inside its square disc, including when the pair collapses. For real
period-one L2 potentials, the actual weak Hill operator reality theorem
proves that both endpoints are real; they can therefore be ordered.
This does not yet identify them with the shared intrinsic global labels.

`HillL2AnnulusCoverage.lean` proves actual source coverage on complete
high frequency annuli and on energy shells rho*n<=|lambda-(n*pi)^2|<=n
for every fixed 0<rho<=1. `HillL2HighMomentFamilies.lean` then proves
that all actual polynomial primitive moments and the shifted cubic
moment are analytic on one common complex L2 neighborhood, before all
high indices and all polynomial levels. These complex constructions
require neither reality nor even Fourier support.

`Coeff 2` here is the library's period-two Fourier realization. Physical
period-one inputs form its even-supported subspace. The complex trace
constructions work on the entire ambient space; the real ordered-pair
assertion includes the even-support and reality hypotheses explicitly.

The squared primitive is filled across the whole energy disc; the
unsquared source primitive is still compared only on its checked source
domain. The quantitative uniform L2 estimates are now proved below.
Full canonical unsquared continuation, H^-1 extension, Birkhoff action
identification and weighted-action descent remain open.
The global physical ell2 Hamiltonian extension is not yet proved.

## Quantitative actual L2 periods on common complex neighborhoods

`HillL2GapQuotients.lean` constructs the actual filled endpoint quotient
Q_n, with |Q_n|<=4/(n*pi*r)^2 throughout the full closed energy disc.
It handles collapsed pairs using their exact order two. The actual
endpoints lie inside radius R/32, where R=n*pi*r. Here gamma_n=|l_n-u_n|.
`HillL2GapScaleBounds.lean` gives |K_n|<=9*gamma_n^2/R^2 on the
whole gap-length disc, and |F+i*n*pi|<=C*gamma_n/n wherever admissible.
`HillL2GapCutRoots.lean` constructs the corresponding analytic cut roots,
with the same scale bound and analytic extension through collapsed gaps.

`HillL2MomentRadius.lean` proves uniform energy-radius independence for
every integer power of the shifted actual primitive. The connected
energy-circle comparison in `HillL2MomentCutRoot.lean` uses one fixed
sign on that circle. Its radius R/4 lies within the original
radius-n energy circle. The actual cubic period then shrinks to the
gap-length circle in `HillL2CubicGapBounds.lean`, giving

```
|R_n| <= C*gamma_n^4/n^3,
|8*n*pi*R_n| <= Cprime*(gamma_n^2/n)^2.
```

`HillL2FreeSquareComparison.lean` fixes a radius before the error tolerance
and compares the actual filled square with the exact free square and its
quadratic model. `HillL2GapQuotientAsymptotics.lean` proves
|4*(n*pi)^2*Q_n+1|<=epsilon on each full high disc and constructs an
energy-analytic unit root within epsilon/(2*n*pi) of i/(2*n*pi).
The constants and neighborhoods are uniform over nearby complex L2
potentials and high indices; the neighborhood may depend on epsilon.
Joint potential analyticity of this chosen unit root is not asserted.

`HillL2ArnoldActionComparison.lean` applies the exact oriented endpoint-root
period to the actual level-zero Arnold period A_n. It proves

```
gamma_n^2/n <= 16*pi*|A_n|,
A_n=0 iff the actual high pair collapses,
|8*n*pi*R_n| <= C*|A_n|^2.
```

For every input potential, one C>0, one N>0 and one complex L2-open V
are chosen before every n>=N and every nearby potential in V. Both
actual periods are analytic on this same V. Their definitions use the
energy circle centered at (n*pi)^2 with radius n: A_n=-(1/pi)*integral F
and R_n=(1/pi)*integral(F+i*n*pi)^3. These are the same source-normalized
periods already identified with the original continuous contours.
No continuous representative, reality, even Fourier support, analytic
individual labels or globally fixed cut-root sign is assumed.

This proves the uniform quantitative bounds in the L2 topology. H^-1
extension, identification with the global Birkhoff actions, analytic
weighted-action descent, real nonpositivity and physical Hamiltonian
identification remain open. Theorem 1.1 is not yet proved.

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

1. Continue the constructed free-normalized primitive from its explicit
   source-segment domain to the canonical gap complement, handle the
   central contours and indexed endpoint values, and identify the constructed
   contour integrals with the physical gap moments
   R_n=(1/pi)*integral Gamma_n F_n^3, F_n=F+i*n*pi (4.8), using the shared
   Hill discriminant and normalized primitive. The discriminant, local
   squared primitive and free-normalized source continuation above are now
   proved, including actual unordered high energy pairs, their analytic
   symmetric data, real ordering, global off-real primitive coverage and common
   high-contour coverage in the continuous potential norm; complete global
   spectral matching, central endpoint normalization, the full canonical
   unsquared primitive and rough-operator identification remain. The high
   indexed endpoint limits, joint squared-primitive matching and bounded
   analytic squares across entire high gaps are now proved. Endpoint
   deflation and analytic roots on the local cut domain are also proved;
   their physical sign on a connected small circle and the deformation
   of the original high contours are now established for moment estimates.
   Prove analytic descent to
   the weighted actions on a common complex neighborhood (Lemma 4.6(ii)).
2. Extend the proved **complex-neighborhood** bound
   |R_n|=O(gamma_n^4/n^3), gamma_n^2/n<=16*pi*|A_n| and
   |8*n*pi*R_n|<=C*|A_n|^2 from the proved complex L2 neighborhoods
   to H^-1. Identify A_n with the global Birkhoff actions I_n and descend
   the moments analytically to the common weighted action neighborhood.
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

The `kdv-estimates` branch was re-inspected through commit `80ac538`.
Its shared work now includes the actual periodic H2 weak Hill operator,
two-mode reduction, weighted root separation and physical gap tails. The
period-one L2 Hill discriminant is jointly entire after square descent,
agrees with the continuous discriminant, and its zeros are identified with
actual Fourier Hill eigenvectors and the reduced determinant. It now also
proves reality for real L2 Hill potentials by Fourier operator symmetry,
physical characteristic multiplicities and ordered high pairs at a checked
linear cutoff. Its latest work bounds the central spectrum, counts the
central characteristic roots as `2*N-1`, sorts them with multiplicities,
and appends the high pairs to construct global nondecreasing real L2
characteristic labels in the exact tail slots `2*n-1` and `2*n`. Those
labels are now intrinsic and independent of the cutoff, with the lowest
energy characterized intrinsically and canonical weighted gap estimates
proved directly for the actual labeled gaps. The 37-module dependency
closure for the L2 source/moment construction and generic phase barrier is
now reused and validated here. All 36 prior shared sources are unchanged;
the generic logarithm-strip normalization module is newly imported.
The additional intrinsic global-label and canonical
gap-tail modules remain available on that branch and are not imported
in this focused build. Identification of those L2 labels with this
branch's continuous contour construction, continuity of spectral data and
analyticity of symmetric combinations in the required H^-1 topology, and the
Birkhoff construction remain open.
No separate messages were sent to other article chats.

## Validation and worktree

The dedicated ordinary Git worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-kdv-convexity/work/checkouts/diss-lean`,
branch `articles/kdv-convexity`, based at
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Managed creation was rejected
because the canonical sourceRoot is not a registered folder in this chat;
the ordinary-worktree fallback was explicitly authorized.

All 123 modules pass focused Lean 4.33.1/mathlib v4.33.1 checks with
`warningAsError=true`. The positive-index inverse example also passes.
`CheckAxioms.lean` imports all article and new shared KdV modules and audits
their namespaces, including generated declarations, plus explicit shared
helpers and all declarations originating in fourteen additional shared modules:
1427 declarations in total, transitively. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no sorry or project axiom is allowed.
The three public declarations of the shared bounded physical-class
inclusion and both new propagation injectivity theorems are explicitly
included in the same transitive audit. The authored complex-analysis
helpers and reused shared-module declarations are covered as well.
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
products are copied wholesale or modified. `KdV`, `ZakharovShabat` and
`ComplexAnalysis`, `FunctionalAnalysis` and `SequenceSpaces` outputs use
real private directories; reference files in
the shared namespaces are linked only for imports, and an output-file link is removed
before compilation. No full repository validation
is claimed, and the dissertation's existing record is unchanged. Shared
main integration and aggregate imports remain sequential; serialize any
future expensive full validations with `/tmp/diss-lean-article-build.lock`.
