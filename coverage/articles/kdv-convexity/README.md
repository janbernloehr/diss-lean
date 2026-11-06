# KdV Hamiltonian convexity

**Theorems 1.1–1.3 are not yet verified.** The checked analytic reduction
constructs one complex neighborhood of the entire nonnegative weighted
action cone, descends real-action-invariant analytic coordinate families
there, and sums their quadratic tails analytically on the positive-ell2
preimage. All actual canonical periods are now invariant under equality
of the full real discriminant. The direct coordinate-extension theorem
derives the positive-ell2 analytic sum from precise spectral coordinate
inputs; construction of that coordinate realization remains open.

On potential space, the actual unit-period Hill discriminant is jointly
entire in energy and complex H^-1 potentials. Local analytic shifted-Miura
charts give the physical L2 comparison and uniform H^-1 high-energy
estimates. The source-normalized root and primitive cover both full
nonreal half-planes at real inputs, satisfy exact Schwarz reflection, and
have strict physical sheet signs. Actual high cut roots match the source
primitive on complete integration circles and both half-discs, including
collapsed gaps.

On one common complex H^-1 neighborhood, the literal high Arnold and
cubic periods are analytic and satisfy
|R_n|<=C*gamma_n^4/n^3, gamma_n^2/n<=16*pi*|A_n| and
|8*n*pi*R_n|<=C*|A_n|^2. The actual high cubic periods are real and
nonpositive at every real input there. No global Birkhoff action has been
substituted for the proved Arnold period A_n.

Exterior confinement now accounts for every actual H^-1 characteristic
root. Source-path separators give the exact central count 2*N-1 with
analytic multiplicities. The central roots are sorted and joined to the
ordered high pairs in slots 2*n-1 and 2*n. This constructs an exhaustive
nondecreasing real characteristic labeling on one common neighborhood,
and an intrinsic lowest characteristic root. The full labeling is now
independent of cutoff and radius, continuous
in H^-1, and normalized by exact indexed trace parity. Canonical gap
circles with actual zero count two are now constructed at every index.
The actual primitive now glues holomorphically on the entire real-band
domain, with exact source normalization. The all-index real periods are
constructed and real. Joint complex-potential reference extensions and
analytic contour-period germs are now proved below. Their identification
with the nearby canonical real families is proved in the latest milestone. Indexed endpoint limits and
energy-analytic filled squares are proved below.

Physical energy/frequency identification, the -6*Id quadratic coefficient
and the Fourier-Lebesgue assertions in Theorems 1.2–1.3 also remain open.
The earlier verified local concavity and inverse-function consequences
are retained as conditional preparation. This record does not reopen the
completed dissertation verification.

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
identification and action descent remain open. The high indexed branch
limits and uniform quadratic bounds for the actual Arnold periods are
proved in the later H^-1 sections below.
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

## Analytic shifted Miura charts in the H^-1 topology

`PeriodOneMassResolvent.lean` constructs the actual continuous linear
isomorphism d/dx+(m+1):L2->H^-1 in unit-period Fourier coordinates.
Its inverse has norm at most 2. Its inverse-symbol sequence kappa_m
converges to zero in ell2; no convergence to zero of the H^-1-to-L2
operator norm is asserted.

`PeriodOneMiuraQuadratic.lean` constructs the actual convolution product
L2 x L2 -> H^-1. Every raw coefficient is its absolutely convergent sum.
After the massive inverse, its bilinear bound is

```
|inverse_mass(v*w)|_2 <= |kappa_m|_2 * |v|_2 * |w|_2.
```

`SmallQuadraticInverse.lean` proves the needed Banach-space argument:
when C*R<=1/4 and |y|<=R/2, id+B(x,x)=y has a solution in the complete
closed radius-R ball. Its derivative is invertible and it has an
analytic inverse on open neighborhoods. A separate linear-normalization
lemma transfers this chart to a different target Banach space.

`PeriodOneMiuraCharts.lean` proves that for every B>=0 there is M such
that for every m>=M and every complex H^-1 q with |q|<=B, there is an
open neighborhood U of q and an analytic s:U->L2 satisfying

```
s(r)' + (m+1)*s(r) + s(r)^2 = r  for every r in U,
|s(q)|_2 <= 4*B+1.
```

The mass is chosen before all potentials in the bounded ball. In
particular every complex H^-1 potential has such a local analytic lift.
No reality, mean-zero or smoothness hypothesis is needed. The derivative
symbol is 2*pi*i*k, matching the article's unit-period normalization.
The ambient period-two physical Hill model requires its explicit
periodDouble insertion later.

`PeriodOneMiuraRegularity.lean` proves that an L2 lift with an L2 image
belongs to H1. The massive inverse first puts the lift in ell^(4/3),
Young puts its square in ell2, and the derivative graph gives the full
Sobolev derivative. This will permit comparison with the existing
physical H1 Miura/Hill identities.

`PeriodOneMiuraShift.lean` constructs the literal map u -> u'+u² and
proves the exact shift identity. Replacing the shifted lift s by
u=s+(m+1)/2 gives an analytic local lift satisfying

```
Miura(u(r)) = r + (m+1)^2/4.
```

The constant is inserted in the zeroth Fourier mode. L2-image H1
regularity is also proved for this literal Miura map. The scalar Hill
energy must therefore be translated by precisely (m+1)^2/4.

The physical discriminant matching and gluing through these charts are
now proved below. Uniform H^-1 period estimates, global Birkhoff action
identification and analytic weighted-action descent remain open.
The global positive-ell2 Hamiltonian extension is not yet proved.

## The global H^-1 trace and its normalized source sheets

`HillL2ConstantShift.lean` proves the exact identity
Delta(q+c,lambda+c)=Delta(q,lambda) for the actual physical L2 monodromy.
It follows first from equality of the scalar position/derivative state
equations, then by continuous Fourier density.

`HillMiuraL2Discriminant.lean` realizes the original diagonal canonical
NLS trace on every complex L2 Miura input. The shared physical H1 identity
and H1 density prove frequency evenness, and Cauchy-circle even descent
gives joint energy/L2 analyticity, including energy zero. If an L2 input
has an L2 distributional Miura image, the proved H1 regularity identifies
its trace with the actual Hill monodromy. No analytic H1 dependence of
the local lifts is assumed.

`PeriodOneHminusOneDensity.lean` proves density of the coefficient-preserving
unit-period L2 inclusion in the full complex H^-1 space. Continuous
functions on an open H^-1 set are determined by their values on that
range. `HillHminusOneDiscriminant.lean` applies this to the energy-shifted
Miura chart traces: they agree on every open overlap, for all complex
energies, independently of mass and inverse-branch choices. It constructs
one trace, `hillHminusDiscriminant`, jointly entire on C x H^-1 and the
unique continuous extension of the physical unit-period L2 trace:

```
Delta_Hminus(periodOneL2Inclusion(q),lambda)
  = hillL2Discriminant(periodDouble(q),lambda).
```

`HillHminusOneSourcePrimitive.lean` constructs the free-normalized root
and primitive on the explicit open straight-source continuation domain.
The free primitive is -i*sqrt(lambda), and the trace, square-root and
energy-derivative identities have their original constants. Under the
L2 inclusion the continuation domains, roots and primitives agree
exactly with the existing physical L2 construction. No additional sign
or logarithm period is left undetermined.

The physical H1 Miura comparison is reused from 65 exact source modules
pinned in `miura-shared-imports.json`. Its transitive source graph has
2,393 modules. One older baseline Hamiltonian module is aligned with the
shared periodic integration-by-parts import; the existing periodic
Fourier evaluation module is recompiled. Three compatible private source
differences are retained and documented: two original independent proofs
and the additional proved strict free-Hill spacing lemma. The original
37-source manifest remains unchanged. The focused validation is incremental; the latest cumulative scope is
recorded under Validation and worktree below. This is not a full
2,393-module or repository build.

Uniform H^-1 high-disc/source-path trace estimates, full analytic primitive
squares and common high-moment analytic domains are now proved below.
The full quartic-gap and quadratic-Arnold-period bounds are now proved below.
Intrinsic singular-operator characteristic identification, global Birkhoff
actions and analytic weighted-action descent remain open.
Theorem 1.1 and the positive-ell2 physical Hamiltonian extension remain
unverified.

## Uniform H^-1 high families and actual analytic contour periods

`ShiftedSquareRootBounds.lean` proves the principal-root estimate
|sqrt(z²+c)-z|<=|c|/Re(z) for Re(z)>0, and one high cutoff for any fixed
energy shift. `HillFreeEnergyShift.lean` reduces the free cosine error to
one compact disc by parity translation.
`HillHminusOneDiscAsymptotics.lean` transfers the original exterior NLS
estimate through an actual Miura chart at sqrt(z²+c). It gives one complex
H^-1-open V and one N, before all nearby potentials, all positive high
indices and every point of each complete closed frequency disc. Maximum
modulus fills the boundary estimate. Compact-set and straight-source-path
versions retain the same order of quantifiers. Openness uses continuity
only on the actual chart domain; no globally continuous lift is assumed.

`HillHminusOneTraceControl.lean` fixes the parity trace half-plane on full
high discs and the near-one normalized trace on smaller discs.
`HillHminusOnePrimitiveStrip.lean` proves |Im(F+i*n*pi)|<pi/2 at every
admissible point, with the index fixed by the free source anchor.
`HillHminusOneWholeGapSquares.lean` constructs K_n jointly analytic on
full energy discs times one H^-1 neighborhood, arbitrarily small there,
with squaredCosh(K_n)=(-1)^n*Delta/2. Its zeros are exactly the actual
radicand zeros, with identical analytic energy orders. It equals
(F+i*n*pi)^2 wherever the source primitive is admissible. The resulting
indexed limits F -> -i*n*pi hold jointly in energy and H^-1 potential,
including multiple zeros and all source-admissible approach directions.

`HillHminusOneFreeSquareComparison.lean` fixes a radius before the error
tolerance and compares these squares with both the exact free square
and -(lambda-(n*pi)^2)^2/(4*(n*pi)^2), on whole closed energy discs.
The potential neighborhood may depend on the tolerance.

`HillHminusOneSmallGapCoverage.lean` confines every actual high trace root
in any prescribed positive frequency radius. It uses the proved trace
error and the filled-sine quotient bound, rather than assuming spectral
labels. `HillHminusOneAnnulusCoverage.lean` covers complete high frequency
annuli and energy shells rho*n<=|lambda-(n*pi)^2|<=n on one H^-1-open
neighborhood, with no reality, mean-zero or parity hypothesis.

`HillHminusOneHighMoments.lean` defines the literal high periods

```
A_n = -(1/pi)*integral F,
R_n = (1/pi)*integral (F+i*n*pi)^3,
```

on the energy circle centered at (n*pi)^2 with radius n. Every integer
hierarchy level has the original Arnold normalization. The periods
vanish freely and agree exactly with the physical L2 periods under
unit-period inclusion and explicit periodDouble insertion. For every
H^-1 potential, one N and one complex open V support analyticity of all
high polynomial and cubic periods simultaneously.
`HillHminusOneMomentRadius.lean` proves uniform radius independence for
every integer power of the shifted primitive on the same checked energy
shells; the indexed shift contributes no constant Arnold period.

The actual H^-1 two-root cluster construction and uniform quartic-gap /
quadratic-Arnold-period bounds are now proved below. Global Birkhoff action
identification and analytic weighted-action descent remain required before
the checked positive-ell2 summation theorem applies to the physical Hamiltonian.

## Actual H^-1 high pairs and quadratic period bounds

`QuadraticClusterCount.lean` proves that a scalar analytic function within
r²/16 of the model -(lambda-c²)²/(4*c²) on the boundary of the energy disc
has exactly two zeros, with repetition and exact analytic multiplicities.
Its boundary is nonvanishing and both roots lie in the open disc.
`HillHminusOneHighGapPairs.lean` applies this to the actual filled square.
The radius is fixed before the tolerance; one H^-1-open neighborhood and
cutoff support every high index. The pair has the exact multiplicities of
the actual radicand and both trace values equal 2*(-1)^n.
`HillHminusOnePairUniqueness.lean` identifies the unordered pair across
any two local radii. The actual radicand has total zero count two on each
closed disc. No analytic ordering of individual endpoints is assumed.

`HillHminusOneGapQuotients.lean` removes both endpoint factors, including
a double root, and proves an analytic nonzero quotient with uniform bound
4/(n*pi*r)². `HillHminusOneGapScaleBounds.lean` gives the filled square and
source primitive bounds on the full gap-sized disc.
`HillHminusOneGapCutRoots.lean` constructs an analytic root off the entire
straight complex gap, extending through a collapsed gap.
`HillHminusOneMomentCutRoot.lean` fixes one sign on a connected integration
circle and matches the actual source period with the cut-root period.
`HillHminusOneCubicGapBounds.lean` proves, uniformly on one complex H^-1
neighborhood and above one cutoff,

```
|R_n| <= C*|lambda_minus-lambda_plus|^4/n^3.
```

`HillHminusOneGapQuotientAsymptotics.lean` normalizes the filled quotient
against -1/(4*n²*pi²) and prescribes its energy-analytic unit square root
near +i/(2*n*pi). The radius precedes the tolerance, but the neighborhood
may depend on that tolerance. Joint potential analyticity of this chosen
unit root is not asserted.
`HillHminusOneArnoldActionComparison.lean` proves the exact estimates

```
|lambda_minus-lambda_plus|^2/n <= 16*pi*|A_n|,
A_n = 0 iff lambda_minus = lambda_plus,
|8*n*pi*R_n| <= C*|A_n|^2.
```

Both actual periods are analytic on the same common complex H^-1
neighborhood. All estimates include collapsed gaps. They concern the
literal source-normalized contour periods. Identifying A_n with the
same global KdV Birkhoff map's actions, descending R_n analytically to a
common neighborhood of the full weighted nonnegative action cone,
central contours, the full canonical unsquared domain, real nonpositivity
and the physical energy/frequency identities remain required. Theorem 1.1
and all main theorem completion flags remain false.

## Common action-family descent and exact weighted summation

`LocalScalarActionFamilyDescent.lean` chooses one local source neighborhood
and one open action image before the scalar function index. Every analytic
invariant in the family factors there. It retains all zero tail actions.
`RealScalarActionFamilyDescent.lean` derives complex tail sign invariance
and rotation stationarity from real action-fiber invariance, using one
finite nonzero head for the entire family.
`ScalarActionFamilyGluing.lean` glues all components on the same union of
balls with nonnegative centers. Compatibility only on nonnegative actions
suffices, by the inherited holomorphic identity theorem; no interior of the
infinite-dimensional cone is assumed.

`GlobalScalarActionFamilyDescent.lean` constructs one complex neighborhood
of the entire nonnegative action cone from coordinate-space analyticity,
real action invariance and local quadratic tail bounds. Nearby nonnegative
actions have real lifts in each local source chart. That supplies overlap
compatibility. The local finite spectral cutoffs and quadratic estimates
survive on every original ball, so they remain local estimates throughout
the resulting global open domain.
`WeightedScalarActionFamilyDescent.lean` transports this result to the
original weighted action space. In normalized Hilbert coordinates the raw
action is (x_k²+y_k²)/(2*w_k). The raw action is distinguished from its
weighted sequence coordinate, and the estimates retain the raw values.

`CoordinateActionExtension.lean` specializes the construction to the exact
KdV base weight (1+n)^(-1), positive n:PNat, and the factor 8*n*pi. It
constructs analytic moment factors R_n on one weighted neighborhood and
applies the checked literal contour-series summation on its ell2 preimage.
This proves the descent/gluing/summation step from real-invariant analytic
coordinate moments with local raw-action tail bounds. It does not provide
the actual KdV Birkhoff map or identify its actions with the proved Arnold
periods. Those physical identities, real isospectral invariance of the
actual periods and the finite central periods remain essential inputs.
Theorem 1.1 and all main theorem flags remain unverified.

The inherited descent dependency slice consists of 51 unchanged source
modules, pinned and hashed in `action-descent-shared-imports.json` against
the already inherited tree at `9d67a0f`. They are checked in dependency
order in the private cache and included in the combined axiom audit.

## Actual real H^-1 spectra, sheets and contour-period reality

`PeriodOneHminusOneRealDensity.lean` defines distributional reality by
q(-k)=conj(q(k)) in the raw unit-period Fourier convention. Symmetric
finite supports preserve this condition. The corresponding literal L2
potentials converge in H^-1, without any bounded-L2-norm assumption.
`ClosedZeroPersistence.lean` proves that a jointly continuous family of
entire scalar functions inherits a closed zero constraint from dense
parameters whenever the limit slice is nontrivial. Local zero-count
stability includes multiple zeros.

`HillHminusOneReality.lean` proves nonconstancy of the actual discriminant
and radicand at every complex H^-1 potential from their genuine high count
of two. Every analytic energy order is finite. Applying closed-zero
persistence to the existing physical L2 Hill reality theorem proves that
all characteristic zeros at real H^-1 potentials are real, including
central and multiple roots, with no high cutoff and no mean-zero input.
Both entries of every constructed high pair are real. Every nonreal energy
belongs to the actual source domain; its root and primitive are analytic
throughout both nonreal half-planes.

`HillHminusOneReflection.lean` transfers Schwarz symmetry of the physical
trace by real Fourier density. The existing source-reflection theorem
fixes the exact identities R(conj lambda)=-conj R(lambda) and
F(conj lambda)=-conj F(lambda), retaining the original free sheet and
logarithm period. At every admissible real energy, F is purely imaginary
and the actual multiplier exp(F) has norm one.
`HillHminusOneMomentReality.lean` combines this reflection with orientation
reversal of a real-centered circle. Every integer-level Arnold period and
the literal cubic period with factor 1/pi are real on every admissible
such circle. One complex H^-1-open neighborhood and cutoff support the
whole high analytic family with reality at every real potential there.

Four exact sources from `articles/kdv-estimates` at `54ab8cf` are reused:
continuous Fourier conjugation, L2 trace conjugation, generic source-sheet
reflection and L2 primitive reflection. The hashed manifest is
`hminus-real-shared-imports.json`. The already checked private classical
conjugation source is retained at the import boundary; its difference
from the shared branch is recorded, and all four exact imported modules
compile against this boundary and pass the combined axiom audit.

Reality does not assert positivity of Arnold actions or nonpositivity of
cubic periods. The singular operator's intrinsic characteristic identity,
canonical product-root identification, finite central canonical contours,
full H^-1 real-band continuation and global KdV Birkhoff/action matching
remain unproved. The main theorems remain unverified.

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

## Physical H^-1 half-plane signs and common high cuts

`HillHminusOneHalfPlaneSheets.lean` transfers the weak upper sign from
literal real L2 potentials by H^-1 density and joint continuity. No bound
on the approximants' L2 norms is assumed. The maximum modulus principle
and the actual entire trace's nonconstancy make this sign strict.
Exact reflection gives the negative lower sign. The actual normalized
Floquet multiplier has modulus greater than one in the upper half-plane
and less than one in the lower half-plane. These assertions hold at every
real H^-1 input, at all nonreal energies, without a high cutoff or a
mean-zero hypothesis.

`HillHminusOnePhysicalCut.lean` proves that a filled shifted primitive
square is real along a real disc diameter, including points where the
source primitive is undefined. On any enclosing source circle, connected
square-root uniqueness fixes one sign. Separate upper and lower anchors
then match that same signed cut root to the actual primitive throughout
both half-discs. The pure imaginary indexed shift preserves the strict
real-part signs.

`HillHminusOnePhysicalHighCuts.lean` applies this to the actual high H^-1
spectral families. One open complex H^-1 neighborhood and one cutoff are
chosen before every index and every real input in that neighborhood.
The actual real endpoints, filled analytic square, analytic cut root,
exact full-circle matching, strict upper/lower signs and real boundary
square are obtained together. Collapsed gaps retain an analytic root
through the endpoint. No arbitrary sheet sign remains on the integration
circle or either nonreal half-disc.

`SignedSquareBoundary.lean` proves full upper/lower boundary limits from
the filled square and a strict real-part sign. Zero boundary values are
included. `PhysicalCutCubicSign.lean` applies the exact real-cut jump
formula: when the filled square is nonnegative along the entire cut,
the counterclockwise cubic integral equals minus twice the integral of
the cubed nonnegative real square root. Thus its real part is nonpositive
and its imaginary part is zero. A collapsed cut uses bounded removability.
This generic theorem is now applied to all sufficiently high actual
H^-1 gaps below. Finite central cubic signs remain unproved.

The 24 exact shared dependencies are pinned in
`physical-cut-shared-imports.json` against `articles/kdv-estimates` at
`2fef357`. They include the physical L2 half-plane sign proof and its
real spectral-label prerequisites, plus the real-cut jump and bounded
puncture lemmas. Retained import boundaries are byte-identical.
The global KdV Birkhoff map, its Arnold-action identity, real isospectral
invariance of the actual cubic moments and finite central periods remain
required to instantiate the checked common-neighborhood action descent
and global positive-ell2 summation. Theorem 1.1 remains unverified.

## Nonpositive actual H^-1 high cubic periods

`NearImaginarySquare.lean` proves that a complex value within one quarter
of a positive imaginary model has a square with strictly negative real
part. A two-endpoint factorization therefore has nonnegative real part
between its ordered real endpoints.
`HillHminusOneRealGapSquares.lean` applies this to the actual H^-1 unit
root near +i/(2*n*pi), on the common complex neighborhood already proved
for its uniform free approximation. It retains the actual ordered root
pair, analytic filled square and nonvanishing analytic cut root. On the
entire closed real gap the filled square is real and nonnegative.
No nonnegativity of a model action is assumed.

`PhysicalCutCubicGeometry.lean` deforms a free-centered circle to a
nested circle around the actual gap midpoint and applies the proved
boundary-jump theorem there. The gap may be off-center or collapsed.
`HillHminusOneCubicSign.lean` matches the physical cut root on the whole
source circle and uses the exact source-annulus deformation. The original
period R_n=(1/pi)*integral (F+i*n*pi)^3 is real and nonpositive for every
real H^-1 input in one open complex neighborhood and every index above
one common cutoff. There is no undetermined sign or logarithm period.

`exists_analytic_nonpositive_hillHminus_moments_with_action_bounds`
chooses the same complex H^-1 neighborhood for cubic-period and
Arnold-period analyticity, the exact weighted estimate
|8*n*pi*R_n|<=C*|A_n|^2 at complex inputs, and the real cubic sign.
The cutoff and neighborhood precede all indices and inputs. These are
actual potential-space assertions; they do not yet supply the global
Birkhoff coordinates, action identity, finite central moments or their
real isospectral invariance needed to apply action descent.
High Arnold positivity and finite central cubic signs remain open.
Theorem 1.1 and the other main theorem flags remain unverified.

The shared branch was re-inspected at `05e5530`. Its new global L2
filled-gap squares and convergent hierarchy trace gap series are available
for subsequent reuse; no additional shared sources are imported in this
four-module milestone.

## Exhaustive H^-1 roots and global real characteristic labels

`HillHminusOneExteriorRoots.lean` uses the actual Miura-chart identity
with the NLS discriminant at sqrt(lambda+c). A locally uniform exterior
periodic-product ratio excludes every root outside the translated free
frequency neighborhoods and a bounded central region. This covers all
actual characteristic roots, including those outside the previously
constructed high discs. Finite chart covers give a single neighborhood
and constants near compact H^-1 sets and along every complete straight
source path. No bound on L2 approximants is assumed.

`HillCentralRegionGeometry.lean` separates the free-energy lattice with
the existing separator pi^2*N^2-12*N.
`HillHminusOneRootRegions.lean` prescribes the high-disc radius first,
then chooses one complex H^-1 neighborhood and a cutoff. Every larger
cutoff works on that neighborhood. Each source-path root lies strictly
above -N^2 and either below the separator or in an actual high energy
disc strictly above it. The entire separator line and the left half-plane
are zero-free. There are no unaccounted roots between high discs.

`HillHminusOneCentralCounting.lean` combines the proved source separators
with real H^-1 root reality. The diameter circle is zero-free throughout
the source homotopy. Its exact analytic zero count is 2*N-1: one free
simple lowest root and N-1 free double roots. Multiple central roots
retain their full analytic orders.
`HillHminusOneCentralRoots.lean` adapts the existing L2 root-multiset
construction to these actual H^-1 controls and sorts the finite cluster.

`HillHminusOneRealPairs.lean` retains each actual ordered high pair and
proves strict separation between different indices and from the central
cluster. `HillHminusOneGlobalRealLabels.lean` appends the pairs to the
sorted central cluster. The resulting sequence is nondecreasing, every
entry is a genuine H^-1 radicand root, and every radicand root receives a
label. High pairs occupy exactly slots 2*n-1 and 2*n, with their analytic
multiplicities, and the central slots retain the exact root-multiset
counts. One complex neighborhood and cutoff precede all these assertions
for every real input there. No caller supplies the missing central roots.

The same construction proves existence of the intrinsic lowest real
characteristic root, its root identity and minimality among all actual
complex characteristic zeros. Minimality determines its value uniquely.
Cutoff-independent uniqueness, H^-1 continuity, lowest-root simplicity,
central trace parity and canonical gap-circle geometry are now proved
below. The actual primitive now glues holomorphically on the entire real-band
domain, with exact source normalization. The all-index real periods are
constructed and real. Joint complex-potential reference extensions and
analytic contour-period germs are now proved below. Their identification
with the nearby canonical real families is proved in the latest milestone. Indexed endpoint limits and
energy-analytic filled squares are proved below. This is a labeling of the constructed entire
H^-1 characteristic; its singular-operator identification and global
KdV Birkhoff-action interpretation remain open. Theorem 1.1 and all other
main theorem flags remain unverified.

## Intrinsic continuous H^-1 labels and all-gap isolating circles

`HillHminusOneLabelFamilies.lean` retains the proved source control and
actual high pairs, with any prescribed finite minimum cutoff and a
single complex H^-1 neighborhood. `HillHminusOneLabelUniqueness.lean`
proves finite occurrence sets and their exact analytic multiplicities.
Ordered high pairs agree at different radii. The shared finite-exception
uniqueness theorem then identifies the entire enumeration, including
repeated central values, independently of cutoff and radius.
`HillHminusOneCanonicalRealLabels.lean` defines the intrinsic labels.

`HillHminusOneCumulativeCounts.lean` identifies diameter-disc zero counts
with finite ordered counts. `HillHminusOneLabelContinuity.lean` uses their
local stability to prove H^-1 continuity of every canonical label and
the lowest root, including closed gaps and repeated central roots.
No simplicity or bounded L2-approximation norm is assumed.
`HillHminusOneCanonicalFreeLabels.lean` identifies the actual free
characteristic with the existing free L2 enumeration and obtains
lambda_j(0)=pi^2*floor((j+1)/2)^2.

`HillHminusOneTraceParity.lean` follows the actual characteristic trace
along the real source path. Continuity and Delta^2=4 fix
Delta(q,lambda_j(q))=2*(-1)^floor((j+1)/2) at every slot. Neighboring band
endpoints are strictly separated. The intrinsic lowest root has analytic
order one; open gap endpoints are simple and a collapsed gap root has
order two, including every central gap.

`HillHminusOneRealGapContours.lean` defines the geometric open real-band
domain and proves nonvanishing of the actual characteristic there. For
every positive gap index, its midpoint and one quarter of the smaller
neighboring band length give a canonical enclosing circle, including at
a collapsed gap. The outer disc with the selected gap removed lies in
that zero-free domain. The enclosing disc contains exactly its two actual
gap endpoints with total analytic zero count two. Each fixed circle
retains count two and boundary nonvanishing on a complex H^-1-open
neighborhood of the real input. This neighborhood may depend on the gap.

The actual primitive now glues holomorphically across all these real
bands, as proved below. Indexed endpoint boundary values and energy-analytic
filled central squares are also proved below. Analytic complex-potential
central Arnold/cubic periods remain to be proved. Theorem 1.1
and all main theorem flags remain unverified; the global Birkhoff-action
identity and real isospectral invariance are still required for action
descent and the global positive-ell2 Hamiltonian extension.

The generic `RealGapDiscIsolation.lean` is reused byte-for-byte from
`articles/kdv-estimates` at `7c7ec17`, with its unchanged import boundary
pinned in `canonical-gap-shared-imports.json`. The existing L2 uniqueness,
count continuity, trace parity and contour proofs are adapted to the
actual H^-1 characteristic; no additional physical spectral theorem is
assumed.

## Actual H^-1 band gluing and all-index real contour periods

`HillHminusOneRegularBoundary.lean` extends the actual upper primitive
and root holomorphically across every regular real energy. One upper
anchor fixes the root sign and primitive value, retaining the exact
logarithmic derivative and hyperbolic trace identities. The upper
boundary functions are literal full half-plane limits and agree with
these local analytic extensions. No high-index cutoff is required.

`HillHminusOneRealBands.lean` uses the intrinsic endpoint trace parity,
root-free open bands and the intermediate value theorem to put the
actual trace strictly between -2 and 2 in every band. The actual upper
boundary primitive is therefore purely imaginary there.
`HillHminusOneBandContinuation.lean` applies exact minus-conjugate
reflection to the regular extension. The same extension matches the
original upper and lower source sheets. Filling real bands by their
actual upper boundary values yields a single holomorphic primitive on
the complete geometric real-band domain, and a holomorphic nonvanishing
root on the same domain.

The glued functions satisfy R^2=Delta^2-4, 2*cosh(F)=Delta,
2*sinh(F)=R, exp(F)=(Delta+R)/2 and F'=Delta'/R. Both retain exact
minus-conjugate reflection. They agree with the original source functions
at every original source point, including admissible real points. This
agreement holds for complex H^-1 potentials too, so joint analyticity is
retained on the original source domain. Joint complex-potential extension
at the additional band points is not yet proved.

`HillHminusOneAllRealPeriods.lean` defines the literal polynomial moments
and shifted cubic periods on every positive-index canonical gap circle,
including central and collapsed gaps. Their integrands are circle
integrable and their values are real. The level-zero Arnold period has
the exact integration-by-parts identity
A_n=-(1/pi)*integral F=(1/pi)*integral lambda*Delta'/R,
with counterclockwise orientation and no extra factor i. The cubic
period is (1/pi)*integral (F+i*n*pi)^3. These are actual real-potential
contour integrals, not assumed coordinate-space factors.

Indexed endpoint boundary values and filled central shifted squares
are proved in the next milestone. Complex-potential analytic extensions
of the central periods and matching to the common high family remain
unproved. Central sign and action
identities, the global KdV Birkhoff map and real isospectral invariance
are still required for action descent and the global positive-ell2
Hamiltonian extension. Theorem 1.1 and the other main theorem flags
remain unverified.

The four generic trace-root, upper-extension and real-cosh modules are
reused byte-for-byte from `articles/kdv-estimates` at `253ce79`. Their
five retained import boundaries are byte-identical and pinned in
`band-primitive-shared-imports.json`. The regular-boundary, real-band and
band-gluing proofs adapt the shared L2 arguments to the actual H^-1
characteristic; no new spectral or Birkhoff theorem is assumed.

## Actual indexed endpoints and filled H^-1 squares at every gap

`HillHminusOneAllBoundaryLimits.lean` proves full upper half-plane limits
of the actual primitive and root at every real energy. At a characteristic
zero the root tends to zero. Its multiplier tends to the nonzero
half-trace, so a local logarithm preserves the actual integer period.
Both real boundary functions are continuous, including branch endpoints
and collisions, and retain their hyperbolic trace identities.

`HillHminusOneBoundaryLabelContinuity.lean` proves continuity of the actual
primitive boundary value at every moving intrinsic label in any
continuous real H^-1 potential family. The joint multiplier limit and a
fixed positive-height anchor control the logarithm period.
`HillHminusOneAllEndpointNormalization.lean` follows the real scaling path
from zero and proves F_upper(lambda_j)=-i*pi*floor((j+1)/2). Both endpoints
of the nth gap therefore have value -i*n*pi. There is no high-energy
cutoff, positive-gap assumption or bounded L2 norm assumption.

`HillHminusOneRealGapSigns.lean` propagates actual characteristic signs
across simple open-gap endpoints. The actual signed trace exceeds two
throughout each open gap. `HillHminusOneRealGapProfile.lean` defines its
literal arcosh profile v_n. It is continuous and nonnegative on each
closed gap, positive in the interior and zero at the endpoints.
`HillHminusOneBoundaryGapProfile.lean` and
`HillHminusOneGlobalGapBoundaryValues.lean` identify the actual full upper
and lower primitive limits with v_n-i*n*pi and -v_n-i*n*pi. Their vertical
jump is exactly 2*v_n, including at central endpoints and collapsed gaps.

`HillHminusOneAllGapSquares.lean` fills K_n=(F+i*n*pi)^2 through every
closed gap. The two boundary signs give the same square, hence a
continuous full-plane extension. The entire squared-cosh coordinate has
nonzero derivative on v_n^2, so its local analytic inverse proves energy
analyticity across the gap and its endpoints. The resulting actual K_n
is analytic on the entire canonical midpoint disc of radius half-gap
length plus twice its positive collar, at every n>=1. On the real gap
K_n=v_n^2 is nonnegative. The exact identity
coshSquareCoordinate(K_n)=(-1)^n*Delta/2 retains source normalization.

This is energy analyticity for each fixed real H^-1 potential. Joint
analyticity in nearby complex potentials, analytic central periods,
matching to the existing common high family, central period signs and
Birkhoff-action identification remain open. The global positive-ell2
Hamiltonian extension and all main theorems remain unverified.

Six generic boundary-limit, sign, continuous-extension and inverse-coordinate
modules are reused byte-for-byte from `articles/kdv-estimates` at
`1184615`, with retained import hashes in `endpoint-shared-imports.json`.
The eight H^-1 modules adapt the verified L2 arguments to the actual
unit-period distributional characteristic and the intrinsic H^-1 labels.

## Joint H^-1 filled-square and primitive-collar continuations

`CompactCoordinateExtension.lean` applies the analytic inverse theorem to
continuous functions on a compact set in the uniform norm. A regular
scalar coordinate gives one analytic parameter neighborhood for the
entire reference family. The exact coordinate equation and every
reference value are preserved. `CompactCoordinateJointExtension.lean`
uses continuous evaluation and scalar inversion to recover joint energy
and parameter analyticity on the compact set's interior.
`CompactCoordinateContinuation.lean` assembles the full construction.
`CompactCoordinateUniqueness.lean` proves uniqueness of continuation
germs for continuous compact lifts with the same reference family and
coordinate image.

`CoshSquareRegularity.lean` proves that a critical value of the entire
squared-cosh coordinate has square one.
`HillHminusOneGapCoordinateRegularity.lean` consequently proves its
nonzero derivative on every actual filled gap disc: the real cut has
nonnegative profile square, while any other critical point would force
an actual characteristic zero in the root-free band domain.

`HillHminusOneJointGapSquares.lean` constructs one jointly analytic filled
square on a fixed disc strictly enclosing the canonical circle, for
one complex-open H^-1 neighborhood of each real reference potential.
It agrees with the actual filled square on the entire reference closed
disc and satisfies coshSquareCoordinate(K)=(-1)^n*Delta/2 throughout the
joint chart, with nonzero coordinate derivative. All positive indices,
central gaps and collisions are included.

`HillHminusOneJointContourPrimitive.lean` applies the compact inverse to
cosh on a compact collar of the canonical circle. It gives one joint
analytic primitive on an open energy collar and one complex potential
neighborhood. On the entire reference collar it equals the actual
source-normalized primitive, including the real band points. Throughout
the complex chart it satisfies 2*cosh(F)=Delta and sinh(F) is nonzero.
Thus the full logarithm period is retained at once around the contour.

`HillHminusOneJointGapPeriodGerms.lean` integrates this same primitive
to construct all polynomial moments and the shifted cubic moment on one
analytic potential neighborhood. Its statement retains the primitive
collar, actual trace identity, exact reference branch and literal integral
formulas. At the reference potential the integrals equal the canonical
real periods, with counterclockwise A_n,m=-(1/pi)*integral lambda^m*F and
R_n=(1/pi)*integral (F+i*n*pi)^3, without an additional factor i.

These are local analytic continuations of the full actual reference
functions. The next milestone identifies their contour integrals with
the actual canonical periods at every nearby real input, simultaneously
on any prescribed finite index set. Gluing a global potential-space
family and matching to the existing common high family remain open. The global Birkhoff map,
action identity and real isospectral invariance remain required before
the verified action-space descent can yield Theorem 1.1. All main theorem
flags remain unverified.

Four compact-function and analytic-circle-integration modules are
reused byte-for-byte from `articles/kdv-estimates` at `174af0e`. Their
retained import boundaries are pinned in `joint-square-shared-imports.json`.

## Actual canonical periods and simultaneous finite-head analyticity

`ScalarCoordinateUniqueness.lean` proves uniqueness of continuous germs
through a regular analytic scalar coordinate.
`HillHminusOneTraceChartSource.lean` applies this to the actual hyperbolic
trace at nonreal anchors. The analytic identity theorem propagates exact
source agreement over connected energy charts for every nearby real
H^-1 input. `HillHminusOneTraceChartBoundary.lean` handles both half-discs
and uses the full upper boundary limits to identify the real diameter.
`HillHminusOneTraceChartRealAgreement.lean` turns these local product
neighborhoods into one potential neighborhood for an entire compact
contour collar. Both source sheets and the original logarithm period
are retained; no nearby-real identification is assumed.

`HillHminusOneGapContourContinuity.lean` proves continuity of canonical
gap centers, half-lengths, collars and radii from the intrinsic labels,
including collisions. It provides a complex-open neighborhood controlling
the center-plus-radius perturbation at every nearby real potential.
`NearbyCircleHomotopy.lean` bounds corresponding circle points and keeps
the affine circle homotopy in one fixed closed collar. The same geometric
bound preserves every holomorphic integrand, so it is independent of the
polynomial moment order.

`HillHminusOneAnalyticCanonicalPeriods.lean` combines the actual collar
agreement with this deformation. For every real H^-1 potential and every
positive gap index it constructs complex-analytic extensions of all
literal canonical polynomial moments and the shifted cubic period on
one neighborhood. They equal the actual moving-circle periods at every
nearby real input, including central and collapsed gaps. This strengthens
the preceding reference-germ result to local analyticity of the actual
canonical periods. The exact counterclockwise factors remain
A_n,m=-(1/pi)*integral lambda^m*F and
R_n=(1/pi)*integral (F+i*n*pi)^3, without an extra factor i.

`HillHminusOneFinitePeriodExtensions.lean` gives one neighborhood before
every index in any prescribed finite set and every polynomial order,
with analytic Arnold/cubic families and exact nearby-real canonical
identities. This supplies the finite central head needed for Lemma 4.6.
Matching the actual canonical periods to the previously constructed
common high family, obtaining one neighborhood for the entire sequence,
central cubic signs and action identities remain open. Global Birkhoff
coordinates and real isospectral invariance are still required for the
positive-ell2 action-space extension. All main theorem flags remain
unverified.

## All-index canonical signs, real formulas and exact zero criteria

`HillHminusOneAllCubicSigns.lean` applies the physical real-cut theorem
to the actual filled square on every canonical gap disc. Global upper
and lower sheet signs fix the counterclockwise jump. Consequently every
actual canonical cubic period is real and nonpositive, including low
and collapsed gaps. Its finite-head analytic extensions retain these
signs at every nearby real input.

`RealCutWeightedPowerIntegral.lean` proves the literal weighted odd-power
cut formula. A filled analytic square bounds the weighted integrands
near both endpoints, and bounded removability handles a collapsed cut.
For every polynomial order m and odd power 2*k+1, the contour integral
of lambda^m*(F+i*n*pi)^(2*k+1) is minus twice the real integral of
x^m*v_n(x)^(2*k+1).

`HillHminusOneRealPeriodFormulas.lean` identifies the original canonical
periods with their real profile integrals:
A_n,m=(2/pi)*integral x^m*v_n(x) and
R_n=-(2/pi)*integral v_n(x)^3,
with bounds lambda_(2*n-1) to lambda_(2*n). Here v_n is the actual signed
arcosh profile, not an assumed comparison profile. The analytic polynomial
shift contributes zero to the Arnold contour. All signs and factors
retain the original counterclockwise normalization, without an extra i.

`HillHminusOneAllPeriodZeros.lean` proves nonnegativity of every even
polynomial Arnold period. The level-zero Arnold period is positive
exactly when the actual gap is open. The cubic period is strictly
negative exactly in that case. Both vanish exactly on a closed gap,
and every polynomial Arnold period vanishes there. Thus R_n=0 if and
only if A_n,0=0, at every positive index, including central endpoints
and collisions.

The article-specific `CanonicalMomentPreparation.lean` packages one
complex-open neighborhood for any prescribed finite positive-index
head. All polynomial and cubic families are analytic there and match
the actual nearby-real canonical periods, with Arnold nonnegativity,
cubic nonpositivity/reality and the exact common zero criterion. This
supplies the finite-head spectral sign and zero inputs for Lemma 4.6(i).
Global Birkhoff actions are not yet identified with these Arnold periods;
Lemma 4.6(ii), the common infinite-tail matching, action-fiber invariance
and the actual global positive-ell2 Hamiltonian extension remain open.
All main theorem flags remain unverified.

## Canonical/high matching and a common all-index analytic family

`HillHminusOneCanonicalTailLocalization.lean` identifies the intrinsic
labels with sharply confined ordered high pairs, independently of disc
radius. On one common H^-1 neighborhood both canonical endpoints lie
within n/8 of the free energy at every high index and real input.
`RealGapCircleNesting.lean` and
`HillHminusOneTailContourGeometry.lean` combine this with the quadratic
free lattice spacing. The adjacent actual bands are at least 8*n long;
the free-centered radius-n disc lies inside the canonical midpoint disc,
and both circles enclose the same gap cut, including a collapsed gap.

`HillHminusOneCanonicalHighPeriods.lean` deforms the two circles through
the actual band-filled primitive's analytic cut domain. Exact source
agreement on the original circle retains both the logarithm period and
the original constants. One complex-open neighborhood and cutoff precede
every high positive index and every polynomial order. At all real inputs
there, the actual canonical Arnold and cubic periods equal the literal
uniform high source periods.

The article-specific `CommonCanonicalMomentFamily.lean` combines that
tail with the simultaneously analytic finite head. At every real H^-1
reference it constructs C>0, N>=2 and one complex-open W, then analytic
A_n,m and R_n on W for every positive n and every polynomial order m.
Every real input in W gives the actual canonical periods. Throughout the
complex tail the functions are exactly the old literal source periods
and satisfy norm(8*n*pi*R_n)<=C*norm(A_n,0)^2 with the same constant C.
All real Arnold nonnegativity, cubic nonpositivity/reality and the exact
common zero criterion survive in this one family.

Thus the finite head and infinite tail no longer require separate
potential neighborhoods. The next milestone glues these local families
on one complex neighborhood of the entire real potential space. Global Birkhoff coordinates, their
Arnold-action identity and real isospectral/action-fiber invariance
remain required before the checked action-space descent and ell2
summation apply. The physical Hamiltonian/frequency identities and all
main theorem completion flags remain open.

## Global potential-space canonical moment gluing

`PhysicalRealImag.lean` constructs the physical real and imaginary
Fourier parts on every symmetric weighted coefficient space. Physical
conjugate reflection is an isometry; both parts are continuous norm
contractions and give an exact complex decomposition.
`PeriodOneHminusOneRealForm.lean` identifies raw H^-1 Fourier reality
with the fixed locus, proves convexity and real-linear closure, and
specializes analytic real-form gluing to the physical potential space.

`RealFormBallGluing.lean` proves that intersecting balls with real centers
contain a real point on the segment joining the centers. The continuous
real-form identity theorem propagates real agreement across the entire
complex overlap. Banach-valued analytic maps therefore glue uniquely
on the union of the balls. That union depends only on the real centers
and radii, so all indices and all moment orders use the same domain.

The article-specific `GlobalCanonicalMomentFamily.lean` chooses one ball
inside each common local chart and glues every polynomial and cubic
family. It constructs one complex-open Omega containing the entire real
unit-period H^-1 space. Every A_n,m and R_n is analytic on Omega and equals
the actual canonical period at every real potential, including central
and collapsed gaps. Arnold nonnegativity, cubic nonpositivity/reality
and the exact common zero criterion hold on the full real locus.

The glued functions agree with each local family on its entire complex
ball. Consequently at every real reference there are C>0, N>=2 and one
complex-open V inside Omega, before every high index and every complex
input p in V, such that norm(8*n*pi*R_n(p))<=C*norm(A_n,0(p))^2.
The whole complex tail also equals the literal high source family there.
No global coefficient-space or action-space normalization is changed.

This completes the potential-space gluing step. The actual global KdV
Birkhoff map, its Arnold-action identity and identification of its action
fibers with discriminant fibers remain required. Full-discriminant
invariance of the actual real periods is now proved below.
The physical Hamiltonian/frequency identities and all main theorem
completion flags remain open.

Four reflection and real-form identity modules are reused byte-for-byte
from `articles/kdv-estimates` at `fe66709`, with their retained import
boundary hashes in `real-form-gluing-shared-imports.json`.

## Actual real isospectral invariance and the ell2 extension connection

`CoshLogBoundaryUniqueness.lean` proves that positive real parts select
the same exponential above a common cosh value, and that a common finite
boundary limit fixes the full logarithm period on a connected domain.
`HillHminusOneIsospectralLabels.lean` transports actual high gap pairs
under equality of the entire discriminants. Their exact tail slots and
ordered multiplicity uniqueness fix all canonical characteristic labels,
including the lowest root and every central collision.

`HillHminusOneIsospectralPrimitive.lean` uses the upper physical sheet
sign and the exact zero boundary value at that common lowest root to
identify the source primitive, without an undetermined logarithm period.
Reflection identifies the lower branch; full upper limits identify all
real boundary values. The complete real-cut primitive, root and filled
squares therefore agree. `HillHminusOneIsospectralPeriods.lean` identifies
the canonical contour geometry and all polynomial and cubic periods,
including central and collapsed gaps. The hypothesis throughout is
**equality of the actual entire discriminant at two real potentials**.
Action equality or equality of gap lengths is not used in its place.

`IsospectralCanonicalMoments.lean` retains one global complex-open
potential neighborhood with all actual real values, signs, zero criteria
and locally uniform complex-tail bounds, and adds this exact real
full-discriminant invariance.

`SpectralCoordinateExtension.lean` defines the precise remaining input:
an analytic potential map near every real normalized Hilbert pair,
preserving reality, whose real Arnold periods are its raw quadratic
actions and whose real action fibers have equal discriminants. No
existence or symplecticity of this coordinate realization is asserted.
The theorem `global_contour_extension_of_spectral_coordinate_realization`
composes the proved actual global periods with any such realization.
Real-form uniqueness continues its real Arnold identity throughout each
complex ball, before every index. The existing uniform spectral estimate
therefore becomes the required complex quadratic action bound without
assuming a complex Arnold identity or additional period estimates.

The proved descent/gluing/summation mechanism then constructs one base
action neighborhood independent of index and an analytic, absolutely
convergent contour sum on its positive-ell2 preimage. It recovers every
actual real cubic period; on the nonnegative base cone each period is
real and nonpositive and vanishes exactly when its own raw action does.
The sum is real and nonpositive on the full positive-ell2 quadrant and
vanishes at zero. This is a **conditional extension theorem**. Constructing
the spectral coordinate realization and identifying the sum with the
physical renormalized Hamiltonian remain required for Theorem 1.1.

## Actual rough quasi-Hill initial-value and monodromy identification

`QuasiHillAffineCoordinates.lean` constructs a fixed state map T, with
T^2=2*Id and inverse T/2. It intertwines the quasi-derivative Hill system
with the physical AKNS system at frequency (mu+1)/2 and potential
(u-i*(mu-1)/2,u+i*(mu-1)/2). The change of coordinates is independent of
energy and stays invertible at zero. No derivative of u is involved.

`L2QuasiHillPotential.lean` constructs this affine potential as an actual
physical Lebesgue L2 class and proves its representative identity almost
everywhere. `L2QuasiHillSolution.lean` transports the verified physical
Volterra solver. It proves exact initial data, the ordinary Bochner
integral equation, absolute continuity, and the differential equation
almost everywhere. The solution is jointly analytic in energy and the
L2 profile in the uniform curve norm. `L2QuasiHillUniqueness.lean` takes
any continuous quasi-derivative integral solution back to the physical
AKNS problem, proving uniqueness for every complex energy.

`L2QuasiHillDiscriminant.lean` defines the trace from the two actual
prescribed-data solution columns. It proves joint entire dependence,
exact recovery of the independently constructed continuous-profile
quasi-Hill solution and trace, and equality at energy z^2 with the
original physical diagonal AKNS trace. The density proof uses actual
physical L2 classes and includes z=0.

`HillMiuraL2PhysicalQuasi.lean` applies the unit-interval Fourier isometry
to the original scalar coefficients. Their diagonal physical class is
exactly the original source-to-physical map, so the previously defined
Miura energy discriminant equals the actual rough quasi-Hill trace at
every complex energy.

`HillHminusOnePhysicalQuasi.lean` gives each shifted-Miura chart its actual
physical L2 profile and unique absolutely continuous solution, with
joint energy/potential analyticity. The checked Fourier formula gives
q_k=2*pi*i*k*u_k+sum_j u_(k-j)*u_j-delta_(k,0)*energyShift,
without changing normalization. The intrinsic H^-1 discriminant is exactly
the sum of the two physical diagonal endpoint entries at shifted energy
lambda+energyShift. These actual traces agree for different lift branches
and different mass shifts on every chart overlap.

This proves the rough initial-value and monodromy-trace comparison. A
chart-independent singular Hill operator domain, its self-adjoint
spectral realization, the actual global KdV coordinate map and its
Arnold-action/fiber identities remain essential work. No main theorem
completion flag changes.

## Actual scalar weak equations and canonical endpoint multipliers

`L2QuasiHillRegularity.lean` defines the actual scalar position and
quasi-derivative curves. Both are absolutely continuous with L2 first
derivatives; their derivative identities hold almost everywhere for the
original L2 profile. Multiplication by a continuous interval curve
preserves L2, so no pointwise regularity of the profile is required.

`L2QuasiHillWeakEquation.lean` constructs the factored shifted Miura
bilinear form integral (y_prime-u*y)*(phi_prime-u*phi)-c*integral y*phi.
The integrand is proved integrable for every pair of continuous curves
with L2 derivatives. The actual solution satisfies Green's identity
against every absolutely continuous test with L2 derivative, retaining
w(1)*phi(1)-w(0)*phi(0)+(mu-c)*integral y*phi. The boundary term uses the
continuous quasi-derivative; it does not evaluate the rough profile at
an endpoint. Zero endpoint tests give the scalar weak eigen-equation.

`L2BoundaryMultipliers.lean` proves that the actual physical L2 monodromy
propagates arbitrary initial coordinates, identifies its matrix kernel
with the endpoint multiplier condition, and derives the full determinant
one quadratic criterion. `L2QuasiHillMultipliers.lean` transports every
complex multiplier through the fixed invertible state map. In particular,
trace +2 is exactly the periodic nonzero-state condition and trace -2 is
exactly the antiperiodic condition, including zero energy.

`L2QuasiHillScalarNontrivial.lean` proves that zero scalar position forces
zero initial data. The first derivative identity forces the continuous
quasi-derivative to vanish almost everywhere; equality on the full closed
interval follows from continuity. Thus a nonzero state gives an actual
nonzero scalar position.

`HillHminusOneWeakEquation.lean` transfers H1 scalar regularity and the
Green identity to every shifted-Miura chart, with the constant shift
cancelled to the literal energy lambda. A state multiplier sigma and
reciprocal test multiplier rho, with sigma*rho=1, cancel the boundary
term. `HillHminusOneWeakSpectrum.lean` identifies all complex endpoint
multipliers directly from the intrinsic H^-1 discriminant. Its radicand
vanishes exactly when a nonzero actual state is periodic or antiperiodic.
For every real canonical label j, including the lowest, central and
collapsed-gap labels, it constructs a nonzero H1 scalar position with
endpoint sign (-1)^floor((j+1)/2) and proves its weak equation for every
H1 test with that same endpoint sign.

The next milestone identifies these chart forms with one intrinsic form
of the original potential. The converse from arbitrary weak solutions,
closed/self-adjoint operator domain and spectral multiplicity
identification remain unproved. The actual KdV coordinate
realization and its Arnold-action/fiber identities are still required
for the unconditional positive-ell2 extension in Theorem 1.1.

## Intrinsic entire weak Hill form and potential functional

`IntervalL2Products.lean` constructs the bounded unconjugated physical
L2 pairing and identifies it with the actual unit-interval integral. A
continuous interval curve acts by a bounded complex-linear L2 multiplier.
`IntervalH1Product.lean` proves that products of H1 interval curves remain
absolutely continuous with L2 derivatives, with the actual a.e. product
rule. `WeakMiuraFormAnalytic.lean` expresses the factored weak form through
these physical bounded maps and proves joint norm analyticity in the L2
profile and constant shift for every fixed H1 curve pair.

`SobolevMiuraPhysicalClass.lean` identifies the unit Fourier isometry of
the original H1 profile and its Miura image with the actual functions u
and u_prime+u^2. The original derivative symbol 2*pi*i*k and the constant
energy translation are retained exactly. `SobolevMiuraWeakForm.lean`
uses integration by parts to identify the factored form with the ordinary
physical L2 Hill form whenever the two H1 curves have matching product
endpoints. This includes periodic, antiperiodic, reciprocal Floquet and
Dirichlet pairs.

`HillHminusOneWeakFormCharts.lean` applies that physical comparison to
every L2 input in every shifted-Miura chart. Norm continuity and H^-1
density then prove equality on every complex chart overlap. The result
has no reality or mean-zero restriction. `HillHminusOneIntrinsicWeakForm.lean`
constructs one form of the original potential, independent of lift branch
and mass shift on all admissible curve pairs. For every such fixed pair,
the form is entire in the original complex H^-1 norm and recovers the
physical L2 Hill form on L2 potentials.

`HillHminusOneWeakPotentialFunctional.lean` subtracts only the kinetic
integral y_prime*phi_prime. Physical L2 density proves exact additivity
and complex homogeneity of the remainder in q. Together with the proved
norm continuity, this constructs a bounded complex-linear functional on
the original H^-1 space. The intrinsic form is therefore the original
kinetic term plus the actual continuous potential pairing, without a
Riccati branch in that conclusion.

`HillHminusOneIntrinsicWeakSolutions.lean` defines the weak eigenfunction
predicate using only q, the scalar H1 curve, endpoint multiplier and
intrinsic weak form. Every complex characteristic multiplier gives an
actual nonzero scalar H1 weak eigenfunction; nonzero multiplier is derived
from the determinant-one quadratic. Every real canonical label, including
the lowest, central and collapsed-gap labels, has one with the exact
indexed sign (-1)^floor((j+1)/2). The test multiplier is the reciprocal
state multiplier, so the complete statement has no chart parameter.

This completes chart independence of the weak form and its bounded
linear dependence on the original potential. The following milestone
proves the weak-solution converse. Closed/self-adjoint intrinsic operator
domains and spectral multiplicity identification remain open, as do the
actual KdV coordinate realization and its Arnold-action/fiber identities.

## Exact weak Floquet spectrum and analytic contour differentiation

`UnitIntervalPrimitive.lean`, `UnitIntervalWeakDerivativeConstant.lean`
and `UnitIntervalWeakDerivativeAC.lean` recover an actual absolutely
continuous representative from an L2 function with an L1 weak derivative.
The zero-derivative argument uses the H1 primitive of the conjugated
zero-mean residual as a Dirichlet test. It assumes no extension of the
weak equation beyond the unit interval.

`L2QuasiHillWeakMomentum.lean` recovers the quasi-derivative from an
arbitrary H1 scalar weak solution. `L2QuasiHillWeakReconstruction.lean`
integrates the resulting AC state and applies actual Volterra uniqueness.
`L2QuasiHillWeakFloquetConverse.lean` uses an H1 test with endpoints one
and reciprocal multiplier to recover the missing momentum endpoint
condition. No momentum regularity or state endpoint equation is an input
to this scalar converse.

`HillHminusOneIntrinsicWeakConverse.lean` therefore proves, in every
Miura chart and at every complex energy,

```text
exists nonzero intrinsic H1 weak Floquet eigenfunction with multiplier sigma
  iff sigma^2 - hillHminusDiscriminant(q,lambda)*sigma + 1 = 0.
```

The intrinsic predicate now explicitly requires `sigma != 0`; the old
zero-multiplier case encoded unrelated mixed endpoint conditions because
inverse zero is zero. The existing forward existence theorem already
derived nonzero multiplier and retains that witness. Periodic and
antiperiodic intrinsic weak energies are exactly the actual radicand
zeros. At every real potential they are exactly the canonical labels,
including the lowest, central and collapsed-gap labels. This proves the
weak-solution converse; closed/self-adjoint operator domains and spectral
multiplicity identification remain open.

`TailSeriesRealization.lean` strengthens the analytic ell2 summation step:
the entire weighted sequence, including every unestimated finite head
term, is an analytic ell1-valued map on the same domain. Its derivative
coordinates are the actual term derivatives, which are absolutely
summable in every ell2 direction. The scalar Frechet derivative equals
their literal sum.

`GlobalContourDifferentiation.lean` transports this result to the exact
base-action preimage containing the entire nonnegative ell2 quadrant.
The normalization is `8*n*pi*R_n`. Local cutoffs may vary between patches.
The complete partial sums converge uniformly on every compact subset of
the same complex domain. These statements use the analytic-moment and
local-tail-bound interface; the actual KdV coordinate realization and
physical Hamiltonian/frequency identification remain required.

## Intrinsic Dirichlet spectrum and analytic H^-1 root branches

Seven exact source modules are reused from `articles/kdv-pseudomeasures`
at `34c933b`, with hashes in `dirichlet-shared-imports.json`. They construct
the original normalized Dirichlet characteristic, jointly entire in
energy and complex H^-1 potential, and retain its free zero-energy value
one. Three existing generic implicit-function modules are reused from
the pinned shared main baseline. All ten are checked in this worktree.

`L2QuasiHillEnergyAgreement.lean` identifies the full actual solution
curves of the two fixed energy-affine state realizations, by their common
continuous-profile IVP and original L2 density. Initial data and zero
energy are retained. `HillHminusOnePhysicalDirichlet.lean` identifies the
entire characteristic with the actual terminal position of the normalized
column `(0,1)`, in every shifted-Miura chart.

`HillHminusOneIntrinsicDirichletSpectrum.lean` proves that its zeros are
exactly the intrinsic nonzero H1 weak Dirichlet eigenfunctions. Every such
function is a nonzero scalar multiple of that same normalized column in
every chart, proving geometric simplicity without assuming a momentum
representative or its regularity in the scalar weak predicate.

`IntervalH1Conjugation.lean` proves conjugate H1 regularity and nonzero
physical L2 mass of a nonzero continuous curve. `HillHminusOneWeakFormReality.lean`
uses actual real L2 potentials and real Fourier density to prove reality
and conjugation symmetry of the intrinsic form at every real H^-1 input.
No real Riccati lift is assumed. `HillHminusOneWeakSpectrumReality.lean`
then proves that all intrinsic Dirichlet energies and every unit-modulus
Floquet energy are real. The actual Dirichlet characteristic has no
nonreal roots at a real potential.

`L2QuasiHillDirichletDerivative.lean` derives the two-energy Lagrange
identity from symmetry of the factored form and the exact weak Green
identities. Uniform-curve analyticity gives, at any complex root,

```text
momentum_lambda(1) * Dirichlet'(lambda) = integral position_lambda^2.
```

`HillHminusOneDirichletSimplicity.lean` transfers the formula to the
original energy, with the chart shift retained. Conjugation symmetry,
geometric simplicity and nonzero physical mass show that the scalar
square integral cannot vanish at a real potential. Every root of the
actual entire Dirichlet characteristic therefore has nonzero energy
derivative and analytic order one, including a root at zero energy.

`HillHminusOneDirichletRootBranches.lean` applies the shared analytic
implicit-function theorem. Every root at every real potential has a local
complex analytic root branch in the original H^-1 norm, real at nearby
real inputs. A global label or continuously selected root is not an input.
Global rough Dirichlet labels/interlacing and the actual global KdV
coordinate realization remain to be constructed. All main theorem flags
remain false.

## One actual Dirichlet label in every canonical H^-1 gap

`IntervalEndpointTests.lean` supplies actual real H1 tests with prescribed
endpoints. `HillHminusOneIntrinsicGreen.lean` exposes the chart-free weak
Green identity on all admissible H1 pairs. Weak conjugation and initial
state reconstruction then prove that the normalized Dirichlet position
is real throughout the unit interval at every real energy and real
H^-1 potential, even for a complex chosen Miura lift and shift. A test
with endpoints one and zero fixes the initial normalization exactly.

`HillHminusOneDirichletBands.lean` proves that the terminal
quasi-derivative at a Dirichlet zero is real and is an actual Floquet
multiplier. Its determinant-one quadratic forces the real discriminant
square to be at least four. Thus every open canonical band, including
the lowest band, contains no Dirichlet root.

The scalar free-flow proofs are reused verbatim from the shared KdV
estimates branch in `ClassicalHillFreeDirichlet.lean`, with an adapted
import to avoid duplicate characteristic declarations. The exact generic
closed-interval-root and positive-zero-uniqueness modules are reused
unchanged. Their source commit and hashes are recorded in
`dirichlet-gap-shared-imports.json`. `HillHminusOneFreeDirichlet.lean`
recovers the original formula `Dirichlet(0,z^2)=sin(z)/z` for nonzero z,
the free zero-energy value one, and the roots `pi^2*n^2`.

`HillHminusOneDirichletGapExistence.lean` proves that the real-family set
of inputs with a Dirichlet root in a fixed indexed closed gap is clopen.
Compact variable-interval projection gives closedness; the actual simple
analytic root branch and neighboring open-band exclusion give openness.
The real scalar path from zero to an arbitrary real H^-1 potential proves
existence in every positive gap, including every collapsed gap.

`IntervalCurveMass.lean` proves strict positivity of the physical scalar
L2 mass. The original energy derivative identity, the real normalized
column and canonical signed trace bound give
`(-1)^n*Re(Dirichlet'(q,x))>0` at every root in the nth closed gap.
`HillHminusOneDirichletGapUniqueness.lean` applies the shared real zero
uniqueness lemma, proving exactly one root per positive canonical gap.

`HillHminusOneDirichletGapLabels.lean` defines these intrinsic labels.
They strictly increase, lie between the exact gap endpoints, equal the
common endpoint in a collapsed gap, and equal `pi^2*n^2` at zero. Each
label agrees locally with a complex analytic branch in the original
H^-1 norm; this agreement also proves global real H^-1 norm continuity.
No continuity of the label was assumed to obtain that agreement.

This constructs the positive-gap labels. Exhaustion of every Dirichlet
zero, especially below the lowest periodic energy, remains unproved.
A common complex domain for sequence-valued Dirichlet/norming data and
the actual global KdV coordinate realization are still required. The
physical Hamiltonian/frequency bridge and all main theorems remain open.

## Intrinsic entire Dirichlet column and actual norming data

`HillHminusOneDirichletColumnCharts.lean` recovers the normalized actual
Dirichlet position from its intrinsic weak equation in every Miura chart.
An H1 test with endpoints one and zero fixes its initial quasi-derivative
to one. Thus all charts give the same entire scalar interval curve at
every complex energy and potential. At a Dirichlet root, a second H1
endpoint test proves equality of the terminal quasi-derivatives as well.
Unrestricted terminal momentum equality away from roots is not claimed.

`HillHminusOneIntrinsicDirichletColumn.lean` constructs one intrinsic
normalized scalar curve. It is jointly entire in energy and original
complex H^-1 potential with values in the full continuous-curve Banach
space and its uniform norm. It is a nonzero H1 curve, starts at zero,
and its terminal value is the original Dirichlet characteristic. At real
inputs and real energies the entire interval position is real.

`HillHminusOneDirichletNorming.lean` evaluates the actual endpoint
quasi-derivative at every positive-gap Dirichlet label. These factors
are independent of the chart, real, nonzero and of exact sign `(-1)^n`.
They satisfy the actual discriminant's multiplier quadratic. Each has a
local complex analytic extension in the original H^-1 norm and is
continuous on the whole real H^-1 space. On a collapsed gap and at the
free potential the factor is exactly `(-1)^n`.

`HillHminusOneDirichletLogNorming.lean` defines
`kappa_n=log((-1)^n*Re(gamma_n))` using the strictly positive signed
endpoint factor. Its real logarithm is the principal complex logarithm
of that positive factor. Each logarithmic coordinate has a local complex
analytic H^-1 extension and global real norm continuity, recovers the
factor under the exponential, and is zero on collapsed gaps and at zero.

`HillHminusOneDirichletNormingTrace.lean` proves the exact physical trace
and already constructed source-profile identities:

```text
(-1)^n*Re(D(q,mu_n)) = 2*cosh(kappa_n)
hillHminusRealGapProfile(q,n,mu_n) = abs(kappa_n).
```

The logarithm is zero exactly when the Dirichlet label is at one of its
canonical gap endpoints. This includes endpoints of open gaps as well
as collapsed gaps; vanishing is not identified with gap closure alone.
These are actual intrinsic spectral quantities. A common sequence-valued
analytic norming map, tail estimates, global inverse and the KdV
symplectic/action identities remain to be proved, as do all main theorems.

## Exhaustive Dirichlet spectrum and two-sided Arnold bounds

`HillHminusOneRealMiuraCharts.lean` uses the exact shared equivariant
quadratic inverse to construct a chart preserving physical realness near
every real H^-1 potential, with one positive real square energy shift.
`L2QuasiHillDirichletPositive.lean` proves strict positivity of every
Dirichlet energy of the actual real L2 Miura factorization, using its
nonzero normalized position and momentum and their positive L2 masses.
`HillHminusOneDirichletLowerBound.lean` obtains a local uniform lower
bound for all actual Dirichlet roots at nearby real inputs.

`HillHminusOneDirichletLowerExterior.lean` proves that existence of a
root at or below the periodic ground state is clopen in any continuous
real family. The local lower bound supplies compactness; the actual
simple analytic root branch and open-band exclusion supply openness.
The scalar homotopy to the free characteristic excludes that entire
lower exterior, including equality at the ground state.

`HillHminusOneLabelCofinality.lean` proves that actual even canonical
labels exceed any prescribed real energy. Together with the lower
exclusion, open-band exclusion and positive-gap uniqueness,
`HillHminusOneDirichletSpectrumExhaustion.lean` proves:

```text
S(q,lambda)=0 iff lambda=mu_n(q) for a unique positive index n
lambda is an intrinsic weak Dirichlet energy iff lambda=mu_n(q).
```

These statements hold at every real H^-1 input and for every complex
energy. Thus all characteristic zeros are exhausted; the previously
proved analytic order one and weak scalar-column uniqueness apply to
each of them. No closed-operator domain or operator algebraic
multiplicity is substituted for this characteristic/weak statement.

`ClassicalHillActionUpperBound.lean` deforms an Arnold cut period to
the gap circle. The primitive contributes one gap factor and the circle
radius contributes a second. The collapsed case extends analytically
through the repeated root and has zero period.
`HillHminusOneArnoldGapUpperBound.lean` applies this to the actual
source-normalized H^-1 periods and combines it with the reverse bound:

```text
gap_n^2/n <= 16*pi*abs(A_n)
abs(A_n) <= C*gap_n^2/n
A_n=0 iff the actual high gap pair coincides.
```

One complex H^-1-open neighborhood, cutoff and constant precede all
high indices and nearby complex potentials. Intrinsic unordered-pair
uniqueness puts both estimates on the same pair even if their original
energy radii differ. This is preparation for the sequence-valued
spectral coordinates needed by the global positive-ell2 extension.
Constructing those coordinates, their inverse and Arnold-action identity
remains required; no unconditional Theorem 1.1 extension is claimed.

## Global analytic weighted Arnold-action sequence

`HillHminusOneMiuraGapComparison.lean` identifies the translated principal
square roots of the actual Hill endpoints as original diagonal NLS
periodic energies. Once the index is large relative to the fixed energy
shift, both lie in the same complete NLS spectral strip. Its two endpoint
values control their difference without choosing an analytic ordering.
The exact energy factorization then gives

```text
abs(lambda_plus-lambda_minus) <= 3*pi*n*abs(diagonal_NLS_gap_n).
```

`HillHminusOneGapMajorant.lean` uses the existing canonical endpoint
cutoff and the actual NLS gap sequence to make this estimate uniform on
one complex H^-1 neighborhood. That ell2 sequence has a locally bounded
norm. Unordered-pair uniqueness makes the bound independent of which
Hill energy radius was used to construct the high pair.
`HillHminusOneArnoldMajorant.lean` combines this with the proved actual
Arnold upper bound, retaining the exact base weight:

```text
abs(A_n)/(1+n) <= C*abs(g_n)^2,   g in ell2, norm(g) locally bounded.
```

`AnalyticSquareTailMajorant.lean` proves a reusable Banach-valued analytic
realization theorem. A sampled ell2 square controls the complete ell1
tail; the finite analytic head has its own local bound. The majorant
itself need not be analytic. Injective sampling cannot increase its
squared norm. This proves actual ell1 membership, the exact coefficient
values and analyticity in the Banach norm, excluding the total
constructor's zero fallback throughout the analytic domain.

`SpectralActionSequence.lean` applies this realization to the actual
canonical periods with raw action coefficients preserved.
`GlobalSpectralActions.lean` constructs one weighted ell1 Arnold-action
map on a single complex-open neighborhood of the entire real H^-1
space. At every real input all raw coordinates are the original
canonical contour periods. The sequence is real and nonnegative, each
coordinate vanishes exactly at its corresponding closed gap, and the
whole sequence vanishes at the free potential. Equality of the entire
real discriminants implies equality of these full action sequences.

This is an actual global analytic **action map**, not an invertible
Cartesian spectral coordinate map. No injectivity, inverse potential
realization, or converse action-fiber/discriminant identity is inferred.
Those remain necessary to instantiate the positive-ell2 extension theorem.

The newly traversed inherited import closure has 650 source modules
outside the prior focused baseline; all match the read-only compiled
reference byte-for-byte. Its source hashes and direct roots are recorded
in `action-sequence-library-reuse.json`. Those reference modules were
used as compiled imports and were not rebuilt in this incremental check.
All actually used transitive axioms are covered by the cumulative audit;
the direct library roots are additionally audited by module origin.

## All-index Dirichlet source identification and global Hilbert coordinates

`L2QuasiHillDirichletGauge.lean` uses the phase-rotated physical profile
`(i*u,-i*u)` and the state map `(f1-f2,-i*z*(f1+f2))`. It intertwines the
actual rough integral equations. The original NLS Dirichlet initial
vector `(1,1)` maps to `(0,-2*i*z)`. Initial-data linearity gives the
exact source-normalized identity `chi_D(z)=z*S_Hill(z^2)`, including
zero frequency and without a trace of the rough profile at the endpoints.

`HillHminusOneDirichletMiuraSource.lean` proves the literal Fourier-to-
physical comparison and the exact shifted identity in every complex
H^-1 Miura chart. At nonzero frequency the characteristic zero conditions
are equivalent, with that nonzero hypothesis kept explicit. A physically
real lift gives an original real-type NLS source.
`HillDirichletMiuraZeroIndex.lean` proves that the added zero-frequency
root has exactly canonical index zero. Along the real scalar homotopy,
strictly ordered neighboring roots, continuity and exhaustion make this
index fixed. Positive indices consequently give exactly positive
frequencies.

`HillHminusOneDirichletMiuraLabels.lean` squares those positive roots
and subtracts the fixed real energy shift. The result is a strictly
increasing enumeration of every actual Hill Dirichlet energy. Uniqueness
of exhaustive ordered enumerations identifies it with `mu_n` at **every
positive index**, including all central modes and closed gaps. No unknown
index offset, high-tail-only matching or eigenvalue-model substitution
enters this identification.

`HillHminusOneDirichletCommonAnalytic.lean` pulls back the existing
Banach-analytic NLS Dirichlet displacement sequence. Uniformly small
high displacements and finitely many nonzero low roots give one complex
H^-1-open neighborhood supporting all positive Dirichlet branches.
Every branch is an actual complex Dirichlet zero throughout this common
domain; on every nearby real input it is the actual indexed label.
One analytic ell2 sequence `d` gives `mu_n=(pi*n+d_n)^2-c^2` with a fixed
positive real `c`.

`HilbertSampling.lean` proves contractivity and linear continuity of
injective integer sampling. `DirichletSequenceCoordinates.lean` uses
it to construct the normalized energy sequence

```text
E_n = (mu_n-pi^2*n^2)/(1+n).
```

Its linear part is a bounded Hilbert multiplier. The quadratic part is
first constructed in ell1 by Holder multiplication and then continuously
included in ell2. Thus the map is analytic in the Hilbert norm, not only
coordinatewise. `GlobalDirichletCoordinates.lean` uses Banach-valued
real-form uniqueness to glue these local maps on one complex-open
neighborhood of the entire real H^-1 space. Every globally recovered
scalar branch remains an actual Dirichlet zero on that same domain.
The real coordinates are exactly the actual canonical labels with the
stated normalization, and the entire sequence vanishes at the free
potential. The logarithmic norming sequence, full Cartesian coordinates,
analytic inverse realization and symplectic/action identities remain.

The newly traversed inherited import closure contains 1184 source
modules outside the preceding focused baseline, all byte-identical to
the read-only compiled reference. Its hashes and direct roots are in
`dirichlet-coordinate-library-reuse.json`. Those inherited modules were
not rebuilt in this incremental check. The cumulative audit covers the
actually used transitive axioms and all direct library-root declarations.

## Global analytic logarithmic Dirichlet norming sequence

`L2QuasiHillNormingGauge.lean` identifies the actual terminal NLS
Dirichlet eigenfunction factor with the normalized rough Hill
quasi-derivative. Determinant one gives the literal anti-discriminant
identity `Delta_minus(nu_n)=gamma_n-gamma_n^-1`.
`HillHminusOneDirichletAntiNorming.lean` transports it to every positive
actual Hill label with the exact Miura energy shift. The signed half
sample equals `sinh(kappa_n)` for the intrinsic norming logarithm
`kappa_n=log((-1)^n Re(gamma_n))`. No open-gap or simple-root hypothesis
is added.

`RealArsinhExtension.lean` constructs the principal complex inverse sinh,
proves agreement with real inverse sinh and analyticity at every real
scalar, and supplies a linear bound near zero.
`AnalyticSuperposition.lean` proves the reusable finite-exponent lp
superposition theorem: exact finite-head coordinates and a common small
tail neighborhood give actual sequence membership, local norm bounds
and Banach analyticity. `ArsinhSuperposition.lean` specializes it near
every real lp sequence and provides analytic parameter pullback.

`SourceDirichletAntiSamplesAnalytic.lean` assembles the actual NLS
Dirichlet anti-discriminant sample sequence as one Banach analytic map
on a common neighborhood of all real sources, using the existing
Lemma 9.2 full sequence bounds. `LogNormingSequenceCoordinates.lean`
uses signed injective positive-index sampling and inverse-sinh
superposition. `GlobalLogNormingCoordinates.lean` glues the resulting
ell2 maps by Banach-valued real-form uniqueness. It proves one
complex-open neighborhood of the entire real H^-1 space supports an
analytic map `K` with **every** real coordinate equal to the actual
intrinsic logarithmic norming constant and `K(0)=0`.

The normalized Dirichlet energies and logarithmic norming sequences
are therefore both globally Banach analytic near all real H^-1 inputs.
The full Cartesian KdV coordinate map, its analytic inverse, quadratic
Arnold-action identification and action-fiber/discriminant identity
remain essential inputs to the positive-ell2 extension of Theorem 1.1.

The inherited closure for this milestone contains 2297 sources outside
the 499-module baseline, all byte-identical to the read-only compiled
reference. These cached imports were not rebuilt; their hashes are in
`log-norming-library-reuse.json`. The pinned mathlib Arsinh source was
additionally compiled into private output. The reproduction script
mirrors mathlib imports with read-only file links and refuses writes
through linked output directories. All canonical sources and build
products remain untouched.

## Intrinsic H1 graph analyticity and Dirichlet energy differentials

`IntervalCurveL2.lean` constructs joint bounded multiplication of a
continuous curve with an actual physical L2 class. The position derivative
of the rough Hill IVP is the actual class `u*y+w`.
`L2QuasiHillDerivativeClass.lean` proves it jointly analytic;
`HillHminusOneDirichletH1Analytic.lean` identifies it with the derivative
of the intrinsic normalized scalar column in every Miura chart. The full
continuous/L2 **H1 graph** is jointly entire in complex energy and the
original complex H^-1 potential, independently of all chart choices.

`PeriodOneMassPhysical.lean` realizes the Fourier operator
`m+1+2*pi*i*k` as the actual physical derivative plus mass on H1 inputs.
`HillHminusOneMassPotentialPairing.lean` proves, for matching-endpoint
H1 products, the literal resolvent formula

```text
q=(d/dx+m+1)U  =>  <q,g>=integral U*((m+1)*g-gprime).
```

Physical integration by parts and density in the original H^-1 norm
remove the Riccati lift. `IntervalH1ProductGraph.lean` gives polynomial
product and derivative formulas on the H1 graph. Together these make
the potential pairing jointly analytic in the graph variables actually
used by the spectral solutions.

`HillHminusOneDirichletPerturbation.lean` proves the intrinsic identity
for arbitrary complex potentials and actual Dirichlet roots:

```text
(mu-lambda)*integral Y(q,lambda)*Y(p,mu)
  = <p-q,Y(q,lambda)*Y(p,mu)>.
```

No common Miura chart or open-gap hypothesis is needed. Differentiating
this identity in `HillHminusOneDirichletDifferential.lean` gives the full
complex H^-1 Frechet differential of every analytic root branch:

```text
da(q)[h]*integral Y(q,a(q))^2 = <h,Y(q,a(q))^2>.
```

At every real input the actual unconjugated square mass is nonzero.
Every actual positive label therefore has the quotient formula,
including central modes and collapsed gaps.
`DirichletCoordinateDifferential.lean` proves the exact differential
of the already constructed global analytic ell2 energy map:

```text
dE_n(q)[h] = <h,Y_n(q)^2>/((1+n)*integral Y_n(q)^2).
```

The coordinate weight is retained exactly. These are actual spectral
Banach derivatives. Explicit free Fourier linearization, the full
Cartesian inverse, canonical action identities and the positive-ell2
extension of Theorem 1.1 remain unproved. The inherited import closure
contains 2294 sources outside the 507-module baseline, all byte-identical
to the read-only compiled reference; hashes and scope are recorded in
`dirichlet-differential-library-reuse.json`. Those cached imports were
not rebuilt in this incremental validation.

## Exact free Fourier linearization of the actual Dirichlet energies

`L2QuasiHillFreeSolution.lean` identifies the actual zero-profile rough
IVP with the ordinary classical free Hill IVP, for every complex energy
and initial state. `HillHminusOneFreeDirichletColumn.lean` uses weak
reconstruction and the endpoint test to identify the intrinsic free
column. This does not assume that the selected Miura chart has zero
lift or zero energy shift at zero potential. The exact result is
`Y(0,z^2)(x)=sin(z*x)/z` for nonzero complex frequency.

`SineSquarePairing.lean` proves the literal unit-interval Fourier
sine-square pairing with both signed frequencies. The free column mass
is exactly `1/(2*(n*pi)^2)`. The potential pairing in
`HillHminusOneFreeDirichletPairing.lean` equals
`(2*h_0-h_n-h_-n)/(4*(n*pi)^2)`, first by the actual L2 integral and
then by density in the original complex H^-1 norm.

`HillHminusOneFreeDirichletDifferential.lean` consequently proves

```text
dmu_n(0)[h] = h_0-(h_n+h_-n)/2.
```

This is the full complex Banach derivative, for all H^-1 directions.
For real mean-zero directions it is exactly `-Re(h_n)`.
`FreeDirichletLinearization.lean` constructs a bounded H^-1-to-ell2
operator using the exact Sobolev weight, positive-index sampling,
reflection and the rank-one mean term. Its coordinates are

```text
L(h)_n = (h_0-(h_n+h_-n)/2)/(1+n).
```

The actual global analytic normalized Dirichlet energy map has this
**entire bounded operator** as its derivative at zero. No finite-mode
restriction or unproved passage from modewise derivatives is used.
The following milestone proves the corresponding logarithmic norming
derivative and combined mean-zero local inverse. Global Cartesian KdV
coordinates and action identities remain required for Theorem 1.1. The inherited import closure contains 2294
byte-identical cached sources outside the 516-module baseline; these
were not rebuilt. Its hashes and audit scope are recorded in
`free-dirichlet-linearization-library-reuse.json`.

## Actual logarithmic norming derivative and local Dirichlet inverse

`HillHminusOneNormingPerturbation.lean` proves an exact Green identity
for the actual terminal quasimomentum at complex Dirichlet roots.
The free cosine test, literal sine-cosine Fourier integral and H^-1
density determine its derivative without an open-gap assumption.
Real-form uniqueness of analytic germs identifies the logarithm of
this momentum with the previously constructed actual norming extension.
`HillHminusOneFreeLogNormingDifferential.lean` proves, at every positive
index and for every complex H^-1 direction,

```text
dkappa_n(0)[h] = (h_-n-h_n)/(4*i*n*pi).
```

`FreeLogNormingLinearization.lean` identifies the entire bounded
H^-1-to-ell2 derivative of the actual global norming map. Together with
the normalized energy derivative, it gives the continuous linear
equivalence `freeDirichletFourierEquiv` on the closed mean-zero H^-1
subspace. Its bounded inverse reconstructs the literal Fourier modes:

```text
h_n  = -(1+n)*E_n-2*i*pi*n*K_n
h_-n = -(1+n)*E_n+2*i*pi*n*K_n
h_0  = 0.
```

Both inverse identities hold for the full Hilbert spaces. The reusable
`AnalyticEquivDerivativeInverse.lean` transports the analytic inverse
function theorem between different Banach spaces and supplies open
source and image sets with exact inverse identities.

`DirichletLocalInverse.lean` constructs `DirichletHilbertCoordinates`
from the actual global energy and norming extensions on one common
complex open neighborhood of the entire real H^-1 space. All canonical
real recovery formulas, actual complex Dirichlet root identities, zero
normalizations and free derivatives are retained. On the mean-zero
subspace the paired map has a two-sided complex analytic inverse on
open neighborhoods of zero. The endpoint is
`exists_actual_Dirichlet_local_analytic_inverse`.

This proves a local Dirichlet spectral inverse. The global Cartesian
KdV coordinate realization near all real normalized Hilbert pairs,
symplecticity, quadratic Arnold action identities and action-fiber
discriminant uniqueness remain required for the positive-ell2 extension
in Theorem 1.1. The inherited import closure contains 2297 byte-identical
cached sources outside the 522-module baseline; these were not rebuilt.
See `dirichlet-local-inverse-library-reuse.json` for hashes and audit scope.

## The actual spectral Jacobian at every real H^-1 potential

`HillHminusOneNormingVariation.lean` replaces the free cosine test with
the actual cosine solution at an arbitrary base potential. Its exact
two-potential Green identity holds at every complex Dirichlet root.
At the base root it also proves that the cosine terminal value times
the Dirichlet terminal momentum is exactly one.

`HillHminusOneNormingDifferential.lean` differentiates that identity in
the original complex H^-1 norm, using the proved analytic H1 graph and
mass-resolvent pairing. The energy-overlap term is retained at arbitrary
base potentials. `HillHminusOneLogNormingDifferential.lean` identifies
any actual analytic norming extension with the signed terminal logarithm
as a complex germ at every real potential.

`HillHminusOneDirichletJacobian.lean` constructs actual bounded
complex-linear energy and logarithmic norming functionals. If `Y_n`
is the normalized Dirichlet column, `C_n` the cosine column in any
Miura chart, `P_h` the intrinsic potential pairing and `M_n=integral Y_n^2`,
then `M_n` is nonzero and

```text
dmu_n(q)[h]    = P_h(Y_n,Y_n)/M_n
dkappa_n(q)[h] = P_h(Y_n,C_n)-integral(Y_n*C_n)*dmu_n(q)[h].
```

The corrected norming functional is independent of the chosen Miura
chart. These are full complex Frechet derivatives for every H^-1
direction, at every real potential and positive index, including all
closed gaps. They do not require finite Fourier support.

`DirichletHilbertJacobian.lean` constructs the full bounded derivative
of the actual energy/norming map into `ell2 x ell2`. This operator-valued
map is Banach analytic on the same complex open neighborhood of the
entire real potential space. At every real potential its coordinate
operators are exactly `dmu_n/(1+n)` and `dkappa_n`. Its restriction to
the mean-zero phase space is the derivative of the actual restricted
map; at zero it equals the previously proved Fourier equivalence.

Invertibility of the mean-zero Jacobian at every real potential remains
open. The present result supplies its exact operator and coordinate
formulas; it does not assert the global inverse, Cartesian KdV
coordinates, symplectic/action identities or Theorem 1.1. The inherited
2297-source import closure outside the 534-module baseline is byte
identical to the read-only compiled reference and was not rebuilt.
See `dirichlet-hilbert-jacobian-library-reuse.json` for hashes and scope.

## Full original physical Hill spectrum at every complex H^-1 potential

Seventy-one shared source modules are copied exactly from
`kdv-pseudomeasures` commit `96091c0` and strictly rechecked in this
private checkout. They construct the original physical singular Hill
operator on its full H1 domain, its dense closed graph in H^-1, compact
resolvent, physical algebraic root spaces and finite spectral projections.
Three existing focused dependencies retain their already validated
versions; no existing source was overwritten. The imported sources all
compile against these retained public interfaces.

`PeriodOneHminusOneDoubling.lean` and
`HillHminusOneSingularPotential.lean` construct the exact source adapter:
`Q_hat(2*n)=q_hat(n)`, with all odd coefficients zero. Both source norms
are compared explicitly as `norm(Q)<=norm(q)<=2*norm(Q)`. Real Fourier
inputs give physically real distributions. No additional regularity,
mean-zero or endpoint-space membership is imposed.

`ClosedZeroGraphPersistence.lean` passes characteristic zeros under dense
parameter approximation into a jointly closed spectral graph, including
multiple zeros. `SingularHillDenseSpectrum.lean` proves the reverse
spectral persistence using arbitrarily small physical resolvent circles
and nonzero finite Riesz projection ranks. These operator ranks persist
in the full original H^-1 norm, independently of an assumed scalar
characteristic determinant.

`HillHminusOnePhysicalSpectrum.lean` proves for **every complex H^-1
potential and every complex energy**, including zero,

```text
lambda in spectrum(L(Q))  iff  Delta_Hminus(q,lambda)^2-4=0
                         iff  an actual nonzero original H1 eigenvector exists.
```

The first equivalence is the complete original physical spectrum, not a
high-frequency or finite-mode criterion. The actual resolvent is exactly
the complement of this characteristic zero set. All real input spectra
are real. `HillHminusOnePhysicalLabels.lean` identifies the canonical real
labels with this entire physical spectrum as a set, supplies an original
H1 eigenvector at every label, proves physical minimality of the lowest
label and transports semisimplicity of real physical root spaces.

The following milestone identifies the **physical algebraic multiplicities**
with those scalar analytic zero orders at every real potential. A self-adjoint L2
realization is not inferred from closedness of the H^-1 operator. The
Cartesian KdV global inverse, action identities and main Theorems 1.1-1.3
also remain open. `physical-spectrum-library-reuse.json` records the
71 exact rechecked source hashes and the 2323 remaining byte-identical
cached dependencies, which were not rebuilt.

## Actual physical algebraic multiplicities at every real H^-1 potential

`SingularHillMovingProjection.lean` proves bounded-operator norm
continuity of the original Riesz projection when potential, circle
center and radius all move continuously. The angular integral stays in
the original H^-1 operator norm. The original H1 domain is unchanged.

`SingularHillFreeMultiplicity.lean` identifies the free effective
determinant exactly as `(lambda-pi^2*n^2)^2` and proves actual original
algebraic multiplicity two at every positive free level.
`SingularHillFreeGround.lean` identifies the entire original ground
eigenspace with the complex constants and proves multiplicity one.

The canonical gap centers and collars are continuous through closed
gaps. `HillHminusOnePhysicalGapProjection.lean` follows these physical
circles along the literal real potential path `t*q`. Finite projection
rank stability makes their ranks constant on `[0,1]`.
`HillHminusOnePhysicalGapRange.lean` identifies the range as the supremum
of the two actual endpoint root spaces and proves its dimension is two
at every positive gap. Independent nonzero endpoint spaces therefore
have dimensions one and one when the gap is open; a closed gap has one
actual root space of dimension two. A separate continuously moving
ground circle retains the one-dimensional free ground range.

`HillHminusOnePhysicalMultiplicity.lean` proves the full identity

```text
physicalAlgebraicMultiplicity(L(Q),lambda)
  = analyticOrderNatAt(Delta_Hminus(q,.)^2-4,lambda)
```

for every **real** unit-period H^-1 potential and **every complex**
energy. The original full H1 operator domain and full algebraic root
chain definition are retained. Ground, zero energy, all low/open/closed
gaps, nonreal energies and nonspectral values are included. There is no
extra mean-zero, finite-support, smoothness or simplicity hypothesis.
The canonical real label fiber counts are now exactly the actual
physical algebraic multiplicities, not only scalar characteristic orders.

No multiplicity equality for nonreal potentials or self-adjoint L2
realization is inferred. Global Cartesian KdV inversion/action identities
and Theorems 1.1-1.3 remain open. The inherited 2323-source import closure
matches the read-only reference and was not rebuilt; its hashes are in
`physical-multiplicity-library-reuse.json`.

The shared frequencies branch was also re-inspected at `6921d8d`.
Its actual global rough forward data are constructed; global real
mean-zero injectivity and real-preserving local inverses at every rough
real base are proved. Those source declarations are pinned as subsequent
reuse candidates, not imported or counted as validated here. Global
rough surjectivity remains explicitly open on that branch too.

## Critical normalized Miura factors and the original Hill actions

The shared frequencies development is pinned at `c44c9e8`. Its actual
normalized factor exists at the intrinsic ground energy for every real
mean-zero H^-1 potential. The central Dirac gap is exactly closed at zero.
Fifty-two sources are reused exactly and one real-form module is adapted
by renaming its two local part definitions to avoid an existing interface
collision. The affected dependency chain is rechecked privately.

`HillMiuraCriticalFrequencies.lean` proves the nonnegative frequency
list has exactly one zero slot and strictly positive remaining slots.
`HillMiuraCriticalSpectrum.lean` proves the full squared list has exactly
the actual Hill characteristic multiplicities. Away from zero the square
map is unramified; at zero the actual Hill ground root is simple.
`HillMiuraCriticalLabels.lean` therefore identifies every canonical Hill
endpoint with its actual squared Dirac endpoint at the critical factor,
including all repeated closed gaps. No outside-spectrum shift is used.

`HillMiuraCriticalActions.lean` identifies the literal arcosh profiles and
changes variables by `E=x^2-e` in the real gap integral. For every actual
real mean-zero L2 factor with `Miura(u)=q+e` and every positive index,

```text
I_n^Hill(q) = 2 * J_(n,1)^Dirac(u).
```

This includes non-L2 rough Hill potentials and all collapsed gaps.
`HillMiuraSignedActions.lean` proves the first weighted Dirac actions are
odd under index reflection. `SignedFiniteSum.lean` combines a symmetric
signed sum into twice its positive part. Consequently
`HillMiuraCriticalEnergyBound.lean` proves

```text
norm(u)^2 <= sum_(n in s) I_n^Hill(q)/(pi*n)
```

for a finite set of positive indices whenever the actual Dirac source
is spectrally finite-gap. At a normalized factor with `norm(u)^2=e`, the
same bound holds for `-lambda_0(q)`. Spectral finite-gap is not a finite
Fourier support hypothesis.

Approximation/continuity extending this estimate to rough limits,
compactness/no-loss reconstruction and global rough-coordinate
surjectivity remain open. This is a verified input toward the global
positive-ell2 extension, not a completion of Theorem 1.1. The weighted
Dirac action identity here does not yet identify quadratic Cartesian
coordinate actions or prove the action-fiber/discriminant identity.
All main theorems remain open. The reuse manifest records all new source
hashes and the 2333 inherited byte-identical reference imports.

## Global rough coercivity in the actual Arnold-action norm

The constructed shared global rough forward data, real-preserving local
weak inverses at every real base and global real mean-zero injectivity
are imported at `540f131`. Their global ground-energy and source bounds
are proved by actual local inverse target truncations and strong H^-1
approximation; no spectral finite-gap or initial source bound remains.
The private integration checks 1469 exact shared sources and 34 explicit
interface adaptations while retaining all 685 baseline proof sources.
Every adaptation is recorded in `global-ground-library-reuse.json`.

`HillHminusPhysicalArnoldActions.lean` identifies the original physical
real gap integrals with the intrinsic rough contour moments at every
positive index and every polynomial moment level.
`HillHminusPhysicalSourceDensity.lean` constructs the literal physical
representative of each real unit-period L2 input and proves those
original physical sources are dense in real H^-1.

`GlobalArnoldCalibration.lean` uses this density and actual continuity to
prove, at **every real H^-1 source**, including non-L2 inputs and closed gaps,

```text
I_n(q) = (1+n)*norm(D.positive(q)_n)^2.
norm(I(q))_ell^(-1,1) = norm(D.positive(q))_ell2^2.
```

`PositiveActionNorm.lean` retains exactly the base weight `1/(1+n)`;
positive coordinates are reindexed without dropping or rescaling terms.
`GlobalArnoldCoercivity.lean` therefore proves, at **every real mean-zero
H^-1 potential**, with no size or finite-gap premise,

```text
-lambda_0(q) <= E,             E=(2/pi)*norm(I(q))_ell^(-1,1),
norm(q)_Hminus1 <= A*sqrt(E)+B*E.
```

Here `A=norm(periodOneMassOperator 0)+norm(periodOneL2Inclusion)` and
`B=norm(periodOneMiuraProduct)+norm(periodOneL2Inclusion)` are fixed
universal operator constants. The actual analytic weighted Arnold map
exists near all real rough potentials with these estimates. These are
bounds in the original spectral action norm, not assumed coordinate
bounds or an inverse map supplied as a premise.

`SourceHigherActionCoefficientContinuity.lean` additionally proves that
every original real higher Dirac action, at every fixed signed index
and every level, is continuous under bounded coefficientwise limits of
real L2 pairs. A real-centered isolating circle persists along the
actual real interpolation segments. Polynomial weights preserve uniform
contour convergence; all closed-gap cases are included.

These estimates and continuity results are inputs toward realizing the
whole positive action cone and proving analytic action descent. They do
not establish norm compactness, properness, global Cartesian inversion
or the action-fiber/discriminant identity. The unconditional positive
ell2 extension and all main Theorems 1.1-1.3 remain open. The subsequent
action-cone realization milestone below removes the onto obligation.

## Actual realization of the whole nonnegative action cone

`GlobalArnoldSurjectivity.lean` proves that **every nonnegative element of
weighted ell^(-1,1)** is the actual full Hill action sequence of a real
mean-zero H^-1 source. In particular every point of the positive ell2
quadrant is realized, including zero coordinates and its entire boundary.
There is no smallness, strict positivity or finite-support hypothesis.
The actual analytic Arnold map near all real sources is onto this cone.

`HillFiniteActionRealization.lean` uses the actual original global L2
Birkhoff inverse to realize every finite nonnegative action prescription.
`FiniteArnoldRealization.lean` realizes each literal finite head of a
weighted action sequence without changing its raw action normalization.
The ground-energy estimate bounds actual real mean-zero L2 Miura factors
of those sources. `HillActionCoefficientLimits.lean` extracts a
coefficientwise factor limit in L2 and reconstructs the actual rough
Hill source by subtracting its exact zero-mode energy. Continuity of the
original higher Dirac actions and the Hill=2*Dirac level-1 identity recover
every prescribed action. No strong convergence or norm conservation of
the factors is assumed.

`HillConstantActionCurves.lean` also proves that every differentiable real
mean-zero original L2 curve preserving all Hill actions has constant
full discriminant, at every complex energy. This gives the stationarity
step toward the action-fiber identity; existence of suitable curves
between all equal-action sources remains to be proved.

This removes the action-cone realization obligation. Equal-action
invariance of the discriminant and analytic descent/gluing are still
needed for the global analytic extension in Theorem 1.1. This result does
not assert global Cartesian-coordinate surjectivity. All main Theorems
1.1-1.3 remain open.

## Full rough action-fiber invariance of the discriminant

`GlobalArnoldActionFibers.lean` proves that **equal intrinsic Arnold
periods determine the entire Hill discriminant at every real mean-zero
H^-1 source**. There is no L2, finite-gap, smallness or open-gap premise.
The actual analytic weighted Arnold map therefore has the required
full-discriminant action-fiber identity on its real mean-zero domain.

`HillOriginalSequenceActions.lean` checks the exact target normalization
`norm(Z_k)^2=4*pi*(k+1)*I_(k+1)`. Smooth one-coordinate phase rotations
lift through the constructed original global physical L2 inverse.
`HillOriginalActionFibers.lean` applies the proved constant-action curve
stationarity. `ModulusFiberInvariance.lean` and
`SingleCoordinatePhase.lean` extend the finite replacements to every
full infinite-dimensional equal-modulus fiber by norm convergence.

`HillRoughActionApproximation.lean` constructs actual original mean-zero
L2 source approximants converging strongly in H^-1. Their SAME global
signed coordinates are literal symmetric finite truncations, preserving
every retained positive phase and normalization.
`HillRoughActionFibers.lean` compares common truncations of two sources
with equal positive moduli using the full physical L2 identity, then
passes the entire discriminant to the strong rough source limits. The
actual global Arnold calibration yields the intrinsic action statement.

Together with action-cone realization, this removes the spectral-fiber
invariance obligation. The analytic local action charts and common-domain
gluing still have to be constructed. Full rough Cartesian surjectivity
is not asserted, and all main Theorems 1.1-1.3 remain open.

## Unconditional global analytic actual contour extension

`UnconditionalContourExtension.lean` now proves
`exists_global_analytic_actual_contour_extension` with **no unproved
spectral-coordinate realization as an input**. One complex open subset
of the original weighted ell^(-1,1) action space contains the entire
nonnegative cone. Every actual cubic Hill moment has an analytic factor
there, recovering the intrinsic cubic moment of **every real mean-zero
H^-1 source** from its actual full Arnold sequence. The locally uniform
bounds `|8*n*pi*R_n|<=C*|I_n|^2` survive on the same action domain.

Pulling this domain back through the proved continuous raw-action
inclusion constructs **one complex open neighborhood of the entire
positive ell2 quadrant**, including all boundary points. The literal
series `sum_n 8*n*pi*R_n` is analytic there, and its terms are norm
summable at every point of that neighborhood. It vanishes at zero and
is real and nonpositive on the whole positive quadrant. On the weighted
nonnegative cone, each cubic factor vanishes exactly when its raw action
coordinate vanishes.

The construction uses actual local rough inverse potentials in normalized
complex Hilbert pairs. `PositiveReindex.lean` and
`SignedHilbertPairs.lean` check the bounded maps and exact `1/sqrt(2)`
normalization, with a constructed right inverse and preservation of the
physical real form. `HillRoughPairInverse.lean` constructs the local
analytic potential at every real mean-zero rough base.
`LocalSpectralPairCharts.lean` proves its literal quadratic Arnold-action
identity. `LocalCubicPairCharts.lean` transfers the actual globally
constructed potential-space moments and their uniform complex tail
bounds to one common pair chart, before choosing the gap index.

`LocalAtlasActionFamilyDescent.lean` descends and glues independent local
real coordinate germs over the whole cone. `ArnoldConeMomentGerms.lean`
constructs these germs from actual source realization and the proved
full rough action-fiber/discriminant identity. `ScalarFamilyTransport.lean`,
`ActionMomentNormalization.lean` and `GlobalActionMomentDescent.lean`
transport the family back through the original weighting and recover
every actual real source value. Default kernel limits are retained;
large proofs are factored into reusable lemmas rather than increasing
heartbeat limits or disabling linters. Full rough Cartesian
surjectivity is neither assumed nor asserted.

This proves the **actual analytic contour-extension step** toward
Theorem 1.1. The contour sum has not yet been identified with the physical
renormalized KdV Hamiltonian. The physical frequency identity and the
Taylor coefficient `-6*Id` also remain open. Consequently no main
Theorem 1.1-1.3 is marked complete.

## Constructed finite-gap physical phase and energy coefficient

`SourceFiniteGapDiscriminantPhase.lean` constructs the normalized analytic
inversion phase of every real finite-gap Dirac source from the actual
Abelian primitive. `AnalyticPhaseEnergyShift.lean` constructs its exact
transport under a constant energy translation. Combined with the actual
ground Miura factor, `HillHminusFiniteGapDiscriminantPhase.lean` gives an
analytic inversion phase for every real mean-zero rough Hill source with
eventually closed gaps, without assuming a phase or an expansion.

For smooth physical sources, `ClassicalHillPhaseCoefficients.lean` and
`HillFiniteGapPhysicalPhase.lean` identify its first five Taylor
coefficients with the independently defined physical integrals:
`A(w)=i*H0*w^3/4+i*Hkdv*w^5/16+O(w^6)`. The actual integral definitions
are `H0=integral(q^2)/2` and `Hkdv=integral((q_prime)^2/2+q^3)`.
`QuarticInversionRemainder.lean` proves the exact expansion
`(-i*z+A(1/z))^4=z^4-H0-Hkdv/(4*z^2)+z^(-3)*B(1/z)`, with `B`
analytic at zero. `QuarticInversionContour.lean` extracts the exact
weighted frequency-circle period `-pi*i*Hkdv`. The unconditional actual
smooth finite-gap factory is
`NLS.KdV.exists_hill_finiteGap_physical_energy_contour`.

This coefficient belongs to the constructed actual discriminant phase.
Matching that phase to the globally normalized source primitive, changing
to the original energy circle, instantiating finite-gap contour
decomposition, and passing the physical identity by density remain open.
No physical Hstar identity, physical frequency identity or `-6*Id`
coefficient is asserted. All main theorem flags remain false.

## Remaining essential KdV work

1. Identify the actual analytic contour sum with physical renormalized
   KdV energy. The finite-gap contour decomposition is checked, but the
   constructed phase must be matched to the normalized source primitive
   and original energy-circle quartic period. Then instantiate the gap
   decomposition and pass the physical identity by density.
2. Identify its bilinear Hilbert gradient with the physical frequencies
   minus `8*pi^3*n^3` on the full common domain.
3. Prove the exact quadratic Taylor coefficients giving `-6*Id`, finish
   the original positive-index local inverse and single-radius Hessian
   statement, and complete main Theorems 1.1-1.3.

The `kdv-estimates` branch was re-inspected through commit `05e5530`.
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
The intrinsic real L2 labels, their continuity and trace parity are now
included as prerequisites of the physical L2 half-plane sign theorem in
the 24-module import slice above. Canonical gap-tail modules remain
available on that branch. The intrinsic H^-1 labels and their continuity, finite real contour
construction and all-index energy-analytic filled squares are now proved
in this branch. Joint complex-potential central periods and the global
Birkhoff construction remain open.
No separate messages were sent to other article chats.

## New shared foundations inspected on 2026-11-06

The read-only `kdv-estimates` branch at `25e906b` now contains the
actual physical mean-zero L2 global inverse and both analytic directions
in `HillOriginalGlobalInverse.lean`. This is a genuine L2 result; the
global H^-1 inverse required here is not inferred from it.
`kdv-pseudomeasures` at `96091c0` supplies the full original singular
H^-1 Hill operator spectrum and algebraic multiplicities, while
`kdv-kdv2-frequencies` at `9d96f3c` supplies an actual rough signed
Abelian local inverse preserving the physical real form at zero.

These sources were initially inspected and pinned as reuse candidates.
The singular Hill operator foundations at `96091c0` are now integrated
as 71 exact, strictly rechecked shared sources with the full H^-1
potential/discriminant bridge proved above. The newer L2 global inverse
and rough signed Abelian local inverse remain candidates for subsequent
integration. Their original inspection identifiers are retained in the
Jacobian progress object in `source-inventory.json` and `validation.json`.

## Validation and worktree

The dedicated ordinary Git worktree is
`/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-kdv-convexity/work/checkouts/diss-lean`,
branch `articles/kdv-convexity`, based at
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. Managed creation was rejected
because the canonical sourceRoot is not a registered folder in this chat;
the ordinary-worktree fallback was explicitly authorized.

The validated baseline at `fc9460c` contains 2217 proof sources, whose
hashes remain unchanged. Seven exact shared sources and eight authored
modules pass strict Lean compilation with `warningAsError=true`. Authored
proofs retain default limits and linters. Reproduction lists 2232 modules.
The positive-index example, combined transitive axiom audit and 1594
coverage declaration checks pass. All 2825 remaining reference import
sources match the read-only compiled reference byte-for-byte and were not
rebuilt. Earlier build receipts remain in the parent commit. This is
incremental validation, not a full repository rebuild.

`CheckAxioms.lean` imports all article and new shared KdV modules and audits
their namespaces, including generated declarations, plus explicit shared
helpers and all declarations originating in 768 additional shared modules:
17242 declarations in total, transitively. Only `propext`,
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
`ComplexAnalysis`, `FunctionalAnalysis`, `SequenceSpaces`, `Fourier`,
`DifferentialPolynomial` and `MKdV` outputs use
real private directories; reference files in
the shared namespaces are linked only for imports, and an output-file link is removed
before compilation. No full repository validation
is claimed, and the dissertation's existing record is unchanged. Shared
main integration and aggregate imports remain sequential; serialize any
future expensive full validations with `/tmp/diss-lean-article-build.lock`.
