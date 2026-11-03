# Validated article progress

## 2026-11-02 — isolated worktree and first proof checkpoint

Branch: `articles/mkdv-nls-hierarchies`.
Worktree: `/home/janbernloehr/Documents/Codex/2026-11-02/diss-lean-mkdv-nls-hierarchies/outputs/dnls`.
Base: `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`.
The app-managed worktree tools rejected the unregistered canonical source and
the unmanaged Git checkout. The separate standard Git worktree is used by
explicit path. Canonical main has not been switched or edited.

Commit `9b664f9` was pushed to the article branch. It integrates the 22 public
declarations from the private first phase, with 15 checked theorems. Focused
compilation in this worktree and the transitive axiom audit of 35 declarations
and generated auxiliaries both passed.

## 2026-11-02 — physical smooth m=2 theorem

Commit `09fa657`, pushed to the article branch, adds the physical fourth-flow identification:

- `classicalNLSHamiltonian_four` derives the article's S4 integral directly
  from the existing Riccati Hamiltonian, retaining its sign and constants.
- `hasDerivAt_classicalNLSHamiltonian_four_fst` and `_snd` certify both
  component gradients by the actual complex first variations of S4 on smooth
  periodic inputs.
- `hasDerivAt_classicalMKdVEnergy` certifies the gradient
  `-u''+2*u^3` of the independently specified physical K2 integral.
- `deriv_classicalMKdVEnergyGradient` identifies its Gardner field with
  `-u'''+6*u^2*u'`.
- `theorem1_m2_smooth` proves both clauses of Theorem 1 at m=2 on smooth
  complex period-one potentials: S4 vanishes on the diagonal, and its physical
  NLS vector field is the pair of physical mKdV vector fields.

The complex case includes the real and purely imaginary reductions without
changing the physical Hamiltonian definitions. This result does not claim the
full H2 extension, higher orders, the frequency theorem, or the mKdV Birkhoff
identification. The source matrix/sign/mean qualifications in the source
inventory remain open for the full main theorems.

All eight article modules pass the focused checker with Lean 4.33.1,
`autoImplicit=false` and warnings as errors. The expanded transitive axiom
audit passes for 55 declarations and generated auxiliaries, allowing only
`propext`, `Classical.choice` and `Quot.sound`. The check uses read-only compiled
imports from the pinned canonical checkout; all writable artifacts are local
to this worktree. It is not a fresh full dependency build.

An aggregate/full-library audit was requested, but the shared full-validation
lock was held by another process. That waiting command was cancelled; no
validation is left running from it. Aggregate imports remain an explicit
sequential main-integration step. The focused proof and transitive-axiom checks
above completed independently of the full-build lock.

Next required mathematics: all-order physical variational recurrence;
sharp even-order Sobolev extensions; actual ZS/Miura/Hill spectral and action
identifications; and the mKdV coordinate/frequency/bracket comparison.

## 2026-11-02 — actual Miura solution and Floquet boundary transfer

`MiuraClassicalSolution.lean` applies the first-order factorization to the
existing constructed `classicalSolution`. Its scalar combination f1+i*f2 has
second derivative `(u'+u^2-z^2)*(f1+i*f2)` at each interior point where u is
differentiable. Thus it satisfies exactly the scalar Miura equation underlying
Lemma 2 (p. 10), using the actual ZS solution rather than an assumed spectral
identification. The potential identity on the closed unit interval and the
pointwise differentiability assumption remain explicit.

`MiuraBoundaryTransfer.lean` proves that the linear state map from the original
solution vector to scalar position and derivative is injective for z!=0.
When u(1)=u(0), an arbitrary complex Floquet multiplier satisfies the original
ZS boundary condition if and only if it satisfies the transformed scalar-state
boundary condition. The z=0 case is deliberately not included in this assertion.

These results are inputs to the independent Hill IVP and discriminant
comparison. They do not define the Hill discriminant using ZS data, and no
equality of independently constructed spectral actions is claimed yet.
No competing Hill-operator foundation was introduced.

All ten article modules now pass the focused checker. The expanded transitive
axiom audit passes for 72 declarations and generated auxiliaries, with the same
three allowed classical axioms. There are 50 public declarations: 35 theorems
and 15 definitions. Main-theorem completion, the independent Hill comparison
and the full repository rebuild remain pending.

## 2026-11-02 — independent physical H¹ Hill discriminant identity

Commit `9614f05` adds the shared bounded complex-linear Volterra initial-value
map and the general intertwining/trace theorem. These generic results are in
`NLS/FunctionalAnalysis/LinearVolterraFlow.lean`; the exact ZS trace adapter is
in `NLS/ZakharovShabat/ClassicalVolterraTrace.lean`.

The independent scalar Hill construction starts from the quasi-derivative
system `g'=u*g+w`, `w'=-mu*g-u*w`. This continuous-coefficient IVP uses no ZS
data. A constant intertwiner with the diagonal ZS equation gives its trace
identity away from zero, and independent analyticity extends the identity to
the zero spectral parameter.

The physical justification is also proved. For absolutely continuous u, every
scalar column and its actual derivative are absolutely continuous and satisfy
`-g''+(u'+u²)*g=mu*g` almost everywhere. Conversely any scalar solution in this
physical class with the given initial position and derivative equals the
constructed column. `PhysicalHillDiscriminant.lean` normalizes the independent
columns by `(g(0),g'(0))=(1,0)` and `(0,1)`, then defines the discriminant by
the literal endpoint diagonal sum. Matching endpoint values of u prove its
trace agrees with the quasi-derivative trace.

For every original complex period-one H¹ source these conditions are supplied
by the existing Fourier representative and absolute-continuity theorems.
`NLS.Articles.MKdVNLSHierarchies.theorem5_discriminant_identity` consequently
proves the paper's Theorem 5, including the squared spectral parameter and
zero. `hill_column_spec` records the physical equation, regularity and initial
normalization as constructed facts. No essential identification is passed in
as a hypothesis.

All 19 article modules and the aggregate compiled against the pinned read-only
dependencies. The article transitive axiom audit passed for 141 declarations
and auxiliaries. A combined audit importing the full aggregate and all article
modules passed for 45,386 NLS declarations, with only `propext`,
`Classical.choice` and `Quot.sound` allowed. The expensive validation ran under
the shared build lock; all writable outputs stayed in this worktree. This used
the existing pinned compiled dependency cache, rather than rebuilding that
entire dependency tree from source.

There are now 96 public declarations in the article's shared/interface modules:
71 theorems and 25 definitions. Theorem 5 is a necessary dependency, not one of
the four introductory main theorems. All-order Hamiltonian identification and
gradients, the sharp Sobolev flow restrictions, and the spectral actions,
coordinates and frequencies required by the main theorems remain incomplete.

## 2026-11-02 — all-order smooth physical variational gradients

The shared differential-polynomial library now proves the Euler–Lagrange
first-variation formula at every polynomial order. A generic chain rule in a
normed complex algebra is applied to continuous physical jet curves; their
bounded complex-linear unit-interval integral commutes with differentiation.
Repeated periodic integration by parts transfers all derivatives off each
variation. The proof uses the finite set of jets occurring in the polynomial
and imposes no maximum order.

`NLS.ZakharovShabat.hasDerivAt_classicalNLSHamiltonian` applies this result to
the existing Riccati Hamiltonians, with their exact powers of `-i`. For every
order and every smooth complex periodic pair, its actual complex derivative
along arbitrary smooth periodic variations is the integral pairing with
`classicalNLSHierarchyGradient`. The two gradient components are proved smooth
and periodic. The physical Hamiltonian or its first variation is not supplied
as an identification hypothesis.

Reusable periodic derivative and integration-by-parts results were moved into
`NLS/FunctionalAnalysis/PeriodicIntegrationByParts.lean`; existing equation
APIs retain wrappers. The polynomial variation and Euler calculus live in
`NLS/DifferentialPolynomial`, and the bounded curve integral in
`NLS/FunctionalAnalysis/UnitIntervalMean.lean`.

All 28 article/shared modules and the NLS aggregate compile with Lean 4.33.1,
`autoImplicit=false` and warnings as errors. The expanded targeted transitive
audit passes for 278 declarations and generated auxiliaries, including the
imported shared differential-polynomial namespace. The combined NLS/article
audit passes for 45,434 declarations. Both allow only `propext`,
`Classical.choice` and `Quot.sound`. This is compilation against the pinned
read-only dependency cache, not a fresh rebuild of all dependencies. The full
validation ran under the shared build lock and wrote only local artifacts.

The public article/shared inventory contains 126 declarations: 94 theorems
and 32 definitions. Main Theorems 1–4 remain incomplete. The next gradient
obligation is the exact H^(k-1) L² extension and symmetry/vector-field
identification; the even/odd hierarchy recurrence and independent all-order
mKdV Hamiltonian identification also remain open.

## 2026-11-02 — Theorem 2(i) on the original complex Sobolev domain

All four assertions of Theorem 2(i), p. 3, are now proved for every k≥1,
every complex pair in H^(k-1), and every real phase α:

- `theorem2_i_swap_gradients` gives the printed gradient swap identity.
- `theorem2_i_phase_gradients` gives the printed phase-gradient identity.
- `theorem2_i_swap_vector_fields` gives the sign `(-1)^k` for the swapped field.
- `theorem2_i_phase_vector_fields` gives phase covariance of the vector field.

These declarations are in
`NLS/Articles/MKdVNLSHierarchies/GradientSymmetries.lean`. They require no
smoothness, real-type, open-gap or caller-supplied gradient-identification
hypothesis. The k=1 H0 endpoint is included.

The shared construction closes the gradient dependency. Partial polynomial
differentiation removes exactly the selected jet's derivative weight, and
the Euler spatial derivatives restore it. Thus the order-k gradient has total
derivative count at most k−1. On H^s with s≥1 and k≤s+1, each monomial contains
at most one top L2 derivative. Its remaining factors have continuous physical
representatives, so the existing bounded circle multiplication supplies an
analytic L2 realization. The bounded physical restriction coefficient map
retains the actual period-one Fourier integrals. The H0 mass gradient is
handled directly, with its two components exchanged.

`fderiv_sobolevNLSHamiltonian_eq_gradient` proves that these analytic L2
coefficients represent the existing physical Hamiltonian's actual complex
Frechet derivative on every admissible H^s domain. It uses the checked smooth
first variation and smooth density in both the base point and direction.
Fourier modes prove uniqueness of this representation. The existing exact-domain
covector symmetries consequently give the physical gradient symmetries, and
the Poisson tensor `-iJ` gives the printed vector-field identities.

All 35 article/shared modules and the NLS aggregate pass with Lean 4.33.1,
`autoImplicit=false` and warnings as errors. The targeted transitive audit
passes for 373 declarations and auxiliaries; the combined NLS/article audit
passes for 45,550 declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. Validation used the pinned read-only compiled
dependency cache and the shared build lock; this is not a fresh rebuild of
all dependencies. There are 168 public declarations: 128 theorems and 40 definitions.

The goal remains incomplete. Theorem 2(ii)'s corrected even/odd gradient
recurrence, the sharp H^m diagonal flow restriction and independent all-order
mKdV Hamiltonian identification in Theorem 1, and the action, coordinate,
bracket and frequency identifications in Theorems 3–4 remain open.

## 2026-11-02 — constructed all-order Riccati resolvent and variation identity

The next dependency toward the corrected Theorem 2(ii) is now proved in the
shared differential-polynomial library. Spatial derivations extend
coefficientwise to formal power series while fixing the spectral parameter.
The generic Riccati recurrence constructs a unique series R; using the
opposite spatial derivation and exchanged fields constructs S. The denominator
`1+t^2*R*S` has constant coefficient one, so its inverse V is constructed over
the coefficient algebra without dividing by either physical field.

The components `A=R*V`, `B=S*V`, `C=t*R*S*V` satisfy the exact formal identities

```
A = -b + t*D(A) + 2*b*t*C
B = -a - t*D(B) + 2*a*t*C
D(C) = b*B - a*A.
```

`constructed_riccati_resolvent_identities` proves these from the actual
constructed series. Their coefficient recurrences are also checked. On the
diagonal, spectral reflection exchanges R and S, fixes V, and negates C.
Every even coupling coefficient consequently vanishes; the first component's
odd coefficient is the spatial derivative of its preceding even coefficient,
and the second has the opposite sign. These are identities at every order.

`riccati_resolvent_coefficient_variation` supplies the required variational
bridge for any coefficient variation E commuting with D:

```
E(a*r_n) = E(a)*A_n + E(b)*B_n - D([t*B*E(R)]_n).
```

Thus the discarded total spatial derivative has an explicit primitive. The
linearized Riccati equation used in this proof is derived from the constructed
series, rather than passed in as an identification assumption.
`NLSRiccatiResolvent.lean` proves that the canonical series input has exactly
the existing NLS Riccati polynomials as its coefficients, fixing the seed and
all orders of the physical recurrence.

All 42 article/shared modules and the NLS aggregate pass with Lean 4.33.1,
`autoImplicit=false` and warnings as errors. The targeted transitive audit
passes for 434 declarations and auxiliaries, and the combined NLS/article
audit passes for 45,611 declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. Validation used the read-only pinned dependency
cache and shared build lock; all writable outputs are local. The entire
dependency tree was not rebuilt from source. The public inventory now contains
209 declarations: 161 theorems and 48 definitions.

No additional main theorem is claimed by this formal bridge. To finish the
corrected Theorem 2(ii), construct arbitrary jet perturbations, identify A_n
and B_n with the certified physical Euler gradients, and transfer the diagonal
identity through phase covariance and exact-domain continuity. Theorem 1's
sharp diagonal flow/Hamiltonian identification and Theorems 3–4 remain open.

## 2026-11-02 — corrected Theorem 2(ii) on the original complex Sobolev domain

Theorem 2 is now proved on its original domains, with the matrix in part (ii)
corrected from the printed `-iJ` to `R=diag(i,-i)`, as required by the paper's
own summation proof on p. 18.

`NLS.Articles.MKdVNLSHierarchies.theorem2_ii_corrected` proves, for every m≥1
and every complex H^(2m−1) pair satisfying `P phi=R_alpha phi` for some real α,
that R times the actual even Hamiltonian gradient equals the actual spatial
derivative of the odd gradient. The derivative is Mathlib's
`TemperedDistribution.derivCLM` of the physical period-one L2 field. Its result
is represented by the certified even L2 gradient. The companion
`theorem2_ii_corrected_coefficients` gives the exact `2*pi*i*j` multiplier
identity. No smoothness, real-type, nonzero-potential or caller-supplied
gradient-identification hypothesis is imposed.

The missing variational bridge is fully constructed. The shared multi-field
jet algebra adds independent background and variation jets; its evolutionary
derivation commutes with spatial differentiation. Differential coefficient
maps preserve the constructed Riccati resolvent. These facts instantiate the
all-order variation identity for arbitrary actual smooth periodic directions.
The explicit total derivative integrates to zero. Smooth Fourier tests then
identify the resolvent components pointwise with the already certified Euler
gradients. `classicalNLSHierarchyGradient_eq_resolvent` retains the original
factor `(-i)^(n+2)` at every Hamiltonian order.

The diagonal parity cancellation now yields the normalized physical gradient
recurrence at every order. Smooth density extends its Fourier identity to all
original diagonal H^(2m−1) inputs. Reciprocal scaling extends it to proportional
components; the printed phase hypothesis supplies exactly such a scaling via
`exp(i*alpha/2)`. Finally, the established Fourier distribution derivative
identifies the coefficient recurrence with the genuine physical derivative.

All 54 article/shared modules and the NLS aggregate pass with Lean 4.33.1,
`autoImplicit=false` and warnings as errors. The targeted transitive audit
passes for 515 declarations and auxiliaries, and the combined NLS/article
audit passes for 45,695 declarations. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. The check ran under the shared build lock against
read-only pinned compiled dependencies, with local writable outputs; it did
not rebuild the whole dependency tree from source. The inventory contains
265 theorem/definition declarations: 207 theorems and 58 definitions.

The goal remains incomplete. Theorems 1, 3 and 4 still require the independent
all-order mKdV/Hill Hamiltonian identification, the sharp H^m diagonal flow
extension, and the spectral action, coordinate, bracket and frequency
comparisons, including the remaining source sign/mean qualifications.


## 2026-11-02 — All-order smooth scalar Hill/Miura hierarchy and flow restriction

The scalar Hamiltonian hierarchy is now independently constructed from the
Hill Riccati recurrence at `q=u_prime+u^2`, with seed `rho_0=-q`, first
coefficient `rho_1=-Dq`, and scalar quadratic coefficient one. Its Hamiltonian
of index m is `(-1)^m/2` times the periodic integral of `rho_(2m-2)`.
This definition does not use the diagonal NLS Hamiltonian. The first two
members are proved equal to the already specified mKdV mass and energy.

The generic differential-algebra theorem `differentialRiccatiSeries_miura`
constructs the exact gauge transformation from the canonical diagonal NLS
Riccati series R. The gauge factor is `1+X R`, which has constant coefficient
one and therefore a constructed formal inverse. Its correction is
`D R/(1+X R)`. The new `logarithmicPrimitiveCoefficient` uses the finite
Taylor coefficient of `log(1+X R)/X`; its derivative is proved equal to each
correction coefficient by the finite geometric-sum identity. No formal
convergence assumption, finite-gap hypothesis or caller-supplied Riccati
solution appears in the resulting coefficient theorem.

`proposition6_smooth_miura` now proves the factor-two periodic Hamiltonian
identity at every order on smooth complex periodic fields. The independently
specified scalar density has a certified physical first variation in
`hasDerivAt_classicalMiuraHillHamiltonian`. Uniqueness of smooth periodic
variational tests identifies its Euler gradient with an odd NLS gradient
component. The two odd NLS components agree on the diagonal, as proved by
the constructed resolvent parity. Combining these results with the existing
normalized gradient recurrence proves the all-order Gardner/NLS flow
identity. `theorem1_smooth_miura_hierarchy` includes both that identity and
actual even NLS Hamiltonian vanishing, for every integer m>=1.

Theorem 1 remains partial: the sharp H^m extension, and full identification
with the article's spectral mKdV hierarchy, are not asserted by this smooth
interface. The spectral gaps, action integrals, Birkhoff coordinates,
brackets and frequencies needed for Theorems 3 and 4 remain open. Theorem 2
retains its previously verified full original domains and matrix correction.

The latest shared article branches were inspected read-only. The KdV
convexity branch `963d5bb` supplies independently calibrated low Hill
coefficients and actual scalar trace estimates; it does not complete the
all-order mKdV comparison. The mKdV-below-L2 branch `205c11c` adds analytic
weighted H4 candidates on physical Banach spaces, and the KdV-frequency
branch `a4d0bd4` adds actual Hill numerators and finite period normalization.
These do not supply the remaining scalar mKdV action/coordinate comparison;
no unrelated article target is counted as completed here. The current
proofs reuse the checked generic Riccati, physical NLS gradient, periodic
integration and Fourier uniqueness developments in this worktree.

All 59 article/shared modules and the NLS aggregate compiled with the pinned
Lean 4.33.1 toolchain, `autoImplicit=false`, and warnings as errors. The
expanded targeted transitive audit passed for 570 declarations and generated
auxiliaries; the combined aggregate/article audit passed for 45,750 NLS
declarations. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
The public theorem/definition inventory now contains 298 declarations:
230 theorems and 68 definitions. Validation used the shared build lock,
read-only pinned compiled imports and private writable outputs; the entire
dependency tree was not rebuilt from source. No admitted proof, new axiom,
disabled linter or caller-supplied essential variation identity was added.
Canonical main remains clean at `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`.


## 2026-11-02 — Sharp H^m even Hamiltonians and scalar Theorem 1 clause

The scalar vanishing clause of Theorem 1 is now proved on its exact domain:
for every integer m>=1 and every complex u in H^m,
`theorem1_even_vanishing_sharp` proves `sobolevEvenHamiltonian m hm (u,u)=0`.
There is no additional smoothness or real-type assumption.

The endpoint construction extends the actual physical Hamiltonian on all
complex H^m pairs before restricting to the diagonal. Polynomial integration
by parts preserves the total derivative count 2m-1 and lowers individual jets
to order m. The sharpened shared L2 realization uses the fact that at most
one order-m jet can occur below total derivative count 2m. Removing it leaves
only lower, continuous Sobolev jets. The former stronger-range comparison
lemmas retain their signatures and now follow from this sharper result.

`NLSEvenHamiltonianReducedPolynomial.lean` constructs one reduced polynomial
before choosing the source. `SobolevEvenHamiltonian.lean` integrates its actual
L2 realization using the bounded physical unit-interval integral. It proves
entire complex analyticity, agreement with the actual classical hierarchy on
all smooth periodic pairs, uniqueness among continuous extensions, and
compatibility with every admissible input of the existing original hierarchy
(`sobolevEvenHamiltonian_eq_original`). Component-swap antisymmetry then
proves diagonal vanishing throughout H^m. This is a genuine extension of
S_(2m), rather than assigning zero by definition on the diagonal.

The shared `SobolevPolynomialVariation.lean` additionally constructs a bounded
partial-jet covector for every density satisfying the endpoint bounds. Its
coefficients are actual period-one Fourier coefficients of the partial jet
L2 fields. Each covector pairs them with the corresponding weak derivative
of the arbitrary H^m direction by bilinear Parseval. The general theorem
`fderiv_sobolevPolynomialL2Mean` identifies this covector with the actual
complex Frechet derivative for every complex Sobolev source and direction.
The proof uses physical smooth first variations and density in both variables.
`fderiv_sobolevEvenHamiltonian_eq_covector` specializes it to the sharp even
Hamiltonians. No gradient identification is a caller hypothesis.

Theorem 1 remains incomplete: its sharp weak vector-field identity and full
spectral identification of the independently constructed scalar Hill/Miura
hierarchy remain to be proved. Theorems 3 and 4 still need spectral action,
coordinate, bracket and frequency comparisons, with the recorded source
corrections. Theorem 2 retains its verified exact original Sobolev domains.

The latest shared branches were inspected read-only: KdV convexity `e848349`
adds Hill spectral reality and analytic tail summation, KdV frequencies
`758dc7c` adds a uniform infinite Hill numerator family and analytic critical
tails, and mKdV-below-L2 `b54fed5` adds refined H4 candidate remainders and a
physical quartic contour. This endpoint polynomial argument reuses the
checked physical Sobolev jets, L2 synthesis, integration by parts, smooth
first variations and density already available in the dissertation library;
no unrelated spectral candidate is counted as a proved main theorem here.

All 63 article/shared modules and the NLS aggregate compiled with pinned
Lean 4.33.1, `autoImplicit=false` and warnings as errors. The targeted
transitive audit passed for 639 declarations and generated auxiliaries;
the combined aggregate/article audit passed for 45,820 NLS declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The current
public inventory contains 330 theorem/definition declarations: 256 theorems
and 74 definitions. Validation used the shared build lock, read-only pinned
compiled dependencies and private writable outputs, without rebuilding the
entire dependency tree. No admitted proof, new axiom or disabled linter was
introduced. The goal remains active while the essential vector-field and
spectral obligations remain.


## 2026-11-02 — Full H^m weak flow restriction for the independent Hill hierarchy

`theorem1_sharp_miura_hierarchy` now proves both scalar vanishing and the
actual weak vector-field identity for every integer m>=1 and every original
complex u in H^m. No smoothness, real-type, nonzero-potential, or caller-supplied
gradient-identification hypothesis is imposed. The scalar hierarchy is
independently constructed from the Hill Riccati densities; its full source
spectral identification remains an explicit essential obligation.

The reusable Sobolev cotangent construction now represents the actual full
Frechet differential of a scalar functional on a pair source by two gradients
in the opposite Sobolev space. It uses the existing full scalar Sobolev duality,
without changing the source product norm or introducing a conjugated pairing.
Every raw Fourier coefficient is evaluated on the actual opposite mode.
`hierarchyWeakGradient_represents` recovers the complete differential, rather
than only its value on finite directions. Analytic functionals have analytic
gradients. Smooth agreement and actual smooth first variations identify the
physical period-one Fourier integrals of these weak gradients.

`SobolevMiuraHillHamiltonian.lean` constructs the scalar H^m Hamiltonian directly
from the scalar Hill density. A new generic integration-by-parts theorem
handles densities without a common field-charge grading by reducing each
monomial with its own gradings, preserving the total-derivative bound. The
scalar Riccati densities have at most n+1 total derivatives. Their normalized
Hamiltonian densities can thus be reduced to jets through m with at most
2m-1 total derivatives, and their actual L2 means are analytic on H^m.
No scalar Hamiltonian is defined as half an NLS restriction. The full scalar
gradient is the actual Frechet derivative represented by Sobolev duality;
its smooth comparison is proved from the already certified physical first
variation of the independent classical Hill Hamiltonian.

`SobolevEvenHierarchyGradient.lean` likewise identifies the weak gradient of
the sharp even NLS Hamiltonian with its actual Frechet differential and
physical smooth gradient. Finite Fourier sources are dense in the original
complex Sobolev space. Analytic dependence in the negative Sobolev norm and
the checked smooth hierarchy flow identity therefore prove the all-input
coefficient identity `sobolevMiuraHillFlowRestriction_coefficients`.

`periodOneSobolevDistribution` reuses the checked arbitrary-period weighted
synthesis at every real Sobolev order. It is a genuine period-one tempered
distribution with exactly the raw source coefficients. Its actual Mathlib
distribution derivative has multiplier `2*pi*i*n`, including negative orders.
`sobolevMiuraHillFlowRestriction` turns the coefficient comparison into the
physical distribution equality: Gardner's derivative of the independent
scalar gradient is represented by each even NLS field in H^(-m). Thus this
result includes the original nonsmooth H^m inputs, with certified actual
derivatives on both sides, rather than just a formal coefficient recurrence.

The goal remains incomplete. The scalar Hill/Miura hierarchy still needs its
full identification with the source's spectral mKdV Hamiltonians and its
native H^(m-1) scalar Hamiltonian extension. Theorems 3 and 4 additionally
require the fixed Hill gap labels, action integrals, mKdV coordinates,
brackets and frequency identification, with the recorded sign and mean
qualifications. Theorem 2 retains its previously verified exact domains.

All 71 article/shared modules and the NLS aggregate compiled with the pinned
Lean 4.33.1 toolchain, `autoImplicit=false` and warnings as errors. The
targeted transitive audit passed for 720 declarations and generated
auxiliaries. The combined aggregate/article audit passed for 45,903 NLS
declarations. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
The public theorem/definition inventory contains 369 declarations: 285
theorems and 84 definitions (aliases excluded). Validation used the shared
build lock, read-only pinned compiled dependencies and private writable
outputs, without rebuilding the whole dependency tree. No admitted proof,
new axiom or disabled linter was introduced. Canonical main remains clean
at `c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`; the goal remains active.


## 2026-11-02 — Native scalar hierarchy and actual Hill trace calibration

The independent scalar hierarchy is now constructed on its exact native
complex domains: `nativeMiuraHillHamiltonian s` is K_(s+1) on all H^s,
including the L2 mass endpoint s=0. No member is defined as half an NLS
restriction. `proposition6_native_miura` proves the factor-two identity on
exactly H^(m-1), and `theorem1_native_miura_hierarchy` uses the actual native
Frechet gradient in the full H^m weak flow identity.

The endpoint improvement is independent of NLS reduction. Subtracting the
linear total derivative from the scalar Hill Riccati coefficient gives
`miuraHillRiccatiRemainder`, with at most n total derivatives at index n.
The normalized remainder at index 2s is reduced directly to jets through s,
retaining at most 2s total derivatives. A new shared endpoint mean allows
two top L2 factors, using bounded bilinear Parseval with continuous lower
factors; the former construction allowed only one. Removing both top
factors leaves derivative count zero. The zero-order mass is handled by
its independent bilinear Hilbert pairing, rather than extending the
continuous lower-factor argument to a false generic H0 assertion.

Each native Hamiltonian is analytic on the whole complex H^s space. It
agrees with the independent physical scalar Hill integral on every smooth
periodic representative, is the unique continuous extension of that
classical hierarchy, and agrees with the preceding H^(s+1) construction.
Full Sobolev duality constructs its actual gradient in H^(-s), representing
the entire Frechet differential. Smooth first variations identify its
physical Fourier coefficients. Scalar smooth density proves compatibility
with the higher-regularity gradient, despite their different opposite-order
norms. The actual Gardner derivative then agrees with the checked even NLS
field on every original complex H^(s+1) input.

`SobolevOddHamiltonianAllOrders.lean` unifies the existing sharp odd NLS
Hamiltonian with its H0 mass endpoint, retaining the original physical
normalization and proving smooth agreement and continuous uniqueness.
This is an adapter of checked NLS constructions. The resulting native
Proposition 6 statement includes m=1 and all nonsmooth complex inputs.

`MiuraHillHamiltonianTrace.lean` additionally proves all-order calibration
of the literal physical Hill discriminant, defined by independent scalar
position/derivative IVPs. Its trace at energy r^2 is approximated by
`2*cos(i*phase_N)` with phase
`-i*r + i*sum_{m=1..N} 2*K_m/(2*r)^(2*m-1)` and error bounded by
`C/(2*abs(r))^(2*N)` for abs(r)>=1. The proof uses the actual Hill/ZS trace
identity and the checked all-order physical NLS WKB estimate. Even terms
vanish, and odd coefficients are the independently defined scalar Hill
Hamiltonians. This is an actual spectral trace estimate, not only a formal
Riccati recurrence or a caller-supplied asymptotic hypothesis.

The latest shared branches were inspected read-only. KdV convexity
`1518245` fixes physical Hill primitive sheets and proves cubic moment
reality; KdV frequencies `3bc5c4e` constructs uniform infinite Hill period
entries and actual tail formulas; mKdV-below-L2 `70da92c` verifies physical
H4 finite-gap derivatives and Lemma 5.2. Their spectral developments remain
available for the next source primitive/action identification. No unrelated
candidate or article theorem is counted as a completed main result here.

All 80 article/shared modules and the NLS aggregate compiled with pinned
Lean 4.33.1, `autoImplicit=false` and warnings as errors. The targeted
transitive audit passed for 854 declarations and generated auxiliaries;
the combined aggregate/article audit passed for 46,038 NLS declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The current
public inventory contains 424 theorem/definition declarations: 326 theorems
and 98 definitions (aliases excluded). Validation used the shared build
lock, read-only pinned compiled dependencies and private writable outputs,
without rebuilding the whole dependency tree. No admitted proof, additional
axiom or disabled linter was introduced.

The goal remains incomplete. Full source free-normalized spectral
primitive-sheet/action identification of the native scalar Hamiltonians is
still essential. Theorems 3 and 4 also require fixed spectral gap labels,
action comparisons, mKdV coordinates, brackets and frequency identification,
with the recorded source sign and signed-mean qualifications. Theorem 2
retains its verified exact original complex Sobolev domains.


## 2026-11-02 — actual free-normalized Miura/Hill and NLS sheet comparison

Integrated 19 unchanged checked shared modules from `articles/kdv-convexity`,
pinned at `d12831411f4ad00777304b6623dbb3226730b4eb`. These provide the
independent scalar Hill IVP, physical Green identity and spectral reality,
free-normalized source-continuation root and primitive, half-plane signs,
reflection and band normalization. Their imported source files are
byte-for-byte identical to the pinned branch.

`MiuraHillSpectralBridge.lean` proves equality between the existing physical
Miura solution state and the shared scalar Hill state by physical weak IVP
uniqueness. Its discriminant identity holds at every complex energy, including
zero, whenever the continuous Hill potential agrees almost everywhere with
the physical Miura potential of an absolutely continuous profile. In
particular every complex C1 profile has this independent operator comparison;
periodicity then gives the exact diagonal ZS trace identity.

`ContinuousPotentialSource.lean` supplies the bounded map from an actual
continuous interval pair to its original physical Fourier source. Both its
canonical discriminant agreement and its real-type preservation are proved.
`HillNLSPrimitivePathComparison.lean` transfers physical trace equality to
exact root and primitive equality along continuous real source paths from
zero, using nonvanishing and the literal free values to fix the sign and the
additive logarithm period.

`MiuraHillPrimitiveComparison.lean` instantiates these results on the actual
Miura image of s*u: q_s=s*u_prime+s_squared*u_squared. This quadratic path
is continuous in the curve norm, remains real, and has the same actual trace
as the original Fourier source of s*u. The independently constructed Hill
root and primitive at z_squared therefore equal the NLS canonical root and
abelian primitive at z for every real C1 period-one profile and every
nonreal z with positive real part. The article exports these as
`lemma4_root_real_C1_right_halfPlane` and
`lemma5_primitive_real_C1_right_halfPlane`.

These are qualified results. The original full H1 domains, real bands and
boundary points of the labeled gap complement, action integrals and mKdV
Birkhoff/frequency identification remain essential obligations. Theorem 1 is
still recorded as partial for the source spectral hierarchy; Theorems 3 and 4
remain incomplete. No completeness claim or new axiom is introduced.

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


## 2026-11-02 — independent physical primitive on the full real H1 domain

`SourceDiscriminantPrimitive.lean` factors the free-normalized continuation
argument into a reusable construction for an actual entire discriminant
on an arbitrary complex normed source space. It proves analyticity of the
root, multiplier and primitive on the open source-continuation domain,
the exact square and hyperbolic trace identities, and the full joint
Frechet differential root_inverse times d_discriminant. All structure
hypotheses are proved for the independent quasi-Hill IVP instance.

`QuasiHillJointAnalytic.lean` proves that the actual quasi-derivative
coefficient is affine, and its Volterra discriminant jointly entire, in
energy and the continuous profile. `QuasiHillSourcePrimitive.lean` constructs
the independent Miura root and primitive from that discriminant. Their
definitions do not use NLS spectral functions. Actual NLS spectral reality
proves admissibility of every real continuous profile at nonreal right
frequency points; continuity from the literal free values then proves exact
root and primitive equality with the original NLS functions.

`QuasiHillPrimitiveComparison.lean` also proves agreement with the previously
integrated independent scalar Hill construction for every C1 periodic real
profile. `SobolevMiuraPrimitive.lean` identifies the physical Fourier source
with the coefficient-preserving original diagonal H1 pair. The physical
period-one representative is a bounded complex-linear map in the original
H1 norm, and the primitive is analytic in that complex H1 source on its
admissible domain. Conjugate reflection of the original coefficients
supplies reality of every representative in the real H1 domain.

The article now exports `lemma4_root_real_H1_right_halfPlane` and
`lemma5_primitive_real_H1_right_halfPlane`. These remove the C1 restriction
on the profile. It also proves the exact hyperbolic trace and energy
derivative for the original physical H1 Hill discriminant, conditional
only on membership in the constructed complex continuation domain.

The frequency restriction Im z != 0, Re z > 0 remains in the comparison.
Real bands, the whole labeled gap complement, spectral action integrals
and mKdV coordinate/frequency comparison remain essential. Theorem 1
for the source spectral hierarchy and Theorems 3 and 4 remain incomplete.

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


## 2026-11-02 — the full H1 Miura potential inside the actual L2 Hill spectrum

Integrated 41 unchanged checked modules from `articles/kdv-estimates` at
`5da8934e019a8a08f314988c311661754b89e925`. These construct the original
periodic H2 Hill operator, its actual L2 monodromy discriminant, entire
energy descent, characteristic root counts and intrinsic ordered real
labels with analytic multiplicities. The copied sources are byte-for-byte
identical to that pinned branch; the checker orders all source dependencies
before their consumers.

`SobolevMiuraPotential.lean` constructs the literal analytic H1-to-L2
Miura map. Its original period-one coefficient is 2*pi*i*n*u_n plus the
actual convolution sum. On every complex H1 input, the coefficients equal
the actual Fourier integrals of u_prime+u_squared. Even insertion retains
these at ambient index 2*n, fixing the Hill period normalization.

`MiuraL2HillDiscriminant.lean` proves equality of the independently
constructed L2 Hill and quasi-Hill monodromy traces on every original
complex H1 input and every complex energy, including zero. Physical IVP
uniqueness proves the smooth comparison; norm continuity and finite
Fourier density extend it to H1. Thus the shared physical H2 Hill operator
now applies to this article's actual rough Miura potential.

`MiuraHillSpectralIdentification.lean` identifies its eigenvalue condition
with the original ZS periodic spectrum at squared energy, without a reality
restriction. Analytic characteristic orders equal the original ZS algebraic
multiplicities away from zero. At zero the frequency order is exactly
twice the energy order, accounting for the square-map ramification. For
real H1 profiles, every Hill characteristic root is real and nonnegative.

`MiuraHillRealLabels.lean` proves Fourier reality of the actual rough
potential, then instantiates the intrinsic ordered real Hill labels. The
labels exhaust its physical characteristic zero set, retain exact analytic
multiplicities and are all nonnegative. The article exports the stronger
physical L2 form of Theorem 5 and the spectral-set, positivity and analytic
multiplicity parts of Lemma 3.

Matching each fixed Hill endpoint label with the corresponding original
NLS endpoint square, the printed geometric-multiplicity comparison,
real-band primitive extension and spectral action integrals remain open.
Theorem 1 for the source spectral hierarchy and Theorems 3 and 4 remain
incomplete. These results do not assert an action or Birkhoff identification.

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


## 2026-11-02 — exact indexed endpoint and gap identification on real H1

`CanonicalPeriodicEvenReflection.lean` proves exact signed-index reflection
for an even original periodic characteristic. Global root multiplicities,
the original l2 lattice displacement and ordered-pair uniqueness fix each
reflected index, including the central pair. This applies to every complex
H1 Miura input; reality is imposed only for the positive real enumeration.

`OrderedNaturalEnumerationUnique.lean` supplies a reusable uniqueness result:
ordered natural enumerations with finite fibers and equal multiplicities
agree at every index. Its proof isolates the first differing slot by a
strict fiber-cardinality inequality. No tail cutoff or unproved indexing
offset enters the comparison.

The positive NLS enumeration starts with lambda_0_plus, followed by both
endpoints of each positive pair. Strict separation excludes extra
occurrences from other pairs. `MiuraPositiveMultiplicity.lean` proves its
exact counts: positive frequencies retain their full original NLS
multiplicity, while the count at zero is exactly half the original NLS
multiplicity. Combining this with the checked square-map ramification
proves that the squared positive sequence has the same multiplicities as
the independently constructed actual Hill labels, including energy zero.

`MiuraSquaredEndpointMultiplicity.lean` then identifies the entire two
natural enumerations. `MiuraGapIdentification.lean` derives the exact
fixed-index endpoint identities, both central identities, square images of
closed positive gaps and collapse equivalence. The article exports these
as lemma3_ground_endpoints, lemma3_indexed_endpoints,
lemma3_gap_square_image and lemma3_gap_collapsed_iff. All original real H1
inputs and every positive index are included without smoothness or
nonzero-mean restrictions.

The printed geometric-eigenspace multiplicity comparison is still separate
from these analytic characteristic multiplicities. Full real-band sheet
extension, spectral action integrals, spectral Hamiltonian identification
and Theorems 3 and 4 remain open. The goal remains incomplete.

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


## 2026-11-02 — actual central and reflected NLS actions in Theorem 4(i)

`ClassicalDiagonalZeroEnergy.lean` solves the original ZS IVP at zero
frequency for every continuous complex diagonal profile. The normalized
solution matrix has diagonal entries cosh(integral_0^x u) and off-diagonal
entries i*sinh(integral_0^x u), -i*sinh(integral_0^x u). IVP uniqueness
identifies this explicit formula with the independently constructed flow;
its actual monodromy trace is 2*cosh(integral_0^1 u).

`MiuraZeroEnergy.lean` identifies the literal physical unit-interval mean
of every original complex H1 profile with its original zeroth Fourier
coefficient. It proves equation (21) for the independently constructed L2
Hill discriminant and the original NLS discriminant. On the full real H1
slice, the central canonical NLS gap collapses exactly when this mean
vanishes. Ordered endpoint separation excludes all other gap indices from
zero; no smoothness or nonzero-mean hypothesis is introduced.

`MiuraActionZeroIdentification.lean` uses the existing sourceIndexedAction
contour integral on the literal diagonal source. The central action
vanishes exactly when the physical mean vanishes. At every positive index
the actual NLS action vanishes exactly when the independently constructed
physical Hill gap collapses. Nonnegativity and reality also follow from
the existing action theorem.

`SourceIndexedActionCosineIntegral.lean` connects the existing indexed
contour action to the independently checked first primitive moment and its
real-gap cosine integral. `MiuraActionReflection.lean` uses the exact
signed endpoint reflection, the even physical discriminant, and the
substitution theta -> pi-theta to prove I_(-n)#=I_n# at every signed index,
including closed gaps. The source action is not defined by this symmetry
or a gap-zero criterion.

The article exports equation21_physical_mean_trace,
theorem4_i_central_action_zero, theorem4_i_action_reflection and
theorem4_i_positive_action_zero_iff_hillGap_collapsed. The central and
reflection clauses of Theorem 4(i) are now proved. The actual contour-defined
mKdV actions J_n, their comparison and analytic factorization, angle and
frequency identities, full real-band primitive extension and the printed
geometric multiplicity comparison remain open. Main Theorems 1, 3 and 4
remain incomplete.

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


## 2026-11-02 — full real-H1 canonical Hill sheets and Lemmas 4 and 5

`NonrealBoundaryExtension.lean` constructs a function's values by limits
from nonreal energies. The nonreal relative neighborhood filter is
nontrivial at every complex point. Agreement off the real axis with a
continuous germ determines each limit; analytic germs make the filled
function analytic. This is reusable complex analysis, with no NLS import.

`MiuraHillBoundaryExtension.lean` applies that construction to the original
independent physical quasi-Hill root and primitive. No NLS function enters
either definition. The already checked nonreal comparison then proves
existence of the limits and their equality with the actual NLS sheets
through the principal energy square root. This includes every real band,
removing the earlier nonreal-frequency restriction. On the old admissible
source-continuation domain the filled functions equal the original
independently constructed functions, also for complex H1 profiles.

`MiuraHillGapComplement.lean` uses only the actual independent Hill labels
to define its energy cut complement: the real ray below and including the
ground label and every positive closed gap are removed. The exact indexed
gap identities prove that squaring the right frequency half-plane maps the
original NLS cut complement exactly to this physical Hill domain. The
principal square root supplies the converse witness, and the domain is open.

`MiuraCanonicalHillSheets.lean` proves spectral analyticity throughout that
full real-H1 domain. Continuity from nonreal energies retains the actual
L2 Hill trace and the root/primitive hyperbolic identities. The root squares
to the physical Hill radicand and never vanishes there. Differentiating the
physical trace gives the exact energy derivative Delta_prime/root. The
first-band sign is the source's positive real value of i times the root.

`MiuraHillPrimitiveEndpoint.lean` proves the exact signed endpoint limits,
including a zero limit at the actual ground energy even when it is zero.
For every smooth integrable connector from that ground energy through the
physical gap complement, the integral of the actual Hill Delta_prime/root
one-form equals the filled primitive. This supplies the source's original
path-integral normalization, rather than only a local logarithm identity.

The article exports full-domain lemma4_root_real_H1_gapComplement and
lemma5_primitive_real_H1_gapComplement, the exact square-domain comparison,
spectral analyticity, physical trace and energy derivative, and equations
(10) and (11). Lemmas 4 and 5 are complete on their original real-H1
domain. Joint complex-source continuation on arbitrary real-band
neighborhoods, inverse-energy-weighted mKdV action contours, spectral
Hamiltonian identification, geometric eigenspace multiplicities and main
Theorems 1, 3 and 4 remain incomplete.

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


## 2026-11-02 — actual weighted spectral actions and complete Theorem 4(i)

`PiecewiseSquareContour.lean` maps actual finite piecewise C1 loops under
z -> z^2 and proves the actual path-integral substitution with Jacobian
2*z, including corners. `PiecewiseSquareWinding.lean` proves that winding
at w^2 equals the sum of the original windings at w and -w. The checked
positive real disc geometry then fixes the orientation and origin exclusion.

`SourceWeightedPrimitiveContour.lean` generalizes the checked real-gap
boundary calculus to every weight analytic on the closed isolating disc.
It includes collapsed gaps. `SourceLaurentActionContour.lean` constructs
the source's actual action contours at all integer levels, including level
zero, and proves their real-gap formula whenever the disc excludes zero.
The global ground-normalized and local gap-normalized primitive contours
agree with their exact constants. `SourceLaurentActionContourPeriod.lean`
proves the actual winding formula on arbitrary close piecewise circuits,
including corners, repeated/reversed traversals and collapsed gaps.

`MiuraLaurentContourComparison.lean` defines the physical mKdV integer-level
action contour by -(4*pi)^(-1) times the actual integral of
mu^(k-2)*F_Hill(mu). The canonical physical Hill primitive is independent
of NLS. Squaring gives exactly 2*J_(n,k)=I_(n,2k-2) for every integer k.
In particular the mKdV action k=1 uses the inverse-energy weight and the
NLS level zero, rather than the ordinary NLS level one.

`MiuraActionContourFamily.lean` constructs actual isolating circles for all
positive indices on every original real H1 profile. The central NLS segment
contains zero, so all other assigned discs exclude zero and lie in the
right half-plane. Their squared contours lie in the actual Hill gap
complement. They have winding one on the intended gap and winding zero on
other positive gaps and at the origin. These assertions use intrinsic
physical Hill labels, not labels defined by the contour.

`MiuraSpectralActions.lean` defines J_n by this actual physical contour.
The real-gap formula is a theorem derived from change of variables and
Cauchy boundary calculus. A mean-value point zeta_n in the actual positive
frequency gap proves J_n=I_n/(2*zeta_n); zeta_n is strictly positive on the
full real H1 domain. No action or gap-length division excludes collapsed
gaps. Thus J_n is real and nonnegative, and J_n=0 iff I_n#=0.
`MiuraSpectralActionContours.lean` proves independence of the checked
family and the full integer-level period formula for arbitrary close
piecewise frequency circuits and their squared energy images.

The article's `SpectralActionIdentification.lean` exports
lemma7_integer_levels_real_H1, theorem4_i_positive_actions and the complete
three-clause theorem4_i. The central and reflected-action clauses use the
previously checked actual NLS action results. Theorem 4(i) is now complete
on every original real H1 profile and every positive index, including
zero mean and collapsed gaps.

Lemma 7's real-H1 integer-level contour identity is proved. Its additional
analytic NLS extension on a neighborhood of the entire real L2 diagonal
remains open, as do complex-source mKdV action neighborhoods, spectral
Hamiltonian calibration, geometric eigenspace multiplicity and the action,
frequency and angle identities needed by Theorems 1, 3 and 4(ii)-(iii).
The overall goal remains incomplete.

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


## 2026-11-02 — finite-gap spectral calibration of native scalar K

The independent physical Hill labels now define the actual finite-gap
locus. Its equivalence with finite support of contour-defined mKdV actions
and with finite-gap of the original diagonal NLS source is proved. The
checked NLS bootstrap gives a smooth periodic profile preserving every
original Fourier coefficient; the original coefficients belong to every
native scalar Sobolev domain.

`equation12_finiteGap_native_laurent` proves the convergent physical Hill
primitive series with exact coefficients i*(2*K_(k+1))/(2*z)^(2*k+1),
for all sufficiently large complex right-half-plane frequencies. The
physical primitive is the independent nonreal-energy limit; its comparison
with the filled NLS primitive also includes collapsed exterior cuts.
`proposition6_finiteGap_native` calibrates the physical NLS odd and even
Hamiltonians at all orders, including the L2 mass member. No smoothness,
finite Fourier support, nonzero mean or primitive asymptotic is assumed.

The source spectral hierarchy still needs its extension/uniqueness
identification on the complete original complex native Sobolev domains.
Theorems 1, 3 and 4(ii)-(iii) remain incomplete.

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


## 2026-11-02 — complete Lemma 7 and ambient complex L2 action extensions

`lemma7` now includes both the actual real-H1 contour identity and the
source's final ambient complex-L2 analytic-extension clause. A single open
subset of the full pair coefficient space contains the entire real L2
diagonal before any index or level is chosen. At every positive n and
every integer k, the actual NLS Laurent action I_(n,2k-2) is analytic
there and restricts exactly to 2*J_(n,k) on every original real H1 input.
Closed gaps and zero mean are included. The central index is excluded.

The proof glues genuine local fixed-circle integrals, using real-form
analytic uniqueness on the entire complex overlap. Each chart's common
source ball is chosen once for the whole infinite contour family and all
integer levels. The atlas is independent of choices, and its positive
levels agree with the existing NLS higher actions on complex overlaps.
The induced complex H1 mKdV actions agree with the physical contours;
their actual Frechet derivatives retain the factor 1/2 and literal
coefficient diagonal.

Four checked component-swap modules were integrated unchanged from
`articles/mkdv-below-l2` at `40d1959bf83cadfd29557cf1a3035bec7db6028c`.
The fixed signed endpoint reflection places zero in the central gap at
every real coefficient diagonal, so all noncentral discs exclude zero
simultaneously. The generic construction works for every finite p>1.

Theorem 1's source spectral Hamiltonian extension/uniqueness step, action
factorization, angles and frequency/bracket identifications remain open.
Theorems 1, 3 and 4(ii)-(iii) remain incomplete.

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


## 2026-11-02 — Theorem 4(iii) angle-action clause on its original domain

`theorem4_iii_angle_action` proves the printed +delta_mn Gardner bracket
for every original real H1 profile and all positive m,n where the angle
at m is defined. The domain is the exact nonzero condition on its own
physical action J_m; the action index n may have a closed gap. Zero mean
is included. The actual normalized NLS phase supplies the restricted
angle, whose logarithmic differential is proved to be the pullback of
the original local angle differential. No angle cotangent or canonical
bracket is left as an input hypothesis.

The scalar action is the common analytic L2 extension of the independently
constructed physical Hill contour. Its full Frechet derivative constructs
the scalar bilinear gradient. This gradient's spatial derivative is
proved square summable and equal to the actual period-one tempered
distribution derivative. The literal Gardner field has diagonal equal
to the original NLS Hamiltonian direction of I_n-I_(-n). The transfer
formula holds for every bounded source cotangent.

The proof differentiates the genuine integer Laurent contours and
integrates the physical discriminant-gradient Fourier recurrence. This
retains all integer levels, all Fourier modes, the 2*pi*i*m multiplier
and the action factor 1/2. Four checked component-swap root/action/
differential/Poisson modules are reused unchanged from
`articles/mkdv-below-l2` at `9a2d23c9f2cf513921eb89cdb69b9a57eed3a3fc`.
Original NLS canonical brackets then prove the angle-action clause.
Original NLS action commutation also proves
`theorem4_ii_restricted_action_invariance` for every signed restricted
NLS action, including the central action, against every positive J_n.

The final Theorem 4(iii) assertion about the independently constructed
mKdV angle sum factoring through actions and mean remains open. Theorem
4(ii)'s normal-form factorization and mean correction, Theorem 1's source
spectral Hamiltonian full native-domain identification, and Theorem 3's
frequency identification remain essential obligations. Theorems 1, 3 and
4(ii)-(iii) as whole statements are still incomplete.

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


## 2026-11-02 — converse action factors and corrected mean-squared recovery

**The converse action clause of Theorem 4(ii) is proved** by
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


## 2026-11-02 — complete Theorem 1 and full native spectral Hamiltonian identification

**Theorem 1 is complete on its original complex Sobolev domains** in
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


## 2026-11-02 — complete commuting physical Gardner action flows

`theorem4_complete_action_flows` now constructs a complete, commuting,
2*pi-periodic Gardner action flow for every positive physical J_n on
the entire original real H1 space. Every trajectory stays real and
continuous in the full H1 norm, and its actual L2 time derivative is
the Gardner vector field of the independent physical Hill contour action.
The spatial derivative in that vector field is the already verified
period-one distribution derivative. No open-gap or nonzero-mean condition
is needed for existence or the equation.

The construction uses opposite original NLS action rotations at n and -n.
The exact inverse Jacobian proves their lifted source derivative equals
the actual Hamiltonian field of I_n-I_-n. Analytic ODE uniqueness proves
independence of the normalized coordinate family and covariance under
component exchange. Consequently the original equal-component diagonal
is preserved. The established Gardner transfer gives the physical scalar
equation. Any competing real H1 trajectory with the same initial value
and this actual L2 equation equals the constructed trajectory.

The group law, pairwise commutation and period are proved for all real
times. Every signed original NLS action, every positive physical mKdV
action and the literal signed mean are conserved. Signed-mean conservation
follows from the proved mean-squared action factor and continuity on the
connected time line; it does not assert global signed-mean recovery from
NLS actions. If the selected physical action vanishes, its entire flow
is stationary. The source flow preserves and reflects all nonnegative
real Sobolev memberships. Its native weighted lift and the scalar flow
are continuous in each full integer H^s norm, including L2; transport
between weights retains the original Fourier coefficients.

These results supply actual action-torus machinery for the remaining
normal forms. They do not identify independent mKdV Birkhoff coordinates.
Theorems 1 and 2 remain complete, as do Theorem 4(i), the converse J_n
and corrected mean-squared clauses of 4(ii), and the angle-action bracket
clause of 4(iii). Forward factorization through J and mean, independent
mKdV angles and the final angle-sum factorization, and the corrected
frequency comparison in Theorem 3 remain essential open obligations.

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


## 2026-11-02 — exact global spectral angle transport and physical action regularity

`theorem4_iii_global_angle_transport` proves the literal phase law along
the complete physical Gardner group. For every positive m,n, every
original real H1 input with J_m!=0 and every real time t, the actual
restricted NLS phase exp(2*i*theta_m) gains the multiplier exp(2*i*t)
when m=n and is constant otherwise. The factor two belongs to the
existing single-valued phase convention; the original angle speed is
the printed Kronecker delta. No open-gap condition is imposed on n.

The shared source theorem works with independently chosen normalized
angular and Birkhoff families. The full original periodic isospectral
data give equality of the canonically labelled gap, so the actual angle
remains defined on the entire real time line. Its analytic phase chain
rule and the proved canonical action bracket give the scalar equation
with constant logarithmic velocity. Actual autonomous ODE uniqueness
then proves the exponential law for every real time. No angular branch
or unproved global angle lift is assumed.

The restricted angle differentials are biorthogonal to the actual
Gardner action vectors. Thus the vectors of every open physical action
are linearly independent, with no restriction on other gaps. A physical
action vector vanishes exactly when that action closes: stationarity
gives one implication, and the actual unit angle-action bracket rules
out the other. The statement includes all closed-action strata.

Physical action cotangents and the mean are also independent. For any
finite collection of open actions, a zero linear combination of their
actual complex Frechet derivatives and the literal zero Fourier
coefficient has only zero coefficients. Applying the physical spatial
Fourier multiplier to the relation kills the mean differential and
produces a relation between the independent Gardner vectors. Evaluation
on the constant Fourier mode then determines the remaining mean
coefficient. This proves the ambient L2 statement for the checked
analytic extensions of the independent physical Hill actions. The
actual Frechet chain rule and dense H1 inclusion prove the corresponding
statement on the entire original H1 domain. Zero mean is allowed.

These results move the remaining coordinate construction beyond bracket
identities to global angle transport and regular physical action strata.
They do not construct an independent global mKdV Birkhoff chart. The
forward restricted-action factorization, independent mKdV angles and
final angle-sum factorization, and the corrected full frequency comparison
in Theorem 3 remain essential open obligations. The overall goal remains
incomplete.

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


## 2026-11-02 — finite local physical action submersions and analytic sections

The actual finite projection records the literal mean and an arbitrary
finite selection of the open physical actions at any original real H1
base point. Its action functionals are the checked complex H1 analytic
extensions of the independent physical Hill contour actions; their base
values are proved to equal those physical actions exactly. Its full
complex Frechet derivative is the assembled row of the actual physical
action derivatives and the bounded mean evaluation.

`theorem4_finite_action_submersion` proves this derivative is surjective.
The preceding independence of action and mean cotangents supplies the
input to a reusable finite-projection theorem: a finite target dual
functional is determined by its values on the coordinate modes, so a
zero dual pullback gives a zero finite cotangent combination and hence
vanishes. Injectivity of the dual map gives surjectivity. A linear right
inverse is constructed, and its finite-dimensional domain makes it
bounded. Neither a submersion nor a right inverse is passed in by a
caller of the physical theorem.

`theorem4_finite_action_sections` constructs local holomorphic H1 sections
of these physical action and mean values. The affine slice through the
constructed right inverse has identity derivative after the physical
projection. The checked analytic inverse theorem on this slice supplies
the actual section. It passes through the original base point, realizes
all nearby selected complex action and mean values exactly, and remains
inside any prescribed open H1 source neighborhood. Its actual derivative
at the base value is precisely the constructed bounded right inverse.
Zero mean is allowed and no condition is imposed on omitted gaps.

This closes a finite local coordinate dependency for the remaining
normal forms. The sections take values in complex H1; real-preserving
sections have not yet been proved. This does not construct an independent
global mKdV Birkhoff chart or settle the infinite action topology or
selected-action collapse. Forward action factorization, independent mKdV
angles and final angle-sum factorization, and the corrected full frequency
comparison remain essential open obligations. Theorems 1 and 2 remain
complete; the overall main-theorem goal remains incomplete.

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


## 2026-11-02 — real-preserving finite physical action sections

`theorem4_real_finite_action_sections` closes the real-preserving local
section dependency left by the preceding complex H1 sections. At every
original real H1 base point, including zero mean, any finite collection
of open positive physical actions together with the literal signed mean
has a constructed local real analytic section. It passes through the
base point, realizes the independent physical Hill contour actions and
the signed zero Fourier coefficient exactly, remains inside any prescribed
open real H1 neighborhood and retains strictly positive selected actions.
There is no restriction on omitted closed gaps.

The reusable weighted Fourier real-form construction uses physical
conjugate reflection, not coefficientwise real Fourier data. This real
subspace is closed and complete with the original weighted norm. A
bounded real-part projection and exact real/imaginary complex
decomposition are constructed and checked coefficient by coefficient.
The physical real-gap formula makes the action projection real on every
real H1 source. Differentiating its imaginary part along real H1 lines
proves that the actual complex action cotangents take real values on
real variations.

`theorem4_real_finite_action_submersion` proves surjectivity of the
actual real Frechet derivative. The physical real part of a complex
right-inverse lift has exactly the same real target: apply each actual
cotangent to the exact complex decomposition and use its proved
real-variation property. This constructs a bounded real right inverse;
none is assumed. The checked real analytic inverse theorem on its affine
slice supplies the local real section. Its actual derivative equals
that constructed right inverse. The target neighborhood is shrunk inside
the positive selected-action cone, without excluding zero mean.

These are finite local real coordinate results. The independent global
mKdV Birkhoff chart, full infinite action topology, collapsed selected-action
coordinates, forward action factorization, independent mKdV angles and
final angle-sum factorization, and corrected full frequency comparison
remain essential open obligations. Theorems 1 and 2 remain complete,
and the overall main-theorem goal remains incomplete.

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


## 2026-11-02 — full native weighted physical action sequence

The infinite action-space map is now constructed, rather than only its
individual analytic coordinates or finite projections. At every integer
Sobolev order s>=0, `miuraSobolevActionSequence s` takes values in the
native weighted l1 target with weight (1+n)^(2s+1). A single open complex
H^s domain contains the whole physical real form and supports the actual
analytic sequence. Its positive coordinates are one-half the literal
NLS Laurent level zero; central and negative entries are zero only as
a representation of the original positive-index target inside Z.

The complex Laurent boundary formula is proved on one common source
ball for all signed noncentral indices and every integer level. It uses
analytic symmetric endpoint cosine means, so it survives a collapsed
complex gap without choosing analytic individual endpoints. Real-source
contour identities and real-form uniqueness identify this mean with the
actual global Laurent contour functions. A real diagonal point inside
a common Cauchy-family ball excludes zero from every noncentral outer
disc, even when the family's chosen center itself is not diagonal.

The uniform reciprocal estimate is geometric. The fixed isolating discs
have bounded radii and centers with bounded displacement from n*pi.
High-index discs give a bound of order 1/(1+|n|); the finitely many low
noncentral discs have a positive distance from zero. Consequently the
actual level-zero action satisfies |I_(n,0)| <= C*|gamma_n|^2/(1+|n|) on
one complex source neighborhood. No action or gap length is divided out.
The checked weighted Hilbert squared-gap bound then controls the full
weighted l1 sequence. Locally bounded analytic sequence realization
upgrades the scalar contour analyticity to Banach analyticity in the
original native Sobolev norm.

`theorem4_mkdv_action_mean_map_analytic` supplies the exact original H1
interface. Every positive coordinate equals the independent physical
Hill contour action, with its factor one half retained. The action
weight is exactly (1+n)^3, and the literal positive-index weighted norm
series is summable. The signed mean pairs with the full action sequence
in one complex analytic H1 map. The actual complete Gardner action
flows conserve that entire weighted action/mean map, not just each
individual coordinate. Zero mean and arbitrary closed gaps are included.

This closes the native infinite action-map/topology dependency. It does
not prove its global inverse geometry or construct the independent
mKdV Birkhoff chart. Forward restricted-NLS-action factorization,
independent mKdV angles and final angle-sum factorization, and corrected
full frequency comparison remain essential open obligations. Theorems 1
and 2 remain complete; the overall main-theorem goal remains incomplete.

The literal printed action-space weight 1+|n|^(2s+1) is supplied as well.
Its comparison with (1+|n|)^(2s+1) has explicit constants 1 and 2^(2s).
`miuraActionTopologyEquiv` is a continuous linear equivalence preserving
every raw coordinate in both directions, and
`native_mkdv_action_sequence_paper_topology` gives the actual analytic
sequence in the printed weighted space. No identification of distinct
norm topologies is left as an assumption.

Validation: all 259 unchanged prefix source hashes match c1ee709; their private outputs were reused. The ten added modules and NLS aggregate compiled with warnings as errors. Targeted and combined transitive audits passed for 3,333 and 48,303 declarations respectively, using only propext, Classical.choice and Quot.sound. The public inventory is 1,707 declarations (1,382 theorems and 325 definitions; aliases and structures excluded), with 271 frozen mathematical source/checker hashes. Pinned cached imports were used; the entire dependency tree was not rebuilt from source.


## 2026-11-02 — actual physical mass trace and zero-action rigidity

The source physical translation frequencies are now derived in the full
rectangular Birkhoff Jacobian: (-2*pi*n*y_n, 2*pi*n*x_n), every signed
n and every original real H1 pair. Open coordinates use actual action
invariance and the normalized angle-momentum cotangent; a collapsed
coordinate stays zero along its entire actual translation orbit. The
angular and Birkhoff families can be independent.

The bounded inverse Jacobian transports the unconditional Hilbert
coordinate expansion into the norm-convergent source identity

    partial_x phi = sum_(n in Z) 2*pi*n*X_(I_n)(phi).

The original diagonal Gardner transfer and pairing positive/negative
indices give the physical scalar identity

    partial_x u = sum_(n>=1) 2*pi*n*Y_(J_n)(u)

with convergence in original L2, not merely coordinatewise. Evaluating
actual cotangents and canceling only a nonzero Fourier frequency gives
the mass cotangent trace at each nonconstant mode. No action or gap
length is divided out.

The first action moment is a bounded functional of the actual native
weighted l1 action map. Its full Banach derivative is an absolutely
convergent scalar action-cotangent series. It agrees with the physical
mass derivative on every original zero-mean H1 tangent, by unconditional
Fourier density. Integrating along every real fixed-mean affine line
and evaluating the constant profile proves

    K1(u) = [u]^2/2 + sum_(n>=1) 2*pi*n*J_n(u).

The native independently defined K1 and the original scalar L2 norm
are identified. Every positive physical action vanishes at a constant;
conversely the trace and Parseval imply that a profile with every
positive action zero equals its literal mean. Thus the zero-action
fiber on every fixed-mean leaf is a singleton. All claims are on the
full original real H1 domain and include zero mean and arbitrary
closed gaps.

This is a global norm/zero-fiber dependency for the missing action
geometry, not a construction of the independent global mKdV chart.
General nonzero-fiber inverse geometry, forward restricted-NLS-action
factorization, independent mKdV angles and final angle-sum factorization,
and full corrected frequency comparison remain essential obligations.
Theorems 1 and 2 remain complete; the overall goal remains active.

Validation: all 269 unchanged prefix module source hashes match 0e4eed8; their private outputs were reused. The twelve added modules and NLS aggregate compiled with warnings as errors. Targeted and combined transitive audits passed for 3,448 and 48,382 declarations respectively, using only propext, Classical.choice and Quot.sound. The public inventory is 1,748 declarations (1,419 theorems and 329 definitions; aliases and structures excluded), with 283 frozen mathematical source/checker hashes. Pinned cached imports were used; the entire dependency tree was not rebuilt from source.


## 2026-11-02 — original L2 mass trace and proper action/mean geometry

The checked L2 prototype is now split into shared native action-sequence,
physical real Fourier-density and endpoint trace modules. The actual
original L2 sequence is analytic in weighted l1 of order one on a complex
neighborhood of the full physical real form. It retains original source
coefficients and all physical H1 Hill-contour coordinates, and pairs with
the literal signed mean. Native K1 on ScalarSobolev 0 is identified with
the original bilinear L2 mass and its convergent actual action moment.

The exact original scalar norm identity and a bound by the full native
action/mean target norm are proved. This bounds source preimages of any
bounded target family. Full target convergence together with coefficient
convergence prevents norm loss and implies strong original L2 convergence.

The weak spectral continuity needed for properness is also proved, without
assuming strong source convergence. Actual indexed endpoints and entire
discriminants converge on bounded Fourier families. Evaluation at moving
cosine gap coordinates gives the arcosh-profile limit, including endpoints
and collapsed gaps. A shared compact joint-limit lemma upgrades this to
uniform convergence on compact parameter sets. Global ordering and zero
in the central gap put every positive diagonal gap strictly to its right.
The inverse-frequency real profile is therefore continuous, and its actual
level-zero Laurent integral converges. Only a nonzero spectral frequency
is inverted; no action or gap length is divided out.

These results construct properness of the actual complete real L2 action
and signed-mean map: every compact set of full native data has compact
preimage in the original L2 topology. In particular every complete fiber
is compact. The proof extracts bounded coefficient subsequences in the
closed physical real Banach form, identifies all actual limiting actions
and the signed mean, then uses the exact trace to obtain strong convergence.
Zero mean and arbitrary collapsed actions are included.

This closes a global compactness dependency, not the independent mKdV
Birkhoff inverse construction. General nonzero-fiber uniqueness, positive
action-cone surjectivity, collapsed Cartesian coordinate geometry, forward
factorization, independent angles/final angle-sum factorization and full
corrected frequency comparison remain essential obligations. Properness
here is in L2; no H1 compactness claim is made. The overall goal stays active.

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

The quotient-descent step through quadratic Cartesian radii and the
signed mean remains essential. The mean must be retained linearly at
zero, rather than squared. A route through the checked finite-head tail
square and tail sum descent keeps its zero Fourier head as a spectator.
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
