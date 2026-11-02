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
