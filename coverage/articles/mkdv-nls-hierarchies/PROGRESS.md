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
