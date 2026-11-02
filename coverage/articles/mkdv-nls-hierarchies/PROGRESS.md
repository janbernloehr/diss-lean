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
