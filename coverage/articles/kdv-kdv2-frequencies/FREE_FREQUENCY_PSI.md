# Actual free normalized frequency differentials

This milestone constructs an entire free numerator basis and proves its
period normalization and collapsed-gap moments. It uses the actual free
Hill discriminant and canonical root sheet. **No main theorem is marked
verified.** Deformation to nonzero potentials, the source's canonical
product representation, sharp uniform spectral estimates and action
identification remain required.

## Shared integration

The article branch now merges `articles/kdv-convexity` through
`ecd010969f63e6b8af8f6ed5aaa1dc571fa7e503`, retaining ancestry. In addition
to the previously imported actual Hill trace and local charts, that commit
constructs the free normalization, continuous scalar Hill flow, Floquet
spectral identification on the interval, and a source-segment continuation
of the primitive and its root. The continuation domain explicitly avoids
actual branch points along the whole straight potential segment; it is
not yet proved to cover all the source's canonical gap complements.

The new frequency proof directly consumes `ClassicalFreePrimitive.lean`.
It does not redefine the actual discriminant or its primitive, and does
not substitute the zero ZS pair for the scalar free Hill potential.
The latter is the triangular pair `(-1,0)`, whose actual trace was computed
by the shared IVP proof. The upstream shared coverage records are imported
historical snapshots; this article's records describe the integration.

## Defined entire numerator and exact constants

All declarations below are in `NLS/KdV/FreeFrequencyPsi.lean`, namespace
`NLS.KdV`. For every positive integer n, define

```text
lambda_n = (n*pi)^2,
psi_n(lambda) = 2*n*pi * dslope(Delta'_0, lambda_n, lambda),
F_k(lambda) = -i*sqrt(lambda) + i*k*pi.
```

`dslope` is the divided difference with its actual derivative value at the
center. It makes psi an entire function; no zero value from total division
is used at the omitted mode. The discriminant here is the constructed
`classicalHillDiscriminant 0`, not a supplied analytic function.

The following exact formulas are proved:

```text
(lambda-lambda_n)*psi_n(lambda) = 2*n*pi*Delta'_0(lambda),
Delta'_0(lambda_n)=0,
Delta''_0(lambda_n) = -(-1)^n / (2*(n*pi)^2) != 0,
psi_n(lambda_n) = -(-1)^n/(n*pi) != 0,
psi_n(lambda_k)=0 for k!=n.
```

On the energy slit plane, away from lambda_n and the root zeros,

```text
r_0(lambda) = -2*i*sin(sqrt(lambda)),
psi_n(lambda)/r_0(lambda)
  = (-i*n*pi/sqrt(lambda))/(lambda-lambda_n).
```

The zero-potential root and primitive have exactly the same sign and
normalization as the shared free-normalized continuation. The nonzero
Delta'' formula also proves the critical-point nondegeneracy needed to
deform this basis away from zero; such a deformation is not asserted yet.

## Actual isolating contours and period equations

`exists_freeHill_isolating_disc` proves that every lambda_k has a positive
isolating radius with its closed disc in the slit plane and with no root
zero off the center. Isolation is derived from the explicitly nonzero
derivative of the actual free root, using its continuous divided difference.
It is not a supplied spectral hypothesis.

`exists_classicalHillFreePsi_periods` then proves that one such radius R_k
works for every output index n, simultaneously:

```text
integral_(C(lambda_k,R_k)) psi_n/r_0 = 2*pi*delta_nk.
```

All other free energies lie outside the closed disc; that is proved using
the root zeros and injectivity of the positive energies. The diagonal
period follows from Cauchy's integral formula and the residue -i; all
off-diagonal periods vanish by Cauchy's theorem. Circles have the source's
counterclockwise orientation, giving positive `2*pi` on the diagonal.

`classicalHillFreePsi_positive_moment_eq_zero` proves, for every n,k and
every m>=0, that the integral of `F_k^(m+1)*psi_n/r_0` vanishes on those
circles. The diagonal differential can have a pole, but its weighted
Cauchy integral is zero because `F_k(lambda_k)=0`. The argument does not
assume the unweighted diagonal quotient is analytic inside the disc.

`classicalHillFreeFrequencyRadius` chooses such a radius for every k.
`classicalHillFreeFrequencyMoment` defines the literal actual free contour
integral, and its theorems `classicalHillFreeFrequencyMoment_zeroth` and
`classicalHillFreeFrequencyMoment_positive` establish the above normalized
zeroth moments and every positive vanishing moment without contour or
spectral assumptions.

## Scope relative to the source and main theorems

The normalization is source equation (53), p. 21, and the free moment
properties are the normalization and collapsed-gap requirements used in
Lemma 3.1, pp. 25–26. These are an explicit entire period-normalized free
basis. The source's product representation (52) has not yet been proved
identical to this construction, and uniqueness among unconstrained entire
functions is not inferred merely from the periods. Nor does a free-potential
calculation establish the analytic frequency maps on rough potential or
action spaces. These qualifications remain explicit.

Next requirements include an actual analytic critical-point/numerator
deformation, construction of the infinite normalized period family, global
canonical normalization and rough-potential compatibility, sharp moment
bounds to instantiate the proved analytic summation theorems, and the
physical Hamiltonian/frequency and Birkhoff-flow identities. The full main
inventory remains open.

## Validation

The focused frequency checker now compiles 23 selected modules, adding
the shared free primitive and the new free numerator/moment module. Its
transitive audit covers every selected declaration, including generated
and private constants, and all imported NLS declarations. Counts and final
status are recorded in `VALIDATION.md` and `source.json`.
The updated shared checker is also rerun in this worktree, with a separate
private build directory. Both expensive runs use the shared build lock;
canonical sources and build products stay read-only.

Final validation passes for all 23 selected frequency modules with both
strict options and default heartbeats. The transitive audit passes for
404 selected declarations and 2002 declarations including imported NLS
dependencies. The shared integration recheck passes its 20 modules,
positive-index example and 269-declaration transitive audit. Only the
standard `propext`, `Classical.choice` and `Quot.sound` axioms are allowed.
