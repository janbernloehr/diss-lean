# Exact critical derivative and entire basis products near zero

The actual selected critical energies now give the derivative product in
source equation (15), with its exact minus sign and denominators. Removing
the nth factor gives the entire critical basis B_n with prefactor 2/(n*pi).
Both limits are locally uniform on the whole complex energy plane,
including the filled critical energy and zero. **The canonical products of
the normalized functions Psi_n in equation (52) remain open. No main
theorem is marked verified.**

The potential space remains `C([0,1],ℂ)` with its sup norm. The same common
open neighborhood V, cutoff N and selected critical family used by the
infinite normalization construction are retained. The critical energy is
called `classicalHillUniformCriticalPoint N n q` in Lean; write it as mu_n
below for brevity. It corresponds to the source's lambda-dot_n, not the
source's Dirichlet eigenvalue mu_n. No real-type hypothesis is imposed on
the complex Hill coefficient pair (-1,-q).

## Complete selected labeling

`NearFreeCriticalRelabeling.lean` is reusable for the complex coefficient
spaces covered by the existing critical labeling theorem. A selected
actual root within pi/8 of every free center is injective. Each selected
central root belongs to the central root multiset; its cardinality and
multiplicities therefore identify that entire multiset. Distant uniqueness
identifies the tail. This transfers the complete labeling, including its
finite head, and the existing l^p displacement to the selected family.

`ClassicalSignedCriticalProduct.lean` applies this to the exact roots

```text
xi_0 = 0, xi_n = sqrt(mu_n), xi_(-n) = -sqrt(mu_n), n>=1.
```

Their criticality follows from the actual frequency/energy derivative
identity. The previously proved uniform critical localization gives the
required pi/8 estimate. The signed displacement is genuinely in l^2.
The shared discriminant derivative product theorem then identifies its
entire product and locally uniform symmetric cutoffs with
`2*z*Delta'_q(z²)` for precisely this labeling.

## Positive energy product and its omitted factor

`ClassicalCriticalEnergyProduct.lean` pairs the positive and negative
factors in each finite symmetric cutoff. The zero frequency contributes
the exact minus sign. For every q in V,

```text
Delta'_q(lambda) = lim_(M->infty)
  - product_(1<=m<=M) (mu_m(q)-lambda)/(m²*pi²).
```

`critical_energy_product` proves locally uniform convergence on all of C;
`critical_energy_product_at` records every pointwise limit.
`SquareProductConvergence.lean` supplies the reusable descent argument:
local square-root charts give convergence away from zero, and the proved
entire-limit removal theorem fills zero. This does not restrict energy to
a particular branch cut or leave convergence at the ramification point
as an assumption.

`ClassicalCriticalBasisProduct.lean` proves

```text
B_n(lambda,q) = lim_(M->infty)
  (2/(n*pi))*product_(1<=m<=M, m!=n) (mu_m(q)-lambda)/(m²*pi²).
```

The exact finite identity, once M>=n, is

```text
(lambda-mu_n)*basisPartial_n = (2*n*pi)*energyPartial.
```

The existing filled numerator identity identifies the limiting product
with the actual B_n. `RemovableFactorConvergence.lean` proves the reusable
locally uniform cancellation of a fixed linear factor for entire
sequences. Thus `critical_basis_product` includes lambda=mu_n, rather
than just asserting the quotient formula off its own critical root.

`exists_classicalHill_critical_products` selects N and an actual open V
containing zero before every potential q and positive index n. It proves
both whole-plane product limits there by the constructed all-contour data;
it has no unproved spectral-data hypothesis.

## Scope and remaining source obligations

These are actual products, with complete selected zeros and proved
locally uniform convergence. They prove equation (15) on the current
continuous-potential neighborhood of zero and identify the critical
basis used in the constructed infinite normalization. They do not yet
supply the source's entire rough-potential domain or globally prescribed
spectral labels/cycles.

At a nonzero potential the normalized Psi_n is an inverse-period-column
combination of the B_m. Its zeros need not be the critical energies.
Identifying those zeros and proving equation (52) remain separate
obligations. The source's sharp moment estimates, Hamiltonian frequency
identities, action descent, weighted asymptotics, compact derivatives and
physical Birkhoff/PDE identification also remain essential.

The strict focused checker selects 90 modules, including the six new
proof files and six newly selected existing dependencies. All selected
files are directly recompiled before their consumers. The auditor checks
all imported NLS declarations and permits only `propext`,
`Classical.choice` and `Quot.sound`. Final results and checked hashes are
recorded in `VALIDATION.md` and `source.json`.
