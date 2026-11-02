# Actual simultaneous normalized zero families near zero

For each fixed omitted numerator mode n, one constructed open potential
neighborhood now supports an analytic l2 displacement selecting actual
zeros of Psi_n at every other positive index. Their energy values are
analytic and distinct, have the exact free values and solve the literal
normalized entire function, including at a filled critical energy.

**The neighborhood may depend on n.** This proves a local simultaneous
zero-family step toward equation (52). It does not prove completeness of
the zeros, simplicity, real gap placement, the canonical product identity
or prefactor, one common zero neighborhood for all n, the source's full
rough/global domain, or any article main theorem.

## One Hilbert candidate domain

Write mu_k for the selected critical energy (the source's lambda-dot_k,
not its Dirichlet eigenvalue), and xi_k=sqrt(mu_k). The earlier selected
critical family satisfies |xi_k-pi*k|<pi/8 on one common complex potential
neighborhood V.

`ClassicalCandidateZeros.lean` proves xi_k is analytic: the critical
localization places its real part above pi*k/2, so mu_k lies in the
principal slit plane. For a genuine l2 displacement x with ||x||<pi/16,
put

```text
z_k(x,q)=xi_k(q)+x_k, lambda_k(x,q)=z_k(x,q)^2.
```

The domain is one Hilbert ball times V. Every candidate lies in the fixed
closed frequency disc of radius pi/4. `HighEnergyDiscSeparation.lean`
extends the earlier contour estimate throughout both closed discs, giving

```text
|lambda_k(x,q)-mu_m(q)| >= (pi²/4)*|k²-m²|, k!=m.
```

The same disc estimate separates candidate energy values from one another.
All source/mode quantifiers precede these bounds. There is no independent
choice of a displacement radius for each k.

## Analytic resolvent rows and the genuine l2 equation

The compatible twice-weighted inverse supplies the actual coefficient
vector b(q)=n*Q(q)e_n. Its positive coordinates satisfy

```text
b_m/m = (m/n)*(R(q)e_n)_m.
```

The filled zero equation uses the rows

```text
r_k(m)=(lambda_k-mu_n)/(m*(lambda_k-mu_m)), m!=k,n;
r_k(k)=r_k(n)=0, and r_k(m)=0 for m<=0.
```

`PositiveEnergyResolventKernel.lean` proves the uniform row bound by a
positive reciprocal and a translated punctured reciprocal. The actual
row in `ClassicalCandidateResolvents.lean` is genuinely in l2, with norm
at most 64*(1+n²), and jointly Banach analytic on the entire candidate
domain. Every coordinate is proved equal to the literal resolvent;
the total realization's zero fallback is excluded there.

`ClassicalNormalizedZeroMap.lean` defines, for positive k!=n,

```text
G_k=b_n/n+dualPairing(r_k,b),
F_k=((lambda_k-mu_n)/(2*xi_k*k))*b_k
    +x_k*(1+x_k/(2*xi_k))*G_k.
```

The auxiliary coordinates k<=0 and k=n are F_k=x_k. The proved multiplier,
row and coefficient bounds give true l2 membership and a common norm
bound for the actual output sequence. Bounded analytic coordinates then
prove joint Banach analyticity of F. Coordinate analyticity alone is not
used as a substitute for this norm-valued assertion.

## A proved identity derivative and constructed infinite branch

At the free potential b=n*e_n, the omitted row coordinate vanishes and
G_k=1. Thus on the Hilbert ball,

```text
F_k(x,0)=x_k*(1+x_k/(2*pi*k)), k>0, k!=n;
F_k(x,0)=x_k on the auxiliary coordinates.
```

`CoordinateQuadraticDerivative.lean` is the reusable sequence theorem:
given actual Banach differentiability, these coordinate quadratic germs
identify the actual Frechet derivative with the bounded identity map.
`ClassicalNormalizedRootBranches.lean` applies it and proves that the
partial derivative of F in x is the identity at (0,0).

The verified analytic Banach implicit function theorem constructs an
analytic map s_n:U_n->l2, with U_n open, 0 in U_n, U_n subset V,
s_n(0)=0, ||s_n(q)||<pi/16 and F(s_n(q),q)=0. All positive k!=n are solved
simultaneously on this U_n. The auxiliary coordinates of s_n vanish.

## Literal normalized numerator zeros, including filled points

`ClassicalNormalizedZeroIdentity.lean` proves that every retained solved
coordinate is a zero of the actual normalized numerator Psi_n defined
from the same inverse R. Multiplying the scalar equation by 2*xi_k gives

```text
((lambda_k-mu_n)/k)*b_k+(lambda_k-mu_k)*G_k=0.
```

Off the own critical energy, the absolutely convergent actual resolvent
expansion and a proved two-index deletion identity give the result. At
lambda_k=mu_k, separation from mu_n forces b_k=0 and hence the actual
inverse coefficient (R e_n)_k=0. Every other basis numerator vanishes
there by its proved filled factor identity. The actual convergent
normalized numerator series therefore vanishes too. No vanishing factor
is divided out in this case.

`ClassicalNormalizedZeros.lean` proves the analytic energy-family statement,
its exact free energies, distinctness and every actual numerator zero.
`exists_classicalHill_local_normalized_zeros` chooses the common normalized
family first and then constructs U_n and s_n for each omitted n. Every
original actual normalization period is retained on the base V, with
the exact source 1/(2*pi) factor and quadratic Jacobian.

## Validation and remaining source obligations

The focused checker and transitive axiom auditor select 116 modules,
including nine new proof modules and four newly selected existing
sequence/implicit-function dependencies. All are directly recompiled in
dependency order with strict warnings and default heartbeats. Final
counts and checked hashes are in `VALIDATION.md` and `source.json`.

The next obligations are completeness and simplicity of the constructed
normalized zeros, their canonical product with exact prefactor 2/(n*pi),
and the source's required uniformity in omitted n and rough/global
spectral compatibility. Real gap placement and the sharp root estimates
in (54) and the following lemmas remain open. Sharp normalized moments,
physical Hamiltonian-frequency identities, action descent, weighted
asymptotics, compact derivatives and Birkhoff/PDE identification remain
essential. No main-theorem inventory row is closed by this local result.

## Subsequent simple-zero milestone

Simplicity of the selected actual zero family is now proved on a smaller
source neighborhood for each n, retaining the same types of analytic
branch and all actual periods. Its free-lattice spectral displacement is
in l2 and the full signed candidate product is constructed. See
[SIMPLE_NORMALIZED_ZEROS.md](SIMPLE_NORMALIZED_ZEROS.md). Completeness and
the exact canonical product identity of Psi_n, omitted-index uniformity,
rough/global compatibility and all main-theorem rows remain open.
