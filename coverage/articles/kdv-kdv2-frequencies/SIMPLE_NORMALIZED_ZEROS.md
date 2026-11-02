# Simple actual normalized zeros and the selected signed product

The actual infinite normalized zero families are now simple on one source
subneighborhood for each fixed omitted mode n. The proof uses an exact
filled factor identity and an actually invertible Hilbert partial
derivative. The reflected selected roots have genuine l2 displacement
from the free lattice, and their full signed product converges locally
uniformly with precisely those simple roots.

**The full signed product still includes zero and the omitted +/-n
placeholders. It is not yet identified with the normalized Psi_n product
(52).** Completeness of the Psi_n zero set, the exact canonical prefactor,
a common zero neighborhood for all omitted n, the source's full rough/
global domain and every main theorem remain open.

## Nonvanishing factors throughout the candidate domain

`ClassicalCandidateNumeratorUnits.lean` uses the complete selected signed
critical labeling. Any zero of the actual discriminant energy derivative
inside a positive candidate disc must be the critical root with that
same label: distinct free centers are at least pi apart, while the two
localization radii total less than pi. This holds for complex potentials;
no ZS real-type hypothesis is applied to the Hill pair (-1,-q).

At the filled own critical energy, the numerator equals
`2*k*pi*Delta''(mu_k)` and is nonzero by the actual critical simplicity.
Thus the entire critical basis factor B_k is nonzero throughout its
candidate disc, including the filled point.

`ClassicalNormalizedZeroFactorization.lean` proves, for every candidate
sequence x in the genuine Hilbert ball and every k!=n,

```text
(lambda_k-mu_n)*Psi_n(lambda_k)
  = (2*n*xi_k/k)*B_k(lambda_k)*F_k(x,q),
xi_k=sqrt(mu_k), lambda_k=(xi_k+x_k)^2.
```

This is an exact identity on the whole candidate domain, rather than only
a zero implication. At lambda_k=mu_k the actual convergent numerator
series and its filled factors give the identity directly. Elsewhere the
proved absolute critical resolvent does so. Every displayed factor other
than F_k and Psi_n is proved nonzero there. Here mu_k is the selected
critical energy (the source's lambda-dot_k), not a Dirichlet eigenvalue.

## Actual regularity of the infinite equation

`ClassicalNormalizedZeroDerivative.lean` defines the actual partial map

```text
L(x,q)=D_x F(x,q): l2 -> l2.
```

It is analytic in operator norm, by the proved Banach analyticity of F
and composition of its full derivative with the fixed bounded inclusion.
Its free value is exactly Id. Along the constructed analytic root graph,
the verified operator inversion theorem constructs a two-sided inverse
on a smaller source neighborhood. That neighborhood precedes every
coordinate index; coordinatewise invertibility is not assumed.

The scalar coordinate F_j depends only on x_j and the potential. This
locality is proved through the actual filled resolvent rows, including
their Hilbert realization. Differentiating along each unit coordinate
vector proves that all off-diagonal entries of L vanish. Injectivity of
the actual bounded partial map then forces every diagonal entry nonzero.

`ClassicalNormalizedSimpleZeros.lean` differentiates the exact filled
identity along one candidate-frequency coordinate. If the literal energy
derivative of Psi_n vanished at the constructed zero, the derivative of
the left side would be zero. The right derivative is the product of the
proved nonzero critical factor and the nonzero scalar diagonal of L.
This contradiction proves

```text
Psi_n(lambda_k(q),q)=0,
deriv_lambda Psi_n(lambda_k(q),q) != 0, all k!=n.
```

The argument includes zeros at their own filled critical energies.
`exists_actual_simple_normalized_zero_family` retains the analytic l2
displacement, zero free displacement, exact free energies, distinctness
and vanishing auxiliary coordinates. The public existence theorem
`exists_classicalHill_local_simple_normalized_zeros` constructs the actual
normalized family first, retains every literal normalization period,
and then constructs one simple-zero source subneighborhood for each n.
The potential norm remains the continuous-potential sup norm near zero.

## Genuine free-lattice displacement and signed products

`ClassicalCandidateRootProducts.lean` defines the signed candidate sequence

```text
eta_j=xi_signed_j+x_j-x_(-j).
```

The complete selected critical displacement is already in l2. Reflection
is an existing linear isometry, so eta_j-pi*j is genuinely in l2 as well.
The actual Hilbert radius gives |eta_j-pi*j|<pi/4, hence distinct labels
are distinct roots. If the auxiliary nonpositive coordinates vanish,
eta_k=xi_k+x_k and eta_(-k)=-(xi_k+x_k); eta_0=0. On the actual omitted
root branch, the +/-n entries are the retained critical placeholders.
This reflection is a spectral labeling construction, not a physical
signed Birkhoff-coordinate assertion.

The existing arbitrary-complex spectral product results are applied with
their actual l2 and injectivity hypotheses. They give an entire function,
locally uniform convergence of its literal symmetric finite cutoffs,
its exact zero set {eta_j}, and a nonzero derivative at every such zero.
No real-gap placement is required by the generic theorems used here.
This product is a candidate spectral product; it does not imply that
Psi_n has no additional zeros or fix its canonical product coefficient.

## Validation and remaining source obligations

The strict checker and transitive axiom audit select 123 modules: the
previous 116, five new proof modules, and two newly selected existing
reflection/product dependencies. Every selected source is directly
recompiled in dependency order. The expanded transitive audit covers all
imported NLS declarations. Default heartbeats, strict warnings and the
permitted axioms `propext`, `Classical.choice`, `Quot.sound` are unchanged.
Final checked counts and hashes are in `VALIDATION.md` and `source.json`.

The next product steps must delete the zero and omitted-mode factors,
pass to the energy coordinate, and prove the identity with the actual
normalized Psi_n, including its exact 2/(n*pi) prefactor. The candidate
product's complete zero set does not yet prove completeness for Psi_n.
Real gap placement, sharp root estimates, global/rough compatibility,
sharp normalized moments, physical Hamiltonian-frequency identities,
action descent, weighted asymptotics, compact derivatives and physical
Birkhoff/PDE identification remain essential. No main theorem is marked
verified by this local simple-zero construction.

Subsequent progress: `NORMALIZED_ENERGY_PRODUCTS.md` records the constructed
omitted positive energy product and its exact literal prefactor, complete
simple candidate zero set, actual entire Psi_n quotient and exact free
quotient value one. Constancy and normalization of this quotient at
nonzero potentials, hence the source Psi_n product identity, remain open.
