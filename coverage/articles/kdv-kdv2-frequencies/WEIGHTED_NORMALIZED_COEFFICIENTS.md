# Actual one-weight control of normalized coefficients

The constructed infinite normalized entire family now has an actual
one-index-weight l2 coefficient estimate on a common neighborhood of zero.
This is a decay step toward identifying its zeros and the source product
(52); it does not yet prove that product or any article main theorem.

## Retaining the sharper actual period estimate

For positive numerator index n and contour index k, the already proved
integration-by-parts estimate retains

```text
|P_nk(q)| <= (20/pi)*A*n*k/|k²-n²|², n!=k.
```

`ClassicalWeightedPeriodOperator.lean` multiplies the matrix entry by k/n.
The remaining kernel satisfies

```text
(k/n)*(n*k/|k²-n²|²)
  = (k/(k+n))²/|k-n|² <= 1/|k-n|².
```

The diagonal is unchanged. Thus the weighted matrix has a common
summable reciprocal-square majorant, including all low positive modes.
The existing bounded-matrix assembly constructs an actual bounded
operator S on l2, with those exact rescaled integral entries and bound
`5*((80/pi)*A+1)`. Its operator-norm analyticity is proved from the
analytic entries and this common bound. At zero it is the identity.
No bounded action of an unbounded index multiplier is assumed.

## Compatible actual inverses

`PositiveIndexWeight.lean` defines w_m=m for m>0 and w_m=1 otherwise.
Its reciprocal is a bounded symbol. `DiagonalIntertwining.lean` proves
that a matrix identity on coordinate vectors gives actual bounded
operator intertwining, and that the intertwining passes to inverses.
These statements are reusable on every finite Banach sequence exponent.

Let J be the bounded reciprocal-weight multiplier. For the actual period
operator T and the constructed weighted operator S, the exact entry
identities give

```text
T J = J S.
```

`AnalyticOperatorInverse.lean` is a reusable local inversion theorem for
an operator-norm analytic family equal to the identity at zero. The
Neumann criterion constructs a neighborhood with an analytic two-sided
inverse, exact free identity and inverse norm at most two.

`ClassicalWeightedPeriodInverse.lean` applies it to S and intersects
neighborhoods with the already constructed inverse R of T. Writing Q for
the inverse of S gives `R J = J Q`, hence, for every integer m,j,

```text
w_m*(R(q)e_j)_m = w_j*(Q(q)e_j)_m.
```

The proof retains the actual unweighted and weighted matrix entries,
both two-sided inverse identities, both norm bounds and the identical
selected critical/numerator/contour data. All four operator families are
analytic on one selected open complex potential neighborhood.

## Genuine weighted coefficient errors

`ClassicalWeightedNormalizedCoefficients.lean` constructs the actual
l2 vector

```text
C_n(q) = n*(Q(q)e_n-e_n), n>=1.
```

The preceding inverse identity proves each literal coordinate equals

```text
C_n(q)_m = w_m*((R(q)e_n)_m-(e_n)_m).
```

Consequently that literal weighted error sequence belongs to l2. The
realization is Banach analytic in q, equals zero at q=0, and satisfies

```text
||C_n(q)||_2 <= n*||Q(q)-Id||.
```

For every epsilon>0 there is one open neighborhood U containing zero,
chosen before n, on which `||C_n(q)||_2 <= epsilon*n` for all n>=1.
This follows from the actual operator-norm continuity of Q at its proved
free identity, rather than from separate coordinate limits.

`exists_classicalHill_weighted_normalized_differentials` combines these
controls with the actual normalized numerators Psi_n. They remain jointly
analytic and retain every literal fixed-frequency-circle normalization
period, with the exact source 1/(2*pi) factor and Jacobian. The same R is
used in the coefficient identities and the normalized entire functions.
The nonpositive auxiliary identity block is not identified with physical
signed Birkhoff coordinates.

## Remaining obligations and validation

This one-weight estimate is not the two-weight control needed for the
next uniform zero-location argument. An additional index weight, the
complete normalized zero sequence, its product normalization (52), and
global/rough spectral compatibility remain open. The next weighted matrix
is not covered merely by the present convolution bound; its extra
far-off-diagonal part needs a separate bounded-operator estimate.

Sharp normalized moments, physical Hamiltonian-frequency identities,
action descent, weighted frequency asymptotics, compact derivatives and
Birkhoff/PDE flow identification remain essential. Every main-theorem
inventory row remains open.

The focused checker directly recompiles 96 selected modules in dependency
order, including the six new proof modules. Strict warnings, default
heartbeats and the restriction to `propext`, `Classical.choice` and
`Quot.sound` are unchanged. The complete transitive audit and checked
source hashes are recorded in `VALIDATION.md` and `source.json`.
