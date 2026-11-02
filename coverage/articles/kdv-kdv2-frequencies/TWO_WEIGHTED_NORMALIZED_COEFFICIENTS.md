# Two-weight normalized coefficients and critical resolvents

The actual normalized inverse columns now have two index weights in l2.
Their literal positive residue coefficients are genuinely in l1 and
Banach analytic. The normalized entire functions have an absolutely
convergent critical resolvent expansion away from the selected critical
energies. These are inputs to the normalized zero equations; **the zeros,
canonical product (52), full rough/global version and every main theorem
remain open.**

The potential space is still `C([0,1],ℂ)` with the sup norm, near zero.
All operators and spectral data below are constructed on one common open
complex potential neighborhood. No real-type assumption on (-1,-q) is used.

## A bounded matrix with the required second weight

For positive numerator index n and contour index k, retain the actual
integration-by-parts bound C*n*k/|k²-n²|². Conjugating by the square of the
positive index gives the kernel

```text
(k/n)²*n*k/|k²-n²|² = k³/[n*(k+n)²*(k-n)²].
```

When k<=2n it is at most 2/|k-n|²; when k>2n it is at most 4/(n*k).
`positiveIndex_twoWeighted_squared_energy_kernel_le` proves the combined
bound. The previous one-weight kernel lemma is made public and reused.
The additional far tail cannot be discarded as a convolution l1 kernel.

`RankOneDominatedMatrix.lean` proves that an arbitrary matrix dominated
by |u_m|*|v_n| for u,v in l2 defines an actual bounded Hilbert operator,
with norm at most ||u||*||v||. Each actual row is in l2; Hilbert duality
and the u bound give actual output membership and the operator norm.

`MixedMajorantMatrix.lean` combines this with the existing convolution
construction. A bounded l-infinity matrix symbol assembles linearly into
an operator whose entries are that symbol times

```text
|b_(m-n)| + |u_m|*|v_n|.
```

The assembly norm is at most ||b||_1+||u||_2*||v||_2. Analytic scalar
entries with a common combined majorant therefore give actual operator-
norm analyticity by the proved bounded-coordinate analytic realization.
All memberships and entries are proved; no formal matrix action is assumed.

`ClassicalTwoWeightedPeriodOperator.lean` applies this to twice the
reciprocal-square kernel and twice the punctured reciprocal Hilbert
sequence in each outer-product factor. The majorant has total norm at
most 26. It constructs the actual twice-weighted period map S with

```text
S_kn = (k/n)²*P_nk, k,n>0,
||S(q)|| <= 26*((80/pi)*A+1), S(0)=Id.
```

The complementary nonpositive block remains the auxiliary identity.
Every low and high positive mode uses the identical actual contour data.

## Exact inverse columns and genuine weighted errors

`PositiveIndexPowerWeight.lean` supplies a bounded reciprocal of every
power of w_m=m for m>0 and w_m=1 otherwise, and a genuine l2 positive
reciprocal sequence of norm at most two.

`ClassicalTwoWeightedPeriodInverse.lean` constructs simultaneous analytic
inverses R of the actual period map T and Q of S. Both inverse norms are
at most two on a smaller common neighborhood. The bounded reciprocal-
square diagonal J gives T J=J S and R J=J Q, hence the literal identity

```text
w_m²*(R(q)e_j)_m = w_j²*(Q(q)e_j)_m.
```

`ClassicalTwoWeightedNormalizedCoefficients.lean` constructs

```text
E_n(q)=n²*(Q(q)e_n-e_n),
E_n(q)_m=w_m²*((R(q)e_n)_m-(e_n)_m).
```

Thus the actual weighted error belongs to l2, is Banach analytic in q,
vanishes at zero and has norm at most n²*||Q(q)-Id||. For every epsilon>0,
one open neighborhood controls all errors by epsilon*n², before all n.
The existence theorem retains the same R in the jointly analytic
normalized entire family and every literal normalization period.
This does not assert an n-independent bound on unscaled zero displacements.

## Summable residues and the actual entire-function identity

`ClassicalNormalizedResidues.lean` constructs an l1-valued analytic
residue sequence by Hilbert Holder multiplication of the positive
reciprocal sequence with n²*Q(q)e_n. Its literal positive coordinates are

```text
c_m^n(q)=m*(R(q)e_n)_m, m>=1;
```

its nonpositive coordinates vanish. The positive norm sum is finite.
The quadratic critical energy growth gives a bounded reciprocal sequence
`1/(lambda-mu_m(q))` for each fixed energy, by an explicit finite head and
uniform tail estimate. Consequently the literal critical resolvent series
is absolutely convergent.

Using the already proved entire numerator factor identity and the actual
positive-index normalized series gives, away from every critical energy,

```text
Psi_n(lambda,q) = 2*pi*Delta'_q(lambda) *
  sum_(m>=1) c_m^n(q)/(lambda-mu_m(q)).
```

Here mu_m denotes the selected critical energy (the source's lambda-dot_m),
not the source's Dirichlet eigenvalue. The formula uses precisely the R
whose weighted coefficients were constructed. It does not equate critical
energies with the different zeros of the normalized Psi_n.

## Validation and remaining scope

The strict checker and transitive axiom audit select 103 modules. Seven
new proof files and the public one-weight kernel dependency are directly
recompiled. Default heartbeats, strict warnings and the permitted axioms
`propext`, `Classical.choice`, `Quot.sound` are unchanged. Checked hashes
and final counts are in `VALIDATION.md` and `source.json`.

Simultaneous normalized zero equations and their complete zero/product
identification, including the exact product prefactor 2/(n*pi), remain
next. Sharp normalized moments, physical Hamiltonian-frequency identities,
action descent, rough/global compatibility, weighted frequency asymptotics,
compact derivatives and Birkhoff/PDE identification remain essential.
No main-theorem inventory row is closed by these coefficient/resolvent results.
