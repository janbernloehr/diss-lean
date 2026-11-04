# Actual Hill discriminant gradient and Gardner trace involution

Subsequent progress: `NORMALIZED_DIRICHLET_TRACE_BRACKET.md` records the
actual rough normalized Dirichlet/discriminant bracket, its source quotient
and filled diagonal. The remaining-step descriptions below record this
earlier milestone; the Abelian-angle and frequency identities remain open.

This step proves necessary physical variational input toward the angle–
discriminant bracket used before Lemma 3.2 (69), PDF page 26. It does not
assert that angle identity, the Hamiltonian frequency formula, or any main
theorem of the article.

## Actual potential derivative

For every continuous complex potential `q`, every continuous complex direction
`h`, and every complex energy `b`, `ClassicalHillDiscriminantGradient` proves

`D_q Delta(q,b)[h] = ∫₀¹ g_b(x)*h(x) dx`,

where `Delta` is the actual scalar Hill IVP discriminant and

`g_b = s(1)*c² + (s'(1)-c(1))*c*s - c'(1)*s²`.

The scalar `c,s` are the actual normalized fundamental solutions at energy
`b`. The proof identifies the scalar kernel with the negative lower component
of the dissertation's proved actual first-order discriminant gradient, using
the actual constant-upper state transformation and fundamental-column
linearity. The affine potential derivative and the complex Banach-space chain
rule give the asserted derivative in every continuous potential direction.
All energies, including zero, are covered by the proved square-coordinate
independence. Neither the gradient representation nor a spectral model is
assumed.

For an actual Dirichlet solution `A` at energy `a`, define the continuous
direction `H_a = (A₁²)' = 2*A₁*A₂`. With only `A₁(1)=0`, it has mean zero and
satisfies the exact actual source variation

`2*(a-b)*D_q Delta(q,b)[H_a] = -(A₂(1)^2-1)*s(1)`.

This retains the diagonal `a=b`. It is an unnormalized Dirichlet squared-state
direction, not yet a normalized Dirichlet eigenvalue or angle bracket.

## Actual Gardner trace involution

`ClassicalHillGardnerTraceInvolution` adds the actual velocity quadratic form
`j_b = s(1)*(c')² + (s'(1)-c(1))*c'*s' - c'(1)*(s')²`.
Writing `h_b = g_b'`, the actual IVP proves the closed differential system

`g_b' = h_b`, `h_b' = 2*j_b + 2*(q-b)*g_b`, `j_b' = (q-b)*h_b`.

All three functions have matching values at 0 and 1; this follows from the
actual monodromy and determinant one, and requires no endpoint condition on
`q`. The proof differentiates an explicit concomitant built from the two
energies. Its matching endpoint values give

`∫₀¹ g_a(x)*g_b'(x) dx = 0`

for all pairs of complex energies. The proof treats coincident energies by
the derivative of `g_a²`; off the diagonal it cancels the proved nonzero
energy factor. There is no derivative of `q` and no smoothness assumption.
The result is available with both the explicit derivative expression and
Lean's actual spatial `deriv`.

The continuous trace Gardner direction `X_b = g_b'` is proved to have mean
zero. The actual potential derivative representation then proves

`D_q Delta(q,a)[X_b] = 0`

for every continuous complex `q` and all `a,b`. This is the actual scalar
Gardner spatial pairing. No NLS symplectic bracket is substituted for it,
and no existence of an isospectral integral curve is inferred solely from
this infinitesimal identity.

## Reuse, validation, and remaining scope

The existing dissertation files `ClassicalForcedKernel` and
`ClassicalDiscriminantGradient` were already transitive dependencies of the
previous selected development. Their only changes remove their old
`maxHeartbeats 400000` overrides. Both now compile strictly under the default
resource limits and are explicitly selected before their existing consumers.
`CANONICAL_TRACE_GRADIENT_REUSE.json` records the original canonical and
current hashes. No mathematical declaration or proof in those two helpers
is changed, and no branch import is added.

Validation reuses 523 unchanged previously checked selected sources, strictly
compiles the two helper files with their resource overrides removed and the
two new scalar Hill proof modules, and runs a fresh combined transitive
axiom audit of all 527 selected modules. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. Selected dependency order, compilation evidence,
source and reuse hashes, nine unchanged shared-import records, private fresh
outputs, and unchanged clean canonical main are checked before publication.

Still required are the actual normalized Dirichlet derivative/mass and sheet
normalizations in the same construction, variation of the normalized entire
differentials and Abelian angles, the exact angle–discriminant identity, and
physical Hamiltonian frequency identification. The finite-gap energy equality
is still not an identity on a complex-open potential ball and cannot simply
be differentiated in arbitrary source directions. All main statement
inventory rows remain open.
