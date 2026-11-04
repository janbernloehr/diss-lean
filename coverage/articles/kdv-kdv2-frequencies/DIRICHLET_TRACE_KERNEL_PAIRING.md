# Actual Dirichlet / monodromy-kernel boundary pairings

Subsequent progress: `ACTUAL_GARDNER_TRACE_INVOLUTION.md` now records the
proved actual potential-derivative representation and scalar Gardner trace
involution. The remaining-step descriptions below record this earlier milestone;
the normalized Dirichlet/angle and frequency identities still remain open.

This is a necessary scalar Hill calculation toward the missing physical
angle–discriminant bracket used before formula (69) in Lemma 3.2 (PDF page
26). It does not yet identify the monodromy kernel with the potential
Frechet derivative of the discriminant, and proves no main theorem.

For a continuous complex potential `q`, let `A` be the actual scalar Hill
state at energy `a` with initial data `(0,1)`, and assume only that its
position vanishes at 1. Let `B,C` be actual states at any second complex
energy `b`, with arbitrary initial data `v,w`. The new reusable module
`ClassicalHillDirichletBoundaryPairing` proves

- `4*(a-b)*∫₀¹ A₁²*B₁*B₂ = A₂(1)²*B₁(1)² - v₁²`;
- `2*(a-b)*∫₀¹ A₁²*(B₁*C₂+B₂*C₁) = A₂(1)²*B₁(1)*C₁(1) - v₁*w₁`.

Both are cross-multiplied identities, valid also at `a=b`. The proofs use
the actual IVP derivatives, the derivatives of products of Wronskians and
positions, and interval integration. Neither an assumed differential
equation model nor a supplied endpoint pairing replaces the actual flow.

`ClassicalHillTracePairingKernel` proves that the actual scalar fundamental
matrix has endpoint determinant one. Writing `c,s` for its fundamental
positions at energy `b`, it constructs the literal quadratic kernel

`g_b(x) = s(1)*c(x)^2 + (s'(1)-c(1))*c(x)*s(x) - c'(1)*s(x)^2`.

It proves the spatial derivative of this kernel and combines the squared
and mixed boundary identities with determinant one to prove

`2*(a-b)*∫₀¹ A₁(x)^2*g_b'(x) = (A₂(1)^2-1)*s(1)`.

The result is available both with the explicit derivative expression and
with Lean's actual `deriv` of the kernel. A quotient corollary assumes only
`a≠b` in addition to the actual Dirichlet endpoint condition. All constants,
endpoint terms and energy signs are explicit.

Remaining physical steps include proving the actual potential-derivative
representation by `g_b`, the genuine Dirichlet mass normalization in the
same construction, the normalized entire interpolation/angle identity,
and Hamiltonian frequency identification. The finite-gap energy identity
alone does not justify differentiation in arbitrary potential directions.
All main statement inventory rows remain open.

Validation reuses 521 unchanged previously checked selected modules,
strictly compiles these two new modules at the default resource limits,
and runs a fresh combined transitive axiom audit of all 523 selected
modules. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
No new imports from other branches, heartbeat changes, warning exceptions,
or linter exceptions are introduced. Source hashes, matching selections,
compilation evidence, nine existing provenance records, private outputs,
and unchanged clean canonical main are verified before publication.
