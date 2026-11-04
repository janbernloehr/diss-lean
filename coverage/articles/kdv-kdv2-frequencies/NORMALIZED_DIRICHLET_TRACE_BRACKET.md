# Actual normalized Dirichlet / discriminant Gardner bracket

This step proves the actual normalized Dirichlet–discriminant bracket
needed for the Abelian-angle calculation preceding Lemma 3.2 (69), PDF
page 26. It includes the removable energy diagonal. It does not prove the
Abelian-angle identity or either article frequency theorem.

## Actual rough trace gradients

`HillL2TraceGradients.lean` constructs the literal continuous scalar
trace-gradient curve from the actual rough fundamental states at frequency
`z`. Its potential-gradient representation holds for arbitrary complex
`q,h : Coeff 2` and every complex energy `b`:

`D_q Delta(q,b)[h] = ∫₀¹ -(hillPhysicalDirection h)₂(x) * g_b(x) dx`.

The source map, physical L2 direction, discriminant and fundamental states
are the existing actual IVP constructions. The proof identifies the scalar
kernel with the negative lower component of the proved physical L2
monodromy gradient and applies the actual Banach-space chain rule. It does
not assume a gradient representation or a spectral model.

The explicit spatial-gradient curve is proved to be the actual spatial
derivative almost everywhere. Both curves agree exactly with the previously
proved continuous-potential kernels under the actual Fourier/state bridge.
Continuity in the source and continuity of the spatial curve in frequency
are proved in the norm of continuous physical curves.

## Physical normalized bracket

For every `q : RealPeriodOneHillPotential`, every positive Dirichlet index
`n`, and every complex energy `b`, let

- `a = nu_n(q)` be the actual labelled Dirichlet energy;
- `D(b)` be the actual Dirichlet characteristic;
- `beta` be the actual endpoint Dirichlet slope at `a`;
- `M` be the actual positive physical Dirichlet mass;
- `r_D(a) = 2*beta - Delta(q,a)` be the already defined sheet root.

The reused shared proofs construct the labelled energies and analytic local
extensions, prove their actual potential derivatives, and show that the
normalized branch gradient is the literal squared state divided by `M`.
The new bracket is the actual unit-interval scalar Gardner pairing

`B_n(b) = ∫₀¹ (A₁(x)^2/M) * deriv(g_b)(x) dx`.

Real period-one Fourier truncations transfer the previously proved actual
continuous boundary identity to these rough states. Norm continuity of the
state curves and the physical integral justifies the limit. The resulting
cross-multiplied identity retains the energy diagonal:

`2*(a-b)*M*B_n(b) = (beta^2-1)*D(b)`.

Using the proved physical normalization `D'(a)*beta=M`, the actual nonzero
slope and actual simple Dirichlet zero, the new theorem proves

`2*(a-b)*D'(a)*B_n(b) = D(b)*r_D(a)`.

The identity `r_D(a)=beta-beta^(-1)` is derived at every actual Dirichlet
zero from the actual scalar Wronskian and trace; it is not a sheet-sign
assumption. Consequently, whenever `a != b`,

`B_n(b) = D(b)*r_D(a) / (2*(a-b)*D'(a))`.

The removable diagonal is filled with its exact signed value:

`B_n(a) = -r_D(a)/2`.

This follows from the actual derivative of `D`, the proved norm continuity
in the square-frequency coordinate, and the cross-multiplied boundary
identity. `QuadraticDividedDifference.lean` handles the punctured square
coordinate including its ramification at zero. No exclusion of zero energy,
open-gap condition, or assumed diagonal value is introduced.

## Reuse and validation scope

Thirty-nine shared files are imported byte for byte from the fixed estimates
snapshot `07d27aaa9471905c4e832ba2229bb75ac79a8c5f`; seven compatible local
variants are retained unchanged. The tenth shared provenance record,
`SHARED_DIRICHLET_NORMALIZATION_IMPORT.json`, records all 46 source/local
hashes. This selectively reuses actual Dirichlet labels, simplicity, mass
normalization, branch derivatives, normalized physical gradients, sheet
root and real period-one truncations. No full branch merge is made.

Validation reuses 527 unchanged previously checked selected sources, strictly
compiles the 39 unchanged selected shared imports and three new proof modules,
and runs a fresh combined transitive axiom audit of all 569 selected modules.
The shared imports were checked in dependency order, followed by the new
modules and the combined audit; no repeated full build is claimed. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. No heartbeat
increase or warning/linter exception is used. Elaborations are split into
separate continuity and finite-approximation lemmas to respect default limits.

Still required are the actual variation of normalized entire differentials
and Abelian angles, the exact angle–discriminant identity with its source
orientation, Hamiltonian frequency identification, weighted estimates and
all full main theorems. No existence of isospectral integral curves or
permission to differentiate a finite-gap pointwise energy equality follows
from these bracket results alone. All main statement inventory rows remain
open.
