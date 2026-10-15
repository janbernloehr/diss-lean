# Section 17 original-family audit

Source: printed pp. 78–81, Propositions 17.1–17.3, Lemmas 17.4–17.5,
and equation (3.9). `sourceSection17_original` constructs the package for
every finite p>1, retaining the original normalized root family and angles.
D below denotes `SourceSection17OriginalData`; H denotes
`D.toSourceSection16OriginalData`. The angular domain W and compatible
map domain V⊆W are unchanged.

| Source assertion | Public evidence | Scope |
| --- | --- | --- |
| Proposition 17.1: local diffeomorphism | `D.proposition17_1` | Actual real map, every real source, all finite p>1; analytic local inverse, both inverse identities, and exact strict derivative of the inverse |
| Ambient complex local inverse | `D.complex_localInverse` | Both local inverse identities in the complex coefficient spaces at each real source, with exact inverse derivative |
| Canonical images in the proof of Proposition 17.1 | `H.jacobian_hamiltonian_coordinates`, `H.normalizedJacobian_hamiltonian_coordinates` | Actual coordinate cotangents and Hamiltonian directions for p≥2; corrected x/y swap after normalization |
| Proposition 17.2: injectivity | `D.proposition17_2` | Entire real source space, all finite p>1 |
| Proposition 17.3: surjectivity | `D.proposition17_3` | Entire real target, 1<p≤2 |
| Global analytic inverse | `D.global_inverse` | Homeomorphism equal to the original map, analytic in both directions, with inverse derivative at every target; 1<p≤2 |
| Equation (3.9) | `H.equation3_9` | Actual Hilbert Jacobian applied to the original theta Hamiltonian; both rectangular components have the inward sign |
| Lemma 17.4 | `H.lemma17_4` | Unique C¹ Hilbert flow on (−∞,Iₖ(φ)), selected action tending to zero, and continuous real-type displacement in every finite exponent r>1 |
| Exact action law | `H.angleFlow_action_law` | For the explicit lifted flow, Iₙ(t)=Iₙ(0)−t when n=k and Iₙ(t)=Iₙ(0) otherwise, including negative times before collapse |
| Collapse endpoint | `H.angleFlow_collapse` | Source-norm limit exists at t=Iₖ(φ), and the selected original periodic gap is closed there |
| Finite flow reductions used in surjectivity | `D.complex.exists_hilbertActionReductionSequence_small_actions`, `D.complex.hilbertActionReductionSequence_mem_exponent_iff` | Constructed admissible moves, arbitrarily small selected actions, unchanged outside coordinates, and unchanged membership in any stronger exponent space |
| Compact action tori | `D.lemma17_5` | Compact in the actual target norm for every finite p>1 |
| Lemma 17.5(i) | `D.lemma17_5` with p≤2 | Actual isospectral image equals the whole original action torus; source isospectral set is compact |
| Lemma 17.5(ii) | `D.lemma17_5` | Isospectral image is contained in the original action torus for every finite p>1, including p>2 |

## Invertibility and injectivity

At p≥2 the actual coordinate Hamiltonians lie in the source space.
Canonical brackets give preimages for every output mode: the negative
y Hamiltonian maps to a positive x mode, and the x Hamiltonian maps to a
positive y mode. Finite output truncations then prove dense range.
The compact perturbation result from Section 16 and the Fredholm
alternative imply that the actual derivative is bijective. At p<2,
exponent compatibility transports a kernel vector into the Hilbert
source space, where injectivity kills it; the Fredholm alternative then
gives surjectivity. The proof does not treat an arbitrary Holder-conjugate
gradient as a source direction below exponent two.

Both real and complex inverse function theorems apply to the actual
Jacobian. The reported inverse derivatives are the inverse bounded
linear equivalences at the recovered source. The global inverse for
p≤2 is analytic on the entire target, and commutes with exponent inclusion
between independently constructed packages in that range.

For global injectivity above two, two hypothetical preimages are first
replaced by an actual finite-gap collision using their local inverse
charts. Finite-gap regularity supplies distinct Hilbert preimages with
the same output, contradicting the proved Hilbert injectivity. Below two,
direct exponent inclusion suffices. This fills in the regularity step
behind the source's sketch of restricting both inverse charts to Hilbert
space; mere openness of their intersections would not supply the needed
Hilbert preimages.

## Original angle flow and surjectivity

The explicit Hilbert flow is the inverse Birkhoff image of the radial
coordinate curve that multiplies the selected coordinate pair by
sqrt(1−t/Iₖ(φ)). Every unselected coordinate is unchanged. Its derivative
is the original theta Hamiltonian for the same s as the map, by the
canonical brackets and the original angle differential identity.

Only the selected initial gap must be open. The solution exists uniquely
on the full interval (−∞,Iₖ(φ)); other gaps may be collapsed. The original
selected action is exactly Iₖ(φ)−t. The source curve extends continuously
to the endpoint, where that gap closes; no C¹ assertion at collapse is
made. The displacement, rather than the initial source itself, has a
continuous realization in every finite exponent r>1. Below two this uses
the stronger angle vector and its Bochner integral; above two Hilbert
inclusion suffices. The additional angle families used to prove this
regularity are constructed internally.

Finite admissible moves make any prescribed finite set of actions
arbitrarily small, without changing any outside rectangular coordinate.
Their total displacement belongs to each finite exponent above one.
Applied to a Hilbert preimage of a p-target with p<2, these moves place
the output in a small ball covered by the original p-map. Hilbert
injectivity identifies the reduced source with its p-preimage. The
stronger-space displacement then recovers p-membership of the original
Hilbert preimage, proving surjectivity. All cutoffs use explicit finite
sets, so the tail estimate matches the actual selected indices.

## Isospectral meaning

`sourceIsospectralSet` uses the original periodic spectrum and its
algebraic multiplicities. This condition is proved equivalent to equality
of the original normalized discriminant, and hence defines a closed set.
Equal spectral data give equal original indexed actions, proving the
torus inclusion at every finite p>1.

In Hilbert space, finite action rotations lift to isospectral sources
and are dense in the full coordinate torus. Continuity of the global
inverse and closedness of the actual isospectral set give the reverse
inclusion. Exponent compatibility transfers this equality below two.
The global inverse maps the compact torus to the source isospectral set,
proving compactness for 1<p≤2. Equality and source compactness for p>2
are not asserted by this milestone.

## Two checked source corrections

The first canonical-image display in Proposition 17.1's proof, printed
p. 78, gives A K bₘ±=−d₋ₘ±. The actual formula swaps the labels:
A K bₘˣ=−d₋ₘʸ and A K bₘʸ=−d₋ₘˣ. The source's following pairing display
already uses the opposite label. `H.normalizedJacobian_hamiltonian_x_ne_printed`
proves that the unswapped x formula is false at every real source for p≥2.

Equation (3.9), printed p. 80, has a positive x-component and negative
y-component. Both components must be negative. For every original Hilbert
package, `H.equation3_9_printed_sign_counterexample` constructs an actual
real source with x₀=1 and y₀=0. Its true x₀ velocity is −1, while the printed
expression evaluates to +1. The source is supplied by the proved global
inverse; realizability is not a premise. These corrections preserve the
numbered propositions and lemmas. See [the discrepancy log](../SOURCE_ERRATA.md).

## Validation and remaining scope

Four new modules and 20 public checks cover the original package,
real and complex inverse derivatives, canonical images, both correction
witnesses, the full original flow, finite reductions, exponent compatibility,
and actual spectral tori. Unconditional constructions are checked at
p=3/2, p=2, and p=4. Full gate results are recorded in
[the implementation status](../STATUS.md).

The precise external Hilbert-map identification and full fractional
smoothness qualification from Section 14 remain. Surjectivity for p>2
is not claimed. Next: audit Section 18 and the Chapter 4 Hamiltonian,
frequency, and flow statements against the original source quantities.
The dissertation remains incomplete.
