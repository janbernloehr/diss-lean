# Actual finite-gap KdV moment identity

## Actual intrinsic moments at all real L2 sources

Let F be the actual normalized primitive, R the actual canonical product
root, psi_n the actual globally normalized numerator and F_k=F+i*k*pi.
The literal source moment is the counterclockwise intrinsic circle integral
Omega_nk^(m)=integral F_k^m*psi_n/R.

For every actual real period-one L2 source, all n,k>=1 and all l>=0:

```text
Omega_nk^(0) = 2*pi*delta_nk,
Omega_nk^(2*l+1) = 0.
```

If the actual k-th gap is closed, EVERY positive moment is zero,
including n=k. No high-index cutoff, gap-opening condition or finite-gap
assumption is needed for these real-L2 identities.

At real points of every actual gap the verified squared primitive equals
the square of the nonnegative actual profile. The squared-cosh coordinate
therefore has nonzero derivative locally. Its ratio constructs an analytic
local chart of F_k*P/R for any entire P. Dense nonreal gluing joins those
charts with the actual regular cut charts into ONE filled differential
on the whole intrinsic outer disc.

The actual F_k^2 is analytic on that disc. Filled circle agreement kills
all odd moments. At a collapsed gap the actual F_k itself is analytic,
so the same filled criterion kills all positive moments, even when the
own normalized numerator is nonzero. Literal total-division values at
branch points are never asserted to be analytic.

These are the real-L2 spectral parts of Lemma3.1(i),(iii),(iv). The full
complex rough-W analytic and quantitative scope remains distinct.

## Actual finite-hole deformation

The intrinsic inner radius is halfGap+collar. The enlarged outer radius
is halfGap+1.5*collar; actual neighboring band separation proves all such
closed discs pairwise disjoint. The larger halfGap+2*collar radius is
retained for analytic charts and is not used for closed-disc separation.

At a source with every gap above N closed, avoiding every first-N inner
disc puts the energy in the actual cubic filled domain, provided N>=n.
All first-N indices remain as holes, including n when closed. A common
positive threshold encloses the finite family before every larger circle.

The verified actual filled cubic kernel and this geometry instantiate
finite-hole Cauchy's theorem. The actual outer contour equals the finite
sum of actual intrinsic gap contours. The independently proved actual
odd moments and the checked binomial contour expansion give

```text
(4/(i*pi))*integral_gap_k F^3*psi_n/R
  = -12*k*Omega_nk^(2) + (2*k*pi)^3*delta_nk.
```

Summing the actual holes retains the leading cube at n even when that
selected gap is closed.

## Actual physical KdV velocity and coordinate derivative

For real smooth period-one mean-zero physical Q, let V_n(Q,N) be the
already verified actual finite Dirichlet velocity sum, where N includes
n and all open gaps. The exact physical cubic contour identity now gives

```text
V_n(Q,N) - (2*n*pi)^3 = -12*sum_(k=1..N) k*Omega_nk^(2)
                       = -12*sum_(k>=1) k*Omega_nk^(2).
```

The countable sum is genuine. The weighted zeroth index is zero and every
term above the actual closed-tail cutoff vanishes; a HasSum theorem proves
the equality with the finite sum for arbitrary complex weights vanishing
at zero and arbitrary positive moments.

The literal physical KdV scalar coordinate derivative consequently is

```text
D Z_n[actual KdV field]
  = ((2*n*pi)^3 - 12*sum_(k>=1) k*Omega_nk^(2)) * (i*z_n).
```

It applies to every differentiable nearby-real matching scalar germ,
including closed selected gaps. Positive physical Fourier time orientation
and the literal source factor -12 are preserved. Neither a prescribed
spectral flow nor an assumed Hamiltonian frequency enters this proof.

## Validation

Prior strict evidence for all 1085 unchanged selected baseline sources; strict dependency-order compilation of six new proof modules; then a fresh combined transitive axiom audit of all 1091 selected modules. Exact checker/audit/coverage/evidence selections, complete transitive selected dependency order and audit reachability, 1120 frozen source/checker/provenance hashes, all 27 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. No repeated full 1091-module rebuild is claimed.

Fresh audit: 9857 selected and 32287 imported NLS declarations.
Lean4.33.1/mathlib4.33.1, warningAsError, default200000heartbeats.
Only `propext`, `Classical.choice`, `Quot.sound`; no sorry, additional
axioms, heartbeat overrides or linter exceptions. All 1085 baseline
selected sources and all 27 provenance records are unchanged.

## Remaining main obligations

The physical spectral-velocity/coefficient version of (69) is proved.
Its full Hamiltonian/action-frequency identification still needs the
actual Birkhoff realization, including at closed selected indices. The
article-level physical statements explicitly assume smooth Q; any
finite-gap regularity representation needed to extend that physical
scope must be verified before claiming the full source theorem.

Complex rough-W moment compatibility/analyticity, sharp estimates and
infinite-gap summability, the quintic coefficient/translation and mass
renormalization for (84), full canonicality/Fourier zero jet/native
Banach analytic map and inverse, action descent and actual PDE flow
realization remain open. All eleven main theorem rows remain OPEN.
