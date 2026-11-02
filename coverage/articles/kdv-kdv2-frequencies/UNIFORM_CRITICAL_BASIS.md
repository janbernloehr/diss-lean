# Actual uniform critical family and infinite numerator basis

This milestone removes a substantive limitation of the finite construction:
one open complex potential neighborhood now supports all positive critical
branches and all entire numerator basis elements simultaneously. The actual
high critical displacement tail is also a Banach analytic ℓ²-valued map,
with uniformly small norm near zero. **The infinite period normalization
and the article main theorems remain open.**

The potentials here are `C([0,1],ℂ)` with the sup Banach norm. The variable
z is the scalar Hill spectral frequency, with energy lambda=z². Its critical
coordinates and displacements are not the Hamiltonian frequencies omega
of KdV or KdV2. No such identification is inferred.

## Imported actual high spectral foundation

The merge retains the ancestry of `articles/kdv-convexity` through
`963d5bb053684ec65427e0a319ffb729beaaa9f0`. It reuses the actual scalar trace
embedding into the existing complex ZS coefficient theory, uniform
source-path contour coverage, and the actual high Hill gap pairs with
multiplicity and parity trace levels. The direct frequency proof consumes
`ContinuousPotentialL2Bound`, `ClassicalSpectralEmbedding`, and
`ClassicalContourCoverage`; the other imported high-pair/moment modules
retain their upstream definitions and are separately rechecked.

The embedding is the literal pair `(-1,-q)` and is not assumed real type
in the ZS sense, even when q is real. All comparisons use the proved actual
IVP trace identity. No second Hill operator or spectral foundation is added.

## General complex-source distant analyticity

`NLS/ZakharovShabat/SourceDistantCriticalPointsAnalyticNeighborhood.lean`
adds `exists_local_source_distantCanonicalCriticalPoints_analytic_complex`.
At an arbitrary complex coefficient source, one cutoff and one open
neighborhood support analyticity and simplicity of every distant
canonical critical root. The existing real-type theorem is unchanged.

The new proof uses the already constructed uniform critical labeling:
its distant zeros have analytic order one. This yields a nonzero second
discriminant derivative and permits the analytic implicit-root theorem.
It does not assume central-root simplicity or apply the real-type theorem
to the constant-upper Hill pair.

## Actual energy critical family on a common neighborhood

`NLS/KdV/ClassicalHighCriticalPoints.lean` defines the undoubled actual
source coefficients and transfers the canonical distant frequency root
zeta_n(q) to the energy critical point `mu_n(q)=zeta_n(q)²`.
It proves the exact derivative relations

```text
D_z'(z,q) = 2*z*Delta_lambda'(z²,q),
D_z''(z,q) = 2*Delta_lambda'(z²,q)
              + 4*z²*Delta_lambda''(z²,q).
```

`exists_analytic_classicalHillHighCriticalPoints` proves that at every
complex continuous potential q0 there are one positive cutoff N and one
open neighborhood V of q0 such that, for every n>N:

- both zeta_n and mu_n are analytic on V;
- zeta_n lies in the actual positive frequency disc `B(n*pi,pi/4)`;
- `Delta'(mu_n)=0` and `Delta''(mu_n)!=0` for every q in V;
- the only energy critical point in the squared closed frequency disc is
  mu_n, with no real-type assumption;
- every squared frequency contour lies in the actual root/primitive
  continuation domain for every q in V.

The cutoff and V are chosen before the tail index and the potential in V.
No countable intersection of mode-dependent neighborhoods is used.
The construction directly matches the shared high-disc geometry; central
and globally ordered rough labels remain separate obligations.

## Infinite entire numerator basis near zero

`NLS/KdV/ClassicalUniformCriticalBasis.lean` joins that intrinsic uniform
high tail to the finite head of previously constructed simple free
critical branches. A finite intersection supplies one open neighborhood
V of zero. `exists_classicalHill_uniform_critical_family` proves on V,
for every positive n simultaneously,

```text
mu_n(0)=(n*pi)²,
mu_n analytic,
Delta'_q(mu_n(q))=0,
Delta''_q(mu_n(q))!=0.
```

The high-contour continuation coverage remains valid on that same V.
The entire numerators are the actual filled quotients

```text
B_n(lambda,q) = 2*n*pi * filled(Delta'_q(lambda)/(lambda-mu_n(q))).
```

`exists_classicalHill_uniform_numerator_basis` proves for every n on one
common `ℂ × V`: joint analyticity, the exact free numerator on the whole
zero-potential slice, the factor identity
`(lambda-mu_n)*B_n=2*n*pi*Delta'_q(lambda)`, and a nonzero filled value at
mu_n. The shared joint moving divided-difference theorem fills the apparent
pole; no analytic numerator selection or inverse period operator is assumed.
These basis elements have not yet been normalized on all infinitely many
gaps. Infinite linear combinations, uniqueness and global products are
not asserted by this construction.

## Actual ℓ² norm analyticity and smallness

`NLS/KdV/ClassicalCriticalTailAnalytic.lean` defines the positive integer
frequency critical displacement tail

```text
T_N(q)_k = zeta_k(q)-pi*k, if k>N; 0 otherwise,  k in Z.
```

Its membership in ℓ² and its norm bound follow from the existing actual
canonical critical displacement sequence by pointwise restriction.
`exists_analytic_classicalHillCriticalFrequencyTail` proves, near every
complex continuous q0, that this is a Banach analytic ℓ² map on one open
neighborhood, with a uniform norm bound and common valid critical labeling.
The proof combines coordinate analyticity with that actual norm bound;
it does not substitute separate coordinate analyticity for Banach analyticity.

`classicalHillCriticalFrequencyTail_free` proves the whole tail is zero at
the free potential from the valid distant labeling and the exact free
trace derivative. Therefore
`exists_small_analytic_classicalHillCriticalFrequencyTail` proves that for
every epsilon>0 there are one cutoff N and one complex open V containing
zero such that `norm(T_N(q))<epsilon` for every q in V, with the full ℓ² map
analytic there. This is uniform control of the infinite sequence norm.
It does not claim a prescribed rate in N or any Sobolev/action asymptotics.

## Validation and remaining obligations

The focused frequency checker selects 40 modules, including every modified
or new consumed dependency. It uses pinned Lean 4.33.1/mathlib v4.33.1,
`autoImplicit=false`, `warningAsError=true`, and default heartbeats. The
shared integration checker is also rerun in its separate private output
directory. Both expensive runs are serialized by the shared build lock.
Current final counts are in `VALIDATION.md` and `source.json`.

The remaining normalization problem is an actual infinite period operator:
construct compatible contour entries for all modes on one neighborhood,
prove its tail/operator norm bounds, and construct the normalized inverse
and resulting entire functions. The present ℓ² tail control is input to
that task, not its solution. The source's canonical zero/product
representation, central/global rough labeling, rough-space compatibility,
sharp frequency moment bounds, physical Hamiltonian/frequency identities,
action descent, weighted asymptotics, compact derivatives and physical
Birkhoff/PDE flow identification also remain open. No main theorem is
marked verified.

The shared estimates line through
`b2097376825d45ff2468d2c2db239c95b61dea59` was inspected: it constructs an
actual jointly analytic L² energy discriminant and physical weighted high
root bounds. It was not merged by this milestone; transferring the present
construction to the source's full rough Fourier-Lebesgue scale remains
explicit work.

The final frequency run passes all 40 selected modules. Its transitive
audit passes for 570 selected declarations and 12091 declarations including
all imported NLS dependencies, allowing only `propext`, `Classical.choice`
and `Quot.sound`. Reproduce with `bash scripts/check-kdv-kdv2-frequencies.sh`.

The separate shared integration recheck passes all 26 shared modules,
the positive-index example and the transitive audit of 337 shared-namespace
declarations. Both serialized validation processes finish successfully.
