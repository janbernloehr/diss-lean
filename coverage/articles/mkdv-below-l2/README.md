# mKdV below L² — private verification

Status: **Theorems 1.2 and 1.3 are verified under the accepted intrinsic
Birkhoff reference. Theorem 1.1 remains open.**

Work is confined to the authorized private worktree on
`articles/mkdv-below-l2`, based on canonical commit
`c5bcf6344cd2e2628ae537e98b85bb9ec1849dec`. The canonical checkout and its
compiled dependencies are unchanged. The workspace decision remains separate.

See the [Theorem 1.2 clause map](theorem-1.2.json),
[Theorem 1.3 clause map](theorem-1.3.json),
[H4 dependency history](theorem-1.3-progress.json),
[Theorem 1.1 progress](theorem-1.1-progress.json), and
[checkpoint history](PROGRESS.md).

## Pinned source

Kappeler–Molnar, *On the wellposedness of the defocusing mKdV equation below L²*,
[arXiv:1606.07052v1](https://arxiv.org/abs/1606.07052v1),
[PDF](https://arxiv.org/pdf/1606.07052v1), downloaded 2026-11-02.
33 PDF pages; printed page numbers equal PDF page numbers.
SHA-256: `7ac1baa898365f4a556aec4d2e3182e82a9dbe782d8a183114ae81acb486e8c1`.
The served PDF displays November 14, 2021 although the watermark and requested
version are v1, 22 June 2016. The hash pins the actual served bytes.
Downloaded PDF/text and compiler outputs are not tracked.

## Main statements and coverage

All spaces are on T = R/Z; indices range over Z. Physical FL^p consists of
periodic distributions with their Fourier coefficient ell^p norm. FL_c^p is
the complex pair space; FL_r^p is the conjugate-reflection real form. The
smaller real mKdV diagonal is E_r^p. Weighted sequence norms use (1+|n|)^s.

**Theorem 1.2, p. 5, verified.** For every finite p≥2, the fixed compatible
physical Birkhoff family is analytic on a complex open neighborhood of all
FL_r^p, fixes zero and is canonical for the physical Fourier bracket. The
maps agree on common complex domains at every pair of exponents. Their real
restrictions are injective local diffeomorphisms with open dense image in the
actual conjugate-pair Banach target. At p=2 the map equals the accepted
intrinsic Hilbert map and has a global real analytic inverse.

**Theorem 1.3, p. 6, verified.** The normalized physical H₄ frequency map
extends to all real physical FL², takes values in every actual real weighted
ell^(-1,r), 1<r≤infinity, and is real analytic into each target. For every
finite p>2 it extends real analytically on all FL_r^p into the literal complex
ell^(-1,p/2) target. Equal physical distributions have the same coordinates.
These are the physical H₄ action frequencies: the extensions agree with the
independently constructed original H^(3/2) Hamiltonian derivatives at every
source and index, including closed actions.

The original H₄ has local complex analytic factors in the actual ell^(3,1)
actions. Its physical open-action frequency is the derivative along unit-speed
action reduction. Its closed-action frequency is the second amplitude
derivative, with action exactly t²/2. Both equal the same raw unit action
partial derivative. This proves full-source real analyticity and continuity
across collapsed gaps. Actual spectral finite-gap approximation in the native
weighted norm then extends Lemma 5.2 to the full domain. The chosen article
moment atlas and physical distribution adapter preserve this identity.

The refined asymptotic has fixed ell^(p/3) and OnePlus remainder maps, with
one neighborhood and both maps preceding all finite q>1. Their bounds hold
locally uniformly. The p/3 quasi-norm is retained for 2<p<3. The asymptotic
identity is stated at n≠0, as appropriate at infinity; the separately proved
exact all-index formula retains the actual singleton term at n=0.

**Theorem 1.1, p. 3, open.** For each finite p>2 the remaining target is local
C⁰ wellposedness of the renormalized mKdV equation on every real FL^p datum,
with a common neighborhood and T>0 and a continuous map into trajectories
in the uniform norm. The global clause requires one neighborhood of zero
working before every T>0. Smooth approximations must give the same
pointwise-in-time limit curve. The original equation must have no continuous
extension at any datum in FL^p outside L², at each fixed t>0 as stated in
Corollary 7.2(iii).

The actual cubic-plus-normalized H4 rotations now have physical distribution
source lifts through the fixed Birkhoff image. A common local interval works
for nearby data; one invariant neighborhood of zero works before every time
interval. The full compact-time source trajectory maps are continuous in the
uniform norm, and convergent approximants have uniformly convergent lift
trajectories. The same physical Birkhoff coordinates, original action products,
time-addition law and admissible inverse steps are verified. These are
rotation-lift results: diagonal invariance and agreement with smooth mKdV PDE
solutions have not yet been proved.

Every physical input outside the Hilbert pair space now has a nonzero first
Birkhoff mode at n≠0. Here Hilbert membership means that exactly the same two
original distributions are represented by a real FL² input. The proof uses
actual finite-gap regularity and Fourier uniqueness, not finite input Fourier
support. The divergent-mass approximation and fixed-time phase separation
steps remain open.

The actual physical mKdV diagonal is now a named closed complete Banach
subspace of equal original distribution fields. Fourier uniqueness identifies
it with the unsigned-component-swap fixed source slice. Symmetric Fourier
cutoffs preserve it and converge in the original physical norm. The exact
unsigned-swap covariance is proved from the physical ODE and extended to all
finite source exponents. Dirichlet and Neumann conditions exchange under this
spectral reflection. Original algebraic multiplicities and complete ordering
fix the signed labels: the swapped left endpoint at n is minus the original
right endpoint at -n, and conversely, including every collision.

The principal standard-root branches and the full canonical root now have
their exact reflected signs. All original higher actions have spectral-power
parity. In particular, actual physical mKdV gaps and original Birkhoff action
products are even in n and the canonical root is odd in the spectral variable.
The normalized physical frequency is now proved odd on the entire finite-p
diagonal, including closed gaps and the zero index. Native physical H4
antisymmetry, the actual action derivatives and original-distribution Fourier
approximants give this identity without an angle hypothesis. Both actual
weighted sequence realizations and the cubic-plus-normalized phase frequency
retain oddness. The phase-angle identity and actual source-flow diagonal
preservation remain open.
The independent physical H2 momentum is now proved zero on the full original
fractional diagonal, giving the precise mass-only fourth-flow normalization.

## Physical conventions and corrections

Fourier synthesis uses exp(2πinx); coefficients use exp(-2πinx). The original
equation is u_t=-u_xxx+6u²u_x. The renormalized equation is
u_t=-u_xxx+6(u²-M)u_x, with M=integral from 0 to 1 of u².
Original-to-renormalized translation is v(t,x)=u(t,x-6Mt), with inverse
x+6Mt and coefficient multiplier exp(-12πinMt). This sign directly satisfies
the equations and corrects the conversion discussed on p. 29.

The action normalization is
omega4star_n = dH4/dI_n - (2πn)^3 - 6H2 - 12πnH1.
The actual moment expression is -12 sum_k k Omega²_nk. It is not the H₃
frequency. H₁ is the physical mass and H₂ the physical momentum, retaining
the original period-one constants. On the mKdV diagonal H₂ vanishes where
classically defined, and omegaSharp_n=(2πn)^3+omega4star_n.

The nonextension argument must select n≠0: the mass-dependent phase in
Theorem 7.1(iii) vanishes at n=0. Corollary 7.2's reference to item (iv) of
Theorem 7.1 is a cross-reference typo; that theorem has three items.

## Remaining integration order for Theorem 1.1

1. Prove preservation of the actual smaller mKdV diagonal. The physical
   diagonal model, unsigned swap covariance, signed periodic endpoints,
   root branches, even actions and full finite-p odd normalized-frequency
   identity are now verified. The Birkhoff phase-angle correspondence remains open;
   a complete alternative proof via Hamiltonian swap covariance must prove
   the same actual source-flow preservation.
2. Identify the verified fourth-frequency rotation lift with the smooth
   physical renormalized evolution. The common local interval, invariant
   small neighborhood and uniform-norm trajectory continuity are now proved
   for this lift on real-type distribution pairs.
3. Prove the exact smooth-approximation solution property and continuity in
   the uniform trajectory norm.
4. Prove fixed-time nonextension at every FL^p datum outside L² using controlled
   smooth approximations, tunable divergent mass and a nonzero signed mode.

## Validation

The focused checker `check.sh` lists 130 article/shared modules and the
consumed hierarchy foundations. Lean 4.33.1 checks use `autoImplicit=false`
and `warningAsError=true`. The seventeenth checkpoint strictly checks all 8
final new modules and reuses 122 parent modules after verifying their sources
are unchanged from `40d1959bf83cadfd29557cf1a3035bec7db6028c`.

The fresh full transitive audit checks all 634 named declarations, including
the main Theorems 1.2 and 1.3. Only `propext`, `Classical.choice` and
`Quot.sound` occur. No holes, new axioms, disabled linters or increased
heartbeat limits were introduced. `validation.txt` captures the checks;
`validation.json` records the build basis, source hashes and audit results.
Canonical compiled dependencies are imported read-only. This is incremental
focused validation, not a fresh whole-repository build or a completed
verification of the entire article.
