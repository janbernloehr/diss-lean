# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–20, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

## Theorem 1.1: partial; printed height above two remains open

For every finite p > 1 the source requires one neighborhood and one positive
cutoff, with two eigenvalues in each distant quarter-pi disk, count 4N+2 in
the central box, the stated periodic/antiperiodic parity counts, no other
eigenvalues, and real spectrum for real-type potentials. The central box has
height `(1+8‖φ‖ₚ)^p`.

The following are verified ingredients:

- `exists_uniform_periodicCountingData` (declaration namespace
  `NLS.ZakharovShabat`, file `NLS/ZakharovShabat/PeriodicCounting.lean`) supplies
  one open convex neighborhood and every larger cutoff, with full algebraic
  multiplicities, disk and central parity, and spectral exhaustion. Its box
  initially has height N. The period-one source embedding supplies the even
  Fourier-support condition required by the parity conclusions.
- `periodicSpectrum_im_eq_zero_of_realType` in
  `NLS/ZakharovShabat/RealType.lean` supplies reality for every finite exponent.
- `exists_source_periodicCounting_printed_height` in
  `NLS/ZakharovShabat/SourcePrintedHeightCounting.lean` transfers the counts to
  each source's own printed-height box for **1 ≤ p ≤ 2**, on one open convex
  source neighborhood. It retains spectral exhaustion and identifies the
  actual moving rectangular integral with the central projection. Those
  integrals depend analytically on the source.

The numerical input is `printed_height_neumann_bound` in
`NLS/ZakharovShabat/PrintedHeight.lean`. Set B=1+8M. Convexity of `B^(-q)`
in q interpolates the p=1 and p=2 estimates, giving
`(4p/B + B^(-p)) M < 1` throughout 1 ≤ p ≤ 2.

For p > 2, `printed_height_neumann_bound_fails` proves that this particular
sufficient criterion is strictly greater than one when
`M ≥ 1/(4p-8)`. The earlier all-exponent height `(1+8pM)^p` remains available,
but it does **not** discharge the printed Theorem 1.1 height. No spectral
counterexample to the printed height is asserted, and no replacement for it
has been accepted as completion of this requirement. A different spectral
argument or a sharper estimate is still needed above two.

## Other overview statements: audit pending

The canonical endpoint displacement sequences and their locally uniform
bounds are in `CanonicalPeriodicEndpoints.lean` and
`CanonicalPeriodicDisplacementBounds.lean`. Source midpoint bounds and gap
summability are in `SourcePeriodicMidpointAsymptotics.lean` and
`SourcePeriodicGapSummability.lean`. These are candidate ingredients for
Theorem 1.2 and Corollary 1.3; the full comparison of ordering, multiplicities,
local uniformity and exact source norms is not yet recorded as complete.

The remaining boundary-spectrum overview statements likewise require a
statement-by-statement check, including their domains and norm constants.
