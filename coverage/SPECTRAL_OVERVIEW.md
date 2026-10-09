# Spectral overview audit

Source: dissertation Section 1, printed pp. 17–20, and the proof of Theorem
1.1 on p. 27. This audit compares statements and quantifiers, not filenames
or declaration counts. It does not certify the whole chapter.

## Theorem 1.1: printed height through four; higher exponents remain open

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
- `exists_source_periodicCounting_printed_height_up_to_four` in
  `NLS/ZakharovShabat/SourcePrintedHeightFourCounting.lean` transfers the counts to
  each source's own printed-height box for **1 ≤ p ≤ 4**, on one open convex
  source neighborhood. It retains spectral exhaustion and identifies the
  actual moving rectangular integral with the central projection. Those
  integrals depend analytically on the source.

The initial numerical input is `printed_height_neumann_bound` in
`NLS/ZakharovShabat/PrintedHeight.lean`, proving
`(4p/B + B^(-p)) M < 1` for B=1+8M throughout 1<=p<=2.
Above two that coarse test can fail, but the sharper reciprocal estimate
retains the conjugate-root coefficient 2*(2/(q-1))^(1/q). The power-sum
inequality 2/(q-1)<=4^q holds through p=4. This gives
`freeL1Bound_le_height_eight`, and
`mem_resolventSet_of_printed_height_up_to_four` proves the unchanged
horizontal edges and exterior region. `abs_im_lt_printed_height_up_to_four`
places every spectral point strictly inside the printed height.

The counting proof is factored through
`exists_source_periodicCounting_printed_height_of_resolvent`, keeping the
old p<=2 API available. The new p<=4 source theorem retains a common open
convex neighborhood, every larger cutoff, both parity clauses, the full
central and disk multiplicities, exhaustion, and actual analytic moving
rectangular projections. Public examples check p=3 and p=4, including
729i at p=3 with norm bound one, where the coarse test exceeds one.

Above four the literal height remains a required open obligation. The
new constant-four power-sum test already fails at p=5, which only rules out
that use of this envelope estimate. No spectral counterexample is claimed.
The all-exponent height `(1+8pM)^p` remains available but is not accepted as
completion of the printed requirement. Neither improved finite-range
estimates nor green tests establish the full theorem for every finite p.

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
