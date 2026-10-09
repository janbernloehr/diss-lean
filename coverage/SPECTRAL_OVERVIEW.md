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

## Theorem 1.2: proved in the full printed range

The source statement on p. 19 requires the globally lexicographically
ordered endpoints, counted with algebraic multiplicity, to have lp
frequency displacements for every finite p>1, with a locally uniform
bound for the sum of both p-th powers over all integer indices.

`NLS/ZakharovShabat/SourcePeriodicOverview.lean` provides the source-facing
entry points:

- `sourcePeriodicEndpointEnergy_sum` proves the literal series is summable
  and equals the two full displacement norm powers. Neither a tail-only
  estimate nor Lean's default value for a nonsummable series is used.
- `sourceTheorem1_2` gives one positive constant on one open convex
  neighborhood in `CoeffPair p`, with its original finite-p component-sum
  norm. Every potential in that neighborhood satisfies the full series
  bound. No uniform global bound over all potentials is claimed.
- `sourceTheorem1_2_ordered_labels` retains `PeriodicEndpointLabeling` and
  both global lexicographic inequalities. Its `central.roots` and
  `central.count_eq` preserve all central repetitions and original
  algebraic multiplicities. Its `distant` field preserves both endpoints
  and their multiplicities in each distant disk. Its `exhaustive` theorem
  identifies all and only the original periodic eigenvalues.
- `PeriodicEndpointLabeling.eq_canonicalPeriodicEndpoints` makes these
  ordered sequences independent of the admissible cutoff and initial
  enumeration. Both displacement sequences belong to actual `Coeff p`.

The common bounds follow from
`exists_uniform_bounded_canonicalPeriodicDisplacements`, pulled back along
the continuous linear period-one source embedding. That construction uses
height-N counting boxes and finite central bounds. It does not require
Theorem 1.1's unresolved printed-height estimate above four. The public
checks include the literal series for general p and the instance p=5,
original central multiplicities, and coincident free endpoints with zero
energy. The full printed range 1<p<infinity is covered, unchanged.

## Corollary 1.3: proved in the full printed range

`sourceCorollary1_3_mem` proves membership of the literal midpoint
frequency displacement and unsquared gap in lp, using the same canonical
ordered endpoints. The identities
`sourcePeriodicMidpointDisplacement_apply` and
`sourcePeriodicGapDisplacement_apply` identify the sequence-space values
with `(lambda_n^-+lambda_n^+)/2-n*pi` and `lambda_n^+-lambda_n^-`.

`sourceCorollary1_3` gives both a common local positive norm bound and,
for any positive epsilon, one open source neighborhood and one cutoff
such that both lp tails are at most epsilon at every larger cutoff.
The neighborhood and cutoff may depend on epsilon, as in the existing
locally uniform tail statements. All finite p>1 and every complex source
potential are covered. No continuity or analyticity of the individually
lexicographically sorted endpoints is inferred from these bounds.

## Corollary 1.6: proved in the full printed range

The statement on p. 21 requires real finite-gap potentials to be dense in
the real source space for every finite p>1. The existing
`NLS/ZakharovShabat/SourceFiniteGapDensity.lean` proves exactly this:

- `sourceFiniteGapLocus`, defined in `SourceFiniteGap.lean`, means that
  only finitely many actual canonical periodic gaps are nonzero. Its
  ambient space is `realTypeSourceLocus p`, with the inherited original
  source norm. It is not a finite Fourier-support definition.
- `exists_real_sourceClosingApproximation` constructs a real source
  arbitrarily close to any real source and closes its original periodic
  spectrum in every sufficiently distant strip. Both spectral closing
  equations vanish there and the determinant order is exactly two.
- `finite_canonicalPeriodicGap_of_singleton_strips` uses the actual
  canonical endpoints and their spectral membership to conclude that
  every sufficiently distant gap vanishes. Thus the approximants satisfy
  the stated spectral definition, not only a target-coordinate condition.
- `exists_mem_sourceFiniteGapLocus_norm_sub_lt` supplies these approximants
  at every positive tolerance in the original norm, and
  `dense_sourceFiniteGapLocus` states the resulting density for all finite
  p>1. Existing public examples check actual spectral finite-gap
  approximation at p=3 and density at p=2 and p=3/2.

This completes the numbered density statement without an additional
assumption of density in a smoother space. The preceding unnumbered
claim of spatial real analyticity for all finite-gap potentials is a
separate regularity claim; it is not certified by this density audit.

## Boundary-spectrum overview statements: audit pending

Theorems 1.4 and 1.5 require a statement-by-statement comparison with the
boundary-spectrum implementation, including both boundary conditions,
domains, ordering, multiplicities, local uniformity, and the exact source
norms and constants. Their completion is not inferred from this
periodic-spectrum or finite-gap density audit. The dissertation remains
incomplete.
