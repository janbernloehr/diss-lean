# Analytic actual normalized second-moment series

`exists_classicalHill_analytic_normalized_frequency_series` in
`NLS/KdV/ClassicalNormalizedFrequencySeries.lean` constructs one open
complex continuous-potential neighborhood U of zero and an actual
analytic normalized period inverse R. The neighborhood precedes every
positive output index n. R is the identity at zero and its norm is at
most two throughout U.

For each n, the literal original second moments satisfy

* the positive series sum_k |k Omega_nk^(2)| converges for every q in U;
* -12 sum_k k Omega_nk^(2) is analytic on U;
* ordinary positive partial sums converge locally uniformly on U.

The constructed family retains all-mode moment analyticity, the exact
zeroth periods Omega_nk^(0)/(2*pi)=delta_nk, and every odd cancellation.
There is no finite-head exception in the series conclusion. The proof
allows arbitrary complex continuous interval potentials near zero,
without imposing endpoint periodicity on the potential curve.

## Actual estimates used in the proof

`ClassicalTwoWeightedMomentBounds.lean` uses the already constructed
twice-weighted inverse Q, compatible with the original inverse R. The
actual weighted column is n² Q e_n. Moving the bounded reciprocal square
index multiplier across the unconjugated Hilbert pairing puts the weight
on the actual critical-resolvent period vector. The all-order off-diagonal
cut bounds yield an actual Hilbert remainder estimate with an additional
factor k^(-2). For G_k=norm(actual energy squared gap) and x_k=G_k/k²,
the second moment satisfies

    |Omega_nk^(2)| <= 1376*pi²*C³*n²*x_k/k²

on every sufficiently high contour, before all n,k. This bound includes
the diagonal. It uses the literal original normalized moments, exact
resolvent formula and substitution lambda=z², d lambda=2z dz. No canonical
product scalar is replaced by one.

`ClassicalFrequencyGapMajorant.lean` constructs an actual l1 coefficient
g(q) by taking the pointwise square of the difference of the two actual
canonical frequency endpoint displacements. Both displacement sequences
belong to l2 with locally uniform norm bounds, for general complex even
coefficient potentials. On one common tail, the proved canonical labeling
identifies g_k with the original contour-defined frequency squared gap.
The counted endpoints bound the frequency midpoint divided by k, giving

    x_k <= 16*pi²*|g_k|.

The l1 norm of g is locally uniformly bounded. This is a frequency-scale
statement. It does not assert that the unscaled energy gap sequence is
in l2. The Hill coefficient pair (-1,-q) is not subjected to a ZS RealType
assumption.

Together the estimates give a genuine locally bounded l1 majorant for
the high tail of k Omega_nk^(2), for each n. The reusable
`AnalyticTailSummation.lean` fills the finite head using its scalar
analyticity and then applies the existing Banach analytic l1 realization
and summation theorem. It does not need continuous ordered individual
gap roots. `DiagonalBilinearPairing.lean` supplies the reusable multiplier
duality identity and actual two-sequence Hilbert majorant estimate.

## Source correspondence and remaining obligations

This proves the local continuous-potential summation part of source
Theorem 3.4, equation (73), PDF page 31. The coefficient -12 is preserved
in `classicalHillMomentFrequencyCorrection`. Identifying this candidate
with the physical KdV correction requires the physical finite-gap
Hamiltonian-frequency identity (69) of Lemma 3.2 and its verified
continuation/density argument. Those are still open. The full rough/global
W domain and action dependence of Remark 3.5 are not proved here.

The source's sharp normalized two-index remainder estimates, diagonal
leading term, exact nonzero-potential canonical scalar, KdV2 fourth-moment
series and physical Hamiltonian/action/Birkhoff identifications also
remain open. No main-theorem inventory row is marked verified. The
current result is a necessary analytic summation step, not an assertion
that the requested main frequency or flow theorems are complete.

No new external branch sources are imported in this milestone. The
existing `CanonicalWeightedGapSummability.lean` is directly selected and
strictly recompiled. The four previous selected-source provenance records
and all 195 previously selected source hashes remain unchanged. Full
strict build and transitive audit results are recorded in `VALIDATION.md`
and `source.json` after the completed run.
