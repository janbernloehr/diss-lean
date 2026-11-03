# Actual analytic rough second-moment frequency series

This milestone constructs the source second-moment correction candidate
on one complex Hminus1-open neighborhood of zero. It uses the actual
normalized moments and a genuine rough summable gap majorant. Every main
theorem remains OPEN: physical Hamiltonian frequency identification, the
full source neighborhood W, action descent and weighted target-space
claims are not asserted by this construction.

## Genuine rough gap sequence

`HillHminusOneCanonicalFrequencyGaps.lean` uses the actual fixed Miura
chart C and its analytic L2 lift. The source potential is

    psi(q) = periodOnePotential(hillMiuraDiagonal(C.lift q)).

The difference of its actual canonical endpoint displacements is a
genuine l2 vector. Its pointwise square is a genuine l1 sequence, denoted
`C.canonicalFrequencyGapSquares q`. A common rough-open neighborhood
supplies a locally uniform l1 norm bound and the actual canonical counted
pair at every sufficiently high index. The proof uses the complex even
source, without a real-type assumption or a continuous-potential norm
budget on a rough ball.

The existing `UniformCanonicalPeriodicEndpoints.lean` is now directly
selected and recompiled. Its common-cutoff theorem identifies the actual
canonical endpoint sequence, rather than unrelated local endpoint choices.

## Fixed energy shift and the actual gap majorant

`HillHminusOneFrequencyGapMajorant.lean` retains the exact trace identity

    Delta_H(q,z^2-C.energyShift) = Delta_NLS(psi(q),z).

The principal roots sqrt(lambda+C.energyShift) of the actual tight high
energy endpoints belong to the positive free frequency disc. The actual
characteristic equation puts each lifted endpoint in the canonical
counted pair at that same positive index.

`SquaredPairGapBound.lean` proves a reusable estimate for the squared
coordinates of any two members of an unordered pair. Repeated members
give gap zero; different members give the pair's gap. A common translation
cancels exactly. With the actual canonical endpoint norm bound, this gives

    |l-u|^2/k^2 <= 16*pi^2*|C.canonicalFrequencyGapSquares(q)_k|.

Only the inequality is asserted. It does not assert that a forward
endpoint inclusion alone proves equality of the two complete multisets.
Collapsed actual pairs are included directly in the inequality.

`HillHminusCriticalPrimitiveCutData.exists_frequency_gap_majorant` applies
this estimate to the same tight actual pair retained by the cut data.
The previously proved unordered-pair uniqueness then gives the bound for
every actual pair on that same disc. One rough-open neighborhood and
one cutoff precede every potential, high index and actual unordered pair.

## Absolutely convergent analytic series

`HillHminusOneNormalizedFrequencySeries.lean` defines the literal terms

    k*Omega_nk^2(q)

using the actual normalized numerator, actual continued primitive/root
and original mapped frequency contour. It defines

    hillHminusMomentFrequencyCorrection(C,N,R,n,q)
      = -12*sum_(k>0) k*Omega_nk^2(q).

The constructed weighted normalized family from the preceding milestone
is kept unchanged. Its actual twice-weighted estimate supplies

    |Omega_nk^2| <= 1376*pi^2*B^3*n^2*(|l-u|^2/k^2)/k^2.

Together with the genuine rough l1 gap majorant this controls the high
tail. Actual scalar moment analyticity handles the finite contour head.
The proved analytic tail-summation theorem and exact positive-index
reindexing yield absolute convergence, locally uniform convergence of
the ordinary positive partial sums, and analyticity of the correction.

`exists_hillHminus_analytic_normalized_frequency_series` constructs one
rough-open U before all output indices n. It retains the full weighted
normalized family on V, with U contained in V, and the actual critical
primitive cut data on U. Consequently all earlier operator/inverse,
free, entire numerator, all-order moment analyticity, exact zeroth-period
and odd-cancellation properties remain available for the same R.

This is the near-zero Hminus1 construction of the actual series appearing
in source Theorem 3.4, equation (73), PDF page 31. The source physical
identity (69) is Lemma 3.2, PDF pages 26–27, and remains separate.

## Remaining main-theorem obligations

The series is a moment-frequency correction candidate. Identifying it
with the actual Hamiltonian derivative requires the finite-gap physical
identity and its continuation. That identity depends on physical
Hamiltonian exterior coefficients, normalized differential identification,
Poisson brackets/angle variables and the relevant contour deformation.
Analyticity near zero alone proves none of these identifications.

Full W continuation, coherent global normalized differentials, the exact
canonical product leading scalar, action descent, source weighted
frequency asymptotics and compact derivatives, and actual Birkhoff/PDE
flow identification remain open. So do the complete source main theorem
statements and their proofs, and the low finite-head collapsed-even
obligation in the full required scope. No main inventory row is closed.

## Validation

Four new proved modules and one newly selected existing common-cutoff
module are included. All 364 earlier selected Lean sources remain
byte-identical and all seven shared import records remain valid. The
focused checker and transitive audit select the new modules in dependency
order. Final counts and build evidence appear in `VALIDATION.md` and
`source.json`. Checks use pinned Lean 4.33.1/mathlib v4.33.1, default
heartbeats, warnings as errors, and private outputs. Only propext,
Classical.choice and Quot.sound are permitted. Canonical main remains
unchanged and read only.
