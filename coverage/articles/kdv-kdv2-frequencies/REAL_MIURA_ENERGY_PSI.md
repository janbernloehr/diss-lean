# Actual real-preserving rough Miura charts and entire energy psi candidates

Every main theorem remains OPEN. This milestone removes an actual
real-type applicability obstruction to the verified NLS psi theorem at
every physically real period-one Hminus1 potential. It also constructs
jointly analytic energy candidates, including their branch-point values.
Their Hill energy periods and identification with the normalized Hill
family have not yet been proved.

## Physical realness and a constructed inverse

`PeriodOneMiuraConjugation.lean` defines the actual Fourier symmetries

    a_k -> conjugate(a_(-k))
    q_k -> conjugate(q_(-k)).

They preserve the L2 and Hminus1 norms and are involutive. Their fixed
points are exactly the coefficient relations a_(-k)=conjugate(a_k) and
q_(-k)=conjugate(q_k). The mass resolvent, actual absolutely convergent
Miura convolution and resolved quadratic equation commute with these
symmetries. The zero Fourier coefficient of a real constant is fixed.
These results concern physical realness, not componentwise real Fourier
coefficients.

`EquivariantSmallQuadraticInverse.lean` proves uniqueness in the actual
contraction ball and the strict interior estimate 3R/4 for the constructed
solution. Symmetry and uniqueness force that solution to be fixed. The
analytic inverse is restricted to a genuine common open neighborhood
where all lifts remain inside the uniqueness ball; every real input in
that neighborhood then has a real lift.

`PeriodOneRealMiuraCharts.lean` applies these results to the actual mass
resolvent. One mass cutoff precedes all masses and real potentials in a
bounded rough ball. Adding the real zero Fourier constant gives an
actual complex analytic Miura lift with one fixed energy translation:

    Miura(u(q)) = q + ((m+1)/2)^2.

The literal distributional Miura identity holds for every complex input
in the chart; real inputs have physically real lifts.

## Verified NLS psi data at every real rough base potential

`HillHminusOneRealMiuraCharts.lean` constructs an actual
`HillHminusMiuraChart` at every physically real rough q0. Its fixed energy
shift is positive and real. At every real input in its domain the lift is
physically real and its diagonal NLS source is proved to be real type.
No such real-type property is assumed for arbitrary complex inputs.

`HillHminusOneRealMiuraSourcePsi.lean` applies the existing verified
`exists_sourcePsi_lemma12_11`. The resulting open set is exactly the
intersection of the actual rough chart domain with the inverse image of
the common complex NLS psi domain. It contains q0 and every real input
in that chart. One rough-open set precedes all deleted indices. Actual
source spectral isolation, analytic deleted-root branches and exact raw
frequency-contour orthogonality are retained. At each complex potential
one actual all-index contour family works for every numerator, with
raw periods 2*pi*delta_mn.

The existing unchanged `ConjugateReflection.lean` and
`SourcePsiLemma12_11.lean` are now directly selected and recompiled by the
article checker. No new shared branch import is required.

## Joint analytic energy descent

`ParametricOddSquareDescent.lean` proves the local-parameter version of
even square descent and its odd filled quotient consequence. It uses a
joint analytic divided difference and fixed Cauchy circles; it does not
assume that a principal square-root selection is analytic or continuous
at its cut or at zero.

`HillHminusOneRealMiuraEnergyPsi.lean` uses the actual NLS numerator phi_n
from the constructed normalized root branch. It defines

    Psi_n(lambda,q) = oddSquareDescent
      (z -> phi_n(z,q) - phi_n(-z,q)) (lambda + C.energyShift).

This is jointly analytic on the entire energy plane times the same
rough-open neighborhood, including lambda=-C.energyShift. The exact
identity, valid even at z=0, is

    (2z)*Psi_n(z^2-C.energyShift,q) = phi_n(z,q)-phi_n(-z,q).

`exists_hillHminus_real_entire_energyPsi` constructs such candidates near
every physically real Hminus1 potential while retaining the actual NLS
normalized extension and original exact frequency periods. The factor
identity is an identity of entire functions; no division by zero is used.

## Relation to the source and remaining obligations

This is infrastructure toward the full rough neighborhood and normalized
Hill psi family used in equations (52)-(53), PDF page 21, and ultimately
the frequency extensions in Theorems 1.2 and 1.9, PDF pages 4 and 6. It is
not yet a proof of those source psi assertions: the candidates still
need exact root parity/sign matching, mapped positive/negative contour
identities, the lowest-cut analysis and actual energy normalization.
They also need agreement on chart overlaps and identification with the
previous local rough normalized family. No global coherent Hill family,
canonical product leading scalar one, root estimate (54), physical
frequency identity (69), action descent, weighted target space or physical
Birkhoff/PDE flow is asserted here. All main inventory rows remain OPEN.

## Validation

Seven new proved modules and two newly selected existing modules are
checked in dependency order. All 369 previously selected Lean sources
remain byte-identical; all seven shared provenance records remain valid.
The full strict build and transitive axiom audit are recorded in
`VALIDATION.md` and `source.json`. Checks use pinned Lean 4.33.1/mathlib
v4.33.1, default heartbeats, warnings as errors and private outputs. Only
propext, Classical.choice and Quot.sound are permitted. Canonical main
remains unchanged and read only.
