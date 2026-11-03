# Exact continuous/rough normalization and all rough odd moments

The later [weighted inverse and critical-gap milestone](HMINUS_WEIGHTED_CRITICAL_GAPS.md)
retains these features in a twice-weighted family and proves actual rough
quadratic critical-gap localization. The sharp normalized rough moment
and full-domain obligations below remain open.

`exists_hillHminus_normalized_all_odd_moments` constructs one complex
Hminus1-open neighborhood of zero before every positive numerator index,
positive contour index and nonnegative moment order. The actual normalized
entire numerators remain jointly analytic, have their exact free values,
and their literal moments remain analytic with the exact zeroth periods.
Every odd moment vanishes on the whole rough neighborhood:

    Omega_nk^(2*l+1)(q) = 0,  n,k > 0, l >= 0.

This includes low indices, diagonal entries and collapsed gaps. The
neighborhood is open in the original unit-period `PeriodOneHminusOne`
Sobolev minus-one norm. It is a local result near zero; the source's full
W domain and the main theorems are not established by this milestone.

## Exact physical embedding without an endpoint hypothesis

`ClassicalRoughEmbedding.lean` constructs bounded complex-linear maps
from the original continuous unit-interval curve parameter to its actual
unit-period L2 Fourier coefficients and then to Hminus1. Continuous
interval potentials need not have equal endpoint values. No periodic
continuous representative or supremum-norm density assertion is imposed.

The literal constant-upper ZS source is proved to be exactly the pair
of the constant coefficient -1 and the negative scalar Fourier sequence.
After even-index period doubling, its existing coefficient operator is
exactly the physical Hill first-order operator. The physical L2 trace
comparison therefore proves, at every complex energy,

    Delta_Hminus1(inclusion(q),lambda) = Delta_classical(q,lambda).

The same identity holds for the energy derivative. The established
classical root and primitive are definitionally the shared free-normalized
trace-family construction. Trace pullback proves exact continuation-domain
membership, exact root equality and exact primitive equality. Neither a
sign nor an additive logarithm period is left undetermined.

Finite unit-period Fourier polynomials recover their literal coefficients.
Their proved weighted density supplies genuine density of this continuous
interval inclusion in the full rough space, as well as density in L2.
This concerns the range of all continuous interval potentials, not the
image of a bounded supremum-norm ball.

## All selected critical energies agree on one neighborhood

`AnalyticImplicitUniqueness.lean` proves a general uniqueness theorem for
continuous implicit zero branches with a bijective partial derivative.
Its proof uses the injective chart supplied by the analytic inverse
function theorem. The scalar version requires only a nonzero derivative.

`ClassicalRoughCriticalCompatibility.lean` applies this result to each
of finitely many low critical energies. The actual high critical-point
uniqueness theorem and the proved rough pi/8 confinement identify every
remaining critical energy. One finite intersection precedes all positive
indices. This works for arbitrary constructed rough and classical
all-contour families, including different finite-head cutoffs.

## Filled numerators, actual operators, inverses and moments agree

`ParametricDividedDifferenceCongruence.lean` proves that filled moving
division depends only on the actual scalar slice and its center.
`ClassicalRoughNormalizationCompatibility.lean` then proves equality of
whole critical numerator functions, including their filled center values.
Exact sheet equality gives equality of every literal period matrix entry.

Equality on the full single-coordinate basis identifies the bounded
operators. Left/right inverse uniqueness identifies their inverses.
Equality of the genuine Hilbert numerator realizations then identifies
the normalized entire numerators and every literal moment, with all
constants and the original contour retained.

`ClassicalAllContourPeriodData.exists_rough_normalization_compatibility`
constructs a rough normalized family for any actual continuous period
inverse, together with one continuous-source neighborhood on which every
numerator and moment agrees. The rough family retains joint entire
analyticity, exact free values, operator inverse norm at most 2, all moment
analyticity, exact zeroth periods and actual rough spectral/contour data.
The unconditional odd-moment theorem instantiates this construction with
the already proved continuous period inverse.

## Analytic propagation supplies a full rough-open neighborhood

A small ball in the stronger continuous norm is not assumed dense in a
rough-open ball. The reusable `DenseLinearAnalyticUniqueness.lean` proves
the needed principle: for a dense bounded complex-linear map L and an
open convex target set containing zero, an analytic scalar function
vanishing near zero after pullback by L vanishes on the whole target set.

The analytic identity theorem first propagates vanishing through the
connected linear preimage of the target set. Continuity and density then
give vanishing throughout the target set. Applied to each actual odd
normalized moment, this transfers the earlier continuous cancellation to
one fixed rough ball. The ball is selected before n,k,l. All original
normalization and analyticity assertions are retained on that ball.

## Source correspondence and remaining obligations

This supplies the actual near-zero rough-topology version of the
analyticity, zeroth normalization and odd cancellation in Lemma 3.1,
clauses (i)–(iii), PDF pages 26–27. It is a dependency of the rough
frequency extension around Theorem 3.4 (page 31). It does not replace
the full source domains or physical frequency identification.

Still open are even collapsed-moment cancellation in the required full
scope, the source's exact nonzero-potential canonical product prefactor,
sharp rough normalized moment estimates and frequency summation,
continuation over the full source neighborhood W, physical Hamiltonian
frequency identity (69), action descent, weighted asymptotics, compact
derivatives and actual Birkhoff/PDE flow identification. The previous
continuous sharp bounds and convergent analytic moment-frequency series
remain available, but their full rough frequency conclusions are not
claimed here. Every main-theorem inventory row remains unverified.

## Validation and isolation

Seven new own modules are selected for strict checking. All 334 previously
selected Lean sources remain unchanged. No new external branch sources
are imported; all six earlier provenance records remain valid.
`VALIDATION.md` and `source.json` record the completed full build and
transitive axiom audit. Builds use pinned Lean 4.33.1/mathlib v4.33.1,
default heartbeats, warnings as errors and private outputs. Only propext,
Classical.choice and Quot.sound are permitted. No placeholders, extra
axioms, heartbeat increases, disabled linters or warning exceptions are
introduced; canonical main stays read only.
