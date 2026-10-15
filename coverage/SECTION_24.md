# Section 24: original higher actions and physical trace formulas

This audit covers printed pp. 106–107 and the related trace outline on
p. 105. The original higher-action definition, formulas (5.2), (5.4),
(5.5), and (5.6), reality, odd-level positivity, and vanishing on collapsed
complex gaps are implemented. The general zero-detection claim and the
final asymptotic sentence still require separate work; this is not a
certificate that all of Section 24 is complete.

## Original actions and domains

[`SourceIndexedHigherAction.lean`](../NLS/ZakharovShabat/SourceIndexedHigherAction.lean)
defines `sourceIndexedHigherAction hp hp1 n k` by the original isolating
circle integral with factor 1/((k+1)π). Lean's natural number k denotes
the spectral power, so the printed level is k+1. At k=0 it is exactly
`sourceIndexedAction`, including the off-domain fallback. Every original
isolating circle computes the same value at complex sources.

[`SourceHigherActionPiecewiseContour.lean`](../NLS/ZakharovShabat/SourceHigherActionPiecewiseContour.lean)
proves the literal piecewise C¹ contour formula on the original cut disk.
The integral is the indexed higher action times the winding integral
about the selected midpoint. This includes repeated and reversed
traversals; winding-one circuits compute the indexed action.

[`SourceIndexedHigherActionAnalytic.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionAnalytic.lean)
proves scalar analyticity on the full original Section 11 contour domain.
The retained Section 19/20 domain U supports all the stronger sequence and
trace assertions below. U is already part of the original family and is
not shrunk for a level, index, Sobolev order, or potential.

[`SourceSection24Original.lean`](../NLS/ZakharovShabat/SourceSection24Original.lean)
packages the results as `SourceSection24Data`, extending the same
`SourceSection23Data`. `SourceSection23Data.section24` augments any chosen
family without changing its domain; `sourceSection24_original` constructs
one family before all levels and Sobolev orders. The original Birkhoff
map, indexed ordinary actions, Section 19 primitive, and Sections 20–23
results remain the same.

## Full complex-domain convergence and traces

The extension from real-centered germs to every complex point of U uses:

- [`SourceFullAbelianSymmetricAnalytic.lean`](../NLS/ZakharovShabat/SourceFullAbelianSymmetricAnalytic.lean): two exterior root values recover analytic midpoint and squared-gap coordinates on each entire Cauchy source ball.
- [`SourceIndexedHigherActionCauchy.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionCauchy.lean): original isolating contours, scalar analyticity, and the boundary formula on that whole ball, simultaneously at every index and level.
- [`SourceIndexedHigherActionBound.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionBound.lean): one local pair of positive constants bounds every higher action by the squared gap times its polynomial spectral weight around every complex point of U.
- [`SourceIndexedHigherActionWeighted.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionWeighted.lean) and [`SourceIndexedHigherActionSobolev.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionSobolev.lean): actual ℓ¹-valued analytic sequences, exact coordinates, absolute convergence, and analytic literal sums through printed level 2s+1 on all of Hˢ_c ∩ U.
- [`SourceHigherSobolevDenseInclusion.lean`](../NLS/ZakharovShabat/SourceHigherSobolevDenseInclusion.lean) and [`SourceIndexedHigherActionTrace.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionTrace.lean): connectedness of the full Sobolev preimage and analytic continuation of the physical real trace.

The Hamiltonians are the independently defined physical Riccati
functionals. They are not defined by the action sums. All sums run over
ℤ, and each displayed trace has a separately proved absolute-convergence
assertion.

| Source assertion | Public entry point | Scope |
| --- | --- | --- |
| Level one is the ordinary action | `sourceIndexedHigherAction_zero` | Every source, with identical defaults. |
| Formula (5.2) | `SourceSection24Data.higherAction_eq_original_primitive` | Every source in U, every original isolating circle, every level, any retained primitive index. |
| Mass trace (5.3) | `SourceSection24Data.trace 0 0` | The physical H₁ trace on H⁰_c ∩ U; at real sources this is the existing mass/Parseval identity. The squared-norm interpretation is real-source only. |
| Theorem 24.1 / (5.4) | `SourceSection24Data.trace_printed_level` | Every printed level k≥1 on the entire H^(k−1)_c ∩ U, with factor 1/2^(k−1). |
| Odd-order trace following (5.4) | `SourceSection24Data.odd_trace` | Every m≥1 on all Hᵐ_c ∩ U, with positive factor 1/4ᵐ. The m=0 case is the mass trace. |
| Formula (5.5) | `sourceIndexedHigherAction_eq_gapIntegral` | Every real source, signed index, and level; the literal original endpoint interval and discriminant arcosh profile, including collapsed gaps. |
| Reality and odd-level nonnegativity | `sourceIndexedHigherAction_real`, `sourceIndexedHigherAction_even_nonneg` | All real sources; Lean power 2m means printed level 2m+1. |
| Odd-level zero detection | `sourceIndexedHigherAction_even_eq_zero_iff` | Every real gap, including central gaps crossing zero. |
| Collapsed complex gaps | `SourceSection19Data.indexedHigherAction_of_collapsed` | Every source in U and every level. |
| Mean-value formula (5.6) | `sourceIndexedHigherAction_eq_power_mul_action` | In fact every natural spectral power, with ζ in the actual closed real gap and the original indexed ordinary action. No division by that action. |

The real assertions are in
[`SourceIndexedHigherActionReal.lean`](../NLS/ZakharovShabat/SourceIndexedHigherActionReal.lean),
[`SourceRealHigherActionPositive.lean`](../NLS/ZakharovShabat/SourceRealHigherActionPositive.lean),
and [`SourceRealHigherActionIntegral.lean`](../NLS/ZakharovShabat/SourceRealHigherActionIntegral.lean).

## Corrections to the Section 23 outline

[`SourceSection23TraceCorrections.lean`](../NLS/ZakharovShabat/SourceSection23TraceCorrections.lean)
constructs actual-source counterexamples to two independent errors in the
p. 105 trace. A source with only I₀=1 has every positive-index higher
action sum equal to zero, while its physical H₃ is at least one. Thus the
restricted index set n≥1 fails already at printed level three.

At printed level five, an actual finite-gap source has H₅>0. Its full
integer higher-action sum equals H₅/16 and cannot equal −H₅/16. Thus the
alternating sign remains incorrect even after restoring the full index
set. The correct odd trace is the full integer sum H_(2m+1)/4ᵐ, agreeing
with Theorem 24.1. See [source discrepancies](../SOURCE_ERRATA.md).

## Validation and remaining work

Thirty-three new public checks cover non-Hilbert exponent three, complex
sources, circle independence, piecewise contours, negative indices,
central open gaps, the literal gap integral, mean-value comparisons,
complex collapsed gaps, exact ℓ¹ coordinates, connected full Sobolev
domains, the mass endpoint, factors two/four/sixteen, the sharp Hᵐ trace,
and the unconditional original-family constructor. Both outline
counterexamples are checked through the original indexed actions.
Full validation is recorded in [implementation status](../STATUS.md).

The sentence after (5.6) asserting the precise two-sided-index asymptotic
still needs a public theorem with its limiting filter and normalization.
The p. 106 claim that every higher-level action vanishes only at a
collapsed gap is not established here: the proved converse is for odd
printed levels at real sources. Its even-level and complex-source scope
must be audited before marking that sentence covered. Existing
[Section 14 qualifications](SECTION_14.md) also remain. The dissertation
is incomplete; Section 25's original localization audit follows these
remaining Section 24 assertions.
