# Appendix D: infinite products

## Positive proof steps and direct constant corrections

The [paired factors](../NLS/ZakharovShabat/AppendixDPairedFactors.lean) in D.4
now have their exact cancellation identities and absolute convergence.
The [exterior denominator estimate](../NLS/ZakharovShabat/AppendixDExteriorGeometry.lean)
in D.5 retains the printed factor four, including disc boundaries.

The [D.6 cutoff](../NLS/ZakharovShabat/AppendixDFactorCutoff.lean) uses abs(n)
and c on both head/tail terms. One cutoff works before all indices
and disc points, giving the positive signed-product inequality.
The [square-row energy](../NLS/ZakharovShabat/AppendixDSquarePower.lean)
retains c^p and the p norm, including the range 1 < p < 2.

Four modules add one definition, eleven positive theorems and six
examples. The constants and displayed inequality are corrected
directly, with no new refutation.

The full check passed: 8,588 build jobs, 7,703 public examples and an axiom audit of 44,763 NLS declarations. The 21 inherited warnings match the preceding check; there are no new warnings.

The thirty-group ordered Appendix D comparison remains in progress,
including further intermediate proof assertions. The
[broader completion qualifications](COMPLETENESS.md) remain.

This compares printed pages 126–130 with the canonical Lean statements.
It includes the unnumbered separation assertion before D.4. All nine
named results have implementations in the scopes below; D.3 requires
the signed-sum interpretation and D.8 uses a removable extension.
This is an appendix audit, not a certificate for the whole dissertation.

| Source assertion | Public entry points | Verified scope |
| --- | --- | --- |
| D.1 | `norm_tprod_one_add_sub_one_le_signed_sum` | The exact bound with the norm of the signed sum, the square sum, and exp(S+S²); absolutely summable complex factors, each of norm at most 1/2. |
| D.2 | `norm_tprod_one_add_sub_one_le_exp_sub_one_le` | Both inequalities with exp(S)-1 and S exp(S); no individual smallness assumption. |
| D.3 | `norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` | The subtracted linear term is the complex sum; the quadratic term retains the factor 1/2. |
| Separation before D.4 | `exists_uniform_displacedRoots_separation` | Every injective displaced lattice with finite ell^p displacement, including p=1, has one positive separation for all distinct indices. |
| D.4 | `tendsto_appendixDDeletedProduct`, `analyticOnNhd_appendixDDeletedProduct`, `analyticOrderAt_appendixDDeletedProduct` | Literal negative symmetric products, joint entire dependence, and exactly the retained root multiplicities, for every finite p>=1. |
| D.4 reciprocal | `tendsto_inv_appendixDDeletedProduct`, `meromorphicOrderAt_inv_appendixDDeletedProduct` | Literal reciprocal cutoffs converge away from retained roots; reciprocal pole orders equal minus the retained multiplicities. Simple sequences give simple poles. |
| D.5 | `exists_local_appendixDProduct_div_sin_sup_lt` | The exact exterior of the open quarter-pi discs, including boundaries. For each tolerance, one displacement neighborhood and positive spectral threshold give the strict supremum bound, for every finite p>=1. |
| D.6 | `sourceLemmaD6_multipliable`, `sourceLemmaD6` | Arbitrary bounded reference and numerator displacements with ell^p difference, 1<p<infinity. The printed tail separation gives convergence and bounds on actual powered disc suprema. |
| D.7 | `sourceRemarkD7_mem`, `sourceRemarkD7`, `sourceRemarkD7_uniform` | The literal signed quadratic remainder has its disc supremum in ell^(p/2), including p<2. This gives the printed sum-space result with zero ell^(1+) component. |
| D.8 | `sourceLemmaD8_uniform`, `sourceLemmaD8`, `sourceLemmaD8_off_center`, `sourceLemmaD8_center` | Both multiplicative and additive errors lie in ell^p over all discs and arbitrary independent samples, with constants uniform on displacement norm balls. |
| D.9 | `sourceLemmaD9_uniform`, `sourceLemmaD9`, `sourceLemmaD9_of_cutoff_limits` | The full negative product has an ell^p sine error at every independently chosen disc sample; actual disc suprema and local uniformity are proved. |

The estimates D.1–D.3 are in
[`SignedProductEstimates.lean`](../NLS/ComplexAnalysis/SignedProductEstimates.lean).
The product normalization, multiplicities, and reciprocal convergence are in
[`AppendixDSineProducts.lean`](../NLS/ZakharovShabat/AppendixDSineProducts.lean),
[`AppendixDProductMultiplicities.lean`](../NLS/ZakharovShabat/AppendixDProductMultiplicities.lean),
and [`AppendixDSimpleRoots.lean`](../NLS/ZakharovShabat/AppendixDSimpleRoots.lean).
Separation and the exterior bound are in
[`DisplacedRootsSeparation.lean`](../NLS/ZakharovShabat/DisplacedRootsSeparation.lean)
and [`AppendixDExteriorAsymptotic.lean`](../NLS/ZakharovShabat/AppendixDExteriorAsymptotic.lean).
The remaining entry points are in
[`SourceLemmaD6.lean`](../NLS/ZakharovShabat/SourceLemmaD6.lean),
[`SourceRemarkD7.lean`](../NLS/ZakharovShabat/SourceRemarkD7.lean),
[`SourceLemmaD8.lean`](../NLS/ZakharovShabat/SourceLemmaD8.lean), and
[`SourceLemmaD9.lean`](../NLS/ZakharovShabat/SourceLemmaD9.lean).

## Convergence and uniformity

The sine products use symmetric integer cutoffs. The absolutely
summable products in D.1–D.3 and the separated ratios in D.6 use
unconditional infinite products. These convergence notions are kept
distinct. The finite-exponent endpoint p=1 belongs to D.4–D.5; D.6–D.9
assume p>1 as printed.

D.6 chooses its constants before both displacement sequences and both
cutoffs, using only the separation constant, exponent, reference norm
bound, and difference norm bound. It proves both a p-power bound and
the literal linear-norm right side printed in the source. Every later
cutoff is allowed, so the source's additional small-tail cutoff is
covered without imposing it. Simplicity of the reference is also
unneeded for this stronger tail result. D.7 concerns those separated
tail discs; it does not assert a bound on unseparated head discs that
may contain poles.

## Corrections and conventions

D.1 defines A as the magnitude of the complex sum. D.3's subtracted A
must instead mean that complex sum itself.
[`ProductEstimateNotation.lean`](../NLS/ComplexAnalysis/ProductEstimateNotation.lean)
proves that the literal magnitude interpretation fails for a single
negative coefficient. The corrected signed formula is proved with the
printed constants. See [source discrepancies](../SOURCE_ERRATA.md).

D.8's sine quotient has value cos(pi*n) at its removable center.
`sourceLemmaD8_off_center` proves the literal quotient away from that
point; `sourceLemmaD8_center` proves the filled value. Equality with
Lean's totalized 0/0 is not asserted. D.9 retains the full product's
negative normalization when restoring the omitted factor.

## Verification evidence

Existing public checks cover signed cancellation, the D.3
counterexample, repeated roots and poles at p=1, exterior disc
boundaries, a nonzero bounded reference displacement, vanishing
numerator factors, the p=3/2 half-exponent case, negative omitted
indices, both sine-quotient center signs, arbitrary cutoff-defined
products, and constants chosen before inputs and samples. The current
full build and axiom-audit totals are recorded in [status](../STATUS.md).

## Absolute convergence in the introductory paragraph

The unnumbered paragraph on p.126 defines convergence as existence of a
finite limit of ordered partial products. It permits zero factors and a
zero limit. Absolute convergence means convergence of the corresponding
positive products of 1+|a_n|.
The public source statements use the exact inclusive cutoffs 1≤n≤N,
with a proved finite reindexing and no constraint on the unused zeroth term.

[`AbsoluteProductConvergence.lean`](../NLS/ComplexAnalysis/AbsoluteProductConvergence.lean)
proves that this absolute convergence is equivalent to summability of
|a_n|. The necessity follows from 1+sum|a_n|≤product(1+|a_n|) on every
finite cutoff and boundedness of a convergent sequence. The sufficiency
and convergence of the complex products follow from the summable norm
criterion. The unordered positive products satisfy the same equivalence
for an arbitrary index type, including the integers.

The ordered complex limit is the genuine unconditional product, also
when a factor vanishes. Under the summability condition, it is nonzero
exactly when every factor is nonzero. The positive majorant limit lies
between 1+sum|a_n| and exp(sum|a_n|).

A sequence with every perturbation equal to -1 has complex partial
products eventually equal to zero, while its positive majorant products
have no finite limit. Thus ordinary convergence in the source's stated
sense need not be absolute. This is a distinction between the definitions,
not an error in the source.

Four examples check an absolutely convergent product containing a zero
factor, ordinary convergence without absolute convergence, both limit
bounds, and the nonvanishing criterion with signed indices. The module
and focused examples compile without new warnings; full repository
validation is recorded in [STATUS.md](../STATUS.md).
