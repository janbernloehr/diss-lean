# Appendix C source audit

The source is printed pages 125–126 of *Features of the Nonlinear Fourier
Transform for the dNLS Equation*. Every result below uses finite 1<p<infinity.
C.1's boundedness assertion is proved, and its isomorphism assertion is
refuted throughout that range. C.2 is proved with its literal hypotheses.
The public source theorems are in `NLS.Fourier`.

| Source requirement | Public evidence | Scope |
| --- | --- | --- |
| C.1, actual ordinary series | `sourceHilbert_hasSum`, `summable_norm_hilbertSeries_of_finite` | Every lp input, every integer output index; explicit omitted diagonal and absolute convergence. |
| C.1, boundedness | `sourceLemmaC1_bounded` | A unique complex continuous linear operator with the actual convergent coefficient formulas and norm bound `hilbertTransformBound`. |
| C.1, printed isomorphism claim | `sourceLemmaC1_not_bijective`, `sourceLemmaC1_no_isomorphism`, `sourceLemmaC1_no_linearEquiv` | Refuted for every finite p>1, including algebraic linear equivalences satisfying the source series. |
| Growing alternating inputs | `HilbertLpObstruction.norm_block_rpow` | Exact lp norm power N+1 for the finite block with coefficients (-1)^k, 0<=k<=N. |
| Bounded transformed blocks | `HilbertLpObstruction.transform_block`, `norm_transform_block_le` | Exact two-translate formula and a bound independent of N. |
| No lower bound or left inverse | `HilbertLpObstruction.not_bounded_below`, `no_left_inverse` | Any continuous linear operator agreeing with the source on finite inputs; every finite p>1. |
| C.2, original perturbed series | `sourceModifiedHilbert_hasSum`, `summable_norm_modifiedHilbert_source_series` | Exact pi factor, explicitly omitted diagonal, and absolute convergence on every input. |
| C.2, uniform operator construction | `sourceLemmaC2` | One constant before both lattices, followed by the unique operator; depends only on p, c and the two displacement norm bounds. |
| Explicit C.2 bound | `norm_modifiedHilbert_le` | `C_p + c*(norm(s)+norm(r))*norm(hilbertSquareCoeffs)`. |
| Normalization check | `modifiedHilbert_common_constant` | Any common constant complex translation recovers the ordinary operator exactly. |

## Ordinary transform and the isomorphism discrepancy

[`AppendixCSourceTransform.lean`](../NLS/Fourier/AppendixCSourceTransform.lean)
packages the ordinary formula

    (H a)(n) = sum_(k != n) a(k)/(k-n).

The underlying full-range boundedness and all-input absolute convergence
are in [`HilbertBoundedness.lean`](../NLS/Fourier/HilbertBoundedness.lean) and
[`HilbertSeries.lean`](../NLS/Fourier/HilbertSeries.lean). Equality of every
convergent row proves uniqueness of the operator.

[`HilbertKernelFactorization.lean`](../NLS/Fourier/HilbertKernelFactorization.lean)
constructs t in every lp space with p>1 such that the kernel -1/n is
t(n)+t(n-1), including the zero diagonal. The extension in
[`HilbertNotIsomorphismLp.lean`](../NLS/Fourier/HilbertNotIsomorphismLp.lean)
then proves, for a_N(k)=(-1)^k on 0,...,N,

    norm(a_N)^p = N+1,
    H a_N = t + (-1)^N shift_(N+1) t,
    norm(H a_N) <= 2 norm(t).

Thus no uniform lower norm bound exists and no continuous linear left
inverse exists. If H were bijective, the Banach inverse theorem would give
such an inverse. This proves non-bijectivity at every exponent in C.1.
Any algebraic linear equivalence satisfying the printed series would equal
this same bounded H, so it is excluded as well. No nonzero-kernel assertion
or separate failure-of-surjectivity assertion is inferred.

This strengthens the earlier exponent-two counterexample. The corrected
source assertion retains boundedness. See [the source discrepancy](../SOURCE_ERRATA.md).

## Perturbed lattices and the uniform constant

For arbitrary s,r in complex l-infinity, the nodes are
sigma(n)=pi*n+s(n) and rho(k)=pi*k+r(k). The exact hypothesis is

    c^(-1)*|k-n| <= |rho(k)-sigma(n)|,  k != n,  c>0.

[`ModifiedHilbertKernel.lean`](../NLS/Fourier/ModifiedHilbertKernel.lean)
uses it to dominate the difference from the ordinary reciprocal kernel by
a summable reciprocal-square kernel.
[`ModifiedHilbert.lean`](../NLS/Fourier/ModifiedHilbert.lean) constructs the
bounded correction and adds the ordinary operator. The source theorem
chooses its constant before s and r with prescribed norm bounds S and R;
no smallness, reality, ordering, or finite-support condition is introduced.

The diagonal term remains omitted even if rho(n) differs from sigma(n).
A unit input at n therefore has zero output at n. The factor pi is retained
in the convergent series, and any common translation cancels exactly.
Only the valid boundedness part of C.1 is needed for C.2.

The reciprocal-square correction also works at p=1 and p=infinity. No such
endpoint extension is claimed for the full ordinary or modified transform.

## Validation scope

Twenty new public checks exercise exponents 3/2, 2 and 4; a negative output
index; the unique ordinary operator; the all-exponent obstruction, exact
block norms and absence of left inverses; C.2 with constants chosen before
large norm balls; complex linearity; absolute convergence; the omitted
diagonal; arbitrary common translations; and the correction's endpoints.
