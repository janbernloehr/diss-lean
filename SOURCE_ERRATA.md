# Source discrepancies

## Lemma G.2: arbitrary-time first inequality under the integral H1 convention

Source: dissertation, printed page 135. This is a **norm-qualified** failure,
not a refutation of every possible interpretation of the unspecified interval
norm. Define the local H1 norm as the square root of the integral of the
squared magnitudes of both potential components and both derivatives.

For the smooth period-one constant potential phi=(1,0), t=1/4 and z=2*pi,
that norm is 1/2. The actual weighted Hermitian first Born operator norm is
1/(2*pi). The first displayed G.2 right side, using this local norm, equals
5/(16*pi), which is strictly smaller. `lemmaG2_firstBorn_integralNorm_counterexample`
proves the strict inequality, while `g2IntegralNormTestPotential_admissible`
checks smoothness, periodicity, and the nonzero spectral parameter. The exact
original oscillatory kernel is evaluated by
`oscillatoryIntegral_const_quarter_period`; no numerical approximation is used.

Consequently this local integral convention cannot validate the printed
first inequality for all nonnegative times. A different interval norm
convention or a change in the estimate would need separate justification.
We do not select such a correction here. The second, unit-interval remainder
bound **does hold** in this same integral H1 norm: it is independently proved
by `l2HermitianRemainder_le_unit_H1`, using a combined endpoint estimate and
G.1. Its factor 3/(2*abs(z)) and coefficient 1+norm(phi)_2 exp(norm(phi)_2)
are unchanged. The same unit-interval consequence is now also proved in
Chapter 5's exact periodic Fourier norm by `sourceLemmaG2_remainder_unit`,
using a constant-one comparison with the integral norm. That theorem does
not select a norm convention for the arbitrary-time local statement.

## The proof of Lemma F.2: a common-path coefficient and a real majorant

Source: dissertation, printed page 134, visually checked in the PDF.
These issues concern intermediate formulas in the proof. The analyticity
statement of F.2 is proved unchanged by identifying actual endpoint
integrals with the already constructed joint analytic primitive.

In (F.3), the common integral from tau_n to nu has coefficient 1/(2*i).
Both endpoint integrals contain that same common path. Averaging therefore
retains its full coefficient 1/i=-i; only the two short endpoint pieces
are halved. `appendixF_shared_path_normalization` proves the exact splitting
algebra, and `appendixF_half_coefficient_ne` proves that the printed half
coefficient differs whenever the common integral is nonzero. The actual
free endpoint average has value -i*nu+i*pi*n, checked nontrivially at n=0,
nu=i, where its value is 1.

The displayed majorant g_k(t)=sqrt(t+|epsilon_k|)/sqrt(t-|epsilon_k|) is
not a real-valued expression for 0<t<|epsilon_k|. It therefore cannot
justify the claimed estimate on all of [0,1] as written. Under Lean's
totalized real square root and division it is zero on that interval.
`appendixF_printed_majorant_counterexample` uses epsilon=i/2, t=1/4,
and w=sqrt(5/16): w^2=t^2-epsilon^2, the actual normalized quotient t/w
has strictly positive norm, while the printed majorant is zero. Thus no
finite constant repairs that pointwise bound under this interpretation.
The imaginary epsilon also avoids a real-parameter root singularity in
the example. An absolute value in the denominator and a treatment of the
moving singularity would be needed for a real-majorant repair; such a
repair is not used or claimed by the formalization.

The formal route constructs finite polygonal integrals, proves their
improper endpoint limits and agreement with admissible C1 curve integrals,
and identifies both endpoint values with the analytic primitive. This
supplies F.2 directly, including complex collapsed gaps.

## Lemma E.2: the neighborhood must meet the real space

Source: dissertation, printed page 131 (visually checked in the PDF).
E.2 calls U an open connected "neighborhood" without specifying its base
point. The proof begins near u in U intersect X_R, so that intersection
must be nonempty. If "neighborhood" means a neighborhood of a real point,
this is the intended condition, not a change to that interpretation.
Both applications in the dissertation use neighborhoods of real-type
potentials and satisfy it.

The reading as an arbitrary nonempty open connected complex domain is
false. `sourceLemmaE2_realSlice_condition_needed` proves the counterexample
X_R=R, X=C, U the ball of radius 1/2 about i, and f identically one.
U is open and connected and its real slice is empty, so f vanishes there
vacuously, but f(i)=1. Nonemptiness of U alone is insufficient.

`sourceLemmaE2` proves the identity with the necessary nonempty real slice
explicit. `sourceLemmaE2_of_real_point` gives the equivalent real-neighborhood
formulation. Neither theorem adds convexity or a contraction condition on
the real and imaginary projections. The general statement uses continuous
complexification coordinates and includes the source's Banach-space case.

## Lemma E.1: the cardinal product must omit the diagonal index

Source: dissertation, printed pages 130-131. The displayed interpolation
formula on page 130 (visually checked in the PDF) writes the product over
m in Z of (sigma_m-z)/(sigma_m-sigma_n). Its factor at m=n has denominator
zero. The residue calculation on page 131 explicitly uses m != n, and
solving that identity gives the omitted-index cardinal product.

`appendixE_all_index_cutoff_eq_zero` proves that every symmetric cutoff
containing n is zero if the all-index formula is interpreted using Lean's
totalized division. This cannot be treated as the intended cardinal
product. `tendsto_appendixEInterpolationKernel` instead proves convergence
of the literal omitted-index cutoffs. The kernel equals one at its own
root and zero at every other root, with the exact derivative normalization.

`sourceLemmaE1_literal` proves the resulting interpolation formula for
all 1 <= p < infinity, including p=1, with the printed circle-supremum
hypothesis. Both infinite operations are specified as symmetric cutoff
limits, as supplied by the source circle proof; no unconditional sum or
absolute convergence is asserted. A focused nonzero example reconstructs
sinc(0)=1 from the simple lattice with its zero-index root moved to i.

## Remark D.3: the subtracted linear term must be the complex sum

Source: dissertation, printed pages 126–127 (visually checked in the PDF).
D.1 defines `A = |sum_m a_m|`, `B = sum_m |a_m|^2`, and `S = sum_m |a_m|`.
D.3 then writes `|prod_m (1+a_m)-1-A| <= |A|^2 exp(S)/2 + B exp(S+S^2)`.
Literal reuse of D.1's nonnegative A in that subtraction is false.

`ProductEstimateNotation.lean` supplies the admissible integer sequence
`a_0=-1/4`, with all other terms zero. It is absolutely summable and every
coefficient has norm at most 1/2. Its product is 3/4, so the literal left
side is 1/2. The right side is `exp(1/4)/32 + exp(5/16)/16`, less than
9/32 since both exponentials are less than 3. The theorem
`printed_D3_absolute_linear_term_fails` verifies the contradiction in Lean.

Taking A to be the **complex sum** in D.3 gives the valid Taylor refinement.
`norm_tprod_one_add_sub_one_sub_tsum_le_signed_square` in
`SignedProductEstimates.lean` proves that interpretation, retaining the
printed 1/2 and `B exp(S+S^2)` constants. The same module proves D.1 with
its printed absolute sum and both inequalities of D.2. No redefinition is
silently applied to the literal source statement.

## Appendix C.1: ordinary Hilbert transform is not an isomorphism

Source: dissertation, Lemma C.1, printed page 125. The operator is
`(Hx)_n = sum_{m != n} x_m/(m-n)`. The assertion that it is a Banach-space
isomorphism for every 1 < p < infinity is false already at p=2.

`HilbertKernelFactorization.lean` proves h(n)=t(n)+t(n-1), with t in ℓ²
and h(n)=-1/n (zero on the diagonal). For the finitely supported sequence
`a_N(k)=(-1)^k` on 0,...,N, `HilbertNotIsomorphism.lean` proves

```
||a_N||₂² = N+1
H a_N = t + (-1)^N shift_(N+1) t
||H a_N||₂ <= 2 ||t||₂.
```

Consequently `discreteHilbert_not_bounded_below` rules out every nonnegative
constant C satisfying `||a||₂ <= C ||Ha||₂` for all a. The theorem
`hilbertTransform_two_no_left_inverse` rules out any bounded linear left
inverse of the completed transform, and `hilbertTransform_two_ne_equiv`
rules out its equality with any continuous linear equivalence. A generic
version applies to any bounded operator agreeing with the printed formula
on finite inputs, so the obstruction is independent of the construction.

The correction is to assert boundedness, which `HilbertBoundedness.lean`
already proves for every 1 < p < infinity. Neither failure of injectivity
nor the corresponding obstruction at every other exponent is asserted here.
Existing library proofs never used the false invertibility assertion.
The source proof of Lemma C.2 uses only the boundedness part of C.1.
`ModifiedHilbert.lean` now proves C.2 with its full two-lattice hypotheses,
exact normalization, and uniform dependence on the specified norms.

## Theorem 1.1: unresolved printed height above two

The printed central box uses `(1+8‖φ‖ₚ)^p`. The Neumann criterion in
Corollary 3.3 is `(4p/H^(1/p)+1/H)‖φ‖ₚ < 1` at height H.
`PrintedHeight.lean` proves that the printed height satisfies this criterion
for all 1 ≤ p ≤ 2, extending the previous Hilbert-only result.

For p > 2 and M ≥ 1/(4p-8), `printed_height_neumann_bound_fails` proves
that the same criterion is strictly greater than one at H=(1+8M)^p.
Failure of a sufficient condition is not a spectral counterexample.
The literal general-exponent height remains unresolved, not disproved;
`(1+8pM)^p` is a proved alternative but does not complete the printed claim.
See [the spectral overview audit](coverage/SPECTRAL_OVERVIEW.md) for the
source-space counting and projection conclusions now proved for p ≤ 2.

## Lemma 26.2: sign of the higher Hamiltonian

Source: [dissertation, Lemma 26.2](https://janbernloehr.de/Download/fs16/diss.pdf#page=113).
The statement and proof contain the factor `(-1)^(m+1) 2^m H_(2m+1)`.
However, [Theorem 24.1, equation (5.4)](https://janbernloehr.de/Download/fs16/diss.pdf#page=107)
states `sum_n J_(n,k) = H_k / 2^(k-1)`. At `k = 2m+1` this gives

```
8^m sum_n J_(n,2m+1) = 2^m H_(2m+1).
```

The additional sign agrees at odd `m` and disagrees at even `m` unless
`H_(2m+1) = 0`. The repository retains the physical Hamiltonians from
Appendix H; it does not absorb this sign into their definition.

Formal results:

- `eight_pow_mul_tsum_realHigherActions` proves the positive trace equality
  on the real H^m source space.
- `printed_even_trace_identity_iff_zero` proves the precise obstruction
  to the printed equality at every even order.
- `classicalNLSHamiltonian_constant_one_five` independently checks the
  Appendix H recurrence: the constant real-type potential `(1,1)` has
  physical `H_5 = 2`.
- `sourceWeightedAction_summable_and_le_half_mass` proves absolute
  summability and the trace-consistent estimate
  `sum_n ⟨2nπ⟩^(2m) |I_n| ≤ C(P,m) ‖ψ‖²/2 + 2^m H_(2m+1)`, where
  `C(P,m) = (1+16π)^(2m) (1+P)^(4m)` and `P` is the norm of an exact
  π-normalized H¹ realization of the period-one source potential.
- `sourceWeightedAction_le_mass` weakens the half-mass factor to the
  full squared pair norm appearing in the printed remainder.

This establishes the corrected estimate and identifies the error in the
printed proof equality. It does not constitute a formal counterexample
to the entire printed inequality, whose positive remainder must also be
accounted for. The literal signed statement of Lemma 26.2 is not claimed
as a proved result.

## Lemma 27.2: corrected global coefficient and optional endpoint sharpening

Source: [dissertation, Lemma 27.2, page 116](https://janbernloehr.de/Download/fs16/diss.pdf#page=116).
At m=1 the printed conclusion is `H3 ≤ 2S+S²`, where
`S = sum_n ⟨2nπ⟩² I_n`. The final energy estimate used in its proof is
`H3 ≤ S+2M²`, with total action M. Even retaining the stronger available
estimate `H3 ≤ S-M+2M²`, the scalar conditions `0 ≤ M ≤ S` alone do not
imply the conclusion at all sizes.

`Lemma272EndpointArithmetic.lean` proves the precise limitation: the maximum
of `S-M+2M²` over `0 ≤ M ≤ S` is `max(S,2S²)`, and it is at most `2S+S²`
exactly when `S ≤ 2`. The scalar choice M=S=3 permits 18 while the target
is 15. No potential realizing these scalar data and energy is asserted.

`SourceH1EndpointActionBound.lean` proves the literal endpoint for S ≤ 2,
a mass-sensitive sufficient condition, and an unrestricted all-order variant
with twice the printed remainder. `SourceH1EndpointMomentCriterion.lean`
reduces the literal endpoint exactly to a lower bound on the real cubic
moments together with the nonnegative kinetic slack. Thus the missing
spectral input is explicit; the literal unrestricted assertion remains open.

The new `SourcePrimitivePowerCubicLowerBound.lean` proves
`π² I_n³ ≤ 4|γ_n|² R_n` from the actual nonnegative gap profile, with R_n
the cubic moment. Summing gives `H3 ≤ S-M+2M²-D-(π²/3)B`, where
`B = sum_n I_n³/|γ_n|²` is convergent and D is the kinetic slack.
The quotient has the continuous expression `|γ_n|⁴|rho_n|³`, including
closed gaps. This supplies a quantitative sufficient condition using only
actions and gaps, but does not yet prove the comparison needed for all
sources. The unrestricted literal endpoint therefore remains open.

The accepted formalization uses the proved corrected global statement
`sobolevOddHamiltonian_le_twice_weighted_action_remainder`, with twice
the printed remainder for all m ≥ 1. The exact printed bound remains
proved for m ≥ 2; the original unrestricted m=1 coefficient is optional
future work, not a blocker, and has not been disproved.
The downstream proof of Theorem 23.2(ii) treats m=1 directly through
Lemma 27.1 with d=√3. Its higher-order branch absorbs its explicit scalar
constants. Theorem 23.1 and Remark 23.3 inherit that proved bound, so no
exact downstream theorem needs a changed constant.

For comparison, [the cited paper, Lemma 16, page 27](https://arxiv.org/pdf/1403.1369#page=27)
uses the different remainder `(64π)^(2m) (1+M)^(2m-1) S^(2m-1)`.
Its coefficient does not disappear on substituting m=1. This comparison
does not establish a counterexample or justify silently replacing the
constant in the dissertation.

## Lemma 28.1: the final scalar comparison at n=N

Source: [dissertation, proof of Lemma 28.1, page 118](https://janbernloehr.de/Download/fs16/diss.pdf#page=118).
The displayed final comparison is

```
(n+N+2/5)/(n-N+3/10) ≤ 4/3+2N ≤ 2⟨N⟩,
```

under `n ≥ N`, with `⟨N⟩=1+N` for a nonnegative integer cutoff.
At `n=N=1`, the ratio is 8, exceeding `2⟨N⟩=4`.
The subsequent scalar comparison to `2048(1+‖φ‖H¹²)` also fails for
admissible scalar cutoff data: with `n=N=10` and `Q=‖φ‖H¹²=21/16`,
`N < 8Q ≤ N+1` holds, but

```
128 (n+N+2/5)/(n-N+3/10) = 8704 > 4736 = 2048(1+Q).
```

Formal results in `Lemma281BoundaryArithmetic.lean` prove both numerical
counterexamples. They also prove:

- for `n ≥ N+1`, the ratio is at most `2(N+1)`, recovering the scalar
  constant 2048 when `N ≤ 8Q`;
- for `n ≥ N`, the ratio is at most `8(N+1)`, giving an inclusive scalar
  constant 8192 under the same cutoff condition.

This audit concerns the printed scalar implication and supplies no
potential whose actual spectral factor violates the claimed norm bound.
The corrected scalar comparisons alone do not prove the spectral claim.

The actual real-source scalar bound is now proved independently in
`SourceH1ActionGapEstimate.lean`. The central product has squared norm at
most `8(N+1)`, using critical-point membership in ordered real gaps.
Combined with the exterior constant 128, this gives
`‖χ_n‖_gap ≤ 2048(1+P²)` even at the inclusive boundary. Public examples
recover the bound 4736 for the actual real gap factor at n=±10 under the
norm assumption above. This does not validate the false ratio chain.
The real-source version of Proposition 28.2 follows, with the stronger
constant 1536 (and hence the printed 4608).

The complex action estimate of Proposition 28.2 is now proved independently
in `SourceProposition28_2.lean`, on a connected L²-open neighborhood of the
entire real L² locus. It uses the real-type projection and uniform continuity
of the normalized actions; it does not rely on a complex version of the
false ratio chain.

The complex scalar gap-factor bound of Lemma 28.1 is now also proved
independently in `SourceLemma28_1.lean`, including the entire closed gap
and the inclusive cutoff. A sharper real constant 1024 provides room for
a uniform comparison to the real-type projection on finitely many gaps;
a separate uniform complex tail bound of 3 handles all distant gaps.
The neighborhood is connected and L²-open, contains the entire real L²
locus, and can be shared with Proposition 28.2. The actual complex bound
4736 at n=±10 and P²=21/16 is checked publicly. None of these results
validates the printed intermediate scalar comparison disproved above.
