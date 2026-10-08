# Source discrepancies

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
constant 1536 (and hence the printed 4608). The almost-real complex
extension and the printed intermediate spectral ratio remain open.
