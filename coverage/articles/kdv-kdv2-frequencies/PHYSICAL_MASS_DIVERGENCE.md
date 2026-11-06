# Global physical mass obstruction for Theorem 1.12(v)

All eleven complete main theorem rows remain OPEN. This proves the mass and actual smooth physical approximation component of part (v) globally, at every genuinely non-L2 real mean-zero datum in its stated -1<s<0 range. It also covers s=-1. It does not assert the full KdV2 frequency or physical solution-map obstruction.

## Original source mass divergence

`NLS.KdV.tendsto_original_L2_norm_sq_atTop_of_nonL2_hminus_limit` proves: for ANY filter of ORIGINAL weighted L2 inputs whose literal `hillOriginalHminusSource` converges to q in H-minus-one, if the raw unit-period coefficients of q are not in L2, then the original squared L2 norms tend to positive infinity. Neither reality nor finite-gap hypotheses nor spectral chart smallness are required.

The proof uses continuous H-minus-one evaluation at each raw coefficient. The squared norm of each original input bounds every finite sum of squared unit-period coefficients because the original source is EXACT even sampling of its period-two coefficients and that sampling is contractive. Raw non-L2 membership gives genuine nonsummability; finite nonnegative coordinate sums then force divergence. No conclusion is inferred from a totalized nonsummable tsum.

`tendsto_original_half_L2_norm_sq_atTop_of_nonL2_sobolev_limit` transports native H^s convergence through the actual continuous Sobolev inclusion for s>=-1, preserving every raw coefficient, and proves divergence with the physical factor one half.

## Actual physical H_0 normalization

For EVERY continuous unit-period circle potential Q, the shared theorem `norm_sq_hillContinuousCoefficients_eq_integral_norm_sq` proves exactly

```text
norm(hillContinuousCoefficients Q)^2 = integral_[0,1] |Q(x)|^2 dx.
```

The original Fourier convention has physical period two and Parseval factor one half on [0,2]. Unit periodicity makes its full-period integral exactly twice the [0,1] integral. This accounts for the normalization explicitly. For real Q, `classicalQuadraticInvariant_re_eq_half_hillContinuousCoefficients_norm_sq` proves

```text
Re(classicalQuadraticInvariant Q)
  = (1/2)*norm(hillContinuousCoefficients Q)^2
  = (1/2)*integral_[0,1] Q(x)^2 dx.
```

Thus `tendsto_physical_H0_atTop_of_nonL2_sobolev_limit` applies to the ACTUAL classical physical invariant, along EVERY real continuous unit-period physical approximation in native H^s, s>=-1, at EVERY raw non-L2 datum. No local rough inverse is used.

## Actual smooth approximants and relative topology

`NLS.KdV.exists_smooth_original_physical_sobolev_approximation` constructs actual C-infinity real mean-zero unit-period circle potentials Q_i at EVERY real mean-zero native H^s datum q, for every real s. Their EXACT original even Fourier coefficients define v_i in the SAME H^s Hilbert space, and v_i tends to q in that native norm. Every v_i remains real and mean-zero. The construction uses symmetric raw Fourier truncation and the existing verified finite physical realization; it assumes neither an L2 bound nor a spectral gap condition.

The article theorem `exists_smooth_physical_approximation_with_H0_divergence` combines this with the non-L2 mass theorem. Its quantifiers cover every genuinely non-L2 real mean-zero q, not only a small neighborhood of zero or selected inverse images.

`not_continuousWithinAt_physical_H0_extension_of_nonL2` proves that ANY real-valued function agreeing with the ACTUAL smooth real mean-zero physical invariant fails continuity at q even WITHIN the real mean-zero subspace equipped with the native H^s topology. A hypothetical relative continuity would give a finite limit along the constructed smooth real mean-zero approximants, contradicting their diverging H_0.

## Exact KdV2 mass term and remaining obligations

`tendsto_kdv2_physical_mass_term_atTop_of_nonL2_sobolev_limit` proves divergence of the EXACT source mass contribution

```text
20*(2*n*pi)*Re(classicalQuadraticInvariant Q_i)
```

for EVERY positive mode n, along EVERY real continuous physical approximation of a genuinely non-L2 datum in native H^s, s>=-1.

To conclude Theorem 1.12(v), the ACTUAL KdV2 frequency still must be identified with this mass term, its leading fifth power and the correct renormalized correction. The required correction extension/continuity on -1<s<0 and the actual PDE phase/solution-map obstruction remain separate proof obligations. The existing analytic second-moment H-minus-one series alone does not prove the full KdV2 second/fourth-moment cancellation. No complete main theorem is marked verified.

## Validation

All 2372 previously selected source bytes and all 39 provenance records remain unchanged. Four new own modules reuse the already reachable verified library without shared-source replacements.

Prior strict evidence retained for all 2372 unchanged selected baseline sources. All four new own proof modules strictly rebuilt in dependency order, followed by a fresh combined transitive axiom audit of all 2376 selected modules. Exact checker/audit/coverage/evidence selections, transitive selected order and reachability, 2418 frozen source/checker/provenance/Mathlib-source hashes, all 39 unchanged verified provenance records, private fresh outputs and unchanged clean canonical main verified. The NLS import closure adds exactly these four selections; no new shared-source import is needed. No full 2376-module rebuild is claimed.

Fresh audit: 18823 selected and 40893 imported NLS declarations. Four own modules contain 12 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no new axioms or proof-checking exceptions. All eleven main theorem rows remain OPEN.
