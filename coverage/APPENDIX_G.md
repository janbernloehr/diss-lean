# Appendix G: current source audit

This compares the statements on printed pages 135–138 with the public Lean
API. It supersedes historical Appendix G progress notes in `COVERAGE.md`.
It is not a completeness certificate for the dissertation. The G.3 proof
line discussed below was checked in the rendered PDF on printed page 136.

| Source item | Authoritative entry points | Current scope |
| --- | --- | --- |
| Opening continuity and analyticity assertion | `continuous_l2PeriodicFundamentalMatrix_joint`, `analyticOnNhd_l2PeriodicFundamentalMatrix_joint` | Actual periodic physical L2 fundamental matrix, joint continuity in time and parameters for nonnegative time; joint complex analyticity in spectral parameter and potential at each fixed time. |
| G.1 | `sourceLemmaG1`, `l2HermitianRemainderOperator_eq_matrix` | Actual physical L2 solution and first Born integral, genuine Hermitian operator norm, original exponential weight and coefficient, entire closed unit interval. |
| G.2, arbitrary-time first inequality | `intervalHermitianFirstBornOperator_weighted_le_of_trace_L2_bound`; `lemmaG2_firstBorn_integralNorm_counterexample` | The trace/derivative-data bound is proved. The printed unspecified interval norm remains unresolved; the usual unnormalized integral H1 interpretation is refuted by a smooth periodic source. |
| G.2, unit-interval consequence | `sourceLemmaG2_remainder_unit`, `sourceLemmaG2_classical_remainder_unit` | Printed factors proved in the exact Chapter 5 periodic H1 norm, using constant-one comparison with physical integral energy. |
| G.3, stated remainder conclusions | `sourceLemmaG3_H1`, `sourceLemmaG3_fourier_decay`, `sourceLemmaG3_shiftedFree_decay` | Full matrices on exact complex H1 source balls. The printed interpolation exponent is used for 0<epsilon<1; both q=2 decay statements are separately proved without the undefined epsilon=1 quotient. |
| G.3, intermediate derivative line | `sourceG3_printed_full_derivative_false`, `sourceLemmaG3_weighted_remainder_derivative` | The un-hatted M derivative bound is false at zero potential. The weighted derivative of M-E has the required uniform bound on the original H1 balls. |
| G.4 | `sourceCorollaryG4`, `sourceG4_remainder_operator_memlp`, `sourceG4_shiftedFree_operator_memlp` | Actual full operator-valued Fourier sequences, finite outer p>1 and q>1+1/p, including q=infinity. Uniformity is over exact source balls after fixing the spectral sequence; arbitrary finite initial values are included. |
| G.5 | `sourceLemmaG5_corrected`, `sourceLemmaG5_shifted_corrected` | Full gradient-valued estimates for finite p>=2 in the conjugate range. The two off-diagonal reference superscripts must be exchanged. The printed outer infinity endpoint is independently refuted. |
| G.6 | `sourceCorollaryG6_discriminant`, `sourceCorollaryG6_antiDiscriminant_corrected` | Exact signed source pair norm and uniform H1-ball majorants in the printed finite range. The anti-discriminant wave index is corrected from -2*n*pi to -2*n. |
| G.7 | `sourceLemmaG7_all_finite_corrected`, `exists_global_sourceG7_below_two_physical_complex`, `exists_global_sourceG7_canonical_midpoint_memlp` | Both actual derivative estimates on original complex H1 sources, a common complex neighborhood for each finite p>1, physical midpoint and Dirichlet realizations, and nonzero Dirichlet normalization. The second half-wave index is corrected to -2*n. |

## Physical formulas and source interfaces

The actual L2 variation kernel and endpoint gradients are constructed in
`L2VariationKernel.lean` and `L2EndpointGradient.lean`. Their agreement with
continuous-potential gradients is proved in `L2GradientComparison.lean`;
Fourier realization is recorded in `L2GradientFourierRealization.lean` and
`L2SourceDirichletFourier.lean`. These identities link the earlier classical
H1 estimates to actual physical L2 derivatives.

For G.7, midpoint gradients are independent of the isolating contour,
including at collapsed gaps. The canonical continuous representative is
unique from its full Hilbert cotangent and from its Fourier coefficients.
Below two, the derivative is restricted along the original coefficient
inclusion. `sobolevSourceExponentInclusion` supplies the H1 source at every
finite exponent and preserves every original Fourier coefficient; it does
not replace the source norm by a maximum norm.

The G.7 neighborhood may depend on the exponent. Its conclusions are
pointwise summability for H1 sources in that neighborhood, not a newly
asserted uniform majorant on all H1 balls. G.6's physical anti-discriminant
error also has an all-complex H1 realization below two at either canonical
boundary sequence, by `sourceG6_below_two_physical_complex`.

## G.3's missing hat

After the bounds for the derivative of M-E, the proof prints a uniform
weighted bound for the derivative of M itself. At the zero potential and
time zero its derivative is diag(-i*z,i*z), with Hermitian operator norm
exactly abs(z). Real z of arbitrarily large magnitude contradict the
printed line, even with abs(z)>=1 and a singleton bounded source set.

`norm_deriv_classicalHermitianFundamental_zeroPotential_at_zero` proves the
exact norm. `sourceLemmaG3_weighted_remainder_derivative` proves the bound
for the remainder, with constant

    4 * (8 + pi) * (2*M) * exp(4*(2*M))

on the original source-norm ball of radius M. It holds for every nonzero
complex z and every time in [0,1]. This repairs the intermediate proof
estimate; the stated G.3 remainder conclusions retain their existing proofs.

## Unresolved and refuted statements

G.2's arbitrary-time interval norm still needs an explicit source convention
or an adopted correction. The proved integral-norm correction candidate is
recorded in `SOURCE_ERRATA.md`; it is not silently substituted for the
printed formula. The refutations of the printed G.5/G.6/G.7 references and
G.5's infinity endpoint also remain explicit there. No build count or label
inventory resolves these mathematical distinctions.
