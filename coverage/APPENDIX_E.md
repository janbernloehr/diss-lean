# Appendix E: current source audit

This compares the statements and proof assertions on printed pages
130–131 with the canonical Lean API. It supersedes the historical
Appendix E entries in `COVERAGE.md`, without certifying the entire
dissertation. The source statements and the three main implementation
files have been inspected directly.

| Source requirement | Authoritative entry points | Verified scope |
| --- | --- | --- |
| E.1: entire numerator and circle decay | `sourceLemmaE1`, `appendixESineCircleSup` | The actual supremum of the sine quotient on the circles of radius N*pi+pi/2 tends to zero. No decay rate or summability of interpolation coefficients is assumed. |
| E.1: simple displaced lattice | `sourceLemmaE1_literal` | Every injective lattice pi*n+a_n with a in ell^p, for every finite Banach exponent p>=1, including complex displacements. Evaluation points avoid the roots. |
| E.1: cardinal products and normalization | `tendsto_appendixEInterpolationKernel`, `appendixEInterpolationKernel_eq_deriv` | Literal symmetric products omit the diagonal index. The ratio equals g(z)/(g'(sigma_n)*(z-sigma_n)), retaining the full-product derivative normalization. |
| E.1: interpolation convergence | `eventually_appendixE_interpolation_error`, `sourceLemmaE1_literal` | Exact finite residue identities and a vanishing outer-contour error prove symmetric-sum convergence to the numerator. |
| E.1: uniform quotient version | `tendstoUniformlyOn_appendixEQuotientInterpolation` | Residue sums converge uniformly on bounded zero-free evaluation sets, as a direct consequence of the contour estimate. |
| E.2: complexification | `RealComplexification`, `sourceLemmaE2` | Arbitrary continuous real-linear complexifications, with no isometry, convexity or projection-norm assumption. Complete complex target spaces are allowed. |
| E.2: connected domain and real slice | `sourceLemmaE2_of_real_point`, `sourceLemmaE2_eq` | A connected open domain meeting the real slice has uniqueness from that slice; two-map agreement and a specified real base point are included. |
| E.2: actual source spaces | `sourceLemmaE2_realType` | The original conjugate-reflected coefficient spaces at every finite Banach exponent, including p=1. |
| E.3: actual coefficients and displacement | `exponentialFourierCoefficients_apply`, `norm_intervalFourierCoefficient_exponential_difference` | Unit-interval Fourier integrals of exp(i*nu*x), complex displacements up to pi/4, all signed indices and the printed reciprocal coefficient-decay bound. |
| E.3: uniform bounds | `sourceLemmaE3_tail`, `sourceLemmaE3`, `sourceLemmaE3_bigO` | Every q>1, including infinity. One tail constant precedes the frequency sequence and cutoff; arbitrary finite exceptional frequencies are absorbed into the global bound. |

The main files are
[`SourceLemmaE1.lean`](../NLS/ZakharovShabat/SourceLemmaE1.lean),
[`SourceLemmaE2.lean`](../NLS/ComplexAnalysis/SourceLemmaE2.lean), and
[`SourceLemmaE3.lean`](../NLS/Fourier/SourceLemmaE3.lean).
The actual source real form is handled in
[`SourceRealTypeIdentity.lean`](../NLS/ZakharovShabat/SourceRealTypeIdentity.lean).

## Corrections and conventions

E.1's displayed product includes the diagonal index, which makes its
factor undefined in the usual complex interpretation. The source's own
residue calculation omits that index. The implementation proves the
omitted-index formula, and `appendixE_all_index_cutoff_eq_zero` exhibits
the obstruction under Lean's totalized division. The outer sum is
explicitly symmetric; unconditional `HasSum` and absolute convergence
are not asserted by this interpolation result.

E.2's proof starts at a real point of its domain. Accordingly, the
nonempty-real-slice condition is explicit. If "neighborhood" is read as
an arbitrary nonempty complex open set, the printed statement fails:
`sourceLemmaE2_realSlice_condition_needed` uses constant one on the
half-unit ball about i. Both dissertation applications start at real
type potentials. These distinctions are recorded in
[`SOURCE_ERRATA.md`](../SOURCE_ERRATA.md).

No correction is recorded for E.3. The unit-interval exponential need
not match periodically at its endpoints; its Fourier coefficients are
the actual integral coefficients. The infinity endpoint and the
unrestricted finite head are part of the formal statement.

## Verification evidence

The existing public checks exercise p=1 and p=3 interpolation, a nonreal
root displacement, cardinal values, the diagonal-product obstruction,
and an end-to-end sinc reconstruction. Identity-theorem examples include
a connected nonconvex domain, a translated real base point, a paired
complex target, the empty-real-slice counterexample and actual source
spaces at p=1 and p=3. Exponential checks cover q=3/2 and infinity, negative
indices, displacement on the pi/4 boundary and an exceptional imaginary
frequency. The repository build and transitive axiom audit check the
canonical declarations; current validation totals belong in `STATUS.md`.
