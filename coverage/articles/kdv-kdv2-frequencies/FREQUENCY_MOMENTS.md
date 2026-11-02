# Frequency-moment contour dependencies

The contour calculations needed for the frequency representations in
Theorems 1.2 and 1.9 are now proved. **The actual spectral constructions,
Hamiltonian-frequency identification and infinite-series estimates remain
open. No main theorem is marked verified by this step.**

The pinned source is arXiv:1605.06690v1, identified in `source.json`.
The relevant source statements are Lemma 3.1 (PDF pp. 25-26), Lemma 3.2
(pp. 26-27), and Lemma 4.1 (pp. 40-41). Source Theorems 3.4 (p. 31) and
4.3 (pp. 42-43) additionally require infinite-series convergence and
identification with physical frequencies, neither of which is inferred
from finite contour algebra.

## Defined quantities and proved analytic properties

`NLS/KdV/FrequencyMoments.lean` defines the literal weighted contour moment

```text
frequencyMoment F G c r m = integral_(C(c,r)) F(z)^m G(z) dz.
```

For the actual source data, `F` will be the local primitive `F_k` and `G`
the quotient `psi_n/sqrt(Delta^2-4)`. Circles are counterclockwise. The
following are proved in namespace `NLS.KdV`:

| Declaration | Proved content and source correspondence |
| --- | --- |
| `analyticOnNhd_frequencyMoment` | Joint complex analyticity of the actual integrand factors, on a domain containing a fixed circle for every parameter in an open Banach-space neighborhood, gives Banach analyticity of each moment. This uses the existing differentiation-under-the-integral theorem, not a coordinatewise substitute. It is the analytic step of Lemma 3.1(ii); construction of the source factors and neighborhoods is still required. |
| `frequencyMoment_odd_eq_zero` | Analytic continuation of `F^2` and `F*G` through the closed disc makes every moment of degree `2l+1` vanish, for every `l>=0`. Each vanishing integral is proved by Cauchy's theorem. This is the contour criterion for Lemma 3.1(iii). |
| `frequencyMoment_pos_eq_zero` | If `F` itself and `F*G` are analytic through the disc, every positive moment vanishes. `G` need not be analytic there, allowing the diagonal closed-gap pole. This is the analytic-removal criterion used in Lemma 3.1(iv); the implication from an actual collapsed spectral gap to these analytic properties remains to be constructed. |
| `norm_frequencyMoment_le` | Circle bounds `abs(F)<=A` and `abs(G)<=B` give `abs(Omega_m)<=2*pi*r*A^m*B`, with `r>=0` and `A>=0`. These explicit contour estimates do not themselves assert the source's sharper spectral asymptotics. |
| `shifted_frequency_period` | General binomial expansion under the contour integral, with integrability derived from continuity on the circle. |
| `cubic_shift_frequency_period` and `fifth_shift_frequency_period` | After the proved odd-moment cancellations, only moments of degrees 0,2 and, in the fifth-power case, 4 remain. |

## Exact frequency coefficients and contour deformation

`NLS/KdV/FrequencyContourDecomposition.lean` proves the two single-gap
calculations after the shift `F = F_k - i*k*pi`:

```text
(4/(i*pi)) integral F^3 G
  = -12*k*Omega_2 + 4*k^3*pi^2*Omega_0,

(-16/(i*pi)) integral F^5 G
  = 80*k*Omega_4 - 160*pi^2*k^3*Omega_2
      + 16*pi^4*k^5*Omega_0.
```

The declarations are `cubic_frequency_gap_contribution` and
`fifth_frequency_gap_contribution`. The zeroth-period normalization
`Omega_0=2*pi*delta_kn` is an explicit input to the subsequent finite-gap
theorems; it has not been assumed to hold for an unconstructed psi family.

The declarations `kdv_frequency_contour_decomposition` and
`kdv2_frequency_contour_decomposition` apply the existing finite-hole Cauchy
theorem to an actual analytic outer integrand `Q`. Their geometric inputs
are positive inner radii, larger disjoint isolating discs strictly inside
the outer circle, and analyticity on the resulting perforated closed disc.
The local circle integrands must match `Q` there. A contour-deformation
identity is a proved conclusion, not a supplied assumption.

For a finite set `A` of strictly positive modes containing the selected
mode `n`, the normalized zeroth periods give exactly:

```text
(4/(i*pi)) integral_outer Q - (2*n*pi)^3
  = -12 sum_(k in A) k*Omega_2(n,k),

(-16/(i*pi)) integral_outer Q - (2*n*pi)^5
  = -160*pi^2 sum_(k in A) k^3*Omega_2(n,k)
      + 80 sum_(k in A) k*Omega_4(n,k).
```

Including `n` in `A` does not assert that its gap is open: an additional
isolating circle may surround a collapsed gap. Actual spectral continuation
and normalization are still needed for that application. The fifth outer
period is intended for the bracket of `H2-10H0^2`; relating it to `omega_2`
must also recover the source's `20(2n*pi)H0` mass term. No physical mass
subtraction or Poisson identity is silently omitted from the completion
requirements.

## Validation, reuse and remaining main-theorem requirements

All twelve selected modules pass pinned Lean 4.33.1/mathlib v4.33.1 with
`-DautoImplicit=false -DwarningAsError=true`. The transitive audit passes
for 218 selected-module declarations and 1593 declarations including
imported NLS dependencies, allowing only `propext`, `Classical.choice` and
`Quot.sound`.

The new reusable frequency theory lives under `NLS/KdV`; article coverage
stays in this directory. It directly reuses the dissertation library's
Banach-analytic circle integration and finite-hole Cauchy theorem, also
used by the shared KdV action-Hamiltonian contour developments. It adds
no competing Hill operator or action Hamiltonian.

To conclude the main frequency theorems still requires construction of
the actual discriminant, canonical root, primitives and normalized psi
functions; their period and analytic-continuation properties; the physical
Poisson/outer-period identities; sharp spectral moment estimates; locally
uniform convergence of the infinite weighted moment sums; action descent;
and the stated asymptotics and compact derivatives. These remain explicit
open obligations in the main source map.


The subsequent [frequency-series milestone](FREQUENCY_SERIES.md) proves
absolute convergence, analyticity and locally uniform positive partial
sums from explicit local remainder bounds. The actual spectral moment
estimates and physical frequency identification remain open. The counts
above are historical for the contour milestone; `VALIDATION.md` records
the current complete focused run.


The later [primitive-continuation milestone](PRIMITIVE_CONTINUATION.md)
imports the actual continuous-potential Hill discriminant and constructs
analytic squared-primitive and primitive/root quotients at both branch
signs, including multiple zeros. The local odd-moment cancellation is now
proved from those charts. Global normalization and the rough-potential
spectral statements remain open.
