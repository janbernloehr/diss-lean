# Actual critical branches and finite period normalization

This milestone moves beyond the free-potential calculation: it constructs
actual entire spectral numerators and solves any finite collection of the
actual Hill period equations on a complex neighborhood of zero.
**The infinite normalized family and the article main theorems remain open.**

The potential space in these constructions is `C([0,1],ℂ)` with its sup
Banach norm. Neighborhoods may depend on the mode or selected finite set.
No common infinite-mode neighborhood or rough-space extension is inferred.
The source correspondence is the critical points and psi normalization of
Section 2.5, especially equations (52)–(53), p. 21, used in Lemma 3.1 and
the main frequency representations.

## Reusable analytic constructions

`NLS/ComplexAnalysis/JointSpectralDerivative.lean` now adds
`analyticOnNhd_spectral_deriv_of_analyticOnNhd`. Spectral differentiation
of a jointly analytic scalar family on an open domain retains full joint
Banach analyticity. The proof evaluates the analytic Fréchet derivative
at `(1,0)`. Existing derivative and continuity statements are unchanged.

`NLS/ComplexAnalysis/ParametricDividedDifference.lean` constructs the filled
quotient by a fixed real interval integral of the spectral derivative.
For an entire-in-energy family F and an analytic moving center μ, it proves
joint analyticity of G on energy times the parameter neighborhood, with

```text
(z-μ(q))*G(z,q) = F(z,q)-F(μ(q),q),
G(μ(q),q) = partial_z F(μ(q),q),
G(z,q) = dslope(F(.,q),μ(q),z).
```

The filled value on the moving diagonal is proved, not taken from total
division. The proof reuses the dissertation's joint interval integration
and normalized convex primitive theorem.

`NLS/ComplexAnalysis/AnalyticFinitePeriodNormalization.lean` proves
`exists_analytic_finite_period_normalization`. Any finite matrix of analytic
period entries equal to the identity at a base parameter admits a jointly
constructed analytic coefficient matrix C nearby, with C(base)=Id and
`C(q)*P(q)=Id`. The analytic implicit function theorem solves every
coefficient equation simultaneously. An inverse matrix, coefficient
selection, or separate invertibility estimate is not assumed.

## Actual spectral critical points and numerator basis

`NLS/KdV/ClassicalCriticalPointBranch.lean` defines the energy derivative
of the actual constructed discriminant and proves joint analyticity of
its first and second energy derivatives. For each positive free mode n,
`exists_classicalHill_critical_point_branch` constructs μ_n and an open
complex potential neighborhood V_n of zero, with

```text
μ_n(0)=(n*pi)^2,
Delta'_q(μ_n(q))=0,
Delta''_q(μ_n(q))!=0,
μ_n analytic on V_n.
```

It uses the previously proved exact free second derivative, so neither
a critical-point selection nor simplicity is an input. It does not yet
identify these local branches with global source gap labels.

`NLS/KdV/ClassicalCriticalNumerator.lean` selects those proved charts and
constructs the actual entire numerator basis B_n:

```text
B_n(z,q) = 2*n*pi * filled(Delta'_q(z)/(z-μ_n(q))),
(z-μ_n(q))*B_n(z,q) = 2*n*pi*Delta'_q(z),
B_n(μ_n(q),q) = 2*n*pi*Delta''_q(μ_n(q)) != 0,
B_n(z,0)=classicalHillFreePsi_n(z).
```

The declarations prove joint analyticity throughout `ℂ × V_n` and genuine
entire energy slices, including the omitted critical point. These are
basis numerators for the period equation; they are not asserted to be
the infinite normalized psi family.

## Actual period entries and finite normalization

`NLS/KdV/ClassicalCriticalPeriods.lean` uses the proved free isolating
circles and the actual root continued from the free potential. It proves
that those whole circles lie in the continuation domain at zero and in
that domain on a constructed common potential neighborhood. The entries

```text
P_nk(q) = (1/(2*pi))*integral_(C(lambda_k,R_k)) B_n(z,q)/r(z,q)
```

are analytic near zero and satisfy `P_nk(0)=delta_nk`. The neighborhood
simultaneously validates the critical branch and the full contour; contour
avoidance is a proved conclusion rather than a supplied spectral input.

`NLS/KdV/ClassicalFiniteNormalizedDifferentials.lean` proves
`exists_classicalHill_finite_normalized_differentials`: for any finite
index type and injective assignment to positive Hill modes, there exist
one open complex neighborhood V of zero and entire numerators Ψ_n such
that every Ψ_n is jointly analytic on `ℂ × V`, equals the previously
constructed free numerator on the entire zero-potential slice, and

```text
(1/(2*pi))*integral_(C(lambda_k,R_k)) Ψ_n(z,q)/r(z,q) = delta_nk
```

for every q in V and every pair of selected modes. The actual construction
is the finite linear combination `Ψ_n=sum_j C_nj*B_j`, with coefficients
solved by the analytic implicit function theorem. The proof derives
circle integrability and finite contour linearity from the constructed
analytic factors. The result also retains full contour-domain coverage
on V, for subsequent weighted moment constructions.

This assertion is uniform over all selected modes on one V, with V chosen
after the finite selection. It does not exchange these quantifiers to
claim a common neighborhood for all positive integers. It does not
assert zero periods on unselected contours. In particular, it does not
identify Ψ with the globally normalized source function in equation (52).

## Reuse, validation and remaining obligations

The actual discriminant, scalar flow, free normalization and source-root
continuation are reused from the already merged shared branch through
`ecd010969f63e6b8af8f6ed5aaa1dc571fa7e503`. The flow, scalar spectrum and
source continuation modules are now also compiled directly by this
article checker. No second Hill foundation is added.

The focused checker now selects 33 modules, using pinned Lean 4.33.1 and
mathlib v4.33.1 with `autoImplicit=false`, `warningAsError=true`, and default
heartbeats. Current final audit counts are in `VALIDATION.md` and
`source.json`. Its outputs remain private to this worktree; canonical
sources and build products are read-only.

The remaining normalization step is genuinely infinite: uniform tail
estimates for the period operator, an infinite inverse/limit construction,
compatibility of the local critical branches with global gap labels, and
the canonical product/zero representation. Further main-theorem obligations
remain: rough Fourier-Lebesgue compatibility, sharp locally uniform moment
bounds, physical Hamiltonian/frequency identities, action descent and the
stated weighted asymptotics/compact derivatives, and the physical
Birkhoff/PDE identification. None is silently discharged by a finite
matrix theorem. All actual main-theorem statuses remain open.

Final validation passes for all 33 selected modules. The transitive audit
passes for 497 selected declarations and 2148 declarations including
imported NLS dependencies, allowing only `propext`, `Classical.choice` and
`Quot.sound`. Reproduce with `bash scripts/check-kdv-kdv2-frequencies.sh`.
