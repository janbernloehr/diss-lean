# Section 22: original phases and physical solutions

This audit concerns printed pp. 98–101. The named Section 22 assertions
are integrated with the original Sections 17–20 family, with the formal
phase-sign correction in equation (4.14) and Remark 22.3. The source
inverse keeps its actual image condition above exponent two. This is
not a completion claim for the dissertation or for the separate
Section 14 qualifications.

## One original family and domain

[`sourceSection22_original`](../NLS/ZakharovShabat/SourceSection22Original.lean)
constructs the original Birkhoff family D and Section 20 moment package Q
before choosing any source, coordinate index, or compact time horizon.
Every finite exponent p > 1 is allowed. The moment frequency, original
map, and original source neighborhood U are retained.

[`SourceSection22Phases.lean`](../NLS/ZakharovShabat/SourceSection22Phases.lean)
proves complex analyticity of the full trajectory in C([−T,T], ℓᵖ × ℓᵖ)
on all of U, for every finite time horizon T. U is not shrunk with T.
The bounded frequency correction has exactly the original scalar moment
frequencies as its coordinates. Time reflection supplies the physical
Hamiltonian orientation while preserving this domain and analyticity.

On the real source space the phase curve is jointly continuous in time
and source in the full sequence norm. Its two components remain conjugate
and preserve the pair norm. The actual spectral action is preserved even
at nonreal sources in U, including at a collapsed gap.

[`SourceSection22Coordinates.lean`](../NLS/ZakharovShabat/SourceSection22Coordinates.lean)
also proves joint real analyticity of both scalar coordinates in real
time and initial coordinates for every signed index. This scalar
statement does not assert sequence-valued differentiability in time
at arbitrary low-regularity sources.

The coordinate-parameterized trajectory uses the original inverse on the
open image of the real Birkhoff map. Analyticity holds on that entire
image. `hamiltonian_coordinate_apply` carries its image-membership guard
and identifies the initial coordinate pair exactly. No assertion uses
the total inverse's fallback outside the image.

## Corrected phase orientation

For the source's z = (x − iy)/√2 and w = (x + iy)/√2, the original action
Hamiltonian rotation (−y,x) has velocities (−iz,+iw). Thus the physical
phases are exp(−itωʳₙ)zₙ and exp(+itωʳₙ)wₙ. Equation (4.14) on p. 98
and Remark 22.3 on p. 101 print the opposite signs.

[`SourceSection22SignCorrection.lean`](../NLS/ZakharovShabat/SourceSection22SignCorrection.lean)
constructs a witness at every nonzero signed index and every finite
p > 1. A small single-coordinate real pair remains inside the original
open image. Its original inverse is finite-gap and has both complex
amplitudes nonzero. Continuity from the zero-source frequency (2πn)²
makes its renormalized frequency positive. This uses the local image
inverse, so it also works above two without global surjectivity.

`equation4_14_printed_sign_counterexample` proves that both printed
coordinate trajectories fail to have their Hamiltonian velocities.
For p ≤ 2, `printed_flows_not_physical_solutions` proves the stronger
statement: at the same actual finite-gap source, neither printed-sign
source flow is a solution in the original all-smooth-approximation sense.
The ordinary frequency remains positive after adding four times the
nonnegative physical mass. See [source discrepancies](../SOURCE_ERRATA.md).

## Assertion map

| Source assertion | Public API | Current scope |
| --- | --- | --- |
| Opening frequency and complex-coordinate formulas | `bounded_phase_correction`, `hamiltonian_phase_coordinates` | Original moment frequency plus (2πn)²; literal complex phase formulas on U with corrected signs. The ordinary phase includes exactly 4 times physical mass. |
| Theorem 22.1(i): continuity and trajectory analyticity | `hamiltonian_phase_joint_continuous`, `hamiltonian_phase_analytic`, `hamiltonian_coordinate_analytic` | Every finite p > 1, full sequence and uniform compact-time norms, actual open coordinate image. |
| Theorem 22.1(i): group and diffeomorphisms | `global_physical_group`, `renormalized_coordinate_time_map` | Every 1 < p ≤ 2, all real times, entire real coordinate space, analytic inverse given by negative time. |
| Theorem 22.1(ii): ordinary trajectories and diffeomorphisms | `ordinary_coordinate_trajectory_analytic`, `ordinary_coordinate_trajectory_apply`, `ordinary_coordinate_time_map`, `global_physical_joint_continuous` | Same range and original family, full compact-time analyticity and physical mass correction. |
| Equations (4.15)–(4.16), physical meaning | `global_physical_solutions` and the retained `complex_map_hamiltonianRenormalizedSourceFlow` / `complex_map_hamiltonianOrdinarySourceFlow` | Original inverse lifts for p ≤ 2, with actual coordinate laws and original approximation-solution meaning. |
| Corollary 22.2(i) | `global_analytic_wellposedness`, `global_physical_trajectories` | Both ordinary and renormalized NLS, original physical flows as witnesses, analytic dependence in the full uniform source norm. |
| Opening scalar analyticity | `phase_coordinate_joint_analytic` | Every finite p > 1 and signed index, joint real time and initial coordinate dependence on the actual open image. |
| Equation (4.15) above two | `trajectory_domain_iff_solution` | The original physical inverse formula is an approximation solution on [−T,T] exactly when its full coordinate curve stays in the original image. |
| Corollary 22.2(ii) | `local_physical_solutions`, `local_analytic_wellposedness`, `small_global_physical_solutions` | Local solutions around every source; one invariant open neighborhood of zero containing a positive norm ball has global solutions, full trajectory analyticity, joint continuity, and group laws. |
| Theorem 22.1(iii) | `coordinate_nonextension_fst`, `coordinate_nonextension_snd` | Both physical coordinate signs, any signed index, actual image points outside ℓ² with the corresponding amplitude nonzero; finite-gap agreement suffices. |
| Corollary 22.2(iii) | `finiteGap_source_nonextension`, `smooth_source_nonextension_all` | At every non-Hilbert source: finite-gap agreement gives all finite targets q≥p>2; all-smooth agreement gives every q≥1, including infinity. Forward and symmetric intervals are covered. |
| Remark 22.3 | `remark22_3`, `renormalized_solution_coordinates`, `coordinate_curve_unique` | Full corrected characterization at every finite p > 1, with the original approximation definition and uniqueness in the continuous-curve class. T = 0 is included. |
| Arbitrary time sets and the ordinary analogue | `renormalized_solution_iff_coordinates`, `ordinary_solution_iff_coordinates` | Both corrected phase characterizations for p ≤ 2 on any time set containing zero. |

The physical solution characterizations are in
[`SourceSection22Solutions.lean`](../NLS/ZakharovShabat/SourceSection22Solutions.lean).
They preserve the solution definition through arbitrary smooth initial-data
approximations. Forward implication uses the proved uniqueness of those
solutions; the converse recovers the constructed physical source flow
through injectivity of the original map and then verifies the approximation
condition. Solutions are not redefined by the coordinate equation.

[`SourceSection22Global.lean`](../NLS/ZakharovShabat/SourceSection22Global.lean)
retains both original physical source flows. Conjugation through the same
original Birkhoff homeomorphism supplies the coordinate time maps and
their analytic negative-time inverses. The source trajectory maps are
analytic as maps into continuous source-valued paths, not only at each
coordinate or fixed time.

## Higher-exponent inversion and full solution characterization

[`SourceSection22Characterization.lean`](../NLS/ZakharovShabat/SourceSection22Characterization.lean)
first identifies the original coordinates of every actual smooth
renormalized solution, at every finite exponent above one. Smooth-data
density and joint continuity of the physical phase then pass the law to
an arbitrary approximation solution. This implication is proved on any
time set in the original solution definition.

For the converse on [−T,T], a continuous curve satisfying the coordinate
law supplies its own image membership: the phase at each time equals the
original map of an actual source. The guarded inverse flow consequently
exists on the interval and satisfies the all-smooth-approximation
condition. Injectivity identifies it with the given curve. The exact
`trajectory_domain_iff_solution` rules out treating the total inverse's
fallback outside its image as a solution. The initial value is forced
by the coordinate law at zero. `coordinate_curve_unique` states the
continuous-curve uniqueness conclusion explicitly.

[`SourceSection22Higher.lean`](../NLS/ZakharovShabat/SourceSection22Higher.lean)
constructs one positive time and open source neighborhood around every
initial source. On that neighborhood the physical inverse trajectories
are analytic in the full uniform source norm. The small-data result
constructs one open invariant neighborhood of zero, containing a
positive source-norm ball, on which every time is admissible. The same
neighborhood supports all compact-time analytic trajectory maps,
joint continuity, both signs of time, and the physical group law.

## Original physical nonextension

[`SourceSection22Nonextension.lean`](../NLS/ZakharovShabat/SourceSection22Nonextension.lean)
proves both scalar obstructions on the original open coordinate image.
A proposed extension need agree only with the actual finite-gap
frequencies and amplitudes. Time reflection transfers the proved
oscillation obstruction to the physical signs. The first and second
components have separate nonvanishing guards, and the index may be zero
or negative.

The source theorem uses the retained original source family and
constructs original Hilbert and target families. Actual classical
finite-gap Fourier coefficients identify the physical Hilbert flow;
the frequency-divergence obstruction then rules out continuity in the
complete forward-time trajectory norm. Agreement with all smooth
classical solutions implies this finite-gap agreement. A symmetric-time
version follows by restriction to [0,T]. No hypothetical classical
trajectory or spectral-flow agreement is required as an extra premise.

## Validation and limits

The first phase/global-flow step added five modules and 26 public
examples. This completion step adds four modules, strengthens the
original constructor, and adds 23 public examples. They cover actual
smooth solutions, arbitrary approximation solutions, the converse from
both scalar laws, forced initial values, full continuous-curve
uniqueness, necessity and sufficiency of the image guard, and T = 0.
Further checks cover joint scalar analyticity, common local existence,
full uniform trajectory analyticity, an invariant positive source ball,
negative-time cancellation, both coordinate obstructions at zero or
negative indices, forward-time nonextension at every larger finite
exponent, finite-gap classical agreement, and the symmetric-time case.
Unconditional constructors are checked at p = 4 and p = 3/2. Full build
and axiom-audit results are in [implementation status](../STATUS.md).

For p > 2, global source solvability is asserted only where the phase
curve stays in the original image; global surjectivity is not asserted.
[Section 14](SECTION_14.md) now proves native fractional Sobolev
analyticity and analytic inverses; its precise 2014 construction
comparison remains unverified. The same original family carries the
named Sobolev and weighted estimates in [Section 23](SECTION_23.md).

## The infinity target in the physical nonextension theorem

Corollary 22.2(iii) on p. 100 states the obstruction for any q >= p;
the proof on p. 101 explicitly uses p <= q < infinity. The original
finite-target proof above remains valid. The follow-up now proves the
same all-smooth physical nonextension conclusion for every target
exponent q >= 1, including infinity. The source exponent p remains
finite, and the source lies outside the original Hilbert locus.

[SmoothSourceMassDivergence.lean](../NLS/ZakharovShabat/SmoothSourceMassDivergence.lean)
identifies the mass of an actual smooth datum with the squared Hilbert
norm of its first Fourier component. Finite Fourier energy sums then
show that every smooth approximation to a non-Hilbert source has mass
tending to infinity. Smooth approximations exist in the original norm.

[VariableAmplitudePhaseObstruction.lean](../NLS/Dynamics/VariableAmplitudePhaseObstruction.lean)
proves that a diverging phase frequency prevents uniform convergence
even when its amplitude is a converging continuous trajectory. At
times pi/frequency tending to zero the phase equals minus one, which
contradicts continuity of a putative limit with nonzero initial value.

[SmoothSourceGaugeObstruction.lean](../NLS/ZakharovShabat/SmoothSourceGaugeObstruction.lean)
applies this argument to an actual nonzero physical Fourier coefficient.
The exact mass gauge has frequency four times the physical mass. Local
analytic renormalized solution maps give uniformly converging amplitude
trajectories on one common short interval. The approximation definition
itself identifies these maps with the smooth solutions there. Fourier
evaluation is continuous at every target exponent, including infinity.
No Birkhoff map at the target exponent is needed.

[SourceSection22NonextensionAll.lean](../NLS/ZakharovShabat/SourceSection22NonextensionAll.lean)
uses the retained original family's local analytic wellposedness to
prove both the forward-time and symmetric-time obstruction. This
requires agreement with every constructed smooth classical solution;
the separate finite-gap-only theorem above keeps its finite-target
scope. The proof uses local source solutions and does not assert global
surjectivity at p > 2.

Four public examples check an unconditionally constructed original
p=4 family with infinity target, the symmetric obstruction at p=3,
the exact negative-index gauge between p=3/2 and infinity, and actual
smooth approximations with diverging mass. The precise 2014 comparison
and Appendix G.2 norm qualification remain unresolved.
