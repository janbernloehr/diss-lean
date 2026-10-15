# Section 22: original phases and physical solutions

This audit concerns printed pp. 98–101. The current step connects the
coordinate trajectories and global solutions for 1 < p ≤ 2 to the
original Sections 17–20 family. It also proves the phase-sign correction
in equation (4.14) and Remark 22.3. The original higher-exponent source
inversion, nonextension assertions, and full Remark 22.3 remain subsequent
steps; this is not a completion claim for the whole section.

## One original family and domain

[`sourceSection22_original_flows`](../NLS/ZakharovShabat/SourceSection22Original.lean)
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
| Remark 22.3 and the ordinary analogue | `renormalized_solution_iff_coordinates`, `ordinary_solution_iff_coordinates` | Corrected phase characterization for p ≤ 2 on any time set containing zero, with continuity of the whole source curve. |
| Theorem 22.1(iii), Corollary 22.2(ii)–(iii), Remark 22.3 above two | Subsequent original-family integration | Earlier general flow and nonextension results exist, but their complete original-family and physical-orientation audit is not claimed here. |

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

## Validation and remaining work

Five modules and 26 public examples check actual frequency coordinates,
one U for every time horizon, both phase signs at a negative index,
complex action preservation at zero index, zero-length time intervals,
reality and pair norms, joint continuity, and the entire coordinate image.
They also check actual finite-gap sign witnesses, both physical solution
definitions, both directions of the solution characterization, the exact
ordinary mass term, cancellation by negative time, full trajectory
analyticity, and analytic coordinate inverse maps. Unconditional
constructors are checked at p = 3/2 and p = 4, including a witness above
the surjective range. Full results are in [implementation status](../STATUS.md).

For p > 2, globally defined coordinate phases are not asserted to remain
in the Birkhoff image for all time. The remaining original audit must
retain that guard for source inversion, prove the higher-exponent version
of the corrected solution characterization, and connect both nonextension
statements to the same original data and physical solution map. Section
14's external Hilbert-map and full fractional-smoothness qualifications
remain. The dissertation is incomplete.
