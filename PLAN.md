# Implementation plan

## Latest progress: higher-action convergence at every integer Sobolev order

Higher-action convergence is now proved on the original Hˢ source for every
nonnegative integer `s`. On a common open complex neighborhood containing all
real Hˢ sources, levels 1 through `2s+1` have absolutely convergent, complex
analytic sums. Locally, their actual ℓ¹ sequences share a single norm bound
and are analytic as ℓ¹-valued maps.

`SourceHigherSobolevEmbedding.lean` uses the standard Fourier weight
`(1+|n|)^s`. Normalized coordinates with weight `(1+2|n|)^s` have an equivalent
topology, with comparison factor `2^s`. Decoding preserves every original
Fourier coefficient and the real form. The weighted spectral realization
therefore gives exactly the original source operator.

`SourceWeightedGapBound.lean` generalizes the weighted squared-gap estimate
to compatible continuous linear source maps. The infinite tail is controlled
by the canonical weighted estimate, and the finite central block by the
local gap-sequence bound. `SourceWeightedHigherActionBound.lean` uses it to
bound any finite range of levels dominated by the squared weight. Existing
H¹ bounds now reuse these proofs without changing their public statements.

`SourceHigherSobolevHigherActionBound.lean` proves the polynomial domination
through order `2s`, giving levels 1 through `2s+1` on Hˢ.
`SourceHigherSobolevHigherActionAnalytic.lean` proves analyticity of the actual
ℓ¹ sequences and their literal infinite sums, and combines local neighborhoods
into an open domain containing the entire real Hˢ locus.

Public examples check unchanged Fourier coefficients, compatibility with the
old H¹ inclusion, the H⁰ endpoint, the level-five sum on H², and simultaneous
bounds and analytic sums at arbitrary integer Sobolev order.

Validation: the full build passes (6241 jobs), all public examples pass,
and the transitive axiom audit passes for 24200 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: independently construct the higher physical Sobolev Hamiltonians
and extend their finite-gap trace identities by density and analytic uniqueness.
The first three physical H¹ traces are already proved. This step establishes
convergence and analyticity, not the remaining physical trace identifications.
The explicit norm-dependent localization and uniform estimates of Sections
25–28 and the full dissertation inventory remain open.

## Previous milestone: the first three physical H¹ trace identities

The second-level higher-action sum now equals half the physical momentum
on every real H¹ source. Together with the mass and energy results, one open
complex H¹ neighborhood of the entire real locus satisfies all three traces:
`∑ₙ J_(n,1) = H_1`, `∑ₙ J_(n,2) = H_2/2`, and `∑ₙ J_(n,3) = H_3/4`.
All three defining series are absolutely convergent there.

`PeriodOneSobolevMomentum.lean` defines physical momentum independently of
spectral actions, using bounded bilinear Fourier duality. Parseval identifies
it with the actual unit-period integral `-i ∫ a b'`. It is complex analytic
on the entire H¹ pair space and agrees with the second Riccati-hierarchy
Hamiltonian on every actual real finite-gap source, at all finite `p > 1`.
The Fourier series and opposite-mode formulas fix the sign and `2π` factor.

`SourceSobolevMomentumTrace.lean` applies H¹ finite-gap density to obtain the
momentum trace for arbitrary real H¹ data, and proves that the physical
momentum is real on the conjugate-pair real form. Analytic uniqueness extends
the identity to complex neighborhoods. Intersecting with the established
mass/energy neighborhoods and taking their union gives one common open
domain for all three physical identities and absolutely convergent series.

The finite-gap density transfer lemma in `SourceSobolevHigherActionTrace.lean`
is now public and reused by all three levels.

Public examples verify both signs on physical Fourier modes, the derivative
integral definition, real momentum and its trace without a finite-gap premise,
and all three traces and convergence on a common complex neighborhood.

Validation: the full build passes (6236 jobs), all public examples pass,
and the transitive axiom audit passes for 24170 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: extend higher-action sequence convergence and all hierarchy trace
identities to the higher Sobolev spaces in Theorem 24.1. The explicit
norm-dependent localization and uniform higher Sobolev estimates of
Sections 25–28 and the full dissertation inventory remain open. The common
trace domain is a neighborhood of the real H¹ locus, not the entire complex
H¹ space.

## Previous milestone: higher-action bounds and physical H¹ traces

The level-one and level-three trace identities now hold beyond finite-gap
data: every real H¹ source satisfies `∑ₙ J_(n,1) = H_1` and
`∑ₙ J_(n,3) = H_3/4`, with the actual physical mass and energy on the right.
Both literal, absolutely convergent series satisfy the same identities on
one open complex H¹ neighborhood containing the entire real H¹ locus.

`SourceHigherActionComplexCosine.lean` continues the polynomially weighted
gap-boundary formula to complex sources. Symmetric midpoint and squared-gap
coordinates make its cosine mean analytic through collapsed gaps. One source
ball works for every index and level.

`SourceHigherActionComplexBound.lean` bounds each higher action by its squared
gap times the spectral size of that gap to the appropriate power.
`SourceHigherActionPolynomialBound.lean` derives the spectral size bound from
the actual displacement norms. On a common complex neighborhood of each real
source, positive constants `B,D` give
`|J_(n,k+1)| ≤ B D^k (1+|n|)^k |γ_n|²` for all indices and orders.
A summable weighted squared-gap majorant therefore gives absolute convergence
and a norm-sum bound at any level. These are local bounds; they are not the
explicit norm-dependent cutoff or global tame estimates of Sections 25–28.

`SourceSobolevHigherActionBound.lean` combines that estimate with the existing
H¹ weighted-gap theorem. The first three levels have actual ℓ¹ realizations,
with one common bound on a complex H¹ neighborhood of each real source.

`SourceSobolevHigherActionAnalytic.lean` upgrades coordinate analyticity and
the ℓ¹ bound to Banach analyticity of those action sequences. Bounded linear
summation proves analyticity of the literal infinite series, not merely of
each indexed action.

`SourceSobolevHigherActionTrace.lean` passes the physical finite-gap mass and
energy traces through H¹ finite-gap density to all real H¹ data. Analytic
uniqueness for the H¹ real form then extends both identities to complex
neighborhoods, whose union contains the full real locus.

Public examples check the all-order polynomial estimate at `p = 3`, the real
H¹ energy trace without a finite-gap premise, analyticity of its literal sum,
the mass and energy identities for nearby complex sources, and the analytic
ℓ¹ realization of the intermediate second level.

Validation: the full build passes (6234 jobs), all public examples pass,
and the transitive axiom audit passes for 24150 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: identify the second-level sum with physical momentum and extend
series convergence and all hierarchy trace identities to the higher Sobolev
spaces in Theorem 24.1. The norm-dependent spectral localization and uniform
higher Sobolev estimates of Sections 25–28 and the full dissertation inventory
remain open. The new complex trace domain is a neighborhood of the real H¹
locus, not the entire complex H¹ space.

## Previous milestone: complex analytic higher actions

Section 24's higher actions now extend to actual complex analytic functions
on one open source domain containing the entire real locus, for every finite
`p > 1`. The domain is chosen before the gap index and level. These functions
are defined by the dissertation's spectral contour integrals and agree with
the real gap integrals already constructed.

`SourceHigherActionCircleAnalytic.lean` proves Banach analyticity of fixed
higher-action contours, invariance under changing real-centered isolating
circles at a real source, and vanishing at collapsed complex gaps at every
level. The collapsed-gap proof uses the analytic filled quotient.

`SourceHigherActionLocalChart.lean` constructs one source ball and one family
of isolating circles for all indices and orders simultaneously. It proves
agreement with the real gap formula and complex collapsed-gap vanishing.

`SourceHigherActionAtlas.lean` glues those contour formulas using the
real-form identity theorem on overlaps of real-centered source balls. The
result is analytic throughout the open union. Different atlases agree on
their complex overlap, and level one equals the original complex action on
the common domain. The module exports a chosen atlas, a common complex
domain, and the resulting `sourceComplexHigherAction` functions.

`SourceHigherActionRegularity.lean` proves real analyticity and continuity
of every real higher action in the original source norm, including at
collapsed gaps. Every real-centered isolating circle computes the same real
gap integral. The glued complex functions inherit the previously proved
all-order physical trace formula at real finite-gap sources.

Public examples check a common analytic domain at `p = 3`, compatibility of
independently chosen atlases on complex overlaps, collapsed complex gaps,
level-one calibration, real analyticity, and the physical finite-gap trace.

Validation: the full build passes (6228 jobs), all public examples pass,
and the transitive axiom audit passes for 24109 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: establish the convergence and uniform bounds on the higher-action
series needed to extend Theorem 24.1 to general Sobolev and complex sources.
The next step is the complex weighted gap-boundary formula and bounds combining
it with the existing weighted gap summability. The norm-dependent spectral localization and higher Sobolev estimates of
Sections 25–28 and the full dissertation inventory also remain. Individual
coordinate analyticity alone does not establish analyticity or convergence
of the infinite higher-action sum.

## Previous milestone: all-order physical finite-gap trace formula

The higher-action trace identity now holds at every order for actual real
finite-gap sources at every finite exponent `p > 1`:
`∑ₙ J_(n,k+1) = H_(k+1)/2^k`. Both finite and infinite sum formulations
are proved. The Hamiltonians are the differential hierarchy of the source's
smooth physical Fourier representative, independently defined by the Riccati
recurrence.

`PolynomialInversionCircleCoefficients.lean` extracts every Taylor coefficient
of an inversion germ by a polynomially weighted exterior circle integral.
The proof uses repeated contour integration by parts and keeps the exact
factorial normalization.

`SourceFiniteGapHigherActionExterior.lean` applies the existing identification
of the normalized inversion germ with the physical Hamiltonian coefficients.
It evaluates every weighted exterior primitive contour, with one radius
threshold working at all orders.

`SourceFiniteGapHigherActionTrace.lean` decomposes that exterior contour over
the finitely many open gaps. The primitive extends through the collapsed
gaps, which contribute zero. The resulting trace formula proves reality of
every positive-order Hamiltonian and nonnegativity of every odd-order
Hamiltonian. No supplied contour family, expansion coefficients, or spectral
sum definition of the Hamiltonians is needed.

Public examples check arbitrary levels at `p = 3`, recovery of physical mass,
the level-three sum as one quarter of the actual H¹ energy, and all-order
reality and odd-order nonnegativity.

Validation: the full build passes (6224 jobs), all public examples pass,
and the transitive axiom audit passes for 24036 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: extend Theorem 24.1 from real finite-gap sources to the stated
Sobolev and complex-source setting, and derive the norm-dependent spectral
localization and higher Sobolev estimates of Sections 25–28. The previous
endpoint comparisons still assume localization bounds. Complex higher-action
gluing and regularity and the full dissertation inventory remain open.

## Previous milestone: higher-level action contours and gap comparisons

Section 24's higher-level actions now have their defining spectral contours,
the integration-by-parts representation, and the real gap formula in cosine
coordinates. Their mean-value comparison with the ordinary action includes
collapsed gaps and yields bounds from localization of the periodic endpoints.

The Chapter 5 review identified an essential distinction: the earlier
Section 21 primitive-power moments integrate powers of the Abelian primitive;
Section 24 instead weights the primitive by powers of the spectral variable.
The existing local H¹ weighted-action bounds do not by themselves provide
the uniform all-order estimates of Theorems 23.1–23.5.

`CirclePolynomialIntegrationByParts.lean` proves integration by parts for
polynomial spectral weights on a closed circle. Analyticity is required
only near the circle, allowing the contour to enclose the spectral cut.

`SourceHigherActionCircle.lean` defines the level `k+1` contour with the
normalization `1/((k+1)π)` and integrand `z^(k+1) Δ'/sqrt(Δ²-4)`.
It proves formula (5.2), identifying this with `-1/π` times the integral of
`z^k F_n(z)`, and recovers the original action circle at level one.

`SourceRealHigherAction.lean` defines the corresponding real gap integral
in cosine coordinates. Its level-one value equals the original contour-defined
action. The weighted mean-value theorem supplies a point ζ in the closed
periodic gap with `J_(n,k+1) = ζ^k I_n`, including collapsed gaps without
dividing by the action. In particular all odd-level actions are nonnegative.
Every collapsed gap contributes zero at every level.

`SourceHigherActionBoundary.lean` proves that the defining contour equals
this real gap integral on intermediate circles of the constructed Cauchy
families. The proof handles open gaps by their actual boundary values and
collapsed gaps by analytic extension through the collapsed cut. An existence
theorem constructs one family of positive-radius circles working at every
index and level, with no supplied chart or contour hypothesis.

`SourceHigherActionEstimates.lean` turns absolute spectral bounds on a gap
into upper and lower bounds for its odd-level actions. If the gap lies in
`[c-r,c+r]` with `r ≤ |c|`, its level `2m+1` action lies between
`(|c|-r)^(2m) I_n` and `(|c|+r)^(2m) I_n`. This isolates the localization
input needed for the later uniform Sobolev estimates.

Public examples check the constructed contour family at `p = 3`, the
level-one normalization, formula (5.6) at level five, quantitative bounds
for a gap on the negative spectral axis, and vanishing of the actual
contour integral at a collapsed gap.

Validation: the full build passes (6221 jobs), all public examples pass,
and the transitive axiom audit passes for 24011 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: establish the all-order hierarchy trace formula of Theorem 24.1,
then the quantitative norm-dependent localization and higher Sobolev estimates
in Sections 25–28. The new localization comparison assumes endpoint bounds;
it does not yet derive the dissertation's explicit spectral cutoff from the
source norm. Global complex-source gluing and regularity of higher actions
also remain to be assembled. The full dissertation inventory remains open.

## Previous milestone: analytic wellposedness in the dissertation solution sense

The analytic wellposedness and classical nonextension conclusions of
Theorem 18.5 and Corollary 22.2 are now connected to the dissertation's
all-smooth-sequence solution definition in the original source norms.

`AnalyticNLSWellposedness.lean` defines local and global real analytic
wellposedness. Local wellposedness supplies a common positive time and an
open neighborhood of every datum, solutions in the approximation sense,
and an analytic map into the uniform norm space of continuous compact-time
trajectories. Global wellposedness on an open set supplies one all-time
solution map with analytic restrictions for every positive time horizon.
Global wellposedness on the whole source space implies local wellposedness.

`GlobalAnalyticNLSSolutions.lean` proves global analytic wellposedness of
both ordinary and renormalized NLS for `1 < p ≤ 2`, constructing all spectral
data internally. Analyticity holds in the full compact trajectory norm,
not merely after evaluation at each time.

`HigherExponentAnalyticNLSSolutions.lean` constructs a common positive
interval and an analytic solution map around every higher-exponent source.
Together with the global low-exponent theorem, this gives local renormalized
analytic wellposedness for every finite `p > 1`. At higher exponents, an
actual open neighborhood of zero containing a positive source-norm ball
supports global approximation solutions and analytic trajectory maps for
every compact horizon. The public theorems have no supplied spectral atlas,
Birkhoff image admissibility, or classical trajectory hypotheses.

`SmoothClassicalNLSNonextension.lean` states agreement with the constructed
ordinary classical solutions of every smooth datum, allowing different input
and output exponents. Classical uniqueness identifies these constructors
with the earlier finite-gap solutions. Consequently, for `2 < p ≤ q < ∞`,
any such extension is discontinuous at every source outside the Hilbert
locus, on both forward `[0,T]` and symmetric `[-T,T]` intervals with `T > 0`.

Public examples extract the all-time solution map and analytic compact-time
maps at `p = 2`, a common local interval around an arbitrary `p = 3` datum,
and a positive ball with unique global renormalized solutions. They also
check ordinary nonextension with a weaker `p = 4` output norm and the
symmetric-time form of Theorem 18.5(iv).

Validation: the full build passes (6216 jobs), all public examples pass,
and the transitive axiom audit passes for 23973 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: perform a theorem-by-theorem inventory against the dissertation,
including earlier chapters and appendices, and fill any missing results or
interface gaps. This milestone completes the stated analytic wellposedness
assembly; it does not certify the entire dissertation as formalized or assert
global renormalized existence for arbitrary higher-exponent rough data.

## Previous milestone: solutions defined by arbitrary smooth approximation

Arbitrary smooth initial data now determine their global ordinary and
renormalized classical solutions internally. Convergence of the initial
Fourier sources implies uniform convergence of these constructed solutions
on compact time intervals in the established exponent and trajectory domains.

`SmoothNLSData.lean` bundles a smooth period-one initial function with its
original Fourier source at every exponent. Its ordinary and renormalized
classical curves are the proved global constructors. Both source curves
have exactly the prescribed source at time zero; each renormalized curve
uses its own actual initial physical mass.

`SmoothNLSDataDensity.lean` turns the existing actual finite-gap approximation
into a sequence of smooth physical initial data converging to every real
source at finite `p > 1`. This witnesses non-vacuity of the universal smooth
approximation condition; finite-gap data are used only to prove density,
not to restrict the sequences quantified over in the solution definition.

`ConstructedClassicalNLSApproximation.lean` proves uniform compact-time
convergence from arbitrary smooth initial-data convergence alone. Ordinary
and renormalized solutions have this property globally for `1 < p ≤ 2`.
At `2 ≤ p < ∞`, renormalized solutions have it on every compact interval
where the limiting spectral trajectory remains in the actual Birkhoff image.
No pre-existing family of classical trajectories is a hypothesis.

`SmoothApproximationSolution.lean` defines solutions by continuity, the
prescribed initial value, and pointwise convergence for every convergent
sequence of smooth initial data. Time domains contain zero. Smooth density
proves uniqueness on intersections of time domains, and restriction gives
the same definition on open intervals or smaller closed intervals.

`SourceSmoothApproximationSolutions.lean` proves that the global ordinary
and renormalized spectral flows satisfy this definition for `1 < p ≤ 2`.
Public existence-and-uniqueness theorems construct their spectral data
internally. Higher-exponent renormalized paths satisfy the definition on
admissible compact intervals, retaining the actual image-domain hypothesis.

Public examples check smooth density and overlapping-domain uniqueness at
`p = 3`, global Hilbert existence and uniqueness for both equations,
restriction to the dissertation's open time interval, the approximants' own
physical masses, and higher-exponent compact convergence and solutionhood.

Validation: the full build passes (6212 jobs), all public examples pass,
and the transitive axiom audit passes for 23954 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: assemble the existing analytic trajectory maps, local admissible
neighborhoods, small-data global domains, and ordinary nonextension results
with this exact solution definition into the dissertation's wellposedness
statements. No global higher-exponent surjectivity or arbitrary-data global
renormalized existence is asserted. The full dissertation inventory remains.

## Previous milestone: global classical NLS existence and uniqueness

Every smooth period-one physical initial function now has a unique ordinary
classical NLS solution defined for all real times. A constructed physical
gauge also gives the unique global classical renormalized solution, with
mass parameter equal to the actual initial integral `∫₀¹ |f|²`.

`CompatibleIntervalExhaustion.lean` glues compatible curves on the intervals
`[-(n+1), n+1]`. The chosen curve agrees with every finite-interval curve on
its entire closed interval, including the boundary times where the selected
interval can change. Every finite interval is covered by this exhaustion.

`GlobalSmoothFourierNLS.lean` uses closed-interval uniqueness to prove
compatibility of the constructed finite-interval solutions. One original
Fourier trajectory then has norm continuity and the coefficient equation on
every finite interval. It is globally norm-continuous and every original
mode has its ordinary scalar derivative at every real time.

`GlobalClassicalNLSExistence.lean` identifies the physical realization with
the existing global classical trajectory predicate: uniform-norm time
differentiability, spatial smoothness, period one, and the actual NLS equation
hold at every real time. Exact initial reconstruction and the existing
classical uniqueness theorem give global existence and uniqueness for every
smooth periodic physical datum. A named constructor supplies the uniquely
determined solution without a pre-existing trajectory premise.

`GlobalClassicalRenormalizedNLS.lean` applies the physical phase rotation to
this constructed solution. Its mass is the literal mass of the original
initial function, and both ordinary and renormalized curves conserve that
mass for all real times. The renormalized global solution is also unique
among all classical trajectories with that initial function and mass.

Public examples check gluing at interval boundaries, a single norm-continuous
Fourier curve satisfying every mode equation for all times, exact initial
equality and uniqueness as continuous circle-valued curves, construction for
arbitrary smooth initial-data sequences, the literal ordinary PDE at arbitrary
times, and the renormalized `36i*u` correction for initial constant value three.

Validation: the full build passes (6207 jobs), all public examples pass,
and the transitive axiom audit passes for 23889 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: insert these constructed global classical solutions into the
all-smooth-sequence solution definition and the existing approximation and
flow-agreement theorems. Global smooth classical existence is established;
the dissertation’s exact wellposedness assembly and full inventory remain.
The new constructors alone do not assert analyticity or continuity of the
solution map with respect to rough initial data.

## Previous milestone: smooth continuation and arbitrary finite intervals

Conserved physical mass and energy now give a uniform bound on the original
absolute Fourier norm, independent of the reference interval length. Smooth
solutions extend past every finite endpoint in either direction, with no
assumed endpoint value, limit, or norm bound. A finite sequence of uniform
extensions constructs a classical solution on any prescribed finite interval.

`ScalarNLSConservedBound.lean` identifies scalar H¹ data with an actual
real-type Sobolev source and equates its bilinear mass with physical mass.
The existing defocusing coercivity estimate bounds the full H¹ norm by
mass plus energy. Sobolev embedding then gives an explicit ℓ¹ Fourier bound
depending only on those conserved quantities.

`FourierNLSConservedBound.lean` constructs a coefficient-identical strong
H¹ realization of every smooth reference trajectory, at any initial time
in its closed interval. It proves conservation there and bounds the original
unit-weight norm by the initial physical mass and energy. Neither the bound
nor the canonical H¹ initial datum depends on the interval length.

`SmoothFourierNLSContinuation.lean` applies this estimate to every closed
truncation of a half-open solution interval. The existing bounded-continuation
theorem extends past the missing endpoint, preserving all old values and
producing an actual classical physical solution on the extended interval.
Separate forward and backward statements work directly from arbitrary
smooth periodic physical initial functions, without weighted or bound premises.

`SmoothFourierNLSFiniteInterval.lean` fixes one positive extension length
from the initial conserved bound. Induction over a truncated time grid reaches
any prescribed endpoint in finitely many steps. Forward and backward curves
join at any chosen initial time. The physical corollary constructs a classical
solution with the exact prescribed smooth periodic initial function on any
finite closed interval, including singleton intervals and endpoint initial times.

Public examples verify one common bound for every reference interval, actual
ℓ¹ norm control, differentiability at previously missing endpoints in both
directions, initial data at a prescribed interval endpoint, and existence on
arbitrarily long symmetric intervals using only physical smoothness and periodicity.

Validation: the full build passes (6203 jobs), all public examples pass,
and the transitive axiom audit passes for 23860 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: use uniqueness on overlapping finite intervals to assemble one
trajectory on all real times, then establish the corresponding global classical
existence statement. Existence on every prescribed finite interval is proved;
the single all-time trajectory has not yet been assembled. The dissertation’s
exact all-smooth-sequence wellposedness assembly and full inventory also remain.

## Previous milestone: local smooth mass and energy conservation

The local classical solutions constructed from arbitrary smooth period-one
initial functions now conserve both mass and the physical defocusing energy
throughout their closed time interval. Energy is identified with the literal
real integral `∫₀¹ (|u_x|² + |u|⁴)`. No finite-gap or spectral-flow assumption
enters the conservation argument.

`ClosedDerivativeZero.lean` proves constancy on a closed interval from
continuity there and zero ordinary derivative in the interior. It includes
both endpoints and singleton intervals. `LocalClassicalNLSMass.lean` applies
this to every local classical trajectory: the physical PDE makes the mass
derivative zero, and the conserved mass equals the integral over one period.

`SobolevHamiltonianConservation.lean` identifies the full derivative of the
existing H¹ Hamiltonian with its two physical first variations. Their sum
vanishes on the classical pair NLS field by direct algebra. A strong local
H¹ curve satisfying that field therefore conserves energy, including the
endpoints. The pair argument also applies to independent complex components.

`FourierNLSWeightedVelocity.lean` supplies the strong original-variable time
derivative at any nonnegative real Sobolev order from a continuous lift two
orders higher. Initial higher membership is enough: the existing persistence
theorem constructs the lift on the whole reference interval.

`ClassicalNLSSobolevEnergy.lean` constructs bounded real-linear physical
conjugation and the real pair on H¹. Its scalar energy is the actual real
kinetic-plus-quartic integral. Every strong H¹ realization of a local classical
scalar solution conserves this energy.

`LocalSmoothNLSConservation.lean` constructs that realization for arbitrary
smooth periodic initial data. The order-one ℓ¹ lift embeds into Hilbert H¹
without changing coefficients or the physical representative; order-three
persistence gives its strong time derivative. The public existence theorem
returns the actual classical curve with exact initial value and both
conservation laws on the closed local interval.

Public examples check mass at opposite endpoints, fractional-order negative
frequency normalization, exact real energy normalization, the literal energy
integral relative to the original initial function, and H¹ time
differentiability at time zero.

Validation: the full build passes (6199 jobs), all public examples pass,
and the transitive axiom audit passes for 23829 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: combine these conserved quantities with coercivity and the
bounded continuation theorem to construct global smooth classical solutions.
Local existence and conservation are established; arbitrary-data global
existence is not yet assembled. The dissertation’s exact all-smooth-sequence
wellposedness assembly and full inventory also remain.

## Previous milestone: local classical NLS existence

Arbitrary smooth period-one physical initial functions now have actual local
classical defocusing NLS solutions. The initial equality is pointwise, time
differentiation is in the uniform spatial norm, and the equation has the
normalization `i*u_t = -u_xx + 2*u²*conj(u)`. No weighted membership,
finite-gap hypothesis, spectral atlas, or supplied classical solution is assumed.

`PeriodOneSynthesisAlgebra.lean` proves that the actual absolutely convergent
convolution synthesizes to pointwise multiplication and conjugate reflection
to complex conjugation. It identifies the weighted cubic field with the
physical cubic term, including its sign and factor two.

`FourierNLSSpatialDerivatives.lean` constructs bounded first- and second-spatial
derivative multipliers from order-two weighted ℓ¹ to the unit-weight space.
Their synthesized series are the actual classical derivatives, with the
original period-one frequency factor `2π`.

`FourierNLSPhysicalEquation.lean` uses a continuous order-two lift to make the
original Fourier velocity continuous in ℓ¹. Coordinate integration upgrades
the mode equations to a strong original-variable derivative. Bounded synthesis
then gives the physical time derivative in uniform norm, including derivatives
within the closed interval at either endpoint. Its value is exactly the
classical NLS vector field.

`LocalClassicalNLSExistence.lean` defines an interval version of the existing
classical trajectory predicate, proves restriction from global trajectories,
and constructs a local classical solution from every smooth periodic function.
The physical curve is uniformly continuous in time on the closed interval,
spatially smooth and period one there, and satisfies the ordinary time equation
at every interior time. No derivative of the arbitrary exterior extension is
asserted at the interval endpoints.

Public examples check products with complex conjugation, the original negative
frequency normalization, strong physical derivatives within the left endpoint,
the literal defocusing PDE sign, exact initial equality as continuous circle
functions, and uniform-norm time differentiability at time zero.

Validation: the full build passes (6193 jobs), all public examples pass,
and the transitive axiom audit passes for 23784 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: conservation and global smooth classical existence. The local
classical solution is now constructed, but global existence for arbitrary
smooth data is not yet assembled. The dissertation’s exact all-smooth-sequence
wellposedness assembly and full inventory also remain.

## Previous milestone: arbitrary smooth physical initial data

Arbitrary smooth period-one physical initial functions now supply the full
weighted Fourier data required by the common-interval existence theorem.
The local Fourier solution starts from their actual unit-period Fourier
integrals, and its physical realization recovers the original function
pointwise. No weighted membership, finite-gap hypothesis, spectral atlas,
or pre-existing classical solution is a premise.

`SobolevAbsoluteSummability.lean` proves that one additional weighted ℓ²
order supplies weighted ℓ¹ membership at any real order, including negative
orders. `SmoothPeriodicCoefficients.lean` uses the actual derivative-coefficient
identity and the Sobolev graph characterization to induct over integer
Hilbert orders. Inclusion gives arbitrary real orders, and the extra-derivative
embedding gives absolute summability. Even period-two modes recover the
original period-one coefficients without losing the frequency normalization.

`FourierNLSPhysicalSynthesis.lean` realizes every Fourier curve in the uniform
norm on the ambient circle. Fourier-space continuity gives uniform physical
continuity; the pullback is period one and its unit-interval Fourier integrals
recover every original trajectory coefficient.

`SmoothInitialFourierNLS.lean` constructs the canonical unit-weight datum from
a smooth periodic function, proves all its Sobolev memberships, and proves
pointwise reconstruction. Its existence theorem selects one positive local
interval for every Sobolev order and returns a physical curve continuous in
time in the uniform spatial norm, with spatial smoothness and period one throughout the closed interval.

Public examples cover negative-order absolute summability, fractional Hilbert
and ℓ¹ orders, normalized constant zero modes, reconstruction at negative
spatial points, negative physical Fourier modes at negative times, exact
initial equality as continuous circle functions, and a common interval for
all orders using only smoothness and periodicity of the physical initial data.

Validation: the full build passes (6189 jobs), all public examples pass,
and the transitive axiom audit passes for 23728 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: identify the physical time derivative and NLS PDE from the original
mode equations and continuous higher-weight lifts. Then prove conservation
and global smooth classical existence. The current physical curve is
continuous in uniform spatial norm and smooth in space; the actual classical
time equation and global existence are not yet assembled. The dissertation’s
exact all-smooth-sequence wellposedness assembly and full inventory also remain.

## Previous milestone: common-interval Sobolev persistence and smooth synthesis

Higher-weight Fourier NLS solutions now exist on the entire closed interval
of a compatible reference solution. No higher-weight trajectory or norm bound
is assumed. Every nonnegative real Sobolev order present initially persists
on that same interval, with an actual norm-continuous higher-weight solution
of the original coefficient equations.

`FourierNLSReferenceInterval.lean` derives one high-norm bound from the compact
reference interval and the tame estimate. Its positive local extension length
is fixed once. Induction over a truncated time grid constructs solutions up
to each grid point; an Archimedean bound makes finitely many steps cover the
whole interval. Separate forward and backward constructions join at any
prescribed initial time, including either endpoint. Endpoint uniqueness
identifies all coefficients with the reference throughout the closed interval.
The reference and higher weights need not be ordered.

`LocalSmoothFourierNLS.lean` turns initial Sobolev membership into a continuous
higher-weight lift and propagates that membership to every time in the interval.
All initial Sobolev weights give genuine spatial `C∞` Fourier synthesis,
including at the interval endpoints. Local existence selects one positive
interval first, and that interval then supports the solutions for every
nonnegative real Sobolev order. Thus the time intervals no longer shrink
as the order increases.

Public examples cover fractional-order lifting from a nonzero initial time,
negative modes at both reference endpoints, backward construction from the
right endpoint, zero order on a singleton interval, endpoint-to-endpoint
membership propagation, spatial smoothness at both endpoints, and the crucial
quantifier order: one positive time interval before all Sobolev orders.

Validation: the full build passes (6185 jobs), all public examples pass,
and the transitive axiom audit passes for 23709 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: prove that arbitrary smooth periodic physical initial data supply
all the weighted coefficient memberships used here, identify the synthesized
physical time derivative and classical PDE, and establish global continuation
using conservation. The current theorem gives a common local Fourier interval
and spatially smooth synthesis; it is not yet the complete global smooth
classical-existence theorem. The dissertation’s exact all-smooth-sequence
wellposedness assembly and full inventory also remain incomplete.

## Previous milestone: bounded continuation and Sobolev regularity continuation

Bounded Fourier NLS trajectories now extend past either finite endpoint.
For every nonnegative real Sobolev order, a compatible reference solution
on the closed interval supplies continuation without assuming either a high
norm bound or a low norm bound. Compactness gives the latter, and the tame
Gronwall estimate gives the former.

`FourierNLSEndpointUniqueness.lean` proves quantitative two-sided stability
for interaction curves and uniqueness from every closed-interval initial
time. The original Fourier equations inherit endpoint uniqueness and
cross-weight compatibility, including singleton intervals.

`UniformLocalNLS.lean` defines the explicit half-lifespan
`nlsLocalTime B = 1/(2*(B+1)^3+1)` for every norm bound `B ≥ 0`.
The same interval length works for every spectral weight and every real
initial time. It constructs strong interaction solutions and restores the
original coefficient equations with the prescribed original initial value.

`ClosedIntegralCurveJoin.lean` glues solutions of a time-dependent field
on adjacent closed intervals. Matching endpoint values and the within-interval
derivatives give the derivative at the join itself. `FourierNLSContinuation.lean`
transfers this to original Fourier trajectories and proves uniform left and
right extensions preserving the entire old closed interval. A trajectory
bounded on all closed truncations of a half-open interval extends past the
missing endpoint, preserving every old value before it. No assigned value
or limiting value at the missing endpoint is assumed.

`FourierNLSRegularityContinuation.lean` combines closed-endpoint compatibility,
compactness of a reference trajectory, and tame growth. It proves continuation
in both directions for every additive spectral weight and, in particular,
every nonnegative real Sobolev order. The reference weight need not be ordered
with the higher weight. These are continuation criteria for supplied trajectories;
constructing a higher-regularity solution on a full prescribed reference
interval is the next existence step.

Public examples cover cross-weight uniqueness from the right endpoint,
the explicit lifespan `1/55` at norm bound two, negative initial times,
the original equation at a negative joining time and Fourier mode, preservation
of the old interval under left extension, both half-open continuation criteria,
and fractional-order continuation with no norm-bound premises.

Validation: the full build passes (6183 jobs), all public examples pass,
and the transitive axiom audit passes for 23701 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: assemble local existence and continuation into common-interval
persistence for all Sobolev orders, identify the synthesized physical PDE,
and prove global smooth classical existence using conservation. The exact
all-smooth-sequence wellposedness assembly and dissertation-wide inventory
also remain incomplete.

## Previous milestone: tame Sobolev estimates and two-sided norm growth

Tame convolution and cubic NLS estimates now control every nonnegative real
Sobolev order using only one high-norm factor. The resulting a priori growth
bound is exponential in elapsed absolute time, with its rate determined by
the raw Fourier ℓ¹ norm. It applies to every local Fourier trajectory and
can use a low norm bound from an independently constructed compatible curve.

`TameSpectralConvolution.lean` proves the additive weight inequality
`w_s(n+k) ≤ 2^s*(w_s(n)+w_s(k))` and derives a tame translation bound from
the exact shifted-norm sum. Summing the convolution series gives
`‖a*b‖_s ≤ 2^s*(‖a‖_s*‖b‖₀ + ‖a‖₀*‖b‖_s)`.
The abstract estimates also cover any spectral weight with an additive bound.

`TameCubicNLS.lean` proves raw-norm invariance under conjugate reflection
and free evolution. Applying the tame convolution estimate to the actual
cubic field gives
`‖N(a)‖_s ≤ (4*(2^s)^2+2*2^s)*‖a‖_s*‖a‖₀^2`.
The same constant works for the interaction field at every real time.

`IntervalNormGronwall.lean` proves two-sided Banach-space exponential growth
using only derivatives within the closed interval. It includes both endpoints,
equal endpoints, zero coupling, and zero initial norm without division.
`FourierNLSNormGrowth.lean` applies this to the strong interaction equation.
If the raw norm is bounded by `M` between two times, the high norm grows by
at most `exp((4*(2^s)^2+2*2^s)*M^2*|time-initial|)`.
Coefficient uniqueness allows the bound to come from a compatible trajectory
in any spectral weight, without ordering the two weights or assuming a bound
on the high norm itself.

Public examples cover fractional orders and negative shifts, the tame product,
the explicit second-order cubic constant 72, free phases at negative times,
backward growth between both interval endpoints, a compatible comparison
trajectory in an arbitrary weight, and the zero-coupling interval estimate.

Validation: the full build passes (6178 jobs), all public examples pass,
and the transitive axiom audit passes for 23676 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: turn the a priori high-norm bound into continuation and common-interval
persistence of arbitrarily high regularity, identify the synthesized physical
PDE, and use conservation to construct global classical solutions for all
smooth initial data. The present estimates hold on an existing interval;
they do not yet extend it. The dissertation’s all-smooth-sequence wellposedness
assembly and full inventory remain incomplete.

## Previous milestone: local Fourier uniqueness and weight compatibility

Local weighted Fourier NLS solutions are now unique on their asserted
intervals and compatible across arbitrary spectral weights. The statements
apply to every norm-continuous curve satisfying the original mode equations,
not just to the particular solution selected by the existence construction.
Equality at any interior initial time determines the entire closed interval.

`WeightedCoordinateFTC.lean` proves that continuous weighted curves with
continuous coordinate velocities satisfy the full Bochner integral identity.
Bounded coefficient evaluation commutes with integration; the scalar
fundamental theorem identifies every coefficient. Differentiating that
identity gives the actual weighted Banach-space derivative, including
one-sided derivatives at the interval endpoints.

`FourierNLSIntegral.lean` packages the mode equations and norm continuity in
`IsFourierNLSTrajectoryOn`. Removing the free phases cancels the unbounded
linear symbol in each coordinate. The coordinate-to-integral theorem then
supplies the strong interaction equation and its integral form. Restriction
to smaller closed intervals preserves the trajectory predicate.

`FourierNLSUniqueness.lean` derives a common norm bound for any two interaction
curves from compactness and applies the uniform cubic Lipschitz estimate.
It proves uniqueness from any interior time and combines it with local
existence. Uniqueness is correctly stated as equality on the interval;
values outside that interval are unrestricted.

`FourierNLSWeightCompatibility.lean` proves that bounded weight inclusions
commute with free evolution, the actual cubic convolution, and the interaction
field, and preserve the original trajectory equations. Comparing both curves
in the unit-weight space proves coefficient equality even for incomparable
weights. Independently constructed solutions on different intervals agree
on their closed overlap when the shared initial time is interior to it.

Public examples cover strong endpoint derivatives from scalar coordinate
equations, negative-time Bochner identities with a nonzero base time,
uniqueness from a nonzero interior time, both overlap endpoints and negative
modes across arbitrary weights, and the interval-scoped unique existence theorem.

Validation: the full build passes (6174 jobs), all public examples pass,
and the transitive axiom audit passes for 23658 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: prove persistence of arbitrarily high Sobolev regularity on a
common time interval, identify the synthesized physical classical PDE, and
use conservation and continuation to construct global classical solutions
for all smooth initial data. Compatibility alone does not prevent the
individual weighted existence intervals from shrinking as regularity grows.
The dissertation’s all-smooth-sequence wellposedness assembly and full
inventory remain incomplete.

## Previous milestone: local weighted Fourier NLS existence

Every initial datum in a spectral-weighted ℓ¹ space now has a local,
norm-continuous Fourier NLS solution on a positive symmetric time interval.
Every original Fourier coefficient satisfies the quadratic Schrödinger term
and literal cubic convolution. No finite Fourier support, finite-gap condition,
spectral atlas, or assumed classical solution is used in this existence proof.

`WeightedPhaseFlow.lean` transports arbitrary diagonal unit phases through
the weighted coefficient isometry. It proves the group law, norm preservation,
and joint strong continuity at every finite exponent, without bounding the
frequency sequence.

`CubicNLS.lean` uses physical conjugate reflection and the actual weighted
convolution to define the field `-2i (a * a * conjugateReflection a)`. Its norm
is at most `2*‖a‖³`; on a norm-bounded ball it has Lipschitz constant `6*R²`.
Both estimates hold for every spectral weight.

`LocalNLSInteraction.lean` removes the free phases with frequencies
`-(2πn)²`. The resulting time-dependent cubic field is jointly continuous
and has the same bounds uniformly in time. Picard–Lindelöf then constructs
an interaction solution on a positive interval about zero, with its actual
Banach-space derivative.

`LocalNLSExistence.lean` restores the free evolution and proves the original
mode equations. The curve is continuous in the full weighted norm; every
mode has the asserted derivative within the closed interval, hence an
ordinary derivative at each interior time. The cubic coefficient formula
retains both convolution sums and the reflected conjugate index explicitly.

Public examples check the physical sign at negative modes, isometry and
reversibility at negative times, the time-independent Lipschitz bound,
the exact zero-mode nonlinearity, arbitrary weighted initial data, and
interior differentiability for the concrete Sobolev weight of order four.

Validation: the full build passes (6170 jobs), all public examples pass,
and the transitive axiom audit passes for 23623 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: prove compatible local uniqueness and persistence of arbitrarily
high Sobolev regularity on a common interval, identify the physical classical
PDE after synthesis, and use conservation and continuation to obtain global
classical solutions for every smooth initial datum. The current theorem is
local Fourier-space existence in each fixed weighted ℓ¹ space; it is not yet
the missing global smooth classical-existence theorem. The dissertation’s
all-smooth-sequence wellposedness assembly and full inventory remain incomplete.

## Previous milestone: smooth classical agreement across source exponents

Canonical smooth physical sources and classical agreement now cover every
finite source exponent greater than one. Ordinary NLS agrees with the global
source flow for `1 < p ≤ 2`; renormalized NLS agrees with the actual image
flow for every finite `p > 1`. Every supplied classical approximation family
converges uniformly on compact time intervals in the corresponding original
source norm, globally below two and on admissible limiting intervals above two.

`SmoothPeriodOneSourceExponent.lean` embeds the canonical H¹ coefficients into
ℓ¹ and then into every exponent at least one. The first component remains the
literal unit-period Fourier integral, the second retains real conjugate
reflection, and exponent inclusions commute with this construction. At two
it is exactly the previously constructed Hilbert source.

`SmoothClassicalNLSAgreementExponent.lean` constructs auxiliary Hilbert
spectral data internally and uses exponent compatibility to identify the
entire real source of every supplied ordinary or renormalized classical
trajectory. Above two, smooth sources stay in the actual Birkhoff image for
all time. This proves classical agreement of the image flow without assuming
surjectivity of the Birkhoff map at those exponents.

`ClassicalNLSSmoothApproximationExponent.lean` combines that agreement with
analytic dependence of compact-time source paths. Initial-source convergence
alone gives uniform source-norm convergence of arbitrary ordinary or
renormalized classical families in the global range. Above two, the
renormalized conclusion retains the explicit condition that the rough limit
belongs to the actual compact-time trajectory domain. Every approximant uses
its own physical initial mass. No finite-gap, stronger-norm convergence, or
common amplitude bound is required.

Public examples cover exponent-one representation, inclusion from two to
four, complete source equality at negative times, negative physical Fourier
modes, zero-length intervals, and arbitrary classical approximation families
at exponent four with an admissible rough limit and varying initial masses.

Validation: the full build passes (6166 jobs), all public examples pass,
and the transitive axiom audit passes for 23581 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: formulate the dissertation’s all-smooth-sequence solution definition
and assemble its global, local, and near-zero analytic wellposedness assertions.
The current results assume the supplied classical trajectories exist. The
classical existence input for every smooth initial datum, cited from [7] on
dissertation page 85, still needs a proved implementation before claiming the
full statements. The dissertation is not complete.

## Previous milestone: smooth physical sources and renormalized classical agreement

Every smooth period-one continuous function now has a canonical real H¹
source with its actual unit-period Fourier coefficients. Both ordinary and
renormalized classical NLS trajectories agree with the corresponding Hilbert
spectral flows without a supplied Sobolev representative or a finite-gap
condition. In the renormalized case the parameter is exactly the physical
mass of that trajectory’s initial data.

`SmoothPeriodOneSource.lean` derives classical H¹ regularity from spatial
smoothness. Reading the even ambient-circle coefficients preserves the H¹
weight and gives the actual unit-period coefficients. Conjugate reflection
constructs the real pair; bounded synthesis recovers the original continuous
function pointwise, including the circle endpoints.

`SourceClassicalRenormalizedNLSAgreement.lean` identifies the spectral mass
with the physical mass for every real H¹ representative. The inverse
classical gauge reduces to the established ordinary agreement theorem,
and the full-source gauge restores the renormalized flow. Equality holds
in physical L² and for every original Fourier integral at all real times.

`SmoothClassicalNLSAgreement.lean` constructs the initial source internally
for both equations and calibrates its mass by the actual physical integral.
No H¹ representative or spectral mass equality is left as a premise.

`ClassicalNLSSmoothApproximation.lean` proves convergence of every family
of classical ordinary or renormalized trajectories whose canonical initial
Hilbert sources converge to an arbitrary real Hilbert source. Their physical
L² paths converge in the uniform compact-time norm. No finite-gap condition,
H¹ convergence, common amplitude bound, or common mass parameter is assumed.
Each renormalized approximant uses its own physical initial mass.

Public examples check exact reconstruction and physical mass, negative
Fourier modes and times for both equations, arbitrary renormalized sequences
with varying masses and a rough Hilbert limit, and zero-length intervals.

Validation: the full build passes (6163 jobs), all public examples pass,
and the transitive axiom audit passes for 23559 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: transfer arbitrary-classical agreement and approximation convergence
to all admissible source exponents, retain the actual local image domains
above two, and assemble the dissertation’s all-smooth-sequence solution and
wellposedness statements. Classical existence for arbitrary smooth initial
data is not proved by these conditional agreement/convergence results and
must be supplied or established before claiming the complete statements.
The dissertation is not complete.

## Previous milestone: energy bounds and arbitrary classical H¹ agreement

The ordinary spectral flow now agrees with every classical trajectory
whose initial continuous representative is supplied by a real H¹ source.
The equality holds at every real time in physical L² and for every literal
unit-period Fourier integral. There is no finite-gap condition on the
limiting source and no supplied bound on approximating trajectories.

`SourceFiniteGapEnergyConservation.lean` proves that the actual physical
third Hamiltonian is fixed by the original actions. The trace identity,
conservation of the mass, and invariance of cubic moments give conservation
of the H¹ Hamiltonian for both physical finite-gap flows at all real times.

`SourceSobolevEnergyCoercivity.lean` identifies the real H¹ mass and kinetic
terms with squared first-component norms. H¹ density transfers the physical
conjugate-pair condition to every real H¹ representative, making the quartic
interaction nonnegative. It proves
`‖a₁‖² ≤ 2*(mass.re + energy.re)` and supplies a continuous explicit bound
`sobolevEnergyAmplitude` on the spatial uniform norm.

`SourceFiniteGapUniformBound.lean` combines conservation and coercivity.
Each finite-gap ordinary and renormalized physical trajectory is bounded
for all real time by its initial amplitude bound. Every H¹-convergent
finite-gap family has one eventual common bound, regardless of the number
of open gaps or Fourier modes.

`SourceClassicalNLSApproximation.lean` now applies the actual PDE stability
theorem without assuming the common bound: it derives that bound from
H¹ convergence and conserved quantities. Actual finite-gap classical
solutions converge to any supplied classical limiting solution, uniformly
on compact time intervals in physical L².

`SourceClassicalNLSAgreement.lean` compares this PDE limit with continuity
of the spectral source flow. Uniqueness of limits proves equality for
arbitrary H¹ initial representatives. The physical Hilbert realization
doubles ambient-circle modes, and the final theorem recovers every original
unit-period Fourier integral with the correct normalization.

Public examples cover full-H¹ coercivity, negative-time renormalized energy
conservation, simultaneous all-time bounds for both equations, compact-time
approximation without a supplied bound, and classical/spectral agreement
at negative times and negative Fourier modes.

Validation: the full build passes (6159 jobs), all public examples pass,
and the transitive axiom audit passes for 23520 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

Remaining: package H¹ representatives of arbitrary smooth initial data,
transfer this agreement through the physical mass gauge to the renormalized
flow and through exponent inclusions, and formulate the all-smooth-sequence
solution definition on dissertation page 86. The current agreement theorem
assumes a classical trajectory and its H¹ initial representative; it does
not establish classical existence for all smooth initial data. Those
requirements and theorem-level wellposedness assembly remain to be checked.
The dissertation is not complete.

## Previous milestone: arbitrary classical stability and physical mass

The actual classical PDE now gives quantitative two-sided-in-time L²
stability for arbitrary smooth trajectories. With a common amplitude bound
`M` between times `a` and `b`, the squared L² error is at most its value at
`a` times `exp(12*M²*|b-a|)`. On `[-T,T]` one common constant controls the
whole path. Convergence of initial data in physical L² therefore gives
uniform-in-time L² convergence of any classical approximation family with
an eventual common amplitude bound. No finite-gap hypothesis is used.

`ClassicalNLSStability.lean` derives these conclusions from the existing
PDE difference-energy derivative, applying Grönwall in both time directions.
The final convergence theorem concerns the actual `ContinuousMap.toLp`
realizations, not only scalar error quantities. Early approximants may
fail the common bound.

`ClassicalNLSMass.lean` proves physical mass conservation for every classical
ordinary or fixed-parameter renormalized trajectory. Periodic integration
by parts cancels the linear term, and the cubic mass pairing has zero real
part. Uniform-norm time differentiability supplies the Hilbert norm derivative;
zero derivative gives conservation between arbitrary real times. The unit
scalar gauge transfers conservation to renormalized trajectories. The mass
is identified with its literal unit-interval integral. When the renormalized
parameter equals the physical initial mass, the equation uses that same
physical integral at every time, as in the dissertation.

Public examples check backwards evolution from a nonzero initial time,
a zero-length interval, an eventually bounded approximation sequence,
physical mass at negative and positive times, a negative fixed gauge
parameter, and recovery of the nonlocal renormalized equation.

Validation: the full build passes (6154 jobs), all public examples pass,
and the transitive axiom audit passes for 23475 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

The common amplitude bound for the approximating family remains an explicit
hypothesis. The next step is to derive it for H¹-convergent finite-gap
approximations from conservation and coercivity of the defocusing physical
energy. The resulting stability limit must then be identified with the
spectral flow for arbitrary smooth initial data. Until that bridge is proved,
the all-smooth-approximation solution definition on dissertation page 86 and
the full wellposedness theorems remain incomplete.

## Previous milestone: local and near-zero global classical renormalized extensions

For every finite `p > 2`, every real source now has an open neighborhood
and a common positive time interval with an analytic renormalized
classical solution-map extension. Every continuous classical extension
on that neighborhood coincides with it there and is automatically analytic.
One invariant open neighborhood of zero, containing a positive source-norm
ball, supports a global group with the same classical agreement and uniqueness
on every compact time interval.

`SourceHamiltonianRenormalizedImageFlow.lean` gives the physical time
orientation of the actual image-inverse flow. Path evaluation and analytic
regularity keep the admissibility condition explicit. The time-addition
law and the comparison with the global flow below two use the same orientation.

`SourceRenormalizedImageClassicalAgreement.lean` proves that every Hilbert
trajectory, included into an exponent `p ≥ 2`, stays in the actual Birkhoff
image for all real time and coincides with the larger-exponent image flow.
This does not assume global surjectivity at that exponent. Every finite-gap
source has its coefficient-identical Hilbert model, so its image-flow
coordinates equal the actual Fourier integrals of the canonical classical
renormalized solution for every time.

`ClassicalRenormalizedNLSLocalExtension.lean` formulates classical agreement
and continuity on an initial-data neighborhood. Openness and actual finite-gap
density prove uniqueness there, the original initial values, and uniform
compact-time convergence of arbitrary finite-gap classical approximations. Early
approximants may lie outside the neighborhood. The local existence theorem
constructs a positive interval, an open source neighborhood, and its analytic
classical extension, with all spectral data constructed internally.

`ClassicalRenormalizedNLSSmallGlobalExtension.lean` constructs one invariant
open neighborhood of zero and a physical global group on it. The theorem
supplies a contained positive-radius source ball, exact initial values,
invariance, the group law, joint continuity, and analytic compact-time maps
that are the unique continuous classical extensions on that neighborhood.
This supplies the finite-gap classical extension part of Corollary 22.2(ii).

Public examples check arbitrary `p=3` initial data, local uniqueness and
automatic analyticity, the zero-length initial-value identity, classical
approximations that are only eventually in the neighborhood, inverse time
maps on the small global domain, its analytic classical compact-time maps,
and negative-time/negative-mode finite-gap agreement.

Validation: the full build passes (6152 jobs), all public examples pass,
and the transitive axiom audit passes for 23451 NLS declarations. The 21
existing warnings are unchanged; no new axioms or unfinished proofs were added.

The definition on dissertation page 86 requires convergence for every
sequence of smooth initial potentials. The current results quantify over
finite-gap classical approximations. Agreement with arbitrary smooth
classical solutions, and hence the full smooth-approximation definition,
remains unproved. Compatibility and theorem-level Chapter 4 assembly also
remain. The dissertation is not complete.

Next implementation targets:

1. Complete smooth classical existence from the now constructed Fourier
   solutions for arbitrary smooth physical data. Identify the synthesized
   time derivative in the uniform physical norm: use a continuous higher-weight
   lift to control the quadratic linear symbol, the coordinate-to-integral
   theorem to obtain the strong derivative, and bounded physical synthesis.
   Order two controls the quadratic symbol; the absolutely convergent
   convolution series and Fourier shift identities provide the product formula.
   Identify spatial differentiation and cubic convolution with the actual
   physical NLS equation, then derive conservation and global continuation.
   Uniform spatial-norm continuity and spatial smoothness alone do not yet
   establish the classical time equation or global existence.
   Then formalize the all-smooth-sequence definition on page 86 and assemble
   the analytic solution maps using the proved cross-exponent approximation
   results and their actual trajectory-domain guards.
2. Prove compatibility on overlapping source neighborhoods and time intervals
   and across admissible exponents; assemble Theorems 18.5 and 22.1 and
   Corollary 22.2 only after their full hypotheses and conclusions are met.
3. Continue the dissertation-wide theorem inventory and fill remaining
   requirements, retaining the distinction from rough weak-PDE uniqueness.

## Previous progress: the global classical renormalized extension

For `1 < p ≤ 2`, the Hamiltonian-oriented renormalized flow is now the
unique continuous extension of the actual classical finite-gap solution
map on every compact interval `[-T,T]`. It is real analytic in the uniform
trajectory norm. Every convergent finite-gap approximation has the same
compact-time limit, and one global group realizes these maps consistently.

`SourceHamiltonianRenormalizedFlowExponent.lean` proves compatibility of
the actual renormalized frequencies across finite source exponents and
of the global physical source flow for `1 < p ≤ q ≤ 2`. Independently
constructed spectral atlases give the same coefficient-compatible flow.

`SourceHamiltonianRenormalizedTrajectories.lean` transfers compact-time
analyticity through bounded time reflection. It provides uniform-path
continuity and convergence in the original source norm with the physical
Hamiltonian time orientation.

`ClassicalRenormalizedNLSContinuousExtension.lean` identifies the source
flow's finite-gap coefficients with the actual Fourier integrals of the
canonical classical renormalized solution. Density proves uniqueness of
continuous extensions, convergence for arbitrary supplied classical
approximation families, and automatic analyticity of every such extension.
The global existence theorem constructs all spectral data and supplies
joint continuity, initial values, the group law, and analytic compact-time maps.

`SourceRenormalizedOrdinaryGauge.lean` extends the physical mass-gauge
identity from classical finite-gap solutions to every source in `1 < p ≤ 2`.
The entire first coefficient sequence differs from the ordinary flow by
`exp(4*i*M*time)` and the second by its conjugate. The proof uses actual
physical Fourier agreement, finite-gap density, and source-norm continuity;
no gauge-equivariance premise on the Birkhoff map or pointwise realization
of rough data is required.

Public examples check the noninteger exponent `p=3/2`, automatic analyticity,
a zero-length time interval, inverse time maps, uniqueness, arbitrary
classical approximation families, the negative-time convention, preservation
of both component norms under the full source gauge, and its sign at negative time.

Validation: the full build passes (6148 jobs), all public examples pass,
and the transitive axiom audit passes for 23426 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This identifies the global renormalized solution map in the range `1 < p ≤ 2`.
Physical identification of the local maps above two and their global maps
near zero remains. Continuous-extension uniqueness does not assert uniqueness
among arbitrary rough weak-PDE trajectories. The dissertation is not complete.

## Previous progress: classical renormalized uniqueness and gauge agreement

The renormalized finite-gap solution is now unique in the classical
solution class: smooth period-one spatial slices and differentiability
in the uniform function norm. This holds for finite-gap sources at every
finite `p > 1`, with mass given by the original physical unit-period
integral. Its classical Fourier coefficients agree with the constructed
Hilbert spectral trajectory of the same source.

`ClassicalRenormalizedNLSGauge.lean` defines the classical equation with a
fixed real mass parameter. Multiplication by `exp(4*i*m*time)` transports
the PDE from parameter `M` to `M+m`, preserves the uniform norm, and has
an exact inverse. The inverse mass gauge reduces to ordinary classical
NLS. The proved ordinary uniqueness theorem therefore gives renormalized
uniqueness from agreement at any one real time, without a finite-gap
restriction on this uniqueness lemma.

`SourceFiniteGapClassicalRenormalizedNLS.lean` places the constructed
renormalized finite-gap flow in that uniform-norm classical class and
proves agreement with every classical solution with the same initial
representative and physical mass. Uniqueness also proves the actual
physical identity `u_ren(time) = exp(4*i*M*time)*u_NLS(time)`, with the
positive physical gauge phase and no assumed Birkhoff gauge equivariance.

`ClassicalRenormalizedNLSFiniteGap.lean` defines the mass as the actual
physical integral and constructs a canonical classical renormalized
trajectory at every finite exponent above one. It proves unique existence,
exact initial values, agreement of its actual Fourier integrals with the
Hilbert spectral flow, and conservation of the physical mass integral for
any classical solution with the given finite-gap initial data. Thus the
constant mass in its equation is also its mass at every later or earlier time.

Public examples check uniqueness from negative initial time, inverse
gauges, negative and zero mass parameters, uniform-norm preservation,
finite-gap unique existence at `p=3`, conserved physical mass at negative
time, the sign of the actual physical gauge, and negative Fourier modes
of the canonical `p=3` solution.

Validation: the full build passes (6144 jobs), all public examples pass,
and the transitive axiom audit passes for 23401 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Rough renormalized solution-map identification remains: these results
provide its classical dense-domain agreement, but do not yet prove the
unique continuous global/local extension in all the stated exponent ranges.
The dissertation formalization is not complete.

## Previous progress: pointwise physical renormalized NLS

The Hamiltonian-oriented renormalized spectral trajectory now solves
`i*u_t = -u_xx + 2*|u|²*u - 4*M*u` pointwise for every real finite-gap
Hilbert source and every real time. The mass is exactly the unit-period
integral of the squared modulus of the physical representative and is
conserved along the trajectory.

`SourceHamiltonianRenormalizedFlow.lean` reverses the existing printed
spectral time convention. It proves the group law, action and mass
conservation, joint continuity, initial-data analyticity, and full source
norm differentiability for finite-gap data, for `1 < p ≤ 2`.

`SourceFiniteGapRenormalizedHamiltonianODE.lean` identifies the Hilbert
velocity as a finite sum of original action Hamiltonian fields and makes
the equation autonomous. `SourceFiniteGapRenormalizedSobolevTime.lean`
uses action conservation to retain a common closed-gap tail, upgrading
the actual trajectory to differentiability in H¹.

`SourceRenormalizedMassCorrection.lean` derives the correction from the
mass action-cotangent trace. The constant-frequency action field is
`-sourcePhase`, so subtracting `4*M` from the ordinary frequencies adds
`4*M*sourcePhase` to the actual source velocity. Derivative uniqueness
identifies the ordinary part with the previously proved physical NLS
field. No gauge-equivariance assumption is supplied.

`SourceFiniteGapPointwiseRenormalizedNLS.lean` synthesizes the H¹ velocity
and proves both physical time equations. The first component has the
negative `4*M*u` correction after multiplication by `i`; the conjugate
component has the opposite mass rotation. It also constructs a global
pointwise trajectory with the exact original physical initial value and
smooth period-one spatial slices, constructing all spectral data internally.

Public examples check inverse time maps, the negative-time convention,
initial Fourier coefficients, conservation of actual physical integrals,
the PDE with its current mass integral, the conjugate-component sign, and
global existence without supplied spectral data.

Validation: the full build passes (6141 jobs), all public examples pass,
and the transitive axiom audit passes for 23342 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This completes pointwise physical identification on the Hilbert finite-gap
locus. Uniqueness in a classical renormalized solution class and transfer
to the rough global/local solution-map extensions remain. The full
dissertation formalization is not complete.

## Previous progress: the unique continuous classical NLS extension

For `1 < p ≤ 2`, the Hamiltonian-oriented ordinary flow is now the unique
continuous extension of the actual finite-gap classical NLS solution map
on every compact interval `[-T,T]`. Every such continuous extension is
real analytic in the full uniform trajectory norm. One constructed global
group realizes these compact-time maps consistently at all times.

`SourceHamiltonianFlowExponent.lean` proves that the physical mass,
ordinary frequency, and full Hamiltonian-oriented source flow commute
with source-exponent inclusion for `1 < p ≤ q ≤ 2`. The result holds for
all sources, using the original coefficient-compatible frequencies and
Birkhoff maps, without a finite-gap restriction.

`SourceHamiltonianTrajectories.lean` gives the compact-time physical paths.
Time reflection acts by a bounded linear map on trajectory space, so the
proved analyticity of the original spectral trajectory transfers to the
Hamiltonian orientation. Convergent initial sources give convergence in
the uniform compact-time source norm.

`ClassicalNLSContinuousExtension.lean` identifies every finite-gap path
with the actual Fourier integrals of the unique classical NLS solution.
Actual finite-gap density proves uniqueness among continuous solution-map
extensions. Every source admits classical finite-gap approximation, and
every convergent finite-gap approximation with the prescribed classical
coefficient trajectories has the same compact-time limit. The global
existence theorem constructs all spectral data and supplies joint
continuity, the original initial values, the group law, and analytic
compact-time maps.

Public examples check the noninteger exponent `p = 3/2`, automatic
analyticity, a zero-length interval, inverse time maps, uniqueness of
extensions, arbitrary classical approximation families, and evaluation at
negative physical time with the correct spectral time orientation.

Validation: the full build passes (6136 jobs), all public examples pass,
and the transitive axiom audit passes for 23291 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This identifies the general ordinary solution map as the unique continuous
extension of classical finite-gap dynamics. It does not establish uniqueness
among arbitrary rough weak-PDE trajectories. Physical identification of the
renormalized flow and the remaining wellposedness claims are still separate
tasks. The dissertation formalization is not complete.

## Previous progress: physical NLS nonextension on positive time intervals

The nonextension assertion now concerns actual classical NLS solutions,
with the physical Hamiltonian sign, on the forward interval `[0,T]` of
Corollary 22.2(iii). Restriction from `[-T,T]` also gives the formulation of
Theorem 18.5(iv). For finite `2 < p ≤ q`, any proposed source-trajectory
extension agreeing with the actual finite-gap classical solutions fails
continuity at every source outside the Hilbert locus.

`HamiltonianPhaseObstruction.lean` transfers the uniform-trajectory
obstruction to negative exponential phases by conjugation. It retains the
same positive interval; no negative-time observations are required.

`SourceHamiltonianSourceObstruction.lean` identifies the observed Hilbert
finite-gap trajectory with the actual Hamiltonian phase at every real time
and after source-exponent inclusion. Diverging physical frequencies and a
nonzero limiting coordinate then obstruct source-map continuity on `[0,T]`.

`ClassicalNLSNonextension.lean` constructs the unique classical finite-gap
trajectory at every finite source exponent greater than one. Its actual
Fourier integrals equal the coefficients of the Hamiltonian-oriented
Hilbert flow. Agreement with any classical representative is equivalent
to agreement with this uniquely constructed trajectory. The nonextension
theorems construct all atlases and Birkhoff data internally and require
only agreement on the finite-gap domain. Reality determines the second
component from the first, so the public hypothesis uses scalar physical
Fourier coefficients directly.

Public examples check negative phases on `[0,1]`, the classical initial
representative at `p = 3`, forward nonextension from `p = 3` to `q = 4`,
symmetric-time nonextension in the original `p = 3` norm, and canonical
agreement at a negative Fourier mode.

Validation: the full build passes (6133 jobs), all public examples pass,
and the transitive axiom audit passes for 23267 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This completes the transfer of the nonextension assertion to the actual
smooth classical finite-gap reference solutions. Physical solution-map
identification beyond finite-gap data and the remaining wellposedness
claims are separate tasks. The dissertation formalization is not complete.

Next implementation targets:

1. Prove cross-exponent compatibility and compact-time analyticity of the
   Hamiltonian-oriented ordinary flow for `1 < p ≤ 2`.
2. Use actual finite-gap density to identify that flow as the unique
   continuous extension of the proved classical finite-gap solution map.
3. Establish the corresponding physical identification for the renormalized
   flow and audit the remaining Chapter 4 wellposedness claims.

## Previous progress: classical uniqueness and finite-gap agreement

The actual finite-gap physical NLS flow now has a unique-existence theorem
in the class of smooth period-one spatial trajectories that are
differentiable in time in the uniform norm. Any such classical solution
with the same initial physical representative agrees with the constructed
Hamiltonian-oriented spectral flow at every real time and spatial point.

`ClassicalNLSDifferenceEstimate.lean` proves the cubic Lipschitz bound
`6 M²` on a complex disc. Periodic integration by parts cancels the linear
Schrödinger contribution, giving the actual difference-energy estimate
`|E′| ≤ 12 M² E`.

`ClassicalNLSUniqueness.lean` identifies normalized circle L² pairings with
the physical unit-interval integrals. Uniform-norm differentiability gives
the energy derivative through bounded inclusion into L², and the PDE gives
the derivative bound. Continuity supplies an amplitude bound on each
compact time interval. Grönwall, including time reflection, proves equality
at all real times from equality at any one time. No energy inequality,
global amplitude bound, or finite-gap assumption is part of the general
uniqueness hypothesis.

`SourceFiniteGapClassicalNLS.lean` realizes the actual finite-gap flow as a
uniform-norm differentiable continuous-function trajectory, verifies the
classical solution hypotheses, and proves agreement and unique existence.
The existence theorem constructs its atlas and Birkhoff data internally.

Public examples check unit-period mass normalization, the zero solution,
uniqueness forward and backward from a negative initial time, unique
finite-gap existence, and agreement with the physical flow at negative time.

Validation: the full build passes (6130 jobs), all public examples pass,
and the transitive axiom audit passes for 23250 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Agreement beyond finite-gap data and transfer of the nonextension theorem
with the Hamiltonian time orientation remain unfinished. The dissertation
formalization is not complete.

Next implementation targets:

1. Transfer nonextension through the proved finite-gap classical agreement
   and Hamiltonian time reversal. The underlying source obstruction already
   requires agreement only on finite-gap Hilbert representatives.
2. Extend classical solution agreement beyond finite-gap initial data.

## Previous progress: the pointwise physical NLS equation

The constructed Hamiltonian-oriented finite-gap trajectory now satisfies
`i*u_t = -u_xx + 2*|u|^2*u` at every real time and spatial point. Both
component time derivatives equal the classical NLS vector field, with the
original Poisson signs. A global scalar trajectory is constructed from any
real finite-gap Hilbert source without supplied spectral atlas data.

`PeriodOneFourierUniqueness.lean` proves that actual period-one Fourier
integrals determine a continuous periodic function everywhere. Even and
odd period-two coefficients reduce the claim to continuous-circle Fourier
uniqueness. An H¹ synthesis with the prescribed coefficients therefore
equals the actual continuous periodic physical function.

`SourceFiniteGapPointwiseNLS.lean` identifies the H¹ time derivative's
source coefficients with the previously proved NLS coefficients and then
identifies its synthesis with the classical spatial field. Bounded point
evaluation gives both actual pointwise time derivatives. The named
physical flow has the exact original initial representative, smooth
period-one spatial slices, and the conjugate-pair reality condition.
The scalar equation is proved both as a `HasDerivAt` statement and as
`i` times the actual time derivative. The final existence theorem
constructs the atlas and Birkhoff data internally.

Public examples check Fourier uniqueness at a negative mode, the exact
initial-time scalar equation, the second component's positive Poisson
sign at negative time, and the global scalar trajectory without supplied
spectral data.

Validation: the full build passes (6127 jobs), all public examples pass,
and the transitive axiom audit passes for 23191 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Classical solution uniqueness and solution-map agreement, followed by
transfer of the nonextension theorem with this time orientation, remain
unfinished. The dissertation formalization is not complete.

Next implementation targets:

1. Establish a suitable uniqueness theorem for periodic classical NLS
   solutions and identify the constructed finite-gap trajectory with them.
2. Extend the solution-map agreement to the required initial-data class.
3. Transfer the existing nonextension theorem through the proved agreement
   and the Hamiltonian time reversal.

## Previous progress: H¹ and pointwise time differentiability

The actual finite-gap Hamiltonian-oriented trajectory is now differentiable
in H¹, and both physical components are differentiable in time at every
spatial point. This closes the time-regularity gap left by the source-norm
and Fourier NLS equations.

`NormalizedWeightedSourceTopology.lean` provides a bounded complex-linear,
injective decoder for normalized weighted coordinates.
`NormalizedWeightedSourceClosing.lean` proves a uniform canonical-gap
closing criterion directly from the weighted periodic spectrum, including
complex sources.

`NormalizedWeightedClosingInverseSupport.lean` gives one common inverse
radius and cutoff: finite Fourier targets produce decoded sources whose
actual spectral gaps vanish beyond that same cutoff. Real targets also
give the exact unweighted adapted coordinates after decoding.
`NormalizedWeightedTruncation.lean` constructs bounded finite weighting
maps, proves exact decoding and reality preservation, and identifies the
actual finite weighted target of every sufficiently regular finite-gap
base point.

`SourceFiniteGapWeightedLift.lean` constructs a complex analytic weighted
lift near each weighted finite-gap base point. On nearby real sources with
a common closed-gap tail, decoding the lift is the identity. The proof
uses the original closing map's lower distance bound. Differentiable source
curves therefore have local differentiable weighted lifts.

`SourceFiniteGapSobolevTime.lean` identifies those lifts with the canonical
H¹ representatives. Action conservation supplies one closed-gap tail for
the full finite-gap trajectory. Bounded synthesis and evaluation then give
pointwise time differentiability of both physical components.

Public examples verify a negative low Fourier mode, the excluded cutoff
boundary, pointwise time differentiability, and compatibility of the H¹
derivative with the established physical NLS velocity in source norm.

Validation: the full build passes (6125 jobs), all public examples pass,
and the transitive axiom audit passes for 23170 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Identifying the pointwise time derivatives with the classical NLS spatial
field, classical solution-map agreement, and the nonextension transfer
remain unfinished. The dissertation formalization is not complete.

Next implementation targets:

1. Identify the bounded physical synthesis of the H¹ time derivative with
   the classical NLS vector field using the proved Fourier coefficients.
2. State and prove the classical pointwise scalar NLS equation.
3. Prove classical solution-map agreement and transfer nonextension with
   the established Hamiltonian time orientation.

## Previous progress: uniform finite-gap closing coordinates

The distant closed-gap equations now hold on open neighborhoods with a
single cutoff. This removes the pointwise choice of cutoff from the
adapted-coordinate regularity route.

`SourceClosedGapCenter.lean` now proves that every nearby real source has
both center closing equations whenever its corresponding distant gap is
closed. The proof combines uniform determinant bounds, root counts, and
canonical endpoint labeling. The original pointwise theorem is retained
as a corollary.

`SourceFiniteGapAdaptedCoordinates.lean` now proves a uniform truncation
identity: nearby real sources whose gaps vanish beyond a common cutoff
have adapted coordinates equal to the same finite Fourier truncation.
The identity holds at every sufficiently large cutoff.

A public example applies the result to a continuous family at exponent 3
with a common closed-gap tail, using a single local cutoff for both
coefficient components.

Validation: the full build passes (6119 jobs), all public examples pass,
and the transitive axiom audit passes for 23115 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

The full source-norm and Fourier NLS equations remain established.
Recovering the trajectory in stronger spatial norms through the weighted
inverse, pointwise time differentiation, and classical solution-map
agreement remain unfinished.

Next implementation targets:

1. Combine uniform spectral closing control with weighted inverse
   uniqueness to recover finite-gap trajectories in stronger spatial norms.
2. Prove pointwise time differentiation and the classical NLS equation.
3. Prove classical solution-map agreement and transfer nonextension.

## Previous progress: the physical NLS field and Fourier equation

The finite-gap trajectory derivative in the original Hilbert source norm
is now the Fourier realization of the classical physical NLS field. Every
signed Fourier mode satisfies the scalar equation with normalization
`i*u_t = -u_xx + 2*|u|^2*u`. Pointwise time differentiation of the physical
trajectory remains a separate regularity step.

`PeriodOneSobolevEnergyVariation.lean` identifies the H¹ energy with the
third classical hierarchy Hamiltonian whenever the physical representatives
are smooth. Complex variations in either Sobolev component give integration
against the previously proved classical spatial energy gradients.

`PhysicalEnergyCotangent.lean` tests these variations against every signed
Fourier mode. The two Hilbert cotangent coefficient sequences are precisely
the reflected Fourier coefficients of the spatial gradients. Applying the
original source Poisson map reverses the indices again and gives exactly
the Fourier coefficients of the classical NLS field, with signs `(-i,+i)`.

`SourceFiniteGapPhysicalNLSCoefficients.lean` realizes that field in the
original Hilbert source space and proves that the constructor recovers
every actual physical Fourier integral. Any Hilbert cotangent restricting
to the physical H¹ energy derivative has this same Hamiltonian direction.
The field preserves the original conjugate-pair real form.

`SourceFiniteGapPhysicalNLSODE.lean` applies the identification to the
constructed finite-gap spectral flow at every time. It proves the full
Hilbert-norm ODE, both component coefficient equations, and the scalar
Fourier form of defocusing NLS. The energy cotangent and inverse Jacobian
no longer occur in the physical velocity statement.

Public examples check the cubic normalization and both Poisson signs for
constant fields, conjugate Fourier reality, the initial source-norm
velocity, and the scalar equation at negative frequency indices.

Validation: the full build passes (6119 jobs), all public examples pass,
and the transitive axiom audit passes for 23109 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Spatial smoothness at each time and source-norm time differentiability
are established. Passing from them to pointwise time differentiation
requires stronger control of the trajectory in spatial norms; that and
classical solution-map agreement remain open. The dissertation
formalization remains unfinished.

Next implementation targets:

1. Establish stronger time regularity of the physical finite-gap trajectory
   in spatial norms sufficient for pointwise evaluation.
2. Upgrade the proved full source-norm and Fourier NLS equations to the
   classical pointwise time equation.
3. Prove classical solution-map agreement and transfer the nonextension
   theorem with the established Hamiltonian time orientation.

## Previous progress: the physical energy Hamiltonian ODE

The actual physical NLS energy now has full complex H¹ differential
`sum_n ordinaryFrequency_n * dI_n` at every real finite-gap source. Its
bounded Hilbert cotangent generates the proved source trajectory through
the original Poisson Hamiltonian direction, at every real time.

`SourceSobolevHamiltonianDifferential.lean` transfers real-form analytic
uniqueness through the existing normalized H¹ coordinate equivalence.
The physical correction and the FL⁴ renormalized Hamiltonian agree as
complex germs near every real H¹ source. Their full complex derivatives
therefore agree on arbitrary H¹ directions, without a finite-gap premise.

`SourceMassActionDifferential.lean` promotes the real action–mass trace to
a complex analytic identity. Bounded ℓ¹ summation gives the mass derivative
as the convergent sum of the original action derivatives. At finite gap
this is a finite sum. Sobolev mass is identified with the original Hilbert
mass under the coefficient inclusion, and inherits the derivative formula.

`SourcePhysicalEnergyActionDifferential.lean` transfers the finite FL⁴
renormalized Hamiltonian derivative to the original Hilbert actions and
frequencies. It combines this with the kinetic-weighted action derivative
and the derivative of twice the mass squared. The coefficient is exactly
`(2πn)² + renormalizedFrequency_n + 4*mass`, the existing ordinary NLS
frequency. A public theorem supplies the finite bounded Hilbert cotangent
whose restriction is the full physical energy derivative.

`SourcePhysicalEnergyHamiltonianODE.lean` identifies the existing finite-gap
trajectory velocity with the Poisson Hamiltonian direction of that actual
physical energy cotangent at each time. One initial finite gap cutoff
continues to suffice, by action conservation. This uses the previously
established Hamiltonian time orientation.

Public examples check the radial mass normalization, the correction
derivative in arbitrary complex H¹ directions, actual complex-line energy
derivatives, and the physical-energy Hamiltonian ODE at initial time.

Validation: the full build passes (6115 jobs), all public examples pass,
and the transitive axiom audit passes for 23083 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

The remaining classical PDE bridge is to identify this physical-energy
cotangent with the smooth spatial gradient and prove the resulting
pointwise NLS equation for the trajectory. The dissertation formalization
remains unfinished.

## Previous progress: finite-gap energy differentials

The full complex action differential now vanishes at every real closed
gap, including directions that open that gap. At a finite-gap source,
one finite set therefore supports the action-sequence differential for
all source directions. A finite chain rule applies to every differentiable
function of the Banach action sequence.

`SourceActionFiniteGapDifferential.lean` proves these statements using
the actual rectangular action-radius identity. The closed-gap and
finite-support results construct their Birkhoff data internally and hold
at every finite source exponent above one.

`SourceSobolevActionDifferential.lean` differentiates the actual analytic
ℓ¹ sequence of kinetic-weighted actions by bounded coordinate evaluation,
and its scalar sum by bounded summation. At finite-gap H¹ sources the
full derivative is the finite sum of `(2πn)² dI_n`. It is the restriction
of an explicit bounded Hilbert source functional, despite the unbounded
kinetic weights. The proof differentiates the Banach sequence map, so it
does not assume that nearby sources have the same finite gap support.

`SourceRenormalizedHamiltonianDifferential.lean` constructs the analytic
action Hamiltonian, identifies its source germ by real-form uniqueness,
and combines the finite chain rule with the proved frequency gradient.
The actual FL⁴ renormalized Hamiltonian consequently has full differential
`sum_n frequency_n * dI_n` at finite-gap sources. The statement assumes
neither an auxiliary action Hamiltonian nor an auxiliary Birkhoff family.

Public examples check arbitrary complex directions at a closed gap, the
zero-source weighted cotangent, the actual H¹ derivative at canonical
smooth finite-gap representatives, and the actual renormalized Hamiltonian
derivative as a finite frequency-weighted cotangent.

Validation: the full build passes (6111 jobs), all public examples pass,
and the transitive axiom audit passes for 23070 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

The remaining energy bridge is to differentiate the real H¹ identity
between the physical correction and the FL⁴ renormalized Hamiltonian,
combine it with the mass correction, and identify the resulting field
with the classical PDE. The dissertation formalization remains unfinished.

## Previous progress: the finite-gap action Hamiltonian ODE

The time derivative of every Hilbert finite-gap Hamiltonian-oriented
ordinary spectral trajectory is now identified with a finite sum of the
original source action Hamiltonian fields, weighted by the actual ordinary
frequencies. The equation is autonomous: the frequencies may be evaluated
at the current source. The trajectory remains finite-gap for all real time.

`SourceFiniteActionHamiltonian.lean` identifies the actual complex Birkhoff
differential with the rectangular Jacobian followed by the fixed complex
coordinate change, and proves its injectivity at every real source. It
then computes the differential of each finite frequency-weighted action
field sum as the full finite phase velocity. Any two finite cutoffs
containing all active coordinates give the same original source field.

`SourceFiniteGapHamiltonianODE.lean` compares that differential with the
proved full-norm trajectory derivative. Injectivity identifies the source
velocities, removing the inverse Jacobian from the ODE statement. The
existing frequency-invariance theorem gives the autonomous form. The
initial coordinate cutoff contains the active coordinates for all time,
and preservation of every action shows that finite-gap sources remain
finite-gap. A public theorem supplies one finite cutoff for the entire
Hilbert finite-gap trajectory.

`Dynamics/FiniteHamiltonianPhaseDerivative.lean` now also exposes the
coordinate evaluations of the finite phase velocity. Public examples
prove vanishing of every finite action-field combination at the zero
source, invariance under adding inactive cutoff indices, and simultaneous
finite-gap preservation and the autonomous ODE at every real time.

Validation: the full build passes (6108 jobs), all public examples pass,
and the transitive axiom audit passes for 23058 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This uses the Hamiltonian time orientation established in the previous
milestone. Identifying the weighted action-field sum with the physical NLS
energy field is the remaining bridge to the classical PDE. The dissertation
formalization remains unfinished.

## Previous progress: Hamiltonian time orientation and finite-gap time derivatives

Checking the classical PDE bridge exposed a sign inconsistency in the
printed equation (4.14), verified directly on PDF page 98. With the stated
coordinates `z = (x-i*y)/sqrt(2)` and the original source Poisson bracket,
the action Hamiltonian rotation `(-y,x)` gives `z_t = -i*z`, `w_t = i*w`.
Equation (4.14) instead prints the opposite phases. Earlier Section 22
flow definitions retain that literal printed convention. The new
`hamiltonianOrdinarySourceFlow` explicitly reverses their time parameter
and is the convention to use for the classical PDE bridge.

`SourceComplexActionHamiltonian.lean` proves the actual complex-coordinate
velocity of every original source action Hamiltonian, including collapsed
gaps. The result follows from the proved canonical rectangular brackets
and the exact complex change of coordinates, so the signs are derived
from the existing source Poisson structure.

`Dynamics/HamiltonianPhaseFlow.lean` defines the time-reversed coordinate
flow, proves both scalar time derivatives and the group law, and proves
that the printed positive first phase cannot have the Hamiltonian velocity
when its frequency and amplitude are nonzero.
`Dynamics/FiniteHamiltonianPhaseDerivative.lean` differentiates the full
sequence-valued trajectory for finite Birkhoff support. The frequency
sequence may be unbounded; only the active coordinate set must be finite.

`SourceHamiltonianOrdinaryFlow.lean` lifts that full-norm derivative through
the actual inverse real Birkhoff Jacobian. Every finite-gap source in
`1 < p <= 2` consequently has a differentiable trajectory in the original
source norm, with an explicit derivative formula. The Hamiltonian-oriented
ordinary flow also has the global group law, joint continuity, analytic
initial-data time maps, and conservation of every action and physical mass.

Public examples check the full Hilbert-norm velocity of a unit mode,
rejection of the opposite printed velocity, the sign derived from the
actual action Hamiltonian, and finite-gap source-norm differentiability.

Validation: the full build passes (6106 jobs), all public examples pass,
and the transitive axiom audit passes for 23038 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Identification of the inverse-Jacobian velocity with the physical NLS
energy field remains open. The classical PDE agreement and the overall
dissertation formalization remain unfinished.

## Previous progress: physical NLS energy variations and vector field

The first variations of the actual physical third hierarchy Hamiltonian
are now proved for arbitrary smooth period-one complex fields and smooth
periodic variation directions. Their gradients are
`(-b_xx + 2*a*b^2, -a_xx + 2*a^2*b)`. Applying the original source Poisson
signs `(-i,+i)` gives a smooth periodic physical vector field. On the real
form `b = conjugate(a)`, it is exactly the scalar defocusing NLS equation
`i*u_t = -u_xx + 2*|u|^2*u`.

`ClassicalNLSEnergyVariation.lean` proves the exact quadratic expansion of
the physical energy when the first field is varied by a complex parameter.
Periodic integration by parts removes derivatives of the variation. This
gives an actual complex `HasDerivAt` theorem for the original hierarchy
Hamiltonian. Symmetry of the third Hamiltonian supplies the second-field
variation with the correct cross-component gradient.

`ClassicalNLSVectorField.lean` defines the physical Hamiltonian field from
these gradients and proves smoothness, periodicity, conjugate-pair reality,
and the scalar NLS normalization. A trajectory whose time derivative is
this field satisfies the conventional classical PDE pointwise.

`SourceFiniteGapNLSVariation.lean` proves that the existing smooth Fourier
representatives of actual finite-gap sources preserve the original real
form at every physical point. It specializes both energy variations and
the smooth periodic real NLS field to those representatives, at every
finite source exponent greater than one. Finite Fourier support is not
assumed. Public examples check the actual constant-potential energy
expansion, its complex derivative, both Poisson signs, and the scalar
PDE identity for finite-gap data.

Validation: the full build passes (6102 jobs), all public examples pass,
and the transitive axiom audit passes for 23010 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This identifies the physical Hamiltonian field. Proving that it equals
the time derivative of the constructed spectral flow, and establishing
agreement with classical PDE solutions, remain open. The dissertation
remains unfinished.

## Previous progress: ordinary source nonextension in weaker norms

The source-trajectory nonextension statement of Corollary 22.2(iii) is
now proved for the constructed ordinary spectral flow. For every finite
`q >= p >= 2`, every `T > 0`, and every initial source outside the embedded
Hilbert locus, a map agreeing with the Hilbert flow cannot be continuous
into `C([-T,T], source q)` at that source. This includes strictly weaker
target norms. At `p = 2` the excluded locus is empty.

`SourceFiniteGapOrdinaryCompatibility.lean` identifies the ordinary
frequency of each finite-gap source with that of its coefficient-preserving
Hilbert model. Compatibility of the actual complex Birkhoff maps then
identifies the first coordinate of the included Hilbert trajectory in any
finite target exponent at least two.

`SourceOrdinarySourceObstruction.lean` proves that every nonzero real source
has a nonzero first complex Birkhoff component. Evaluating this component
is continuous on the target space and hence on compact-time paths. The
previous scalar obstruction therefore rules out continuous dependence of
source paths at non-Hilbert data.
Agreement only on finite-gap Hilbert representatives already suffices.

`SourceOrdinaryCorollary22_2III.lean` gives the result on the full interval
`[-T,T]`, constructs the source and target atlases, and packages analytic
Hilbert trajectories with their nonextension property. A separate theorem
rules out a globally continuous extension when a non-Hilbert source is
given. Public examples cover `p = q = 3`, `p = 3, q = 4`, and the equivalent
hypothesis of nonsummable squared Fourier coefficients.

Validation: the full build passes (6099 jobs), all public examples pass,
and the transitive axiom audit passes for 22987 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Agreement of the constructed spectral flows with classical PDE solutions
remains open. The dissertation remains unfinished.

## Previous progress: ordinary coordinate nonextension outside ell²

The coordinate nonextension result of Theorem 22.1(iii) is now proved.
At a point of the actual Birkhoff image outside `ell^2`, an ordinary NLS
coordinate with nonzero initial amplitude has no continuous extension
into `C([-T,T], complex)` for any `T > 0`. Both complex components are
covered. Agreement with the original dynamics on actual finite-gap data
alone is already enough to force the obstruction.

`Dynamics/UnboundedPhaseObstruction.lean` proves a general uniform-trajectory
obstruction. Convergent nonzero amplitudes with frequencies tending to
positive infinity cannot give convergent continuous paths. At times
`pi/frequency` tending to zero the phase equals minus one, contradicting
the initial value of any continuous limiting path. The theorem works
for arbitrary nontrivial filters, not just one chosen sequence.

`SourceFiniteGapMassDivergence.lean` characterizes the embedded Hilbert
source locus by square summability of the first Fourier component.
It identifies the finite-gap physical mass with the Hilbert model's
coefficient energy and bounds every finite partial energy sum by that
mass. Consequently every convergent finite-gap approximation outside the
Hilbert locus has mass tending to positive infinity. The existing finite-gap
density theorem supplies such approximating sequences.

`SourceFiniteGapOrdinaryTrajectory.lean` restores the physical mass in
the renormalized frequencies and identifies the result with the original
finite-gap Hamiltonian frequency. It defines both scalar coordinate paths
and proves agreement with the previously constructed ordinary flow in
`p <= 2`. Each fixed ordinary frequency diverges along the non-Hilbert
approximations, while its renormalized part converges.

`SourceOrdinaryCoordinateObstruction.lean` applies the scalar obstruction
to the actual Birkhoff amplitudes. Conjugation gives the opposite-sign
second coordinate. The actual Birkhoff image homeomorphism transfers the
result from source parameters to coordinate initial data.
`SourceComplexBirkhoffExponent.lean` proves compatibility of the complex
coordinate map across exponents and square summability of coordinates for
embedded Hilbert sources. `SourceOrdinaryTheorem22_1III.lean` states the
nonextension results on the Birkhoff image and the full interval `[-T,T]`,
with failure of square summability as the explicit initial-coordinate
hypothesis. For real data the second coordinate is conjugate to the first,
so this hypothesis is exactly exclusion from the complex `ell^2` pair space.

Public examples check an explicit sequence of diverging frequencies,
existence of actual finite-gap approximations with divergent mass,
agreement with the earlier ordinary flow, and both forms of the
coordinate obstruction, including the negative phase on `[-T,T]`.

Validation: the full build passes (6096 jobs), all public examples pass,
and the transitive axiom audit passes for 22980 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

The source-trajectory nonextension statement in the weaker target norms
of Corollary 22.2(iii), and agreement of the spectral flows with classical
PDE solutions, remain open. The dissertation remains unfinished.

## Previous progress: ordinary NLS mass correction and global analytic flows

For `1 < p <= 2`, the ordinary NLS spectral flow now forms a global
continuous group on the original real source space. Its complete
trajectory depends real analytically on the initial source in the uniform
norm on every compact time interval. Each fixed-time map and its
negative-time inverse are real analytic. This supplies the ordinary-flow
construction in Theorem 22.1(ii) and Corollary 22.2(i).

`SourceOrdinaryMass.lean` pulls the physical Hilbert mass back through the
bounded exponent inclusion. The resulting complex mass is entire, and
its real restriction equals the literal absolutely convergent sum of the
original spectral actions. This uses the proved Hilbert trace formula and
compatibility of the original actions across exponents. Thus the mass
correction has its physical normalization and is preserved by any map
preserving the original actions.

`SourceOrdinaryPhaseTrajectory.lean` adds four times this mass to the
renormalized frequencies. `SourceOrdinaryFlow.lean` lifts the opposite
phase rotations through the actual global Birkhoff inverse, proving the
coordinate identity, action and mass conservation, frequency invariance,
the group law, joint continuity, and inverse time homeomorphisms.
`SourceOrdinaryFlowTrajectories.lean` supplies complete compact-time paths
and continuous dependence in their uniform norms.

`SourceOrdinaryPhaseAnalytic.lean` adds the entire complex mass as a
constant bounded frequency symbol. One complex neighborhood supports
analytic extensions of all compact-time coordinate trajectories.
`SourceOrdinarySourceTrajectoryAnalytic.lean` applies the function-space
inverse theorem to the actual Birkhoff map and projects the analytic lift
back to the original real source space. `SourceOrdinaryFlowAnalytic.lean`
proves analytic time maps, analytic inverses, and analytic trajectory
parametrization by initial Birkhoff coordinates.

`SourceOrdinaryMassShift.lean` proves the exact scalar phase factors
`exp(+4it H1)` and `exp(-4it H1)` relative to the renormalized coordinates.
`SourceOrdinaryFlowExistence.lean` constructs the spectral atlas and
Birkhoff family with the global analytic trajectory and conservation laws.
Public examples check absolute convergence of the action sum, both mass
phase signs, mass conservation, time reversal, full trajectory derivatives,
analytic inverse maps, and the initial value of the compact-time path.

Validation: the full build passes (6090 jobs), all public examples pass,
and the transitive axiom audit passes for 22941 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Agreement with classical PDE solutions and failure of continuous extension
outside `ell^2` for `p > 2` remain open. The ordinary and renormalized flows
constructed here are spectral flows; the dissertation remains unfinished.

## Previous progress: local and small-data global analytic source flows

At every finite `p > 1`, including `p > 2`, the renormalized spectral flow
now exists locally around every real source and globally on an open
invariant neighborhood of zero. Nearby initial sources share a positive
time interval. The complete source trajectory depends real analytically
on the initial source in the uniform norm on each admissible compact
interval. This supplies the spectral-flow construction in Corollary 22.2(ii).

`SourceBirkhoffImageInverse.lean` identifies the source with the actual open
Birkhoff image and proves analyticity of its inverse there. It also proves
that the original Birkhoff maps send zero to zero. `SourceRenormalizedImageFlow.lean`
constructs the flow with an explicit image-domain condition, proves joint
continuity, its exact coordinates, preservation of actions and frequencies,
the restart-domain identity, and time addition. In the globally surjective
range it agrees with the previously constructed source flow.

`SourceRenormalizedLocalFlow.lean` gives a common positive existence interval
for a neighborhood of every source and proves reversibility. A sufficiently
small ball in complex Birkhoff coordinates remains admissible for all time:
phase rotation preserves its norm, and the bounded real decoder keeps it
inside the actual image. Its source preimage is open, invariant, contains
zero, and contains a source norm ball of positive radius.

`SourceRenormalizedImageTrajectories.lean` proves that the initial sources
admissible on a compact interval form an open set. The full trajectory is
continuous there; the function-space inverse theorem for the actual
Birkhoff map upgrades this lift to a real analytic trajectory map.
`SourceRenormalizedLocalExistence.lean` packages local analytic existence
and small-data global analytic dynamics, with the actual spectral atlas
and Birkhoff family constructed rather than assumed.

Public examples cover negative-time reversal with its domain condition,
the uniform-norm trajectory derivative, evaluation at time zero, agreement
with the previous global flow, a local analytic trajectory at `p = 4`,
and all-time existence from positive coordinate and source norm bounds.

Validation: the full build passes (6081 jobs), all public examples pass,
and the transitive axiom audit passes for 22846 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

The ordinary NLS mass shift, its discontinuity outside `ell^2`, and agreement
with classical PDE solutions remain open Section 22 work. These results
concern the constructed renormalized spectral flow; the dissertation
remains unfinished.

## Previous progress: analytic compact-time source trajectories

For every `1 < p <= 2`, the actual renormalized source trajectory now depends
real analytically on its initial source as a map into `C([-T,T], E)` for
every compact time interval. This closes the source-trajectory analyticity
gap from the previous milestone. The target is the original closed real
source space with its uniform trajectory norm.

`ComplexAnalysis/ContinuousMapAnalytic.lean` proves that norm continuity
and analytic point evaluations imply analyticity into a compact continuous
function space. Cauchy's integral formula proves the complex-line case;
the existing Banach analytic-line criterion supplies the general result.
`ContinuousMapSuperposition.lean` then makes pointwise composition analytic
on the open set of paths whose ranges lie inside an analytic map's domain.
Its derivative is exactly pointwise application of the original derivative.

`ContinuousMapAnalyticInverse.lean` proves that pointwise invertible
derivatives along a compact path give an invertible derivative on the
whole trajectory space. Continuity of operator inversion supplies the
continuous inverse path. The analytic inverse theorem yields a local
inverse in the uniform norm, and upgrades a continuous real-parameter lift
with analytic image to an analytic lift.

`SourceRenormalizedSourceTrajectoryAnalytic.lean` applies these results to
the actual Birkhoff map along the previously constructed source flow.
Its image is exactly the analytic rectangular coordinate trajectory.
The actual invertible source Jacobians supply the function-space inverse,
and the bounded real-form projection retains the original trajectory.
`SourceRenormalizedAnalyticTrajectoriesExistence.lean` constructs the
spectral data with global continuous dynamics, the group law, action
preservation, and analytic compact-time source dependence.

Public examples check analytic pointwise exponentiation, the literal
composition values, its full trajectory derivative, a local analytic
inverse around every compact exponential path, and the actual source
trajectory's analyticity, derivative, and Birkhoff image identity.

Validation: the full build passes (6076 jobs), all public examples pass,
and the transitive axiom audit passes for 22792 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 22 work includes the local source flow and small-data
global flow for `p > 2`, the ordinary NLS mass shift and its discontinuity
outside `ell^2`, and agreement with classical NLS solutions. This milestone
establishes analytic dependence for the constructed renormalized spectral
flow; the dissertation remains unfinished.

## Previous progress: analytic compact-time coordinate trajectories and fixed-time source flows

The actual renormalized coordinate trajectories now depend real analytically
on the initial source in `C([-T,T], ell^p × ell^p)` for every finite `p > 1`.
There is a complex analytic extension on one common open source neighborhood
containing the real locus, valid for every compact time interval. For
`1 < p <= 2`, each fixed-time source flow and its negative-time inverse are
real analytic, strengthening the previous homeomorphisms to bi-analytic maps.

`SequenceSpaces/AnalyticPhaseTrajectory.lean` separates an arbitrary fixed
real frequency sequence from a bounded complex correction. The fixed phase
rotation acts bounded linearly on continuous trajectories, even with
unbounded quadratic frequencies. The correction exponential is constructed
in the Banach algebra of continuous bounded-symbol families. Its bounded
bilinear action on the initial amplitude proves entire dependence in the
uniform trajectory norm. Coordinate evaluation gives the literal scalar
exponential formula.

`Dynamics/AnalyticComplexPhaseTrajectory.lean` assembles the two opposite
phase signs. `SourceRenormalizedPhaseAnalytic.lean` inserts the actual
analytic moment-sum correction and original complex Birkhoff coordinates.
Its extension agrees exactly with the previously constructed real
trajectories, rather than introducing a different dynamics.

`SourceRenormalizedFlowAnalytic.lean` evaluates these trajectories at any
fixed real time and composes with the actual analytic Birkhoff inverse.
It also proves compact-time analytic dependence on real Birkhoff initial
coordinates globally for `p <= 2`, and locally on the actual coordinate
image at every finite `p > 1`. `SourceRenormalizedAnalyticExistence.lean`
constructs the spectral atlas and Birkhoff family with these properties.

Public examples check the unbounded quadratic base at `p = 4`, complex
frequency corrections with both signs, zero amplitudes, analytic dependence
in the full trajectory space, analytic inverse flow maps, and local
coordinate parametrization without global-surjectivity assumptions.

Validation: the full build passes (6070 jobs), all public examples pass,
and the transitive axiom audit passes for 22764 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 22 work includes analytic dependence of the complete
source-valued trajectory in `C([-T,T], E)`, the local source flow and
small-data global flow for `p > 2`, the ordinary NLS mass shift and its
discontinuity outside `ell^2`, and agreement with classical NLS solutions.
Fixed-time analyticity alone does not close the source-trajectory gap.
The dissertation remains unfinished.

## Previous progress: continuous renormalized coordinate and source flows

Section 22 now has actual global coordinate trajectories for every finite
source exponent `p > 1`, with joint time/source continuity in the sequence
norm. For `1 < p <= 2`, the actual global Birkhoff inverse lifts them to a
continuous group on the original real source space. Every fixed-time map
is a homeomorphism with negative time as its inverse, and the original
spectral actions remain constant along the flow.

`SequenceSpaces/PhaseRotation.lean` constructs simultaneous unit phase
rotations for arbitrary real frequency sequences. Exact preservation of
the finite-tail norm proves continuity without a bounded-frequency
assumption, so the physical quadratic term `(2*pi*n)^2` is included.
`Dynamics/ComplexPhaseFlow.lean` uses opposite signs for the two components,
preserves their products and norms, and retains same-index conjugate reality.

The complex/rectangular coordinate modules implement exactly
`z=(x-i*y)/sqrt(2)` and `w=(x+i*y)/sqrt(2)`, with continuous inverse maps.
`SourceComplexBirkhoffMap.lean` identifies their products with the original
spectral actions. `SourceRenormalizedPhaseTrajectory.lean` inserts the actual
moment-sum frequency, proves the literal formulas in (4.14), and establishes
joint time/source continuity at all finite exponents above one.

`SourceRenormalizedFlow.lean` lifts these trajectories through the actual
Birkhoff inverse for `p <= 2`. Action preservation gives invariance of the
actual frequencies and hence the nonlinear group law. The compact-time
trajectory module proves continuous dependence in `C([-T,T], E)` and uniform
convergence of source trajectories for convergent initial data.
`SourceRenormalizedFlowExistence.lean` constructs the moment atlas and
Birkhoff data together with the resulting continuous flow statements.

Public examples check unbounded quadratic frequencies, the fixed zero mode,
closed coordinates, exact complex action preservation, coordinate decoding,
the physical frequency signs, nonlinear backward-time inversion, and uniform
convergence on compact time intervals.

Validation: the full build passes (6065 jobs), all public examples pass,
and the transitive axiom audit passes for 22679 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 22 work includes analytic dependence in compact-time
trajectory spaces, the local source flow and small-data global flow for
`p > 2`, the ordinary NLS mass shift and its discontinuity outside `ell^2`,
and the required agreement with classical NLS solutions. This milestone
establishes continuous spectral dynamics, not all of Theorem 22.1 or
Corollary 22.2. The dissertation remains unfinished.

## Previous progress: H¹ finite-gap density and physical Hamiltonian identification

The physical H¹ Hamiltonian correction now equals the FL⁴ cubic-moment
extension at every real H¹ source. This includes the literal absolutely
convergent subtraction `sum_n (2*pi*n)^2 I_n`. The physical correction is
real and nonpositive, and vanishes exactly at the zero source.

The missing approximation argument is proved in the H¹ topology.
`NormalizedWeightedPeriodOne.lean` embeds normalized source coordinates
isometrically into the weighted physical space for every spectral weight.
The normalized closing map, derivative estimates, analytic inverse,
reality preservation, and truncated targets construct nearby real sources
with all sufficiently distant actual closing equations zero.
`NormalizedWeightedSource.lean` recovers the unchanged original physical
operator and proves that these sources satisfy the existing canonical
spectral finite-gap definition.

`SourceSobolevNormalizedCoordinates.lean` supplies a continuous linear
equivalence between H¹ sources and coordinates weighted by `1+2*|n|`,
with exact physical-realization and reality compatibility.
`SourceSobolevFiniteGapDensity.lean` proves actual finite-gap density in
H¹, approximation preserving any open condition, and passage of continuous
identities from finite-gap sources to all real H¹ sources.

`SourceSobolevHamiltonianIdentification.lean` uses this density, continuity
of the physical correction, analyticity of the cubic-moment sum, and
finite-gap exponent compatibility to prove the full physical identity.
It constructs an actual primitive atlas satisfying the identity, and
transfers the sign and zero-rigidity statements to the physical H¹ expression.

Public examples check unit-weight compatibility, negative-frequency
normalization, spectral finite-gap approximation in H¹, simultaneous
control of the physical correction, the literal Hamiltonian series identity,
and sign and rigidity without a finite-gap hypothesis.

Validation: the full build passes (6056 jobs), all public examples pass,
and the transitive axiom audit passes for 22568 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

This closes the physical H¹ identification gap recorded for Section 21.
Next is Section 22: the renormalized NLS flow in complex Birkhoff coordinates,
its continuity and wellposedness, and the source-space flow obtained through
the actual Birkhoff map. The dissertation is not yet fully formalized.

## Previous progress: analytic weighted spectral sum and physical H¹ correction

The literal weighted spectral sum `sum_n (2*pi*n)^2 I_n` is now absolutely
convergent at every real H¹ source and analytic on a complex neighborhood
of each such source. The weighted action sequence itself takes values
analytically in `ell^1` on one open complex H¹ domain containing the entire
real source locus.

`CanonicalWeightedGapSummability.lean` identifies distant canonical
squared gaps with the intrinsic contour invariants, independently of root
ordering and including collapsed gaps, and transports the existing
weighted power-tail estimates. `SourceSobolevEmbedding.lean` embeds the
original H¹ source continuously into both its unweighted source and its
weighted period-two physical realization, with exact coefficient and
operator compatibility.

`SourceSobolevGapBound.lean` combines the weighted tail estimate with a
bound on the finite central block to obtain locally bounded `ell^1`
realizations of the weighted squared gaps. This part holds near every
complex H¹ source. `SourceNormalizedActionUniformBound.lean` bounds all
normalized action factors on a common neighborhood of each real Hilbert
source. `SourceSobolevActionBound.lean` then proves the full weighted action
bound by the exact squared-gap factorization and the physical kinetic weight.

`SourceSobolevActionAnalytic.lean` assembles the actual scalar actions into
the analytic `ell^1` sequence and sums it by a bounded linear map. It also
proves analyticity of the literal infinite series near every real H¹ source.
`SourceSobolevPhysicalCorrection.lean` combines this with the physical
energy and mass to define the full correction
`H3 - 2 H1^2 - sum_n (2*pi*n)^2 I_n`, proves its analyticity and H¹
continuity near real sources, and identifies it with the existing physical
finite-gap correction for Hilbert sources.

Public examples check absolute summability without finite-gap assumptions,
the signed kinetic normalization, convergence of the literal spectral sum
under arbitrary H¹ perturbations toward a real source, continuity of the
physical correction, and exact finite-gap calibration.

Validation: the full build passes (6044 jobs), all public examples pass,
and the transitive axiom audit passes for 22466 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 21 work: prove that this physical H¹ correction agrees
with the cubic-moment extension for all real H¹ sources. The continuity
prerequisites are now established; Sobolev-controlled finite-gap approximation
or a direct physical trace argument is still needed. Unweighted FL⁴ density
and smoothness of individual finite-gap sources do not supply that argument.
Section 22 remains ahead, and the dissertation is unfinished.

## Previous progress: physical period-one H¹ mass and NLS energy

The physical period-one mass and NLS energy are now complex analytic on the
entire product H¹ coefficient space. Their definitions equal the actual
unit-interval integrals `int a*b` and `int a'*b' + a^2*b^2`, where the
classical derivatives are square integrable. Finite Fourier truncations
converge in physical energy.

`SobolevPeriodDoubling.lean` inserts original frequencies at the even
period-two indices as a bounded linear map on the weighted Hilbert domain.
`PeriodOneSobolev.lean` identifies its continuous representative with the
period-one Fourier series, proves absolute continuity and square-integrable
classical derivatives, and recovers the exact multiplier `2*pi*i*n`.
The unit-interval bilinear Parseval theorem now works for arbitrary L²
inputs, allowing its use on these derivatives without extra smoothness.

`PeriodOneSobolevHamiltonian.lean` constructs the mass, kinetic energy,
quartic interaction, and full NLS energy, proves the physical integral
identities, and establishes analyticity and continuity on the full H¹
product. `SourceFiniteGapSobolevHamiltonian.lean` embeds each finite-gap
source with unchanged coefficients and identifies the new mass and energy
with the first and third physical hierarchy Hamiltonians at every finite
source exponent above one.

Public examples check a negative frequency's derivative, the `(2*pi*n)^2`
kinetic normalization of opposite signed modes, the nonzero quartic term
for constant fields, full-domain analyticity, and finite-gap calibration.

Validation: the full build passes (6037 jobs), all public examples pass,
and the transitive axiom audit passes for 22412 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 21 work: convergence and continuity of the weighted
spectral action subtraction, followed by the physical/cubic-moment
identification using Sobolev-controlled finite-gap approximation or another
physical trace argument. Fourier truncation convergence of the physical
energy does not supply spectral finite-gap approximation. The existing
FL⁴ density theorem and smoothness of individual finite-gap sources do not
by themselves close this gap. Section 22 remains ahead, and the dissertation
is unfinished.

## Previous progress: Hamiltonian gradient, Hessian, and strict concavity

The analytic action Hamiltonian now has the actual renormalized frequency
as its `ell^2` gradient at every real `FL^4` source. The full differential
is the absolutely convergent pairing
`D H*(I(phi))[J] = sum_n omega*_n(phi) J_n`, for every complex `ell^2`
direction, without a finite-gap or finite-support restriction.

Its Hessian at zero is the full complex bilinear form
`D^2 H*(0)[v,w] = -2 sum_n v_n w_n`.
There is a positive-radius complex action ball on which, for every real
`ell^2` direction `J`, the real part of the Hessian satisfies
`Re D^2 H*(I)[J,J] <= -norm(J)^2`. In particular, every nonzero real
direction has strictly negative second variation. The earlier analytic
extension, nonnegative-domain sign, and exact zero criterion are retained.

`SourceHilbertActionReductionWeighted.lean` proves the exact affine change
of arbitrary weighted finite-gap action sums on the actual action-reduction
curve. `SourceFiniteGapRenormalizedDerivative.lean` differentiates physical
`H3`, the mass subtraction, and the weighted-action subtraction, obtaining
minus the actual renormalized frequency along that decreasing-action curve.

`SourceFiniteGapHamiltonianExponent.lean` identifies the physical smooth
representatives and every hierarchy Hamiltonian across coefficient-identical
sources, and transfers the physical correction under exponent inclusion.
`SourceHamiltonianOpenActionDerivative.lean` uses this to identify an action
derivative of the actual `FL^4` extension. The gap-opening limit in
`SourceHamiltonianFiniteGapDerivative.lean` covers closed actions, including
zero. `SourceHamiltonianRealGradient.lean` uses finite-gap density in the
original `FL^4` norm to cover every real source and every Hilbert direction.

`HilbertScalarGradient.lean` represents a scalar differential by its analytic
Hilbert coefficient gradient and relates the scalar Hessian to the gradient
derivative. `SourceHamiltonianHessian.lean` applies the established frequency
derivative at zero. `HilbertScalarConcavity.lean` proves the quantitative
concavity estimate by continuity in operator norm.
`SourceHamiltonianActionConcavity.lean` constructs the complete action
extension, gradient, Hessian, and concavity packet from actual spectral data.

Public examples construct a positive-radius concavity ball, check the exact
second variation at zero and strict negativity in every nonzero real Hilbert
direction, recover the absolutely convergent frequency pairing for arbitrary
complex directions, and verify physical exponent compatibility.

Validation: the full build passes (6033 jobs), all public examples pass,
and the transitive axiom audit passes for 22333 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining Section 21 identification: agreement with a separately defined
physical correction on the full `H^1` domain still needs a Sobolev
continuity/density bridge or another physical trace argument. The action
calculus and concavity are now proved for the cubic-moment extension;
physical normalization is currently verified on finite-gap sources.
After this identification, continue to the NLS wellposedness and flow
results in Section 22. The dissertation remains unfinished.

## Previous progress: analytic Hamiltonian on action space

The cubic-moment Hamiltonian now descends to one analytic scalar function
on an open complex `ell^2` action domain. The domain contains the action
sequence of every real `FL^4` source and the full nonnegative `ell^1`
cone. The function recovers the actual source Hamiltonian at every real
source, and this recovery uniquely determines it among analytic functions
on the constructed domain.

On every nonnegative `ell^2` action in the domain, the extension is real
and nonpositive, and vanishes exactly at the zero action. This uses real
source realization throughout the nonnegative part of each action ball;
it does not assume global surjectivity of the `FL^4` Birkhoff map.

`SourcePrimitivePowerIsospectral.lean` proves action invariance of all
primitive-power moments at every finite source exponent above one, even
for independently chosen atlases. Summing the cubic moments gives action
invariance of the actual renormalized Hamiltonian.

`ScalarTailSquareDescent.lean` transfers analytic descent to scalar maps
through a continuous linear embedding into one `ell^1` coordinate.
`LocalScalarActionDescent.lean` combines this with tail-sum and finite-head
action charts. Independent tail sign symmetry and rotation stationarity
give a scalar analytic factor with exact recovery on an open complex
neighborhood; infinitely many zero tail coordinates are allowed.

`SourceHamiltonianLocalActionDescent.lean` applies that construction to
the actual Hamiltonian at every real `FL^4` source.
`SourceHamiltonianRealActionBalls.lean` restricts the factors to balls
with real action lifts and proves recovery for every real representative.
`SourceHamiltonianActionExtension.lean` glues those factors, realizes the
nonnegative summable cone, and proves analytic uniqueness, sign, and the
exact zero criterion on the nonnegative part of the action domain.

Public examples construct an actual extension analytic at the fully
collapsed zero action, prove strict negativity at nonzero nonnegative
actions in its domain, and check invariance of every moment across two
atlases at source exponent `3/2`.

Validation: the full build passes (6023 jobs), all public examples pass,
and the transitive axiom audit passes for 22291 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: identify the action gradient with the established renormalized
frequency map, compute the Hessian at zero, and prove local strict
concavity in Theorem 18.3(ii). Agreement with a separately defined physical
correction on the full `H^1` domain still needs the Sobolev continuity and
density bridge; physical normalization is currently proved on finite-gap
sources. The later dissertation remains unfinished.

Planned derivative bridge:

1. Differentiate the physical finite-gap correction along the existing
   Hilbert action-reduction curves. `SourceFiniteGapOpenFrequency.lean`
   already identifies the physical third-Hamiltonian derivative; account
   for the mass and weighted-action subtractions.
2. Transport that calculation to the new `ell^2` action extension, then
   use finite-gap approximation and analytic uniqueness to identify its
   coordinate derivatives with the established frequency map.
3. Combine the gradient identity with the frequency derivative at zero
   to obtain the Hamiltonian Hessian. Continuity in operator norm should
   then give the stated strict-concavity estimate on real directions.

## Previous progress: analytic cubic-moment Hamiltonian extension

The cubic-moment series now constructs the source-space Hamiltonian
extension in Proposition 21.3 on a connected open complex neighborhood
of every real `FL^4` source. It is absolutely and locally uniformly
convergent, complex analytic, and real analytic on the full real source
space. Its real value is nonpositive and vanishes exactly at zero.

`QuarticSummability.lean` turns the actual quartic gap bound into an
absolute `ell^1` estimate. `SourcePrimitivePowerCubicSequence.lean`
constructs the cubic moments as an actual `ell^1`-valued map. Local norm
bounds and bounded-coordinate Taylor assembly prove Banach analyticity.
Continuous linear summation then gives the analytic scalar Hamiltonian.

`LocallyUniformSummation.lean` proves locally uniform convergence of
symmetric sums for every continuous `ell^1`-valued family. Dini's theorem
applies to the continuous decreasing norms of the truncation tails.
The result uses `TendstoLocallyUniformlyOn`, with the neighborhood allowed
to depend on the error tolerance, and implies uniform convergence on
every compact subset of the source domain.

`SourceClosedGapsZero.lean` identifies closure of all periodic gaps with
the zero real source at every finite exponent above one, using the
Birkhoff coordinate zero criterion and global injectivity.

`SourceRenormalizedHamiltonian.lean` defines the literal sum
`H* = -(4/3) * sum_n R_n^(3)`, proves its real sign and exact zero
criterion without a finite-gap premise, and identifies its finite-gap
values with the physical correction proved in Lemma 21.2.
`SourceRenormalizedHamiltonianProposition21_3.lean` assembles the source
extension, proves independence of the primitive atlas on complex
overlaps, and uniqueness among continuous real-source extensions of
the physical finite-gap values. The normalization here is explicitly
verified on finite-gap sources.

Public examples check compact-uniform convergence, strict negativity
at any nonzero real `FL^4` source, uniqueness from physical finite-gap
data, and the closed-gap zero criterion at exponent `3/2`.

Validation: the full build passes (6017 jobs), all public examples pass,
and the transitive axiom audit passes for 22275 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Remaining identification: agreement with a separately defined physical
correction on the full `H^1` domain needs a Sobolev continuity/density
bridge; the current normalization is proved on finite-gap sources.
Next also come the action-domain extension in Theorem 18.3(ii), its
identification with the established frequency map, and the Hessian and
strict-concavity statements. The later dissertation remains unfinished.

## Previous milestone: finite-gap Hamiltonian identity

Lemma 21.2 is now proved for every real finite-gap source at every finite
source exponent greater than one, using the actual physical Hamiltonians,
spectral actions, and primitive-power moments:

`H_3 - 2*H_1^2 - sum_n (2*n*pi)^2 I_n = -(4/3) * sum_n R_n^(3)`.

`SourceFiniteGapContourDecomposition.lean` decomposes a sufficiently large
circle into any real-centered isolating family around precisely the open
gaps. One threshold works for every function analytic off the open gaps;
closed gaps require no holes or exterior spectral-avoidance assumption.

`SourcePrimitivePowerCubicShift.lean` expands the actual identity
`F_0 = F_n - i*pi*n`. Zeroth and second moments vanish, leaving the first
and third moments with their exact coefficients and signs.

`SourcePrimitivePowerHamiltonian.lean` combines this decomposition with
the established physical Hamiltonian contour formula. Weighted moments
have finite support at finite-gap sources, so the displayed infinite
sums are proved equal to the actual finite sums over open gaps.

`SourceFiniteGapRenormalizedHamiltonian.lean` defines the physical
correction and proves it real and nonpositive. It is strictly negative
whenever any gap is open and vanishes exactly when all gaps close.
These are finite-gap consequences; the extension to all real sources
required by Theorem 18.3 is not yet proved.

Public examples construct the full identity at exponent `4`, verify the
sign and zero criterion at exponent `3/2`, and use actual gap-opening
curves to produce strictly negative corrections for every signed index.

Validation: the full build passes (6010 jobs), all public examples pass,
and the transitive axiom audit passes for 22238 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: Proposition 21.3, extending the cubic-moment sum analytically to
the `FL^4` source neighborhood with its global real sign. Then establish
the action-domain extension and local strict concavity in Theorem 18.3.
The later dissertation remains unfinished.

## Previous milestone: complete Lemma 21.1 and complex gap bounds

The primitive-power moments now satisfy all five assertions of Lemma
21.1 on one connected open complex neighborhood containing every real
source, for every finite source exponent greater than one.

`SourcePrimitivePowerComplexCosine.lean` proves joint analyticity of the
odd-power numerator and its cosine mean using symmetric endpoint
coordinates. Real-form uniqueness extends the actual boundary integral
to a complex source ball, including collapsed gaps. The same ball works
for all indices and orders.

`SourceFullAbelianAllGapBound.lean` converts the mixed sequence majorants
and their finite central correction into one scalar bound on both
primitive boundary values at every gap. No index cutoff is needed.

`SourcePrimitivePowerComplexBound.lean` integrates this estimate to prove
`norm R_n^(m) <= B^m * norm gamma_n^(m+1)`. At every complex point in the
common domain, one radius and positive constant work for all nearby
complex sources, all signed indices, and all natural orders. This
completes Lemma 21.1(iii) with a bound uniform over every index.

`SourcePrimitivePowerLemma21_1.lean` assembles the full statement: actual
contour representation, analyticity, even-order vanishing, locally
uniform gap bounds, collapsed-gap vanishing, real positivity and odd
zero detection, and the identity `R_n^(1) = I_n`.

Public examples combine the actual action and cubic moment estimates
on a single complex ball at exponent `4`, and verify the full all-order
bound at exponent `3/2`.

Validation: the full build passes (6006 jobs), all public examples pass,
and the transitive axiom audit passes for 22216 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: the finite-gap Hamiltonian identity in Lemma 21.2, followed by
Theorem 18.3. The later dissertation remains unfinished.

## Previous milestone: positivity and real gap bounds for primitive-power moments

Every primitive-power moment is now proved real and nonnegative at real
sources, and every odd moment vanishes exactly when its spectral gap
closes. This completes Lemma 21.1(iv), including all natural orders and
all signed indices.

`SourcePrimitivePowerBoundary.lean` constructs the analytic numerator
obtained by multiplying an odd primitive power by the selected root.
Shrinking a real isolating circle gives the exact cosine integral of
the actual upper boundary power, with its orientation and coefficient.

`SourcePrimitivePowerRealIntegral.lean` identifies the boundary value
with the real arcosh profile by uniqueness of vertical limits. Every
atlas therefore satisfies the actual arcosh integral formula, including
collapsed gaps and without dependence on its chosen Cauchy family.

`SourcePrimitivePowerPositive.lean` proves continuity and positivity of
the cosine profile, strict positivity of every odd moment on open gaps,
and nonnegativity and reality at every natural order.

`SourcePrimitivePowerRealBound.lean` turns a profile bound into a moment
bound with one additional gap-width factor. The established primitive
estimates give `norm R_n^(m) <= B^m * norm gamma_n^(m+1)` locally uniformly
in real sources and uniformly for distant indices, with the same
neighborhood, cutoff and constant for all orders. In particular the
cubic moment has a quartic gap bound. This is the real-source portion
of Lemma 21.1(iii); its full complex-neighborhood assertion is still open.

Public examples include actual one-gap Hilbert sources with strictly
positive cubic and fifth moments, all-order positivity and zero detection
at exponent `4`, and the locally uniform quartic estimate.

Validation: the full build passes (6002 jobs), all public examples pass,
and the transitive axiom audit passes for 22192 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: extend the gap-size estimate to the complex source neighborhood
in Lemma 21.1(iii), then prove the finite-gap Hamiltonian identity in
Lemma 21.2. Theorem 18.3 and the later dissertation remain unfinished.

## Previous milestone: primitive-power moments and the action identity

The Section 21 moments are now defined from the actual normalized
primitive by `R_n^(m) = -(1/pi) * integral F_n^m`. These have their own
construction, separate from the psi-weighted Section 20 moments.

`SourcePrimitivePowerCircle.lean` proves fixed-contour analyticity,
even-order vanishing (including order zero), and vanishing of every
order at a collapsed gap. The proofs use the analytic square and the
regular Cauchy quotient of the existing full primitive.

`SourceGapContourComparison.lean` gives contour comparison for arbitrary
holomorphic gap integrands. `SourcePrimitivePowerLocalChart.lean` constructs
one source ball supporting every index and order.
`SourcePrimitivePowerAtlas.lean` glues these charts into moments on a
common open neighborhood of the entire real source locus. Contour and
ambient-neighborhood independence hold across the full complex overlaps.

`SourcePrimitivePowerAction.lean` proves the exact first-order identity
`R_n^(1) = I_n` by closed-circle integration by parts. Each moment chart
also supplies an action chart, so equality holds on the full complex
moment domain. The existence theorem constructs all of this data for
every finite source exponent above one.

This proves Lemma 21.1(i), (ii), and (v), and the collapsed-gap consequence
of (iii). Public examples cover source exponents `4` and `3/2`, independence
of ambient constructions, odd moments at complex collapsed gaps, and the
first moment's real-action positivity criterion.

Validation: the full build passes (5998 jobs), all public examples pass,
and the transitive axiom audit passes for 22145 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: the uniform gap-size estimate in Lemma 21.1(iii), positivity and
strict positivity of higher odd moments in (iv), and the finite-gap
Hamiltonian identity in Lemma 21.2. Theorem 18.3 and the later dissertation
remain unfinished.

## Previous milestone: real sequence-space values of the frequency map

The actual renormalized frequency is now proved real at every real
source, and every continuous analytic action realization is real on the
nonnegative part of its domain. Finite summable approximations extend
this statement to nonnegative actions that need not belong to `l1`.

`SourceMomentReality.lean` proves that the filled even-moment numerator
is purely imaginary on a real gap: its squared Abelian factor is the
real arcosh profile squared, and its regular psi quotient has the
required imaginary factor. Conjugation through the cosine integral
then proves reality of every positive even moment, including collapsed
gaps. Conjugation through the moment sum gives reality of the actual
frequency without assuming a finite-gap source.

`RealSummableApproximation.lean` constructs nonnegative finite actions
in `RealCoeff 1` converging in each finite target exponent.
`SourceFrequencyReality.lean` combines Hilbert realization with this
approximation and supplies real-valued analytic extensions agreeing
in complex sequence norm on nonnegative actions.

`SourceFrequencyTheorem18_1Real.lean` adds the real sequence-space range
to Theorem 18.1. One fixed actual frequency on nonnegative summable
actions has a real-valued analytic realization in every finite target
exponent above one. The theorem retains the compatible complex
extensions and locally uniform mixed remainder estimates. Public
examples use target exponents `5/4` and `2`, and nonnegative `l3` actions
for source exponent `6`.

Validation: the full build passes (5993 jobs), all public examples pass,
and the transitive axiom audit passes for 22069 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: the Hamiltonian and convexity results beginning with Theorem 18.3.
Start with the primitive-power moments of Lemma 21.1 and the finite-gap
Hamiltonian identity in Lemma 21.2. These and the later dissertation
remain unfinished.

## Previous milestone: generic local invertibility of the frequency map

The actual frequency map now has two-sided analytic local inverses on an
open dense subset of a connected complex action domain, for every finite
source exponent `p > 2`. This proves the complex generic local
invertibility assertion of Corollary 18.2(iv), retaining the origin
inverse, compact corrected derivative, and Fredholm index zero.

`SchurComplement.lean` proves exact block elimination. The analytic Schur
expression and its finite-dimensional determinant detect invertibility
even when the center is singular. `CompactInvertibleComplement.lean`
extracts the invariant finite-dimensional summand and invertible closed
complement already used for the Fredholm proof; that proof now reuses
the extracted result. Nearby operators need not preserve this splitting.

`LocalAnalyticNonvanishing.lean` propagates density through connected
open sets using the identity theorem. Different neighborhoods may use
different scalar determinants. `AnalyticFredholmDensity.lean` applies
this argument to analytic compact scalar perturbations with one
invertible member.

`SourceFrequencyGenericLocalInverse.lean` chooses the component of zero
and proves that it still contains every real-source action and the
nonnegative summable action cone. It also retains the open source-image
description. Each point in the resulting open dense set has both local
inverse identities and the inverse derivative. Public examples cover
`p = 5/2`, `p = 6`, and a block family whose off-diagonal coupling shifts
its singular parameter from zero to one.

Validation: the full build passes (5989 jobs), all public examples pass,
and the transitive axiom audit passes for 22056 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: the separate real-coordinate frequency range assertion, then the
Hamiltonian and convexity results beginning with Theorem 18.3. The later
dissertation remains unfinished.

## Previous milestone: the origin derivative and analytic local inverse

The actual action-frequency map now satisfies `dF(0) = -2*Id` for
every finite source exponent `p > 2`. The analytic inverse function
theorem supplies an analytic local inverse `G` fixing zero, both local
inverse identities, and `dG(0) = (-2)⁻¹*Id`. This proves the complex local
invertibility assertion of Corollary 18.2(i), alongside the previously
proved compactness and Fredholm assertions (ii) and (iii).

The first frequency coefficient is derived from the spectral moment
formula. A sine-square mean removes the vanishing gap factor from the
second moment, including at collapsed gaps. Its free value and the
normalized action factor give a continuous quotient with value `pi`
on the diagonal and zero off the diagonal. Opening one Hilbert action
therefore gives the frequency coefficient `-2` on the selected mode and
zero on the other modes. Compatibility across source exponents and
density of finite Fourier sums identify the full bounded derivative.

`SourceFrequencyLocalInverse.lean` retains the actual frequency recovery,
full open action domain, nonnegative summable action cone, and Fredholm
index zero throughout the domain. Public examples obtain both inverse
identities and both origin derivatives for `p = 5/2` and `p = 6`.

Validation: the full build passes (5980 jobs), all public examples pass,
and the transitive axiom audit passes for 22025 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: generic local invertibility in Corollary 18.2(iv). The separate
real-coordinate frequency range assertion and the later dissertation
remain unfinished.

## Previous milestone: Fredholm frequency derivatives of index zero

The actual frequency derivative is now Fredholm of index zero at every
complex point of its action domain, for every finite source exponent
`p > 2`. This proves Corollary 18.2(iii), retaining compactness of
`dF(b) + 2*Id`, recovery of the original normalized frequencies at all
real sources, the nonnegative summable action cone, and the open
source-image description of the domain.

`FredholmDecomposition.lean` proves a general reduction: an operator
preserving a finite-dimensional summand and acting invertibly on its
closed complement is Fredholm. Explicit kernel and quotient equivalences
reduce equality of kernel and cokernel dimensions to finite-dimensional
rank-nullity. The conclusion includes closed range, finite-dimensional
kernel and cokernel, and the topological requirements in mathlib's
`ContinuousLinearMap.IsFredholm`.

`CompactFredholm.lean` applies the existing stabilized generalized
eigenspace decomposition to every nonzero scalar shift of a compact
operator on a complex Banach space. Its complementary restriction is
injective and hence bijective by the compact Fredholm alternative. The
result does not assume that the full operator is invertible.

`SourceFrequencyFredholmDerivative.lean` applies this result to the
actual corrected frequency derivative. Public examples include a
singular finite-rank perturbation on `Coeff 2` and actual frequency
extensions for `p = 5/2` and `p = 6` on their whole complex action domains.

Validation: the full build passes (5971 jobs), all public examples pass,
and the transitive axiom audit passes for 21992 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: Corollary 18.2(i), identifying the first frequency Taylor coefficient
and proving `dF(0) = -2*Id` before applying the inverse function theorem.
Generic local invertibility in (iv), the separate real-coordinate frequency
range assertion, and the later dissertation remain unfinished.

## Previous milestone: Pitt's theorem and compact frequency derivatives

Pitt's compactness theorem is now proved for arbitrary bounded complex
operators `Coeff p ->L[ℂ] Coeff q` whenever `1 <= q < p < infinity`,
including the target exponent one. Applying it to the actual refined
frequency derivative proves Corollary 18.2(ii): `dF(b) + 2*Id` is compact
at every complex point of the action domain, for every finite source
exponent above two.

`BoundedCoefficientWeakLimit.lean` uses the existing conjugate cotangent
representation to show that bounded coefficient-null families converge to
zero under every continuous functional, and hence coordinatewise under
any bounded operator. `DisjointCoefficientSums.lean` proves the exact
power-norm identity for finite sums with disjoint coordinate supports,
and its matching cardinality growth bounds.

`SimultaneousBlockApproximation.lean` constructs one increasing subsequence
and disjoint finite blocks for a sequence and its image simultaneously,
with any prescribed positive errors. `StrictPowerGrowth.lean` and
`PittBlockContradiction.lean` show that images cannot remain bounded away
from zero: the disjoint output blocks would grow faster than the bounded
operator allows. Summable geometric approximation errors are included.

`Pitt.lean` upgrades bounded coefficient convergence to norm convergence
of images. Coefficient subsequences and the limit norm bound then show
that the image of the closed unit ball is sequentially compact, yielding
compactness of the operator. The proof does not assume compactness of a
sequence inclusion or a uniform-tail condition on the operator.

`CompactActionDerivative.lean` composes this compact refined derivative
with the bounded inclusion. `SourceFrequencyCompactDerivative.lean`
constructs the actual normalized frequency extension with compact
corrected derivative everywhere. It retains recovery at all real sources,
the full positive summable action cone, the open source-image description,
and the zero value of the frequency.

Public examples cover arbitrary operators `l3 -> l2` and `l2 -> l1`, norm
convergence from bounded coefficient convergence, and actual frequency
extensions at `p = 5/2` and `p = 6`, with compactness on their whole complex
action domains.

Validation: the full build passes (5963 jobs), all public examples pass,
and the transitive axiom audit passes for 21985 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: Corollary 18.2(i), identifying the first frequency Taylor coefficient
and proving `dF(0) = -2*Id` before applying the inverse function theorem.
For (iii), compactness is now available; the Fredholm statement still needs
closed range, finite-dimensional kernel and cokernel, and index zero.
Generic local invertibility in (iv), the separate real-coordinate frequency
range assertion, and the later dissertation remain unfinished.

## Previous progress: Actual frequency derivatives in a strictly refined target

The actual action-frequency maps now have the refined derivative
factorization used in the proof of Corollary 18.2(ii). For every finite
`p > 2`, one target `r` satisfies `1 < r < p/2` and `p/3 <= r`. On the
entire complex action domain, the bounded operator `dF(b) + 2*Id` equals
the inclusion of `dH(b)`, where the analytic correction `H` takes values
in `Coeff r`. The operator-valued map `b -> dH(b)` is analytic.

`RefinedActionExponent.lean` proves the strict target exists, including
source exponents arbitrarily close to two. `RefinedActionDerivative.lean`
differentiates the exact correction identity as an equality of continuous
linear maps. It also retains each coordinate identity and the quantitative
bound `norm(dF(b)v + 2v) <= norm(dH(b))*norm(v)`.

`SourceFrequencyOrigin.lean` proves that every spectral action, the full
action sequence, and the normalized moment-sum frequency vanish at the
zero source at every finite source exponent above one. This generalizes
the previously exposed Hilbert frequency value at zero.

`SourceFrequencySmoothingDerivative.lean` constructs the actual maps,
retaining the normalization witness, recovery of all real-source
frequencies, positive summable action coverage, and the open source-image
description of the domain. The zero action lies in the domain, and both
the frequency and its refined correction vanish there. A single refined
target serves every complex point, with an analytic family of derivatives
and the exact operator factorization.

Public checks specialize the derivative theorem at `p = 5/2` and `p = 6`,
verify the zero values, and retain the coordinate and operator norm bounds.
A general check covers the strict target for every finite `p > 2`, without
an extra assumption such as `p > 3`.

Validation: the full build passes (5955 jobs), all public examples pass,
and the transitive axiom audit passes for 21967 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove the first frequency Taylor coefficient, hence
`dF(0) = -2*Id`, and apply the inverse function theorem. For compactness,
the refined derivative factorization is now available; Pitt's compactness
theorem for operators from a larger finite sequence exponent to a smaller
one remains to be formalized. The sequence inclusion itself is only used
as a bounded operator. Corollary 18.2's compactness, Fredholm index, generic
local invertibility, and the later dissertation remain unfinished. The
separate real-coordinate frequency range assertion is also still pending.

## Previous progress: Theorem 18.1 locally uniform action remainder

The analytic extension and locally uniform mixed asymptotic assertions of
Theorem 18.1 are now assembled in `exists_sourceFrequency_theorem18_1`.
One fixed Hilbert action frequency has compatible analytic extensions for
every finite `p > 2`. At every complex point of the extension domain,
`F(b)_n + 2*b_n` has one `l(p/3) + l(1+)` decomposition on one open
neighborhood. Both components and the neighborhood are chosen before all
auxiliary projection exponents. This includes the quasi-normed range
`2 < p < 3`.

`SourceActionCorrectionBounds.lean` records the common source neighborhood
for all refined target bounds. Stronger Birkhoff-chart, tail-action,
tail-sum, and full-action descent interfaces retain this property; the
previous interfaces remain available as wrappers. The action balls are
shrunk into the image of the bounded source neighborhood, so every complex
action on a ball has a source lift satisfying the same family of bounds.

`BoundedRealActionBallGluing.lean` preserves those bounds through analytic
gluing. `SourceFrequencyBoundedActionSpaceMaps.lean` constructs one action
ball cover before all target exponents. `SourceFrequencyActionSpaceAsymptotic.lean`
then applies the refined sequence decomposition on each ball, obtaining
fixed components with all their uniform bounds. The domain remains the
actual action image of an open source neighborhood containing all real
sources and contains the entire nonnegative summable action cone.

`SourceFrequencyTheorem18_1.lean` combines the mixed remainder with the
previous fixed Hilbert frequency and cross-exponent compatibility. The
maps have complex coefficients and are analytic over both complex and
real scalars. This does not assert a separately constructed RealCoeff-valued
frequency map, nor a Frechet-analytic structure on `CoeffOnePlus`.

Public examples specialize the assembled theorem at `p = 5/2` and `p = 6`,
with action exponents `5/4` and `3` and remainder exponents `5/6` and `2`.
They retain one neighborhood and both components before every finite
projection exponent above one.

Validation: the full build passes (5951 jobs), all public examples pass,
and the transitive axiom audit passes for 21960 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: Corollary 18.2, starting with the derivative at zero and the local
inverse theorem. The compactness argument will use the refined derivative
target and Pitt's theorem, as in the dissertation. Compactness of the
corrected derivative, Fredholm index zero, generic local invertibility,
and the later dissertation remain unfinished. A separate real-coordinate
range assertion for the frequency also remains to be exposed.

## Previous progress: One fixed action frequency with compatible exponent extensions

There is now one fixed actual Hilbert action-frequency map, chosen before
all larger source exponents. On a common open l1 action neighborhood it
has complex and real analytic realizations in every finite target `r > 1`.
For every finite source exponent `p > 2`, its analytic half-exponent action
map agrees with that same fixed frequency on the entire nonnegative l1
cone. All refined correction targets for that extension share its domain
and satisfy the exact complex correction identity there.

`SourceFrequencyActionExponentCompatibility.lean` realizes a nonnegative
summable action sequence by one real Hilbert source, then includes that
source at two arbitrary exponents at least two. The actual action
sequences remain unchanged under coordinate-preserving inclusion. The
normalized moment-frequency compatibility theorem then identifies the
action maps, even when they use independently chosen atlases, Birkhoff
families, action spaces, and target realizations.

`SourceFrequencyActionExtensions.lean` fixes a Hilbert frequency once and
proves that every finite Hilbert target realization has the same scalar
coordinates throughout the complex l1 domain. It constructs the compatible
half-exponent extensions for all finite `p > 2`, deriving the admissibility
of the target `p/2` from the Holder relation. Each extension domain is an
actual spectral-action image of an open source neighborhood containing
all real sources. Analytic refined corrections share that domain and the
literal identity `H(b)_n = F(b)_n + 2*b_n`.

Public checks construct a genuine `CoeffOnePlus` value for the fixed
frequency at every point of its complex l1 domain. They also compare the
`p = 3` and `p = 6` extensions, with action exponents `3/2` and `3`, and
correction targets `5/4` and `2`. The checks cover the whole nonnegative
summable cone, complex-domain correction identities, and fractional
exponent instances.

Validation: the full build passes (5946 jobs), all public examples pass,
and the transitive axiom audit passes for 21948 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: transfer the existing locally uniform source correction bounds to
action space, preserving one neighborhood chosen before every auxiliary
target exponent. Retain the common source bound neighborhood through the
local descent construction, shrink each action ball into its action image,
and use exact local recovery to bound all correction targets on that same
ball. Then apply `Coeff.exists_onePlus_decomposition_of_refined` to obtain
the fixed `l(p/3) + l(1+)` remainder required by Theorem 18.1, including the
range `2 < p <= 3`. The analytic extensions and their exponent compatibility
are proved; these uniform mixed bounds, Corollary 18.2, and the later
dissertation remain unfinished.

## Previous progress: Global analytic frequency maps on action space

The actual local frequency and refined correction maps now glue on one
open complex action domain. It contains every real source action and the
entire nonnegative summable action cone. It is exactly the action image
of an open source neighborhood containing all real sources. One domain
serves all admissible finite target exponents, and the literal identity
`H(b)_n = F(b)_n + 2*b_n` holds throughout that complex domain.

`RealActionPairLifting.lean` constructs nearby real representatives of a
nonnegative scalar action by radial rescaling, with a separate choice at
the zero pair. `RealActionLifting.lean` assembles these into full sequence
lifts and proves `norm(w-z)^2 <= 2*norm(b-I(z))`. The estimate includes
arbitrary infinite zero sets. A nonnegative action ball of radius `R^2/2`
therefore has real lifts in the original coordinate ball of radius `R`.

`SourceRealActionLifting.lean` transfers the real lifts to actual source
charts. It identifies equal Banach action sequences with equal original
real actions, and proves that a local factor recovers an action invariant
function at every real source with a locally represented action.

The tail, tail-sum, and full-action descent constructions now retain their
normalized psi extension witness in stronger interfaces. Existing public
interfaces remain available as wrappers. `SourceFrequencyRealActionBalls.lean`
uses that witness to prove compatibility with every real source, for both
the frequency and correction, on one family of action balls independent
of the target exponent. Every point of a ball has a complex source lift;
every nonnegative point has a real source lift.

`RealActionBallGluing.lean` supplies gluing and uniqueness from those real
representatives. `SourceFrequencyActionSpaceMaps.lean` applies it to the
actual maps, proves inclusion of the full nonnegative l1 cone, and realizes
the resulting domain as the exact image of an open source neighborhood.
`ActionCorrectionIdentity.lean` and `SourceFrequencyActionSpaceCorrection.lean`
then extend the exact correction identity from real representatives to
all complex actions, even when the frequency and correction target norms
differ. Normalization witnesses remain available for later comparisons.

Public checks cover a decreasing action that forces the second coordinate
to change, the full non-Hilbert real-lifting estimate, the Hilbert `l1`
action domain with every finite target `r > 1`, and the actual `p = 6`
frequency and correction on a common `l3` domain with `l3` and `l2` targets.
They verify the global correction identity, positive-cone coverage, exact
source-image equality, and actual frequency recovery at every real source.

Validation: the full build passes (5944 jobs), all public examples pass,
and the transitive axiom audit passes for 21945 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: package the locally uniform mixed-remainder bounds and exponent
compatibility directly on action space in the statement of Theorem 18.1.
The global analytic gluing and literal complex correction identity are
now proved. The derivative at zero needed for Corollary 18.2, its subsequent
compactness/Fredholm conclusions, and the later dissertation remain unfinished.

## Previous progress: Analytic uniqueness and gluing from nonnegative actions

Local analytic maps on balls with nonnegative action centers now agree
throughout their complex overlaps whenever they agree on the nonnegative
parts. An arbitrary compatible family therefore glues uniquely on the
union of its balls, in any complete complex Banach target. This is a
general gluing criterion; the actual frequency maps still need to be
shown to satisfy its real-action agreement hypotheses.

`NonnegativeActions.lean` defines the nonnegative real action locus,
proves its convexity, and identifies it exactly with the quadratic-action
image of the real Birkhoff form. Every such sequence has a real lift with
second component zero, including sequences with infinitely many zero
coordinates.

`NonnegativeActionIdentity.lean` proves complex germ uniqueness at any
nonnegative base, including zero. It pulls the maps back through quadratic
actions, applies the existing real-form identity theorem, then transfers
the germ equality back using openness of the action map. On an open convex
domain meeting the nonnegative locus, agreement on that locus determines
the analytic map everywhere. No interior of the nonnegative cone is assumed.

`NonnegativeActionOverlap.lean` proves that two intersecting balls with
nonnegative centers contain a nonnegative point on the segment joining
the centers. The identity theorem then gives agreement on the full convex
intersection. Empty intersections and arbitrary real radii are allowed.

`NonnegativeActionGluing.lean` constructs the glued map, proves full
Banach-valued analyticity, exact recovery of each local map, and uniqueness
on the union. The domain depends only on the balls, independently of the
target norm. Compatibility is required only on nonnegative actions.

Public checks cover sparse actions with infinitely many zeros, germ
uniqueness at zero with an `l∞` target, overlap uniqueness for maps from
`l3` to `l2`, and gluing an arbitrary family of `l∞`-valued maps recovering
one common real-action function.

Validation: the full build passes (5936 jobs), all public examples pass,
and the transitive axiom audit passes for 21919 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove nearby real lifting of nonnegative actions around arbitrary
real Birkhoff pairs, and use real action invariance to verify compatibility
of the actual local frequency and correction maps on suitably restricted
action balls. The general gluing criterion is proved; its application to
the actual maps, the global domain of Theorem 18.1, Corollary 18.2, and the
later dissertation remain unfinished.

## Previous progress: Local analytic frequency maps on action space

The actual frequency and refined correction now factor analytically through
the full quadratic action sequence on one common open action neighborhood
of each real base. Exact recovery holds at every point of an open original
Birkhoff neighborhood, simultaneously in all admissible target norms. The
action neighborhood is exactly the image of that original neighborhood.

`HeadActionPath.lean` constructs explicit paths to the analytic action
section. Each free head coordinate moves linearly to its base value; a
normalized square root supplies its partner while preserving the action.
The infinite tail remains fixed. All actions are preserved for every
complex time, the base path is constant, and time one reaches the section.

`HeadActionPathAnalytic.lean` proves joint analyticity near every point
of the base path. Uniqueness of continuous square-root branches gives the
correct initial point throughout a neighborhood of the base.
`HeadActionPathNeighborhood.lean` uses the compact unit interval and the
generalized tube lemma to choose one neighborhood where every complete
path remains in the prescribed domain, analytic, and free of zero retained
pairs.

`LocalHeadActionDescent.lean` packages the neighborhoods into an action
chart. Rotation stationarity and the proved curve invariance yield exact
local recovery through the full action map, with no joining-curve
assumptions left to the caller. The explicit factor is analytic and unique
on the chosen action neighborhood.

`SourceFrequencyLocalActionDescent.lean` combines the head and tail
constructions for the actual maps. One source chart and one action domain
serve the frequency targets `r > 1`, `r >= p/2`, and the correction targets
`r > 1`, `r >= p/3`. It preserves the exact coordinate formulas and proves
that every point of the action domain has an original lift in the chosen
Birkhoff neighborhood.

Public checks include a nonzero complex pair with zero quadratic action,
local recovery at the zero base with an empty head and an `l∞` target,
and the actual `p = 6` maps from one `l3` action domain into `l3` and `l2`.
The latter also proves the correction identity `H(b)_n = F(b)_n + 2*b_n`
throughout the action neighborhood, using the proved image equality.

Validation: the full build passes (5932 jobs), all public examples pass,
and the transitive axiom audit passes for 21905 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: establish agreement of the local action maps on overlaps and glue
them into the action-space map required by Theorem 18.1, including its
common domain around the real nonnegative action locus. Local action
factorization is now proved; the global gluing, Corollary 18.2, and the
later dissertation remain unfinished.

## Previous milestone: Invariance along head-action curves

The actual frequency and refined correction in finite-head/tail-sum
coordinates now have zero derivative in every retained-head rotation.
At a head with no zero pair, their derivatives therefore annihilate every
tangent preserving the head actions. They are constant along every
differentiable action-preserving curve satisfying the explicit domain and
nonzero-pair conditions.

`HeadRotationStationarity.lean` proves that a rotation line in a retained
head coordinate stays linear through mixed squaring and tail summation.
Differentiating exact recovery transfers rotation stationarity to the
reduced function. It also proves that the chosen original neighborhood
covers the whole local tail-sum target.

`HeadRotationDescent.lean` uses that coverage and local recovery to prove
the rotation identity at every target point. The source local tail-sum
theorem now has a stronger version exposing these identities for the
actual frequency and correction in all admissible target norms. Both
previous theorem interfaces remain available as corollaries.

`HeadActionTangent.lean` expresses every action-preserving head tangent as
a finite sum of rotations, choosing a nonzero member of each pair. One
member may vanish, and the quadratic action itself need not be nonzero.
`HeadActionCurveInvariance.lean` differentiates the quadratic identities
and applies the mean-value theorem to obtain equality at the endpoints
of a curve. The hypotheses require action preservation for the whole real
parameter, differentiability and domain membership on the unit interval,
and nonzero retained pairs along that interval. No connectivity of an
entire action fiber is assumed.

Public checks cover a pair with zero first coordinate, tangent annihilation
with an `l∞` target, and the actual `p = 6` frequency/correction maps in
`l3` and `l2`, including common-domain rotation identities, constancy along
admissible curves, and exact recovery from the original source chart.

Validation: the full build passes (5927 jobs), all public examples pass,
and the transitive axiom audit passes for 21841 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: construct local action-preserving curves joining nearby points to
the explicit analytic action section and apply the proved curve invariance.
This is needed for recovery throughout an action neighborhood; the current
curve theorem alone does not supply the joining curves. Gluing then remains.
Theorem 18.1, Corollary 18.2, and the later dissertation are unfinished.

## Previous milestone: Analytic sections for head actions

The finite-head/tail-sum coordinates now admit an explicit analytic
section from the full quadratic action space near each base with no zero
retained pair. The actual frequency charts can be chosen with exactly this
nonzero-head property, on the same common domains and for every admissible
target exponent as before.

`NonzeroFiniteCenter.lean` removes indices where both base coordinates
vanish from any finite truncation without changing its center. Consequently,
the centered ball used for sign-invariant descent can retain only pairs
with a nonzero coordinate. This works for complex as well as real bases.

`HeadActionSection.lean` defines the remaining action map on the finite
head and tail sums, with the normalization factor one half. It proves that
composition with mixed squaring and tail summation is precisely the
original `quadraticActionsExponent` map. At each retained index the section
solves for a nonzero coordinate using a prescribed analytic square root
and keeps the other coordinate fixed. All infinitely many tail coordinates
are linear. The section recovers its base exactly and is a right inverse
to the action map, with analyticity in the full sequence norm near the base.
It can be restricted to any prescribed open neighborhood of that base.

The source stationary-descent and local tail-sum-descent theorems now have
stronger versions exposing a nonzero retained head. Their previous APIs
remain available as corollaries. Both frequency and correction can thus be
composed analytically with these action sections on a common neighborhood.

Public checks cover a negative prescribed first coordinate, a zero first
coordinate with a nonzero imaginary second coordinate, the empty head at
the zero base with arbitrary sequence tails, and the actual `p = 6` maps
in `l3` and `l2`. The latter checks simultaneous analyticity after section
composition and exact frequency/correction recovery at the base point.

Validation: the full build passes (5923 jobs), all public examples pass,
and the transitive axiom audit passes for 21820 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.
An initial verification process was terminated with exit code 143; the
complete rerun passed.

Next: prove local constancy along the remaining head-action fibers so that
the section compositions recover the frequency at every nearby point,
then glue the local action maps. Base recovery and an analytic right inverse
alone do not prove this factorization. Theorem 18.1, Corollary 18.2, and the
later dissertation remain unfinished.

## Previous milestone: Local analytic tail-sum factors

The actual frequency and refined correction now factor analytically through
one sequence of tail sums together with the retained finite head. The same
local chart and open neighborhood work for every admissible target exponent,
with exact recovery of the original sequence maps.

`TailSumCoordinates.lean` defines the coordinate space
`(S → Complex) × Coeff q`: its finite component is the first head, while its
sequence component is the second head and the sum of the two tail entries.
The coordinate map is bounded linear and has an explicit bounded linear
right inverse. Its fibers are exactly the tail redistributions already
proved to preserve the descended maps. After mixed squaring, each tail
sum is twice the corresponding quadratic action.

`LocalTailSumDescent.lean` constructs an affine section through any base
point of any open mixed-coordinate domain. It chooses common open source
and target neighborhoods so that every source point is joined to its
section representative by a segment inside the original domain. Evaluation
on this section gives an analytic factor, exact recovery follows from tail
stationarity, and any other factor satisfying recovery agrees on the target.
The target is exactly the image of the chosen source neighborhood. No
nonvanishing condition on the tail or global fiber-connectivity assumption
is needed.

`SourceFrequencyLocalTailSumDescent.lean` applies this construction to the
actual frequency and refined correction simultaneously, preserving the
complex rotation identities of their lifts for the subsequent finite-head
step. It supplies a common open Birkhoff neighborhood of each real source
and exact sequence and coordinate recovery formulas.

Public checks include arbitrary infinite-support tail redistributions,
analytic recovery at the all-zero base point into `l∞`, the sum model with
empty head, and simultaneous actual `p = 6` frequency/correction factors
in `l3` and `l2` on one finite-head/tail-sum domain.

Validation: the full build passes (5921 jobs), all public examples pass,
and the transitive axiom audit passes for 21791 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: replace the retained head coordinates by their quadratic actions,
then glue the local action maps. The analytic action map required by
Theorem 18.1 is still incomplete; Corollary 18.2 and the later dissertation
remain unfinished.

## Previous milestone: Complex tail-action invariance

The actual analytic frequency and refined correction descents now have
zero derivative in every tail redistribution direction `(-v,v)` with
`v` vanishing on the retained head. Directions may have infinite support,
and the identity includes zero tail entries. Their original lifts also
have zero derivative along every complex coordinate rotation, including
rotations of retained head coordinates.

`ComplexActionStationarity.lean` constructs the bounded complex rotation
vector field `(-y_k e_k, x_k e_k)`. Real action invariance makes the
frequency constant along small real rotations; differentiation gives the
identity on the real form. Holomorphic uniqueness extends it throughout
an open convex complex domain, in the full target norm.

`ActionSplitDirection.lean` computes the mixed-square image of a rotation
line, including its quadratic error. The chain rule transfers rotation
stationarity to a weighted tail-splitting identity.
`PairCoordinateDensity.lean` removes the two nonvanishing-coordinate
restrictions by continuity along a punctured scalar perturbation.
`TailActionStationarity.lean` therefore proves that the descended
derivative annihilates each tail-splitting direction even at zero modes.

`TailActionInvariance.lean` uses finite truncations and bounded linearity
to extend the identity to arbitrary tail directions. The mean-value
theorem proves constancy along any redistribution segment contained in
the domain. Thus two mixed-coordinate points with the same retained head
and the same pairwise sums have equal images whenever their joining
segment stays inside the domain. No global convexity of the mixed image
or connectedness of an entire action fiber is asserted.

`SourceFrequencyTailActionStationarity.lean` proves these derivative
identities for the actual frequency and refined correction on one common
open mixed-coordinate domain, retaining joint analyticity, all admissible
target exponents, and exact source recovery formulas.

Public checks cover complex rotation stationarity with an `l∞` target,
continuity at zero entries, infinite tail directions at the all-zero
quadratic example, and the actual `p = 6` maps in `l3` and `l2`, including
their rotation identities and equality on same-action tail segments.

Validation: the full build passes (5918 jobs), all public examples pass,
and the transitive axiom audit passes for 21726 NLS declarations, with no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: construct local analytic factors through the tail sums, then
replace retained head pairs by their quadratic actions and glue the
local action maps. Openness of the full action map is already available.
The analytic action map required by Theorem 18.1 is still incomplete;
Corollary 18.2 and the later dissertation remain unfinished.

## Previous progress: Joint analyticity of the frequency descent

The actual descended frequency and refined correction are now jointly
analytic on their common open mixed-coordinate domain, in every
admissible target sequence norm. The result supplies genuine local Banach
power series, including at zero tail entries. The source charts, common
domain, and exact frequency and correction formulas are preserved.

`HolomorphicCircleIntegral.lean` differentiates parameter-dependent circle
integrals assuming only complex Fréchet differentiability on an open joint
domain. Automatic `C¹` regularity supplies derivative continuity; compactness
of the circle gives a common parameter neighborhood and a uniform bound.
`FDerivCauchyFormula.lean` differentiates the affine-line Cauchy identity in
the base point, obtaining an identity valued in the full operator space.

`FDerivAnalyticLine.lean` turns this identity into an operator-norm power
series along each affine line. Derivative continuity and the earlier
line-to-Fréchet theorem show that differentiating preserves holomorphicity.
`BanachHolomorphicAnalytic.lean` iterates this result to obtain complex
smoothness and applies the existing Banach Taylor theorem. It proves that
complex Fréchet differentiability on an open domain implies joint
analyticity, with a positive-radius expansion using the normalized
Fréchet Taylor coefficients. It also gives the direct criterion from
norm continuity and analytic complex line restrictions.

`TailSquareDescentAnalytic.lean` proves joint analyticity of the general
sign-invariant sequence descent, allowing an `l∞` target.
`SourceFrequencyAnalyticDescent.lean` applies the result to the actual
frequency and refined correction with all admissible exponents and exact
source recovery formulas.

Public checks cover operator-valued analytic lines, normalized Taylor
series with positive radius, the line-to-joint criterion, an `l∞` target,
the all-zero quadratic example, and the actual `p = 6` frequency and
correction as jointly analytic maps into `l3` and `l2`.

Validation: the full check script passes (5,912 build jobs, all public
examples, and an axiom audit of 21,699 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: descend the mixed coordinates (retained head entries and individual
tail squares) to the quadratic actions `I_n = (z₁,n² + z₂,n²)/2`, and glue
the local maps. `QuadraticActionLifting.lean` already proves openness of
the action map, and real action invariance is available. Constancy on
complex action fibers and the analytic action descent still need proofs.
The analytic action map required by Theorem 18.1 is not yet formalized.
Corollary 18.2 and the later dissertation remain unfinished.

## Previous progress: Complex Fréchet differentiability of the frequency descent

The actual descended frequency and refined correction now have complex
Fréchet derivatives throughout their common open mixed-coordinate domain.
Their derivatives are continuous in operator norm: both maps are complex
`C¹`, in every admissible target sequence norm. The source charts, domain,
and exact frequency and correction recovery formulas are preserved.

`AnalyticLineDerivative.lean` proves joint continuity of directional
derivatives in the center and direction using locally uniform convergence
of holomorphic derivatives. `AnalyticLineDerivativeLinear.lean` restricts
to two-dimensional affine planes to prove additivity, then packages the
homogeneous directional derivative as a continuous complex-linear map.
`AnalyticLineDerivativeBounds.lean` proves the Cauchy operator bound
`‖D f(a)‖ ≤ 2*M/R` on a source ball of radius `R` bounded by `M`.

`AnalyticLineRemainder.lean` applies the Schwarz estimate to each line
after subtracting its constant and linear terms. Uniformly for
`‖h‖ < R/2`, the error is bounded by `12*M/R² * ‖h‖²`.
`AnalyticLineFrechet.lean` uses this estimate to prove a genuine Fréchet
derivative, identifies its action with the directional derivative, and
uses the existing holomorphic regularity theorem to obtain complex `C¹`.
The general domain may be any complex normed space; the target is complete.

`TailSquareDescentFrechet.lean` applies these results to the sign-invariant
sequence descent, including infinite target exponent and zero tail entries.
`SourceFrequencyFrechetDescent.lean` proves complex `C¹` regularity of the
actual frequency and refined correction on the same local domain, with
all admissible exponents and exact source formulas.

Public checks cover complex-linear derivative identities, a quantitative
quadratic remainder in an infinite-dimensional domain, an `l∞` target,
Fréchet differentiability at the all-zero source, and the actual `p = 6`
frequency and correction as `C¹` maps into `l3` and `l2`.

Validation: the full check script passes (5,906 build jobs, all public
examples, and an axiom audit of 21,679 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: upgrade complex Fréchet differentiability to joint analyticity,
then descend from individual coordinate squares to quadratic actions and
glue the local maps. The joint analytic action map required by Theorem 18.1
has not yet been formalized. Corollary 18.2 and the later dissertation
remain unfinished.

## Previous progress: Analytic slices in arbitrary sequence directions

The actual descended frequency and refined correction now have analytic
slices in every complex sequence direction, in their full target norms.
Directions need not have finite support. The result holds on the entire
open preimage of the common mixed-coordinate domain and keeps the same
inverse charts, admissible target exponents, and exact source formulas.

`AnalyticLineLimit.lean` proves that analyticity along convergent directions
passes to the limiting direction for a norm-continuous map on an open set
with a complete complex normed target. A common small scalar disc stays
inside the domain for nearby directions. Joint continuity gives uniform
convergence on its compact closure, and the holomorphic-limit theorem
proves analyticity. Only eventual analyticity of the approximations is
needed. Translating the center gives the result on the full line domain.

`TailSquareDescentAnalyticLine.lean` applies this result to finite
truncations of arbitrary coefficient-pair directions. It also proves that
the mixed half exponent is finite whenever the source exponent is finite;
no additional exponent-finiteness assumption is imposed on the descent.
`SourceFrequencyAnalyticLineDescent.lean` upgrades the actual frequency
and correction maps on their common domain to analytic slices in every
direction, in the full target sequence norm.

Public checks cover limits with only eventual analyticity, exponent
finiteness, arbitrary directions with an `l∞` target for the general
sequence theorem, the invariant quadratic sequence map at zero, and the
actual `p = 6` frequency and correction in `l3` and `l2` norms.

Validation: the full check script passes (5,898 build jobs, all public
examples, and an axiom audit of 21,635 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove joint Fréchet analyticity from the analytic line restrictions
and local norm bounds. Then descend from individual coordinate squares
to quadratic actions and glue the local maps. Analyticity along every
line has not yet been upgraded to the joint analytic map required by
Theorem 18.1. Corollary 18.2 and the later dissertation remain unfinished.

A concrete next target is the directional derivative
`D(a,v) = deriv (fun t => G(a+t*v)) 0`. A common Cauchy circle and local
norm bounds should give continuity of `D` in the center and direction,
a linear norm bound in `v`, and a uniform quadratic remainder for small
increments. Additivity in `v` must be proved, not assumed: it can be
compared using two successive increments and continuity as their centers
approach `a`. Together with complex homogeneity, these properties would
produce a bounded complex-linear Fréchet derivative. Full joint
analyticity still needs a proved upgrade after that. Existing references
include `TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn`,
`Complex.cderiv`, and `BanachHolomorphicC1.lean`; the latter already
proves continuous Fréchet derivatives once differentiability is known.

## Previous milestone: Analytic slices in finite-support directions

The descended frequency and refined correction now have analytic slices
in every finite-support direction, in their full target sequence norms.
A single direction may change both components, retained head entries, and
multiple zero tail entries simultaneously. The theorem holds on the full
open preimage of the common mixed-coordinate domain and preserves all
admissible target exponents and exact source recovery formulas.

`QuadraticLineRoot.lean` constructs a root of `a² + u²*d` that equals `a`
at zero and is analytic there, including when `a = 0`. In that case it is
`u*sqrt(d)`; otherwise it uses the normalized prescribed root. The square
identity holds globally, while analyticity is asserted locally at zero.

`FiniteMixedSquareLineLift.lean` assembles these roots into an analytic
finite-coordinate perturbation of a coefficient pair. Its mixed-square
image is exactly `Q(z) + u²*truncatePair(T,d)`. Retained head entries use
the quadratic parameter directly, and unchanged coordinates stay fixed.
No nonvanishing condition on the tail is required.

`TailSquareDescentFiniteLine.lean` combines this lift with input-square
analytic descent to prove scalar analyticity along each finite-support
line. Norm continuity then upgrades the entire sequence-valued slice.
`SourceFrequencyFiniteLineDescent.lean` applies the construction to the
actual frequency and correction on their common open domain.

Public checks cover collapsed and noncollapsed roots, a squared center
on the principal branch cut, head and zero tail entries moving together,
an empty direction block, simultaneous changes in both components,
sequence-valued quadratic descent at zero, and the actual `p = 6`
frequency and correction in `l3` and `l2` norms.

Validation: the full check script passes (5,895 build jobs, all public
examples, and an axiom audit of 21,625 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: extend the line result from finite-support directions to arbitrary
sequence directions, and prove joint Fréchet analyticity. Then descend
from individual coordinate squares to quadratic actions and glue the
local maps. Finite-support line analyticity is not yet the analytic
action-space frequency map of Theorem 18.1; Corollary 18.2 and the later
dissertation also remain unfinished.

For the next extension, a useful Mathlib lemma is
`IsCompact.mem_uniformity_of_prod` in `Topology/UniformSpace/HeineCantor`.
It gives uniform convergence on a compact scalar disc for a jointly
continuous family as its direction parameter converges, without assuming
local compactness of the sequence space. Around a fixed domain point,
choose a small scalar disc and a bounded neighborhood of the desired
direction so all affine points remain in the domain. Apply this lemma to
`(v,t) ↦ G(b+t*v)` and the finite truncations of `v`. The existing
`TendstoLocallyUniformlyOn.differentiableOn` theorem then provides a route
to analyticity along arbitrary directions. This limit argument and the
subsequent joint Fréchet-analytic conclusion are not yet formalized.

## Previous milestone: Analytic coordinate slices in the full sequence norm

The actual descended frequency and refined correction are now analytic
in their full target sequence norms along every individual coordinate line.
The result holds on the entire open preimage of the common mixed-coordinate
domain, including zero tail squares and retained head coordinates. It keeps
the same charts, domain, admissible target exponents, exact recovery, and
literal coordinate formulas as the preceding construction.

`AnalyticSequenceSlice.lean` upgrades scalar output analyticity and norm
continuity to analytic sequence-valued affine slices. It translates the
analytic germ at each line point and applies the existing locally bounded
coordinate realization theorem. The affine base need not belong to the
domain; analyticity is asserted only on its open preimage. The general
lemma also supports an `l∞` target and a zero linear direction.

`TailSquareDescentAnalyticSlice.lean` applies this result to invariant
analytic sequence maps, supplying analyticity on the full slice domain
and at every image point. `SourceFrequencyAnalyticSliceDescent.lean`
constructs the actual frequency and correction maps with these properties
on one common domain, before choosing their target exponents. Frequency
targets remain finite `r > 1` with `r >= p/2`; correction targets remain
finite `r > 1` with `r >= p/3`.

Public checks cover an `l∞` target with an arbitrary affine base, the
sequence-valued quadratic polynomial at the all-zero source in both
components, full slice domains, and actual `p = 6` frequency and correction
slices analytic in `l3` and `l2` norms, respectively.

Validation: the full check script passes (5,891 build jobs, all public
examples, and an axiom audit of 21,606 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: handle simultaneous coordinate variations and establish joint
Banach-space analyticity, then descend from individual squares to quadratic
actions and glue the local maps. Analyticity along individual coordinate
lines alone is not being treated as a proof of joint analyticity. Theorem
18.1, Corollary 18.2, and the later dissertation remain unfinished.

A route for simultaneous finite-support directions is to pull the line
parameter back by `t = u²`. For each changed tail entry, the radicand is
`a + u²*d`. If its center `a` is zero, use the analytic root `u*sqrt(d)`;
otherwise use the prescribed local analytic root already proved. Only
finitely many entries change, so their analytic lifts can be combined on
one neighborhood; retained head entries vary by `u²` directly. The mixed
recovery identity and `analyticAt_of_comp_sq` should then establish scalar
analyticity of this finite-support line, and the new sequence-slice theorem
can upgrade the output norm. This construction, extension to arbitrary
source directions, and the joint Fréchet-analytic conclusion are still
unproved; do not infer the last conclusion from coordinate slices alone.

## Previous milestone: Analyticity in individual squared tail coordinates

The actual frequency and refined correction now have scalar components
analytic in every individual coordinate of the mixed half-exponent domain,
including at zero tail coordinates. This uses the same continuous descended
maps, common open domain, inverse chart, and admissible target exponents as
the previous milestone. Exact sequence recovery and the literal moment-sum
frequency and correction formulas remain part of the theorem.

`AnalyticSquareDescent.lean` proves that analyticity of `w ↦ g(w²)` at
any complex `w` implies analyticity of `g` at `w²`, without assuming
continuity of `g`. At zero, an even Cauchy transform gives the analytic
descent; away from zero, a prescribed local analytic square root suffices.
The proof also handles squared base points on the principal square-root
branch cut.

`TailSquareDescentCoordinateAnalytic.lean` constructs an analytic lift for
a single tail coordinate and proves its exact mixed-square identity.
Every continuous linear scalar observation of a descended analytic map is
analytic along each coordinate of either component. Combining this with
the retained-head result covers all signed indices. The recovery-based
lemma is also available independently of the chosen descent construction.

`SourceFrequencyCoordinateAnalyticDescent.lean` applies these results to
the actual frequency and correction sequences. Their scalar components
are separately analytic in every mixed coordinate; the retained finite
head still has analyticity in the full target norm.

Public checks cover the double root without a continuity hypothesis,
a squared base point on the branch cut, an invariant nonlinear polynomial at the
all-zero sequence in both components, arbitrary scalar linear observations,
and the actual `p = 6` frequency in `l3` and correction in `l2` on one
open `l3`-pair domain.

Validation: the full check script passes (5,888 build jobs, all public
examples, and an axiom audit of 21,600 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: establish joint Banach-space analyticity, descend from the individual
coordinate squares to quadratic actions, and glue the local maps. Separate
coordinate analyticity alone is not being identified with joint analyticity.
The analytic action-space map of Theorem 18.1, Corollary 18.2, and the later
dissertation remain unfinished.

A concrete next bridge is the theorem
`Coeff.analyticOnNhd_of_coordinatewise_of_continuousOn` in
`BoundedCoordinateAnalytic.lean`:
restrict the descended sequence map to the open preimage of its domain
under `t ↦ b + pairSingleCLM q second k t`. The new coordinate theorem,
translated at each parameter value, gives analytic scalar output components
on that preimage; existing norm continuity then gives analyticity of the
entire sequence-valued slice. This still concerns one input coordinate at
a time. A further argument is needed for finite-dimensional slices and
joint analyticity in the infinite-dimensional source norm.

## Previous milestone: Continuous descent to squared tail coordinates

`SourceFrequencyTailSquareDescent.lean` constructs continuous descended
frequency and correction maps on one open mixed-coordinate domain around
every real source. The finite head remains unsquared, while both tail
components are squared into the Banach half-exponent space. The theorem
retains analyticity of the lifted maps, exact sequence recovery, and the
literal moment-sum frequency and correction coordinate formulas.

The common domain and chart precede all admissible target exponents:
finite `r > 1` with `r >= p/2` for the frequency and `r >= p/3` for the
refined correction. The source half exponent is Banach here. The descended
maps are also analytic in all retained finite-head perturbations, in the
full target norm. Analyticity in the squared tail is not yet proved.

`MixedSquare.lean` constructs the analytic mixed-coordinate map and proves
it is an open surjection. A nearby lift has distance at most
`sqrt(norm(delta)) + K*norm(delta)`, where the finite-head transfer operator
determines `K`. Its fibers are precisely equal finite heads and equal
coordinate squares. `OpenMapDescent.lean` supplies continuous descent
along a continuous open map on an open domain. `TailSquareDescent.lean`
uses the proved complex tail sign invariance to obtain exact recovery,
uniqueness on the image, and transfer of bounds.
`TailSquareDescentHeadAnalytic.lean` supplies the explicit linear lift for
finite-head perturbations and proves their analyticity.

Public checks cover the empty head, zero coordinates, openness and
surjectivity, a nonlinear polynomial whose descended formula is linear,
transfer of sequence norm bounds, finite-head analyticity, and the actual
`p = 6` frequency and correction on one open `l3`-pair domain.

Validation: the full check script passes (5,885 build jobs, all public
examples, and an axiom audit of 21,587 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove analyticity in squared tail coordinates through their zeros,
then establish joint Banach-space analyticity, pass from the individual
coordinate squares to quadratic actions, and glue the local maps. These
mixed-coordinate maps are not yet the analytic action-space frequency
map of Theorem 18.1. Corollary 18.2 and the later dissertation remain
unfinished as well.

For the next local step, prove scalar analyticity along one squared tail
coordinate. At a nonzero lifted coordinate, use the prescribed local
analytic root in `LocalAnalyticSquareRoot.lean`. At zero, use
`ParametricEvenSquareDescent.lean` and the proved complex sign symmetry.
In both cases, identify the result with the existing descended map through
`tailSquareDescent_apply`. Joint analyticity in the infinite-dimensional
Banach norm will then need its own proof.

## Previous milestone: Complex tail sign invariance for frequency charts

`SourceFrequencyComplexSignInvariance.lean` constructs a complex ball
around every real source's Birkhoff coordinates whose center has finite
support. The ball contains the original point and lies inside its actual
inverse chart. One finite block, chart, and radius work for every
admissible sequence target: `r > 1`, finite, and `r >= p/2` for the
frequency or `r >= p/3` for its refined action correction.

Both actual sequences are analytic and invariant under arbitrary
independent complex coordinate sign changes outside that finite block.
The signs may change infinitely many coordinates. Real action invariance
and holomorphic uniqueness prove this symmetry; it is not supplied as a
complex invariance assumption. The construction retains the coordinate
identities for the literal moment-sum frequency and correction.

`SequenceSpaces/RealFormIdentity.lean` proves Banach-valued holomorphic
uniqueness from real coefficient pairs on open convex domains, using
contractive real and imaginary projections. `SignChange.lean` constructs
the bounded complex linear sign maps and proves their isometry, reality,
and square-preservation properties. `FiniteCenterBall.lean` uses norm
convergence of finite truncations to obtain the required center and ball.
`ComplexSignInvariance.lean` extends real sign symmetries to complex
balls and proves independence from coordinatewise square-root choices
when the finite head is fixed, including zero coordinates.

Public checks cover infinite sign selections, Banach-valued uniqueness,
finite centers below the Hilbert exponent, tail root-choice independence,
and a common actual `p = 6` chart with `l3` frequency and `l2` correction.

Validation: the full check script passes (5,880 build jobs, all public
examples, and an axiom audit of 21,553 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: construct analytic descent through the squared tail coordinates,
then pass to quadratic actions and glue the local action-space maps.
Sign invariance and root-choice independence do not yet prove invariance
on every complex quadratic action fiber or analytic descent. Theorem 18.1,
Corollary 18.2, and the later dissertation remain unfinished.

## Previous milestone: Open action neighborhoods and quantitative square-root lifts

`SourceActionNeighborhood.lean` constructs an open complex neighborhood
in the Banach half-exponent action space, containing every real spectral
action value. For finite `p >= 2`, it contains the entire nonnegative
`l1` cone under its natural inclusion. Every point of the neighborhood
is realized by the original spectral actions of a source inside any
prescribed open neighborhood of the real source locus.

The geometric input is quantitative. `NearbySquareRoot.lean` selects a
root close to any prescribed complex value.
`SquareRootLifting.lean` lifts this coordinatewise to prove
`norm(w-a)^2 <= norm(b-a^2)` in the `lp` and `l(p/2)` norms.
`QuadraticActionLifting.lean` keeps the second coordinate fixed and proves
`norm(w-z)^2 <= 2*norm(b-Q(z))` for the actual quadratic action map.
Consequently, an action ball of radius `r^2/2` lifts into a coordinate
ball of radius `r`. Both squaring and quadratic actions are open
surjections and topological quotient maps, including at zero.

`SourcePositiveActionRealization.lean` realizes every nonnegative `l1`
sequence through real square roots and the global Hilbert Birkhoff
inverse. Exponent compatibility preserves the original actions for
larger finite source exponents. This does not require global Birkhoff
surjectivity above exponent two. The inverse charts from the preceding
milestone transfer the open quadratic images to actual spectral actions.

Public checks cover the sharp square-root bound, arbitrary complex
coordinate pairs, the all-zero case, Hilbert actions, quotient topology,
positive-cone realization, and a complex `l2` action neighborhood at `p = 4`.

Validation: the full check script passes (5,875 build jobs, all public
examples, and an axiom audit of 21,519 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove complex action-fiber invariance and analytic descent of the
frequency through the quadratic map, including zero coordinates, then
glue the local descended maps. The geometric action neighborhood is now
constructed; Theorem 18.1's analytic frequency map on it remains unfinished.
Corollary 18.2 and the later dissertation also remain unfinished.

## Previous milestone: Real-compatible complex frequency charts

`SourceBirkhoffInverseChart.lean` constructs complex analytic local inverses
at every real source for every finite `p > 1`, restricted inside any
prescribed open source neighborhood. Reality is proved by comparing the
actual real and complex inverse germs. The charts retain both inverse
identities and identify every original spectral action, including zero
actions, with `(x_n^2 + y_n^2)/2`. The entire Banach action sequence has
this identity as well.

`SourceFrequencyBirkhoffChart.lean` constructs the moment atlas, Birkhoff
family, and one chart per real source before choosing any target exponent.
The frequency is analytic in every finite `lr` with `r > 1` and
`r >= p/2`; its action correction is analytic for `r >= p/3` under the
same finite and strict lower bounds. On that chart the correction is
exactly frequency plus `x_n^2 + y_n^2`. Both actual sequences are constant
on real quadratic action fibers. No inverse chart, contour atlas, or
reality property is assumed in the construction theorem.

Public checks cover a common `p = 6` chart with an `l3` frequency and
an `l2` correction, the full `p = 4` action sequence, zero coordinates,
real action-fiber invariance, and charts below the Hilbert exponent
inside prescribed open source neighborhoods.

Validation: the full check script passes (5,870 build jobs, all public
examples, and an axiom audit of 21,483 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove analytic descent through the quadratic action map, including
zero coordinates, and construct the complex action neighborhood in
Theorem 18.1. These charts supply the required coordinate preparation;
they do not yet prove analytic descent. Corollary 18.2 and the later
dissertation remain unfinished.

## Previous milestone: Frequency invariance on action level sets

`SourceFrequencyActionInvariance.lean` proves that the actual moment-sum
frequency depends only on the original spectral actions for every finite
`p > 1`. It compares independent contour atlases and compatible normalized
psi extensions. The entire frequency sequence and its refined action
correction have the same invariance. Each scalar frequency factors through
the action values; no analyticity on action space is claimed yet.

`SourceActionIsospectralAllExponents.lean` extends the equality of action
level sets and actual isospectral sets to every finite `p > 1`. First,
equal-action finite-gap sources have equal spectra through their physical
Hilbert representatives. Then independent local Birkhoff inverses lift
matching finite output truncations of two arbitrary equal-action sources.
Continuity of the discriminant passes equality to the limits, preserving
the original spectrum and every algebraic multiplicity. This argument
does not require global Birkhoff surjectivity above exponent two.

`SourcePsiGapRootIsospectral.lean` transports signed gap geometry and the
literal normalized contour equations. Uniqueness identifies the actual
psi root vectors. `SourceAbelianPrimitiveIsospectral.lean` uses the proved
endpoint normalization on the half-planes and continuity on real bands
to preserve the primitive without an additive constant.
`SourceAbelianMomentIsospectral.lean` compares literal integrands on a
common circle and then uses contour homotopy. All moment orders, both
signed indices, and collapsed gaps are included.

An unconditional construction combines the analytic source frequency
map from Theorem 20.5 with its action invariance. The caller supplies
only a finite exponent above one. Public checks cover the `p = 4`
spectrum and multiplicities, the sub-Hilbert range, all moment orders
across independent atlases, an analytic `l2` frequency map constant on
action level sets, the refined correction, and the zero-action case.

Validation: the full check script passes (5,868 build jobs, all public
examples, and an axiom audit of 21,443 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: prove analytic descent of the frequency map to action space,
including the complex action neighborhood in Theorem 18.1. The present
factorization proves well-definedness only. Corollary 18.2 and the later
dissertation remain unfinished.

## Previous milestone: Action-frequency asymptotics before descent

`SourceActionFrequencyAsymptotic.lean` constructs the actual correction
`omega*_n + 2*I_n` on one connected complex neighborhood of the real
source locus, for every finite `p > 1`. It is complex and real analytic
in every finite `lr` with `r > 1` and `r >= p/3`, and retains the physical
finite-gap frequency identity.

The mixed remainder is a single pair of maps into `l(p/3)` and the
actual intersection space `CoeffOnePlus`. The components are chosen
before the projection exponent. Their norms are locally uniformly
bounded, separately for each finite projection of the `l(1+)` component.
This establishes the source-space input to equation (4.12), including
quasi-normed third exponents and complex closed gaps.

`SourceActionGapCorrection.lean` uses the normalized-action factorization
to bound `I_n - gamma_n^2/4` by a cubic sequence product. It provides one
common domain and local neighborhoods independent of the target exponent.
`SourceActionFrequencyCorrection.lean` combines this with Theorem 20.5
through an exact replacement identity. `LocallyBoundedRealization.lean`
upgrades the scalar analytic coordinates to the actual Banach sequence
map; `RefinedOnePlusDecomposition.lean` supplies the fixed mixed pair.

`QuadraticActionsExponent.lean` extends the entire quadratic action map
to every Banach half exponent, with a squared-norm bound.
`SourceActionSequenceExponent.lean` identifies it with the original
spectral actions, proves sequence-valued analyticity and the coordinate
formula for its derivative, and recovers the existing Hilbert action map.
The analytic action sequence is constructed without assuming a Birkhoff
family.

Public checks cover the `p = 4` action map and its derivative into `l2`,
a signed one-mode action radius, the sharp `p = 6` frequency correction
into `l2`, a fixed mixed pair with quasi-normed first component, and the
closed-gap replacement identity.

Validation: the full check script passes (5,863 build jobs, all public
examples, and an axiom audit of 21,416 declarations). There are no
admitted proofs or new axioms. The 21 existing warnings are unchanged.

Next: complete Theorem 18.1 by proving that the frequency depends only
on the actions and descends analytically to action space. The source-space
asymptotic above does not yet prove this descent. Corollary 18.2 and the
later dissertation also remain unfinished.

## Previous milestone: Theorem 20.5 frequency maps and asymptotics

`SourceFrequencyTheorem20_5.lean` constructs the frequency map on one
connected open neighborhood of the real source locus for every finite
`p > 1`. Its coordinates are the actual moment-sum frequencies from
Theorem 20.4. The sequence map is complex and real analytic in every
finite `lr` with `r > 1` and `r >= p/2`. This includes every finite
`r > 1` at `p = 2` and the exact target `l(p/2)` at `p > 2`.

The correction `omega*_n + gamma_n^2/2` is locally bounded in every
finite `lr` with `r > 1` and `r >= p/3`. It also has the stated
`l(p/3) + lq` decomposition for every finite `q > 1`, including the
quasi-normed range `p/3 < 1`. The local source neighborhood is selected
before the target exponent; its bound may depend on that exponent.

`RefinedTripleProduct.lean` proves cubic product estimates without a
Banach assumption on the intermediate exponents.
`ReciprocalRowSumCoefficients.lean` sums varying coefficient rows using
a shared reciprocal majorant, proving absolute convergence and the
norm bound for the actual summed sequence. The frequency correction
then follows from the exact diagonal/off-diagonal moment decomposition.
Local norm bounds and scalar analyticity yield sequence-valued
analyticity through the bounded-coordinate theorem.

The construction includes the physical finite-gap frequency identity.
A separate compatibility theorem identifies sequence maps at different
source exponents whenever the real potentials have the same Fourier
coefficients. Public checks cover the Hilbert target range, the exact
`p = 4` physical frequency map into `l2`, the quasi-normed mixed remainder,
the sharp `p = 6` cubic threshold, and the zero potential.

Validation: the full check script passes (5,856 build jobs, all public
examples, and an axiom audit of 21,382 declarations). There are no
admitted proofs or new axioms and no new warnings; the 21 existing
warnings remain.

Next: the deduction of Theorem 18.1 and Corollary 18.2 following Theorem
20.5: descent to action variables, the action-frequency asymptotic, and
the differential and local invertibility statements. These and the later
dissertation remain unfinished.

## Previous milestone: Theorem 20.4 at all finite source exponents

`SourceSecondMomentFrequencyTheorem20_4.lean` completes the physical
finite-gap identification and analytic uniqueness for every finite
`p > 1`. The renormalized frequency is the actual absolutely and locally
uniformly convergent sum `-4/(2*pi) * sum_k Omega_nk^(2)`. On one connected
open neighborhood of the real source locus it is complex analytic and
real analytic, agrees with the physical finite-gap frequency after
subtracting `4*H_1 + (2*n*pi)^2`, and is uniquely determined by those
finite-gap values. Local uniform convergence is for each fixed index.

`SourceAbelianPrimitiveExponent.lean` preserves the endpoint-normalized
primitive across source exponents, first on the half-planes and then on
the real bands. `SourceAbelianMomentExponent.lean` compares the literal
integrands on a common circle and uses contour homotopy to compare
independent atlases. It proves compatibility of every moment order and
both indices, including collapsed gaps, whenever Fourier coefficients
coincide.

`SourceFiniteGapFrequencyExponent.lean` constructs the unique Hilbert
representative of each actual finite-gap source. It preserves the smooth
physical potential pointwise and every physical Hamiltonian. The physical
frequency is transported from the previously defined Hamiltonian
derivative, independently of the moment sum. It is independent of the
Birkhoff realization and source exponent, and recovers the original
frequency at `p = 2`.

`SourceAbelianMomentLocalChart.lean` now constructs charts for any
specified normalized psi extension while preserving its previous public
existence theorem. `SourceAbelianMomentSquaredGapAtlas.lean` uses this to
construct the atlas and squared-gap estimates with the same branch.
`SourceSecondMomentFrequencyExistence.lean` then gives an unconditional
Theorem 20.4 construction from only `p < infinity` and `p > 1`, with
physical agreement for every Birkhoff realization.

Public checks exercise the constructed analytic family at `p = 3/2`,
physical agreement at `p = 3`, equality of transported frequencies across
those exponents, the all-closed zero potential with its free dispersion,
and preservation of the physical NLS Hamiltonian.

Next: Theorem 20.5, sequence-valued analyticity of the frequency map and
the locally uniform asymptotic `omega*_n + gamma_n^2/2` in
`l(p/3) + l(1+)`. For `p = 2` the target is every `lr`, `r > 1`; for
`p > 2` it is `l(p/2)`. This theorem and the later dissertation remain
unfinished.

## Previous milestone: Analytic moment sums and Hilbert Theorem 20.4

`SourceAbelianMomentSeries.lean` proves absolute and locally uniform
convergence of the actual second-moment series for every finite `p > 1`.
It uses Lemma 20.3 at exponent `p`, the locally bounded gap sequence,
and a fixed reciprocal kernel in the conjugate exponent. The source
neighborhood is common to every selected index; convergence is uniform
in the source for each fixed index, with no assertion of uniform
convergence over all selected indices.

`ReciprocalSeriesConvergence.lean` supplies the general Holder argument,
including a separately bounded diagonal. Bounded coefficient rows need
not have uniform tails: the tails come from the fixed reciprocal kernel.
`SourceSecondMomentFrequencyAnalytic.lean` defines the renormalized sum
with the exact factor `-4/(2*pi)` and proves complex analyticity in the
full Banach source variable using locally uniform analytic approximation.
Real analyticity follows by restricting scalars.

`SourceFiniteGapAnalyticUniqueness.lean` proves that actual spectral
finite-gap values determine an analytic function on a connected almost-real
domain, for every finite `p > 1`. It combines finite-gap density, the
real-form identity principle, and analytic continuation.
`SourceSecondMomentFrequencyFiniteGap.lean` packages the Hilbert version
of Theorem 20.4: absolute and locally uniform convergence, complex and
real analyticity, agreement with physical finite-gap frequencies after
subtracting mass and free dispersion, and uniqueness. The physical
frequency remains defined independently through Hamiltonian derivatives.
The renormalized frequency vanishes at the zero source.

Public checks cover a bounded coefficient family with no assumed uniform
tails and a nonzero diagonal, the non-Hilbert exponent `p = 3`, uniqueness
from spectral finite-gap data, the zero potential at a nonzero selected
index, and the exact physical mass renormalization.

Next: transport the physical finite-gap frequency identification across
source exponents to finish the all-exponent form of Theorem 20.4. The
analytic series construction and finite-gap uniqueness already hold for
all finite `p > 1`; the packaged physical agreement currently has `p = 2`.
Theorem 20.5 and the rest of the dissertation remain unfinished.

## Previous milestone: Full Lemma 20.3 on one complex neighborhood

`SourceAbelianMomentLemma20_3.lean` proves both assertions of Lemma 20.3
for the actual normalized second moments, on one connected open complex
neighborhood of the real source locus. The off-diagonal formula is
`Omega_nk^(2) = gamma_k^3/(n-k)*(a_k+b_k)` for `k != n`; the diagonal
formula is `Omega_kk^(2) = gamma_k^2/4*(pi+d_k+e_k)`. For every finite
`q > 1`, `a,d` belong to `lq` and `b,e` to `l(p/2)`, with one positive
locally uniform norm bound, uniform in the deleted index. The local
source ball is chosen before `q`. Collapsed gaps are included.

The refined theorem constructs the actual diagonal correction and every
actual off-diagonal coefficient row in each finite `lr`, `r > 1` and
`r >= p/2`. These coefficients are independent of the exponent. The
previous off-diagonal power-sum theorem remains available.

The new diagonal proof uses a shared sequence rather than unrelated
row bounds. `UniformHolderConvolution.lean` and
`UniformReciprocalMajorant.lean` use powered Young and Holder to bound
all varying lp rows by one sequence built from the fixed weights.
`SourceMidpointProductSharedMajorant.lean` retains this common sequence
through the infinite-product remainder. `SourcePsiSharedQuotientTail.lean`
uses squared gaps as the fixed weights and adds the shared reciprocal-square
gap correction. `SourcePsiSharedActualGapMajorant.lean` patches the
central indices and restricts to actual moving segments. Its sequence
is chosen before **both** the deleted and selected indices.

`SourceAbelianMomentDiagonalCoefficients.lean` combines that quotient
bound with the square-error estimate and verifies the normalization
constant `pi/4`, including zero gaps. The diagonal neighborhood theorem
and the off-diagonal result are then placed on one common connected
domain in `SourceAbelianMomentLemma20_3.lean`.

Public checks cover a varying test row under one reciprocal majorant,
square-summability of the actual diagonal and off-diagonal coefficients
on the same source domain, the filled value at a collapsed gap, and the
exact diagonal leading term when the two approximation errors vanish.

Next: Theorem 20.4, proving absolute and locally uniform convergence of
the moment sum, its analytic frequency extension, and agreement with
the physical finite-gap frequencies. Theorem 20.5 and the remaining
dissertation are still unfinished.

## Previous milestone: Off-diagonal Lemma 20.3 and uniform power sums

`SourceAbelianMomentLemma20_3OffDiagonal.lean` proves the off-diagonal
assertion of Lemma 20.3 for the actual normalized moments. On one connected
open neighborhood of the real source locus, the exact formula is
`Omega_nk^(2) = gamma_k^3 / (n-k) * (a_k + b_k)` for `k != n`, where
`a` belongs to every requested finite `lq`, `q > 1`, and `b` belongs to
`l(p/2)`. Their row norms are uniform in the deleted index and locally
uniform at every complex source. The local ball is chosen before `q`.

The explicit power-sum version is also proved: the actual coefficient
`(n-k)*Omega_nk^(2)/gamma_k^3`, set to zero at the deleted index and at
closed gaps, is in every finite `lr` with `r > 1` and `r >= p/2`.
Its `r`-power sum has a positive bound uniform in the deleted index and
locally uniform in the source. The coefficient itself is independent of
`r`. The cubic estimate forces the actual moment to vanish at a collapsed
gap, so the exact formula remains valid there.

`RefinedProductMajorant.lean` combines quasi-Banach Holder multiplication
with contractive exponent inclusion, preserving the product norm bound
also when `p/2 < 1`. `SourceAbelianMomentSquareMajorants.lean` transfers
the filled-square estimates to the moment atlas's own ambient domain.
`SourceAbelianMomentOffDiagonalMajorants.lean` combines these with the
actual root offsets and all-gap chi errors to give the uniform cubic
majorant. `SourceAbelianMomentCubicCoefficients.lean` constructs the exact
coefficient sequence, and `SourceAbelianMomentOffDiagonalNeighborhood.lean`
puts it on a common connected almost-real domain.

Public checks cover the half-exponent `3/4` product gain, the actual
square-summable coefficient power sum at source exponent four, vanishing
at collapsed selected gaps, and zero at the deleted index.

Next: prove the diagonal assertion of Lemma 20.3 with a single sequence
majorant across diagonal indices. Uniform norms for separate off-diagonal
rows do not establish that diagonal estimate. The full Lemma 20.3,
general infinite-gap frequencies, and the remaining dissertation are
still unfinished.

## Previous milestone: Refined psi row bounds on all complex gaps

`SourcePsiCentralGapBound.lean` bounds the actual filled-root quotient
near the compact real gap-root product. Uniform branch stability makes
this bound independent of the deleted index. The positive collar between
the selected inner and outer spectral discs separates every other moving
midpoint. Together with the bounded midpoint displacement, it controls
the lattice-scaled denominator for all deleted indices, including nearby
ones. A finite intersection gives one bound for any finite selected family.
The estimates include collapsed gaps and require no supplied chi bound.

`SourcePsiRefinedActualGapMajorants.lean` patches these central estimates
to the refined tail bounds with a finite-support correction. On one open
source neighborhood, the actual quotient and off-diagonal chi errors on
**every** moving gap are dominated by a common row in every finite `ℓr`
with `r > 1` and `r >= p/2`. The neighborhood precedes the exponent and
deleted index; row norms are uniform in that index. The quotient bound
also includes the selected index equal to the deleted index.

Public checks cover square-summable rows at source exponent four, one
neighborhood for all finite exponents above one at source exponent two,
and the central selected gap zero with arbitrary deleted index.

Next: combine these all-index row bounds with the square estimates and
quantitative moment inequalities. The diagonal still requires a shared
sequence estimate: uniform norms for separate rows do not establish the
sequence of their diagonal entries. Lemma 20.3's final moment sequence
bounds, general infinite-gap frequencies, and the rest of the dissertation
remain unfinished.

## Previous milestone: Refined psi tail exponents on actual complex gaps

`SourcePsiRefinedOffsetExponent.lean` uses the actual squared-gap
root offsets of Lemma 12.12 to construct the midpoint-filled numerator
displacement at every finite exponent above one and at least `p/2`.
A bounded multiplier acts on the squared-gap sequence, followed by the
contractive exponent inclusion, including when `p/2 < 1`. One source
neighborhood and norm bound are chosen before both the deleted index
and the target exponent.

`SourcePsiRefinedQuotientTail.lean` inserts that actual displacement into
Lemma 10.8. It combines the quotient's two error sequences at the target
exponent and bounds their explicit constants on a compact range of the
source norms. The source neighborhood and tail cutoff are independent
of the exponent and deleted index; only the norm bound depends on the
exponent.

`SourcePsiRefinedChiTail.lean` carries the refined exponent through the
midpoint denominator estimate. The added term is a translated reciprocal
lattice whose norm is independent of the deleted index. The theorem uses
the actual normalized psi branch, rather than a supplied root family or
an assumed chi asymptotic.

`SourcePsiRefinedActualGapTail.lean` places every distant moving complex
gap inside its free-centered eighth-pi disc and restricts both estimates
to the actual segments used by the moment formulas. Quotient and chi
row majorants have uniform norms for every finite `r > 1` with `r >= p/2`.
Both share one source neighborhood and cutoff selected before `r` and
the deleted index. Collapsed selected gaps are included.

Public checks cover the gain from source exponent four to exponent two,
actual chi bounds on moving gaps, the half-exponent `3/4` case for a
source exponent of `3/2`, and applicability at collapsed selected gaps.

Next: patch the finite central selected indices uniformly in the deleted
index and combine the tail majorants with the square estimates and the
quantitative moment inequalities. The diagonal still needs a single
sequence estimate; a uniform bound on separate row majorants does not
by itself prove that. Lemma 20.3's final moment sequence bounds, general
infinite-gap frequencies, and the remaining dissertation are unfinished.

## Previous milestone: Quantitative second-moment errors and actual root offsets

`SourceMomentRegularFactorization.lean` identifies the diagonal regular
numerator with `i` times the single-root quotient. Its cross-multiplied
identity remains valid at numerator-root collisions. Filling the omitted
root leaves the numerator unchanged, and the off-diagonal numerator,
scaled by `pi*(n-k)`, factors into the selected root displacement times
the actual midpoint-filled chi factor from Section 12.

`SourceGapCosineError.lean` justifies subtracting continuous model
numerators before integration and proves the normalized supremum error
bound on the actual complex gap. It also proves the quadratic bound
`|P_k| <= |gamma_k|^2/4` and the product estimate with error coefficient
`E*(F+1)+F/4`. `SourceAbelianMomentGapRegularity.lean` supplies all-index
spectral regularity on a common almost-real domain.

`SourceAbelianMomentErrorDomain.lean` combines the actual cosine formulas,
numerator continuity, and gap separation on one connected neighborhood
of the entire real source locus. Its model-error theorem allows arbitrary
constant scaling and continuous comparison numerators. The neighborhood
is chosen before indices and error bounds; these regularity assumptions
are constructed from the normalized psi extension and moment atlas.

`SourceAbelianMomentSecondError.lean` proves the quantitative diagonal
error around `pi*gamma_k^2/4`, retaining two gap factors. Off the diagonal,
the exact leading term of `(n-k)*Omega_nk^(2)` is
`gamma_k^2*(sigma_k^n-tau_k)/4`; the remainder retains three gap factors.
The constants follow from the proved cosine polynomial integrals.

`SourceAbelianMomentSquaredOffsetError.lean` substitutes the actual
squared-gap root offsets from Lemma 12.12, eliminating a separate
root-to-gap-distance assumption. The resulting cubic-gap bound uses the
actual normalized branch's offset coefficients, whose lp norms are
uniform in the deleted index and locally uniform in the source. All
estimates include collapsed gaps and avoid division by gap lengths.

Public checks cover the cross identity at a deleted numerator root,
construction of the common error domain, the exact diagonal coefficient
when errors vanish, off-diagonal cancellation for a midpoint root, and
locally uniform bounds for the actual offset coefficients.

Next: supply mixed `ell^(p/2) + ell^q` majorants for the actual diagonal
quotient and midpoint-filled chi errors and combine them with the proved
square majorants and these quantitative moment inequalities. Lemma
20.3's final sequence estimates, general infinite-gap frequencies, and
the remaining dissertation are unfinished.

## Previous milestone: One complex source neighborhood for every cosine moment

`ParametricCosineMeanSegment.lean` proves analyticity from regularity
along the actual cosine segment, without an enclosing midpoint disc.
At a nonzero half-gap a local analytic square root of its square supplies
a branch, and evenness removes any sign choice. At a zero half-gap the
existing square-descent construction applies on a small disc. The
half-gap selection itself need not be continuous. A local theorem for
jointly analytic interval integrals supplies the parameter regularity.

`SourceGapCosineMeanDomain.lean` applies this result at arbitrary complex
sources on a prescribed common domain. `SourceAbelianMomentUniformCosine.lean`
uses the canonical all-gap Cauchy family and the common symmetric-coordinate
and omitted-product domains to choose a positive source radius before
both indices and the moment order. Real-form continuation then identifies
all positive even moments with their actual cosine integrals on that same
ball, including all open and closed gaps.

`SourceAbelianMomentCosineNeighborhood.lean` assembles these balls into one
open connected neighborhood containing the entire real source locus.
Every positive even cosine formula holds there. The same domain supports
the normalized second-moment bound by the product of a filled-square
bound and a regular psi-factor bound, for every pair of indices. This
removes the index-dependent-neighborhood limitation of the previous step.

Public checks cover a pole outside the actual segment but inside its
centered enclosing discs, a discontinuous half-gap sign selection, a
square-root collision, a radius chosen before both indices, and all-index
second-moment bounds on one connected almost-real domain.

Next: combine these common-domain formulas with the polynomial model and
the square and psi-factor sequence estimates to obtain Lemma 20.3's
uniform diagonal and off-diagonal decay. Those estimates, general
infinite-gap frequencies, and the remaining dissertation are unfinished.

## Previous milestone: Complex-source cosine moment identities and gap bounds

`SourceAbelianMomentRealCosine.lean` extends the real cosine formula to
all positive even orders at closed gaps. The filled square vanishes at
the coincident endpoint, so both the positive moment and its regular
cosine integral vanish. No division by the gap length is used.

`SourceAbelianMomentComplexCosine.lean` constructs all joint regularity
needed by the actual cosine mean from local canonical Cauchy families,
midpoint and squared-gap analyticity, and omitted-product analyticity.
Independence of the primitive's ambient neighborhood transfers the result
to any given moment atlas. The real-form identity theorem then proves the
exact cosine representation of every positive even moment on a complex
neighborhood of every real source in the normalized psi domain. Closed
gaps are included, and no extra spectral regularity premises or analytic
endpoint choices are required.

`SourceGapCosineMeanBound.lean` proves the normalized supremum bound on
the actual complex gap. It gives a source ball on which bounds for the
filled square and regular psi factor multiply to bound the second moment.
The radius is selected before the pointwise bounds, but it may still
depend on the two indices. `SourceGapCosinePolynomial.lean` computes the
exact complex polynomial models: the diagonal term is `pi * gamma_k^2/4`,
and the shifted model retains only the displacement from the midpoint.
Both identities include collapsed gaps.

Public checks cover a nonreal half-gap, cancellation of the centered
linear correction, the normalized constant-numerator estimate, a fourth-
order numerator at a closed gap, complex continuation of the fourth
moment, and the second-moment bound with independently supplied factors.

Next: obtain one source neighborhood for all moment indices, then combine
the exact cosine identities and polynomial models with the square and
psi-factor sequence estimates. Lemma 20.3's uniform decay claims, general
infinite-gap frequencies, and the remaining dissertation are unfinished.

## Previous milestone: Analytic cosine means through closed gaps

`ParametricEvenSquareDescent.lean` constructs a fixed Cauchy integral
whose kernel depends on a squared coordinate. It is jointly analytic
inside the squared contour radius. At `d^2` its exact value is the average
of the original family at `d` and `-d`, including `d=0`. For an even family
this recovers its original value. Consequently an arbitrary square-root
selection may be substituted into an even analytic family whenever its
square is analytic; no continuity of the selected root is required.

`ParametricCosineMean.lean` proves that cosine integration is even in the
half-gap and jointly analytic in an independent half-gap and source
parameter. Square descent then gives analyticity when only the squared
half-gap is analytic. `ParametricCosineMeanLocal.lean` uses a compact
spectral disc to supply the needed common parameter neighborhood. This
local theorem handles endpoint collision without assuming analytic
individual endpoints.

`SourceGapCosineMeanAnalytic.lean` applies the construction to the actual
canonical midpoint and half-gap. A real-centered isolating contour
provides the required midpoint disc. For the normalized psi branch and
canonical filled even-moment numerator, the resulting cosine mean is
analytic at every real source, whether the selected gap is open or closed.
The regular numerator and filled square retain their established joint
analytic domains; the theorem does not introduce endpoint-branch inputs.

Public checks cover exact reconstruction at a double root, an even
polynomial with a parameter, invariance under endpoint exchange, a cosine
mean involving `Complex.sqrt` that is analytic at zero, and the actual
normalized second-moment mean without a nonzero-gap premise.

Next: use this analyticity and the real-gap identities to identify the
complex-source moments with the cosine integral, then combine the square
and psi-factor estimates to finish Lemma 20.3. Its uniform moment decay
claims, general infinite-gap frequencies, and the rest of the
dissertation remain unfinished.

## Previous milestone: Joint filled squares and complex-gap sequence estimates

`SourceFullAbelianSquareGapBound.lean` identifies the square of either
complex gap-side root with the selected quadratic polynomial, and proves
the sharp root bound `norm(w) <= norm(gamma)/2`. Factoring the filled-square
error gives `norm(F^2 + w^2) <= norm(gamma)^2 * E * (E+1)` whenever the
primitive error is bounded by `norm(gamma)*E`. The result includes both
endpoints and collapsed gaps.

`SourceFullAbelianSquareGapMajorants.lean` converts Lemma 19.4's primitive
majorants into the square expansion used in Lemma 20.3. On every point of
every complex gap, the error is bounded by `norm(gamma_k)^2` times the sum
of an `ell^q` and an `ell^(p/2)` majorant. Their norms are locally uniformly
bounded. The same source ball works for all indices and is chosen before
any finite auxiliary exponent `q>1`. Scalar rescaling preserves the
half-exponent space even when `p/2<1`.

`SourceFullAbelianSquareJointAnalytic.lean` proves that the canonical
filled square is jointly analytic in spectral point and source, through
the entire selected moving gap. The Cauchy construction uses only the
analytic midpoint and squared gap, so it needs no analytic choice of
individual endpoints at a collision. A single connected almost-real
source neighborhood carries this joint regularity and the mixed square
error estimates simultaneously.

`SourceAbelianMomentEvenNumeratorJoint.lean` proves joint analyticity of
the regular psi factor and all filled even-moment numerators, including
the actual normalized psi branch. Only the other gaps remain excluded.
These are the analytic integrands needed to extend the real-gap formulas.

Public checks cover side independence, the sharp half-gap constant,
exact square cancellation when the primitive error vanishes, normalized
numerator regularity, and the concrete exponent `p=3/2`, where the second
majorant lies in `ell^(3/4)` without a Banach-space assumption.

Next: finish the complex-gap moment integral formula and combine the
square expansion with the psi factor asymptotics to obtain Lemma 20.3's
off-diagonal cubic-gap decay and diagonal leading term. Lemma 20.3,
general infinite-gap frequencies, and the rest of the dissertation
remain unfinished.

## Previous milestone: Real gap integrals and leading terms for Lemma 20.3

`SourceAbelianMomentEvenNumerator.lean` factors every even-order raw
moment into the canonical filled square power times the regular psi
numerator, divided by the selected standard root. The identity holds for
complex sources on the root domain and on every admissible circle. Its
numerator is analytic through the selected gap and both endpoints. At
real sources this regularity requires no supplied Cauchy family or
omitted-product analyticity assumption.

`SourceStandardRootWeightedRealCircleBoundary.lean` shrinks any
real-centered enclosing circle to its selected open real gap. The
numerator may be complex valued. The orientation gives minus twice the
upper-side integral, and the normalized contour is bounded by the
attained maximum of the numerator on the gap.

`SourceAbelianMomentRealGapIntegral.lean` applies this to the actual
glued normalized moments at every real source, without a finite-gap
restriction. All even orders have exact gap-side and nonsingular cosine
integral formulas at open gaps. The second-moment gap-side formula also
holds at collapsed gaps, where both sides vanish. Separate gap bounds
`M` for the filled square and `B` for the regular psi factor give
`norm(Omega_nk^2/(2*pi)) <= M*B`, including collapsed gaps.

`SourceStandardRootGapSidePolynomial.lean` evaluates the leading
polynomial side integrals for arbitrary complex midpoint and gap. On the
lower side, the quadratic root polynomial has integral
`i*pi*gamma^2/8`; multiplying by the centered factor `tau-lambda`
gives zero; multiplying by `sigma-lambda` leaves exactly
`i*pi*gamma^2*(sigma-tau)/8`. These identities include zero gaps.

Public checks cover the complex-source weighted representation, the
real second-moment formula without an open-gap premise, the cosine
representation, the product bound, and the three leading constants.

Next: extend the moment contour-shrinking estimates to the common
complex source neighborhood and combine the established primitive and
psi asymptotics to prove Lemma 20.3's locally uniform sequence bounds.
Lemma 20.3 is not yet complete; general infinite-gap frequencies and
the rest of the dissertation remain unfinished.

## Previous milestone: Lemma 20.2 including closed finite-gap actions

`RealActionOpening.lean` opens one zero Birkhoff coordinate with amplitude
`t`, giving exactly the action `t^2/2`. It also identifies action reduction
on that ray with its scalar square-root change of amplitude.
`SourceHilbertGapOpening.lean` pulls this line back through the actual
global analytic Birkhoff inverse. The source curve is analytic, preserves
all unselected actions and closed-gap status, and stays in the original
finite gap support together with the selected index. Every nonzero
amplitude opens an initially collapsed selected gap.

`SourceFiniteGapOpeningHamiltonian.lean` proves that physical `H3` is
analytic along any analytic real source curve with fixed finite gap
support. The proof uses one locally valid physical contour and the
original source mass. Along the opening line it obtains the exact
identity `H3'(t)=t*omega_n(t)` for nonzero amplitudes, by comparing with
the actual action-reduction curve.

`AmplitudeDerivativeLimit.lean` proves the scalar calculus step: an
analytic physical energy with `H'(a_k)=a_k*omega_k`, where nonzero `a_k`
tend to zero and `omega_k` converges, has `H'(0)=0` and `H''(0)` equal
to that frequency limit. `SourceFiniteGapClosedFrequency.lean` applies
this to the explicit amplitudes `1/(k+1)`. The corresponding sources
converge in the Hilbert source norm and have fixed finite gap support.
Continuity of the moment sum and physical mass identifies the limit
with the physical second amplitude derivative. The closed frequency
is defined by that derivative, without a moment input.

`SourceFiniteGapLemma20_2.lean` combines the physical first action
derivative at open gaps and second amplitude derivative at closed gaps.
For every real finite-gap Hilbert source and every integer index it proves
`omega_n - 4*H1 - (2*n*pi)^2 = -4/(2*pi)*sum_k Omega_nk^2`.
The resulting frequency is independent of the chosen Birkhoff data.
At the all-closed zero source it recovers exactly `(2*n*pi)^2`.
Thus the physical finite-gap Hilbert version of Lemma 20.2 now covers
all selected indices. The closed-gap proof uses analyticity of the
physical energy on the explicit finite-support curve; it does not assume
a general Sobolev frequency-continuity theorem.

Public checks cover the all-index identity, the physical second-derivative
definition, convergence of the actual open frequencies to the closed
frequency, and the nonzero free frequency `4*pi^2` in mode one.

Next: Lemma 20.3's locally uniform second-moment decay estimates on the
common complex source neighborhood. Frequencies on general infinite-gap
sources and the rest of the dissertation remain unfinished.

## Previous milestone: Physical frequency formula at open finite-gap actions

`SourceFullAbelianPhysicalContourLocal.lean` proves that every positive
circle enclosing all open gaps has the physical cubic-contour value
`H3-2*H1^2`. Annular deformation removes the point-dependent asymptotic
radius. Finite endpoint continuity gives one fixed contour on nearby
real sources with fixed finite gap support. Arbitrarily large admissible
circles enclosing a prescribed finite gap family are constructed.

`SourceHilbertActionReductionFiniteGap.lean` proves that the actual
Birkhoff action-reduction curve remains finite-gap at every time,
including collapse, and preserves all unselected closed gaps. With an
open selected gap it introduces no new open-gap index. The first
physical Hamiltonian is the source mass and decreases exactly by the
curve parameter before collapse.

`SourceFiniteGapOpenFrequency.lean` evaluates the physical Appendix H
hierarchy along that source curve. A fixed contour identity on a whole
time neighborhood now justifies differentiation: the derivative of
physical `H3` is minus the cubic contour's angle bracket minus `4*H1`.
The open-action frequency is defined as minus this physical derivative,
not by a contour or moment formula. The module proves
`omega_n - 4*H1 - (2*n*pi)^2 = -4/(2*pi)*sum_k Omega_nk^2`
for real finite-gap Hilbert sources with an open selected gap. The final
formula accepts any normalized moment atlas, constructs the required
angle and primitive data internally, and compares their different
source neighborhoods and psi branches. The physical frequency is
independent of the chosen Birkhoff data.

Public checks use the physical derivative definition, all-time finite-gap
preservation, the moment formula without supplied angle/primitive data,
and independence across Birkhoff realizations.

Lemma 20.2 is not complete: the selected closed-gap case still needs a
physical frequency extension/continuity theorem and a finite-gap opening
approximation in the required topology. The present physical frequency
interface is for open actions in the Hilbert source space. The
dissertation as a whole remains unfinished.

## Previous milestone: Finite-gap moment contour decomposition

`FilledSimpleQuotient.lean` fills a quotient at simple denominator zeros
with the ratio of derivatives and proves analyticity when the numerator
also vanishes. The filled value is not the literal quotient's default
zero at a denominator zero.

`SourcePsiOpenGapQuotient.lean` proves that the actual canonical root has
a simple zero at every collapsed real gap, and that the normalized psi
numerator vanishes there whenever the gap differs from its deleted index.
For an open selected gap, the filled psi quotient is analytic on the
complement of all open gaps. This holds at every finite exponent `p>1`,
without a finite-gap hypothesis.

`SourceAbelianMomentFiniteGapContour.lean` applies Cauchy's theorem on a
disc with finitely many holes. At a real finite-gap source, every
sufficiently large circle avoiding the gaps decomposes into the atlas
circles around precisely the open gaps. One threshold works for all open
selected indices, primitive normalization indices and moment orders.
The existing quadratic shift then yields
`-4/(2*pi)*integral F_0^2*psi_n/root - (2*n*pi)^2 = -4/(2*pi)*sum_k Omega_nk^2`.
Combining this with the actual angle derivative gives the same moment
sum for the cubic contour's angle bracket, using compatible primitive,
angle and moment data for `p>=2`.

Public checks cover a nonzero filled value at a common zero, analyticity
at collapsed gaps for arbitrary finite `p>1`, the large-circle formula at
`p=3`, and the actual angle-bracket formula at `p=2`.

Lemma 20.2 remains unfinished: the contour bracket must still be
identified with the physical NLS frequency, and the selected closed-gap
case needs the finite-gap approximation and frequency-continuity
argument. The dissertation as a whole remains unfinished.

## Previous milestone: Angle derivative of the cubic contour

`SourceFullAbelianDifferentialData.lean` constructs an open joint domain
for the actual full primitive and its exact differential near every real
source. It supplies the source cotangent as the discriminant cotangent
divided by the canonical root, at every finite exponent `p>1`.

`SourceFullAbelianAnglePoisson.lean` combines this differential with the
established angle/discriminant identity. At a real source with an open
selected angle gap, `{theta_n,F_j}` is exactly `-psi_n/(2*canonicalRoot)`
for every primitive normalization index. The power chain rule gives
`{theta_n,F_j^(m+1)} = -(m+1)/2 * F_j^m * psi_n/canonicalRoot`.
These Poisson identities use the existing source bivector for `p>=2`.

`SourceBracketCircleIntegral.lean` proves that pairing a fixed source
cotangent with the derivative of a jointly analytic contour integral
commutes with the integral. Compactness provides the local uniform
derivative bound; the Hamiltonian-direction evaluation fixes the sign.

`SourceFullAbelianCubicContourPoisson.lean` defines the scaled cubic
contour functional `(8/(6*pi))*integral F_0^3`, proves its local source
analyticity, and obtains the exact identity
`{theta_n,cubicContour} = -4/(2*pi)*integral F_0^2*psi_n/canonicalRoot`.
It also retains the physical value `H3-2*H1^2` on sufficiently large
circles at real finite-gap sources, using the same ambient primitive.
An existence theorem constructs the normalized psi, angle and primitive
data internally for every finite exponent `p>=2`; no supplied chart or
differential formula is required.

Public checks extract both the actual bracket and physical contour value
in the Hilbert case, compare brackets for different primitive normalization
indices, and recover the source cotangent below the Hilbert exponent at
`p=3/2` without imposing an unavailable Poisson pairing there.

Lemma 20.2 remains unfinished. A pointwise physical value of the cubic
contour at finite-gap sources is not yet an identification of its angle
bracket with the NLS frequency. Remaining work includes that frequency
identification, the large-circle finite-gap decomposition of the quadratic
integrand, and the approximation/continuity argument when the selected
gap collapses. The dissertation as a whole remains unfinished.

## Previous milestone: Contour and finite-sum steps toward Lemma 20.2

`CubicInversionContour.lean` extracts the exact contour coefficient
from the analytic inverse-frequency cubic expansion. The analytic
quadratic remainder has zero period, leaving
`integral F^3 = (3*pi/4)*(H3-2*H1^2)` on every sufficiently large circle.

`SourceFullAbelianCubicHamiltonianContour.lean` applies this to the actual
full primitive and physical finite-gap Hamiltonians, proving the first
identity used in Lemma 20.2:
`H3-2*H1^2 = (8/(6*pi))*integral F_0^3`.
It holds at every finite `p>1` and every real finite-gap source. The
formula is also transported to any existing spectral chart, so it can
use the same ambient primitive as the normalized moment atlas.

`SourceAbelianMomentFiniteSums.lean` proves that one finite set of actual
open gaps supports all positive-order moment rows at a finite-gap source.
The sums have genuine `HasSum` witnesses and equal the corresponding
finite sums. If a convergent family has its open gaps eventually confined
to one finite set, its total positive-order moment sums converge. The
limiting gaps may collapse; no fixed nonvanishing-gap hypothesis is needed.

`SourceAbelianMomentQuadraticShift.lean` expands `F_0 = F_k-i*k*pi` inside
the actual contour integral. The first moment vanishes and the zero-order
period supplies the Kronecker correction. On any finite gap support
containing the selected index, multiplying the summed unshifted contours
by `-4/(2*pi)` and subtracting `(2*n*pi)^2` gives exactly
`-4/(2*pi)` times the full quadratic-moment sum.

Public checks at `p=3/2` recover the physical cubic contour formula with
and without an existing moment atlas, prove quadratic-moment summability,
pass to a source limit with gaps supported in `S union {n}`, and specialize
the quadratic contour correction to the zero lattice index.

Lemma 20.2 remains unfinished. The remaining work is to identify the
actual Hamiltonian frequency with the unshifted quadratic contour via
the angle/discriminant Poisson identity, justify the large-circle
finite-gap decomposition for that integrand, and supply the finite-gap
approximation and frequency continuity for a collapsed selected gap.
The contour algebra and moment-sum limit proved here do not assume or
define the frequency formula. The dissertation as a whole remains unfinished.

## Previous milestone: Lemma 20.1 on a common source neighborhood

`SourceAbelianMomentContourHomotopy.lean` proves invariance under smooth
gap-avoiding contour deformations, with concrete comparisons for nested
circles and circles inside a common outer isolating disc. Moments also
remain unchanged when the primitive's ambient neighborhood is changed.
`SourceAbelianMomentRealContourComparison.lean` compares arbitrary valid
real-centered circles at real sources, even from different disc families.

`SourceAbelianMomentLocalChart.lean` constructs actual normalized moment
charts near every real potential. Each chart has one positive source
radius and one fixed all-index circle family supporting every moment
order. Analytic continuation of the real normalization proves the exact
zero-order periods throughout the complex source ball. All odd moments
and all positive-order moments at collapsed gaps vanish on that same ball.

`SourceAbelianMomentAtlas.lean` uses the real-form identity theorem to
prove agreement on full complex source-ball overlaps and glues the local
integrals. The resulting moments are analytic and have one simultaneous
contour representation for every numerator, gap index, and order.
Their values are independent of the local atlas and of the ambient
primitive neighborhood on common source domains.

`SourceAbelianMomentDomain.lean` contracts the union of the source balls
to the real locus and then to zero, proving the moment domain simply
connected. `SourceAbelianMomentLemma20_1.lean` assembles all four clauses:
`Omega_nk^0 = 2*pi*delta_nk`, analyticity, odd-order vanishing, and
positive-order vanishing when `gamma_k=0`. The common open neighborhood
contains every real source and works for all indices and orders at
every finite exponent `p>1`. The numerator is the actual normalized psi
branch and the primitive is the actual full Abelian primitive.

Public checks at `p=3/2` extract the simultaneous contour representation,
diagonal/off-diagonal normalization, cubic vanishing, and collapsed-gap
quadratic vanishing. Additional checks compare distinct atlases and
primitive neighborhoods and deform an even moment between nested circles
at a complex potential.

Lemma 20.1 is complete. Next is Lemma 20.2: express the renormalized NLS
frequency at a finite-gap real potential as `-4/(2*pi)` times the sum of
its quadratic moments. The dissertation as a whole remains unfinished.

## Previous milestone: Section 20 moments on isolating circles

`SourceAbelianMomentCircle.lean` defines the Section 20 moments as raw
circle integrals of `F_k^m * psi_n / canonicalRoot`. The primitive uses
the integration-gap index, independently of the numerator index. For
the actual normalized psi branch, one isolating circle family has
zero-order moments exactly `2*pi*delta_nk`, including the omitted index.

`SourceAbelianMomentCircleAnalytic.lean` proves joint analyticity in
numerator-root coefficients and the source on a fixed admissible circle.
Compactness supplies a parameter neighborhood from admissibility at a
single source. Composition with the normalized psi branch gives source
analyticity for every moment order.

`SourceAbelianMomentCancellation.lean` cancels one selected standard
root using the actual primitive's Cauchy representation. Its analytic
square handles the remaining even powers. At a collapsed gap the
standard root is linear, so every positive-order integrand extends
across the filled disc. `SourceAbelianMomentCircleVanishing.lean` applies
Cauchy's theorem to prove odd-order vanishing and collapsed-gap
positive-order vanishing on all intermediate isolating circles. The
argument includes both diagonal and off-diagonal numerator indices.

`SourceAbelianMomentLocalVanishing.lean` supplies the omitted-product
analyticity from its established joint extension. Near every real
source, one open neighborhood supports these vanishing identities for
all indices, numerator coefficients, orders, and intermediate radii.
Public checks at `p=3/2` recover the actual diagonal and off-diagonal
zero-order periods, choose concrete positive radii for all vanishing
identities, and differentiate an even moment on the omitted-index circle.

This is the fixed-circle foundation for Lemma 20.1. Still to do:
prove independence of admissible isolating contours, define the global
normalized moments, and assemble all four clauses on a common almost-real
source neighborhood. Lemma 20.1 and the dissertation remain unfinished.

## Previous milestone: Lemma 19.4 on one almost-real neighborhood

`SourceFullAbelianCentralGapBound.lean` bounds the Cauchy-quotient
error on compact inner discs, using joint analyticity and one local
source restriction. A finite collection of central gaps therefore has
one bound proportional to each gap length, including collapsed gaps.

`SourceCriticalFactorAllExponents.lean` strengthens the deleted-factor
estimate by choosing the neighborhood and index threshold before the
auxiliary exponent. `SourceFullAbelianGapAllExponentTails.lean` preserves
that quantifier order for the actual primitive error. Only the majorant
sequences and their common norm bound may depend on `q>1`. The earlier
fixed-exponent tail theorem is now a corollary of this stronger result.

`SourceFullAbelianAllGapMajorants.lean` absorbs the central gaps into a
finitely supported nonnegative correction to the auxiliary `l^q`
majorant. It proves the mixed estimate at every signed index, with no
remaining tail cutoff, on both sides of every closed complex gap.

`SourceFullAbelianRefinedGapBound.lean` completes Lemma 19.4. One open
connected almost-real neighborhood supports joint analyticity and,
locally uniformly at every complex source in that neighborhood,
`|F_n-i*w_n| <= |gamma_n|*(|Bq_n|+|Bg_n|)`.
Here `Bq` belongs to any finite `l^q`, `q>1`, and `Bg` belongs to
`l^(p/2)`; both sequence norms have a common local bound. The ambient
neighborhood and local source radius are independent of `q`. The theorem
uses actual limits on both sides of noncollapsed gaps, covers endpoints,
and uses the actual filled error at collapsed gaps. It also includes
`F_n(z,0)=i*w_n(z,0)=-i*z+i*pi*n` at every complex frequency.

Public checks specialize the all-index midpoint limits to `p=3/2`,
retaining a common ball for all auxiliary exponents, and recover the
free endpoint values without a caller-supplied chart.

Lemma 19.4 is complete. The next step is Section 20: define the moments
`Omega_nk^(m)` using the actual normalized primitive and normalized
spectral differential, then prove their normalization, analyticity,
odd-moment vanishing, and collapsed-gap vanishing in Lemma 20.1.
The dissertation as a whole remains unfinished.

## Previous milestone: Mixed sequence majorants for the gap error

`QuasiHolderProduct.lean` constructs scalar coefficient products for
any Holder triple and proves the norm bound at all positive finite
exponents, including targets below one.

`SourceCriticalHalfExponentOffsets.lean` places both the actual
critical-midpoint offset `gamma_n^2*q_n` and its normalized form
`gamma_n*q_n` in `l^(p/2)`. Their norms are bounded on a common source
neighborhood. The critical-point identities are exact at every signed
index and remain meaningful when a gap collapses.

`SourceCriticalFactorDiscMajorants.lean` specializes Lemma 10.8 to the
actual canonical critical sequence. On distant free discs, the error
`chi_n-1` is bounded by `|Bq_n|+|Bg_n|`, with `Bq` in any finite `l^q`,
`q>1`, and `Bg` in `l^(p/2)`. One constant bounds both sequence norms
for every source in the same neighborhood. When `p/2<=1`, contractive
inclusion into `l^1` uses the endpoint version of Lemma 10.8. When
`p/2>1`, the two half-exponent majorants combine directly.

`SourceFullAbelianGapTailMajorants.lean` transfers these estimates to
the actual primitive. Near every real source, one neighborhood, index
threshold, and sequence-norm bound give
`|F_n-i*w_n| <= |gamma_n|*(|Bq_n|+|Bg_n|)`
on both sides of every sufficiently distant closed complex gap.
The same majorants cover every angle and every compatible Cauchy chart.
No primitive or deleted-factor asymptotic estimate is assumed.

Public checks exercise multiplication below exponent one at `p=3/2`,
the exact critical-offset factorization there, and the normalized
primitive error at `p=4` with the smaller auxiliary exponent `q=3/2`.

Lemma 19.4 is not yet complete. The remaining work is to control
the finitely many central gaps and assemble the result on an open
almost-real neighborhood, using the already proved side limits and
collapsed-gap identities. The dissertation as a whole remains unfinished.

## Previous milestone: Quantitative gap comparison for Lemma 19.4

`QuadraticPrimitiveGapComparison.lean` subtracts a constant from the
analytic Cauchy quotient and bounds the resulting boundary error by the
linear-numerator defect. The proof uses the cosine-parametrized quadratic
equation and never divides by the gap length.

`SourceFullAbelianGapComparison.lean` applies this estimate to the actual
primitive and the standard root. It constructs both root boundary values,
proves both side limits of `F_n-i*w_n`, and bounds the error by
`pi * (D*E + |critical_n-midpoint_n|)`, where `D` bounds the critical-point
distance on the gap and `E` bounds the deleted factor's error from `-i`.
That factor error has exactly the norm of `chi_n-1` from Lemma 10.8.
The filled error is zero at every collapsed gap. The zero-potential clause
of Lemma 19.4 is proved exactly at every complex spectral parameter.

`SourceFullAbelianUniformGapComparison.lean` supplies one neighborhood
of each real source and one positive constant `A` such that, on both
sides of every closed complex gap,
`|F_n-i*w_n| <= pi*|gamma_n|*(A*E_n + |gamma_n|*|q_n|)`.
Here `q_n` is the actual squared-gap critical quotient from Lemma 10.10,
whose full `lp` norm is bounded uniformly on that same neighborhood.
The estimate applies to every compatible Cauchy chart, every gap index,
and both endpoints, including collapsed gaps.

Public checks cover the free identity at arbitrary complex frequencies,
the actual filled error at collapsed complex gaps, and exact agreement
on both sides when the deleted-factor error and critical offset vanish.

Lemma 19.4 is not yet complete. The next step is to specialize the
Lemma 10.8 majorants to the critical sequence and place the normalized
boundary error in `l^(p/2) + l^(1+)`, locally uniformly on an almost-real
neighborhood. The dissertation as a whole remains unfinished.

## Previous milestone: Corollary 19.3 with a uniform cubic remainder

`CubicInversionRemainder.lean` proves the exact algebraic cubic expansion
of a normalized analytic inversion phase. Its error is `z^-2 * B(1/z)`
with `B` analytic at zero, giving a positive constant and an exterior
radius on which the error is at most `K/|z|^2` in every complex direction.

`SourceFullAbelianHamiltonianInversion.lean` records the actual normalized
finite-gap inversion phase together with all its physical Hamiltonian
Taylor derivatives. The phase and coefficients are derived from the
existing source construction and the smooth Fourier realization.

`SourceFullAbelianCubeAsymptotics.lean` proves Corollary 19.3:
`F_0(z)^3 = i*z^3 - (3*i/2)*H_1*z - (3*i/4)*H_2
- (3*i/8)*(H_3 - 2*H_1^2)/z + O(z^-2)`.
Here each `H_k` is the physical Appendix H Hamiltonian of the original
finite-gap source. The factor `3/8` multiplies the whole parenthesis,
as checked directly on PDF page 91.

The result includes analyticity outside a disc, an explicit uniform
quadratic error bound, and the literal `IsBigO` statement at complex
infinity. The same bound works for every normalization index after
subtracting `i*pi*n`. A common open neighborhood of the real source
locus supplies the zero-index corollary at every real finite-gap source
for every `1 < p < infinity`, without additional asymptotic hypotheses.

Public checks verify the positive mass-squared cross term using the
exact model `F(z) = -i*z + i/z`, test the placement of the `3/8` factor,
and specialize the printed big-O expansion to an actual `p=3` source.

Corollary 19.3 is now proved. The next step is Lemma 19.4, the refined
comparison between the gap boundary primitive and `i*w_n`, including
its locally uniform sequence-space error. The dissertation as a whole
remains unfinished.

## Previous milestone: Lemma 19.2 with the actual physical Hamiltonians

`PeriodOneSmoothSynthesis.lean` proves that all Sobolev weights at any
finite Banach exponent give a smooth period-one Fourier representative.
It constructs the absolutely summable derivative series and differentiates
at every real point, including period endpoints.

`SourceFiniteGapSmoothRealization.lean` applies the existing finite-gap
Sobolev bootstrap to the original source coefficients. The resulting
pair is smooth and periodic, its Fourier integrals recover every original
coefficient, and its classical discriminant equals the canonical source
discriminant. Exponent compatibility and the coefficient-preserving
Hilbert realization establish this identity for every `1 < p < infinity`.
No smooth representative or trace identity remains as a premise.

`SourceFiniteGapNLSHamiltonians.lean` evaluates the Appendix H differential
hierarchy on this actual Fourier representative. Its first Hamiltonian
is proved equal to the original reflected source pairing
`sum_k phi_-(k)*phi_+(-k)`.

`SourceFullAbelianHamiltonianLaurent.lean` completes Lemma 19.2: every real
finite-gap source has an exterior analytic primitive and the convergent
Laurent expansion with these physical Hamiltonians. The zero-index
formula is `F_0(z) = -i*z + sum_{k>=1} i*H_k/(2*z)^k`; all other indices
have exactly the prescribed additive constant `i*pi*n`. The series holds
in every complex direction outside one sufficiently large disc. A single
open neighborhood of the real source locus supplies the statement for
all real finite-gap sources, with no caller-supplied chart, regularity,
classical realization, asymptotic estimate, or coefficient identification.

Public checks cover the smooth coefficient-preserving realization at
`p=3/2`, the original mass normalization at `p=3`, and the complete
zero-index Hamiltonian series at arbitrary large complex frequencies.

Lemma 19.2 is now proved with its physical Hamiltonian coefficients.
The next step is Corollary 19.3, the expansion of `F_0^3` through its
inverse-frequency term with a quadratic remainder. The dissertation as
a whole remains unfinished.

For Corollary 19.3, the printed formula on PDF page 91 is
`F_0(z)^3 = i*z^3 - (3*i/2)*H_1*z - (3*i/4)*H_2
- (3*i/8)*(H_3 - 2*H_1^2)/z + O(z^-2)`.
The factor `3/8` multiplies the entire parenthesis. Here the printed
energy `H` is the third Appendix H Hamiltonian. This placement was
checked directly in the PDF and agrees with cubing the Laurent series.

## Previous milestone: Hamiltonian coefficient identification from the discriminant

`LocalSinhComparison.lean` proves a quantitative local inverse estimate
for complex hyperbolic sine. At real zeros of cosine, the discriminant
error therefore controls the small phase error with no inverse-branch
choice. `SampledAnalyticOrder.lean` proves that a bound along any nonzero
sequence tending to zero forces the corresponding analytic vanishing
order and vanishing Taylor derivatives.

`NLSHamiltonianPhasePolynomial.lean` expresses the finite Hamiltonian
phase as a polynomial in inverse frequency and computes every Taylor
coefficient. `NLSHamiltonianPrimitiveCoefficients.lean` combines the
actual classical discriminant estimate with the sequence
`pi*(j+1/2)`. For a normalized analytic inversion phase `A` satisfying
the exact discriminant identity, it proves
`A^(k+1)(0) = (k+1)! * i*H_(k+1)/2^(k+1)` for every `k`.
The resulting Hamiltonian series converges near zero, and the Laurent
series converges in every complex direction outside a sufficiently
large disc. No higher coefficient or asymptotic estimate for the
primitive is assumed.

`SourceFullAbelianHamiltonianReduction.lean` proves the exact identity
`2*cosh(F_0) = Delta` for the actual real-source primitive throughout
the open-gap complement, including filled collapsed endpoints. It then
uses the established finite-gap inversion remainder to obtain the
Hamiltonian Laurent series for every normalization index whenever a
smooth periodic classical potential with the same discriminant is
supplied. This last realization hypothesis is explicit.

Public checks cover Taylor derivatives detected from sparse samples,
the third coefficient expressed through the physical energy integral,
and the empty phase correction.

The next step is to construct the required smooth periodic physical
realization from finite-gap Sobolev regularity and prove its discriminant
agreement. This will discharge the remaining realization hypothesis;
Lemma 19.2 in its full source formulation and the dissertation remain
unfinished.

## Previous milestone: actual monodromy and Hamiltonian discriminant asymptotics

`NLSWKBComparison.lean` compares the finite Hamiltonian approximation
with the actual initial-value solution having the same initial vector.
At every order `N`, their difference is bounded by `C/(2*|r|)^N`,
uniformly over the whole physical period and both directions of the
real spectral axis with `|r| ≥ 1`. Periodicity then gives an actual
monodromy approximate-eigenvector estimate with the finite Hamiltonian
sum in the multiplier.

`ClassicalResidualStability.lean` proves a general forcing-to-solution
error estimate using the true determinant-one fundamental matrix and
its adjugate variation-of-constants formula. The resulting stability
constant on the real spectral axis is independent of the spectral
parameter. `NLSWKBCarrierBounds.lean` bounds both the approximate
carrier and its reciprocal uniformly on that axis.

`UnimodularTraceError.lean` converts a normalized approximate eigenvector
into a trace estimate for a determinant-one two-by-two matrix.
`NLSHamiltonianDiscriminantAsymptotics.lean` applies it to the actual
monodromy: for every smooth periodic complex potential and every `N`,
`|Delta(r) - 2*cos(i*sigma_N(r))| ≤ C/(2*|r|)^N`, where
`sigma_N(r) = -i*r + sum_{k=1}^N i*H_k/(2*r)^k` uses the physical
Appendix H Hamiltonians. No asymptotic formula is supplied as a premise.

Public checks cover exact recovery when the forcing vanishes, negative
real frequencies at interior spatial times, and the explicit first three
Hamiltonian factors in the actual discriminant estimate.

The all-order classical discriminant asymptotics used in Lemma 19.2 are
now proved. The next steps are to connect smooth physical representatives
to the finite-gap source and extract the normalized primitive's Laurent
coefficients from these asymptotics. The full lemma and dissertation
remain unfinished.

## Previous milestone: all-order Riccati and spectral-system residual bounds

`NLSRiccatiTruncation.lean` proves exact cancellation at every order:
the residual polynomial of the first `N` Riccati terms is divisible
by `X^N`. No smoothness hypothesis is needed for this algebraic result,
and the empty truncation is included.

`PolynomialFunctionBounds.lean` turns that divisibility into a uniform
power bound for polynomials with continuous spatial coefficients.
`NLSRiccatiResidualBounds.lean` applies it to actual finite Riccati
approximations. For smooth potentials and every `N`, a positive constant
bounds the differential residual by `C/(2*|z|)^N`, uniformly over one
spatial period and every complex direction with `|z| ≥ 1`. The constant
may depend on the potentials and `N`. The approximation itself is
uniformly first order in inverse frequency.

`NLSWKBApproximation.lean` constructs a nonvanishing exponential carrier
and a two-component approximate solution of the original Zakharov–Shabat
system. Its exact forcing term is the evaluated residual polynomial.
The norm of the spectral-system residual is bounded by
`C/(2*|z|)^N` times the carrier's norm. For periodic potentials, the
approximation has an exact endpoint multiplier with exponent
`-i*z + sum_{k=1}^N i*H_k/(2*z)^k`.

Public checks cover the empty truncation, the nonzero quadratic residual
for constant potentials, the factors 2, 4, and 8 in the first three
Hamiltonian terms, and the fourth-order spectral-system estimate.

The next step is to compare this approximation with the actual
fundamental solution and monodromy, then use the resulting asymptotics
to identify the higher Laurent coefficients in Lemma 19.2. The residual
bounds do not yet establish that identification. The full lemma and
dissertation remain unfinished.

## Previous milestone: physical Riccati hierarchy and Hamiltonian normalization

`NLSRiccatiHierarchy.lean` implements Appendix H's full recursive
density sequence, beginning with `u₁ = -φ₊` and
`u_(k+1) = ∂x u_k + φ₋*sum(u_(k-l)*u_l)`. It proves uniqueness of
all coefficients, smoothness at every order, and the exact formal
Riccati generating-series identity.

The same module proves that `i*y₂/y₁` for the actual classical
Zakharov–Shabat solution satisfies the corresponding Riccati equation
where `y₁` is nonzero. Its first component's logarithmic derivative
is `-i*z + φ₋*(i*y₂/y₁)`, connecting the hierarchy to the original
spectral equation with the exact signs.

`ClassicalNLSHamiltonians.lean` defines the physical positive-index
Hamiltonians by the Appendix H integrals. Every density preserves
periodicity and is integrable for smooth potentials. Integration by
parts proves that `H₁` is the existing physical mass, `H₂` is the
symmetrized momentum, and `H₃` is the NLS energy
`integral(φ₋' * φ₊' + φ₋² * φ₊²)`. At every order, the integrated
Riccati term has exactly the factor `i*H_k/(2*z)^k` from Lemma 19.2.

Public checks verify nonzero constant potentials, the positive quartic
energy term, smooth periodic densities at arbitrary order, and the
third-order factor `i*H₃/(8*z³)`.

These are the physical hierarchy and formal expansion needed for the
remaining coefficients of Lemma 19.2. Quantitative remainder estimates
and the identification with the actual convergent finite-gap Laurent
series remain to be proved. The full lemma and dissertation are unfinished.

## Previous milestone: first Laurent coefficient equals the source mass

`SourceFullAbelianMassCoefficient.lean` identifies the first coefficient
in the actual finite-gap Laurent expansion with `i*H₁/2`, where `H₁` is
the original Fourier mass pairing `sum φ₁(k)*φ₂(-k)`. The result holds
at every finite exponent above one, with one coefficient sequence and
one exterior radius for all signed primitive indices. At exponent two,
this coefficient is exactly `i*‖φ‖²/4` in the Hilbert pair norm.

The same module proves the all-direction limit
`z*(F_n(z)+i*z-i*pi*n) → i*H₁/2`. It constructs an analytic inversion
remainder with derivative `i*H₁/2` at zero, using the existing normalized
remainder limit to fix the integration constant. One ambient source
neighborhood supports the mass-calibrated convergent series at every
real finite-gap source.

`SourceFiniteGapMassExponent.lean` proves that exponent inclusion
preserves both the finite-gap property and the filled Floquet logarithmic
derivative. Every real finite-gap source has a coefficient-preserving
finite-gap Hilbert model. This establishes absolute convergence of its
original mass pairing and transfers the previously proved Hilbert
exterior mass formula to all finite exponents above one.

`ExteriorInversionRemainder.lean` now retains the first Taylor coefficient
in its positive-power series theorem and recovers it through the scaled
inversion limit. Public checks cover exponents 3/2, 2, and 3, the negative
primitive index -2, and the exact real and imaginary parts of the Hilbert
mass coefficient.

The mass term in Lemma 19.2 is now identified. Identification of the
higher Laurent coefficients with the remaining NLS Hamiltonians is the
next step; the full lemma and dissertation remain unfinished.

## Previous milestone: normalized convergent finite-gap Laurent expansion

`SourceFullAbelianFiniteGapLaurent.lean` proves a convergent Laurent
series for the actual full primitive at every real finite-gap source:
`F_n(z) = -i*z + i*pi*n + sum (a_k / z^(k+1))` outside one positive
radius. The same coefficients and radius work for every signed index.
The theorem provides `HasSum`, not merely a formal series or a bound.
The normalized remainder tends to zero in every direction at infinity.

`ExteriorInversionRemainder.lean` integrates an analytic quadratic
inverse-frequency derivative remainder on the whole connected exterior.
It obtains `F(z) = -i*z + A(1/z) + c`, with `A` analytic near zero and
`A(0) = 0`, and proves the positive-power series for `A`.

`SourcePeriodicEndpointAtInfinity.lean` proves that the actual left
periodic endpoints escape to infinity and their displacements from
`pi*n` tend to zero at every finite exponent. In
`SourceFullAbelianFiniteGapInversion.lean`, all sufficiently distant
finite-gap endpoints are collapsed and have their already-proved exact
primitive values. These values force the integration constant `c` to
vanish. No asymptotic normalization is supplied as an extra hypothesis.
The signed index shift then gives one common analytic remainder for
all `F_n`.

Public checks express the actual primitive as its convergent sum at
exponent 3/2, verify the analytic remainder's zero constant term for
index -3, and check the all-direction remainder limit for index -2.

The analytic expansion and its normalization in Lemma 19.2 are now
proved. Identification of the coefficients with the NLS Hamiltonians
is still required before the full lemma is complete, starting with the
mass coefficient. Later frequency results and the full dissertation
remain unfinished.

## Previous milestone: real boundary formula and finite-gap exterior

`SourceFullAbelianRealBoundary.lean` transfers Lemma 19.1(v) to the full
canonical primitive. At every point of every closed real gap, arbitrary
upper-half-plane approaches give the positive real arcosh profile and
lower-half-plane approaches give its negative. Endpoints and collapsed
gaps are included. For primitive index `m` on gap `n`, the exact added
constant is `i*pi*(m-n)`. One ambient neighborhood supports these formulas
for every real source and the exact free formula of Lemma 19.1(vi).

The same module proves that the full primitive has the regular Floquet
logarithmic derivative throughout the real-source spectral domain,
including collapsed spectral points. This transfers the derivative
without restricting it to the complement of all closed cuts.

`SourceFullAbelianFiniteGapExterior.lean` supplies the exterior analyticity
assertion at the start of Lemma 19.2 for the actual full primitive. At
each real finite-gap source, one radius works for every normalization
index. Beyond it the primitive is analytic and its derivative is exactly
`-i + z^(-2)*h(1/z)`, where one function `h` is analytic near zero. The
construction uses the earlier finite-gap quotient estimates and imposes
no extra cut-avoidance condition at exterior periodic endpoints.

Public checks cover both arcosh limits at exponent 3/2, the exact
`5*i*pi` shift for gap -2 and primitive index 3, the free value at index
-2, derivatives at exterior periodic endpoints, and the common analytic
inverse-frequency remainder at a non-Hilbert exponent.

The full Laurent expansion of `F_0` in Lemma 19.2 is not yet proved:
the derivative expansion must be integrated, its additive constant
fixed, and its coefficients identified with the NLS Hamiltonians. That
is the next step. Later frequency results and the full dissertation
remain unfinished.

## Previous milestone: analytic square continuation across complex gaps

`SourceFullAbelianUniformSquare.lean` proves Lemma 19.1(iv) for the
canonical full primitive on one open connected almost-real source
neighborhood. For every source and every signed index, its continued
square is analytic on the plane with only the other noncollapsed gaps
removed. The selected complex gap, both of its endpoints, and every
collapsed gap are included. Both selected endpoints have value zero.

`SourceFullAbelianCauchySquare.lean` uses the exact factorization of the
normalized primitive into its selected standard root and the analytic
Cauchy quotient. Its square is the endpoint polynomial times the square
of that quotient, which is analytic on the entire assigned disc. On the
closed gap this equals the square of either boundary profile.

`SourceFullAbelianSquare.lean` defines the global square by relative
limits from the dense canonical root domain. It agrees with every local
Cauchy square and preserves the original full primitive's square on the
complement of noncollapsed gaps. The construction is independent of the
ambient source neighborhood and agrees exactly with the earlier
real-source square. At zero potential it is the entire quadratic
`-(z-pi*n)^2`, including all collapsed free spectral points.

Public checks cover exponent 3/2, the common neighborhood for all signed
indices, analyticity at every point of a complex gap of index -2, equality
of the two boundary squares, the real arcosh-square formula, and the free
quadratic at index -3. No noncollapse or real-source assumption is used
for the complex-gap analyticity checks.

The next step is to transfer the real boundary formula in Lemma 19.1(v)
to the full canonical primitive. Later frequency results and the full
dissertation remain unfinished. This milestone proves spectral
analyticity of the square, not joint analyticity on its filled cuts.

## Previous milestone: uniform gap bounds for the full primitive

`SourceFullAbelianUniformGapBound.lean` proves the gap-size estimate of
Lemma 19.1(iii) for the canonical full primitive. On one open connected
neighborhood of the real-source locus, every complex base source has a
positive source radius, one tail cutoff, and one positive constant.
These control both boundary values at every point of every sufficiently
large signed gap by that gap's length. Noncollapsed values are limits
from the actual oriented half-planes; collapsed values are values of the
filled function and equal zero. The same primitive remains jointly
analytic off the moving cuts on this neighborhood.

`SourceCriticalRootRatioUniformTailBound.lean` bounds the regular deleted
factor using the uniform product estimate, critical displacement norms,
and squared-gap row estimates. `SourceCriticalRootGapUniformBound.lean`
combines it with the squared-gap critical offset to bound the regular
numerator linearly in the gap length. The constants are derived from
existing source estimates, not assumed as new hypotheses.

`QuadraticPrimitiveGapBound.lean` proves a general cosine-coordinate
estimate for a quadratic-root primitive. Its sine-weighted Cauchy
quotient has derivative equal to the regular numerator, so the mean
value estimate gives a factor of pi. `SourceFullAbelianGapBoundary.lean`
identifies the resulting profiles with the two limits of the actual
canonical primitive, proves that the profiles are opposites, and covers
the entire closed gap, including both endpoints and collapsed gaps.

Public checks specialize the result to exponent 3/2 and all sufficiently
large negative gap indices, obtain both opposite side limits, verify the
uniform estimate around arbitrary complex base sources, and check the
zero filled value at a collapsed complex gap of index -2.

The next step is the square continuation in Lemma 19.1(iv). The later
frequency results and the full dissertation remain unfinished. Joint
analyticity at filled collapsed endpoints is not asserted here.

## Previous milestone: uniform endpoint normalization for all gaps

`SourceFullAbelianUniformEndpoints.lean` now gives one open connected
almost-real neighborhood on which the canonical full primitive has the
exact endpoint limits `i pi (n-j)` for every gap `j` and normalization
index `n`. Around each complex base potential there is one positive
source radius working for all gaps simultaneously. The limits are taken
relative to the whole complement of noncollapsed gaps, not merely a
selected cut disc. At a collapsed endpoint the filled function itself
has the prescribed value. The same function is jointly analytic off all
moving cuts on this neighborhood.

`SourceFullAbelianCauchyPrimitive.lean` applies the quadratic Cauchy
construction directly to the full canonical function. Its quotient is
analytic in the whole interior disc and the source; multiplying by the
selected standard root recovers the exact spectral derivative and zero
endpoint limits. `SourceFullAbelianUniformCauchyFamily.lean` supplies all
these constructions on the common source ball, using the uniform disc
family and the global standard-root and numerator-extension results.

`SourceFullAbelianUniformNormalization.lean` identifies each analytic
source-dependent offset. The actual real normalization fixes the offset
near the real anchor. The identity theorem then fixes it throughout the
original connected source ball. Applying this separately to each index
does not shrink the ball, so the resulting endpoint normalization is
simultaneous for the whole infinite family.

Public checks verify one common radius at exponent 3/2, both endpoint
limits for every signed gap and normalization index, filled-slice
analyticity, and joint analyticity of the same function. A collapsed
complex gap at index -2 has the exact filled value `5 i pi` for primitive
index 3, with no reality assumption on the perturbed source.

This supplies the common-neighborhood endpoint normalization in Lemma
19.1(ii), together with the previously proved index-shift identity. The
uniform gap-size bounds in (iii) are next. Further square-continuation
results, later frequency results, and the full dissertation remain
unfinished. Joint analyticity at filled collapsed endpoints is not
asserted by these off-cut joint-domain theorems.

## Previous milestone: full interior regularity and Cauchy normalization

`SourceFullAbelianJointAnalytic.lean` proves joint analyticity of the
canonical full primitive throughout the complex cut complement on one
open connected neighborhood of the real-source locus. The same function
retains spectral analyticity on the larger domain with collapsed gaps
filled. Joint analyticity here is asserted off all moving cuts; no joint
regularity at a filled collapsed endpoint is claimed.

The generic `ParametricPrimitivePropagation.lean` supplies the missing
parameter argument. On a convex product chart, a spectral primitive is
the sum of its anchor value and the explicit parametric integral of its
derivative. An analytic anchor value therefore propagates across the
chart without assuming source continuity of the primitive. An open-and-
closed argument propagates this regularity along any connected spectral
slice. The common exterior supplies the initial anchor.

`SourceFullAbelianDifferential.lean` propagates the exact Floquet
exponential identity to the full spectral cut complement. Joint
analyticity identifies the normalized logarithm germ and proves the full
differential `canonicalRoot⁻¹ • d Delta` everywhere off the cuts,
including the potential gradient in arbitrary complex directions.

`SourceFullAbelianCauchyCompatibility.lean` identifies the full function
with every overlapping normalized Cauchy disc chart. The real projection
path fixes the value at a common collar anchor; uniqueness on the
connected cut disc identifies all remaining values. The canonical full
primitive consequently inherits the exact limit `i pi (n-j)` at both
endpoints of gap `j`, including a collapsed selected gap. An existence
theorem supplies such a complex source neighborhood around every real
source and every selected gap.

Public checks verify full joint and filled-slice analyticity together
with the exact differential at exponent 3/2, the full interior potential
gradient, and the exact endpoint limit `-5 i pi` for index -3 at gap 2.

This removes the interior parameter-regularity gap and transfers the
previous local endpoint normalization to the canonical function. The
endpoint-neighborhood radius may still depend on the selected gap;
uniform endpoint control across all gaps on a common almost-real
neighborhood remains next. The estimates in Lemma 19.1(iii), later
frequency results, and the full dissertation remain unfinished.

## Previous milestone: one compatible full spectral primitive

`SourceFullAbelianPrimitive.lean` now defines one spectral abelian
primitive whose values are independent of the supporting source ball,
selected spectral chart, and ambient root neighborhood. The equality
holds on the whole complement of noncollapsed gaps, including every
filled collapsed gap. The function retains the exact spectral
derivative, all signed-index shifts, the actual real-source values,
and the free formula at every spectral point.

`RealCenteredDiscExterior.lean` proves path connectedness of the exterior
of uniformly bounded discs with real centers and a real exterior point.
`SourceAbelianComplexDomainConnected.lean` applies this geometry to the
common disc family and proves connectedness of the full cut complement
at complex potentials. Any two constructions have a nonempty open
exterior intersection. The identity theorem identifies their primitives
off the cuts; density and continuity identify their collapsed fillings.
`SourceAbelianSpectralChart.lean` packages these compatible constructions.

`SourceFullAbelianExterior.lean` proves that this same defined function
agrees with the projected primitive on every supported exterior product.
It is jointly analytic there, with full differential
`canonicalRoot⁻¹ • d Delta`. One open connected neighborhood of the whole
real-source locus supports both full spectral analyticity and uniform
joint exterior regularity for this function.

Public checks use exponent 3/2 to verify both forms of analyticity and
the exact differential simultaneously. They also check independence
between different ambient neighborhoods with a negative index shift,
the canonical free formula including collapsed lattice gaps, and the
spectral derivative throughout the cut complement.

This closes the choice-compatibility gap left by the previous milestone
and combines the spectral and exterior regularity toward Lemma 19.1(i).
Joint regularity in the interior and agreement there with the earlier
normalized Cauchy charts remain to be established for this full function.
That agreement should propagate the exact complex endpoint constants
uniformly. The estimates in (iii), later frequency results, and the full
dissertation remain unfinished.

## Previous milestone: common-neighborhood full spectral continuation

`SourceAbelianAlmostRealSpectralContinuation.lean` now constructs an
open connected neighborhood of the real-source locus covered by source
balls that control every gap simultaneously. For every complex source
in each ball, the actual projected exterior primitive has a spectral
continuation to the whole complement of noncollapsed gaps, with its
exact spectral derivative off the cuts and all signed-index shifts.
Collapsed gaps are included in the analytic domain.

`SourceAbelianUniformDiscFamily.lean` builds the common source ball
from the existing uniform tail and finite central contour family. Each
assigned disc has a smaller concentric radius enclosing its moving
segment uniformly on that ball. The larger discs are pairwise disjoint
and their closures avoid every unselected cut. Only finitely many
assigned discs differ from the free lattice discs; the new generic
`LocallyFiniteLatticeDiscs.lean` proves local finiteness and provides a
compact-set radius lemma. Thus the complement of all smaller closed
discs is one open exterior, and its product with the entire source ball
lies in the projected joint domain.

`SourceAbelianUniformSpectralContinuation.lean` extends that exterior
function into every cut disc at once and glues the spectral extensions.
The exterior and the cut discs are proved to cover the entire canonical
cut complement. This replaces per-gap source neighborhoods with one
source ball for the full infinite family.

`SourceAbelianUniformCollapsedFilling.lean` proves density of the cut
complement for arbitrary complex sources and uses dense limits to join
all analytic collapsed-gap fillings. The construction retains every
value off the cuts and the prescribed exterior values.
`SourceAbelianUniformRealNormalization.lean` proves that the exterior
is nonempty and that its real-source normalization determines the
filled primitive on the whole real spectral domain.

Public checks construct a single positive source radius at exponent
3/2 with full spectral analyticity, the actual derivative, and all index
shifts. They check arbitrary complex-source density, literal all-disc
coverage, and the complete free formula at every spectral point,
including all collapsed lattice gaps.

This supplies full spectral continuation on common almost-real source
neighborhoods, including collapsed-gap removal, toward Lemma 19.1(i).
The current theorem constructs spectral functions separately for each
complex source and supporting source ball, with fixed exterior values.
It does not yet identify all choices between different source balls or
with the earlier jointly analytic continued function throughout their
interior overlaps. Those compatibility and parameter-regularity steps
are next, together with uniform propagation of the exact complex
endpoint constants. The estimates in (iii), later frequency results,
and the full dissertation remain unfinished.

## Previous milestone: gluing interior discs and the exact potential gradient

The new `SourceAbelianContinuedPrimitive` joins the existing enlarged
exterior function to every normalized interior disc chart on one open
joint domain. Agreement holds on complete overlaps, including charts
for different selected gaps and different real-source centers. Every
previous exterior value and every established exterior product
neighborhood are retained.

`SourceFloquetJointDerivative.lean` derives the exact multiplier
differential at complex sources from the canonical-root identity.
`SourceAbelianCauchyDifferential.lean` propagates the Floquet exponential
identity from the normalized collar over the connected cut disc. The
zero-index continuation is then locally the exact normalized Floquet
logarithm. This proves its full joint differential `d Delta / canonicalRoot`,
including the potential gradient on the new interior domain.

`SourceAbelianDiscJointChart.lean` supplies normalized interior charts
on real-centered source balls inside one fixed analytic root neighborhood.
Such a chart exists for every selected gap at every real source in that
neighborhood, including collapsed gaps. Within each isolating disc its
only excluded spectral set is its own moving selected cut.
`SourceAbelianDiscCompatibility.lean` proves agreement with other disc
charts, old product charts, and the projected exterior function. For
distinct gaps, the two isolating discs jointly exclude all cuts along
the source projection path; continuous logarithm uniqueness fixes the
common value from the real-source normalization.

`SourceAbelianContinuedPrimitive.lean` glues this compatible family.
`SourceAbelianContinuedProperties.lean` proves joint analyticity, both
coordinate derivative formulas, the Floquet exponential identity,
signed-index shifts, the complete real-source normalization, and exact
endpoint limits `i (n-j) pi`. The selected-index square agrees with the
previous analytic filling across each entire local complex gap.

Public checks construct local coverage and the potential derivative
at exponent 3/2 for every real source and selected gap. They also check
negative-index endpoint normalization after gluing, free normalization,
and agreement between arbitrary overlapping disc charts.

This closes the local interior potential-gradient and chart-gluing
steps toward Lemma 19.1(i). The union is proved open, and the whole cut
disc is covered at every source in each chart's source ball. A single
almost-real source neighborhood giving full spectral coverage for all
gaps simultaneously still requires uniform tail and finite-core
arguments. The locally source-uniform and index-uniform estimates in
(iii), subsequent frequency results, and the full dissertation remain
unfinished.

## Previous milestone: exact complex endpoint normalization and filled squares

`SourceAbelianCauchyContinuation.lean` identifies the exact endpoint
values of the complex-source continuation: the normalized primitive
`F_n` tends to `i (n-j) pi` at both endpoints of the selected gap `j`.
The result includes collapsed gaps. Around every real source and
selected gap, one open complex-source neighborhood and one fixed
spectral collar work for every normalization index. The explicit
continued function agrees with the actual old joint primitive, and
with the enlarged primitive, on that entire collar.

`SourceAbelianCauchyPrimitive.lean` constructs the interior Cauchy
transform of the actual zero-index collar primitive divided by the
selected standard root. Its quadratic differential equation holds
throughout the disc. Multiplication by the root gives the exact
spectral derivative `Delta' / canonicalRoot` and zero limits at both
endpoints, even when they coincide.

`SourceAbelianCauchyChart.lean` supplies uniform charts at every real
source, including collapsed real gaps. The Cauchy quotient is jointly
analytic on the full disc times the source neighborhood. The additive
offset from the old collar function is therefore analytic in the source.
`SourceAbelianCauchyNormalization.lean` identifies its actual real-source
value as `-i j pi`; uniqueness from the real-source locus propagates that
value to complex potentials. This determines the constant without
assuming continuity or analyticity of the ordered complex endpoints.

The continued primitive is jointly analytic off the moving selected
cut, retains the exact spectral derivative and signed-index shift, and
agrees with the actual real-source primitive throughout each real slice.
`SourceAbelianCauchySquare.lean` proves that different charts for the same
gap agree on their complete cut-disc overlaps. It also constructs the
selected-index square explicitly as the endpoint polynomial times the
square of the Cauchy quotient. This square is spectrally analytic across
the entire complex gap, vanishes at both endpoints, and is independent
of the chart even at points on the filled cut.

Public checks cover constructed complex-source normalization at exponent
3/2, joint analyticity inside the disc, the relative sign for index -3
at gap 2, the full free quadratic formula through a collapsed gap, and
chart independence of the filled square.

This proves the exact local complex endpoint normalization and local
square continuation required in Lemma 19.1(ii) and (vi). The next step
is to glue the normalized local charts with the existing exterior
function across all isolating discs and obtain a common almost-real
source neighborhood. The full global complex-source spectral clause
of (i), the potential gradient on the new interior domain, locally
source-uniform and index-uniform estimates in (iii), subsequent
frequency results, and the full dissertation remain unfinished.

## Previous milestone: complex cut-disc continuation and endpoint limits

`SourceAbelianComplexDiscContinuation.lean` continues the actual
normalized joint primitive into a whole isolating disc minus its moving
complex spectral segment. Around each real source and selected gap,
one fixed annular collar, disc, and open complex-source neighborhood
work for every normalization index. A compact collar lies in the
existing joint domain; radial continuation preserves every value on
that collar and has the exact spectral derivative `Delta' / canonicalRoot`
throughout the cut disc. No open-gap assumption is required at the base
source or at its complex perturbations.

The continuation is uniquely determined by its derivative and one value.
Consequently it retains the signed index relation and the actual
real-source values throughout its cut disc. On the collar it also agrees
with the enlarged primitive from the preceding milestone.

`SourceAbelianComplexEndpointLimits.lean` proves a common weighted bound
at both endpoints of a nondegenerate complex gap. Its weight uses the
norm of the complex gap displacement, so tilted and vertical gaps are
included. Boundedness of the regular numerator and the standard-root
lower bound give finite limits along every approach in the full cut
disc, without a real-source or real-ordering hypothesis.

`SourceAbelianComplexCollapsedExtension.lean` fills a collapsed cut
analytically while preserving every previously defined cut-disc value.
The filled derivative is the regular deleted quotient. A single open
neighborhood of all real sources supports this removability and full
finite endpoint limits for all gaps. The combined local theorem gives
continued primitives with endpoint limits and collapsed-gap removal on
the same source neighborhood, simultaneously for all normalization indices.

Public checks cover the combined continuation at exponent 3/2, nonreal
gap displacements, the full free formula at an odd negative index, and
analytic filling of arbitrary complex-source collapsed-gap primitives.

The source neighborhood for the continuation still depends on the
selected gap. The next steps are to identify the complex endpoint
constants as the prescribed `i (n-j) pi`, and glue the local spectral
continuations consistently across all isolating discs. This does not
yet establish the full complex-source spectral clause of Lemma 19.1(i),
complex-source square continuation, the locally source-uniform and
index-uniform estimates in (iii), later frequency results, or the full
dissertation.

## Previous milestone: one enlarged domain over an almost-real source neighborhood

`SourceAbelianEnlargedExterior.lean` places all exterior continuations
in one open joint domain. There is an open connected neighborhood `V`
of the entire real-source locus such that every complex source in `V`
has a positive source radius and a fixed family of pairwise disjoint
isolating discs. The full unbounded exterior, including its boundary,
times that source ball lies in the same enlarged domain. The radius
works for every signed index, and all nearby spectral clusters stay
inside their assigned discs.

`SourceAbelianProjectedPrimitive.lean` normalizes each complex source
at its contractive real projection, then integrates the Floquet
logarithmic derivative along the straight source segment. The domain
where that entire segment avoids the canonical cuts is open.
`MovingSourceLogarithm.lean` proves joint analytic dependence of the
logarithmic integral on its moving anchor, spectral point, and terminal
source. Combined with real-source continuity, this gives a continuous
logarithm; local logarithm uniqueness then proves complex analyticity
even though the defining projection is only real linear.

`SourceAbelianProjectedCompatibility.lean` proves agreement with every
previous chart on its entire overlap, by following the projection path.
`SourceAbelianEnlargedPrimitive.lean` therefore unites the projected and
previously glued domains into one analytic function. It preserves all
previous complex-source values, the actual real-source normalization,
the signed index shifts, and the exact Floquet exponential identity.
Its full differential is `d Delta / canonicalRoot`; both the potential
gradient and the spectral derivative are proved explicitly. Every real
slice still contains exactly its full canonical-cut complement.

Public checks cover one common function over a connected source
neighborhood at exponent 3/2, uniform exterior analyticity and the
potential gradient at arbitrary complex base sources, preservation of
the entire old domain and function, the exact exponential and spectral
derivative, complete real-source slices, and free normalization at a
nonreal spectral point with an odd negative index.

This establishes the joint exterior-domain and gradient part of
Lemma 19.1(i) on one almost-real source neighborhood. The next step is
complex-source spectral continuation inside the isolating discs,
including removal at collapsed gaps and endpoint normalization.
The full complex-source spectral clause of (i), complex-source endpoint
and square continuation, the locally source-uniform and index-uniform
estimates in (iii), subsequent frequency results, and the full
dissertation remain unfinished.

## Previous milestone: uniform continuation over the full spectral exterior

`SourceAbelianExteriorProduct.lean` proves uniform exterior continuation
around every real source. One positive potential radius and one fixed
family of pairwise disjoint isolating discs work for every signed index
and the full unbounded spectral exterior, including its boundary.
The continued abelian integral is jointly complex analytic there, has
full differential `d Delta / canonicalRoot`, and retains the actual
normalization at every nearby real source. Every nearby spectral
cluster stays inside its assigned disc.

`SourceAbelianRadialPrimitive.lean` constructs this continuation by
integrating the Floquet logarithmic derivative along a straight source
segment, starting at the actual real-source primitive. Exponentiation
recovers the multiplier exactly; differentiating that identity gives
the full joint differential and the potential gradient. Continuous
logarithm uniqueness fixes the normalization throughout a convex
neighborhood of real sources.

`ParametricSourceLogarithm.lean` and `ParametricSourceLogDomain.lean`
supply the reusable Banach-parameter construction. The set of points
whose entire straight source segment stays inside an open analytic
domain is open, by compactness of the path parameter. This proves
analyticity at exterior boundary points without assuming that the
spectral exterior itself is open or bounded. All-index isolation keeps
the source paths away from every canonical cut at once.

`SourceAbelianRadialCompatibility.lean` identifies the continuation
with the previously glued joint primitive at every common complex-source
point in the exterior product. The proof uses
`ContinuousLogarithmUnique.lean` and
`SourceRealTypeLogarithmUnique.lean`: projection to real sources stays
inside both source balls, and the common exponential and real-source
normalization determine the logarithm throughout their overlap.

Public checks cover unrestricted exponential source transport, a common
radius over the unbounded exterior at exponent 3/2, the exact potential
gradient for arbitrary nearby complex sources and all indices,
compatibility with the glued primitive, nearby real-source values at
an odd negative index, and the complete free base-source formula.

This establishes the uniform exterior-domain continuation and gradient
around every real anchor in Lemma 19.1(i). The next step is to place these
extensions in one enlarged open joint domain over an almost-real source
neighborhood; the previously defined `sourceAbelianJointDomain` has not
yet been proved to contain these entire exterior products. Complex-source
endpoint and square continuation, locally source-uniform and index-uniform
estimates in (iii), subsequent frequency results, and the full dissertation
remain unfinished.

## Previous milestone: a single joint analytic abelian primitive

`SourceAbelianJointPrimitive.lean` constructs one chart-independent,
jointly complex-analytic normalized abelian primitive on an open union
of product neighborhoods. Its intersection with every real-source slice
is exactly that source's full spectral cut complement, and its values
there are the actual `F_0 + i n pi`. At every complex-source point of the
joint domain, its full differential is `d Delta / canonicalRoot`.
Changing the signed index adds exactly `i n pi`, and exponentiation
recovers the Floquet multiplier with its prescribed index factor.

`SourceAbelianJointChart.lean` proves compatibility for charts with both
different spectral anchors and different real-source anchors, on their
entire complex-source overlap. The real-part projection contracts
distances and fixes real sources, so projecting an overlap point stays
inside both chart balls. The actual real-source values agree there;
equality of joint derivatives extends this equality over the convex
overlap. The existing holomorphic-chart gluing construction then gives
the single primitive, independent of every local chart choice.

`SourceAbelianJointProperties.lean` proves the spectral derivative and
the potential derivative `partial Delta / canonicalRoot` for this glued
function. Every compact spectral subset off the cuts has an open
spectral neighborhood and one common complex-source ball contained in
the joint domain. This is uniform over the entire compact set and all
signed indices. The exact free-source formula is also retained.

Public checks cover complex-source overlaps between independently
anchored charts, inclusion and exact values on all real-source slices,
common product neighborhoods over arbitrary compact sets at exponent
3/2, complex-source derivatives and exponentiation, and an odd negative
free normalization at a nonreal spectral point.

This resolves complex-source chart compatibility and constructs the
joint primitive needed for Lemma 19.1(i). The remaining domain assertion
is a single source neighborhood over the full unbounded spectral
exterior of an isolating-disc family; compact-set uniformity alone does
not prove it. Complex-source endpoint and square continuation, locally
source-uniform and index-uniform estimates in (iii), subsequent frequency
results, and the full dissertation remain unfinished.

## Previous milestone: actual joint charts at every off-cut anchor

`SourceAbelianJointExtension.lean` removes the band-anchor restriction:
at every spectral point off the cuts of a real potential, one positive
product neighborhood supports jointly complex-analytic logarithm charts
for all signed indices. On every nearby real-source slice, each chart
equals the actual `F_0 + i n pi` throughout the complex spectral ball.
The full differential remains `d Delta / canonicalRoot`, including the
potential derivative at nearby complex sources. The actual primitive is
jointly continuous in complex spectral coordinate and real source at
every such point.

`SourceRootDomainConnected.lean` proves connectedness of the entire
real-source cut complement. Each nonempty vertical band strip joins the
two half-planes, and these regions cover the domain even when gaps have
collapsed. `ParameterContinuityPropagation.lean` gives a reusable
connected-set argument: continuity in a parameter at one anchor
propagates if differences at nearby spectral points are continuous.

`SourceAbelianSourceContinuity.lean` verifies that hypothesis for the
actual primitive. On a small spectral ball, actual increments equal
increments of a joint analytic chart because the additive constants
cancel. Starting from the exact band normalization, this proves source
continuity at arbitrary off-cut points. Normalized-log uniqueness then
fixes each chart at its anchor, and equality of spectral derivatives
extends the agreement over the whole ball. The previous band-chart
results are now specializations of the general theorems.

Public checks cover connectedness with all gaps collapsed, nonreal
anchors at exponent 3/2, a common product neighborhood for all indices,
exact potential derivatives at nearby complex sources, and agreement
of independently anchored charts on common real-source slices.

This advances Lemma 19.1(i) from band anchors to every off-cut spectral
anchor. Gluing the charts on complex-source overlaps and constructing
the stated product domain with one source neighborhood over the full
spectral exterior remain next. Complex-source endpoint and square
continuation, locally source-uniform and index-uniform estimates in
(iii), subsequent frequency results, and the full dissertation remain
unfinished.

## Previous milestone: normalized band charts for nearby real sources

`SourceAbelianBandChart.lean` proves that a local joint logarithm chart
is an actual extension of the normalized abelian integral for every
nearby real potential. At any real spectral band anchor there is a
positive-radius product of spectral and complex-source balls on which
all signed-index charts are analytic and have differential
`d Delta / canonicalRoot`. On every real-source slice they equal
`F_0 + i n pi` throughout the complex spectral ball.

`SourceAbelianRealBandValue.lean` fixes the exact band formula
`F_0(x) = P_n(x) - i pi/2 - i n pi`, where `P_n` is the existing
arcsine primitive. Its constant is determined by the actual endpoint
limit. `SourceAbelianBandSourceContinuity.lean` uses continuity of the
periodic endpoints to keep nearby points in the same band and proves
joint continuity of these actual values as real sources vary.
Normalized-log uniqueness fixes the chart at the real anchor for all
nearby real sources; equality of spectral derivatives then extends
this agreement across the spectral ball. The actual primitive is
therefore jointly continuous in complex spectral coordinate and real
source at every real band anchor.

Public checks cover an odd negative band index, joint continuity with
complex spectral coordinates, and a common product neighborhood at
exponent 3/2. The latter checks agreement for every nearby real source
and every index, together with the exact potential derivative at
arbitrary nearby complex sources.

This advances Lemma 19.1(i) by establishing normalization compatibility
as real sources vary near band anchors. Continuing these compatible
charts to arbitrary spectral anchors and assembling the full
complex-source product-domain primitive remain next. Complex-source
endpoint and square continuation, locally source-uniform and
index-uniform estimates in (iii), subsequent frequency results, and
the full dissertation remain unfinished.

## Previous milestone: local joint logarithm charts and exact differential

`SourceAbelianLogChart.lean` constructs local logarithm charts anchored
at the exact value of the real-source normalized abelian primitive.
For every spectral point off the cuts, an open neighborhood in the
joint spectral/complex-source space supports all signed indices at
once. Each chart is jointly complex analytic there, and its full
Fréchet differential is `d Delta / canonicalRoot`.

Restricting this differential gives both the spectral quotient and the
potential derivative `partial Delta / canonicalRoot` at every complex
source in the neighborhood. The chart agrees exactly with the existing
normalized primitive on the anchor real source's spectral germ.
Changing the index adds precisely `i n pi`, and exponentiation recovers
the Floquet multiplier with the exact corresponding exponential factor.

`NormalizedLogChart.lean` supplies a reusable local logarithm
`A + log(M/M(anchor))`, fixing the additive value even when the original
multiplier lies outside the principal slit plane. `SourceFloquetJointLog.lean`
proves joint analyticity of the actual multiplier and derives the
logarithmic differential from the canonical root's square identity.
The derivative formula applies throughout the complex-source analytic
domain whenever the normalized logarithm is on its slit plane.

Public checks use exponent 3/2, one neighborhood for all signed indices,
arbitrary nearby complex potentials in the potential and spectral
derivative formulas, an exact negative-index free-source germ, and
recovery of the multiplier by exponentiation.

This supplies local charts and the differential needed for Lemma 19.1(i).
It does not yet identify charts anchored at different sources with one
globally normalized complex-source primitive. That compatibility and
the full product-domain joint-analyticity assertion remain next.
Complex-source endpoint and square continuation, locally source-uniform
and index-uniform estimates in (iii), subsequent frequency results,
and the full dissertation remain unfinished.

## Previous milestone: analytic square across the selected gap

`SourceAbelianSquare.lean` constructs a chart-independent continuation
of `(F_0 + i n pi)^2`. It agrees with the actual normalized square on
the plane with only noncollapsed cuts removed, and is analytic after
adjoining the entire selected isolating disc. In particular, every
point of the selected closed gap is an analytic point, with no
open-gap or finite-gap assumption.

The generic `GapPrimitiveSquare.lean` theorem continues local
endpoint-normalized primitives onto regular square-root sheets.
Squaring cancels their root-ratio signs, so the local squares agree
on a dense subset and hence on overlaps. Zero endpoint limits and
the removable-singularity theorem fill the two remaining points.
`DenseAnalyticExtension.lean` supplies the reusable dense-limit and
finite-boundary extension results. The argument includes a collapsed
segment without dividing by its length.

`SourceAbelianDiscSquare.lean` applies this to the actual discriminant
quotient and its analytic regular numerator. The resulting global
square has zero values at both selected endpoints and equals the
squared real arcosh profile on the whole closed gap. At zero potential,
it is exactly the entire quadratic `-(lambda - n pi)^2`.

Public checks cover analyticity on the cut at exponent 3/2 and index
-3, positivity of the continued square in a real gap interior,
agreement of distinct isolating charts even on the cut, and the
shifted free quadratic at arbitrary complex spectral parameters.

This proves the real-source continuation assertion of Lemma 19.1(iv).
Extending the construction to the complex-source neighborhoods and
proving joint analyticity and the potential gradient in (i) remain
next. The locally source-uniform and index-uniform estimates in (iii),
subsequent frequency results, and the full dissertation are unfinished.

## Previous milestone: exact half-plane gap boundary values

`SourceAbelianGapBoundary.lean` proves the exact boundary formula
`F_n(x + i0) = arcosh((-1)^n Delta(x)/2)` and
`F_n(x - i0) = -arcosh((-1)^n Delta(x)/2)` for real sources.
The limits allow arbitrary approaches within the corresponding
half-plane. They hold on the entire closed gap, at every signed index
and every finite exponent `1 < p`, including collapsed gaps.

The proof first converts the transverse quotient estimate into an
integrable real endpoint weight. Dominated convergence then passes
partial displaced horizontal integrals to their exact arcosh values.
The fundamental theorem identifies these integrals with differences
of actual half-plane primitive values; endpoint normalization fixes
the additive constant. A local quotient bound at each interior gap
point upgrades the vertical limits to full half-plane limits.

The same formula is proved for the filled global primitive after
adding `i n pi`. Public checks exercise an odd negative index at
exponent 3/2, the negative lower-side value with the global index
correction, and the collapsed-gap limit from either half-plane.

This completes the real-source boundary assertion of Lemma 19.1(v).
The next step is continuation of the squared normalized primitive
across the selected gap, as in (iv). The complex-source construction,
joint analyticity and potential gradient in (i), locally source-uniform
and index-uniform gap estimates in (iii), subsequent frequency results,
and the full dissertation remain unfinished.

## Previous milestone: exact partial gap-side arcosh integrals

`SourceRealGapArcoshPrimitive.lean` defines the real arcosh profile
`arcosh((-1)^n Delta(x)/2)` on each canonical gap. It proves that the
actual upper canonical-root quotient is its derivative, with the
parity signs canceled exactly for every signed index. The profile is
continuous on the closed gap, zero at both endpoints, and strictly
positive in the interior.

Both actual side quotients are integrable across the endpoints.
Integrating from the left endpoint to any point of the closed gap gives
exactly the arcosh profile on the upper side and its negative on the
lower side. No integrability or open-gap hypothesis is required from
the caller; collapsed gaps are included.

`SourceRealGapArcoshBound.lean` proves that the profile is nonnegative
and bounded by `sqrt(g^2-1)`, where `g` is the signed half-discriminant.
The exact deleted-product factorization gives the quantitative bound
`profile(x) <= (gap length)/2 * sqrt(K)` whenever the real deleted
periodic product at `x` is bounded by `K >= 0`. Compactness supplies
one such finite `K` on every fixed closed gap.

Public checks cover an odd negative index at exponent 3/2, the strict
negative sign of the lower partial integral, a numerical deleted-product
bound yielding a full-gap-length norm bound, and the zero full-gap
integral without an open-gap assumption.

This proves the exact real side integrals used in Lemma 19.1(v) and a
quantitative ingredient for (iii). Identifying these side integrals
with the half-plane boundary limits of `F_n` remains next. The bound
proved here is for a fixed source and gap; local uniformity in the
source and uniformity in the index remain to be established. The
complex-source and joint-analyticity assertions, potential gradient,
square continuation, subsequent frequency results, and the full
dissertation remain unfinished.

## Previous progress: analytic extension through collapsed gaps

`SourceCollapsedGapNeighborhood.lean` proves that a collapsed gap is
an isolated missing point of the canonical cut complement. Its whole
isolating neighborhood belongs to the complement of the noncollapsed
cuts. This enlarged domain is open for every real source, without a
finite-gap assumption.

`SourceAbelianPrimitive.lean` inserts the limits of the global primitive
at the missing points. It agrees with the original function off all
cuts and has value `-i n pi` at either endpoint of gap `n`. Riemann's
removable singularity theorem proves complex analyticity through every
collapsed gap. The resulting primitive is analytic throughout the
plane with only the noncollapsed cuts removed.

`SourceAbelianPrimitiveProperties.lean` extends the exact Floquet
identity to this enlarged domain and identifies the derivative as
`sourceFloquetLogDerivative`, the regular multiplier logarithmic
derivative. It agrees with the literal `Delta'/canonicalRoot` away
from all cuts. Endpoint limits hold along all approaches in the
enlarged domain, and every smooth path there integrates the regular
one-form to the difference of primitive values. Such paths may pass
directly through collapsed endpoints.

At the free source, the enlarged domain is the whole plane and the
filled primitive is exactly the entire function `-i lambda`. Its
regular derivative is `-i` even at periodic lattice points, where the
literal quotient has zero denominator.

Public checks cover a collapsed negative-index gap at exponent 3/2,
the distinction between the regular derivative and literal quotient at
the free origin, a real path passing through three collapsed periodic
points, and endpoint limits without any gap-width assumptions.

This completes the collapsed-point extension for real sources. The
complex-source and joint-analyticity assertions of Lemma 19.1, its
potential gradient, gap-side formulas and estimates, and square
continuation remain to be proved. Subsequent frequency results and
the full dissertation remain unfinished.

## Previous progress: global real-source abelian primitive off the cuts

`SourceAbelianBandGluing.lean` constructs a quotient primitive on each
full vertical real-band strip which matches the zero-index primitive
on both half-planes. An existing corrected disc chart fixes the common
real value and hence removes the lower-half-plane constant ambiguity.

`SourceRealBandCoverage.lean` uses the bounded endpoint displacements
from `pi n` to find the greatest gap to the left of every real point
off the cuts. Thus the half-planes and band strips cover the entire
canonical cut complement, including both infinite spectral tails.

`SourceAbelianGlobalPrimitive.lean` glues these pieces into one function
for every real source at every finite exponent `1 < p`. It has the
actual derivative `Delta'/canonicalRoot` and is complex analytic on
the full cut complement. It agrees with every corrected isolating-disc
chart, independently of all local primitive and band choices.

`SourceAbelianGlobalProperties.lean` proves the full-domain endpoint
limits `F(lambda_n^±) = -i n pi` for all signed indices, including
collapsed gaps as boundary points. Every smooth path off the cuts
integrates the actual quotient to `F(b)-F(a)`; in particular, every
smooth closed path has zero period without a supplied homotopy.
The exact identity `exp(F) = (Delta + canonicalRoot)/2` holds everywhere
on this domain. At the free source the global function is `-i lambda`,
including its real band values.

Public checks cover the complex derivative at real band points for
exponent 3/2, an actual vertical path crossing from the lower to the
upper half-plane, a negative-index full-domain endpoint limit, and a
free real band value between collapsed gaps.

This constructs the global real-source abelian primitive off all cuts.
Analytically filling collapsed points is next; they are currently
excluded from this primitive's analytic domain. Joint source
analyticity, the remaining assertions of Lemma 19.1, the frequency
results, and the full dissertation remain unfinished.

## Previous progress: exact signed-index abelian normalization

`ContinuousBoundaryTransfer.lean` transfers a relative boundary limit to
closure points of a domain wherever a continuous extension is available.
`SourceAbelianBandTransfer.lean` extends each half-plane primitive across
an adjacent real-band strip and compares it with the actual arcsine
primitive. This fixes the boundary increment across every band at
exactly `-i pi`, on both sides of the real axis.

`SourceAbelianHalfPlaneNormalization.lean` proves the exact formulas
`F_n = F_0 + i n pi` and `F_n - F_m = i (n-m) pi` on both complete
half-planes, for arbitrary signed indices. At either endpoint of gap
`m`, the half-plane boundary limit of `F_n` is `i (n-m) pi`.
In particular, the zero-index primitive has value `-i m pi` there,
including when the gap is collapsed.

`SourceAbelianNormalizedCharts.lean` subtracts `i n pi` from each local
gap-normalized chart. The corrected charts retain the actual quotient
derivative and analyticity and agree with `F_0` on both half-planes.
Charts selected at different gap indices agree everywhere on their
common domain, including real overlap points. Their full chart-relative
endpoint limits have the prescribed value `-i n pi`.

Public checks exercise opposite signed indices at exponent 3/2,
negative-index lower-half-plane endpoint values, boundary limits for
both half-planes, and agreement of charts at different indices on the
real axis.

This establishes Lemma 19.1(ii)'s indexed half-plane constants for real
sources. Gluing across the entire real axis and filling collapsed
points remain next. Joint source analyticity, the remaining assertions
of Lemma 19.1, the frequency results, and the full dissertation remain
unfinished.

## Previous progress: exact adjacent-band improper integrals

`SourceRealBandGeometry.lean` identifies the nonempty real band between
consecutive canonical gaps and proves that it avoids every spectral cut.
The interval including its left endpoint still avoids all other gaps,
which permits continuation of the selected omitted root product.

`SourceCanonicalRootRealBand.lean` proves reality of the omitted product
at every real point of its domain. Continuity and nonvanishing carry its
known gap parity sign into the adjacent band. Thus the canonical root
is purely imaginary there, with sign `-(-1)^n`, and is exactly the
correspondingly signed positive square root of `4 - Delta^2`. The
actual real discriminant lies strictly between `-2` and `2` on the band.
These assertions include bands adjacent to collapsed gaps.

`SourceRealBandArcsin.lean` constructs the continuous arcsine expression
`i (-1)^n arcsin(Delta(x)/2)` and proves that its interior derivative
is the actual canonical quotient. Its left and right endpoint values
are `i pi/2` and `-i pi/2` for every signed index.

`SourceRealBandIntegral.lean` evaluates the actual quotient integral on
any compact subinterval, in either direction, with integrability derived
from continuity. Taking both endpoints independently to their adjacent
periodic endpoints gives the improper integral exactly `-i pi`.
An explicit positive cutoff realizes the same limit. No open-gap or
endpoint integrability hypothesis is imposed on the caller.

Public checks cover the actual improper integral at exponent 3/2, the
root orientation at an odd negative gap index, cancellation under
reversal of the integration direction, and the explicit free band
between `-3 pi` and `-2 pi`, where both neighboring gaps are collapsed.

This proves the real adjacent-band improper integral calculation used
in Lemma 19.1(ii). Transferring it to the half-plane primitives' boundary
constants, summing the increments to obtain `-i n pi`, and completing
global continuation remain next. Joint source analyticity and the other
remaining assertions of Lemma 19.1, the frequency results, and the full
dissertation remain unfinished.

## Previous progress: exact abelian logarithm and Floquet identities

`NormalizedLogarithmicPrimitive.lean` proves that an actual primitive
of a multiplier's logarithmic derivative exponentiates to that multiplier,
with its multiplicative constant determined by a boundary limit. No
principal-logarithm domain assumption is imposed.

`SourceFloquetEndpointLimit.lean` proves that the canonical root tends to
zero at either periodic endpoint along every approach off the cuts,
including at collapsed gaps. The actual Floquet multiplier consequently
tends to the signed index value `(-1)^n`.

`SourceAbelianFloquetIdentity.lean` identifies the exact exponential of
the normalized primitive on both complete half-planes and their joined
isolating-disc domain:

`exp(F_n) = (-1)^n (Delta + canonicalRoot) / 2`.

The opposite exponential equals the signed companion multiplier. Thus
`cosh(F_n) = (-1)^n Delta / 2` and
`sinh(F_n) = (-1)^n canonicalRoot / 2`, preserving the canonical sheet
orientation. The real part is exactly the logarithm of the multiplier's
modulus, independent of the chosen normalization index on common domains.
Near either endpoint the full continued primitive equals the principal
logarithm of the signed multiplier, because its zero boundary limit
selects the principal imaginary strip.

Public checks construct the local logarithm representation at exponent
3/2 without an open-gap assumption, verify both spectral signs at a
negative odd index on the real axis, compare real parts across different
normalization indices, and check the exact exponential at a free spectral
point far outside the local principal-logarithm chart.

This supplies the logarithm identity used in the proof of Lemma 19.1.
It does not yet construct the continuation across the rest of the real
axis or determine the full indexed `-i n pi` additive constants. Joint
source analyticity, the gap-side arcosh formula and estimates, and the
remaining assertions of Lemma 19.1 still require proof. The global
abelian integral, subsequent frequency results, and the full dissertation
remain unfinished.

## Previous progress: local gluing of normalized abelian primitives

`SourceAbelianDiscPrimitive.lean` uses the proved zero enclosing-circle
period to construct an actual quotient primitive throughout an isolating
disc minus the selected gap. Inverse-square-root endpoint estimates give
finite limits along every approach in this cut complement at open gaps.

`SourceAbelianDiscGluing.lean` fixes the left endpoint value to zero and
compares the resulting primitive with both independently normalized
half-plane primitives. The right endpoint value is consequently zero as
well. Collapsed gaps use the analytic removable extension of the actual
quotient. Every real source, signed index, and finite `p > 1` admits such
a normalized disc chart, and any two charts agree on their overlap.

`SourceAbelianLocalExtension.lean` joins both complete half-planes and
the isolating cut disc into one open domain and one analytic function.
It has the actual quotient derivative even at the newly included real
points, retains both zero endpoint limits on the whole joined domain,
and is independent of the chosen chart on overlaps. Every smooth path
inside this domain integrates the actual quotient to the function's
endpoint difference, including paths crossing the real axis.

Public checks construct the continuation at exponent 3/2, verify its
actual derivative and chart independence at real points, and evaluate
cross-half-plane path integrals at a collapsed free gap with negative
index. No open-gap or assumed primitive existence premise is needed for
the chart construction.

This completes the local gluing step around the selected gap in Section
19. Continuation across the rest of the real axis, the indexed `-i n π`
constants, joint source analyticity, and the remaining assertions of
Lemma 19.1 are still required. The globally normalized abelian integral,
frequency results, and full dissertation remain unfinished.

## Previous progress: normalized half-plane abelian primitives

`PrimitiveRemovableBoundary.lean` proves that a holomorphic extension
of a primitive's derivative through a boundary point gives a full relative
boundary limit. A prescribed common boundary value fixes the primitive
uniquely on a connected open domain.

`SourceAbelianHalfPlane.lean` constructs the endpoint-normalized abelian
primitive on each complete open half-plane for every real source, signed
gap index, and finite `p > 1`. Existing square-root estimates handle open
gaps. At a collapsed gap, the actual quotient's removable extension gives
a finite boundary value at the common endpoint. Subtracting that value
makes both endpoint limits zero. Uniqueness makes the values independent
of the primitive chosen during construction; no open-gap assumption is
required.

`SourceAbelianHalfPlaneProperties.lean` proves spectral analyticity and
identifies the primitive with the actual integral along every smooth
integrable connector from either selected endpoint into its half-plane.
The full normalized value commutes with exponent inclusion and is an
invariant of the original periodic spectrum with algebraic multiplicities.
At the zero source it is exactly `-i λ + i n π` on both half-planes for
every signed index, establishing Lemma 19.1(vi) on these domains.

Public checks verify the free normalization at a negative index above
the real axis and a positive index below it, compare independently chosen
primitives at exponents 3/2 and 3, and prove invariance under the actual
source phase rotation without an assumed isospectrality premise.

This begins Section 19. Gluing the half-plane constructions across the
real axis outside the open gaps, establishing the indexed `-i n π`
endpoint constants, joint source analyticity, and the remaining estimates
of Lemma 19.1 are still required. The complete globally normalized abelian
integral, subsequent frequency results, and the full dissertation remain
unfinished.

## Previous progress: Lemma 17.5 completed

`RealActionRotationOrbit.lean` proves that finite coordinate rotations
are dense in every prescribed action torus at every finite Banach
exponent, including `p = 1`. Equal-radius pairs differ by the difference
of their complex arguments, a formula that also handles radius zero.
Finite lists of these rotations match any finite target block exactly
while retaining the original tail. The resulting block replacements
converge in the full sequence norm, so the orbit closure is exactly the
action torus.

`SourceBirkhoffLemma17_5.lean` pulls the closed actual isospectral set
back through the global Hilbert inverse. It contains every finite
rotation orbit point, hence the entire coordinate torus by density.
Consequently, equal original Hilbert actions imply equality of the
original periodic spectrum and all algebraic multiplicities, without
a finite-gap hypothesis.

Inclusion into Hilbert space preserves the original actions and normalized
discriminant. This transfers the implication to every `1 < p ≤ 2`, with
a Hilbert normalized family constructed internally. Actual isospectral
sets are therefore exactly the original action level sets in this range.
Their Birkhoff images equal the whole prescribed action tori, and they
are compact in the original source norm. Together with the previously
proved inclusion for `p > 2`, this completes Lemma 17.5(i) and (ii).

Public checks cover full-norm finite-rotation approximation at `p = 1`,
exact matching of signed finite coordinate blocks at `p = 3`, construction
of a normalized family with a unique actual isospectral preimage for every
torus point at `p = 3/2`, and recovery of the entire discriminant and
algebraic multiplicities from the original actions below two.

Next continue into Chapter 4: the abelian integral `F` and its estimates
in Section 19, followed by the frequency analysis in Section 20 supporting
Theorem 18.1. Those results and the subsequent convexity and wellposedness
results remain unfinished. The full dissertation is not complete.

## Previous progress: complete isospectral Hilbert action flows

`RealActionRotation.lean` constructs a one-mode coordinate rotation at
every sequence exponent. Its selected velocity is `(-y_k,x_k)`, every
unselected coordinate is fixed, and every quadratic action is preserved.
The derivative exists in the full sequence norm for every real time.
Rotation times add, negative time reverses the motion, and a collapsed
selected action gives the constant curve.

`SourceBirkhoffActionHamiltonian.lean` differentiates the analytic
coordinate action-radius identity to obtain `dI_k = x_k dx_k + y_k dy_k`
at every point of the complex map domain, including closed gaps. The
proved canonical Poisson identities identify the original action
Hamiltonian's coordinate velocity with precisely this one-mode rotation
for every finite `p ≥ 2`.

`SourceHilbertActionRotation.lean` lifts the coordinate rotation through
the actual global Hilbert Birkhoff inverse. The inverse Jacobian proves
that its source-norm derivative is the original action Hamiltonian at
every time, with no open-gap hypothesis. Infinitesimal isospectrality
makes every fixed-parameter discriminant derivative zero, so the whole
normalized discriminant is constant along the complete curve. Therefore
the original periodic spectrum and all algebraic multiplicities are
preserved. Finite lists of rotations retain their exact coordinate
meaning and are isospectral, without restrictions on indices or times.

Public checks verify a quarter-turn at a negative index with the canonical
signs and an unchanged positive index, reversal by negative time, a
stationary source at zero original action, preservation of full spectral
data under norm limits of finite rotation sequences, and coordinate
action preservation at exponent 3.

Next prove that finite coordinate rotations approximate every point of
the prescribed Hilbert action torus. Continuity of the global inverse
and closedness of actual isospectral sets then give the converse torus
inclusion. Transfer to `1 < p < 2` remains after that. Lemma 17.5(i) and
the full dissertation are not yet complete.

## Previous progress: actual isospectral invariants and compactness

`PeriodicDiscriminantSpectralData.lean` proves that the original periodic
spectrum together with its algebraic multiplicities determines the
normalized discriminant at real-type even potentials. The canonical
endpoint product determines its square; the known endpoint value fixes
the sign, and analytic uniqueness gives equality everywhere. Conversely,
equality of discriminants recovers the original spectrum and every
algebraic multiplicity, without a reality assumption.

`SourceIsospectralSet.lean` defines actual isospectral sets using the
original operator spectrum and algebraic multiplicities. Equality of
discriminants characterizes membership and proves closedness in the
source norm at every finite `p > 1`. Common spectral data give identical
canonical roots and action-circle integrals. Comparing both definitions
on a common admissible circle proves equality of every full complex
indexed action, including closed gaps and the finite central block.

Consequently, the Birkhoff image of an actual isospectral set lies in its
prescribed action torus for every finite `p > 1`. This proves Lemma
17.5(ii). For `1 < p ≤ 2`, closedness inside the compact original action
level set proves compactness of the actual isospectral set, as asserted
in Lemma 17.5(i), with no finite-gap hypothesis.

Public checks cover invariance of full actions under the actual source
phase rotation at exponent 3, recovery of algebraic multiplicities from
discriminants at complex potentials, preservation of spectral data under
source-norm limits at exponent 3, and norm-convergent subsequences of
actual isospectral sequences at exponent 3/2.

The converse torus inclusion in Lemma 17.5(i) remains: lift Hilbert
coordinate rotations to the action Hamiltonian flows, prove they preserve
the discriminant, pass to limits of finite rotations, and transfer the
result to `1 < p < 2`. Equality of action level sets and actual isospectral
sets has not yet been proved. The full dissertation remains unfinished.

## Previous progress: compact action tori and source action level sets

`DominatedCompactness.lean` proves that a closed family of complex
coefficient sequences dominated coordinatewise by one finite-exponent
sequence is compact in the full norm topology. The existing uniform-tail
subsequence theorem supplies norm convergence. Continuous complex
inclusion and real projection give the corresponding real-sequence
criterion.

`RealActionTorus.lean` defines the torus with prescribed quadratic
actions `(x_n² + y_n²)/2 = I_n`. Coordinate evaluation proves closedness.
For any nonempty torus, one reference element bounds both components of
every other element by the sum of its own component magnitudes. This is
a summable majorant, so the torus is norm compact at every finite Banach
exponent, including `p = 1`. Empty tori and infinitely many nonzero actions
are covered. A zero action forces both corresponding coordinates to vanish.

`SourceActionTorus.lean` defines level sets of the original spectral
actions and identifies them exactly with preimages of the coordinate
action tori. These level sets are closed at every finite `p > 1` and
their images lie in the prescribed tori. For `1 < p ≤ 2`, surjectivity
gives equality of those images with the whole tori, and the global
homeomorphism makes the level sets compact in the original source norm.
No finite-gap or finite-support hypothesis is imposed.

Public checks cover compactness at exponents 1 and 3 for arbitrary action
sequences, the fully collapsed torus being exactly the zero target,
source-norm convergent subsequences with all actions retained at `p = 3/2`,
and a unique original source in the action level set for every point of
its coordinate torus.

This proves the compact-torus foundation for Lemma 17.5. The remaining
step is to identify these original action level sets with the actual
isospectral sets, including both directions of the Hilbert assertion
and its exponent transfer. Lemma 17.5 is not yet complete.

## Previous progress: global analytic inverse and open dense range

`SourceBirkhoffGlobalInverse.lean` bundles the actual real Birkhoff map
as a global homeomorphism for every `1 < p ≤ 2`. Its inverse agrees near
each target with the analytic local inverse of Proposition 17.1, hence
is analytic everywhere. Its strict derivative is exactly the inverse of
the original real Birkhoff Jacobian at the recovered source. Global
inverses commute with increasing the exponent within this range, even
for independently constructed normalized families. A family realizing
the bi-real-analytic diffeomorphism of Theorem 14.1(v) is constructed.

`SourceBirkhoffDenseRange.lean` proves that every finite output truncation
belongs to the actual real map's range at every finite exponent above
one. Below two this follows from Proposition 17.3. Above two the finite
block is realized in Hilbert space and the actual source is included
into the larger exponent; map compatibility gives exactly the desired
truncation. Norm convergence of finite truncations proves dense range.
Together with the existing open embedding, the image is open and dense
for every `1 < p < ∞`, as asserted in Theorem 14.1(iv).

Public checks construct the global analytic homeomorphism at `p = 3/2`,
verify that its inverse derivative inverts the original Jacobian at any
target, and compare its source Fourier coefficients with those of an
independently constructed Hilbert inverse. At `p = 3`, arbitrary targets
can be approximated in the full target norm by actual images, and every
finite truncation has an actual finite-gap preimage.

Next continue with Lemma 17.5: define the action tori, prove their
compactness, and identify the images of actual isospectral sets.
That identification and the remaining dissertation results are still
unfinished. Surjectivity for `p > 2` is not claimed.

## Previous progress: Proposition 17.3

`SourceHilbertFiniteActionReduction.lean` composes the actual Hilbert
angle flows in list order. Admissibility checks each nonnegative time
against the current selected action, so every move stops before collapse.
All actions are nonincreasing, and every unselected rectangular coordinate
is retained. The displacements sum to an element of every finite source
exponent above one. For `p ≤ 2`, this gives literal equality after inclusion
into Hilbert space and proves that an admissible finite sequence preserves
whether its source belongs to exponent `p`.

Finite-set induction constructs such a list making every selected action
smaller than any prescribed positive bound. Already small actions,
including closed gaps, are skipped. The resulting theorem also retains
every outside coordinate and supplies the displacement at all exponents.

`RealActionTail.lean` transfers finite coordinate blocks between arbitrary
real sequence exponents. A bound on their quadratic actions bounds the
block norm. Finite truncations of any target in a finite exponent converge,
so small enough actions on a suitable finite block, with the original
outside coordinates, yield a target of arbitrarily small norm in that
same exponent. The candidate can initially be given only in Hilbert space.

`SourceBirkhoffProposition17_3.lean` takes the Hilbert preimage of an
arbitrary exponent-`p` target. The constructed finite reductions put its
output inside the neighborhood of zero already in the range of the
exponent-`p` map. Exponent compatibility and Hilbert injectivity identify
the reduced source with this exponent-`p` preimage. The total displacement
then recovers the original source in exponent `p`. This proves Proposition
17.3 for every `1 < p ≤ 2`, without a supplied preimage or range premise.
Together with Proposition 17.2, a normalized family with bijective actual
real map is constructed throughout this range.

Public checks construct a family with a unique source for every target at
`p = 3/2`, apply different strict bounds to two signed modes while retaining
an unrelated mode, verify preservation of nonmembership in the stronger
source space, and exercise the inclusive endpoint `p = 2`.

Proposition 17.3 is complete. Next package the global analytic inverse
for `1 < p ≤ 2` and continue to the isospectral-torus statements of
Lemma 17.5. Surjectivity for `p > 2` is not claimed.

## Previous progress: complete Lemma 17.4

`ConjugateCotangentLinear.lean` makes conjugate-exponent cotangent
recovery a bounded complex-linear map. For source pairs it reconstructs
the Hamiltonian direction with the original Fourier reflection and Poisson
signs; its inclusion into Hilbert space is the original Hamiltonian.

`SourceHilbertAngleStrongRegularity.lean` applies this to the actual angle
cotangent. For conjugate exponents `p ≤ 2 ≤ q`, the Hilbert angle vector
has an exponent-`p` representative that depends analytically on the source
near every real source with its selected gap open. The identification
allows independently constructed normalized families at the two exponents.

`IntegralDisplacement.lean` proves a Banach-space integration result:
a continuous stronger-space representative of a curve's derivative
integrates to its displacement through a bounded linear inclusion. The
result holds on the entire interval before a positive terminal time,
including negative times.

`SourceHilbertAngleDisplacement.lean` uses that result for `1 < p < 2`
and continuous Hilbert inclusion for `p ≥ 2`. It constructs a continuous
curve in the actual real source space of every finite exponent above one,
with precisely the Fourier coefficients of the original flow displacement.
No membership of the initial Hilbert source in the stronger space is
assumed. The public theorem `lemma17_4` combines this with the initial
value, continuous differentiability, actual Hamiltonian equation,
uniqueness, and vanishing-action limit. Lemma 17.4 is now complete.

Public checks cover the sign and reflected frequency of an imaginary
cotangent at conjugate exponents 3 and 3/2, recovery of a negative-time
displacement by integration, and the exponent-3/2 realization of a
general Hilbert source's displacement. The constructed-family check now
includes every exponent's continuous displacement in the same theorem
as existence, uniqueness, and the action limit.

Next use finite successive action reductions and a small action tail
to prove Proposition 17.3 for `1 < p < 2`. That proposition and
surjectivity outside the Hilbert case are not yet complete.

## Previous progress: actual angle Hamiltonian flow and uniqueness

`SourceAngularThetaRectangularDifferential.lean` identifies the actual
branch-independent angle cotangent with `(-y_k dx_k + x_k dy_k)/(2 I_k)`.
The identity holds for every finite exponent above one and transfers
between independently constructed normalized families. Canonical Poisson
relations then give both rectangular velocities along the actual angle
Hamiltonian, including unselected closed gaps.

`SourceAngularThetaHamiltonian.lean` defines that Hamiltonian vector with
the original source Fourier reflection and Poisson signs. It proves
analyticity on the selected open-gap domain and preservation of the real
source form for exponents at least two.

`SourceHilbertAngleHamiltonian.lean` proves that the complex Birkhoff
Jacobian sends this vector to the explicit radial vector. Jacobian
injectivity identifies it with the previously constructed inverse-Jacobian
vector. The lifted action-reduction curve therefore solves the original
angle-Hamiltonian equation for all times before collapse; its selected
gap remains open throughout that interval.

`AutonomousODEUniqueness.lean` propagates local ODE uniqueness across a
preconnected open time domain. Smoothness only near the reference
trajectory is needed, without a global Lipschitz constant.
`SourceHilbertAngleFlowUnique.lean` applies this to prove uniqueness of
the actual Hamiltonian solution on the whole interval `(-∞, I_k(φ₀))`.
It packages the initial value, continuous differentiability, differential
equation, uniqueness, and vanishing-action limit for every real source
whose selected gap is open. Thus Lemma 17.4's initial-value statement
and part (i) are proved.

Public checks cover uniqueness for the nonglobally-Lipschitz scalar field
`x²`, the zero velocity of every nonselected mode at exponent 3, and the
construction of a normalized family with the full Hilbert existence,
uniqueness, and action-limit conclusions without supplied flow premises.

Lemma 17.4(ii) remains: the source displacement must be continuous in
every finite exponent above one. Next obtain the stronger-exponent
regularity of the angle Hamiltonian from its compatible cotangents and
integrate the vector field in that exponent. Proposition 17.3 and
surjectivity outside the Hilbert case are not yet complete.

## Previous progress: Hilbert action-reduction curves

`RealActionReduction.lean` constructs the explicit one-mode radial curve
in every real sequence space. For positive initial action `a`, the selected
coordinate pair is multiplied by `sqrt(1-t/a)`. Its action is exactly `a-t`
for `t ≤ a`; every other coordinate and action is unchanged. The curve is
continuous through collapse and smooth for all `t < a`, including negative
times. Its derivative solves the autonomous radial equation with velocity
`-(x_k,y_k)/(2 I_k)` in the selected mode.

`SourceHilbertActionReduction.lean` lifts that curve through the proved
global Hilbert Birkhoff inverse. The original spectral actions satisfy the
same exact reduction and conservation laws. The lifted curve starts at
the given source, is smooth before collapse, and solves the differential
equation whose vector field is the radial vector pulled back by the actual
inverse Jacobian. The derivative of the global inverse is explicitly
identified with that inverse Jacobian.

At the collapse time the curve converges in the source norm to an actual
source whose selected periodic gap is closed. Every other action remains
fixed. A further theorem chooses a finite nonnegative time strictly before
collapse at which the selected action is positive and below any prescribed
positive threshold.

Public checks cover the exact negative velocity of a 3-4 coordinate pair,
an unrelated nonzero mode, action growth at negative time, the source-space
differential equation, and the source-norm limit with its closed gap and
conserved other actions.

This completes the radial-curve construction needed for Lemma 17.4. The
identification of its pulled-back vector with the actual angle Hamiltonian,
uniqueness for that Hamiltonian equation, and continuity of the displacement
in every stronger exponent remain to be proved. Proposition 17.3 and
surjectivity outside the Hilbert case are not yet complete. Next establish
the Hamiltonian identification and stronger-exponent displacement estimate,
then use finite successive action reductions for Proposition 17.3.

## Previous progress: global Hilbert inverse and Proposition 17.2

`ClosedLocalHomeomorph.lean` proves that a closed local homeomorphism
from a Hausdorff space to a preconnected target is bijective whenever it
has one singleton fiber. The locus of fibers with at most one point is
both open and closed; the range is also open and closed. The proof applies
to infinite-dimensional spaces without local compactness assumptions.

`SourceBirkhoffLocalHomeomorph.lean` packages Proposition 17.1 as a local
homeomorphism for the actual real Birkhoff map at every finite exponent
above one. `SourceHilbertGlobalInverse.lean` combines this with Hilbert
properness and the singleton zero fiber to prove global Hilbert
bijectivity. It bundles the original spectral map as a homeomorphism and
proves its global inverse analytic at every target point by agreement
with the existing analytic local inverses. A normalized family realizing
this global real analytic homeomorphism is constructed.

`SourceBirkhoffProposition17_2.lean` discharges the Hilbert injectivity
premise in the existing exponent-extension argument. Proposition 17.2
is now proved for every `1 < p < ∞`. Each actual real Birkhoff map is an
open embedding. The proof above two uses finite-gap collision reduction;
below two it uses coefficient-preserving exponent inclusion.

Public checks give a unique source for every Hilbert target, verify
analyticity of the global inverse at arbitrary targets, eliminate
collisions at exponent 3, construct an injective family at exponent 3/2,
and verify openness of images of arbitrary open source sets.

The global Hilbert inverse and Proposition 17.2 are complete. Surjectivity
at other exponents is not claimed. Next is Proposition 17.3 for `1 < p < 2`,
including the action-angle flow and regularity argument of Lemma 17.4.
The remaining dissertation results are still in progress.

## Previous progress: bounded action continuity and Hilbert properness

`SourceActionSegmentCircle.lean` strengthens the common action contour:
one constructed circle stays outside every periodic cut along every point
of every eventual real interpolation segment. The construction works at
all finite exponents above one, including collapsed selected gaps.

`SquareRootPathStability.lean` proves a quantitative branch-preservation
lemma. A continuous root path anchored at its initial value cannot cross
the separating circle while its square stays close. Applied to the actual
jointly analytic canonical root and the proved discriminant limits,
`SourceCanonicalRootCoefficientContinuity.lean` gives uniform convergence
of the correctly normalized root on compact sets valid along the segments.
No replacement by a principal square root or unproved sign choice occurs.

`UniformInverseCompact.lean` supplies uniform inversion near compact nonzero
limits. `SourceActionCoefficientContinuity.lean` combines the canonical-root
and spectral-derivative limits to prove uniform convergence of the actual
critical-root quotient, then convergence of its weighted circle integral.
Every original indexed real Hilbert action converges under bounded
coefficient limits. The public theorem constructs its contour, requires
only first-component coefficient limits, permits countably generated
filters, and includes open and collapsed gaps.

`SourceHilbertProperness.lean` discharges
`SourceHilbertActionsContinuousOnBoundedCoefficients`. The action-mass
trace identity and coefficient compactness now prove properness of the
actual Hilbert action sequence map and the real Hilbert Birkhoff map,
without a separate spectral-continuity premise. An existence theorem
constructs a normalized family with both proper maps.

Public checks retain a negative root branch, construct segment-wide circles
at exponent 3, take action limits at collapsed gaps, verify the discharged
continuity obligation, and obtain compact preimages of arbitrary compact
Birkhoff target sets in the original source norm.

Hilbert properness and bounded-coefficient action continuity are complete.
Global injectivity and surjectivity, the global inverse, and the remaining
claims of Proposition 17.2 and subsequent chapters are not yet complete.
Next combine Hilbert properness with the proved local inverse and zero fiber,
then use exponent compatibility for the global Birkhoff conclusions.

## Previous progress: discriminant and spectral derivative coefficient limits

`UniformDualCoefficientLimits.lean` moves finite Fourier truncation across
the bilinear coefficient pairing and proves an explicit head/tail bound.
A bounded coefficient-null family pairs to zero uniformly against every
sequence dominated by one fixed finite-exponent majorant. This is a general
conjugate-exponent result; it does not require norm convergence of the input.

`SourceDiscriminantCoefficientContinuity.lean` applies that argument to the
actual two Hilbert cotangent coefficient sequences. Cotangent values on
bounded coefficient-null directions tend uniformly to zero over simultaneous
bounded source and spectral balls. Differentiating the actual discriminant
along straight real-parameter source segments and applying the mean value
bound gives uniform discriminant convergence on every bounded spectral set.
The theorem permits arbitrary filters and complex sources, with no real-type
condition or strong source-norm convergence. Pointwise and locally uniform
versions are exported.

`SourceDiscriminantDerivativeCoefficientContinuity.lean` applies the Cauchy
integral convergence theorem to obtain the same locally uniform and bounded-set
uniform convergence for the actual spectral derivative. Thus the numerator
of the action integrand now converges on every fixed common action circle.

Public checks cover both functions on arbitrary fixed circles, the real-source
specialization using only first-component coefficient limits, and reflected
unit Fourier modes whose source norms stay bounded away from zero while their
entire discriminants and spectral derivatives converge to the free functions.

Next prove convergence of the correctly normalized canonical square-root
branch on the common action circles, then pass to the quotient and action
integral. Convergence of the discriminant square alone does not choose a
square-root sign. `SourceHilbertActionsContinuousOnBoundedCoefficients`,
unconditional properness, and Proposition 17.2 remain unfinished.

## Previous progress: uniform Hilbert discriminant cotangent tails

`ClassicalDiscriminantGradientEnergy.lean` bounds the actual physical
discriminant gradient and its transported diagonal term by cubic solution
growth controlled by integrated potential energy. The time derivative has
an integrable potential factor. Its integral norm, and hence every Fourier
coefficient of either gradient component, is bounded by the same energy-only
constant. The estimate includes frequency zero and imposes no physical
supremum bound. The generic Fourier estimate now accepts an integrated
derivative bound; its previous supremum-bound API is retained.

`SourceDiscriminantCotangentDecay.lean` transfers that estimate through exact
finite-source realization and density to every complex Hilbert source.
Both actual cotangent coefficient sequences satisfy an explicit bound of
the form `C(M,R)/(1+|n|)` on simultaneous source-norm and spectral balls.
One square-summable majorant controls the entire family. The reusable
`DominatedTails.lean` theorem then gives uniformly small Fourier tails:
the finite cutoff is chosen before the potential and spectral parameter,
and every larger cutoff works for both components.

Public checks cover the tail criterion at exponent 3, the zero-frequency
cotangent direction, the physical Fourier normalization, and a common
cutoff for arbitrary bounded complex source families with moving spectral
parameters. No real-type condition or coefficient convergence is needed
for these uniform estimates.

Next use the uniform cotangent tails along bounded interpolation segments
to prove discriminant continuity under coefficient limits, then control its
spectral derivative and the canonical-root branch on common action circles.
`SourceHilbertActionsContinuousOnBoundedCoefficients` remains unproved;
unconditional properness and Proposition 17.2 remain unfinished.

## Previous progress: canonical coefficient continuity and common action circles

`BoundedSegmentLimits.lean` proves that interpolation from a fixed vector to
a bounded family stays bounded and that every converging linear coordinate
converges uniformly along those segments. `SourceSegmentResolventPersistence.lean`
then proves eventual common resolvent membership on any compact spectral set
for every point of every segment, with one eventual index for all parameters.

`SourceSpectralSelectionCoefficientContinuity.lean` upgrades strong continuity
of any periodic eigenvalue selection on real sources to continuity under
bounded coefficient limits. Spectral discreteness supplies arbitrarily small
circles around the limit value. Along each real interpolation segment the
selection is continuous and cannot cross the common spectral-free circle.
This retains its original label without assuming a common cluster assignment.

`SourceCanonicalCoefficientContinuity.lean` applies that argument to both
actual canonical periodic endpoints. Every fixed original indexed endpoint,
midpoint, and gap converges at every finite `p>1`, including closed gaps.
The real-type Fourier relation makes first-component coefficient convergence
sufficient. These theorems allow arbitrary filters and do not assume strong
convergence, an externally chosen contour, or a positive gap.

`SourceActionCoefficientCircle.lean` constructs one real-centered circle for
each selected action, valid at the limit and eventually for the family. The
selected segment stays inside, and convergence of adjacent endpoints plus
global real spectral ordering keeps every other gap outside the closed disc.
The actual indexed actions therefore use this same circle, including at
collapsed gaps. Convergence of their integrands is not yet proved.

Public checks cover uniform segment persistence for complex sources, actual
indexed gap convergence at exponent 3, construction of a common Hilbert action
circle, and real sources formed from moving reflected unit Fourier modes.
Those sources have norms bounded away from zero while both actual canonical
endpoints at every fixed index converge to the corresponding free value.

Next prove convergence of the critical-root quotient on the constructed
common action circles. `SourceHilbertActionsContinuousOnBoundedCoefficients`
remains unproved; unconditional properness and Proposition 17.2 remain
unfinished. The previously planned global indexed-pair continuity step is
now complete for bounded coefficient limits of real sources.

## Previous milestone: spectral trace and ordered eigenvalue limits

`ContourOperatorCoefficientConvergence.lean` identifies the bounded spectral
restriction `L P` with the first weighted resolvent integral. Every continuous
scalar weight on a spectral-free limit circle preserves operator-norm
convergence of the integrals under bounded coefficient limits. In particular,
the bounded spectral restrictions converge, without assuming norm convergence
of the original potentials or their unbounded operators.

`ContourTraceCoefficientConvergence.lean` transports each varying contour
range to the fixed finite-dimensional limit range. The transport tends to the
identity, the reduced operators converge in norm, and continuity of trace on
this fixed space proves convergence of every intrinsic power trace. The
contour midpoint and squared-gap expressions consequently converge as well.

`RealSpectralPairCoefficientConvergence.lean` reconstructs an ordered real
rank-two eigenvalue pair from the midpoint and the nonnegative square root of
the squared gap. Both endpoints converge, including when they coincide at the
limit. This theorem explicitly assumes that the specified pair eventually
exhausts the chosen circle; it derives eventual rank two from the limit rank.
A separate unconditional corollary at a zero coefficient limit proves
midpoint limit `π n` and squared-gap limit zero in every fixed free disk.
`SourceSpectralTraceCoefficientConvergence.lean` exports the restriction,
power-trace, symmetric-expression, and ordered-pair limits in period-one
source coordinates. The convergence theorems cover finite `p>1` and countably
generated filters; the weighted restriction identity also covers `p=1`.

Public checks cover a cubic resolvent weight at exponent 3, arbitrary source
power traces, ordered endpoints converging to a double eigenvalue, and moving
unit Fourier modes whose norms stay one but whose fixed-disk midpoint and
squared gap converge to the free values.

The global indexed pair identification and continuity of the critical-root
quotient and individual actions under bounded coefficient limits remain.
`SourceHilbertActionsContinuousOnBoundedCoefficients` is still unproved;
unconditional properness and Proposition 17.2 remain unfinished.

Next prove compact resolvent-set persistence uniformly along the real line
segments from the limit source to the approximating sources. These segments
remain bounded and converge coefficientwise to the same limit, uniformly in
the segment parameter. Existing strong continuity of canonical endpoints
along each segment should then prevent them from crossing an isolating
circle, supplying the missing global indexed-pair identification. This is a
planned proof route, not yet a formalized result.

## Previous milestone: compact spectral convergence and cluster stability

`ResolventReferenceChange.lean` factors the spectral pencil through a full
resolvent at any common reference point. Invertibility of the bounded transition
operator characterizes the entire resolvent set. Operator-norm convergence at
the reference point therefore gives eventual spectral membership and resolvent
convergence at every limit resolvent parameter, including moving parameters.
This reference-change result also covers the endpoint exponent `p=1`.

`ResolventCompactConvergence.lean` upgrades this to locally uniform convergence
on the limit resolvent set and eventual common spectral membership on each
compact subset. The previously constructed high reference point supplies these
conclusions for every bounded coefficientwise convergent family at finite
`p>1`. On every spectral-free limit circle, the normalized contour projections
converge in operator norm. The contour limit theorem uses a countably generated
filter, including ordinary sequences.

`SpectralClusterCoefficientStability.lean` proves eventual equality of the
finite projection ranks and hence of the total enclosed algebraic
multiplicities. Eigenvalues may split or coalesce inside the circle.
`SourceSpectralCoefficientConvergence.lean` supplies the corresponding
compact-set, contour, rank, and multiplicity theorems in period-one source
coordinates, without an assumption of strong convergence of the potentials.

Public checks cover reference transport at `p=1`, uniform convergence on
arbitrary compact sets at source exponent 3, preservation of a cluster with
multiplicity two, and convergence of contour projections for moving unit
Fourier modes whose potential norms do not tend to zero.

Next identify the limiting indexed spectral data and prove continuity of
individual actions under bounded coefficient limits.
`SourceHilbertActionsContinuousOnBoundedCoefficients` remains unproved;
unconditional properness and Proposition 17.2 remain unfinished.

## Previous milestone: norm-resolvent limits from bounded coefficient limits

`ConvolutionSandwichCoefficientContinuity.lean` views two-sided convolution
as a linear map from potentials into bounded operators. Cutting off both
multiplier symbols leaves dependence on only finitely many potential
coefficients. The cutoffs converge in operator norm, proving compactness of
the potential-to-operator map and its continuity along bounded coefficientwise
limits whenever the conjugate symbol exponent is finite.

`DoubleResolventCoefficientContinuity.lean` identifies the existing double
free resolvent with a pair of these convolution sandwiches. Consequently
`R₀ Φ R₀ : FLᵖ → FL¹` converges in operator norm under bounded coefficientwise
convergence of potentials, at each fixed parameter off the free lattice.
The theorem is also provided in the actual period-one source coordinates.

`NeumannResolventCoefficientContinuity.lean` retains summable output for the
full Neumann resolvent. Its fixed-point equation bounds the difference of
two full resolvents by the difference of their double free resolvents, with
a common positive Neumann margin. The existing height-decay estimate then
constructs this margin uniformly on every bounded family. For every bounded
coefficientwise convergent family, a positive height is constructed above
which every full resolvent exists and converges in operator norm. The theorem
covers all finite exponents `p>1`, complex potentials, and period-one source
pairs; no externally supplied spectral-membership or smallness premise is
needed in the final common-height statement.

Public examples verify compact potential dependence, convergence for moving
unit Fourier modes whose source norms stay one, the double-resolvent result
at exponent 3, the explicit full-resolvent difference estimate, and the
constructed common-height result for actual Hilbert source pairs.

Next propagate this norm-resolvent limit from the common high region to
spectral contours and prove continuity of the spectral data and individual
actions. `SourceHilbertActionsContinuousOnBoundedCoefficients` is still an
unproved obligation; unconditional properness and Proposition 17.2 remain
unfinished.

## Previous milestone: coefficient compactness and the properness criterion

`CoefficientCompactness.lean` proves that every bounded sequence of Fourier
coefficients has a coefficientwise convergent subsequence with a limit in the
same `ℓᵖ` space, including `p=∞`. The proof combines compact coordinate balls
with the sequence-space bound on pointwise limits. For `ℓ²`, an exact Fourier
truncation energy identity upgrades coefficientwise convergence to norm
convergence whenever the squared norms converge to the limit's squared norm.

`SourceHilbertCoefficientCompactness.lean` carries this construction to real
sources, preserving the conjugate-reflection relation. The first component
determines the second, and the original Hilbert pair norm has exactly twice
the first component's squared norm.

`SourceHilbertActionPropernessCriterion.lean` uses the proved trace identity
to show that bounded action sequences have bounded source preimages and that
convergence of actions rules out energy loss at a coefficientwise source
limit. It then proves compactness of preimages of compact action sets, and
hence properness of both the action map and the real Birkhoff map, conditional
on `SourceHilbertActionsContinuousOnBoundedCoefficients`.

That named proposition is an explicit, still unproved spectral obligation:
each individual real action must converge along bounded, coefficientwise
convergent real Hilbert source sequences. The compactness, boundedness, and
strong-convergence parts are proved; unconditional properness and Proposition
17.2 are not yet claimed.

Public examples include moving unit Fourier modes: their coefficients tend
to zero while their norms stay one. This checks the essential distinction
between coefficient compactness and norm compactness. Further examples cover
real-source extraction at exponent 3, the exact action norm, the strong-limit
upgrade, and the conditional properness theorems.

Next prove the named spectral continuity obligation from continuity of the
spectral data under bounded coefficient limits, then apply the properness
criterion and the singleton zero fiber toward global invertibility.

## Previous milestone: the full Hilbert action–mass trace formula

`SourceRealActionRealCenteredCircle.lean` proves that every real-centered
isolating circle computes its indexed real action, including collapsed gaps,
at every finite exponent `p>1`.

`SourceFiniteGapActionTrace.lean` applies finite-hole contour decomposition
to the weighted, regularized logarithmic derivative around the finitely many
open gaps. The individual circles compute the actions, and the exterior
circle computes source mass. Thus the finite action sum equals source mass;
analyticity through collapsed gaps handles all other spectral points.

`SourceHilbertActionTrace.lean` extends this equality by continuity and
actual finite-gap density to every real Hilbert source. In the repository's
pair normalization, the resulting formula is

`∑ₙ Iₙ(φ) = ‖φ‖²/2`.

The public theorem `sourceHilbert_sum_actions_eq_half_norm_sq` needs neither
a finite-gap assumption nor a chosen Birkhoff family. For every constructed
Hilbert Birkhoff family, the squared norms of its two real output components
sum to the squared source norm. Consequently its zero fiber is exactly `{0}`.

Public examples cover a real-centered circle at exponent 3, the vanishing
of a finite-gap source with no open gaps, the unconditional infinite trace,
the zero-fiber consequence, and the two-component norm identity.

The action/mass trace identity is now proved. Weak continuity of the spectral
actions and properness of the action map remain next steps toward Proposition
17.2 and global injectivity; the norm identity alone does not prove properness.

## Previous milestone: mass identification and the evaluated exterior contour

The analytic remainder's local primitive now gives an exterior primitive
with coefficient `2i h(0)`. Comparing it with the mass-normalized actual
primitive proves `h(0) = -i sourceHilbertMass/2`. Thus every sufficiently
large weighted contour of the regularized quotient equals `π` times source
mass, or equivalently `π ‖φ‖²/2`, for real Hilbert finite-gap sources.
All auxiliary regularity, normalization, and coefficient premises are
fully discharged.

Next identify the finite collection of isolating-circle integrals with the
indexed real actions and apply finite-hole decomposition to their weighted
regularized quotient. This will give the finite-gap action/mass trace
identity; the existing continuity-and-density theorem extends it to every
real Hilbert source. Spectral-action weak continuity and properness remain
later steps toward global injectivity.

## Previous progress: exact exterior remainder and contour coefficient

The analytic inversion germ now has zero linear coefficient, proved from
the actual zero exterior period. Two divided differences produce an exact
analytic remainder: `q(z) = -i + z⁻² h(1/z)`. The weighted exterior circle
integral is exactly `2πi h(0)`, at all finite exponents `p>1` for actual
finite-gap sources, without any assumed residue or expansion coefficient.

Next take a primitive `H` of `h` near zero with `H(0)=0`. Then
`-iz-H(1/z)` has derivative `q(z)` on the exterior. Compare it along the
upper imaginary ray with the already mass-normalized exterior primitive;
the ray limit should give `h(0) = -i sourceHilbertMass/2`. Finally consolidate
the individual action contours. Density extension, spectral-action weak
continuity, and properness remain later steps toward global injectivity.

## Previous progress: removability and the leading value at infinity

The logarithmic derivative is now uniformly bounded on sufficiently large
half-integer circles by the free derivative and root asymptotics. Maximum
modulus extends that bound over a full exterior region. At finite-gap sources,
inversion and the removable-singularity theorem construct an analytic germ
at infinity, with the exact leading value `-i`. These conclusions hold for
every finite exponent `p>1`, without extra analytic or quantitative premises.

Next extract the higher coefficients of this analytic germ. The established
zero exterior period should remove the inverse-frequency term; compare the
next coefficient with the mass-normalized exterior primitive's ray limit.
Then evaluate the weighted contour to prove the finite-gap action/mass trace
identity. Density extension, spectral-action weak continuity, and properness
remain subsequent steps toward global injectivity.

## Previous progress: the mass-normalized exterior primitive

The finite-hole contour theorem and actual disjoint isolating circles now
prove zero period for the regularized quotient on every sufficiently large
circle. A general circular-hole filling argument constructs a primitive on
the whole exterior. This supplies the actual finite-gap exterior primitive
at every finite `p>1`, without period or contour-geometry assumptions.
At the Hilbert exponent, one additive correction gives this same primitive
the exact coefficient `2y (F(iy)-y) → ‖φ‖²/2` on the upper imaginary ray.

Next combine the existing exterior discriminant-derivative and canonical-root
asymptotics on large circles separated from the free lattice. Use those
bounds to establish removable-singularity control for the exterior quotient
at infinity, so that the ray coefficient determines a Laurent coefficient.
Then consolidate and
evaluate the weighted action contours to prove the finite-gap action/mass
trace formula. Its density extension, spectral-action weak continuity,
and properness remain later steps toward global injectivity.

## Previous progress: the finite-gap exterior spectral functions

The canonical root and Floquet multiplier now extend analytically through
all collapsed gaps at every real source and finite exponent `p>1`. The
multiplier stays nonzero, and its logarithmic derivative is the analytic
extension of `Δ'/root`. For finite-gap sources, compactness of the finite
union of open-gap segments gives a full exterior region of analyticity.

Next establish zero exterior period for the filled quotient, construct its
exterior primitive, and match it to the mass-normalized upper primitive.
Then control the expansion at infinity and consolidate the action contours
to prove the finite-gap action/mass trace identity. A vertical-ray limit
alone still does not suffice. Density, spectral-action weak continuity,
and properness remain later steps toward global injectivity.

## Previous progress: the mass-normalized upper primitive

The canonical Floquet multiplier is analytic and nonzero off the gap cuts;
its local logarithmic derivative is the actual quotient `Δ'/root`. The root's
upper normalization fixes its sign, and its square identity transfers the
source mass coefficient to the root and multiplier. The eventual principal
logarithm satisfies `2y (log multiplier(iy)-y) → sourceHilbertMass φ` for
absolutely summable real Hilbert sources. Matching any global upper-half-plane
primitive to the logarithm up to a constant constructs a mass-normalized
primitive on the entire upper half-plane. At real finite-gap sources its
coefficient is exactly `‖φ‖²/2`, with no remaining regularity assumption.

Next continue this primitive across the closed gaps to an exterior domain
containing only finitely many open cuts. Prove the required expansion at
infinity, using global growth or removable-singularity control; the vertical
coefficient limit alone is not a contour asymptotic. The library has annular
zero-period primitives and the root derivative identity available. Consolidate
the finite action contours and identify the contour coefficient to establish
the finite-gap action/mass trace formula. The existing density reduction then
extends it to every real Hilbert source. Spectral-action weak continuity and
properness remain subsequent obligations for global injectivity.

## Previous progress: the canonical finite-gap source mass coefficient

Absolute period-one Fourier synthesis now gives the actual continuous
representative and exact physical/source mass equality by bilinear
Parseval. The canonical discriminant of every absolutely summable complex
Hilbert source recovers `sourceHilbertMass` as its first upper coefficient.
The finite-gap Sobolev bootstrap discharges summability, giving the exact
limit `2y (exp(-y) Δφ(iy)-1) → ‖φ‖²/2` for real Hilbert finite-gap sources.
Equal canonical discriminants consequently give equal source norms there.

Next recover the same first coefficient for the canonical root and the
Floquet multiplier `(Δ + root)/2`. The existing root/free asymptotic uses
`-2i sin(z)`, positive along the upper imaginary ray, and the square identity
`root² = Δ²-4` fixes the difference from the discriminant at this order.
Establish the logarithmic multiplier's derivative `Δ'/root` and match it
to the existing half-plane primitive, retaining its additive constant.
Then consolidate the finitely many action contours into an exterior contour
to prove the finite-gap action/mass trace identity. The established density
reduction extends that identity to all real Hilbert sources. Weak continuity
of spectral actions and properness remain subsequent obligations.

## Previous progress: the first high-energy mass coefficient

For every continuous complex potential, the actual classical discriminant
now satisfies `2y (exp(-y) Δ(iy) - 1) → ∫₀¹ φ₁ φ₂`. The proof isolates an
explicit quadratic Volterra term with an inverse-square remainder, then
uses an exponential approximate identity and dominated convergence. The
remainder estimate is uniform in the real spectral part. Equal classical
discriminants therefore have equal physical masses.

Next use the existing H¹ realization of finite-gap sources and the
classical/canonical discriminant identification to transport this limit.
Prove the Fourier/physical mass identification with the original source
normalization. Then identify the inverse-frequency coefficient of the
canonical discriminant-ratio primitive and combine finite action contours
into an exterior contour to establish the finite-gap trace formula.
The analytic action-sum density reduction is already available. After the
trace identity, prove weak continuity of spectral actions and action-map
properness to finish the remaining Hilbert global injectivity argument.

## Previous progress: analytic ℓ¹ Hilbert action map

The actual action sequence is now holomorphic into complex ℓ¹ on its
constructed domain and real analytic into real ℓ¹ on all real Hilbert
sources. Both sums converge absolutely; directional derivative sums
converge absolutely and equal the derivative of the total. The real
total equals half the sum of the two Birkhoff output norm squares.
The source-mass identity is reduced, by actual finite-gap density, to
its finite-gap case. Properness of the actual action map transfers to
the actual Birkhoff map. The missing trace and properness premises
remain explicit.

Next prove the finite-gap action/mass identity. Consolidate the finitely
many action contours into an exterior contour, integrate the canonical
discriminant-ratio primitive, and identify its inverse-frequency
coefficient with the physical mass. The required mass correction is
stronger than the existing leading half-plane asymptotic. Then obtain
weak continuity of the spectral action coordinates and use the trace
formula to prove action-map properness. Do not replace these actual
spectral assertions with assumed properness or a norm identity.


## Previous progress: global injectivity reduced to Hilbert finite-gap sources

The full exponent-extension step of Proposition 17.2 is proved. Nonlinear
output support equals the open-gap set. Any collision is approximated,
in arbitrary neighborhoods of its two distinct sources, by a finite-gap
collision over one finite output truncation. Above two, finite-gap
Hilbert realizations and full map compatibility lift this collision to
Hilbert space; below two, direct inclusion transports it. Thus global
injectivity for every finite `p>1` follows from injectivity on Hilbert
finite-gap sources. All premises on that missing Hilbert result remain
explicit. The reduction does not assert Proposition 17.2 itself.

Next establish the missing Hilbert finite-gap injectivity result, or
formalize the cited global Hilbert theorem [23, Theorem 19.3]. Reuse the
proved finite-gap reduction to avoid redoing exponent extension. Neither
local invertibility nor density by itself proves this remaining global
uniqueness assertion. Continue with Proposition 17.3 only once this
prerequisite has been addressed or its dependencies made explicit.



A primary reference for the missing Hilbert argument is Grébert–Kappeler–Pöschel,
[Normal Form Theory for the NLS Equation, Global Diffeomorphism section](https://arxiv.org/html/0907.3938#Ch2.S7).
It proves properness of the action map from the action-sum/norm identity,
weak continuity of spectral data, and weak convergence plus convergence
of Hilbert norms. Properness, local invertibility, and the singleton zero
fiber then give global bijectivity by connectedness. This is a concrete
alternative to finite-gap inverse spectral reconstruction. The actual
action-sum identity and weak-continuity prerequisites have not yet been
located in the current library; establish them with the repository's
period and pair-norm normalization before applying this route.

## Previous progress: Proposition 17.1 for every 1 < p < ∞

Proposition 17.1 is complete for the constructed actual Birkhoff family.
The full sequence Jacobian commutes with exponent inclusion, for any two
constructed families. Below two, Hilbert injectivity and injectivity of
the source inclusion give a trivial kernel. Compact normalization and
the Fredholm alternative give bijectivity. Real/complex derivative
compatibility transfers this to the actual real spaces. Both complex
and real analytic local inverses now exist at every real source for
all finite `p>1`, with both inverse identities and the exact derivative.

Next address Proposition 17.2, global injectivity. First identify or
formalize the Hilbert global injectivity result used by the dissertation,
then transport injectivity across exponents using the established local
inverses and compatibility. Do not assume that external theorem as an
axiom or conclude global injectivity from local invertibility alone.


## Previous progress: Proposition 17.1 for 2 ≤ p < ∞

The actual complex and real Jacobians are now bounded isomorphisms at
every real source for `2≤p<∞`. Canonical Hamiltonian directions supply
preimages of all finite output modes; truncation gives dense range, and
the compact perturbation gives bijectivity. Differentiation of the real
inclusion and the source real/imaginary decomposition give real
bijectivity. The inverse function theorem supplies analytic complex and
real local inverses, including both local identities and inverse derivatives.
A constructed-family theorem supplies the actual real local inverses.

Next extend Jacobian injectivity to `1<p<2`, using compatibility with
the Hilbert exponent and its established invertibility, then apply the
compact Fredholm alternative. The real derivative inclusion is already
available at every finite exponent above one. Finish Proposition 17.1
across the full exponent range before continuing with global injectivity.


## Previous progress: Lemma 16.3 at every real source

Theorem 15.2, Lemma 15.3, the free Fourier Jacobian identity, and finite-gap
regularity in all nonnegative Sobolev weights (including H¹) are complete.
Appendix G.3–G.4, finite-p G.5, and both G.6 assertions are proved for
constructed physical H¹ potentials. G.5's printed infinite endpoint is
refuted and stays excluded.

The actual discriminant-gradient disc suprema have common outer ℓp bounds
on H¹ balls. The contour quotient is now controlled as well: for every
`0<r≤π/2`, one cutoff gives a positive lower bound on `|Δ²−4|` and a
uniform bound on `|Δ/(Δ²−4)|` at every point of every distant circle.
The literal quotient-weighted gradient Fourier integrand has a common
summable majorant for finite `p>1`, `q>1+1/p`, including the conjugate
exponent. No pole-avoidance or denominator lower-bound premise is supplied.

The actual midpoint derivatives now form an outer ℓp sequence in source
operator norm at every H¹ potential in a common open neighborhood of the
real locus, for finite `p≥2`. The physical/source gradient identification is
proved for every compatible continuous representative, with reversed Fourier
indices and exact period conventions. Hölder duality bounds the actual source
operator by the two conjugate physical Fourier norms. The existing H¹-ball
majorants and zero-free contours supply the full estimate; no gradient or
majorant premise is left. Collapsed gaps and finite central heads are included.

G.7's exact classical Dirichlet normalization is now proved: at a simple
root, the bilinear quantity `Q=2∫g₁g₂` is nonzero, and the actual derivative
of any continuous local root branch is the integral against `(g₂²,g₁²)/Q`.
Spectral differentiation of the Volterra solution supplies the denominator
identity. The free normalization is exactly two, with the two opposite
exponential waves and factor one half verified explicitly.

The formula is now instantiated at all canonical signed Dirichlet roots of
real continuously represented sources, including the H¹ sources. Completed
source and physical boundary characteristics agree by bounded physical
restriction and density. Both actual root-cotangent Fourier components are
identified at reversed frequency for every finite source exponent `p≥2`.
No simplicity or candidate-gradient premise is added at these real sources.

One common open complex neighborhood now supports this formula at every
index for finite `p≥2`. Both ordinary boundary sequences are analytic and
simple on a common domain for every finite `p>1`, by uniform tail counts and
continuity in the finite central block. The actual H¹ Dirichlet cotangent
has both normalized physical Fourier coefficients throughout the constructed
domain; reality, simplicity, and normalization are not additional premises.

The actual canonical Dirichlet and Neumann roots now have locally uniform
`O(1/|n|)` displacement on physical H¹ balls. The Dirichlet normalization
satisfies `Q−2=O(1/|n|)`, `|Q|≥1`, and an inverse error of the same order.
Combining these with the actual solution bounds gives a uniform pointwise
`O(1/|n|)` error for the normalized gradient against the two exact free waves.
These estimates apply at nearby complex sources and derive all root and
denominator bounds from the source data.

The normalized gradient error now satisfies its exact signed time ODE and a
uniform derivative bound. Its actual unit-interval Fourier coefficients
have a common summable tail majorant on source neighborhoods and H¹ balls
for outer exponent `s>1` and inner exponent `q>1+1/s`. At each fixed source,
the full sequence, including the finite head, is summable; in particular
the conjugate Fourier norms form an outer ℓp sequence for finite `p≥2`.

The actual Dirichlet root derivative minus the explicit free functional
`h ↦ (h₁(-n)+h₂(n))/2` now has a physical Fourier coefficient pair with outer
ℓp summability in the conjugate component-sum norm, for every finite `p≥2`.
Both component identities are proved on a common complex neighborhood of
the entire real source locus. Exponent compatibility and density identify
the free functional at every such source exponent. The actual source
operator error is summable too, including every signed central index.

Both actual derivative estimates now hold on one shared complex domain in
the literal conjugate Fourier pair norm. A bounded scalar functional has a
conjugate coefficient representative with equal norm, proved by finite dual
tests and bounded pointwise limits. Component recovery and frequency
reversal form a bounded complex-linear map from source operators to physical
Fourier gradients. It gives the midpoint estimate and the Dirichlet error
estimate, their full-direction duality formulas, and their outer ℓp
summability, for every finite `p≥2`.

The actual anti-discriminant derivative error now satisfies G.6 at both
canonical boundary sequences of every complex H¹ source, for finite `p≥2`.
Continuous physical realization identifies its full cotangent and Fourier
coefficients. The actual boundary displacement supplies the asymptotic
hypothesis; the resulting operator and conjugate Fourier pair norms are
outer ℓp sequences, including the finite head. The reference is exactly
`i cos(πn) (h₁(-n)−h₂(n))`, proved at every finite `p>1` by exponent
compatibility and density.

The omitted-root-product normalization is now proved at both actual boundary
sequences for every real source and every finite `p>1`. Closed-gap reality
and parity select the signed square root, including collapsed gaps. Generic
ℓp-displaced sampling controls the squared error; both the product and its
reciprocal differ from `cos(πn)` by ℓp sequences, with bounded reciprocals
across all signed indices. The existing open-gap sign APIs remain available.

The finite-gap coordinate derivative estimate is now proved for finite
`p≥2`. The exact free functional selects the signed component with factor
minus two. The closed-gap error splits into the two G.7 errors and three
anti-discriminant corrections controlled by G.6, scalar spectral-derivative
summability, and inverse omitted-product normalization. Finite-gap regularity
constructs a compatible real Hilbert source and physical H¹ representative.
The actual coordinate derivative agrees with the closed-gap expression
outside the finite set of open gaps; finite modification includes every
remaining index. Both source operator norm and the conjugate Fourier pair
norm give outer ℓp sequences, with the local common-domain construction as
the coordinate hypothesis.

Lemma 16.1 is now proved in the full range `1<p<∞`. The Hilbert source
cotangents have every outer exponent above one, by the physical estimates
with inner exponent two. Restriction along coefficient inclusion then
proves the actual real H¹ midpoint, Dirichlet, and anti-discriminant
estimates below two. Finite-gap regularity supplies the physical H¹
representative; the shared closed-gap decomposition and finite modification
complete the full source-operator estimate. Conjugate-gradient recovery
identifies both literal signed Fourier modes and gives exactly the two
ℓp norm sequences. A final existence theorem supplies a constructed
Birkhoff family satisfying the estimates at every real finite-gap source.

Lemma 16.2 is now proved for the full range `1<p<∞`. At finite-gap sources,
the beta correction is a finite sum over the open gaps, with each summand
controlled in ℓp by a shifted reciprocal lattice. The normalized-action
root and complete exponential phase multiplier are summably close to one.
Closed-gap vanishing removes their derivatives in the exact product rule;
Lemma 16.1 and bounded scalar multiplication control the signed derivative
errors, and finite modification includes the open gaps. The normalized sum
and difference give both actual rectangular derivative errors in operator
norm. Exact free Fourier functionals and conjugate-gradient recovery then
prove both literal conjugate-pair norm sequences. A constructed Birkhoff
family supplies the domain and all data for the final existence theorem.

Lemma 16.3 is now proved at every real source for `1<p<∞`. The actual
finite-gap Jacobian remainder has two ℓp row majorants, hence its finite
output truncations converge in operator norm and the remainder is compact.
The existing density of real finite-gap sources and continuity of the
Jacobian extend compactness to all real sources. An explicit bounded
Fourier inverse gives `Aφ = F⁻¹ dφΩ`; the exact identity for `Aφ−Id`
transfers compactness. The normalized Jacobian is complex analytic on the
constructed domain and real analytic on the complete real source space,
and normalization preserves bounded isomorphisms in both directions.
A constructed-family existence theorem supplies the full Lemma 16.3.

Next prove Proposition 17.1: use the compact perturbation and canonical
gradient identities to establish invertibility of the Jacobian, then apply
the inverse function theorem to the actual real Birkhoff map. The sharper
G.1 integral bound, remaining assertions of Theorem 14.1, and later chapters
remain unfinished.

## Milestones

1. **Sequence spaces:** finite truncations, density, weighted coefficients,
   bounded Fourier multipliers, convolution estimates.
2. **Fourier realization:** identify the `p = 2` model with periodic `L²`, prove
   the periodic-distribution interpretation, and fix period-one/period-two and
   signed-component conventions.
3. **First spectral milestone:** domain inclusion, differentiation and potential
   multiplication, the free Zakharov–Shabat resolvent, and compactness.
4. **General analysis:** audit exact convolution, discrete Hilbert transform,
   contour integration, infinite product, and compact operator dependencies.
5. **Spectral data:** localization, multiplicities, finite-dimensional reduction,
   and locally uniform sequence asymptotics (Chapter 1).
6. **Classical dependencies:** formalize the necessary results from reference
   [23], Grébert–Kappeler, *The defocusing NLS equation and its normal form*.
   Conditional development may use explicit hypotheses, but final main theorems
   must instantiate them with proofs.
7. **Coordinates:** actions, angle branches, analytic rectangular coordinates,
   canonical relations, and the precise conclusions of Theorem 14.1.
8. **Applications:** frequencies and Hamiltonian (Theorems 18.1–18.3), dynamics
   (Theorem 18.5), and Sobolev estimates (Theorems 23.1–23.4).

## Statement audit

- Equation (2.4) and Lemma 8.1 on printed page 48 use inconsistent prefactors.
  With the actual zero-potential spectra, the displayed `-2` periodic product
  is zero at `λ=0`, while the displayed `2` antiperiodic product equals two.
  Thus no value of `∆` can satisfy both `∆=f+2=g-2`, even as limits. Euler's
  symmetric free product proves that the periodic prefactor must be `-1`
  (as used in the proof on the same page); the free value at zero forces the
  antiperiodic prefactor to be `4`. The full periodic product's `-4` in (2.1)
  is correct. Retain these distinctions when implementing Section 8; the
  corrected perturbed products are implemented, and their classical
  discriminant identification is proved for continuously represented even
  Hilbert potentials. The intrinsic shifted identity and full product/spectrum
  characterization now extend to every finite p>1.
- Lemma 8.1(iii)'s detailed quotient by `2 cos λ` is undefined at the
  arbitrarily large points `λ=π(n+1/2)`, all outside the stated radius-`π/4`
  free discs. Lean's totalized quotient has error exactly one there for every
  numerator. The formal audit rejects that literal uniform quotient bound;
  it does not reject an additive asymptotic or a suitably restricted quotient.
  Fixed-potential additive trace and derivative asymptotics normalized by
  `exp(|Im λ|)` are now proved on the full free-disc exterior.
- Lemma 6.9's printed page-43 displacement estimate fails with its claimed
  local uniformity at zero. The actual signed single-mode family has roots
  `nπ±t` and Hilbert pair norm squared `2t²`, whereas the printed budget is
  at most `24 C t⁴` for `t≤1` and cutoffs at least one. The formal counterexample
  works in every open neighborhood of zero and beyond every prescribed cutoff.
  It refutes a necessary single-root consequence of the sum estimate; it does
  not assert failure of an eventual estimate for each fixed potential with an
  unrestricted potential-dependent cutoff. Retain an additive leading-tail
  term in the corrected estimate.
- On printed pages 33 and 53, the auxiliary Dirichlet domain is
  `f₋+if₊=0` at both endpoints, but the displayed formula labeled
  `χD*` has the monodromy sign of the auxiliary Neumann domain
  `f₋−if₊=0`; the displayed `χN*` has the Dirichlet sign. This is an
  exact algebraic mismatch with the printed `δ=χD*−χN*` when the
  functions are labeled by their actual endpoint domains. The corrected
  domain-based identity is `δ=χN*−χD*`. Keep the actual domain labels and
  preserve the sine normalization in formal proofs.
- Propositions 6.1 and 6.3 on printed pages 35–36 repeat the nonlinear-only
  budget with locally uniform cutoffs. The scalar-root formalization retains
  the additive leading-tail term required by the single-mode audit. Do not
  present these corrected estimates as proofs of the literal printed bounds;
  the original periodic spectral multiplicities are now identified with the
  scalar analytic orders in all sufficiently distant strips.
- Preserve `1 < p < ∞` versus `1 < p ≤ 2` hypotheses. Do not assume that the
  Birkhoff map is surjective for `p > 2`.
- Treat analyticity on a positive cone using an ambient open extension.
- Encode locally uniform sequence estimates with neighborhood norm bounds.
- Renormalized quantities must be defined by convergent expressions before
  proving identities involving subtraction on the classical domain.
- Preserve the smooth-approximation notion of rough solutions in Section 18.
- The Hessian display on printed page 12 requires correction: the preceding
  expansion for `H` gives `4 - 2 δ_nm`; `-2 δ_nm` is the corresponding Hessian
  of the renormalized Hamiltonian at zero.

## Completion policy

Every implemented theorem must compile without `sorry`, `admit`, or project
axioms. Main-result completion also requires an audit of transitive axioms.
Dependencies and source-page references should be recorded as each theorem is
introduced. Definition-only stubs do not count as proved results.

## Current next proof target

Corollary 13.2, Lemma 15.1, the rectangular construction, and Theorem 15.2
are proved throughout `1 < p < ∞`. Lemma 15.3 is proved on the real
open-gap locus using the actual rectangular derivatives and regular
cotangent pairings. Next extend its three identities across closed gaps
and retain the root family of the sequence-valued Birkhoff map. Preserve
the physical bracket sign `−i` and the mixed value `−δₙₘ`.
The remaining assertions of Theorem 14.1 follow later. See `STATUS.md`
for current coverage; the entries below record the historical sequence
of proof targets.

## Earlier proof targets

The Fourier-side convolution multiplication estimate
`FL^p × FL^{1,p} → FL^p` is now proved for every finite `p≥1`, with a constant
depending only on `p`. The scalar and pair domain inclusions, differentiation,
and the two-component operator are also proved, with explicit period-two signs
and maximum-pair-norm bounds. Both signed free modes have eigenvalue `π n`.

The free resolvent away from `πℤ` is now constructed as a bounded inverse into the
one-derivative domain, with both inverse identities and a spectral-gap bound on
the base space. Compactness follows from operator-norm convergence of finite
Fourier cutoffs. The signed-mode formulas and resolvent identity are also proved.

The `FL^p → FL^1` Hölder estimate is now proved with the conjugate-symbol norms
kept explicit. It bounds `Φ R₀` and supplies a sufficient Neumann condition.
Under that condition, the perturbed inverse is constructed with both inverse
identities, norm bounds, and compactness. For `p=1`, the condition follows from
`|Im z| > ‖φ‖`, giving an admissible parameter for every `l1` potential.

Uniform high-imaginary-part regions are now proved for all finite Banach
exponents. A concrete reciprocal envelope has conjugate norm tending to zero;
Fourier recentering makes the bound uniform in the real part. Each norm ball of
potentials therefore has a common Neumann height, and every finite-p potential
has a compact two-sided inverse at some parameter without a smallness assumption.

The unbounded realization is now a partial linear map on the base space with
exactly the included one-derivative domain. Its domain is dense and its graph is
closed, using the bounded two-sided inverse to characterize graph membership.
Base-norm limits of graph points remain in the graph.

The full resolvent set is now defined by bijectivity of the spectral pencil.
It is nonempty for every potential; the joint domain in potential and parameter
is open. A single totalized resolvent agrees with the Neumann construction and
is jointly complex analytic on its domain, with compact base-space values.

The periodic spectrum is now proved closed and discrete, with finitely many
points in every bounded region. Each point is an eigenvalue with a
finite-dimensional domain eigenspace. The proof includes compact-operator
spectral finiteness away from zero and the reciprocal spectral transformation.

The general resolvent identities, commutation, and explicit joint Fréchet
derivative are now proved. Spectral differentiation gives `∂z R = -R²`; potential
differentiation gives `Dφ R[ψ] = R Φ(ψ) R_D`. The full and free constructions
agree at zero potential, and the pre-Neumann identity is proved without a
smallness restriction when the required resolvents exist.

Periodic root spaces are now defined recursively with domain membership at
each step. Their full union is finite dimensional and attained at a finite level,
using a bounded compact-pencil representation and the proved stabilization of
nonzero compact-operator generalized eigenspaces. The resulting algebraic
multiplicity is positive exactly on the periodic spectrum.

Bounded finite-rank projections onto individual full root spaces are now
constructed from topological kernel/range decompositions of stabilized compact
pencils. They are independent of the reference resolvent parameter, commute
with every resolvent, and have rank equal to algebraic multiplicity. Every base
vector has a unique root-space/complement decomposition.

Distinct full root spaces are now proved disjoint, and their projections
annihilate each other. Finite sums give bounded, compact cluster projections
whose ranges are the sums of root spaces and whose kernels are intersections
of the individual kernels. Cluster rank is the sum of algebraic multiplicities;
composition corresponds to intersection of parameter sets.

The normalized resolvent circle integral from Section 3, equation (1.4), is now
constructed as a bounded operator with a domain-valued factorization and proved
compact. It vanishes on resolvent disks and is unchanged by radius deformation
through resolvent annuli. A root-chain calculation proves identity on enclosed
full root spaces and zero on excluded ones. It commutes with resolvents and
individual spectral projections; composing with a finite cluster projection
selects precisely the parameters inside the circle.

Nested-circle integration now proves the contour projection law, using a
circle-integral interchange theorem and the resolvent identity. Local spectral
finiteness gives nearby resolvent annuli, so radius deformation proves
idempotence for every resolvent circle. Compactness then gives finite rank.
Decomposing the finite-dimensional contour range under a restricted resolvent
identifies it with the enclosed root spaces, proving equality with the algebraic
cluster projection on the whole base space. Rank is the sum of enclosed
algebraic multiplicities; circles enclosing the same spectrum give equal operators.

For a fixed circle, the admissible potential set is open, and the contour
projection is analytic in operator norm. Uniform Banach-algebra inversion along
the circle and bounded linear integration establish this dependence. Projections
less than one apart have the same rank, so total enclosed algebraic multiplicity
is locally constant.

Appendix B.1 is now proved with both stated constants, including `α=0`,
summability, one-sided tail estimates, and translated bilateral lattice bounds.
The reciprocal Sobolev constant is now at most `2p`. Punctured-strip geometry
then gives `freeL1Bound ≤ 2p/r` and the stated `8p/r` operator estimate of
Lemma 3.2(iii), with the library's maximum pair norm. Under `2p * ‖φ‖ < r`,
all spectral circles are admissible and the entire spectrum lies in the union
of disks about `πℤ`.

Lemma 3.2(ii) is also proved: the free `FL^p → FL^1` norm is at most
`4p / abs(Im z)^(1/p) + 1 / abs(Im z)` for nonzero imaginary part. Removing
the central coefficient gives the separate tail and central contributions.
The numerical Neumann region lies in the full resolvent set, where the
resolvent is compact and analytic. Its height bound tends to zero and gives
a common region for every bounded potential set.

The double-resolvent operator, its coefficient formulas, and the factorization
of `(Φ R₀)²` through `FL^1` are proved. The squared Neumann condition yields
a two-sided domain inverse, agrees with the full resolvent, and gives a
quantitative norm bound. One-sided potentials provide verified examples
outside the original Neumann condition, with exact two-term inverses.

Lemma 3.4 is now proved with the explicit maximum-pair-norm constant `32p²`.
The proof splits the reciprocal symbols into near and far windows about the
opposite scalar frequencies. The far symbols decay as `|n|^(-1/p)`, including
the endpoint, while the near-near term contains only the potential tail
`|k| ≥ |n|`. The symmetric tails converge to zero, and the numerical estimate
supplies squared Neumann criteria for entire punctured strips and circles.

Corollary 3.5 is also proved: the height region and the tail estimate give one
central box and one open convex neighborhood of any potential, containing zero,
on which every exterior resolvent is compact and analytic. The periodic
spectrum lies in the exact central box and the high-frequency quarter-pi disks.
The box uses a strict real boundary and a non-strict imaginary boundary; the
coverage proof treats the vertical edges separately.

Lemma 3.6 is proved for even-supported coefficient potentials. Closed
complementary parity subspaces have contractive coordinate projections, which
also preserve the weighted operator domain. The operator, spectral pencil,
full resolvent, and spectral circle integrals satisfy the corresponding
projection identities and preserve both parities. Signed free modes retain
the parity of their spectral index, including negative frequencies.

The high-frequency disk count in Proposition 1.1(i) is proved. A coefficient
induction rules out longer free Jordan chains, and the two signed modes give
algebraic multiplicity two. Contour rank and total multiplicity are constant on
any preconnected admissible family. The uniform convex neighborhood from
Lemma 3.4 therefore gives rank two and total algebraic multiplicity two in
every sufficiently far disk, for every positive radius at most `π/4`.

The parity assertion in Proposition 1.1(i) is also proved. A continuous
preconnected family of projections cannot deform zero into a nonzero
projection, since a nonzero projection has norm at least one. Applied to
the complementary parity part of each contour, this keeps its entire range
in parity `n`. All enclosed generalized eigenvectors have that parity, all
ordinary eigenfunctions have it in the weighted domain, and opposite-parity
inputs are annihilated. The result is uniform on the even potentials in the
same open convex neighborhood used for the multiplicity count.

The closed/open central rectangles and all boundary edges are constructed.
The uniform height estimate is retained at equality, proving that the horizontal
edges, as well as the vertical edges, are resolvent points. One open convex
neighborhood works for every larger positive cutoff. Open, closed, and mixed
boundary conventions then give identical central spectra. The finite central
algebraic spectral projection is constructed, and its free rank is `4N+2`,
by counting the signed indices `-N,…,N` with multiplicity two.

The central projection’s analytic deformation and total count in Proposition
1.1(ii) are now proved. At a sufficiently larger cutoff, a circle of radius
`πK+π/2` avoids the entire localized spectrum and selects exactly the central
box’s spectral values. The full projections are equal, so circle analyticity
and rank stability give central rank and total multiplicity `4K+2`. One open
convex neighborhood works for every larger cutoff. The proof does not require
that the circle contain the corners of the box with the same cutoff.

The central parity split in Proposition 1.1(ii) is now proved. Filtering the
signed free indices gives `N+1` indices in the cutoff’s parity and `N` in the
other. The parity components of the free projector equal the corresponding
filtered spectral clusters. General rank stability for continuous preconnected
families of finite-rank projections transfers their ranks to even potentials.
The component ranges equal the parity intersections of the central spectral
space, so their dimensions are `2N+2` and `2N`, with the larger part switching
with the cutoff’s parity. The total count, parity counts, and analytic
projection families share one neighborhood and one cutoff.

The localization and counting conclusions are now assembled in
`PeriodicCountingData`. One open convex neighborhood and threshold support all
larger cutoffs, central and high-disk multiplicities, parity conclusions, and
analytic projection families. Every noncentral spectral value has a unique disk
index, and each high disk admits a pair of eigenvalues counted with multiplicity,
allowing repetition for a double value.

The real-type clause (iv) is now proved for all finite Banach exponents. Absolute
convergence of coefficient duality and of the double convolution sum establishes
the adjoint identity for conjugate-reflected kernels. Together with the real
free symbols, this gives symmetry on the weighted domain. Its strictly positive
coefficient energy forces every eigenvalue to be real. Spectral discreteness
and the eigenvector characterization then put every nonreal parameter in the
resolvent set, without assuming a Hilbert-space realization.

The analytic local reduction used in Lemma 3.7 is now constructed. The explicit
intertwiner `QP + (1-Q)(1-P)` equals the identity at the reference projection,
has analytic inverse nearby, and induces equivalences of the full ranges.
The contour projection is analytic in the stronger domain norm, so `L P_D`
is bounded and analytic. Its commutation with the spectral projection gives
an analytic operator on a fixed finite-dimensional reference range, with an
exact intertwining identity and the correct enclosed-eigenvector action.

Lemma 3.7 is now proved. The range equivalence conjugates the local reduction
to the intrinsic restriction, so traces of all powers are reference-independent
and analytic. Its eigenvalues are exactly the enclosed spectral values. In
dimension two, the characteristic polynomial and Cayley–Hamilton give the
midpoint and squared-gap identities, including repeated values and Jordan blocks.
One counting neighborhood supports analyticity for every sufficiently high index;
the source normalization `γ²/2` follows from the centered-square trace identity.

Section 4's coefficient boundary spaces are now constructed. Frequency reflection
is an isometry at every Sobolev regularity, and the positive/negative reflected
graphs are closed complementary subspaces with isometric amplitude coordinates
and contractive projections. Both signed boundary modes have free eigenvalue
`π n`. For already-reflected Dirichlet potentials, Lemma 4.4's operator invariance,
restricted bounded operators, projection intertwining, and the opposite signs
in the potential's mode action are proved for every finite Banach exponent.

The full resolvents of both boundary restrictions are now constructed. Each
resolvent set is defined by bijectivity of its own pencil, and normalization
by the fixed free inverse gives both inverse identities, compactness, and joint
analyticity on the full open domain of reflected potentials and parameters.
The periodic resolvent set is their intersection and the periodic spectrum is
the union of the boundary spectra. Both spectra are closed and discrete with
finite bounded portions; compact-resolvent spectral transformation proves that
every spectral point has an eigenvector satisfying the selected boundary condition.
The periodic resolvent and circle projections preserve both boundary spaces.

Boundary root chains now use the actual restricted pencils, and their ambient
images equal the corresponding boundary intersections of periodic root spaces
at every level. The full spaces are finite dimensional and stabilize; their
ranks define algebraic multiplicity and sum to periodic multiplicity. Free
boundary spectra are the full signed lattice, each value has multiplicity one,
and the free quarter-pi contour has rank one in each summand. The free central
algebraic count is `2N+1` for both boundary conditions.

The coefficient counting argument of Theorem 1.4 is now proved. Boundary cluster
spaces are finite sums of the actual restricted full root spaces, and their
images are exactly the boundary intersections of periodic clusters. Bounded
cluster projections on both the boundary and ambient spaces have these ranges
and ranks equal to sums of boundary algebraic multiplicities. Circle projectors
select the same clusters and are analytic in operator norm. Rank constancy on
the reflected part of a common convex neighborhood carries the free counts to
every reflected potential there. `BoundaryCountingData` gives one simple value
in each high disk and `2N+1` central values counted algebraically, for both
conditions and every larger cutoff, together with the periodic localization.

Lemma 4.5 is now proved for the coefficient restrictions. The boundary contour
lifts analytically into its weighted boundary domain; inclusion recovers the
base projector, and applying the original operator through the lift gives a
bounded analytic spectral restriction. A general trace theorem handles varying
finite-dimensional ranges using local projection transport. In dimension one,
its intrinsic trace equals the enclosed eigenvalue. The trace-defined Dirichlet
and Neumann functions are analytic on one open convex neighborhood in the
reflected potential space and agree with the previously counted simple values.
Their free values are `πn`, and they have actual weighted-domain eigenvectors.

The physical piecewise interval extensions and their normalized Fourier formulas
are now proved. Translates of the half-interval kernel give linear maps from
finite period-one coefficient pairs into the actual boundary `ℓp` spaces for
`p>1`, including `∞` for this finite-input construction. The odd reciprocal tail
is not in `ℓ1`, as witnessed by the constant input `(0,1)`. The derivation from
(1.8)–(1.9) corrects the missing normalization on printed page 31.

The Hilbert exponent is now handled uniformly. Mathlib's interval Parseval
identity is connected to our normalization, giving the exact finite-input
energy identity. Dense finite coefficient inclusion then yields unique bounded
interval extensions on all `PairSpace 2`, with boundary membership, injectivity,
and the same energy identity. Odd-index sampling extracts the normalized
shifted Hilbert kernel `2/[π(2k-2n-1)]` as a bounded `ℓ2` operator.

The first non-Hilbert exponent is now proved. The ordinary kernel `-1/j`
and unnormalized shifted kernel `-2/(2j+1)` differ by an absolutely summable
sequence with square decay. Young's inequality handles this correction at
all Banach exponents and supplies the ordinary Hilbert `ℓ2` bound.
The discrete Cotlar identity is proved on finite complex sequences, including
both diagonal square-kernel terms. Hölder `ℓ4 × ℓ4 → ℓ2` and the ordinary
`ℓ2` bound give a support-independent quartic estimate. Density constructs
both ordinary and normalized shifted Hilbert transforms on all `ℓ4`, with
exact agreement with the finite reciprocal formulas.

The general doubling step is now proved: any uniform finite-input estimate at
`p` gives an estimate at `2p`, and density supplies unique continuous ordinary
and shifted operators. The Hölder product and exact square-norm identity work
at general doubled exponents. Induction constructs both operators at every
`2^(n+1)`, with bound `2^n B₂ + (2^n-1)(3M+1)`. These exponents are proved
unbounded. The old quartic product is a specialization of the general product.

The duality step is now proved. Finite conjugate tests detect each truncated
sequence norm, using mathlib's finite Hölder extremizer; density detects the
full norm. Antisymmetry of the finite Hilbert kernel transfers every proved
finite-exponent estimate to the conjugate exponent with the same constant.
The transposition identity extends to arbitrary conjugate inputs. Applying this
to the dyadic estimates constructs ordinary and shifted transforms at
`2, 4/3, 8/7, …`, all in `(1,2]` and arbitrarily close to one.

Finite interpolation and the full Hilbert exponent range are now proved.
Complex phase/exponential families retain finite support, are entire in the
strip parameter, and have normalized endpoint norms. Their finite scalar kernel
pairing is uniformly bounded in the imaginary direction. Mathlib's Hadamard
three-lines theorem bounds the interior pairing by the maximum endpoint constant.
Conjugate unit tests detect the output norm, and rescaling removes normalization.
This constructs `HilbertEstimate.interpolate` with a support-independent bound.

An intermediate-value argument chooses a reciprocal interpolation parameter.
The dyadic and conjugate estimates bracket every finite `p>1`, supplying completed
ordinary and shifted transforms on every `Coeff p`. Uniqueness identifies them
with previous constructions at overlapping exponents. Hölder duality and density
also prove absolute convergence and the exact reciprocal coefficient series on
all inputs. Thus the boundedness part of Appendix C.1 needed here is established.

The full-range interval maps are now constructed. Zero insertion along integer
embeddings is a linear isometry, including the supremum endpoint. Inserting
`a/2` at even indices and `i Sa/2` at odd indices defines the bounded
half-interval Fourier map and recovers the exact physical finite coefficients.
Combining the two input halves with signed reflection defines the Dirichlet
and Neumann maps on all `PairSpace p`, `1<p<∞`. They land in the actual closed
boundary spaces, are bounded and analytic there, and are uniquely determined
by the finite Fourier formulas. At `p=2` they equal the earlier Parseval maps.
The coefficient statement of Lemma 4.3 is therefore proved.

The classical domain identifications in Lemma 4.2 are now proved. Actual
functions on `[0,1]` form complex Banach spaces with their exact physical
component-sum `H¹` norm. Signed extension and physical restriction are continuous
linear inverses, with operator bounds `1` and `√2 π`. Membership agrees with the
original equal/opposite component endpoint conditions, including odd modes.

The physical Hilbert-space operator bridge is now proved. Convolution realizes
actual multiplication of arbitrary `L²` potentials with `H¹` functions, and the
full coefficient and physical eigen-equations agree on `[0,2]`. Nonzero domain
vectors remain nonzero as physical `L²` functions.

Lemma 4.1's classical interval transfer is now proved. Arbitrary original `L²`
potentials have an a.e. reconstructed Dirichlet coefficient extension. Both
signed eigenfunction extensions intertwine the actual differential equation,
and nonzero original eigenfunctions enter the selected boundary and periodic
coefficient spectra with the same eigenvalue.

The converse restriction now identifies the original classical eigenvalue sets
with the coefficient boundary spectra. They are closed, discrete, and finite
in bounded regions; their union equals the periodic coefficient spectrum.
Both free sets are exactly `πℤ`, including odd modes, and a.e. equal potentials
have equal eigenvalue sets.

Original physical potential classes now carry the exact component-sum `L²` norm.
Their Dirichlet coefficient map has norm factor `√2/2` and is bounded, injective,
and analytic. Pullback gives one open convex physical neighborhood and cutoff
for both high-index branches, unique original eigenvalues in the high disks,
and uniform coefficient counting data.

Both signed physical `L²` base-space equivalences are now proved. The Dirichlet
map has closed, dense range and hence is onto; isometric component sign changes
give the Neumann map. Forward synthesis is actual signed reflection, and the
inverse is actual restriction almost everywhere. Both exact norm factors are
proved. The maps commute with classical domain extension and base inclusion.

The original operator/resolvent correspondence is now proved. The physical
classical-domain operator realizes the actual differential expression for any
original representatives. Its partial linear realization is closed and densely
defined on exactly the original endpoint domain. Physical and coefficient
pencils intertwine, their resolvent sets agree, and the physical inverse is
bounded with compact base-space resolvent. Its spectrum is exactly the original
classical eigenvalue set.

Original physical root spaces are now independently defined using the physical
pencil and domain at every chain level. The base/domain isomorphisms identify
each level and the full generalized eigenspaces. Their finite dimensions define
physical algebraic multiplicities and prove agreement with coefficient counts.
The physical central finite set, central multiplicity `2N+1`, unique algebraically
simple high-disk eigenvalues, and exclusion of other spectrum now hold uniformly
on one physical neighborhood for both boundary conditions, with analytic branches.
The free physical multiplicities and the periodic sum formula are also proved.
Both boundary spectral problems use the Dirichlet extension of the potential;
the boundary sign selects the eigenfunction extension and restricted domain. Preserve this distinction in the transfer.
Individual kernel membership alone remains insufficient for uniform boundedness.
Only boundedness is needed from Appendix C.1; its additional isomorphism assertion
is not assumed here.
The actual rectangular contour integral is now constructed as four oriented
operator-norm edge integrals. Its domain-valued factorization proves compactness,
and it commutes with resolvents and algebraic root-space projections. Horizontal
and vertical subdivision cancel shared edges; Cauchy's theorem gives invariance
under edge motion through filled resolvent strips. The central corner rectangle
and boundary agree exactly with the existing box, and one common neighborhood
admits all sufficiently large contours in the domain norm.
Logarithmic edge primitives now compute the exact simple-pole residue `2πi`;
exterior poles and all higher pole terms integrate to zero. Applying these
formulas along finite Jordan chains proves full root-space selection and exact
finite-cluster filtering. In particular the actual central rectangular integral
absorbs the central algebraic projection, and its range contains the central
algebraic range. Mixed-contour Fubini and the resolvent identity now show that
an enclosing circular projection captures all action of the rectangular integral.
Finite-cluster filtering then identifies the whole rectangular operator with the
central algebraic projection. The actual rectangle is idempotent, has exactly
the central full-root-space range, and varies analytically with rank `4N+2` on
one common neighborhood for all larger cutoffs. The unified statement uses Corollary 3.5's height-`N` box;
the printed norm-dependent height is now proved at `p=2`, with uniform
central count `4N+2` and equality of spectral clusters. The explicit sufficient
height `(1+8pM)^p` holds for every finite exponent. Direct substitution of the
printed `(1+8M)^p` into the existing `4p` estimate fails already at `p=3`,
`M=1`; this is a limitation of that argument, not a spectral counterexample.
The actual contour now equals the full enclosed cluster projection for every
ordered admissible rectangle. At the printed Hilbert height and the proved
all-exponent height, its boundary is admissible and the moving integral is
analytic with rank `4N+2`, uniformly on one counting neighborhood; no regularity
of the height function is needed beyond a uniform sufficient bound.
Resolve the general printed bound separately, retaining the distinction from
the proved bound.
The source's finite-exponent coefficient pair norm and weighted pair norm are
now implemented exactly, with energy exponent `sp` and sharp comparison factor
`2^(1/p)`. The proved heights and actual analytic contour neighborhoods transfer
to the component-sum parameter space without increasing the height constants.
Canonical period doubling is now an isometry onto the even coefficient space,
with contractive sampling, exact projection identities, and convolution
compatibility. Splitting the actual physical integrals identifies every
integrable period-one function's period-two coefficients with even insertion,
preserving the coefficient norm. Absolutely summable sequences have an injective
continuous period-one realization. Pair insertion covers all even potentials
and supplies the parity hypotheses for resolvents and contours.
Every Banach `lp` sequence now synthesizes continuously and injectively into
mathlib's genuine tempered distributions. Signed half-integer Fourier samples
of Schwartz tests give an absolutely convergent action, and localized smooth
frequency tests recover every coefficient. Finite Fourier sums converge in the
pointwise tempered-distribution topology, including at infinity. Translation
proves period two and characterizes period one exactly by even support. At
absolute summability the action is integration against the existing continuous
series. Actual distributional differentiation now agrees with `iπn`, and its
graph within the same Fourier class is exactly the scalar one-derivative domain.
The signed-pair free operator has the same exact domain identification. Scalar
and free pair graphs are closed even at infinity; limits only require the two
base coefficient norms. Finite-exponent continuous representatives satisfy
weak integration by parts against Schwartz tests. Multiplication by every Fourier
polynomial is now Mathlib's genuine smooth distribution multiplication; the
coefficient convolution is its unique continuous extension to `ℓ¹` multiplier
data. Arbitrary converging smooth coefficient approximations give the same limit.
The test action is an absolutely convergent sum of actual Fourier integrals of
the continuous multiplier times a Schwartz test. This also proves agreement with
all temperate smooth multipliers and with ordinary function products for `ℓ¹`
potential data. On the finite-exponent one-derivative domain the full signed
operator and its eigenvalue equations agree with these distributional products.
The Schwartz-to-circle bridge is now a continuous periodization map, with an
absolutely convergent physical translate sum and exact period-two Poisson formula.
It preserves the integral; a coefficient test at `n` periodizes to half the wave
at `-n`. Explicit Schwartz lifts cover all Fourier polynomials and prove uniform
density of periodizations. Its kernel is the common annihilator of the realized
Fourier distributions, and translating a test by two preserves periodization.
Periodization now commutes with every classical derivative. Each derivative is
a continuous linear image into continuous circle functions, is uniformly bounded,
and has an absolutely convergent physical translate sum. The same Fourier
truncations converge uniformly in every fixed derivative order, and periodizations
satisfy the genuine temperate-growth condition for smooth Schwartz multipliers.
A finite Leibniz seminorm estimate now proves that uniform convergence of all
multiplier derivatives gives convergence in genuine Schwartz topology after
multiplication by any fixed Schwartz window. Windowed Fourier reconstruction
converges in that topology, and every tempered distribution evaluates it through
an absolutely convergent scalar coefficient series, without a periodicity or
Fourier-class hypothesis on the distribution.
A direct construction now sums any series absolutely summable in all Schwartz
seminorms, with quantitative seminorm tails and actual Schwartz convergence.
Products of two Schwartz tests have inverse-square seminorm decay as one factor
is translated by the period lattice. Their convergent sums identify the two
sides of the periodization/window exchange under arbitrary periodic distributions.
Consequently, actual period-two invariance is equivalent to annihilating the
periodization kernel. Every periodic tempered distribution has an absolutely
convergent Fourier reconstruction from its coefficient-test values, and those
values determine it uniquely. The intrinsic Banach `ℓᵖ` condition is now equivalent
to unique representation by distributional synthesis, including `p=∞`.
The realization now extends to every positive weight with polynomially bounded
reciprocal. This condition is proved for every real Sobolev exponent, including
negative and fractional regularity. Weighted Schwartz sampling is a continuous
linear map into `ℓ¹`; weighting the coefficient sequence cancels the reciprocal
weight in the actual action. Weighted synthesis is continuous and injective,
preserves the raw Fourier coefficients, and is intrinsic across weights and
exponents. Arbitrary finite truncations converge distributionally, including
at infinity. Actual periodicity and weighted `Memℓp` are equivalent to unique
weighted synthesis. The full real Sobolev scale has a direct public API.
Weighted multipliers now have continuous linear maps with the pointwise
weight-comparison constant. Monotone real Sobolev embeddings are contractive,
injective, compose correctly, and preserve the actual distribution.
Differentiation maps regularity `s+1` to `s` with constant `π`, at every real `s`
and Banach exponent including infinity. The actual distributional derivative
has exactly this domain and a closed graph. Intrinsically, simultaneous
regularity `s` of a periodic distribution and its derivative is equivalent to
regularity `s+1` of the distribution. The exponent-changing embeddings are
now implemented below; the full two-input Young inequality is proved subsequently.
The source's distinct infinity pair norm is now implemented as `lp` of
sum-norm pairs, with complete weighted variants and exact supremum formulas.
Its comparison with the maximum product has sharp factor two. The first signed
coefficient is reflected explicitly in the equivalences to the scalar-coordinate
spaces, respecting (1.2). At every real Sobolev regularity, the endpoint pair
space has continuous injective actual distributional synthesis, coefficient
recovery, its exact intrinsic norm formula, and a unique representation theorem
for arbitrary periodic pairs with the stated endpoint regularity.

Increasing the sequence exponent is now a contractive continuous injection,
including the infinity target. Weighted versions preserve raw coefficients,
compose across exponents, and combine with decreasing real Sobolev regularity.
General Hölder triples provide weight-ratio embeddings into smaller exponents,
with the ratio norm as the explicit constant. Finite-exponent Sobolev reciprocal
summability is characterized exactly by the strict threshold `(s-t)r > 1`;
at the infinity multiplier endpoint zero regularity gain is allowed.
All these embeddings preserve the actual periodic distribution, and arbitrary
periodic source inputs have unique target representatives under the Hölder
condition. This supplies the coefficient estimate in Appendix A.9, without
asserting its separate fractional interval-Sobolev identification. That physical
identification remains a subsequent proof target; the full two-input Young
inequality is now proved below.

Appendix B.2 is now proved with its exact exponent relation and constant one
for all Banach exponents, including infinity. A weighted arithmetic-geometric
mean argument bounds finite trilinear convolution pairings. Finite norming
tests turn this into uniform finite Young estimates. Hölder and exponent
inclusion prove pointwise absolute convergence for arbitrary inputs; dominated
convergence of finite cutoffs and the `lp` Fatou property give full membership
and the norm bound. The convolution is a continuous complex bilinear map with
operator norm exactly one, is commutative, and agrees with the old `l1`-factor
construction. Finite input cutoffs converge in output norm, including conjugate
inputs with infinity output.

Appendix A.7 is now proved in the period-two model: every Banach Young triple
gives an actual periodic tempered product with the exact Fourier norm bound.
The construction is intrinsic to the two distributions, independently of their
exponent representations. It agrees with genuine polynomial multiplication
and is the unique joint continuous extension agreeing with polynomial
multipliers in either variable. Every admissible triple has a finite input
exponent; approximation in that factor handles the infinity endpoints without
claiming norm density in `l∞`. Shared Wiener representations recover actual
smooth and ordinary function multiplication.

The displayed mixed three-sequence inequality in Appendix B.3 is now proved
for its positive finite real exponents, including values below one. Powers of
magnitudes divide the sequence exponent with exact norm identities. The source
conditions construct an intermediate exponent satisfying the two scaled Young
relations. Applying the full Young inequality twice gives the exact nested
norm bound with constant one and proves convergence at all three summation
levels. Unit modes attain the bound. The next Fourier-space target is the
physical fractional Sobolev identification in Appendix A.9; the printed
general-`p` central spectral height and the main Birkhoff dependencies also remain.


The physical translation-energy foundation for Appendix A.9 is now in place.
Actual circle `L²` translations are strongly continuous isometries, and Parseval
gives both their exact Fourier increment energy and the factor-two physical
interval normalization. Nonnegative kernel energies admit a genuine physical
double-integral formula and an exact Fourier diagonalization by Tonelli,
including infinite energies. The fractional kernel on `[-1,1]` defines a
physical regularity predicate and has translation-invariant energy, symmetric
frequency weights, and exact single-mode and constant-function identities.
The spectral comparison is now proved below; the interval boundary estimate
below `s=1/2` remains necessary before claiming the physical statement of
Appendix A.9.


The fractional spectral weights now have uniform two-sided bounds by
`|n|^(2s)` for `0<s<1`. Quadratic phase cancellation and bounded phase increments
prove that the unit-frequency model kernel is globally integrable, and its
mass on `[0,1]` is positive. Exact frequency scaling gives the model integral
on `[-n,n]`; its positive core and finite total mass give frequency-independent
constants. The bounds include zero and negative frequencies and lift to the
full physical energy, including infinite values. Physical fractional regularity
is now equivalent to summability of the conventional homogeneous Fourier square
sum. The weighted coefficient identification is now proved below; the
nonperiodic interval boundary estimate for Appendix A.9 remains.


The periodic fractional Sobolev identification is now proved for `0<s<1`.
Homogeneous moment summability together with `L²` is equivalent to the project’s
`(1+|n|)^s` weighted square summability. Contractive Hilbert synthesis and actual
Fourier coefficients give both inverse identities and a unique weighted
representative for every physically regular periodic function. Explicit bounds
compare the weighted norm with the physical fractional energy plus the `L²`
term, which retains the zero mode. The next Appendix A.9 dependency is the
nonperiodic interval boundary estimate below one half, followed by the endpoint
conclusion through lower regularity.


The interval boundary kernel is now evaluated exactly for arbitrary positive
length `L`: its exterior mass at `x∈(0,L)` is
`[x^(-2s)+(L-x)^(-2s)]/(2s)`. The corresponding nonnegative double integral is
the mixed interaction of the actual zero extension and equals the weighted
boundary energy, including infinite values. The intrinsic interval difference
energy has also been defined and respects almost-everywhere equality.
The boundary weight has exact mass `2 L^(1-2s)/(1-2s)` below one half and is
integrable if and only if `s<1/2`. Constant interval data therefore has finite
zero-extension interaction exactly below half regularity; its intrinsic energy
vanishes at every exponent. Bounded interval data has an explicit exterior
energy bound below half. The next dependency is the fractional Hardy estimate
controlling the boundary-weighted square integral by the intrinsic interval
energy plus `L²` for arbitrary data, followed by the extension/periodization
comparison. These results do not yet prove the interval identification in A.9.

Planned Hardy proof: for `0<s<1/2`, average the inequality
`|f(x)|² ≤ (1+ε)|f(y)|²+(1+1/ε)|f(x)-f(y)|²` over `x<y<2x`,
with `δ<x<L/2`. Reversing the triangular integral gives the coefficient
`c_s=(2^(2s)-1)/(2s)=∫₁² t^(2s-1)dt<1` in front of the truncated
left-boundary energy. Choose `ε>0` with `(1+ε)c_s<1` and absorb that term.
The difference term is controlled by the intrinsic interval kernel because
`0<y-x<x`; the remaining half interval is controlled by `L²`. First work
with `δ>0`, where weighted square integrability follows from `L²`, then pass
to the nonnegative integral as `δ` decreases to zero. Reflection supplies the
right endpoint. This avoids assuming the weighted integrability being proved.


The fractional Hardy estimate described above is now proved. The annular mass
produces `c_s=(2^(2s)-1)/(2s)`, and its integral representation proves
`0<c_s<1` for `0<s<1/2`. A measurable triangular kernel gives an exact Tonelli
identity for arbitrary nonnegative data, a uniform truncated averaging bound,
and domination of the difference term by the intrinsic interval energy.
With `ε_s=(1-c_s)/(2c_s)`, the actual square-energy preestimate has coefficient
`a_s=(1+c_s)/2<1`. Every positive cutoff has finite weighted energy from `L²`;
only then is the averaged term absorbed. Increasing cutoff intervals and
nonnegative monotone convergence give the full left endpoint estimate.
Reflection yields both endpoint weights. In particular, arbitrary interval
`L²` data with finite intrinsic fractional energy has finite zero-extension
exterior interaction below one half. Almost-everywhere replacement removes the
global measurability assumption in the finiteness conclusion.
The next A.9 step is the extension/periodization comparison with the already
identified physical periodic space, followed by the Fourier-Lebesgue embedding
and the separate half-regularity consequence through lower regularity.


The zero-extension and forward periodization comparison are now proved.
Full line difference energy equals intrinsic interval energy plus twice the
exterior interaction, including infinite values. This yields the exact
zero-extension regularity equivalence for arbitrary positive interval length
and `0<s<1/2`. A measure-preserving change of variables and Tonelli identify
line difference energy with actual translation-increment energy, also for
arbitrary `L²` representatives.

For period two and displacements at most one, the periodic increment is the
sum of three adjacent zero-extension increments, outside an irrelevant finite
set of endpoint crossings. Its square integral is at most nine times the full
line square increment integral. The normalization of circle `L²` gives a
periodic energy bound by `9/2` times the line translation energy. Actual
interval Fourier reconstruction and almost-everywhere invariance transfer
this bound to arbitrary original interval data. In particular, finite intrinsic
energy and interval `L²` imply `(1+|n|)^s` weighted square summability of the
actual Fourier integrals throughout `0<s<1/2`, with no matching endpoint values.
The next step is to assemble the sharp `q>1/(s+1/2)` Fourier-Lebesgue conclusion
from the existing Hölder coefficient embedding, handle `s=0`, and deduce the
separate `s=1/2` consequence by decreasing regularity.


The period-two A.9 membership conclusions are now assembled. The coefficient
map uses monotone exponent inclusion for `q≥2` and the explicit Hölder exponent
`r=(1/q-1/2)⁻¹` below two. It is an injective continuous linear map and preserves
raw coefficients. Composing with the physical interval bridge gives the
source's strict range `q>1/(s+1/2)` for positive subcritical regularity.
At zero, only `L²` is required, and the equality target two is also available.
Infinity follows from `L²` independently of fractional energy.

An arbitrary-length kernel comparison proves
`E_t(f) ≤ L^(2(s-t)) E_s(f)` for `0≤t≤s`. For each finite `q>1`, choose
`max(0,1/q-1/2)<t<1/2`; lowering the intrinsic half energy before periodization
then proves the separate half-regularity conclusion. No critical
zero-extension or matching-endpoint assumption is introduced.

Next, combine the existing quantitative Hardy, periodization, spectral, and
coefficient bounds into a single bound in an intrinsic interval norm, then
prove the Fourier scaling needed for the arbitrary-period statement. The
current membership theorems use period two; arbitrary-length energy estimates
alone do not establish the source's general-period identification.


The uniform intrinsic bounds above are now proved. The coercive Hardy gap is
inverted explicitly, giving a finite exterior constant for every positive
interval length below half regularity. Almost-everywhere replacement extends
the quantitative bound to arbitrary interval `L²` representatives. The
period-two Parseval identity retains its exact factor `1/2`; combining Hardy,
periodization, and the lower spectral estimate gives a finite weighted Fourier
norm bound in the original full intrinsic energy `N+E_s`.

Composition with the continuous coefficient embedding gives the complete
period-two Fourier-Lebesgue norm bound throughout the positive subcritical
range. The explicit intermediate index
`t(q)=(max(0,1/q-1/2)+1/2)/2` and a quantitative lowering inequality give the
half-regularity bound in the original intrinsic half size. At zero, only `N`
is used, and the constant `sqrt(1/2)` is attained by a constant function even
for the infinity target. These are uniform inequalities on representatives;
the intrinsic normed quotient API is implemented in the later step below.

The next A.9 step is the actual Fourier scaling from period two to arbitrary
positive periods, including the normalization of physical square and
fractional energies. The existing arbitrary-length kernel estimates do not
replace that coefficient identification.


The arbitrary-period scaling step is now proved. Restricted Lebesgue measure
under `x ↦ cx` has inverse Jacobian `c⁻¹`; `MemLp` and nonnegative integrals
transport with that exact factor. Kernel homogeneity and two changes of
variables give the fractional factor `c^(2s-1)`, including infinite energies.
The full intrinsic size has a proved bound accounting separately for its
square-integral and fractional terms.

The actual normalized integral on `[0,L]` with frequency `2πn/L` agrees with
mathlib's interval Fourier coefficient and with the period-two coefficient of
`f((L/2)·)`. Thus A.9's membership and uniform intrinsic bounds now hold on every
positive period, including the zero branch with no fractional hypothesis and
the separate half conclusion. At zero the normalization is `L^(-1/2)`.

The next function-space step is the reverse comparison from physical periodic
fractional energy to intrinsic interval energy, followed by the normed
intrinsic Sobolev function-space identification. The forward comparison alone
already proves A.9's coefficient conclusions; the reverse direction is the
remaining part of the equality of Sobolev spaces invoked in its proof.


The reverse comparison is now proved. Enlarging the intrinsic interval
integral, changing to displacement variables, and applying Tonelli bounds it
by twice the full translation energy. The exact tail mass is `1/s`, and the
uniform `L²` increment estimate gives
`E_interval ≤ 2(E_periodic+(4/s)‖f‖²)` for every positive index, including
infinite energies. Below half this combines with forward periodization to
identify the physical periodic and intrinsic interval regularity conditions.

Actual Fourier reconstruction and bidirectional dilation finiteness give the
weighted square-summability criterion on every positive interval length,
together with a unique weighted representative. The reverse spectral bound
retains the zero mode: `I_s ≤ R_s ‖a‖²` with
`R_s=2+2(C_upper(s)+4/s)` for `0<s<1`. Below half, the forward and reverse
bounds give explicit norm equivalence for arbitrary period-two interval data.

The intrinsic normed quotient and continuous Fourier embedding are now
implemented in the following step.


The intrinsic function-space step is now proved on every positive interval.
A normalized circle `L²` class represents arbitrary interval data by the
coordinate change `x ↦ 2x/L`, with exact square-energy factor `L`. Reconstruction
is almost everywhere, and equality of constructed classes is exactly interval
almost-everywhere equality. Thus the representation imposes no endpoint condition.

The physical difference quotient `(f(x)-f(y))/|x-y|^(1/2+s)` is square integrable
precisely when the intrinsic fractional energy is finite. Its class and the
scaled original `L²` class form an injective linear graph in a product of `L²`
spaces. The induced norm has square exactly `N+E_s`; its equality with the
previously defined intrinsic size is proved. Both graph components are
continuous, with the normalized `L²` inclusion factor `1/sqrt(L)`.

The existing A.9 bounds now give continuous complex-linear Fourier injections
from this actual normed space, preserving the original normalized Fourier
integrals. The positive subcritical source range and the separate half case
are both covered, including nonperiodic ramps. At zero regularity, the earlier
ordinary `L²` API still applies; the fractional graph at zero is not identified
with the ordinary `L²` norm.

The completeness and continuous weighted Fourier equivalence steps are now
proved below, with quantitative bounds on arbitrary interval lengths.


The intrinsic space is now a complete complex Hilbert space. Convergence in
`L²` gives an almost-everywhere convergent subsequence of the original circle
classes. Pulling its convergence back to the physical interval and taking a
further subsequence for the difference quotients identifies the graph limit
pointwise almost everywhere on the interval square. This proves closedness
of the actual physical graph, with no restriction on its real index and no
endpoint assumptions. Completeness follows from its isometric inclusion into
the product of complete `L²` spaces, including at the critical half index.

The induced complex inner product is
`L * inner(f,g) + inner(Q_s f,Q_s g)` in normalized circle coordinates, with
the usual conjugate-linearity in the first argument. Convergence in the
intrinsic norm is equivalent to simultaneous convergence of the two graph
components. Norm-summable series of nonperiodic half-regularity ramps now
exist in the intrinsic space, and both difference-quotient and Fourier maps
commute with these sums.

The continuous weighted Fourier equivalence and its approximation consequences
are now proved in the next step.


The subcritical identification is now a genuine continuous linear equivalence
between the intrinsic Hilbert quotient and the normalized-frequency weighted
coefficient space `(1+|n|)^s ℓ²`. Analysis is given by the actual normalized
physical Fourier integrals; synthesis is the existing `L²` Fourier inverse.
Both inverse identities are proved. For physical interval length `L`, the
analysis bound is `sqrt(C_Sob(s)) sqrt(D_s(L/2))`, while the synthesis bound is
`sqrt(D_s(2/L)) sqrt(R_s)`, with `D_s(c)=c⁻¹+c^(2s-1)`. The dependence on interval
length is retained in both directions. Synthesis and its norm bound hold for
all `0<s<1`; the two-sided equivalence requires `0<s<1/2`.

The A.9 intrinsic Fourier map factors through this exact equivalence and the
proved weighted Hilbert coefficient inclusion. Finite Fourier truncations
retain precisely the selected actual coefficients, have a uniform bound
independent of their finite support, and converge in the full intrinsic norm
below half regularity. Hence classes with finite Fourier support are dense,
including when the original interval input has unequal endpoint values.

The next Section 6 weight and shifted-norm step is now implemented below.
The resonant splitting and complementary free inverse feed Lemma 6.4 and the
eigenvalue and weighted-gap asymptotics of Propositions 6.1 and 6.3. The printed
general-`p` central-height constant in Proposition 3.1 remains independent.


The displayed Section 6 weight class is now formalized with lower bound one,
symmetry, submultiplicativity, and monotonicity on the nonnegative integers.
The normalization does not impose `w(0)=1`; constant weights greater than one
are included. Scaled Sobolev weights `(1+c|n|)^s` with `c,s≥0` include both the
existing normalized-frequency weights and the source's exact `π` scale. Every
source weight has tempered reciprocal and a contractive inclusion into the
unweighted coefficient space.

Translated weights `w(n+i)` define the same coefficient space, with continuous
identity maps and comparison factor `w(i)` in both directions. Reindexing gives
an isometric map from the shifted-weight class to the original weight, and the
resulting modulation has raw coefficients `a(n-i)`. Its norm is exactly the
source's shifted scalar norm. The modulation also agrees with Mathlib's actual
multiplication of the synthesized tempered distribution by `exp(iπix)`.
The scalar results include the infinity exponent.

For finite Banach exponents, the pair norm modulates the first physical
component by `-i` and the second by `i`. The exact energy is
`Σ_n w(n+i)^p (|f_minus(-n)|^p+|f_plus(n)|^p)`, as in Section 6's signed mode
coordinates. Both comparisons again have factor `w(i)`, with no additional
pair-norm constant. Unit weights give isometric pair shifts.

The resonant projections and complementary free inverse are now implemented.
The projections select physical frequencies `-n` and `n`, sum to the identity,
and are idempotent and mutually annihilating. The complement is characterized
by vanishing of those two coordinates.

All nonresonant denominators dominate `|m-n|≥1` throughout the closed strip,
including its center. The zeroed reciprocal defines a continuous linear inverse
into the domain with weight `w(k)(1+|k|)`. Both compositions with the free pencil
give the appropriate complementary projection, and the complementary solution
is unique. The domain map has bound `1+(1+|λ|)/π`. Forgetting the source weight
identifies the pencil with the original free differential operator on its
existing domain. The base inverse and both projections contract every signed
shifted finite-exponent pair norm with constant one.

Lemma 6.4 is now proved. Weighted convolution is a continuous bilinear map
with Young constant one, constructed by a norm-summable series and identified
with the existing raw-coefficient product. The punctured reciprocal lattice
belongs to the conjugate space for every finite Banach input exponent,
including `p=1`. Its Hilbert norm is at most two. The chosen exponent-only
constant `c_p=max(‖puncturedLattice‖_{p′},2)` therefore has `c₂=2`.

The complementary inverse gains weighted `ℓ¹` regularity uniformly in the
strip and in every scalar shifted norm. Composing it with the off-diagonal
weighted product gives the actual `T_n`, with the source's sign-reversing bound
`‖T_n f‖_{w,p;i}≤c_p‖φ‖_{w,p}‖f‖_{w,p;-i}`. The original potential/domain
identification is proved. Squaring restores the shift with bound `(c_p‖φ‖)²`.

Lemma 6.5 is now proved. Weighted scalar and pair tails retain `|k|=|n|`
and converge in norm for every finite exponent. The two closed half-radius
windows isolate the potential remainder. Monotonicity and symmetry give the
near-near comparison `w(j-n)w(n)≤w(j-k)w(k-n)`, which positive coefficient
majorants transfer to a full shifted norm bound with the factor `1/w(n)`.
The two far terms use uniform reciprocal-tail decay, including the `p=1`
conjugate-infinity endpoint and the central lattice parameter.

The actual square factors through the two scalar double-complementary
inverses. The resulting estimate in shift `n`, and equivalently in the induced
operator norm, is
`C_p‖φ‖(‖φ‖/(1+|n|)^(1/p)+‖R_n φ‖/w(n))`, with
`C_p=64p c_p+c_p²`. It is valid for every integer center, including zero,
and all parameters of the full closed strip. The exact finite-`p` pair norm
and the inverse-weight improvement are retained.

The locally uniform threshold after Lemma 6.5 is now proved. Forgetting the
weight preserves both physical Fourier components and commutes with `T_n`.
The exact unit-weight pair norm is invariant under signed shifts. A common
bound in the weighted full norm and weighted tail therefore controls both
operator squares. For every positive tolerance, one open convex neighborhood
containing the potential and zero has a common cutoff `N≥1` valid on every
full closed strip with `|n|≥N`. Taking tolerance `1/2` gives the source's
simultaneous unweighted and weighted shifted contraction.

The squared Neumann inverse and the Q-equation are now proved. Conjugating
by the signed shift gives a small square; the geometric series is then
transported continuously back to the original operator algebra. It gives
both inverses of `Id-T_n²` and the factorization
`T̂_n=(Id+T_n)(Id-T_n²)⁻¹`, with both inverse identities for `Id-T_n`.
The inverse commutes with `T_n` and agrees with the unweighted inverse on
common inputs.

The actual potential is implemented continuously from the weighted derivative
domain to the base via the one-derivative weighted Hölder embedding and
convolution. Its coefficients identify it with the original potential and
its composition with the complementary inverse is exactly `T_n`. The
reconstructed `v=A_λ⁻¹ Q_n T̂_n Φu` lies in the complementary derivative
domain, satisfies the Q-equation and `Φv=T̂_n T_n Φu`, and is unique.
Existence and uniqueness hold uniformly over the previously constructed
open convex neighborhood and every sufficiently distant full closed strip.

Lemma 6.6 is now proved. Continuous extraction and synthesis identify the
two physical resonant modes with `Fin 2 → ℂ`, including an explicit lift
into the derivative domain. The free pencil acts there by `λ-nπ`. The map
`S_n=(λ-nπ)Id - coordinates ∘ T̂_n Φ ∘ synthesis` has an explicit `2×2`
matrix in this basis. Reconstruction preserves the resonant amplitudes and
its full differential residual is the synthesis of `S_n c`. Conversely,
every domain eigenvector is reconstructed from its two coefficients.

The unit-weight base and derivative-domain equivalences preserve original
Fourier coefficients and identify the full weighted equation with the
existing periodic operator. Thus the determinant criterion concerns the
original periodic spectrum, with nonzero eigenvectors preserved in both
directions. One open convex neighborhood and one cutoff `N≥1` make the
criterion valid on every full closed strip with `|n|≥N`.

Lemma 6.7(i), on source pages 40–41, is now proved for arbitrary complex
potentials and every finite Banach exponent. Reflected bilinear convolution
testing gives a Green identity for the actual free pencil and potential.
Applied to the reconstructed vectors, the exact residual identity forces
equality of both resonant diagonals. The common coefficient `a_n`, both
`b_n` coefficients, and the displayed common-diagonal matrix are implemented.

The printed unconditional reality clause in Lemma 6.7(ii) is false for
general complex potentials. Constant components `(a,b)` have the actual
correction `ab/(λ+nπ)` for `n≠0`. Choosing `(1,i)` gives `i/(2πn)` at a
positive central resonance. The formal counterexample meets the source's
half-size contraction at arbitrarily large indices. The source proof assumes
`φ*=±φ` for both conjugation identities; the corrected statement now
retains that condition.

The conditional identities in Lemma 6.7(ii) are now proved. Physical conjugation
is a norm-preserving involution on every symmetric weighted coefficient space,
including infinity. The potential star exchanges these conjugate-reflected
components; both Fourier coefficient identities characterize `φ*=εφ`.
For `ε²=1`, signed conjugation commutes with the actual domain potential and
intertwines the complementary inverse at `λ` with that at `conj λ`.

Uniqueness of the actual Neumann inverse proves the corresponding correction
identity. Its resonant action gives `a_n(conj λ)=conj(a_n(λ))` and both signed
off-diagonal exchange formulas. On the real spectral axis, the diagonal has
zero imaginary part for either reality type. A common open convex neighborhood
and frequency cutoff provide both inverse hypotheses throughout the full
closed strips. The argument covers every finite Banach exponent.

The source's basis order is now explicit. Physical coordinates use
`(e_n⁻,e_n⁺)`, and the displayed matrix uses the reverse order. The `b_n⁺`
and `b_n⁻` names have been corrected to follow the source definitions. An
explicit simultaneous reversal of both matrix indices gives the printed
form, preserves the determinant, and retains the eigenvalue criterion.
The actual potential-source vectors have exactly the component shifts
`φ_+(k+n)` and `φ_-(k-n)`. Thus the leading signed coefficients are the raw
second coefficient at `2n` and the raw first coefficient at `-2n`.

Equations (1.14)–(1.15) are now proved. The operator exchanges physical
components, its square preserves them, and continuous testing of its
convergent even Neumann series preserves those closed component subspaces.
The common diagonal is the odd correction. The off-diagonals are the even
corrections, with their actual Fourier leading terms removed by `T_n²`.
Individual unwanted terms vanish, and the remaining odd/positive-even
scalar series converge to the precise source coefficients and remainders.

The uniform shifted bound on `(Id-T_n²)⁻¹ Φe_n±` is now proved with the
source constant two and the exact opposite component norm. It also controls
the unweighted finite-exponent pair norm. The exact finite-series remainder
gives the geometric error `2·2⁻ᵐ`, uniformly on one open convex potential
neighborhood and every sufficiently distant full closed strip. One truncation
length works for both vectors and every parameter in that set.

The analytic assertion of Lemma 6.8 is now proved. Resolvent identities
normalize the complementary inverse at the strip center. Its domain-valued
extension is analytic and equals the actual inverse, including at central
lattice points and closed strip edges. Weighted convolution makes the actual
domain potential continuous linear in the potential; composition proves
joint analyticity of `T_n`.

Banach-algebra inversion and the squared factorization give analytic even
and full corrections on a proved open joint domain. Inverse uniqueness
identifies them with the existing Neumann constructions. Continuous resonant
extraction gives all three source coefficients with the correct basis labels.
One open convex potential neighborhood and one cutoff give joint analyticity
on every distant closed strip, explicitly accompanied by the small-square
witness and equality to the actual coefficients. All finite Banach exponents,
including `p=1`, are covered; the free complementary extension also covers
infinity in the existing `WithLp ∞` maximum pair norm.

The diagonal Hölder estimate on source pages 41–42 is now proved. The even
inverse and its source vectors commute with forgetting the weight. The unit
square has exactly the same norm in shifted and unshifted coordinates, so
the simultaneous contraction gives a vector bound with the unweighted
potential norm retained. The actual diagonal Fourier series is absolutely
convergent and is bounded by that vector norm times a reciprocal row norm.
For finite conjugate exponent this row norm equals the source's displayed
sum after the signed reindexing. The `p=1` endpoint uses the conjugate
infinity norm. The actual full-strip supremum is defined, bounded by this
same expression, and dominates all original coefficient values, uniformly
on one potential neighborhood and every distant closed strip.

Lemma 6.8(i) is now proved. Powered Young with inner exponent `min(p,p')`
constructs an outer `ℓ^p` sequence of reciprocal row norms. Contractive
exponent inclusion treats both sides of two. At the sampled frequency `2n`,
the exact support split at `N` separates a reciprocal tail from a potential
tail; this even improves the intermediate potential cutoff from `N/2` to `N`.
Appendix B.1 bounds the reciprocal tail, and the inner conjugate identity
produces the exact power `min(1,p-1)` after raising to `p`.

The actual full-strip supremum tail is an `ℓ^p` sequence. Its power series
converges and obeys the printed bound with the unweighted source pair norm
and `N/2` tail, with explicit constant `(8 max(p,p'))^p 2^(p-1)`.
All cutoffs beyond one threshold work uniformly on an open convex potential
neighborhood containing the given potential and zero. The source range
`1<p<∞` is retained for this summability result.

The reciprocal region estimates following (1.16) are now proved for every
finite `p>1`. Iterating powered Young constructs the exact nested row norm
sequence at `2n`. Its double power sum is jointly summable, and exchanging
the kernel indices preserves the norm. The exact support split puts the two
kernel tails at `N/2` and the near-near potential tail at `N`.

The two far regions have equal norms. Each has outer power sum at most
`C_p ‖a‖_p^p/M^min(1,p-1)` for reciprocal cutoff `M>0`, and the near majorant
has sum at most `C_p ‖R_N a‖_p^p`, where
`C_p=(16 max(p,p')²)^p`. These are actual convergent sums at the source inner
exponent `p'`, controlled through `min(p,p')`. The signed physical sum formula
is proved, including vanishing resonant-denominator terms.

The actual off-diagonal double Fourier series and their weighted Hölder
bounds are now proved. The first physical coefficient is reflected where
required by the source basis; both coefficient labels retain their correct
leading Fourier modes. Spectral-weight reflection is an exact isometry and
reverses the scalar shift. Two successive Hölder tests give joint absolute
convergence and the full-index form of (1.16), with the exact shifted vector
norm and double reciprocal row retained.

The half-contraction vector bound yields
`w(2n)|b_n^- - φ_-(-2n)| ≤ 2‖φ_-‖² ‖doubleRow(weight φ_+)‖`
and the corresponding positive bound with the components exchanged and the
first potential reflected. One open convex neighborhood and one cutoff give
both bounds for the actual coefficients and analytic extensions throughout
all distant closed strips, including `p=1` with conjugate infinity.

The proof-consistent weighted inequality in Lemma 6.8(ii) is now proved for
all finite `p>1`. A disjoint split avoids counting the far-far corner twice.
The near region retains both potential tails at `N`; regional power sums
then give an explicit exponent-only constant. Reflection preserves weighted
tails, and integer-half-cutoff decay loses at most three.

Both actual weighted full-strip remainder suprema have convergent power
tails with bound
`C_p ‖φ_±‖^p (‖φ‖^(2p)/N^min(1,p-1) + ‖R_(N/2)φ‖^(2p))`,
where `C_p=3·4^p·2^(p-1)·(16 max(p,p')²)^p`. One open convex potential
neighborhood and one threshold work for both signs and every larger cutoff.
This uses the `p`-power sum and full pair norm in the proof on source page 43.
The printed page-41 statement omits those left-hand powers and writes the
positive component in the first numerator; its literal form is not asserted.
See STATUS.md for the precise source-display qualification.

Lemma 6.9's uniform smallness, localization, and root-gap estimates are now
proved. Norm-and-tail neighborhoods make the actual suprema arbitrarily
small. The signed weighted leading coefficients also decay locally uniformly,
giving the source numerical bounds on all full coefficients. The scalar
analytic determinant equals the actual reduced determinant and has the
original periodic spectral zero criterion; at zero potential it is exactly
the centered square.

Any zero in a distant strip lies within `3π/32` of its center. On the circle
of radius `π/4`, the determinant perturbation is strictly smaller than the
centered square. Analyticity and matrix agreement share the same cutoff and
potential neighborhood. Cauchy's estimate gives the derivative bound `1/8`,
and the actual full-strip product supremum controls any pair of zeros by
`|ξ-η|²≤6|b_n⁺b_n⁻|_{U_n}`, without choosing square-root branches.

The scalar analytic zero count is now proved independently of the existing
spectral algebraic count. Local analytic factorization identifies each pole
of `f'/f` with its analytic zero order. Finite pole removal and Cauchy's
integral theorem give the disc argument principle. The principal logarithm
of a strict boundary ratio gives Rouché's theorem. Applied to the actual
determinant and its centered square, it gives count two on the closed disc,
open refined disc, and whole strip. A multiset representation yields two
roots allowing coincidence, exhausts all strip zeros, and records their
exact analytic orders. Their localization and factor-six gap estimate hold
on one open convex potential neighborhood with one signed-frequency cutoff.

The source displacement display has now been audited against the actual
operator. `SingleResonantPotential` places amplitudes at `-2n` and `2n`; the
complementary source vanishes and the actual determinant is `(z-nπ)²-ba`.
`RootDisplacementSourceAudit` uses equal real amplitudes to refute the printed
budget locally uniformly at zero, including on the valid small-square domain.
`RootDisplacementPower` proves a branch-free per-root power estimate and
separates both leading Fourier modes from their actual remainders.

The corrected displacement power sum is now proved. Injective frequency
sampling controls the two weighted leading coefficients by the pair Fourier
tail, retaining its cutoff boundary. The actual diagonal and remainder
suprema give one summable majorant for both roots. For `B=‖φ‖_(w,p)`,
`T=‖R_(N/2)φ‖_(w,p)`, and `δ=min(1,p-1)`, its sum is at most
`C_p [T^p + (B^p/N^δ+T^p)(1+B^p)B^p]`, with an explicit exponent-only
constant. Root selection preserves the scalar analytic multiplicities,
localization, and factor-six gap bound on the same open convex neighborhood
and signed-frequency cutoff; every larger displacement tail converges and
obeys this estimate. This is the corrected quantitative form of Lemma 6.9,
not the disproved printed display.

The weighted gap power tail is now proved for the same root sequences. For
`B=‖φ‖_(w,p)`, `T=‖R_(N/2)φ‖_(w,p)`, and `δ=min(1,p-1)`, its sum is bounded by
`G_p [T^p + E_p B^p (B^(2p)/N^δ + T^(2p))]`, where
`G_p=2^p (2^(p-1))²` and `E_p` is the existing off-diagonal summation constant.
The proof transfers weights to the full-strip product supremum, applies a
valid power-mean bound for every finite exponent, and sums the leading and
remainder majorants. No diagonal term is needed. The same open convex
neighborhood, signed cutoff, root localization, and exact analytic orders
support both displacement and weighted gap tails for every larger cutoff.

The bridge to the original periodic spectrum is now proved. Forgetting the
spectral weight commutes with the complementary inverse, so the weighted and
unit-weight determinants agree on their common contraction domain. The
uniform square estimate provides both domains together. On a distant disc,
the spectral count two and positivity identify each algebraic multiplicity
with the occurrence count in the scalar pair, hence with its analytic order.
The contour midpoint and squared gap coincide with the same pair's formulas.

`PeriodicResonantPair` records these original spectral identifications and
localization bounds. Any two such pairs agree up to exchange, and arbitrary
modewise label choices give exactly the same displacement and gap tails.
`exists_uniform_periodicRoots_with_power_sums` retains both quantitative sums
on the same neighborhood. `exists_uniform_periodicGapSummability` expresses
the weighted bound directly using the intrinsic contour-defined squared gap,
via `|γ²|^(p/2)=|γ|^p`. These are corrected original spectral versions of
Propositions 6.1 and 6.3, with the additive leading Fourier-tail terms retained.

The midpoint sequence consequence and ordinary boundary asymptotics are now
proved. `SpectralDisplacementTail` turns a convergent signed tail into global
`Memℓp` membership by adding only finitely many omitted modes. Convexity gives
the original contour midpoint exactly half the two-root displacement budget.
For reflected potentials, each ordinary Dirichlet or Neumann eigenvalue is a
periodic root in the same disc, so the existing displacement sum bounds both
branches on one common neighborhood and cutoff.

The completed interval extension pulls this estimate back to the source
period-one `CoeffPair p` for all finite `p>1`; both boundary displacement
sequences belong to `ℓp` and retain every larger quantitative tail. The physical
interval extension also gives the actual original `L²` boundary eigenvalues
square-summable displacements, together with their unique high-disc spectral
characterization on the same neighborhood.

The auxiliary coefficient realization is now proved. `AuxiliaryPhase`
constructs `G(f₋,f₊)=(f₋,if₊)` as a linear isometry in both base and domain
norms, and verifies the exact operator and pencil conjugation with potential
`(iφ₋,-iφ₊)`. Neumann-reflected potentials become Dirichlet-reflected ones.
The phase images give the auxiliary closed complementary spaces, their raw
`±i` reflection conditions, and the same decomposition at all real Sobolev
regularities. Domain inclusion preserves the auxiliary boundary condition.

`AuxiliarySpectrum` defines the actual restricted auxiliary operator and
pencil; its resolvent set is actual bijectivity. Restricted-pencil conjugation
then proves equality with the ordinary spectrum at the transformed potential.
The spectra are closed, discrete, finite in bounded sets, and every spectral
point has a nonzero eigenvector in the actual auxiliary domain.

The source Neumann potential extension feeds both auxiliary branches.
`exists_uniform_auxiliaryPeriodOneAsymptotics` supplies both starred source
coefficient branches with global `ℓp` displacement membership, unique actual
high-disc spectral identification, and every larger corrected power tail on
one open convex potential neighborhood. Together with the ordinary branches,
this proves all four coefficient displacement conclusions in Corollary 6.2.
The budgets use the actual reflected/conjugated potential tails.

The actual auxiliary root-chain recursion is now identified level by level
with ordinary boundary chains. Its full root space is finite dimensional and
stabilizes, and its dimension equals the conjugate ordinary multiplicity.
`AuxiliaryCountingData` records actual spectral localization, central algebraic
count `2N+1`, and simple high-disc eigenvalues for both auxiliary restrictions.
These hold on one open convex neighborhood containing the given potential and
zero, for every larger cutoff, including after source period-one extension.

The original auxiliary H¹ endpoint conditions in (1.10) are now defined
independently of Fourier coefficients. Physical phase conjugation identifies
them with the ordinary endpoint conditions and intertwines the actual
differential expression. The source phased extension reconstructs the original
function on the closed interval and gives a unique auxiliary weighted-domain
representative. Actual Fourier integrals define the Neumann potential extension;
its conjugation identity proves equality of original auxiliary eigenvalue sets
with the actual coefficient spectra. Both directions of the physical/coefficient
eigenvalue equation transfer are proved, completing this physical form of
Lemma 5.1.

The auxiliary physical domain now stores actual closed-interval functions and
has exactly the original component-sum H¹ norm. Phase rotation is an isometry
from the ordinary domain, proving completeness. Actual Fourier extension and
restriction are continuous linear inverses with bounds `1` and `√2 π`.
Physical L² phase isometries transport inclusion and the differential operator;
representative theorems prove their actual physical action. The independently
defined physical pencil is invertible exactly at the conjugate ordinary
resolvent parameters. Its bounded inverse satisfies both original-space inverse
identities, and its base-space resolvent is compact. The resulting unbounded
operator has precisely the original auxiliary endpoint domain, is densely
defined and closed, and has spectrum equal to the original auxiliary eigenvalue
set and the actual coefficient auxiliary spectrum.

Actual physical auxiliary generalized root spaces now use the original
pencil and H¹ domain at every chain step. Phase conjugation identifies every
level and full root space, proving stabilization and finite dimension.
Algebraic multiplicity is the actual physical full-root-space dimension and
agrees with the auxiliary coefficient multiplicity at the Neumann extension.
Physical clusters give central count `2N+1` and simple high-disc eigenvalues.
One common open convex L² neighborhood supports both counting data and analytic
high-index branches, together with full square-summable displacements and
all larger quantitative tails. This completes the physical starred part of
Corollary 6.2.

The completed half-interval map now preserves conjugation with index reversal
at every `1<p<∞`, including its odd Hilbert tail. Hence both signed source
extensions preserve real type, in particular the Neumann potential extension
used by both auxiliary problems. Proposition 5.2(iv) now holds for source
period-one coefficient potentials. Actual Fourier-integral compatibility also
proves it for arbitrary real-type original physical L² potentials, with the
real-type hypothesis imposed only a.e. and invariant under representatives.
Both actual auxiliary resolvent sets contain every nonreal parameter.

Both bounded period-one auxiliary eigenfunction extensions are now constructed
in the source's actual component-sum pair norms. Their finite Fourier formulas
are the actual integrals of the phased reflection, and density proves uniqueness
of the completed map. Compatible finite H¹ inputs agree with the original
Sobolev extension. The maps have an explicit common bound at every `1<p<∞`,
are analytic into the closed source-norm auxiliary targets, and preserve the
source norm exactly at `p=2`. The constant input `(0,1)` also proves that the
strict lower exponent restriction cannot be dropped.

The free spectral products now have an explicit symmetric cutoff and a proof
that pairing positive and negative indices equals the original integer cutoff,
including zero factors. Euler's product proves convergence at every complex
parameter. The full product gives `(2 cos λ)^2-4` with prefactor `-4`; the even
subproduct gives `2 cos λ-2` with prefactor `-1`. The formal source audit above
refutes the printed prefactors in Lemma 8.1(ii) and determines their necessary
replacements from free values.

The full perturbed periodic product now converges pointwise off `πℤ`.
The free resolvent and Sobolev embedding make relative displacements absolutely
summable at every finite Banach exponent. The actual finite central polynomial
retains original algebraic multiplicities; distant counted pairs supply the
tail. The resulting product has exactly the actual periodic spectral zeros
off the lattice and is unchanged by modewise label exchanges. For large finite
cutoffs, all artificial central free factors cancel and only constant
normalizations remain. One open convex neighborhood and threshold support
this construction for every larger central cutoff and every finite `p>1`
potential, using the already proved displacement and counting results.

The products now converge locally uniformly in the spectral parameter off
`πℤ`. Half-gap balls give summable uniform relative majorants, while compact
quadratic majorants upgrade the free Euler products on the whole plane.
The actual normalized polynomial cutoffs converge to a holomorphic limit off
the lattice, and their derivatives also converge locally uniformly there.
This stage concerns fixed potentials; uniform convergence in the potential
is established in the later stages below.

The actual products now extend to entire functions, with polynomial and
derivative convergence locally uniform on the whole plane. The maximum
modulus principle transfers uniform Cauchy estimates from circles avoiding
the countable lattice to their discs. Continuity uniquely fixes the filled
values. Reciprocal maximum-modulus bounds prevent extra zeros at lattice
points, while every actual spectral value makes all sufficiently large
cutoffs vanish. Thus the entire zero set is precisely the original periodic
spectrum, and pair-label independence holds globally.

The entire product now has the exact original spectral algebraic multiplicity
as its analytic order at every complex parameter. Finite spectral polynomials
have the prescribed central exponents and counted pair orders. Disjointness
identifies the unique contributing factor, and Rouché stability on isolating
discs passes these orders to the limit. Infinite analytic order is excluded
explicitly, including at filled free lattice points.

The central-cutoff choice is now eliminated. Enlarging the central cluster
absorbs exactly the intervening disjoint spectral pairs, preserving their
original multiplicities and the constant normalization. All sufficiently large
finite polynomial cutoffs agree exactly, including at spectral zeros. Uniqueness
of limits gives equality of the entire functions for arbitrary admissible
cutoffs and pair labels. Every finite `p>1` potential has one such function for
all larger cutoffs, retaining exact orders and polynomial/derivative convergence.

The finite polynomial part of potential analyticity is now proved. Generalized
root chains of the contour reduction agree with the original domain recursion,
so the determinant has exactly the original spectral multiplicities. Local
projection transport and the finite determinant formula give joint analyticity
of all sufficiently large central polynomials on one potential neighborhood.
Their normalized limits define the canonical full periodic product directly
from the potential, with the exact original zeros, orders, and locally uniform
spectral-parameter and derivative convergence.

The relative-product tails are now controlled uniformly over actual potential
neighborhoods. Finite products satisfy exponential perturbation bounds even
when factors vanish. A fixed finite conjugate-exponent multiplier has uniformly
small absolute tails on bounded `ℓp` families, although those families may have
no uniform coordinatewise tails. Reciprocal free denominators give these
multipliers on closed half-gap balls. The corrected root displacement budget
supplies one common displacement norm bound on an open convex potential
neighborhood, proving uniform paired relative-product convergence there without
continuity of root labels.

The central and free factors are now restored. Central root localization and
the exact total multiplicity give a uniform bound for the central correction.
Finite spectral covers preserve the unrestricted potential factor, and maximum
modulus fills the free lattice uniformly over it. One open convex potential
neighborhood works for every compact spectral set. The intrinsic approximants
therefore converge locally uniformly jointly in both variables, and their
eventual joint analyticity proves joint continuity of the canonical product.

The Banach-space derivative limit argument is now proved. Schwarz estimates
turn uniform function differences on a larger ball into operator-norm bounds
for Fréchet derivative differences on a smaller ball. Local uniform analytic
approximation is preserved by differentiation, giving continuous complex
Fréchet derivatives of every finite order. Applied to the canonical product,
this proves joint complex smoothness, locally uniform operator-norm convergence
of the polynomial derivatives, and entire restrictions to every complex affine
line. The hypotheses use actual joint balls, not a compactness assumption on
the infinite-dimensional potential domain.

Joint Banach-space analyticity is now proved. Schwarz estimates on equally
spaced nested balls give geometric bounds for the factorial-normalized Fréchet
Taylor coefficients and a positive operator-norm convergence radius. Along
every complex affine line, the same coefficients are the ordinary Taylor
coefficients of an entire scalar function. Cauchy's theorem identifies the
sum with the canonical product, yielding its actual joint Fréchet power
series. Potential and weighted pullbacks and all mixed iterated derivatives
are analytic as well.

The odd free-product identity and complete-sequence perturbed parity products
are now proved. Affine reindexing preserves finite-exponent ℓp displacements.
Exact finite cutoff identities keep the zero-mode denominator and the literal
asymmetric odd interval. The resulting even and odd limits are entire, with
locally uniform polynomial and derivative convergence, including at p=1 and
free lattice points. Their free specializations recover Δ−2 and Δ+2 with
prefactors −1 and 4.

Actual central parity root multisets and polynomials are now constructed.
Parity root-space dimensions count the original Jordan chains and sum to the
full algebraic multiplicity. Projection commutation distributes parity over
finite spectral clusters, turning central rank counts into exact multiplicity
sums. The two central polynomials multiply to the full original polynomial,
with the precise parity zero sets and analytic orders. Root multisets retain
shared eigenvalues and have the exact uniform central cardinalities.

The actual central roots are now assigned two slots per parity index and
spliced into the distant counted pairs. Finite replacement preserves ℓp
displacements. The completed sequences enumerate exactly the original parity
eigenvalues, including the weighted-domain eigenvector characterization.
Their entire parity products have exactly these whole-plane zero sets:
spectral isolation and reciprocal maximum-modulus bounds prevent extra zeros
when filling the free lattice. Both the literal cutoffs and their derivatives
converge locally uniformly in the spectral parameter. Actual data supply this
construction on common neighborhoods and central thresholds for finite p>1.

Label and cutoff independence of the actual parity products is now proved.
Larger central polynomials absorb the counted pairs in their parity. Even
literal cutoffs are intrinsically normalized central polynomials at `2M`;
odd cutoffs retain one additional counted boundary factor at `2M+1`. All
sufficiently large finite cutoffs agree exactly for arbitrary admissible
central cutoffs and root labels, including at spectral zeros. Uniqueness of
limits gives one pair of entire functions independent of these choices.

Exact analytic orders of both actual parity products are now proved. Every
fixed point eventually lies inside the central box, where the intrinsic parity
polynomial has the original order and the odd boundary factor has order zero.
Spectral isolation and Rouché stability pass these orders to the entire limits.
The orders of their product add to the full original spectral multiplicity.
The neighborhood existence theorem retains these orders and choice independence.

The actual parity products now multiply exactly to the canonical full product.
The literal finite identity retains the positive odd boundary factor; bounded
spectral displacements make this factor tend to one. Completed central labels
also identify every sufficiently large full cutoff with the intrinsic normalized
central polynomial. Thus the limit fixes the entire normalization, and its
spectral derivative satisfies the product rule. Actual potential neighborhoods
admit choice-independent entire factors with exact orders and this identity.

Joint analyticity of the finite central parity polynomials is now proved on
the actual even-supported potential subspace. The parity contour projection
has precisely the full contour range intersected with the parity subspace.
Its analytic transport gives a fixed finite-dimensional operator whose root
chains and characteristic-root multiplicities equal the original parity root
spaces. Its determinant is therefore the actual central parity polynomial.
All sufficiently large normalized parity approximants are jointly analytic on
one common neighborhood, with the corrected prefactors and odd endpoint intact.

Joint uniform convergence of the parity approximants is now proved. Complete
paired products converge uniformly over every norm-bounded displacement family
on each spectral compact set; affine parity sampling preserves a common norm
bound. The fixed central box bounds all central root labels, so actual completed
pairs have one displacement bound over an open convex potential neighborhood.
Both literal parity cutoffs therefore converge uniformly over its even-supported
potentials. The odd boundary factor and its inverse tend uniformly to one,
with simultaneous eventual nonvanishing. Removing it proves uniform convergence
of both intrinsic central parity approximants at `2M` to their actual products.

Intrinsic parity limits are now defined directly from the potential, agree
with every admissible completed-root construction, and retain its exact
orders and factorization. The normalized polynomials converge uniformly on
actual joint neighborhoods of the even-supported potential space. Combined
with eventual analyticity, this gives complex smoothness, uniform convergence
of Fréchet derivatives, and positive-radius Taylor expansions. Both limits
are jointly analytic, including on the source period-one coefficient space
and at spectral collisions. Every mixed iterated derivative is analytic.

The classical fundamental solution is now constructed for arbitrary continuous
potentials on the full unit interval. A factorial Picard-iterate estimate
proves existence and uniqueness without restricting the coefficient size.
The solution satisfies the original physical spectral equation. Its normalized
columns have Wronskian one, their matrix propagates every initial vector, and
the monodromy trace detects periodic and antiperiodic solutions through the
characteristic determinant. The free trace is exactly `2 cos z`.

The classical construction is now jointly analytic in the spectral parameter
and continuous potential. The coefficient-to-Volterra map is bounded complex
linear, and its factorial power bound makes `1-V` invertible for every
coefficient size. The inverse equals the earlier initial-value solution and
depends analytically on the coefficient in the supremum norm. Composing with
the actual joint coefficient map proves analyticity of the monodromy, trace,
and boundary determinants, including at multiple roots. All mixed derivatives
of the trace are analytic.

The forward bridge from original Hilbert parity eigenvectors to classical
monodromy is now proved for potentials with a continuous representative on
the unit interval. Absolute continuity and the almost-everywhere original
equation give the constructed classical solution. Fourier parity supplies
the endpoint sign and makes restriction to the unit interval injective.
Nonzero eigenvectors have nonzero initial values, so intrinsic even and odd
product zeros force trace values `2` and `-2`. Their zero sets are disjoint;
full-product zeros force zeros of the classical discriminant squared minus four.

The reverse spectral bridge is now proved under the same Hilbert and continuous
representative assumptions. Signed repetition of a classical endpoint solution
has weighted Fourier coordinates with the correct parity. An almost-everywhere
parity translation identity makes unit-interval vanishing determine an original
base vector, so the original eigen-equation can be checked on that interval.
The extension therefore gives a nonzero original parity eigenvector. Intrinsic
even and odd product zeros are now equivalent to trace values `2` and `-2`;
the full-product zero set equals the trace-squared-minus-four zero set.

The inhomogeneous bridge is now proved for original domain-valued sources.
The inverse Volterra operator constructs physical C¹ forced solutions, with
uniqueness among absolutely continuous almost-everywhere solutions. The source
signs agree with `(z-L)a=b`. Fixed-parity source equations can be checked on the
unit interval, and signed extension proves the converse. Fixing the initial
vector gives a unique original preimage. At every finite root-chain length,
extending a prescribed original source is equivalent to a two-coordinate
classical endpoint equation involving the zero-initial forced solution.

The normalized zero-initial chain operator now gives the exact spectral
factorization and a convergent whole-curve Taylor series with positive radius.
Every spectral derivative is the corresponding signed chain curve multiplied
by its factorial. Evaluating the two columns gives the same series and derivative
identities for the fundamental matrix and actual monodromy. The boundary matrix
series has constant coefficient `M(z)-σI` and signed chain endpoints thereafter.

Finite original parity chains are now identified with the actual boundary
Taylor equations. Their classical curves are finite convolutions of normalized
chains and arbitrary initial values. Alternating those initial values gives
the ordinary Taylor coefficients. The finite boundary convolution is a linear
map on finitely many complex pairs; each kernel vector yields a unique original
chain top vector, and each original finite parity root vector has a unique
representing kernel jet.

The reconstruction is now complex linear, with the actual physical curve and
initial values retained. Domain inclusion gives a linear equivalence of each
finite boundary Taylor kernel with the corresponding original parity root
space. All finite nullities agree with the original root dimensions, increase,
and eventually equal the full original parity algebraic multiplicity. The
free nullity sequence is computed exactly at all lengths and Fourier indices.

Scalar truncated multiplication is now identified with its formal Taylor
convolution, with exact nullity `min(N,m)` for a scalar series of order `m`.
Its formal order equals the analytic vanishing order for convergent Taylor
series, including infinite order. Diagonal two-by-two formal systems split
linearly and have eventual nullity equal to their determinant order. The
actual monodromy boundary maps now equal the formal matrix Taylor actions
built from their convergent coefficients.

General formal matrices now reduce to diagonal form through row and column
units. Every finite nullity is preserved, and for nonzero determinant it has
the exact form `min(N,a)+min(N,b)`, where `a+b` is the determinant order. A
singular formal matrix has nullity at least `N`; the original root-dimension
bound therefore proves that each actual boundary formal determinant is
nonzero. Its order now equals the original parity algebraic multiplicity.

Scalar Taylor extraction now respects multiplication, by the iterated
product rule and its factorial coefficients. Consequently, forming the
formal determinant commutes with the convergent matrix Taylor expansion.
Classical analytic boundary determinant orders now equal original parity
algebraic multiplicities. The shifted traces `Δ−2`, `Δ+2` and the full
characteristic function `Δ²−4` have the exact original multiplicities,
and hence the same vanishing orders as the intrinsic canonical products.

Equal finite orders now give canonical filled quotients that are entire and
nonvanishing. The actual shifted traces and full characteristic function
factor exactly as those quotients times their canonical spectral products,
including at common zeros. The parity quotients multiply to the full quotient.
A bounded quotient is a nonzero constant; a prescribed finite limit at infinity
determines that constant and, in particular, a limit of one proves normalization.

The first product estimates at infinity are now proved. On a fixed vertical
line, all free denominators dominate their height-one values once the absolute
imaginary height is at least one. The existing finite-exponent resolvent
summability gives a common summable majorant. Dominated convergence makes the
absolute relative-displacement sum tend to zero; an exponential product bound
then makes the relative product tend to one. Rescaling retains the even and
odd signs, and completed actual pairs transfer this limit to all three
canonical products for every finite `p>1` and even-supported potential.

The classical solution now has an exact scalar Duhamel formula in each
coordinate after multiplication by any common exponential weight. The weights
`exp(izt)` and `exp(-izt)` isolate the decaying coordinate in the upper and lower
half-planes. The decaying kernel has integral at most the reciprocal decay
rate, uniformly in the oscillatory part. Its actual coordinate error is thus
bounded by `‖Φ‖ B/(2|Im z|)`, provided the opposite weighted coordinate is bounded
by `B`. Nonzero triangular potentials verify both signs and the height-two
constant `1/4`.

The coupled integral equations now close this bound without a hypothesis on
the unknown solution: for decay rate `a≥2‖Φ‖²`, the slow coordinate is bounded
by `2(|u(0)|+‖Φ‖|v(0)|/a)`. Applying this to the two normalized columns gives
trace error at most `2‖Φ‖²/a+2‖Φ‖²/a²`. Thus the exponentially normalized
classical trace tends to one at both imaginary ends, and every fixed shift
of the trace, as well as `Δ²−4`, has ratio one to its free function. These
limits allow an arbitrary varying real spectral part for fixed continuous
potentials.

The classical/canonical filled factors now tend to one at both ends of every
fixed vertical line. For compatible continuous Hilbert potentials, boundedness
alone therefore proves each exact normalization by Liouville's theorem.
Outside fixed discs around `πℤ`, the scalar free resolvent has a common operator
bound into `ℓ¹`. Finite Fourier inputs tend to zero as `|z|→∞`, and density plus
equicontinuity extends this to all finite Banach exponents. Consequently the
absolute relative-displacement sum vanishes there. Full and parity spectral
products, and all intrinsic canonical products for finite `p>1`, have ratio
one to their free functions along every such escaping path, including real
midpoints between consecutive lattice points.

A real phase gauge now removes the real spectral part without changing either
the potential supremum norm or the solution norm. Gronwall gives the global
trace bound `|Δ(z)|≤2 exp(|Im z|+‖Φ‖)`, uniform in the real part and on potential
norm balls. Every free sphere lies outside all open free discs. Maximum modulus
therefore extends an exterior entire-function bound across every disc, and
compactness handles an omitted bounded central region. Exact parity and full
normalization now reduce to a quotient bound at large exterior parameters.

The remaining quotient bound is now proved. Periodic reduction bounds both
free parity inverses on every horizontal strip outside fixed free discs. The
classical half-plane limits give bounds above and below this strip. Pulling back
real at-top filters turns the canonical exterior limits into one uniform
positive lower bound for all large separated spectral parameters. Division
then bounds the actual filled quotient at exterior infinity. Maximum modulus
and its vertical limit fix the entire factor to one. Thus the corrected
identities `f=Δ−2`, `g=Δ+2`, and `fg=Δ²−4` hold for every even Hilbert potential
with a compatible continuous representative, at every complex parameter.

Parity-preserving finite Fourier truncations now converge inside each parity
subspace at every finite exponent, and lift to the original one-derivative
domain. The exact classical identity on even Hilbert domain potentials and
continuity of both products imply `f+2=g−2` for every even Hilbert potential,
without any continuous-representative assumption. The intrinsic discriminant
is now defined as `f+2`, jointly analytic for finite p>1. At p=2 it equals
`g−2`, its square minus four is the full spectral product, and its ±2 levels
are the original parity spectra. Classical traces of any convergent even domain
approximation have this intrinsic limit, with only Hilbert-norm convergence.

The exponent comparison is now proved for arbitrary common potentials. The canonical contractive base and domain inclusions
commute with the actual spectral pencil. A larger-exponent domain vector has
absolutely summable coefficients; its equation with a smaller-exponent potential
and source recovers the derivative at that smaller exponent. Induction transports
every finite generalized root space onto its counterpart. Full root spaces,
spectra, and both parity multiplicities agree, hence so do all normalized central
polynomials and all canonical products. Density of the Hilbert image above two,
and direct comparison below two, establish `f+2=g−2` for every finite p>1.
The squared discriminant minus four is the full product, with exactly the
original spectral zeros and multiplicities. Its values on the dense absolutely
summable Hilbert potentials uniquely determine the continuous extension.

The printed cosine-quotient domain is now audited using arbitrarily large free
cosine zeros in the exterior. A valid additive formulation is proved for each
fixed even potential at finite p>1: both `Δ−2 cos` and `Δ′+2 sin`, divided by
`exp(|Im z|)`, tend to zero uniformly in sufficiently large exterior parameters.
The derivative proof uses Cauchy circles of half the separation radius.

The normalized reciprocal sine is now bounded on the full exterior, using
compact periodic reduction on a strip and an explicit constant-four bound
above imaginary height one. Hence `Δ′/(−2 sin) → 1` at every fixed potential,
with uniform spectral thresholds. All sufficiently large critical points lie
inside arbitrary radius-r free discs, for 0<r≤π/4. The entire derivative is
nontrivial, with finite orders, isolated zeros, and finitely many zeros on
every compact set. Its zero-potential critical set is exactly πℤ.

The free derivative now has exact order one at each lattice point, count one
in a disc of radius less than π around it, and count 2N+1 in the central disc.
Rouché transfers these counts to Δ′ beyond a fixed-potential cutoff, with no
boundary zeros. The count-one multiset gives a unique simple critical point
strictly inside each distant disc. The central and distant open discs exhaust
all critical points, with one common cutoff and any 0<r≤π/4.

For each tolerance, the corrected displacement budget now becomes small on
one open convex potential neighborhood. Complete actual parity pairs have
bounded full displacement norms and small tails there. Uniform finite-head
resolvent decay plus the common tail bound makes both absolute relative sums
small at exterior infinity. Exponential product control and parity subsum
comparison give simultaneous full/even/odd canonical ratio estimates.

The valid additive trace and derivative asymptotics, and the derivative ratio,
now have one potential neighborhood and one spectral threshold for each positive
tolerance. Both may depend on the tolerance. Joint limits permit the potential
to converge while the spectral parameter escapes. The cosine-quotient source
audit remains in force.

The neighborhood derivative estimate now gives one integer cutoff for the
distant count one and the central count 2K+1, simultaneously for all nearby
even potentials and every larger central cutoff. Both boundary families are
zero-free; each distant critical point is unique and simple. The central and
distant open discs exhaust all critical points on that same neighborhood.

Real-type critical points are now proved real. Gauss–Lucas excludes nonreal
critical points of the positive-degree central spectral polynomials. The
nontrivial canonical derivative has finite orders, so locally uniform limits
preserve nonvanishing off the real axis. Differentiating Δ²−4 transfers this
to Δ′. One theorem now packages every assertion of Lemma 8.3.

The free-reference off-diagonal product estimate is now proved. Keeping the
signed linear term gives a quadratic infinite-product remainder bound.
Arbitrary half-unit sampling perturbations change the bounded Hilbert
transform by an ℓ¹ square-kernel convolution. Young puts the absolute rows
in ℓ^(2p); Hölder returns their squares to ℓᵖ. Rescaling gives the spectral
relative product with its local factor omitted, uniformly on displacement
norm balls and over all samples in closed half-π free discs.

A positive lp majorant now controls the off-diagonal product throughout every
free disc at once. Filled sine quotients have exact center values and a
uniform disc bound. Restoring the local factor gives a filled local product
whose sampled error from sine belongs to lp, uniformly on displacement norm
balls. Off the lattice it agrees exactly with sine times the full relative
product, even when spectral numerators vanish.

The paired product is now identified off the lattice as minus four times the
restored sine factors. Maximum modulus carries the lp majorants through all
free centers, and Cauchy controls derivatives on smaller discs. Rescaling
both parities and interleaving their coefficient majorants transfers the
bounds to the actual canonical discriminant. One open convex potential
neighborhood supplies common lp norm bounds for every admissible sampling
sequence. This completes both sampled error assertions and the local
uniformity of Lemma 8.4.

The inverse filled sine quotient now bounds a critical-point displacement
by its sine value. Lemma 8.4 controls the distant critical roots in lp.
The 2N+1 central analytic roots are enumerated with multiplicities and
spliced into the unique simple distant sequence. The completed sequence
has exact global analytic multiplicities and an lp displacement bound
uniform on one open convex potential neighborhood. This proves the
displacement assertion of Lemma 8.5.

The normalized single product is now constructed from the literal cutoffs
`2 ∏[-N,N] (ξn−z)/πn`, with exceptional denominator one at zero. Euler
products fix the free limit as minus twice sine. Local uniform convergence
extends through the free lattice, including derivative convergence. The
filled product has exactly the selected closed root set, hence exactly the
critical zero set for a complete critical labeling. Its quotient by minus
twice sine tends to one along every separated escaping path.

Each critical-root fiber is now proved finite, and finite cutoff orders
stabilize to the derivative's analytic multiplicities. Rouché stability
on isolating discs transfers these orders to the entire product. The
filled quotient is entire, tends to one on the free-disc exterior, and
is globally bounded by maximum modulus. Liouville and an escaping
cosine-zero sequence fix the quotient to one. This proves the derivative
product identity and locally uniform cutoff convergence on the whole
plane, together with the previously obtained locally uniform lp bounds.

Finite multisets can now be enumerated in order on prescribed finite
ordered index sets, retaining repetitions. A separate complex lexicographic
relation orders the central critical multiset. Replacing the central head
preserves complete labeling and all multiplicities. Real-part bounds order
the two distant tails and separate them from the central cluster. Thus
complete ordered critical sequences now exist on a common potential
neighborhood, with lp norm bounds and the exact derivative product.

Ordered finite enumerations are now unique even with repetitions. A
complete critical sequence remains a valid labeling at every larger
central cutoff. Comparing two sequences at a common cutoff proves global
uniqueness. Canonical critical coordinates and their lp displacement
coefficient are now defined, with exact multiplicities, reality at
real-type potentials, the derivative product, common local norm bounds,
and exact free values `nπ`.

Joint continuity now gives locally uniform potential limits of the
discriminant and its derivative. Compact root confinement and Rouché
preserve zero-free compact sets and circular counts. Distant canonical
coordinates are continuous at every even potential; imaginary parts of
all canonical coordinates are continuous at real-type potentials.
Restricting root multisets to central subsets now identifies analytic
counts with counts of canonical indices, retaining repeated roots.

Real-diameter discs now separate prefixes and suffixes of the real
critical sequence. Their zero-free boundaries preserve counts under
perturbation, and finite ordered-count bounds trap each nearby real part
between arbitrarily close barriers. This proves full canonical coordinate
continuity at real-type potentials, including central collisions and
complex even perturbations. A combined theorem now packages all assertions
of Lemma 8.5 with the canonical roots and their common local lp bounds.

Conjugation symmetry now passes from finite parity polynomials to the
discriminant. Its values and derivatives are real on the real axis at
real-type potentials. Real Rolle and distant critical uniqueness give
strict interlacing between distinct actual distant gap endpoints.
Multiplicity at least two proves the collapsed-gap equality, even for
complex potentials. The canonical critical coordinates therefore lie
in every sufficiently distant actual real periodic gap, regardless of
the order of the pair slots.

The full central periodic multiset now retains every original algebraic
multiplicity and is the sum of the parity multisets. An ordered paired
enumeration sorts it without losing repeated values. Complete endpoint
labelings record this central multiset, the exact original distant
pairs, and both lp displacements. Sorting the distant slots and replacing
the center preserves these data. Real-part separation proves global
lexicographic order on one potential neighborhood at every sufficiently
large cutoff.

Ordered paired multiset uniqueness and central cutoff growth now prove
that the complete ordered endpoint sequences are independent of cutoff.
Canonical left and right endpoints retain spectral exhaustion, real-type
reality, and lp displacements. One neighborhood gives common valid cutoffs
for these fixed coordinates. At zero potential both endpoints are exactly
`nπ`, with identically zero displacement coefficients.

The periodic product now has locally uniform parameter limits and stable
circular counts on the full potential space. Within the central real-part
bounds, these analytic counts equal counts of both endpoint slots, including
repeated values. Compact confinement controls imaginary parts; stable
prefix and suffix counts control real parts. Both canonical endpoint
coordinates are now continuous at real-type potentials under arbitrary
even complex perturbations, including spectral collisions.

Real scaling preserves real type and produces continuous canonical
endpoint paths. The endpoint discriminant levels cannot change along
these paths, so their free values identify each signed index's parity.
Filtering by these levels recovers the exact central parity multisets.
Neighboring real gaps are strictly separated; Rolle and repeated-root
multiplicity give a critical point in every open or collapsed gap.

One distinct critical witness per real gap now exhausts the full central
critical multiset at every common cutoff. Ordered enumeration uniqueness
identifies each witness with its canonical critical index. This proves
global indexed interlacing, strict inequalities for open gaps, and equality
for collapsed gaps. Each real gap contains exactly one critical point,
and every critical point belongs to exactly one gap. The canonical critical
sequence is strictly increasing, so the exact multiplicity formula makes
every critical point simple, with nonzero second discriminant derivative.

A strict real second-derivative test and the real-axis derivative bridge
now make every canonical critical coordinate a strict local maximum or
minimum, including at collapsed gaps. Fermat's theorem identifies all
real local extrema with the canonical critical sequence; each indexed
gap contains exactly one.

The exact factorization behind Lemma 8.6 is now proved. Deleted-pair
polynomial cutoffs and their derivatives converge locally uniformly on
all of the complex plane. Their entire limit `Gₙ` gives
`∆²−4 = −4((λ−τₙ)²−γₙ²/4)Gₙ`, correcting the printed positive sign.
At a canonical critical point, with `a = λₙ•−τₙ`, differentiation gives
`(2Gₙ+aGₙ′)a = γₙ²Gₙ′/4`; a nonzero coefficient yields the exact quotient
formula without dividing by the gap. At zero potential `Gₙ` is the square
of the filled sine quotient and has value one at the removed root.

The remaining product now equals the squared free sine quotient times
the two omitted-diagonal relative products off the free lattice, including
at actual endpoint zeros. Maximum modulus and Cauchy's estimate give
bounded lp majorants for its error and derivative error on half-pi and
quarter-pi discs. These estimates hold on a common potential neighborhood
for the canonical product. Canonical endpoint displacements now have
bounded full norms and arbitrarily small local tails; ordering preserves
the original pairwise tail estimates.

Free squared-quotient displacement bounds now give locally uniform lp
tail representatives for `Gₙ(cₙ)−1` and `Gₙ′(cₙ)`. Finite modification
proves full lp membership at each fixed potential. The actual midpoint
offset has locally bounded lp norm, and the bounded multiplier estimate
therefore gives locally uniform lp tails for `2Gₙ+aGₙ′−2`, retaining the
exact squared-gap identity at all even complex potentials.

A finite-block and small-tail split now makes the relative products
uniformly close to one on distant free discs. Maximum modulus, Cauchy,
and arbitrarily small critical localization give uniform smallness of
`Gₙ(cₙ)−1` and `Gₙ′(cₙ)`. The midpoint coefficient consequently has norm
at least one on a common tail. Its exact quotient supplies locally
uniformly bounded lp coefficients in `cₙ−τₙ=γₙ²aₙ`, completing Lemma 8.6
for all finite exponents greater than one and all even complex potentials,
including collapsed gaps. This uses genuine uniform small-tail control,
not decay inferred from a bounded lp ball.

The real gap characterization is now complete. Positive real pair
denominators and the negative full-product normalization give the correct
cutoff signs. Passing to the limit and using spectral exhaustion proves
that closed gaps are exactly where `|∆|≥2`, open interiors exactly where
`|∆|>2`, and endpoints exactly where equality holds. Continuity and the
known endpoint parity give `(-1)^n ∆≥2` on each closed gap, strictly inside
an open gap, for every signed index.

Complete actual Dirichlet and Neumann sequences now enumerate the central
root multisets and the distant simple branches, retaining every algebraic
multiplicity and lp displacement. One neighborhood and cutoff work for
both boundary conditions. The ordinary period-one interval extension
transfers these results to source coefficient potentials. The normalized
Section 9 cutoffs now converge locally uniformly to entire functions with
exactly the actual boundary spectra as their zeros; the free value is
`sin λ`. This proves the fixed-potential product construction, without
yet claiming independence from central label choices or joint analyticity.

Complete boundary labelings now retain their exact central multisets at
every larger cutoff. The normalized intrinsic central polynomials therefore
identify all such products, independently of labels and cutoff. Their limit
defines the intrinsic Dirichlet and Neumann characteristic functions, with
locally uniform convergence of values and first spectral derivatives. Finite
root-polynomial orders and Rouché stability identify the exact analytic zero
orders with the original restricted-operator multiplicities. Both intrinsic
functions equal sine at zero potential. All these conclusions also hold for
the original period-one coefficient realization.

Projection transport now gives intrinsic shifted determinants on varying
finite spectral ranges, jointly analytic even at determinant zeros. Boundary
contour restrictions retain all original generalized root chains and
algebraic multiplicities. Their determinants equal the actual finite
boundary root products. Consequently one open convex neighborhood and
threshold give joint analyticity of both normalized central polynomials
at every larger cutoff, including after the source interval extension.

Complete ordinary boundary root displacements now have uniformly bounded
full lp norms: distant roots belong to the corresponding periodic pair,
and the common central box bounds every central enumeration. Hölder tails
give single-product convergence uniform over bounded families off the free
lattice; maximum modulus fills the free centers uniformly. Intrinsic boundary
polynomials therefore converge uniformly over one potential neighborhood
and every compact spectral set for both boundary conditions. Local analytic
approximation gives joint complex smoothness, operator-norm convergence of
Fréchet derivatives, and joint Banach-space analyticity of the intrinsic
infinite products. Pullback proves joint analyticity and exact spectral zeros
on the original source coefficient space, completing ordinary Lemma 9.1(i).

Canonical ordinary boundary coordinates are now constructed by sorting the
actual central multiset while fixing distant branches. Their ordered
labelings agree across cutoffs, retain exact original multiplicities and lp
displacements, and recover the intrinsic characteristic products. Free values
are the signed lattice and real-type roots are real at every index. Both
canonical sequences have common locally bounded full lp norms and complete
labelings at all sufficiently large cutoffs.

Local uniform characteristic families and exact analytic counts on the
central vertical strip now give stability of prefix and suffix counts.
Compact root confinement controls imaginary parts; arbitrarily close real
barriers control each ordered real coordinate. Thus every canonical ordinary
boundary coordinate is continuous at real type under complex perturbations,
including collisions. The ordinary source interval extension preserves real
type, so pullback proves Lemma 9.1(ii) on the original coefficient space.
Both canonical source sequences are analytic outside a finite central block
at arbitrary complex potentials.

The classical part of the boundary gap comparison is now established. The
literal endpoint functions have their exact free normalization and joint
analyticity, and their zeros are exactly the original physical separated
eigenvalues. Unimodularity gives `Δ²−4=δ²−4χDχN`; real-type monodromy symmetry
then gives the trace bound at boundary roots, with strictness characterized
by nonzero anti-discriminant. Comparing compatible physical representatives
locates real boundary eigenvalues in some original periodic gap, while
keeping the periodic and reflected boundary potentials distinct. Real scaling
now gives continuous boundary roots and original periodic endpoints with the
same physical representative. A midpoint-barrier continuation theorem
preserves the initial free gap index, proving indexed interlacing for all
compatible continuous real-type potentials in the Hilbert realization.
Collapsed gaps identify both boundary roots with the endpoint, and the
literal signed trace bounds hold for every integer index.

Boundary reflection conditions and all generalized root spaces now commute
with finite exponent inclusion. This preserves original boundary spectra,
algebraic multiplicities, and every fixed central multiset, including at
p=1. Comparing ordered central enumerations in a block containing any given
signed index proves canonical boundary coordinate invariance for p>1.
Canonical displacements and normalized characteristic functions agree too.
Both original periodic endpoints and their displacement sequences are now
exponent independent, by the analogous ordered paired-multiset comparison.
Finite-polynomial physical formulas and density identify the half-interval
map across exponents. This proves compatibility of the completed ordinary
and auxiliary reflected extensions. A continuous inclusion in the source
pair topology commutes with all three distinct potential realizations;
source boundary coordinates, normalized characteristics, and the original
periodic endpoints consequently agree across finite exponents.

Finite source Fourier polynomials now reconstruct their actual periodic and
Dirichlet-reflected Hilbert potentials. Both agree with one continuous
pointwise real-type curve on the original unit interval. The continuous-case
interlacing proof gives the correct signed gap for each finite real-type
polynomial. Exact exponent compatibility carries this to all finite p>1.
Symmetric Fourier truncations preserve real type and converge in the source
pair norm; continuity of both boundary roots and original periodic endpoints
passes the inequalities to every real-type source potential. This completes
the ordinary Dirichlet and Neumann Lemma 9.1(iii), including collapsed gaps,
strict neighboring-gap separation, and the alternating discriminant level.

The starred boundary roots are now canonical signed coordinates of the
actual auxiliary restricted pencils through their proved phase conjugation.
Their normalized entire characteristics have exactly the auxiliary spectra,
with original generalized multiplicities as analytic orders. Pullback proves
joint analyticity and coordinate continuity at real-type source potentials;
both canonical coordinates and normalized products are exponent independent.
This establishes the auxiliary analogues of Lemma 9.1(i–ii).

The source phase map now has exact coefficients `(i φ₁, -i φ₂)` and commutes
with period doubling. It transforms the Neumann-reflected auxiliary source
potential into the Dirichlet-reflected ordinary potential of the rotated
source. Thus all starred signed roots and normalized characteristics are
literally ordinary ones at that source. The unrestricted periodic pencils
are phase-conjugate at every chain length; their spectra and original
algebraic multiplicities agree, also on period-one source potentials.

The intrinsic periodic spectrum together with algebraic multiplicities now
uniquely determines both complete ordered signed endpoint sequences, even
when comparing different even potentials. Applying this to the source phase
proves exact endpoint invariance. Ordinary indexed interlacing therefore
transfers to both actual starred boundary restrictions at every finite p>1,
including neighboring-gap separation, collapsed-gap equality, and the
alternating original discriminant level. This completes the starred
interlacing portion of Lemma 9.1(iii).

The actual classical auxiliary endpoint characteristics are now given by
monodromy formulas with the signs dictated by the page-33 domains. Their
zeros satisfy the normalized endpoint equations, both are jointly analytic,
and their Neumann-minus-Dirichlet difference is the classical monodromy
anti-discriminant. The page-53 printed starred D/N monodromy labels are
proved to be swapped relative to those domains. On the full finite-exponent
source space, the corresponding difference of normalized canonical products
is entire, jointly analytic, exponent independent, and zero at the free
potential. It is currently named `sourceAntiDiscriminantCandidate` because
its agreement with the physical monodromy anti-trace for arbitrary `L²`
source input is not yet proved; agreement on dense finite Fourier input and
uniqueness of continuous extension are now proved.

Classical initial-value uniqueness now proves exact phase conjugation for
continuous potentials. The phase fixes both diagonal monodromy entries and
the discriminant, rotates the off-diagonal entries by `i` and `-i`, and
identifies each actual auxiliary characteristic with the ordinary separated
characteristic of the rotated continuous potential. The classical
anti-discriminant consequently equals the ordinary Neumann-minus-Dirichlet
characteristic difference after phase rotation.

The monodromy characteristic's zeros are now proved equivalent to the
actual physical auxiliary eigenvalues of every continuous curve and to the
Neumann-extended coefficient spectrum. For finite source Fourier pairs, the
Neumann extension is exactly the source auxiliary coefficient potential;
therefore each classical auxiliary characteristic and normalized starred
source product have precisely the same zeros. This establishes the zero-set
part of the dense-subspace comparison. Analytic orders and the entire
normalization factor remain to be identified.

The source-normalized complete boundary product now has ratio one to the
free sine along every separated escaping spectral path. This passes to both
intrinsic boundary characteristics and their ordinary and actual starred
source pullbacks at every finite exponent. An exterior threshold bounds the
intrinsic/free ratio below by one half. Separately, the classical monodromy
characteristic has sine-scale growth in the imaginary spectral height, so
its ratio to an intrinsic boundary characteristic is uniformly bounded on
the distant separated exterior. Weighted Volterra entry bounds now prove
that both classical separated characteristics have ratio one to free sine
as imaginary height tends to positive infinity, uniformly in real spectral
part. The phase-conjugated classical auxiliary characteristics share that
limit. Thus classical-to-intrinsic and actual auxiliary-to-starred-source
quotients tend to one along upper separated paths, including the matched
finite Fourier source input. A convergent scalar endpoint Taylor series now
identifies every coefficient with a signed normalized forced-solution chain.
Finite scalar Taylor kernels are exactly the separated endpoint equations for
such chains, and their nullity is the truncated classical analytic order.
The corresponding physical forced chains now define a linear injection into
each finite boundary root space. This proves finite classical analytic orders
and the inequality from classical order to physical algebraic multiplicity.
The scalar Taylor kernel is now linearly bijective with each finite physical
root space. Their dimensions are `min N m`, and the classical characteristic's
analytic order equals the full physical algebraic multiplicity. The intrinsic
boundary characteristic already has that physical order. Their filled
quotient is now entire and bounded; its upper limit one proves exact equality
of the classical and intrinsic normalized characteristics for continuous
physical potentials.

The normalized starred source characteristics now equal the actual classical
auxiliary monodromy functions on every finite Fourier source pair. Their
Neumann-minus-Dirichlet difference equals the classical anti-discriminant
there, for every finite exponent, and the jointly analytic candidate is the
unique continuous extension of those dense finite values. Next connect this
extension with physical monodromy for arbitrary `L²` source data. The full
source identity `∆²−4=δ²−4χDχN` has already been proved by finite-input
comparison and density, so Lemma 9.2(ii) holds at every indexed Dirichlet
root, even if it is multiple. For Lemma 9.2(iii), the generic entire boundary product has a
single ℓᵖ majorant for its sine error on every closed half-π free disc and
its derivative error on every quarter-π disc, uniformly on displacement-norm
balls. That transfer and high-index evaluation are now proved: both starred
products, their difference, and its derivative have uniform free-disc
majorants; all distant canonical Dirichlet samples obey one ℓᵖ tail bound.
The complete sampled sequences lie in ℓᵖ pointwise. A compactness bound for
the jointly analytic candidate on a fixed spectral ball, together with
Cauchy's estimate, now uniformly controls the finite central samples.
Combining that finite block with the tail completes the locally uniform full
ℓᵖ norm assertion of source Lemma 9.2(iii). Next connect the source candidate
with physical monodromy for arbitrary `L²` input, then continue to the action
coordinate prerequisites.
For Lemma 10.1, a common source neighborhood and cutoff now localize both
periodic endpoints, both ordinary boundary roots, and the critical point in
their free quarter-π discs at all distant indices. Those discs are pairwise
disjoint and satisfy explicit linear pointwise separation bounds.
The real-type five-coordinate clusters are now proved to lie in their
indexed gaps and to be strictly separated in real part, with a metric lower
bound by the intervening periodic endpoint gap.
The finite central disc construction is now proved: each midpoint disc
contains its real-type five-coordinate cluster, and a finite minimum of
the positive inter-cluster gaps supplies one margin making all central
discs pairwise disjoint. The discs can now be frozen at the base potential:
continuity of the five coordinates and finite intersection yield one open
source neighborhood where every nearby central cluster remains inside its
assigned disc. The central and uniform tail neighborhoods are now
intersected: every signed index has an explicit assigned disc containing
all five nearby source coordinates. Central discs are mutually disjoint,
as are the free tail discs. Bounded finite margins and localization of the
two outer central endpoints now prove cross separation as well. A connected
source ball supports pairwise disjoint discs for every index and all five
coordinates. The real-type source locus is convex and connected; the union
of its local connected balls is an open connected `Ŵp`. Every point of
this union inherits one local common sequence of pairwise disjoint discs,
with free quarter-π discs at high indices. Convexity of the discs also
contains the complete periodic endpoint segment. This completes the
source-coefficient geometric statement of Lemma 10.1. Next use these
isolating neighborhoods for Lemma 10.2's analytic symmetric spectral
coordinates and the action-coordinate prerequisites.
The next contour step is now proved: every assigned disc contains exactly
its own two canonical periodic endpoints from the actual spectrum, and
every circular boundary lies in the resolvent set. The finite enclosed
spectral set is exactly that endpoint pair. The complete canonical multiset
labeling and pairwise disc disjointness now identify each root's algebraic
multiplicity with its occurrence count in the indexed pair. Summing those
counts proves that every assigned Cauchy–Riesz projection has rank two,
including when the two endpoints coincide. The first two analytic contour
traces now agree on each common disc neighborhood with the canonical
periodic midpoint and squared gap. These canonical functions are therefore
analytic at every source potential in the open connected almost-real domain,
even at double endpoints. The endpoint product now equals the quadratic
expression in the midpoint, squared gap, and spectral parameter. This
identity proves joint analyticity on the same domain, completing Lemma
10.2(iii). A two-step symmetric recurrence now expresses every endpoint
power sum as a polynomial in the analytic midpoint and squared gap. This
proves the full family in Lemma 10.2(i), including coincident endpoints.
The canonical midpoint displacement is now an actual ℓᵖ sequence, with a
uniform full norm bound and uniformly small ℓᵖ tails on a source
neighborhood around every parameter. This proves the midpoint part of
Lemma 10.2(ii). The canonical gap is now an actual ℓᵖ sequence, and its
square belongs to ℓᵖ⁄² pointwise for every finite p>1, including p<2.
The squared-gap `p/2` power tail sum is now exactly the `p` power of the
unsquared gap's ℓᵖ tail norm. Common endpoint tail estimates make it
uniformly small on a source neighborhood around every parameter. This
completes all three assertions of Lemma 10.2 in the source-coefficient
setting. Next formalize the standard roots and contour geometry of
Lemma 10.3, followed by the action-coordinate prerequisites. The
arbitrary-L² physical anti-trace identification remains a separate gap.
For Lemma 10.3, equation (2.9)'s normalized principal standard root is
now defined and its square is identified with the canonical endpoint
factor at every point outside the gap segment. A collapsed gap reduces
exactly to the linear midpoint expression. Next prove that the normalized
radicand avoids the principal square-root cut on the segment complement,
then establish joint analyticity and the cross-disc estimates.
The general preimage calculation for the principal square-root cut is
proved: `1-w²` can leave the slit plane only when `w` is real and
`|w.re|≥1`. For the normalized endpoint ratio, this real condition now
forces the spectral parameter onto the closed endpoint segment. Thus the
canonical source radicand is in the slit plane off its gap segment. The
principal standard root is therefore analytic in the spectral parameter
throughout this complement. The analytic midpoint and squared gap now
also make it jointly analytic in source coefficients and spectral parameter
on the same connected almost-real source domain, including collapsed gaps.
The root norm squared is now identified with the product of its endpoint
distances, and roots are nonzero on distinct isolating discs. Abstract
two-sided endpoint bounds transfer to the root. The free quarter-π disc separation now proves the explicit (2.10)
bounds for every two distinct tail indices on a common connected source
neighborhood. A finite central block now has both a locally uniform positive lower
bound and a uniform upper bound. Its finite index span turns these into
the full index-scale estimate (2.10) for all distinct central indices
on one connected source neighborhood. Sharpening the outer endpoint
localization now gives a π/4 pointwise gap between any central disc and
a positive tail disc, and the same lower bound for standard roots in
both orientations. The mirrored strict negative outer-endpoint
localization gives the same π/4 bound for central–negative-tail pairs.
A finite bound on the central discs’ offsets from the free lattice
centers and the quarter-π tail radius now give a common `|m−n|` upper
bound for mixed-pair roots in both orientations. The fixed π/4 separation
and lattice-center triangle inequality likewise yield one `|m−n|`
lower bound in both orientations, conditional on endpoint localization,
pointwise separation, and segment exclusion. The positive and negative
tail geometry supplies these conditions on every assigned central/tail
disc pair when nearby clusters lie in the disc family. One constant now
gives both sides of (2.10) for all mixed pairs. Uniform tail isolation
and finite central-disc isolation now supply a single connected source
neighborhood and disc family for that mixed estimate. Next reconcile the
central-block estimate with this same disc family. The central estimate
now permits its margin to be reduced below any prescribed positive bound,
in particular π/4. A common connected source neighborhood and
pairwise-disjoint all-index disc family now combine the central,
mixed, and tail estimates into the full two-sided bound (2.10).
The reciprocal root is analytic outside its gap segment, and Cauchy's
theorem gives the off-diagonal circle integral zero. The normalized
diagonal integral equals `−1` when the gap collapses. Circle inversion
and the complex mean-value theorem now establish the same value for
every midpoint-centered circle strictly enclosing the gap, even when
the gap is noncollapsed. Interpolating centers and radii of two discs
that contain the gap now keeps the segment strictly inside every
intermediate circle. A shifted inversion computes the integral on large
circles about any center, and annulus invariance carries its value to
every smaller circle still enclosing the full gap. Thus the diagonal
normalized integral is `−1` on any such circle; the off-diagonal integral
is zero on filled circles in a different isolating disc. A general
holomorphic one-form theorem and its source-root specialization now prove
invariance of the path integral along smooth closed-loop homotopies that
stay away from the gap. Reparameterizing a circle on the unit interval
identifies its path integral with the existing circle integral. Thus the
normalized value is `−1` for any smooth closed loop with a gap-avoiding
smooth homotopy from an enclosing circle. A periodic twice-smooth polar
radius above the gap-enclosing radius now supplies such a homotopy;
its contour therefore has value `−1`, with a cosine modulation as an
explicit noncircular example. The affine radial homotopy also remains
inside any outer disc that bounds both endpoint radii. Confined to an
assigned isolating disc, it transfers the off-diagonal zero circle
integral to the polar contour. Thus the normalized indexed integral is
`−δₘₙ` for this noncircular class. The same identity now applies to any
smooth loop with a smooth homotopy from an enclosing circle whose image
avoids the indexed gap and stays in the assigned isolating disc. The
homotopy image is compact, so no auxiliary neighborhood is needed in
the theorem statement. An affine homotopy now supplies the deformation
for every twice-smooth loop uniformly close to an enclosing circle.
Explicit distance bounds keep every intermediate point outside a disc
containing the indexed gap and inside an outer disc contained in its
isolating disc; hence this class also satisfies `−δₘₙ`. Convex
contraction now proves off-diagonal zero for every twice-smooth closed
loop contained in an assigned isolating disc, with no homotopy or
circle-closeness hypothesis. The full indexed theorem therefore requires
a gap-avoiding circle homotopy only for the diagonal case; that homotopy
need not remain in the isolating disc. Next establish the diagonal value
for the full admissible contour class of Lemma 10.3. The inverse-root
integral is now locally constant in the uniform topology on smooth loops
avoiding the gap: compactness supplies a positive uniform buffer, and
every sufficiently close smooth loop deforms affinely within the gap
complement. Thus a known diagonal `−1` value persists under all such
small deformations. It remains to connect every admissible
counterclockwise contour to a known one, or prove the same value by a
winding-number argument. Local constancy and connectedness now carry
the integral across any continuous family of twice-smooth gap-avoiding
loops, including moving basepoints. The normalized `−δₘₙ` theorem uses
only such a continuous family from an enclosing circle; it no longer
requires the homotopy map on the full square to be twice smooth.
The boundary values in equation (2.12) now hold on both sides of every
noncollapsed canonical complex periodic gap for all `−1≤t≤1`, including
the midpoint and endpoints. A connectedness argument fixes the root
branch throughout the upper half-plane; reflection fixes the lower
branch. Their continuity gives joint one-sided limits as the spectral
parameter approaches each gap point through its entire open side, even
when the longitudinal coordinate varies. The cosine parametrization of
Lemma 10.4 now removes the endpoint singularities of the side kernel:
its integral equals `±i` times an ordinary integral over an interval
of length at most `π`. Compactness gives an attained maximum of `‖f‖`
on the gap, and this one maximum bounds both normalized side integrals
uniformly in the stopping point. The result applies to the actual
canonical source root through its proved side limits. The weighted
integral in the dissertation's `r` parameter is now proved integrable
and equal to the cosine integral by substitution. An independently
defined straight side path integral has the same value and satisfies
the same canonical-source maximum bound. Removing the left singular
endpoint gives that value as a limit; at the right gap endpoint,
removing both singular endpoints does too. Next continue with the
infinite standard-root product in Lemma 10.5.
The printed general-`p` central-height constant remains a separate open item.

The Lemma 10.5 factor step is in `SourceStandardRootProductFactors.lean`:
normalized errors have an exact midpoint/spectral/square-root decomposition,
the free spectral terms cancel for `k,-k`, and the paired factor is
`1+a_k+a_{-k}+a_ka_{-k}`. A global norm estimate controls the principal
square-root error by the radicand error. Next use the source midpoint and
squared-gap sequence bounds to prove locally uniform summability of the
paired errors and convergence of the infinite product.

`SourceStandardRootMidpointProduct.lean` now constructs the source midpoint
factor correction as an `ℓ¹` sequence. Its `k,-k` pairing is absolutely
summable, and the correction has uniformly small `ℓ¹` tails on a source
neighborhood. Next bound the square-root remainder by a summable tail,
then combine it with the midpoint correction and quadratic error term
to build the locally uniform paired product.

`SourceStandardRootSqrtRemainder.lean` proves the rationalized pointwise
root-error bound, absolute summability of the source square-root remainder,
and a shared summable `1/k²` majorant on source neighborhoods and bounded
spectral regions. Next combine midpoint and square-root terms to show
absolute summability of paired factor errors, control their quadratic
cross term, and construct the locally uniform nonzero product.

`SourceStandardRootPairedProduct.lean` now constructs the omitted-zero
product itself. The normalized single-factor error is an `ℓ²` sequence,
the paired excess is `ℓ¹`, and the natural finite paired cutoffs converge.
Off the noncentral gap segments, no factor vanishes and neither does the
infinite product. Next prove locally uniform convergence and analyticity
in the spectral parameter and source potential, then extend from omitted
index zero to an arbitrary omitted index.

`SourceStandardRootPairedProductAnalytic.lean` defines the natural finite
cutoffs and proves their pointwise convergence to the existing product.
Each factor and cutoff is spectrally analytic off the noncentral gaps; the
cutoffs are jointly analytic on the common connected almost-real source
domain. Factor continuity on compact subsets is available for the next step:
prove locally uniform convergence, then pass analyticity to the limit.

`SourceStandardRootPairedProductUniform.lean` proves a uniform `1/|k|`
bound for single-factor errors on source neighborhoods and bounded spectral
sets, hence a shared summable `1/k²` bound for their paired cross term.
For each fixed source potential, it then gives a summable factor majorant
on compact spectral sets and uniform convergence of the finite cutoffs
there. Next show the gap-complement domain is open and transfer spectral
analyticity to the limit; the source-uniform midpoint tails are available
for the later joint-analyticity argument.

`SourceStandardRootPairedProductHolomorphic.lean` bounds every periodic
gap segment within a fixed radius of its free lattice point, proving the
family locally finite and the noncentral-gap complement open. Compact-
uniform product convergence then becomes local uniform convergence on that
domain. Analytic finite cutoffs give spectral analyticity of the infinite
omitted-zero product for each source potential. Next prove source-uniform
product convergence and joint analyticity, then extend the omitted index.

`SourceStandardRootPairedProductJointUniform.lean` uses a fixed reciprocal
lattice and source-uniform Hölder tails to control all finite midpoint
correction sums. Combined with the square-root and quadratic cross-term
majorants, this gives uniformly vanishing finite absolute tails for complete
paired-factor errors near any source and on bounded spectral sets.
`UniformProductTails.lean` supplies the finite-prefix product criterion, so
the paired cutoffs converge uniformly on a joint neighborhood wherever the
finite cutoffs are continuous. The existing connected source domain makes
this available at every point of the noncentral-gap complement. Next prove
joint analyticity of the limit on an open joint domain, then extend from
omitted index zero to arbitrary omitted indices.

Joint local uniform convergence and analytic finite cutoffs now imply
joint continuity of the infinite omitted-zero product wherever the source
lies in the common connected almost-real domain and the spectral point
avoids noncentral gaps. The pointwise nonvanishing theorem strengthens
this to nonvanishing on a joint neighborhood at each such point. Next
establish a common open analytic domain for all finite cutoffs and pass
Banach-space analyticity to the locally uniform limit.

`SymmetricSegmentIncidence.lean` expresses membership in a complex gap
segment through its midpoint, squared endpoint difference, and a compact
real parameter. The incidence set is closed; continuity of the symmetric
gap data therefore makes avoidance of each fixed moving gap locally
stable without ordering the endpoints. `SourceStandardRootPairedJointDomain.lean`
adds a source-uniform free-lattice bound, so all sufficiently distant gaps
avoid one spectral ball. Finite-gap stability and this tail bound prove the
joint moving-gap complement open. On a single connected source domain,
all finite paired cutoffs are analytic and converge locally uniformly on
that open complement. Next apply a Banach-space analytic-limit theorem to
the infinite product, then extend to arbitrary omitted indices.

`LocalAnalyticApproximationOn.lean` extends the Banach-space
fixed-ball approximation criterion to an open domain. Uniform convergence
and analytic finite approximants survive Fréchet differentiation on
smaller balls, yielding `ContDiffOn ℂ ∞` and uniform operator-norm
convergence of first derivatives. Applied in
`SourceStandardRootPairedProductJointSmooth.lean`, the omitted-zero
paired product is jointly complex smooth on the open moving-gap domain.
Next establish a local Taylor expansion for complex-smooth maps there,
then treat arbitrary omitted indices.

`BanachTaylorBoundsOn.lean` and `BanachSmoothAnalyticOn.lean` now supply
the local Taylor expansion for scalar-valued complex-smooth maps on open
Banach domains. The Fréchet series has positive radius and sums along
short complex lines by Cauchy's theorem. Applied in
`SourceStandardRootPairedProductJointAnalytic.lean`, this proves joint
analyticity of the omitted-zero paired product on the open moving-gap
domain. The next product step is arbitrary omitted indices.

`SourceStandardRootOmittedFinite.lean` starts the arbitrary-index case
of Lemma 10.5 with the literal symmetric cutoffs and the existing
single-root free normalization. The moving-gap complement is open for
every omitted index on one common connected almost-real source set;
every cutoff is jointly analytic and nonzero on its domain, and the
zero-index cutoff is definitionally related to the paired construction.
Next prove local uniform convergence of these cutoffs and analyticity
and nonvanishing of their infinite limit.

`SourceStandardRootOmittedProduct.lean` factors each literal symmetric
cutoff into its zero mode and paired factors with the omitted root
replaced by `1`. The paired deviations remain absolutely summable
because only one pair changes. This proves pointwise convergence of
the literal cutoffs for every omitted index and nonvanishing of the
limit on the corresponding gap complement; at index zero the limit
equals the previous paired product. Next upgrade convergence to local
uniform convergence on the open joint domain and prove joint
analyticity of the limit.

`UniformProductTails.lean` now allows a bounded zero-mode prefactor in
the natural-number product criterion. With the previous paired-factor
tail estimate, `SourceStandardRootOmittedJointAnalytic.lean` proves
local uniform convergence of the literal cutoffs for every omitted
index on its open joint moving-gap domain. The local Banach-space
analyticity theorem gives joint analyticity, and the pointwise factor
argument gives nonvanishing. This completes the product assertions of
Lemma 10.5 in the current source model. Next formalize Corollary 10.6.

`JointSingleSpectralProducts.lean` establishes the numerator's first
analyticity ingredient: the entire normalized single-root product is
jointly analytic in the spectral parameter and arbitrary `ℓᵖ`
displacements, with literal finite cutoffs converging uniformly on
compact spectral sets over bounded displacement families. Next delete
one prescribed numerator factor, retain analyticity across its root,
and divide by Lemma 10.5's nonzero omitted-root product.

The deleted numerator and Corollary 10.6 quotient are now formalized.
The numerator converges uniformly over compact spectral sets and bounded
`ℓᵖ` families and is jointly entire across its omitted root. The literal
finite quotient factors converge to a jointly analytic function on the
moving-gap complement over one common connected source domain. Next
work through Lemma 10.7: assemble the full canonical-root product and
its analytic and boundary behavior.

The canonical root now has its full normalized product, pointwise
convergence of the literal cutoffs, arbitrary-index factorization,
and the identity `root² = Δ²−4` off the gaps. Its spectral and joint
analyticity clauses are proved, as is analytic extension through a
collapsed gap using the omitted product. Finish Lemma 10.7 by proving
the opposite boundary values on the two sides of each noncollapsed gap,
then continue to the asymptotics of Lemma 10.8.

`SourceCanonicalRootGapSides.lean` multiplies the established standard-root
side limits by the omitted product, which is continuous at points on the
selected gap. `SourceCanonicalRootGapIsolation.lean` uses the global
isolating discs to put every point of one gap outside all other gaps and
combines the analytic, collapsed-gap, and opposite-side clauses on one
connected source neighborhood. Lemma 10.7 is complete in this source
model. Next formalize Lemma 10.8's canonical-root asymptotics.

`SourceSingleRootAsymptoticFactors.lean` begins Lemma 10.8. It factors
the literal finite quotient exactly into midpoint and gap-correction
products, proves the inverse square-root perturbation bound on the
half-unit ball, and bounds the correction product's error by the
exponential of the sum of radicand norms. Next prove the uniform
isolating-disc separation and powered Young estimate for that sum,
then the midpoint quotient asymptotics and infinite-product limit.

`SquaredReciprocalRows.lean` proves the reciprocal-square kernel belongs
to every `ℓᵗ` above one half and applies powered Young with
`t = min(1,p/2)`. `SourceSquaredGapReciprocalRows.lean` instantiates this
for the canonical source gaps: every physical off-diagonal row converges
and its row-sum sequence lies in `ℓ^(p/2)`, including `1 < p < 2`.
Next transfer this row bound to the radicand on each isolating disc,
then estimate the midpoint quotient and pass to infinite products.

`SourceMidpointDiscSeparation.lean` now establishes a common local
midpoint-distance constant across central, mixed, and tail indices.
It transfers that geometry and the physical reciprocal-square row
summability to a uniform bound for every finite off-diagonal radicand
sum on each isolating disc. Next control the midpoint quotient, then
combine it with the gap correction and pass to the product limit.

`SourceSingleRootMidpointBounds.lean` pairs the root-minus-midpoint
displacement with the punctured reciprocal lattice. It bounds all
finite midpoint products uniformly over the isolating discs and joins
this with the squared-gap row estimate into a finite full-quotient
bound whenever that row is small. Next derive eventual row smallness
from its `ℓ^(p/2)` membership, control the first-order midpoint term
in `ℓᑫ` across omitted indices, and pass to the infinite product.

`FiniteExponentTail.lean` extracts two-sided coordinate decay from any
finite positive `ℓʳ` exponent. `SourceSquaredGapRowTails.lean` applies
this to the physical reciprocal-square rows, and
`SourceSingleRootAsymptoticTailBounds.lean` removes the finite
product's small-radicand assumption on all sufficiently remote discs
for each fixed source. Next make that row threshold uniform on a source
neighborhood, obtain the first-order `ℓᑫ` omitted-index estimate, and
pass to the infinite product.

`UniformWeightedRows.lean` shows that a summable nonnegative kernel has
uniformly vanishing translated rows for families with uniformly small
tails. `SourceSquaredGapUniformRowTails.lean` applies this to the actual
source gaps and produces a common half-unit threshold.
`SourceSingleRootUniformAsymptoticTailBounds.lean` combines it with
midpoint separation on a connected neighborhood, giving the finite
full-quotient estimate with one threshold for all nearby sources.
Next prove the first-order `ℓᑫ` omitted-index estimate and pass to the
infinite product.

`SeparatedReciprocalRows.lean` proves that changing a linearly separated
reciprocal denominator by a bounded midpoint displacement gains a
reciprocal-square factor. The resulting correction rows are absolutely
summable and form an `ℓᑫ` sequence for every Banach exponent, with a
square-kernel norm bound. `SourceMidpointHilbertCorrection.lean`
instantiates this for the physical periodic midpoints on distant source
discs and supplies one connected neighborhood with uniform separation
and midpoint-displacement bounds. Next identify the free-lattice term
with the sampled Hilbert transform to complete the signed first-order
`ℓᑫ` estimate for `1 < q < ∞`, then pass to infinite products.

`FreeLatticeSampledRows.lean` now identifies every selected free-lattice
reciprocal row with the sampled discrete Hilbert transform. Together
with the square-kernel correction, `PhysicalMidpointHilbertRows.lean`
proves absolute convergence of each physical row and an `ℓᑫ` norm
bound for the signed sums when `1 < q < ∞`.
`SourceMidpointHilbertCorrection.lean` specializes this to all distant
source discs, uniformly over nearby potentials and every selection of
one spectral point per disc. Next turn this selection-uniform bound into
the `ℓᑫ` sequence of disc suprema required by Lemma 10.8, handle the
`q=1` endpoint where needed, and pass to the infinite-product estimate.

`UniformSelectionSup.lean` now upgrades any norm bound valid for every
independent coordinate selection to an `ℓᑫ` bound for the least
coordinatewise supremum majorant. `SourceMidpointHilbertDiscSup.lean`
applies this to the signed midpoint sum on every distant isolating disc.
It proves the required supremum sequence lies in `ℓᑫ` for
`1 < q < ∞`, locally uniformly near a real-type source. For `q=1`,
the same supremum lies in every finite `ℓʳ` with `r>1`, giving the
`ℓ^{1+}` endpoint. Next use these first-order bounds in the
infinite-product estimate of Lemma 10.8.

`SourceSingleRootQuotientTailLimit.lean` now places each sufficiently
distant assigned disc in the moving-gap complement by comparing two
local isolating-disc families. The literal finite quotient products
therefore converge on those discs to the analytic quotient of
Corollary 10.6, and their neighborhood-uniform finite bound passes to
that infinite quotient. Next retain the signed first-order sum when
estimating the midpoint product, control its quadratic remainder in a
sequence space, and combine it with the squared-gap correction to get
the full `ℓᑫ + ℓ^(p/2) + ℓ^{1+}` asymptotic of Lemma 10.8.

`PhysicalMidpointProductRemainder.lean` now puts the absolute physical
midpoint row in the doubled exponent using reciprocal-kernel Young
convolution, then applies the quadratic product theorem to return the
nonlinear remainder to the original exponent. The source specialization
and `SourceMidpointProductDiscSup.lean` control the supremum of the
exact infinite midpoint product minus its signed linear sum in `ℓᑫ`,
including `q=1`, with a bound quadratic in the numerator displacement.
Next combine this remainder with the signed disc-supremum term, identify
the midpoint product with the quotient factor, and add the squared-gap
correction to complete the sequence estimate.

`SourceMidpointProductFullDiscSup.lean` now combines the signed row and
quadratic remainder before taking coordinatewise disc suprema. The full
infinite midpoint product minus one has a locally uniform `ℓᑫ` bound
when `1 < q < ∞`; an `ℓ¹` numerator gives every finite exponent above
one, matching the `ℓ^{1+}` endpoint. Next identify this product with
the literal midpoint cutoff limit, then compare the latter with the
infinite single-root quotient using the squared-gap row.

`SourceMidpointProductCutoffLimit.lean` now proves that each literal
symmetric finite midpoint quotient converges to the unconditional
midpoint product used above. The proof checks absolute summability from
disc separation and identifies every finite factor exactly with its
off-diagonal perturbation. Next pass the finite quotient-minus-midpoint
estimate to the two infinite limits and extract its `ℓ^(p/2)` disc row.

`SourceSingleRootGapCorrectionLimit.lean` now passes the finite
quotient-minus-midpoint estimate to the actual analytic quotient and
the infinite midpoint product. `SourceSingleRootGapCorrectionDiscSup.lean`
uses the physical reciprocal-square row to give a uniform-in-disc-point
`ℓ^(p/2)` majorant for their difference on one connected source
neighborhood, also when `1 < p < 2`. Next intersect this neighborhood
with the midpoint-product disc bound and state the full first
asymptotic of Lemma 10.8, including the `q=1` endpoint.

`SourceSquaredGapNorm.lean` now bounds the squared-gap half-exponent
norm by the square of the unsquared-gap norm and extracts a common
local source bound. `SourceSingleRootQuotientAsymptoticDiscSup.lean`
combines the midpoint and gap rows for the actual analytic quotient on
one connected source neighborhood: its distant-disc error is
`ℓᑫ + ℓ^(p/2)` for `1 < q < ∞`, and `ℓʳ + ℓ^(p/2)` for every finite
`r > 1` when `q=1`, with common local constants and threshold. This
formalizes the first assertion of Lemma 10.8 near real-type base
sources. Next derive its stated sine-product consequence from the
appropriate free-product identity.

`SourceDeletedFreeSine.lean` now identifies the free deleted numerator
with the filled sine quotient at every complex spectral point,
including the removed free root. `SourceFreeSineQuotientAsymptotic.lean`
specializes the quotient asymptotic to the free numerator: near a
real-type base source, the filled sine quotient divided by the
omitted standard-root product has locally uniform
`ℓᵖ + ℓ^(p/2)` disc majorants. This proves the corresponding
sine-product consequence in the source setting. Next compare the
remaining Chapter 2 statements with this local formulation and
continue through the subsequent lemmas.

For Lemma 10.10, `SourceCriticalMidpointGapSquaredTail.lean` now
transfers the existing canonical Lemma 8.6 estimate to source
coordinates. On a common open source neighborhood, the critical-root
offset equals the squared periodic gap times a uniformly bounded
`ℓᵖ` sequence at every sufficiently distant signed index. It also
shows that a collapsed distant gap has its critical root exactly at
its midpoint, even for complex source potentials. The remaining
Lemma 10.10 work is the uniform squared-gap bound at the finitely
many central indices.

`CriticalOffsetCoefficientOpenGap.lean` now handles the algebraic
nonvanishing issue at every open real gap, including central indices.
The critical point lies in the gap interior, where the discriminant
has modulus greater than two; hence the deleted periodic product is
nonzero. The quadratic critical identity then makes the coefficient
nonzero and gives the exact squared-gap offset formula. To finish
Lemma 10.10, establish the corresponding local bound across collapsed
central gaps and control the finitely many coefficients uniformly on
a source neighborhood.

`CriticalOffsetCoefficientCollapsedGap.lean` now proves that a
collapsed canonical pair at any real-type potential has exactly two
spectral occurrences, including in the central block. Analytic
orders then show that deleting this pair leaves a nonzero product at
the common endpoint. Together with the open-gap result, this makes
the midpoint coefficient nonzero and gives the exact squared-gap
critical-root formula at every index of each real-type potential.
The remaining Lemma 10.10 step is to extend that formula and its
uniform `ℓᵖ` coefficient bound to a complex source neighborhood.

`SourceDeletedPairOmittedSquare.lean` now identifies the deleted
periodic-pair product with the square of the corresponding omitted
standard-root product, first for literal cutoffs and then for their
entire limits. On any common isolating-disc family, the deleted
periodic product is nonzero throughout the selected disc, even along
the selected gap and at its endpoints. This supplies the nonvanishing
input for extending the central critical-offset argument to nearby
complex sources.

`SourceCriticalOffsetCoefficientNonzero.lean` now combines the
nonzero deleted product with indexed cluster separation. A collapsed
complex periodic pair has its canonical critical root at the common
endpoint. Thus the midpoint coefficient is nonzero and the exact
squared-gap critical-offset identity holds at every signed index on
the connected almost-real source domain. The remaining quantitative
Lemma 10.10 task is a common local `ℓᵖ` norm bound for the quotient
coefficients, especially at the finitely many central indices.

`JointSpectralDerivative.lean` proves a general regularity lemma:
the spectral derivative of a jointly analytic complex Banach-space
family is jointly continuous. `SourceDeletedPairJointAnalytic.lean`
applies the omitted-product square identity to make the deleted
periodic-pair product jointly analytic, with jointly continuous
spectral derivative, on the open moving-gap complement. The central
quotient's numerator now has the needed local continuity; next
combine this with critical-root and midpoint continuity to bound
finitely many central coefficients on one source neighborhood.
