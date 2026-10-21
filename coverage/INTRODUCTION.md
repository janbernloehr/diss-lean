# Introduction: the three main theorems and their qualifications

This audit covers the three main results, their analytic setup on printed
pp. 10–13, and the method-of-proof outline on pp. 13–15. The main-results
interfaces below are implemented. The wider introductory background on
pp. 9–10 remains a separate audit, apart from the original spectral
conservation, action integrals, oscillators, almost-periodicity, critical
Sobolev inclusion, complete critical homogeneous space, dilation, and full
distributional Galilean results documented below. This document does not
certify the entire introduction or dissertation. The precise 2014 edition comparison
and the G.2 norm qualification also remain open.

## Physical Hamiltonian, normal form and Fourier normalization, printed pp. 9–11

[ClassicalNLSHamiltonians.lean](../NLS/ZakharovShabat/ClassicalNLSHamiltonians.lean)
identifies the original pair Hamiltonian with the integral of a'*b'+a^2*b^2.
[ClassicalNLSEnergyVariation.lean](../NLS/ZakharovShabat/ClassicalNLSEnergyVariation.lean)
proves its actual first variations.
[ClassicalNLSSobolevEnergy.lean](../NLS/ZakharovShabat/ClassicalNLSSobolevEnergy.lean)
identifies the scalar energy with the physical unit-interval integral
of |u'|^2+|u|^4, and
[ClassicalNLSVectorField.lean](../NLS/ZakharovShabat/ClassicalNLSVectorField.lean)
gives the scalar NLS vector field with its original signs.

[SourceSection17Original.lean](../NLS/ZakharovShabat/SourceSection17Original.lean)
constructs the original global analytic Birkhoff inverse for 1<p<=2.
[SourceWeightedActionHamiltonianDerivative.lean](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianDerivative.lean)
keeps the full action Hamiltonian on its original weighted domain;
its coordinate derivative is F(a)_n+4*mass(a)+(2*pi*n)^2.
The physical Hilbert map and inverse are globally real analytic and
preserve the pair norm, as proved in
[PhysicalBirkhoffIntrinsicProperties.lean](../NLS/ZakharovShabat/PhysicalBirkhoffIntrinsicProperties.lean).

The bounded physical derivative at zero is identified in
[PhysicalBirkhoffLinearization.lean](../NLS/ZakharovShabat/PhysicalBirkhoffLinearization.lean).
Its Fourier integral formulas retain the index reflection, signs,
square-root-two normalization and imaginary factor documented below.

[ScalarNonlinearParseval.lean](../NLS/ZakharovShabat/ScalarNonlinearParseval.lean)
makes the scalar normalization explicit. The original input is exactly
the physical pair (u, conjugate u), whose squared norm is 2*norm(u)^2.
For the intrinsic real Birkhoff coordinates (x,y), the normalized complex
coefficient z_n=(x_n-i*y_n)/sqrt(2) has norm(z)=norm(u).
The sum of |z_n|^2 converges to norm(u)^2. Thus scalar nonlinear Parseval
holds with the exact physical convention. The raw rectangular pair
continues to use the physical pair norm.

## Original spectral conservation and oscillators, printed p. 9

[`SourceOriginalSpectralConservation.lean`](../NLS/ZakharovShabat/SourceOriginalSpectralConservation.lean)
proves that every original global ordinary or renormalized solution preserves
each original action for 1<p<=2. Equal actions imply membership in the actual
original isospectral set, retaining the periodic spectrum and its algebraic
multiplicities. The normalized entire discriminant itself is conserved.
These theorems construct the original solution data internally and use the
existing all-smooth-approximation solution definition and its uniqueness.

[`SourceOriginalActionIntegrals.lean`](../NLS/ZakharovShabat/SourceOriginalActionIntegrals.lean)
constructs a one-mode original source to separate each action from all
others. Thus the original real action functions are linearly independent.
The same functions are conserved along every original global solution,
and their actual regular cotangents commute under the physical Poisson
pairing. The following differential-independence result gives the precise
condition on the original source gaps.

[`RectangularHamiltonianOscillators.lean`](../NLS/Dynamics/RectangularHamiltonianOscillators.lean)
proves literal coordinate derivatives for the decoded Hamiltonian phase
flow: x_n'=-omega_n*y_n and y_n'=omega_n*x_n. It allows arbitrary real
frequency sequences, without a bounded-frequency or finite-gap hypothesis.
[`SourceOriginalOscillators.lean`](../NLS/ZakharovShabat/SourceOriginalOscillators.lean)
identifies every original solution with that same real Birkhoff trajectory
and proves those equations for its actual coordinates at every time.
The retained original ordinary or renormalized frequency sequence is
constant along the solution. These are coordinatewise derivatives;
time differentiability in the full sequence norm is not asserted.

## Independence of the actual action differentials, printed p. 9

[SourceActionDifferentialIndependence.lean](../NLS/ZakharovShabat/SourceActionDifferentialIndependence.lean)
uses the original angle/action canonical pairing to separate a finite
linear combination of the actual complex action differentials. At every
real source, the differentials indexed by its open gaps are linearly
independent over C. The result also holds for the original indexed contour
actions, using their proved local germ agreement.

[SourceRealActionDifferentialIndependence.lean](../NLS/ZakharovShabat/SourceRealActionDifferentialIndependence.lean)
identifies each real action derivative with the real restriction of the
complex derivative. The real/imaginary source decomposition transfers
independence to the actual real action differentials on the open gaps.

At a closed gap the nonnegative real action attains zero, so its
differential vanishes. Conversely, the open-gap independence theorem
excludes a zero differential. Thus vanishing is equivalent to gap
collapse, and independence of the entire real differential family is
equivalent to every gap being open.

These statements hold for every finite p>1, retaining the same original
source norm and actions. The separate global-solution conservation result
above has the range 1<p<=2. No differential independence at closed gaps
is asserted.

## Almost periodicity, printed p. 9

The original ordinary and renormalized global solutions are Bohr almost
periodic in the full source norm for 1<p<=2. For each epsilon>0 there is
L>0 such that every interval [a,a+L] contains a shift tau satisfying
norm(gamma(t+tau)-gamma(t))<epsilon for every real t. This includes the
Hilbert endpoint and does not merely assert compact orbit closure or
coordinatewise recurrence. Periodic and quasiperiodic orbits also satisfy
this recurrence conclusion; no disjoint classification is asserted.

[`BohrAlmostPeriodic.lean`](../NLS/Dynamics/BohrAlmostPeriodic.lean)
proves the general finite-net argument for continuous isometric orbits
with totally bounded range, and transport through a continuous map on a
compact containing set.
[`PhaseAlmostPeriodic.lean`](../NLS/Dynamics/PhaseAlmostPeriodic.lean)
supplies a compact coefficient majorant box, common return times for
both Birkhoff components, and arbitrary unbounded real frequencies at
every finite sequence exponent. It covers the Hamiltonian signs (-,+).

[`SourceFlowAlmostPeriodic.lean`](../NLS/ZakharovShabat/SourceFlowAlmostPeriodic.lean)
transfers recurrence through the actual global Birkhoff inverse.
[`SourceOriginalAlmostPeriodic.lean`](../NLS/ZakharovShabat/SourceOriginalAlmostPeriodic.lean)
constructs both original solution curves and proves recurrence for every
global solution in the existing all-smooth-approximation definition.
The main entry points are `exists_original_almostPeriodic_solutions`,
`bohrAlmostPeriodic_of_isOrdinaryNLSSolutionOn_univ`, and
`bohrAlmostPeriodic_of_isRenormalizedNLSSolutionOn_univ`.

The stronger result uses the same original solution at every nonnegative
real Sobolev order. [Weighted sequence recurrence](../NLS/SequenceSpaces/WeightedPhaseAlmostPeriodic.lean)
holds for arbitrary positive weights. [Weighted real phase rotation](../NLS/Dynamics/WeightedRealPhaseFlow.lean)
uses the actual lp pair norm and commutes exactly with forgetting weights.
[The native Sobolev lift](../NLS/ZakharovShabat/SourceSobolevPhaseFlow.lean)
uses the original global weighted Birkhoff inverse, retains the initial
weighted source, and recovers the unweighted source phase curve exactly.

[`SourceSobolevAlmostPeriodic.lean`](../NLS/ZakharovShabat/SourceSobolevAlmostPeriodic.lean)
constructs both original global solution representatives in the stronger
norm. Its two `exists_sobolev_almostPeriodic_lift_of_is...SolutionOn_univ`
theorems identify the same stronger representative for any original
global ordinary or renormalized solution. The exact source-frequency
identity `sourceFrequencyWeight_sobolev` gives the weight (1+|n|)^s,
without an unmentioned doubling factor. Both the native norm and all raw
coefficients are retained.

These results cover 1<p<=2 and every nonnegative real regularity. They do
not assert global solutions above p=2 or phase norm continuity at p=infinity.

## Critical Sobolev inclusion, printed p. 10

For each finite real p>2 and every positive period L, the original FL^p
space embeds continuously and injectively into H^(-1/2).
[`CriticalSobolevInclusion.lean`](../NLS/SequenceSpaces/CriticalSobolevInclusion.lean)
constructs the coefficient-preserving bounded linear map. The exact Holder
exponent r=(1/2-1/p)^(-1) satisfies r>2, so the negative-half multiplier
(1+|n|)^(-1/2) has the strict summability needed by Holder's inequality.

[`PeriodicCriticalSobolevInclusion.lean`](../NLS/Fourier/PeriodicCriticalSobolevInclusion.lean)
transfers this map through the original coefficient isometries. Its
`criticalSobolevInclusion_val` theorem identifies the output with the
same original periodic distribution, and `criticalSobolevInclusion_injective`
proves injectivity. The target is the existing original
`FourierLebesgueSpace L (-1/2) 2`, with its normalized coefficient norm.
The statement makes no infinity input claim and does not equate that
norm with an unnormalized physical interval norm.

The subsequent full-line dilation and Galilean statements are separate
background claims. Dilation is covered in the next section in its stated
energy scope; the full distributional Galilean result follows it.

## Full-line dilation and critical homogeneous energy, printed p. 10

[`ScalarNLSScaling.lean`](../NLS/ZakharovShabat/ScalarNLSScaling.lean)
proves covariance of the actual scalar field under c*f(c*x), including
its second derivative and cubic nonlinearity. The theorem
`hasDerivAt_scalarNLS_dilation` preserves the physical time-derivative
equation under c*u(c^2*t,c*x). Smooth spatial slices remain smooth.

[`HomogeneousNLSScaling.lean`](../NLS/Fourier/HomogeneousNLSScaling.lean)
retains the full-line Jacobian and proves the actual Fourier formula
F_c(xi)=F(xi/c) for c>0. Its `homogeneousSpectralEnergy` is the extended
nonnegative integral of |xi|^(2s)*|F(xi)|^2. The exact factor is c^(2s+1),
so `homogeneousCriticalEnergy_scalarNLS_dilation` gives equality at s=-1/2,
including preservation of finite energy and of infinite values.

The physical-profile energy uses the actual Fourier integral. The next
section supplies a complete distributional realization and its converse
Fourier-density characterization. The usual inhomogeneous Sobolev norm
has a different scaling formula; the exact invariance here is homogeneous.

## Original distributions beyond L2, printed p. 10

[PeriodicFourierLebesgueStrictness.lean](../NLS/Fourier/PeriodicFourierLebesgueStrictness.lean)
proves that an actual integrable circle function induces a distribution
of order zero. Using the exact FL2=L2 isometry and its representative
identity, this also holds for every original FL2 distribution.

The existing nonmeasure counterexample has nonzero distributional order.
It belongs to every FLp with p>2, including infinity, but cannot belong
to FL2. The theorem supplies this same original distribution simultaneously
for all exponents, for every positive period. This proves actual strictness
beyond L2, rather than only failure of a coefficient norm estimate.

## The complete critical homogeneous space, printed p. 10

[`LineTemperedNLSScaling.lean`](../NLS/Fourier/LineTemperedNLSScaling.lean)
constructs the actual physical action c*T(c*x) on tempered distributions
for c>0, with the inverse Jacobian retained. Its actual Fourier transform
is the inverse frequency dilation, and reciprocal scaling recovers T.

[`CriticalFrequencyMeasure.lean`](../NLS/Fourier/CriticalFrequencyMeasure.lean)
proves local finiteness, temperate growth, and the exact quadratic dilation
Jacobian for the measure |xi| dxi.
[`CriticalHomogeneousSobolev.lean`](../NLS/Fourier/CriticalHomogeneousSobolev.lean)
uses L2 of this measure as a complete normed model. The actual inverse
Fourier transform embeds it continuously and injectively into tempered
distributions. Its Fourier density is |xi|*f(xi), and its norm squared is
exactly the integral of |xi|^(-1)*|F(xi)|^2. The physical NLS dilation is a
surjective complex linear isometry of this same space; the distributional
identity and exact norm are both retained.

[`CriticalHomogeneousCharacterization.lean`](../NLS/Fourier/CriticalHomogeneousCharacterization.lean)
proves the converse: every measurable Fourier density of finite critical
energy has a unique representative in the model, with exactly matching
norm. `isCriticalHomogeneousSobolev_iff_fourier_density` characterizes the
original tempered distribution by its actual Fourier transform acting on
Schwartz tests. Thus the complete realization agrees with the finite-energy
Fourier-density definition. This does not assert a separate completion
construction from a selected smooth core.

## Galilean symmetry on the full line, printed p. 10

[`ScalarNLSGalilean.lean`](../NLS/ZakharovShabat/ScalarNLSGalilean.lean)
proves the literal source boost exp(i*(nu*x-nu^2*t))*u(t,x-2*nu*t)
preserves the actual scalar NLS equation. The proof uses joint classical
differentiability and differentiability of the first spatial derivative.
It retains the original cubic, moving-frame chain rule, and second
derivative. This PDE theorem has classical regularity assumptions.

[`LineGalileanFourier.lean`](../NLS/Fourier/LineGalileanFourier.lean)
proves the function formula with the exact Fourier normalization:
F_boost(xi)=exp(i*(nu^2*t-4*pi*nu*t*xi))*F(xi-nu/(2*pi)).
[`LineAngularSchwartz.lean`](../NLS/Fourier/LineAngularSchwartz.lean)
constructs the actual Schwartz modulation and translation operators.
[`LineTemperedGalilean.lean`](../NLS/Fourier/LineTemperedGalilean.lean)
then proves covariance of the actual Fourier transform on all tempered
distributions, using physical translation and smooth distribution
multiplication. The opposite boost is the inverse.

[`LineFourierLebesgueGalilean.lean`](../NLS/Fourier/LineFourierLebesgueGalilean.lean)
defines membership by the original distribution's actual Fourier
transform having an Lp representative. For every p>=1, including infinity,
`isLineFourierLebesgue_galilean_iff` preserves membership in both directions.
`exists_lineFourierLebesgue_galilean_representative` retains the exact norm
of that unique representative. No physical-space integrability assumption
is imposed. Public examples include a boosted Dirac mass in FL-infinity
and its exact action on a Schwartz test.

## Theorem 0.1 and the original Sobolev norms

[`SourceSection23Sobolev.lean`](../NLS/ZakharovShabat/SourceSection23Sobolev.lean)
proves `SourceSection17OriginalData.section23_sobolev_bounds`. For any
retained original Hilbert Birkhoff family and any integer m >= 1 it gives
positive c and d before choosing the potential. `SourceSection23SobolevBounds`
contains both Birkhoff estimates and both original indexed-action estimates.
The upper remainder has exponent 2m and the lower remainder exponent 4m−3.
The highest-order norm occurs linearly; the remainder uses only orders one
and zero. The source coordinates carry the physical weights 1+|2 pi n|,
and the target uses the sum of its two component energies.

[`SourceSection23Original.lean`](../NLS/ZakharovShabat/SourceSection23Original.lean)
constructs one original family before all integer orders and weights.
`SourceSection23Data.sobolev` retains those estimates together with the
preceding original primitive, frequency, and solution results.

The opening Hilbert and Sobolev geometry is supplied by the
[Section 14 audit](SECTION_14.md). The exact physical canonical brackets are
in [`PhysicalBirkhoffCanonical.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffCanonical.lean).
`intrinsicPhysicalBirkhoffMap_fderiv_zero_coordinates` in
[`PhysicalBirkhoffLinearization.lean`](../NLS/ZakharovShabat/PhysicalBirkhoffLinearization.lean)
gives the actual Fourier integral formulas, including index reflection and
the square-root-two and imaginary factors. The inverse derivative is the
inverse of that same Fourier operator. Exact nonlinear Parseval follows
from `SourceSection17OriginalData.section23_parseval` in
[`SourceSection23Actions.lean`](../NLS/ZakharovShabat/SourceSection23Actions.lean).
Global native real Sobolev analyticity in both directions is proved in
[`SourceBirkhoffSobolevGlobalInverse.lean`](../NLS/ZakharovShabat/SourceBirkhoffSobolevGlobalInverse.lean).

The comparison with the inspected 2013 external construction has precise
physical identifications. Agreement with the exact 2014 cited edition
remains unverified; the introduction audit does not remove that qualification.

## Theorem 0.2 and the retained Hamiltonian

[`SourceHamiltonianOriginal.lean`](../NLS/ZakharovShabat/SourceHamiltonianOriginal.lean)
constructs `SourceOriginalHamiltonianData D T F H`. The same H is analytic
on an open connected complex ell^2 domain T containing every nonnegative
summable action and every real source action from the original FL^4 family.
It has nonpositive real values on the nonnegative part of T and vanishes
there exactly at zero. Its physical identity holds at every real H1 source:
H* equals physical H minus twice squared mass minus the weighted linear
action sum. That series is absolutely summable.

`Q.gradient_eq` identifies the retained frequency F with the gradient of H
throughout T. `Q.hessian_zero` is minus twice the unconjugated Hilbert
pairing. `Q.concavity` supplies one positive-radius ball in T on which the
real Hessian is bounded above by minus the squared ell^2 norm in every real
direction. This proves the quantitative local concavity in Theorem 0.2.

`Q.real_summable_extension` and `Q.positive_domain` in
[`SourceOriginalActionDomains.lean`](../NLS/ZakharovShabat/SourceOriginalActionDomains.lean)
retain the same real summable-action values and the relatively open dense
positive part of T. `E.positive_domain` gives the corresponding result for
each retained finite-exponent frequency domain.

Restriction through the bounded ell^1-to-ell^2 inclusion gives the
summable-action assertion. The positive-domain density argument uses
`Coeff.isOpen_dense_nonnegative_domain` from
[`NonnegativeActionDensity.lean`](../NLS/SequenceSpaces/NonnegativeActionDensity.lean).
Its openness is relative to the nonnegative cone. The finite-exponent
hypothesis holds at exponent two. Neither an extension to all nonnegative
ell^2 actions nor global concavity is asserted.

The consequence following Theorem 0.2 is proved in the stronger form of
failure of continuity at zero relative to the nonnegative ell^q cone,
for every q>2 including infinity. `Q.no_continuous_extension_all` in
[`SourceHamiltonianOriginalNonextensionTop.lean`](../NLS/ZakharovShabat/SourceHamiltonianOriginalNonextensionTop.lean)
retains this same H, its physical identity, and its frequency data.

## Theorem 0.3 and a single common frequency

`sourceSection18_original_frequencies` in
[`SourceFrequencyOriginalHilbert.lean`](../NLS/ZakharovShabat/SourceFrequencyOriginalHilbert.lean)
constructs one original common frequency on summable actions. Every original
higher-exponent family agrees with it on the full nonnegative summable cone.
`SourceOriginalHilbertFrequencyData.realizations_all` in
[`SourceFrequencyOriginalHilbertTop.lean`](../NLS/ZakharovShabat/SourceFrequencyOriginalHilbertTop.lean)
provides complex and real analytic realizations into every ell^r with r>1,
including infinity, using the same domain and the same coordinates.

For each finite p>2, `SourceOriginalFrequencyData` in
[`SourceFrequencyOriginalAsymptotic.lean`](../NLS/ZakharovShabat/SourceFrequencyOriginalAsymptotic.lean)
retains one analytic extension F on an open connected ell^(p/2) domain U.
The domain contains zero and the entire nonnegative summable cone.
`E.refined` realizes F(I)+2I analytically in every finite ell^r satisfying
r>1 and r>=p/3. Thus for 2<p<=3 it supplies every finite r>1, and for p>3
one may take r=p/3. The bounded inclusion into ell-infinity gives the
remaining target endpoint. `E.mixed` additionally retains one literal
decomposition in ell^(p/3)+ell^(1+) on one neighborhood with uniform bounds
chosen before the ell^(1+) projection exponent. For 2<p<3 the p/3 term
remains a quasi-normed sequence space; no Banach structure is assumed.

[`SourceFrequencyOriginalInverse.lean`](../NLS/ZakharovShabat/SourceFrequencyOriginalInverse.lean)
proves dF(0)=−2Id, both local inverse identities, inverse derivative −Id/2,
and an open dense set of actual analytic local inverses for the same F.
It also supplies a real-valued analytic realization. Relative density of
U in its nonnegative cone follows from the same finite-exponent density
theorem, now at exponent p/2. Infinity here is only a frequency target;
no extension on all bounded action inputs is claimed.

## The mass term and the renormalized flow

The unnumbered p. 12 assertion about H1=sum I has a direct obstruction.
`Coeff.not_continuousWithinAt_mass_extension` in
[`ActionMassNonextension.lean`](../NLS/SequenceSpaces/ActionMassNonextension.lean)
proves that no extension is continuous at zero relative to the positive
ell^q cone for any q>1, including infinity. Agreement is needed only on
summable nonnegative actions in a neighborhood of zero. The finite
counterexample sequences all have total action exactly one, while their
ell^q norms tend to zero.

[`RealActionMassNonextension.lean`](../NLS/SequenceSpaces/RealActionMassNonextension.lean)
proves the corresponding assertion directly on the real action space.
This threshold is q>1 for mass; the separate H* obstruction uses q>2.

The physical equations of motion and the corrected renormalized flow are
audited in [Section 22](SECTION_22.md). The original solution definition
uses every convergent smooth initial-data approximation, with constructed
classical solutions. The original higher-exponent nonextension result
is stronger than the introductory motivation: it applies at every source
outside L2 in the stated finite-exponent range. This does not identify
an arbitrary coordinate flow with a physical solution.

## Normalization corrections

The introduction's printed full-Hamiltonian Hessian −2 delta(n,m) omits
the contribution of twice squared mass. The correct full frequency
derivative is 4−2 delta(n,m). The original-family theorem
`Q.restored_frequency_derivative` and the actual-source diagonal
counterexample `Q.full_hessian_ne_printed` are in
[`SourceSection18HamiltonianCorrection.lean`](../NLS/ZakharovShabat/SourceSection18HamiltonianCorrection.lean).
The displayed Hessian is correct for H*, whose weighted linear and mass
terms have both been subtracted.

The gauge following (0.4) must be exp(4 i mass t), with mass the squared
L2 norm. `SmoothNLSData.renormalized_phase` proves that phase for the
constructed smooth solutions. `original_gauge_printed_phase_counterexample`
uses a genuine smooth constant initial datum of mass one to refute the
printed exp(i t) phase directly in the renormalized PDE. Both are in
[`SourceSection18GaugeCorrection.lean`](../NLS/ZakharovShabat/SourceSection18GaugeCorrection.lean).

## Full energy in the introductory weighted topology

The full energy on standard ell^(2,1) actions is defined in
[`SourceStandardActionHamiltonian.lean`](../NLS/ZakharovShabat/SourceStandardActionHamiltonian.lean).
Its complex analytic domain is the inverse image of the same original T,
and contains every nonnegative weighted action. The named real restriction
is analytic on the corresponding real domain and has the exact complex
energy there on the entire nonnegative cone.

The standard weight is (1+|n|)^2. The physical construction first uses
(1+2 pi |n|)^2; `sourceEnergyActionsStandardEquiv` in
[`SourceWeightedActionHamiltonianNorm.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianNorm.lean)
preserves every coordinate and proves
norm_standard <= norm_physical <= (2 pi)^2 norm_standard.
The norms are not equated.

The restored expression is H*(I) + 2(sum I)^2 + sum (2 pi n)^2 I_n.
Both sums converge absolutely. Every original real H1 source has an
actual weighted action sequence, its action sum equals physical mass,
and its full action energy equals the actual physical energy. These
identifications are in
[`SourceWeightedActionHamiltonianPhysical.lean`](../NLS/ZakharovShabat/SourceWeightedActionHamiltonianPhysical.lean).
The literal coordinate derivative is the retained frequency plus four
times mass plus (2 pi n)^2. It is proved throughout the original complex
domain in both weighted conventions. The physical H1 angle-energy bracket
is also proved in
[`SourceSection20SobolevEnergy.lean`](../NLS/ZakharovShabat/SourceSection20SobolevEnergy.lean).

## Method-of-proof outline, printed pp. 13–15

The two indexed-action estimates on p. 13 are fields of the same
`SourceSection23SobolevBounds` package as Theorem 0.1. The upper squared
remainder uses exponent 4m; the lower squared remainder uses 4m−3 with
the weighted action norm, retaining the original physical conventions.

The higher actions and their exact asymptotic statement are audited in
[Section 24](SECTION_24.md). Every real source has actual gap samples
whose powers give the higher actions, and the asymptotic runs along the
cofinite filter on the signed integer index. It includes collapsed gaps.
The trace is the full integer sum H_(2m+1)/4^m. The p. 14 display restricts
the sum to n>=1, repeating the index omission addressed by
`section23_positiveIndex_trace_counterexample` in
[`SourceSection23TraceCorrections.lean`](../NLS/ZakharovShabat/SourceSection23TraceCorrections.lean).

[Section 25](SECTION_25.md) supplies localization uniform on physical H1
balls, with the literal source norm, threshold, signed indices, and
original multiplicities. [Section 26](SECTION_26.md) connects these
estimates to the quantitative bounds in [Section 23](SECTION_23.md).
The introductory order-comparison symbols summarize these results;
they are not treated as additional uniform asymptotic theorems.

The cubic residue construction is audited in [Section 21](SECTION_21.md).
Its moments are analytic on one original complex neighborhood, bounded
locally by the fourth power of the gap at cubic order, and their sum
converges absolutely and locally uniformly. The coefficient is −4/3.
The p. 14 overview prints +4/3, repeating the sign error in (4.13).
`printed_lemma21_2_sign_counterexample` in
[`SourceSection21SignCorrections.lean`](../NLS/ZakharovShabat/SourceSection21SignCorrections.lean)
refutes that positive coefficient with an actual finite-gap source.
The action-domain conclusion retains the exact domain qualification in
[Section 18](SECTION_18.md), rather than asserting all nonnegative ell^2
actions lie in the original action image.

The second-moment frequency formula has coefficient −4/(2 pi), with
the raw contour normalization used in [Section 20](SECTION_20.md).
That audit supplies absolute and locally uniform convergence, actual
source recovery, exponent compatibility, and the mixed sequence
remainder used by Theorem 0.3.

The related-work comparisons and historical priority discussion are
bibliographic statements. This audit does not verify those external
literature claims or the exact cited 2014 edition. The cited one-smoothing
property itself is proved for the retained original map and its inverse
at every positive integer Sobolev order in [Section 23](SECTION_23.md).
