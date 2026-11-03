# Actual rough Hill energy roots, mapped periods and root chart agreement

Every main theorem remains OPEN. This milestone constructs an actual
analytic Hill energy-root branch and normalized smooth energy contours
near every physically real Hminus1 input. It proves independence of the
root on overlaps at real inputs and equality of the full joint
holomorphic root germs. It does not yet prove independence of the entire
numerators or their agreement with the earlier weighted normalized family.

## Positive original circles and the principal square root

`EvenPositivePeriodCircle.lean` uses the proved full endpoint reflection
to put zero in the actual central gap. Complete canonical order and the
original circle's separation from that gap force, for every positive
index, center-radius>0. Its entire closed disc lies in the right
half-plane. This holds for complex sources with even discriminant;
no real-type hypothesis is added to that geometry.

The actual principal square root therefore satisfies sqrt(z^2)=z on
every such closed disc. The branch point is outside these contours.

## A nonvanishing root of the actual rough Hill radicand

`HillHminusOneMiuraEnergyRoot.lean` defines, for an actual chart C,

    C.energyRoot(q,lambda)
      = sourceCanonicalRoot(C.criticalSource(q),sqrt(lambda+C.energyShift)).

Its domain requires lambda+C.energyShift in the slit plane and the
principal frequency in the actual NLS canonical-root domain. On the
actual chart it satisfies

    C.energyRoot(q,lambda)^2 = Delta_H(q,lambda)^2-4.

The discriminant is the independently glued rough Hill trace. The proof
uses the exact fixed Miura shift and the verified NLS product identity.
The root is nonzero on its domain. The verified original NLS Theorem12.1
supplies joint root analyticity: over one common rough-open V the entire
moving energy-root domain is open and the root is holomorphic jointly in
energy and the Hminus1 input. No square root or sign is assumed.

## Actual smooth energy contours and exact normalization

`ShiftedSquaredCircle.lean` constructs the actual smooth closed path
obtained by applying z->z^2-shift to the ordinary positively oriented
frequency circle. Its integral is the ordinary curve integral on that
mapped path. The chain rule proves the exact substitution with Jacobian
2z, without defining an energy integral by its desired period.

On a right-half-plane disc the mapped contour has winding integral one
about x^2-shift for every x in the disc. The proof splits the actual
reciprocal-pole pullback into (z-x)^(-1)+(z+x)^(-1); the second term has
zero period on the right half-plane. The winding uses its conventional
1/(2*pi*i) normalization, separately from the psi period's 1/(2*pi).

`HillHminusOneMappedEnergyPeriods.lean` proves that the mapped canonical
endpoint energies are actual zeros of Delta_H^2-4. The mapped energy
contour lies entirely in the actual energy-root domain and winds once
positively about the image of the selected gap, including both endpoint
energies. For the same previously constructed entire candidate Psi_n,

    integral_Gamma_m Psi_n(lambda,q)/C.energyRoot(q,lambda) d(lambda)
      = 2*pi*delta_mn,                 m,n>0.

`exists_hillHminus_real_normalized_mapped_energy_periods` constructs one
common complex Hminus1-open neighborhood before all numerator and circle
indices at every real rough base potential. It retains the actual
real-preserving Miura chart, fixed positive real energy shift, full
verified NLS psi data, joint entire-energy numerator analyticity, an open
joint analytic energy-root domain, nonempty simultaneous original circle
families, exact mapped-contour domain membership, winding one and all
normalization periods. Central and collapsed pairs remain included in
the underlying endpoint/root and normalization results.

## Root agreement fixes the sign from actual spectral data

`SourceHighShiftedRealBand.lean` proves that one sufficiently large cutoff
puts sqrt((pi*n+pi/2)^2+shift) on the real band following the actual nth
canonical pair, for every subsequent n and every fixed real shift. It
uses actual counted high endpoint pairs and the proved quantitative
principal-root shift bound. The band index is proved, not assumed.

`HillHminusOneEnergyRootChartAgreement.lean` compares two actual charts
at a common real input, with their real shifts and proved real-type
sources. Choose the same sufficiently high real energy for both charts.
The already verified canonical-root real-band sign fixes the same branch
at that point. Their squares equal the same independent Hill radicand,
so opposite signs are excluded by the strict actual band sign.

Both root domains contain every nonreal energy. Their common domain
contains the constructed real band point. The reusable
`NonrealConnectedDomain.lean` proves that such a domain is connected,
using the upper and lower half-planes with their real boundaries.
Analytic uniqueness gives agreement on the entire common energy domain:

    C.energyRoot(q,lambda) = E.energyRoot(q,lambda).

This proves `energyRoot_eq_on_real_input` without assuming any base root
agreement. For two actual source neighborhoods,
`energyRoot_germ_eq_on_real_input` then proves equality in a full complex
neighborhood of (lambda,q0). The proof uses the actual joint analytic
root domains, the proved base agreement and nonvanishing, and the common
radicand identity. This is joint holomorphic germ agreement, not merely
agreement on a real or fixed-energy slice.

The existing unchanged `SourceCanonicalRootRealBand.lean` and
`SourceCriticalRootRatioContourHomotopy.lean` are now directly recompiled
for the actual band normalization and real-source root-domain openness.

## Relation to the source and remaining obligations

These are actual chartwise normalized energy differentials and root
germs toward (52)-(53), PDF21, and the frequency extensions in Theorems1.2
and1.9, PDF4/6. Root chart agreement does not prove uniqueness or chart
agreement of the entire numerators. The latter still need their actual
growth/zero-product or critical-basis realization and agreement with the
earlier local rough weighted normalized family.

A single coherent entire normalized family on full W, lowest-cut
primitive and filled moment identifications, canonical product leading
scalar one, source root estimate(54), physical Hamiltonian frequency
identity(69), action descent, weighted target-space/asymptotic/compact
claims and actual Birkhoff/PDE identification remain open. No main
inventory row is closed by this milestone.

## Validation

Seven new proved modules and two newly selected unchanged dependencies
are checked. All 385 previously selected Lean sources remain byte-identical
and all seven shared provenance records remain valid. Checker and audit
orders now follow actual transitive selected imports, including the newly
selected existing dependencies before their earlier consumers. Counts
and full audit evidence are in `VALIDATION.md` and `source.json`.
Pinned Lean4.33.1/mathlibv4.33.1, default heartbeats, warnings as errors,
private fresh outputs, and the permitted propext/Classical.choice/Quot.sound
axioms are retained. Canonical main remains unchanged and read only.
