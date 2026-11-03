# Actual continued-root compatibility near zero

Every article main theorem remains OPEN. This milestone compares the
constructed canonical Miura energy root with the independently defined,
free-normalized rough Hill continuation root. The earlier normalized
moments and weighted frequency series use the latter root. Entire
numerator identification is still a separate open obligation.

## Nonreal spectral exclusion for every real rough input

`PeriodOneRealScaling.lean` proves that physical conjugate Fourier
reflection commutes with real scalar multiplication. In particular,
real radial source paths stay physically real, and zero is real.

For every physically real Hminus1 potential q, the actual real Miura
chart construction supplies C with q in its domain, a real energy shift,
and an actual real-type NLS source. Its canonical energy root is defined
and nonzero at every nonreal energy. Its square equals the independent
rough Hill radicand Delta_H(q,lambda)^2-4. Consequently,

    lambda.im != 0 => Delta_H(q,lambda)^2-4 != 0.

This is proved in `HillHminusOneRealSpectralExclusion.lean` as
`hillHminusRadicand_ne_zero_of_real_of_im_ne_zero`, without assuming an
abstract spectral reality certificate. It holds at every physically real
rough potential, not just near zero or at L2 inputs.

Apply this result to every real scaling r*q, 0<=r<=1. Every nonreal energy
is in the slit plane and its actual radicand stays nonzero along the full
radial source path. Hence `nonreal_mem_hillHminusContinuationDomain`
places (lambda,q) in the original free-normalized continuation domain
for every real rough q and every nonreal lambda.

## The actual free normalization

`HillHminusOneEnergyRootFreeAgreement.lean` first proves the unconditional
original base value in `hillHminusContinuedRoot_base_sine`

    hillHminusContinuedRoot(lambda,0) = -2*i*sin(sqrt(lambda)).

For any actual chart at zero having real shift and real-type source, a
sufficiently high real energy lambda=(pi*n+pi/2)^2 lies in its root domain
and in the old continuation domain. The high-band placement theorem is
applied both to the actual chart source with its shift and to the literal
zero NLS source with shift zero. Both canonical roots have the same strict
parity sign in the same actual indexed real band. The zero-source product
has the proved value -2*i*sin(z). Their squares are the same actual free
Hill radicand, so the opposite sign is excluded.

This fixes the sign without assuming that the chart's lift at zero is
constant, without assuming any root agreement, and without introducing a
fake chart of shift zero. Both energy domains contain every nonreal point
and the constructed common real band point. Their intersection is
preconnected. Actual analyticity and nonvanishing therefore extend the
agreement to the full common energy domain:
`HillHminusMiuraChart.energyRoot_eq_continuedRoot_at_zero`.

## Real source paths and full complex germs

`HillHminusOneEnergyRootContinuationAgreement.lean` works with the actual
verified NLS Theorem12.1 data and the proved open joint root domain on an
actual complex rough-open pullback V containing zero. If the real radial
path r*q stays in V, then for every fixed nonreal energy both roots are
continuous and nonzero along that entire path. Their squares agree with
the same independent rough Hill radicand. Their equality at zero persists
on the connected interval 0<=r<=1. This proves
`HillHminusMiuraChart.energyRoot_eq_continuedRoot_nonreal`.

For any real energy in the common domain, that domain contains all
nonreal energies and this real point, hence is preconnected. The same
nonvanishing square-root uniqueness extends equality to the full common
domain, in `energyRoot_eq_continuedRoot_of_real_segment`.

At each common-domain point the two actual joint domains are open and
both roots are jointly analytic. Their proven value agreement and common
square identity imply equality in a full complex neighborhood of
(lambda,q), in `energyRoot_germ_eq_continuedRoot_of_real_segment`.
This is equality of joint energy/Hminus1 germs, beyond a real slice.

Finally, `exists_hillHminus_energyRoot_continuation_agreement` constructs
one actual chart and one positive norm-ball radius before all real
inputs and all energies. The ball lies in the complex pullback V and
real radial paths stay in it by the norm estimate. All the preceding
value and full-germ conclusions hold for every physically real q in
that ball and every energy in its actual common domain. No index,
noncollapsed-gap, finite-head or L2 qualification is imposed.

## Limits and remaining proof obligations

The common norm ball is uniform for the real inputs. The full complex
germ may depend on the energy and the real base input. The result does
not yet give one complex rough neighborhood covering all old frequency
contours simultaneously. It does not assert that either energy domain
contains the other's real cuts or its excluded slit.

The actual NLS-derived entire energy numerator still needs its genuine
critical-basis Hilbert realization or growth/product argument to identify
it with the earlier normalized weighted rough family. Normalization
periods alone do not prove uniqueness of arbitrary entire functions.
These steps, the full coherent W family, lowest-cut primitive/moment
identification, canonical leading scalar one, sharp source estimate(54),
physical Hamiltonian frequency identity(69), action descent, weighted
asymptotic and compact derivative claims and actual Birkhoff/PDE flows
remain open. No main theorem is certified by this milestone.

## Validation

Four new proved modules are directly checked. All 394 previous selected
Lean sources remain byte-identical and all seven shared provenance
records remain valid. The exact checker/audit/PASS/coverage selections
and full transitive axiom counts are recorded in `VALIDATION.md` and
`source.json`. Pinned Lean4.33.1/mathlibv4.33.1, default heartbeats,
warnings as errors, private fresh outputs and the permitted
propext/Classical.choice/Quot.sound axioms are retained. Canonical main
remains unchanged and read only.
