# Intrinsic critical labels and compatible complex germs

This step supports the source's coherent spectral neighborhood construction.
It does not close a main theorem or identify the normalized numerator family.

`HillHminusMiuraChart.energyCritical_eq_of_real_overlap` proves that any two
actual charts with real shifts and real-type spectral sources at a common
input have identical positive critical energy labels. Each chart's sequence
is real, strictly increasing, and exhausts all zeros of the independent rough
Hill discriminant derivative. Equality of their real ranges, followed by
strict monotone enumeration uniqueness on the positive integers, identifies
all labels. There is no smallness, cutoff, or open-gap hypothesis.

`eventually_energyCritical_is_critical` proves that a canonical energy label
is an actual critical point on a full complex neighborhood of a real-type
input. At the base point its frequency is positive and its canonical branch
is analytic. Continuity keeps that frequency nonzero nearby, and the actual
frequency derivative identity gives the energy root identity. The nearby
inputs themselves need not be real type.

The reusable `NLS.ComplexAnalysis.eventuallyEq_of_simple_spectral_root`
identifies a continuous root branch with an analytic reference branch through
the same simple root. The actual moving divided difference is continuous
along the competing graph and nonzero at the center. Its exact factorization
then forces equality on a neighborhood. No uniqueness premise is assumed.

`HillHminusMiuraChart.eventuallyEq_energyCritical_of_simple_root` specializes
that result to the actual rough Hill trace. Any continuous actual critical
branch through the canonical value has the same full complex germ.
`eventuallyEq_energyCritical_of_real_overlap` combines this with intrinsic
real labels to prove equality of the two canonical chart germs.

The neighborhood may depend on the positive index. This does not assert a
single complex neighborhood on which every label of both charts agrees,
joint source analyticity of the entire Hilbert basis, agreement of actual
normalized numerators between charts, or identification with the earlier
weighted normalized family. Free-label identification, continuation from
free values to the earlier local labels, actual contour normalization,
physical frequency(69), and all main theorem obligations remain open.
