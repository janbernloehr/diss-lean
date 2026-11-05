# Actual rough action amplitudes for the finite head

This proves necessary amplitude geometry toward Theorem 1.1 at its Hminus-one endpoint. All eleven complete main theorem rows remain OPEN.

## Exact physical rough amplitude germs

`NLS.KdV.exists_hillHminusLocalActionGapRatio_analytic_positive_physical` and `NLS.KdV.exists_hillHminusLocalActionAmplitude_analytic_physical` construct, for EVERY fixed positive index n, a complex Hminus-one ball near zero carrying analytic extensions R_n and B_n of the original physical action-to-half-gap-square ratio and its principal amplitude. The ratio has positive real part, and

```text
R_n(0) = 1/(2*pi*n),
B_n = sqrt(2*R_n)/sqrt(2),
B_n(0) = 1/sqrt(2*pi*n).
```

The ratio is normalized by the squared HALF energy gap. The existing physical action satisfies `I_n = half_gap_n^2 * R_n`. Normalizing by the full gap square would introduce a factor of four.

On its rough ball each amplitude has a genuine weighted bound `sqrt(1+n)*norm(B_n(q)) <= C_n`. At EVERY original physical real L2 source whose literal Hminus-one inclusion belongs to that ball, the ratio and amplitude equal the ORIGINAL physical `hillActionGapRatio` and `hillAbelianAmplitudePrefactor`. Collapsed gaps and nonzero means are included. The physical L2 norm need not be small. The proved recovery is on the dense original physical L2 slice; an identity with an intrinsic rough action integral is a further obligation.

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_finite_physical_action_amplitudes` chooses ONE complex source radius and ONE weighted bound BEFORE every index in any prescribed FINITE set of positive indices. The set may contain the first gap and any collapsed gaps. A common source radius before ALL infinitely many indices has not yet been proved here; the infinite-tail estimate remains an explicit assembly obligation.

## Construction and physical matching

The scalar rough midpoint and squared-gap germs are logarithmic moments of the actual entire rough radicand on the original free integration circle. Cauchy deflation gives a joint energy/source analytic unit, and the actual original free root fixes its square root. Dividing the derivative of the rough discriminant by that root gives the actual free-normalized trace germ. The quadratic sine-squared cosine mean is analytic through the collapsed free gap.

All of these formulas agree EXACTLY with the existing complex L2 formulas on EVERY complex L2 inclusion, for the entire energy variable. This supplies the original physical L2 germ.

`NLS.KdV.analyticAt_hillActionGapRatio_realScale` proves the existing physical ratio is real analytic along every real scaling line, including through collapsed gaps. `NLS.KdV.hillActionGapRatio_eq_on_rough_ball_of_germ` then uses analytic uniqueness on the connected inverse image of a rough ball to continue germ agreement to EVERY physical L2 source in that ball. Thus physical matching on the rough ball is proved; it is not inferred from small L2 norm.

## Native normalized energy gap squares

`NLS.KdV.exists_hillHminus_native_gap_square_sequence` constructs a native ell1 analytic map around EVERY actual real Hminus-one base, on one complex neighborhood before every positive index, recovering

```text
G_n = ((actual_upper_energy_n-actual_lower_energy_n)/n)^2.
```

The symmetric frequency formula is `(2*pi+2*d_n/n)^2*g_n`, where d is the actual NLS frequency midpoint displacement in ell2 and g is its actual squared gap sequence in ell1. A bounded reciprocal inclusion and Holder multiplication make this a genuine Banach analytic map; every nonpositive output is zero.

`NLS.Articles.KdVKdV2Frequencies.exists_hillHminus_native_gap_square_packet` chooses one near-zero complex ball with G0=0 and `norm(Gq)<=C*norm(q)`, before ALL positive indices. The construction includes all real rough inputs, first and collapsed gaps and nonzero means. A quadratic bound is not claimed.

## Remaining main obligations and validation

The finite-head amplitude germs must be combined with a proved common infinite-tail amplitude family. Full rough regular-phase estimates and the negative-half target Abelian map remain to be assembled. Full coordinate-coordinate canonicality, global inverse, the entire regularity scale and the actual Hamiltonian/frequency/PDE main conclusions remain open.

The construction reuses the existing dissertation/shared developments without changing any prior selected source or provenance record. No new shared import or alternate spectral family is substituted.

Prior strict evidence retained for all 1439 unchanged selected baseline sources; all seven new proof modules strictly compiled in dependency order, followed by a fresh combined transitive axiom audit of all 1446 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1484 frozen source/checker/provenance/Mathlib-source hashes, all 35 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these seven new proof modules. No full 1446-module rebuild is claimed.

Fresh audit: 12566 selected and 34636 imported NLS declarations. Seven new proof modules contain 30 explicit theorems and 10 definitions. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
