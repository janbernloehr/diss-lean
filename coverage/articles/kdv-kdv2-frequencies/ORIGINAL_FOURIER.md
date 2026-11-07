# Exact original-potential Fourier remainder

The actual retained Miura lift is eliminated from the Fourier core toward Corollary 1.7. At EVERY real ORIGINAL L2 source, ONE common complex original-L2 neighborhood gives the SAME globally calibrated signed forward map as the inclusion of an analytic raw h^(1/2) ORIGINAL-potential Fourier core plus a uniformly locally bounded analytic raw h^(3/2) TOTAL remainder. The core has zero coefficient at 0, and at BOTH signed labels plus/minus n it is EXACTLY the ORIGINAL potential coefficient q_(plus/minus n)/sqrt(2*pi*n), multiplied by the SAME fixed physical sign stored at positive n in the base chart. All finite positive labels, closed gaps, original root witnesses and source conjugations are retained. The remainder includes all prior phase/midpoint/amplitude/own-eta/spectral errors and the actual nonlinear Miura correction.

## Actual shifted Miura equation

The retained chart already satisfies its ORIGINAL period-one distributional Miura equation. Taking a nonzero coefficient removes its actual energy shift, since that shift is supported only at zero. Thus q_n = 2*pi*i*n*u_n + convolution(u,u)_n at every nonzero signed label, for the SAME retained lift. No unrelated inverse or substitute potential is chosen.

One unchanged verified H1 convolution module supplies bounded bilinear multiplication with its literal convolution sum. The actual retained H1 germ therefore gives the bounded analytic h1 correction T = 2*pi*i*u - convolution(u,u) on one smaller ORIGINAL complex L2 neighborhood. Local analytic boundedness is used only after shrinking that neighborhood; no bound on an arbitrary whole ball is inferred.

## Exact finite-index normalization

The preceding normalized packet core was 2*pi*i*freeAmplitude_n*u_n. The exact equation gives

`2*pi*i*u_n - q_n/(1+n) = (2*pi*i*u_n-convolution(u,u)_n)/(1+n)`.

The correction on the right has an analytic h2 realization: apply the h1 weight, multiply by the bounded positive free-amplitude symbol, and undo the h2 weight. Its coefficient is exactly freeAmplitude_n*T_n/(1+n). Adding this correction to the prior TOTAL remainder leaves the exact normalized ORIGINAL-potential core freeAmplitude_n*q_n/(1+n). The nonpositive core head remains zero. No factor 1+n is replaced by n.

The exact free factor is sqrt(1+n)/sqrt(2*pi*n). Signed half-order transport multiplies the positive core by sqrt(1+n), and the proved square-root identity gives exactly q_n/sqrt(2*pi*n), including every finite positive label.

## Both signed halves of the SAME map

The same globally calibrated positive map is reconstructed using its previously stored physical signs. A reusable signed-completion theorem identifies the raw core at zero and at BOTH plus/minus n. The positive physical sign at n applies to both halves; the original source conjugate reflection and output conjugation cancel exactly on the linear Fourier coefficient. This holds on the common complex original-L2 neighborhood, rather than just at real points. The core is zero at zero. Its analytic raw h^(1/2) realization plus the TOTAL analytic raw h^(3/2) remainder equals the SAME signed physical forward map.

The output signs retained in this statement belong to the chart at the real base. A theorem comparing with one fixed global Fourier orientation still requires identifying those signs across global charts (or proving that their changes contribute only the required smoothing). The full inverse comparison and physical PDE solution identification also remain. This milestone makes no complete Corollary 1.7 claim.

## Own modules

- `NLS/Articles/KdVKdV2Frequencies/ActualL2OriginalFourierIdentification.lean`: The SAME globally calibrated positive physical forward map is reconstructed from its exact ORIGINAL-potential Fourier core and TOTAL analytic h2 remainder, retaining every stored base-chart physical sign.
- `NLS/Articles/KdVKdV2Frequencies/ActualL2OriginalFourierRemainder.lean`: The SAME actual normalized packet has exact ORIGINAL potential positive core freeAmplitude_n*q_n/(1+n), zero nonpositive head, and a TOTAL analytic uniformly locally bounded h2 remainder through its actual shifted Miura equation.
- `NLS/Articles/KdVKdV2Frequencies/ActualL2RawOriginalFourierRemainder.lean`: Final actual-map dependency: the SAME signed physical forward map has zero Fourier core at 0 and EXACT signed original q_(plus/minus n)/sqrt(2*pi*n) coefficients at BOTH halves, plus a TOTAL analytic raw h^(3/2) locally bounded remainder near EVERY real ORIGINAL L2 source. Fixed global Fourier orientation, inverse comparison and physical PDE identification remain.
- `NLS/ComplexAnalysis/BoundedAnalyticGerm.lean`: A Banach-valued analytic germ has one smaller original-norm complex neighborhood with a common finite norm bound. Opaque source/target spaces retain default kernel limits.
- `NLS/KdV/HillHminusL2MiuraNonlinear.lean`: The SAME retained native H1 Miura germ gives an analytic bounded h1 realization of 2*pi*i*actualLift minus its actual convolution square, on ONE ORIGINAL complex L2 neighborhood.
- `NLS/KdV/HillHminusMiuraNonzeroEquation.lean`: The SAME supplied retained chart satisfies the literal ORIGINAL period-one Miura equation at EVERY nonzero signed coefficient. Its actual energy shift contributes ONLY at zero.
- `NLS/KdV/HillRawFreeFourierNormalization.lean`: Exact identity sqrt(1+n)*freeAmplitude_n/(1+n)=1/sqrt(2*pi*n) at EVERY positive label. No finite-index or asymptotic normalization is discarded.
- `NLS/SequenceSpaces/AnalyticBracketPacketRefinement.lean`: A bounded analytic h1 correction divided by the EXACT inverse bracket has an analytic h2 realization; add it to the prior TOTAL packet remainder with exact ALL-slot coefficients and zero nonpositive head.
- `NLS/SequenceSpaces/SignedHalfOriginalFourierCore.lean`: A literal real positive Fourier multiplier determines BOTH signed halves and the zero coefficient of the original-source signed completion, retaining every fixed output sign and source conjugation.

## Validation

All 3806 prior selected sources and all 62 prior provenance records remain byte-identical. The exact new transitive import closure is 10 modules: nine own modules with nine explicit public theorems, and one unchanged verified shared H1 convolution module pinned to commit 334579e6fb05cfac349f0a25d87640cebf24005c. One new provenance record gives 63 total. All 10 modules were strictly rebuilt in dependency order AFTER freezing 3882 selected-source/checker/provenance/pinned-Mathlib-source hashes. The fresh transitive axiom audit covers all 3816 selections and EVERY imported NLS declaration: 27909 selected declarations and 49979 imported declarations. Its ENTIRE traversal and allowed-axiom loop remain byte-identical to the previous milestone. Exact ordered selection, dependencies, private fresh outputs, overlay targets, 30 private chunks of at most 128 names, and the bidirectional 3816-name set probe with insertion/deletion rejection are verified. The cumulative 3824 strict PASS records cover 3816 unique modules, retaining eight prior repeats. All prior logs are retained for this milestone, including the 31 baseline checks explicitly refreshed and disclosed in the preceding retained-eta-fourier milestone. The unique evidence prefix is original-potential-fourier. Canonical main and pinned Mathlib remain unchanged. Default heartbeat, recursion and kernel limits, autoImplicit=false and warningAsError=true apply; only propext, Classical.choice and Quot.sound are allowed. This is a 10-module incremental rebuild retaining prior strict evidence, not a full rebuild.

## Remaining main obligations

Complete main rows remain 3 VERIFIED: Theorem 1.1, Corollary 1.4 and ALL THREE clauses of Corollary 1.5; 8 main rows remain OPEN. The SAME chart now has the EXACT ORIGINAL-potential Fourier core at zero and BOTH signed halves, with a TOTAL locally bounded analytic one-derivative remainder in the ORIGINAL L2 norm. The core retains the base chart physical output signs; identifying one fixed Fourier orientation across all global charts, the full inverse one-smoothing comparison, and identification with the unique physical PDE solution remain essential for Corollary 1.7. No full physical Corollary 1.7 or globally fixed-orientation forward/inverse smoothing theorem is claimed. Theorem 1.2 still lacks the ORIGINAL ACTION s=-1 UNIFORM little-o endpoint. The goal remains ACTIVE and incomplete.
