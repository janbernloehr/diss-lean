# Rough analytic action ratios are identified through collapsed gaps

This proves necessary physical normalization geometry toward the Hminus-one endpoint of Theorem 1.1. All eleven main theorem rows remain OPEN.

## Nontriviality of every selected gap germ

`NLS.KdV.frequently_hillRealGapHalfLength_ne_zero` proves that for EVERY fixed positive index n, actual original physical real L2 sources with an open nth gap occur arbitrarily near zero. If that gap were identically collapsed on a physical neighborhood, its actual Abelian coordinate would vanish there. The already proved exact free Fourier derivative, tested on the literal even Fourier single mode, contradicts this.

`NLS.KdV.hillLocalGapSquare_native_germ_nontrivial` and `NLS.KdV.hillHminusLocalGapSquare_l2_germ_nontrivial` transfer this to the actual analytic squared-gap formulas in native complex L2 coordinates. These germs are nontrivial even though their value at zero is zero. The statements do not assert gap-opening density near arbitrary bases or one potential opening all gaps simultaneously.

## Cancellation without division at a closed gap

`NLS.ComplexAnalysis.analytic_germ_cancel` and `analytic_germ_cancel_eq` work on any complex normed source. A nontrivial scalar analytic multiplier can be cancelled from germ identities. The proof selects a nearby point where the multiplier is nonzero, obtains vanishing on a neighborhood of that point by continuity, and applies analytic uniqueness on a connected ball. No nonzero value at the original base is required.

`NLS.KdV.eventuallyEq_native_of_physical_real_germ` proves that the ORIGINAL physical real potential germ determines a scalar native complex L2 analytic germ. The proof uses the actual continuous unit source lift, exact even-index insertion and sampling inverse, and the previously verified period-one real-form identity principle.

`NLS.KdV.hillHminus_ratio_l2_germ_eq_of_gap_products` and `hillHminus_ratio_physical_germ_eq_of_gap_products` combine those facts. For rough analytic candidates R and H, the identity

```text
half_gap_n(p)^2 * R(physical_Hminus_source(p))
  = half_gap_n(p)^2 * H(physical_Hminus_source(p))
```

on an original physical real L2 germ implies equality of their native complex L2 and physical real germs. The multiplier is the actual selected spectral gap, with its normalization proved by logarithmic moments. All closed gaps at the free base are included.

## From actual actions to the original ratio on the whole rough ball

`NLS.KdV.hillHminus_action_ratio_germ_of_physical_actions` identifies any rough analytic candidate R satisfying the ACTUAL physical action identity

```text
I_n(p) = half_gap_n(p)^2 * R(physical_Hminus_source(p))
```

on the original physical real L2 germ with the original `hillActionGapRatio` germ. The previously constructed actual rough local ratio provides the comparison, so its physical normalization is not supplied by the caller.

`NLS.KdV.hillHminus_action_ratio_eq_on_ball_of_physical_action_germ` then propagates this equality to EVERY original physical L2 source in the candidate's entire complex rough ball. Its physical L2 norm need not be small. The factorization hypothesis uses the squared HALF energy gap; switching to the full gap square changes the constant by four.

These are identification theorems with explicit candidate analyticity and actual action factorization hypotheses. They do not by themselves construct the high-frequency family. The next task is to supply those hypotheses using the verified shared high-contour action family, combine its common infinite-tail ball with the proved finite head, and obtain common all-index rough amplitudes. Full rough phase/Abelian-map assembly, canonicality, global inverse, the full regularity scale and the actual frequency/PDE main conclusions remain open.

## Validation

Prior strict evidence retained for all 1446 unchanged selected baseline sources; all four new proof modules strictly compiled in dependency order, followed by a fresh combined transitive axiom audit of all 1450 selected modules. Exact checker/audit/coverage/evidence selections, full transitive selected order and reachability, 1488 frozen source/checker/provenance/Mathlib-source hashes, all 35 unchanged verified provenance records, private fresh outputs and clean unchanged canonical main verified. The imported NLS source closure adds exactly these four new proof modules. No full 1450-module rebuild is claimed.

Fresh audit: 12583 selected and 34650 imported NLS declarations. Four new proof modules contain 10 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no sorry, new axiom, heartbeat/recursion override or linter exception. All eleven main theorem rows remain OPEN.
