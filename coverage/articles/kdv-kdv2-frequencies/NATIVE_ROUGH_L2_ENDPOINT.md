# Exact physical L2 endpoint of the actual rough inverse

This advances the actual Birkhoff and physical approximation dependencies of Theorem 1.1 and Theorem 1.12(v). All eleven complete main theorem rows remain OPEN.

## The same actual rough analytic inverse

`exists_hillHminus_native_L2_endpoint_inverse` and its direct real-target formulation `exists_hillHminus_native_real_target_L2_endpoint_inverse` retain ONE actual signed rough Abelian map Z, its exact original physical recovery on a complex H-minus-one ball, and an explicit complex Banach analytic inverse family R on an OPEN negative-half target neighborhood W containing zero. R(0)=0. Every complex target b in W has a mean-zero rough source R(b) in the source ball and the literal right inverse identity

```text
Z(R(b)) = meanZeroWeightedLiftCLM(sobolev(-1/2), b).
```

Every real b gives a physical-real rough source. These are the actual native spectral map and inverse already constructed; no caller-supplied L2 inverse or action-frequency model replaces them.

## Exact endpoint for arbitrary real targets

For EVERY real b in W, let a be its literal weighted target lift. The new theorem proves, including arbitrary infinite support:

```text
raw R(b) belongs to L2  iff  a belongs to native h^(1/2).
```

The target lift is signed-real and has central coefficient zero. Equivalently, the theorem quantifies over EVERY original signed-real a in native h^(-1/2) whose exact Hilbert-weight coordinate belongs to W. The direct b formulation proves explicitly that all real targets in W are covered.

For every endpoint-regular target, an ORIGINAL physical real mean-zero L2 potential p is reconstructed with EXACT literal rough inclusion equal to R(b), and EVERY fixed GLOBAL original Birkhoff Abelian coordinate equals a_n. Its mass has the exact normalization

```text
norm(p)^2 = sum_(n>=1) 4*pi*n*|a_n|^2
          = 2*kdvFiniteMass(a).
```

The KdV Hamiltonian half-norm convention has coefficient 2*pi*n. The displayed norm is the squared original L2 norm. The target has genuine finite mass by native half regularity; no use is made of a nonsummable totalized tsum.

## Why L2 membership is derived

Symmetric finite truncations in the deleted Hilbert target preserve physical conjugation and the omitted central slot, have genuine finite support, converge in the native norm and commute exactly with every weighted lift. They eventually belong to W. The previously constructed finite-support physical inverse theorem gives ORIGINAL L2 preimages of all sufficiently large truncations, with exact squared norm equal to twice the truncated KdV mass.

Native half regularity makes these masses genuinely summable and bounds EVERY truncated mass by the original mass. Thus the physical L2 preimages have a common L2 bound. Continuity of the SAME analytic R gives convergence of their literal H-minus-one inclusions to R(b). The existing original real L2 compactness theorem yields a physical L2 subsequential limit, and uniqueness of the rough limit identifies its inclusion EXACTLY with R(b). This proves the sufficiency without assuming L2 membership of the inverse image.

For necessity, an L2 rough source is reconstructed in original physical mean-zero coordinates. Exact whole-ball physical recovery identifies its target with the fixed GLOBAL original Birkhoff coordinates. Native Hilbert membership of that map proves genuine positive mass summability. The already verified signed-real endpoint characterization then gives full native h^(1/2) regularity, including negative modes and the zero slot. Summability is not inferred from a norm equality involving an unrestricted tsum.

## Remaining main obligations

The statement concerns the actual local rough inverse at zero. It does not assert arbitrary-base or global H-minus-one inversion, nor full inverse Sobolev regularity and topology for arbitrary targets. R is complex analytic with values in H-minus-one; a separate stronger L2-valued analytic restriction is not packaged by this theorem. Actual physical approximation/mass-divergence families, quantitative negative-Sobolev convergence, Hamiltonian/action-frequency identification, frequency-map estimates and the physical PDE main conclusions still require proof. No complete main theorem is marked verified.

## Validation

All 2367 previously selected source bytes and all 39 provenance records remain unchanged. Five new own proof modules reuse the already reachable verified library, without shared-source replacements.

Prior strict evidence retained for all 2367 unchanged selected baseline sources. All five new own proof modules strictly rebuilt in dependency order, followed by a fresh combined transitive axiom audit of all 2372 selected modules. Exact checker/audit/coverage/evidence selections, transitive selected order and reachability, 2414 frozen source/checker/provenance/Mathlib-source hashes, all 39 unchanged verified provenance records, private fresh outputs and unchanged clean canonical main verified. The NLS import closure adds exactly these five selections; no new shared-source import is needed. No full 2372-module rebuild is claimed.

Fresh audit: 18809 selected and 40879 imported NLS declarations. Five own modules contain 15 explicit theorems. Lean4.33.1/mathlib4.33.1, warningAsError, autoImplicit=false and default heartbeats. Only propext, Classical.choice and Quot.sound; no new axioms or proof-checking exceptions. All eleven main theorem rows remain OPEN.
