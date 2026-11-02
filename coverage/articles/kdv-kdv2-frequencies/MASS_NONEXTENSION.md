# Endpoint mass and the nonextension dependency

Status: the signed-coordinate mass and compact-time obstruction below are
proved. **Theorem 1.12(v) for the physical equation remains open.**

The source is the pinned arXiv v1 in `source.json`. The relevant passages
are Theorem 1.12(v), PDF p. 8, the endpoint and phase formula (90), p. 51,
and the proof of Theorem 4.14(v), p. 54. The exact normalization is

```text
H0(z) = sum_(n>=1) (2n*pi) |z_n|^2,
omega_2,n = (2n*pi)^5 + 20(2n*pi)H0 + omega_2*,n.
```

## Proven declarations

The declarations are in
`NLS/Articles/KdVKdV2Frequencies/SignedMassDivergence.lean`, under
`NLS.Articles.KdVKdV2Frequencies`.

| Declaration | Exact contribution |
| --- | --- |
| `hasHalfRegularity_iff_summable_kdvMassTerm` | For every positive weight `w` and real signed mean-zero `a` in the native weighted Hilbert sequence space, the raw coefficients belong to `h^(1/2)` if and only if the positive-index mass terms are summable. The endpoint uses the source weight `(1+abs(n))^(1/2)`. No mass/regularity equivalence is left as a caller assumption. |
| `tendsto_kdvFiniteMass_atTop` | For every filter, every endpoint-irregular signed datum `a` and **every** endpoint-regular family `z_i` converging coefficientwise to it, `H0(z_i)` tends to positive infinity. The family can use a different positive weight; there is no hidden uniform bound or finite-support hypothesis. |
| `signedTruncate`, `tendsto_signedTruncate`, `hasHalfRegularity_signedTruncate` | Construct symmetric finite coefficient truncations, prove that zero mode and conjugate symmetry are preserved, prove native weighted norm convergence, and prove membership of every approximant in `h^(1/2)`. |
| `tendsto_kdvFiniteMass_signedTruncate` | The explicitly constructed norm-convergent approximants have diverging mass at every endpoint-irregular signed datum. |
| `exists_positive_nonzero_of_not_hasHalfRegularity` | Every such rough datum has a nonzero positive mode. No nonzero-mode assumption is needed to establish availability of an obstruction mode. |
| `not_tendsto_kdv2_signedTruncate_phaseTrajectories` | For every fixed nonzero positive mode, every `T>0`, and every correction continuous at the rough datum, trajectories satisfying the exact negative Hamiltonian phase formula along these truncations cannot converge in `C([0,T], C)` to **any** continuous limit. The earlier adapter's mass-divergence and approximation assumptions are now discharged by the constructed truncations. |
| `not_continuousAt_kdv2_modeTrajectory_extension` | No map to `C([0,T], C)` continuous at that datum can agree with the displayed KdV2 phase formula along the truncations. The agreement and actual correction remain explicit inputs, pending their spectral construction. |

`kdvFiniteMass` is an ordinary real `tsum`, used with a proved finite-mass
hypothesis at each approximant. It is not asserted to be positive infinity
at a rough datum: Lean's real `tsum` is totalized. The divergence conclusions
are genuine filter limits of finite real masses.

The generic finite-partial-sum argument lives once in
`NLS/SequenceSpaces/NonnegativeEnergyDivergence.lean`, as
`NLS.tendsto_atTop_of_nonsummable_coordinate_limit`. The existing
`NLS.Coeff.tendsto_energy_atTop_of_nonsummable_limit` now calls it with
unchanged statement; the existing pair-energy theorem remains unchanged.
Thus the article and the prior Hilbert result share the proof rather than
duplicating it.

## Remaining physical requirements

For the source range `-1<s<0`, take `w = Weight.sobolev (s+1/2)`. This
specialization has the exact Birkhoff target and endpoint. To conclude the
actual main theorem still requires all of:

1. The constructed physical Hill/Birkhoff map and inverse with this
   regularity, topology and normalization, including equivalence of `L2_0`
   and the `h^(1/2)` target.
2. The actual KdV2 renormalized spectral correction continuous (indeed
   analytic in the source) on the lower-regularity space, and its exact
   frequency identity with coefficient `20(2n*pi)`.
3. Smooth physical solutions identified with the Hamiltonian phase flow
   for the inverse images of finite signed truncations.
4. Transfer of the coordinate obstruction through the continuous physical
   Birkhoff map on compact-time trajectory spaces.

The source's later Theorem 4.14(v) also claims a **fixed-time coordinate**
nonextension result. The new theorem concerns the uniform compact-time
topology; it is not used to claim that stronger fixed-time assertion. The
fixed-time proof and all actual-equation identifications remain open.

## Shared development inspection

The dedicated branches now contain committed work beyond the article plan:
the Hill/free-complement line was inspected through `5b29695`, and the KdV
action contour analytic-summation line through `be9eba0`. These supply
useful foundations but not yet the full physical Birkhoff map or spectral
frequency identity required above. Their source was read without editing
another branch or sending other-chat messages. This step reuses the
dissertation's established sequence, phase and analytic-topology library;
it introduces no competing Hill or action-Hamiltonian construction.
