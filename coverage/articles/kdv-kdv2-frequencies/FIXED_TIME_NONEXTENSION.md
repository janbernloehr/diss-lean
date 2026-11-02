# Fixed-time coordinate nonextension

The sequence-space obstruction required for the fixed-time claim of
Theorem 4.14(v), PDF p. 52, is now proved. **The actual spectral correction
and the physical KdV2/Birkhoff-flow identification remain open**, so this
does not mark Theorem 1.12 or 4.14 verified for the actual equation.

## Precise proved statement

`NLS.Articles.KdVKdV2Frequencies.not_continuousAt_kdv2_fixedTime_mode_extension`
is in `NLS/Articles/KdVKdV2Frequencies/FixedTimeNonextension.lean`.
Its quantifiers and topology are:

- Every real `sigma < 1/2`, with the native strong norm on signed real,
  zero-mode-free `ell^(sigma,2)` coefficients.
- Every datum `a` in that space, every positive integer `n >= 1` with
  `a_n != 0`, and every fixed time `t > 0`.
- Every supplied scalar correction continuous at `a`, and every mode map
  `Q` agreeing on the endpoint-regular data with the exact KdV2 phase value
  `exp(-i*t*((2n*pi)^5+20(2n*pi)H0+correction))*z_n`.
- The conclusion is `not ContinuousAt Q a`, with codomain `C` in its usual
  norm topology. It is a fixed-time conclusion, not a statement about
  uniform compact-time convergence.

Taking `sigma = s+1/2` covers the source range `-1<s<0`. The theorem does
not assume the datum itself is outside `h^(1/2)`: a nonzero selected mode
is sufficient for the lower-topology obstruction. Agreement is required
only on endpoint-regular inputs, where the mass is a finite real sum.
No real `tsum` at rough data is interpreted as positive infinity.

The source prints a positive exponential in (91), but p. 3 gives the
negative Hamiltonian phase at positive modes. This implementation follows
the Hamiltonian time orientation already recorded in `SOURCE_MAP.md`.
The phase separation is unchanged by reversal of this sign; physical
identification still needs to check the selected convention explicitly.

## Construction and proof dependencies

For each truncation index `N`, let `p_N` be the symmetric finite truncation
of `a`. Define

```text
D = pi / (t * 20(2n*pi)) > 0,
m_N = N+1,
r_N = sqrt(D / (2*m_N*pi)),
q_N = p_N + r_N at each of the two modes +/-m_N.
```

The new `SignedMassInsertion.lean` proves:

| Declaration | Content |
| --- | --- |
| `signedNeedle` and `massInsertedTruncate` | Explicit conjugate-real, zero-mode-preserving finite perturbations, disjoint from the support of the old truncation. |
| `hasHalfRegularity_massInsertedTruncate` | Every perturbed approximant belongs to the exact endpoint `h^(1/2)`. |
| `kdvFiniteMass_massInsertedTruncate` and `kdvFiniteMass_prescribed_insert` | `H0(q_N)=H0(p_N)+D` exactly. The two signed coordinates represent one positive action; the mass increment is `(2*m_N*pi)*r_N^2`, without an extra factor two. |
| `tendsto_sobolev_div_sqrt` | `(1+m)^sigma/sqrt(m)` tends to zero for each `sigma<1/2`. |
| `norm_signedNeedle_le` and `tendsto_signedNeedle_zero` | The inserted pair tends to zero in the native weighted norm. |
| `tendsto_massInsertedTruncate` | Both `p_N` and `q_N` converge to the same original datum in that norm. |

For all sufficiently large `N`, the selected `n`th coordinates of the two
approximants agree. The exact source coefficient gives

```text
t * (omega_n(q_N)-omega_n(p_N))
  = pi + t * (correction(q_N)-correction(p_N)) -> pi.
```

The generic result
`NLS.Dynamics.not_tendsto_same_limit_of_phase_gap`, in
`NLS/Dynamics/FixedTimePhaseObstruction.lean`, proves that their phase values
have limiting separation twice the nonzero limiting amplitude. It reuses
the existing phase-flow increment identity via a single supported
coefficient. The individual frequencies need not converge. Continuity of
`Q` at the common input limit would force both outputs to the same value,
giving the contradiction.

## Validation and remaining requirements

All ten selected modules compile with pinned Lean 4.33.1/mathlib v4.33.1,
`-DautoImplicit=false -DwarningAsError=true`, with the default heartbeat
budget. The transitive audit passes for 191 selected-module declarations
and 1489 declarations including imported NLS dependencies. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed.

This closes the fixed-time sequence argument, including construction and
norm convergence of the separating approximants. It leaves the actual
spectral correction, its lower-regularity continuity, the Birkhoff map and
the endpoint physical phase formula to be constructed and identified.
Those are essential requirements of the main article theorems and are
not replaced by parameters counted as completion.
