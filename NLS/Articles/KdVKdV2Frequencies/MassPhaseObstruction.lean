import NLS.Dynamics.UnboundedPhaseObstruction

/-! # The mass term in the KdV2 frequency obstruction

This adapter retains precisely the coefficient in source equation (90),
PDF p. 51. It is a dependency for Theorem 1.12(v), not a proof of that theorem:
mass divergence for physical smooth approximants and the spectral frequency
identity still have to be supplied by the actual KdV construction.
-/

noncomputable section
set_option autoImplicit false
open Set Filter Topology

namespace NLS.Articles.KdVKdV2Frequencies

/-- The full positive-mode KdV2 frequency with a specified mass and correction. -/
def kdv2FrequencyFromMass (n : ℕ) (mass correction : ℝ) : ℝ :=
  (2 * (n : ℝ) * Real.pi) ^ 5 + 20 * (2 * (n : ℝ) * Real.pi) * mass + correction

/-- At each fixed positive mode, diverging mass dominates any convergent
renormalized correction, with the exact source normalization. -/
theorem tendsto_kdv2FrequencyFromMass_atTop {ι : Type*} {l : Filter ι}
    (n : ℕ) (hn : 1 ≤ n) (mass correction : ι → ℝ) (r : ℝ)
    (hmass : Tendsto mass l atTop) (hcorrection : Tendsto correction l (𝓝 r)) :
    Tendsto (fun j => kdv2FrequencyFromMass n (mass j) (correction j)) l atTop := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hc : 0 < 20 * (2 * (n : ℝ) * Real.pi) := by positivity
  exact ((tendsto_const_nhds (x := (2 * (n : ℝ) * Real.pi) ^ 5)).add_atTop
    (hmass.const_mul_atTop hc)).atTop_add hcorrection

/-- A nonzero limiting mode cannot have a uniform compact-time trajectory
limit when its KdV2 mass diverges and its correction converges. -/
theorem not_tendsto_kdv2Mass_phaseTrajectories {ι : Type*} {l : Filter ι} [NeBot l]
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n)
    (mass correction : ι → ℝ) (r : ℝ)
    (hmass : Tendsto mass l atTop) (hcorrection : Tendsto correction l (𝓝 r))
    (amp : ι → ℂ) (a : ℂ) (ha : a ≠ 0) (hamp : Tendsto amp l (𝓝 a))
    (g : ι → C(Icc (0 : ℝ) T, ℂ))
    (he : ∀ j (τ : Icc (0 : ℝ) T), g j τ =
      Complex.exp (((τ.val * kdv2FrequencyFromMass n (mass j) (correction j) : ℝ) : ℂ) *
        Complex.I) * amp j)
    (G : C(Icc (0 : ℝ) T, ℂ)) : ¬ Tendsto g l (𝓝 G) :=
  Dynamics.not_tendsto_phase_trajectories T hT
    (fun j => kdv2FrequencyFromMass n (mass j) (correction j)) amp a ha
    (tendsto_kdv2FrequencyFromMass_atTop n hn mass correction r hmass hcorrection)
    hamp g he G

end NLS.Articles.KdVKdV2Frequencies
