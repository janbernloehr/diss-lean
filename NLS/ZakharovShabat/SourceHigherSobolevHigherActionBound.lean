import NLS.ZakharovShabat.SourceHigherSobolevEmbedding
import NLS.ZakharovShabat.SourceWeightedHigherActionBound

/-! # Absolute convergence through level 2s+1 on the original Hˢ source -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The squared Hˢ gap weight dominates all polynomial factors through order 2s. -/
theorem higherAction_higherSobolev_weight_bound (s : ℕ) (n : ℤ) (k : ℕ) (hk : k ≤ 2*s) :
    (1+|(n:ℝ)|)^k ≤ ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n))^2 := by
  calc
    _ ≤ (1+|(n:ℝ)|)^(2*s) := pow_le_pow_right₀ (by linarith [abs_nonneg (n:ℝ)]) hk
    _ ≤ (1+2*|(n:ℝ)|)^(2*s) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [abs_nonneg (n:ℝ)]
    _ = _ := by
      simp only [SpectralWeight.sobolev_apply, Weight.sobolev_apply, Real.rpow_natCast,
        Int.cast_mul, Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), ← pow_mul]
      rw [Nat.mul_comm s 2]

/-- One complex Hˢ neighborhood and one bound work for all higher-action
levels 1 through 2s+1. This uses the original Fourier coefficients. -/
theorem exists_local_sourceHigherSobolevHigherAction_bound
    (s : ℕ) (a : SobolevSource s)
    (ha : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∀ k : ℕ, k ≤ 2*s → ∃ J : Coeff 1,
        (∀ n : ℤ, J n = sourceComplexHigherAction (by simp) (by norm_num) n k
          (higherSobolevSourceInclusion s b)) ∧ ‖J‖ ≤ C :=
  exists_local_sourceWeightedHigherAction_bound
    (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))
    (higherSobolevSourceInclusion s) (higherSobolevSourceWeightedPeriodOne s)
    (weightedBaseToPair_higherSobolevSourceWeightedPeriodOne s) (2*s)
    (higherAction_higherSobolev_weight_bound s) a ha

end NLS.ZakharovShabat
