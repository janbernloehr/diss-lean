import NLS.ZakharovShabat.ResonantCubicTail

/-! # Normalized fourth-power tails of the cubic remainder

For potentials bounded by B*s as s tends to zero from above, the full-strip
fourth-power error sum divided by s^12 tends to zero. The sum is infinite,
and the error supremum is taken over each whole closed strip.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance cubicFourthTailFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The signed fourth-power tail of actual full-strip error suprema. -/
def resonantCubicFourthErrorSum (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 4)
    (N : ℕ) (positive : Bool) : ℝ :=
  ∑' n : ℤ, sourceCoefficientPowerTail 4 N (fun k => resonantCubicErrorSup (by simp) w φ k positive) n

/-- The fourth-power error sum is nonnegative, even before summability is established. -/
theorem resonantCubicFourthErrorSum_nonneg (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 4)
    (N : ℕ) (positive : Bool) : 0 ≤ resonantCubicFourthErrorSum w φ N positive := by
  apply tsum_nonneg
  intro n
  unfold sourceCoefficientPowerTail
  split_ifs
  · norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
    exact (show Even (4 : ℕ) by decide).pow_nonneg _
  · exact le_rfl

/-- The actual fourth-power error sum is bounded by a constant times norm(phi)^20. -/
theorem resonantCubicFourthErrorSum_le (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 4)
    (N : ℕ) (hN : 0 < N) (positive : Bool)
    (hsmall : 2*weightedDoubleConstant (p := 4) (by simp)*‖φ‖^2 ≤ 1/2) :
    resonantCubicFourthErrorSum w φ N positive ≤ resonantCubicTailConstant (p := 4) (by simp)*‖φ‖^20 := by
  have h := (resonantCubicErrorSup_tail (p := 4) (by simp) (by norm_num) w φ N hN hsmall positive).2
  simpa only [resonantCubicFourthErrorSum,ENNReal.toReal_ofNat,show (5 : ℝ)*4=20 by norm_num,
    Real.rpow_ofNat] using h

/-- After cubic normalization, a linearly bounded potential has an eighth-power error budget. -/
theorem resonantCubicFourthErrorSum_normalized_le (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight 4)
    (N : ℕ) (hN : 0 < N) (positive : Bool) (B s : ℝ) (hs : 0 < s)
    (hsmall : 2*weightedDoubleConstant (p := 4) (by simp)*‖φ‖^2 ≤ 1/2)
    (hφ : ‖φ‖ ≤ B*s) :
    resonantCubicFourthErrorSum w φ N positive/s^12 ≤
      resonantCubicTailConstant (p := 4) (by simp)*B^20*s^8 := by
  apply (div_le_iff₀ (pow_pos hs 12)).mpr
  have h := (resonantCubicFourthErrorSum_le w φ N hN positive hsmall).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hφ 20)
      (resonantCubicTailConstant_nonneg (p := 4) (by simp) (by norm_num)))
  apply h.trans_eq
  ring

open Filter Topology in
/-- The normalized infinite fourth-power error sum tends to zero along any controlled small family. -/
theorem resonantCubicFourthErrorSum_normalized_tendsto (w : SpectralWeight)
    (φ : ℝ → WeightedCoeffPair w.toWeight 4) (N : ℕ) (hN : 0 < N) (positive : Bool)
    (B : ℝ) (hφ : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      2*weightedDoubleConstant (p := 4) (by simp)*‖φ s‖^2 ≤ 1/2 ∧ ‖φ s‖ ≤ B*s) :
    Tendsto (fun s => resonantCubicFourthErrorSum w (φ s) N positive/s^12) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hupper : Tendsto (fun s : ℝ => resonantCubicTailConstant (p := 4) (by simp)*B^20*s^8)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => resonantCubicTailConstant (p := 4) (by simp)*B^20*s^8)
        (𝓝 0) (𝓝 (resonantCubicTailConstant (p := 4) (by simp)*B^20*(0 : ℝ)^8)) :=
      tendsto_const_nhds.mul (tendsto_id.pow 8)
    simpa using (h : Tendsto (fun s : ℝ => resonantCubicTailConstant (p := 4) (by simp)*B^20*s^8)
      (𝓝 0) (𝓝 (resonantCubicTailConstant (p := 4) (by simp)*B^20*(0 : ℝ)^8))).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun s =>
    div_nonneg (resonantCubicFourthErrorSum_nonneg w (φ s) N positive) (by positivity))) ?_ hupper
  filter_upwards [hφ,self_mem_nhdsWithin] with s hs hspos
  exact resonantCubicFourthErrorSum_normalized_le w (φ s) N hN positive B s hspos hs.1 hs.2

end NLS.ZakharovShabat
