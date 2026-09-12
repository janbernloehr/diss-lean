import NLS.Fourier.FractionalKernelScaling

/-!
# Fractional spectral weights are comparable to `|n|^(2s)`

The lower constant is the positive model-kernel mass on `[0,1]`; the upper
constant is its finite total mass. Scaling and monotonicity of nonnegative
integrals prove the comparison uniformly in all integer frequencies.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

def fractionalLowerConstant (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, fractionalModelKernel s x

def fractionalUpperConstant (s : ℝ) : ℝ := ∫ x : ℝ, fractionalModelKernel s x

theorem fractionalLowerConstant_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    0 < fractionalLowerConstant s := fractionalModelKernel_core_pos hs hs₁

theorem fractionalLowerConstant_le_upper {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    fractionalLowerConstant s ≤ fractionalUpperConstant s := by
  rw [fractionalLowerConstant, intervalIntegral.integral_of_le (by norm_num)]
  exact setIntegral_le_integral (integrable_fractionalModelKernel hs hs₁)
    (Filter.Eventually.of_forall (fractionalModelKernel_nonneg s))

theorem fractionalUpperConstant_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    0 < fractionalUpperConstant s :=
  (fractionalLowerConstant_pos hs hs₁).trans_le (fractionalLowerConstant_le_upper hs hs₁)

/-- Every scaled interval contains the same positive core and is bounded by the total mass. -/
theorem fractionalModelKernel_integral_bounds {s R : ℝ} (hs : 0 < s) (hs₁ : s < 1) (hR : 1 ≤ R) :
    fractionalLowerConstant s ≤ (∫ x in -R..R, fractionalModelKernel s x) ∧
      (∫ x in -R..R, fractionalModelKernel s x) ≤ fractionalUpperConstant s := by
  have hi := integrable_fractionalModelKernel hs hs₁
  rw [intervalIntegral.integral_of_le (by linarith)]
  constructor
  · rw [fractionalLowerConstant, intervalIntegral.integral_of_le (by norm_num)]
    apply setIntegral_mono_set hi.integrableOn
      (Filter.Eventually.of_forall (fractionalModelKernel_nonneg s))
    apply Filter.Eventually.of_forall
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans hR⟩
  · exact setIntegral_le_integral hi (Filter.Eventually.of_forall (fractionalModelKernel_nonneg s))

/-- Two-sided bounds at every positive frequency, with constants independent of that frequency. -/
theorem fractionalSpectralWeight_bounds_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    {n : ℤ} (hn : 0 < n) :
    ENNReal.ofReal (fractionalLowerConstant s * (n : ℝ) ^ (2 * s)) ≤ fractionalSpectralWeight s n ∧
      fractionalSpectralWeight s n ≤ ENNReal.ofReal (fractionalUpperConstant s * (n : ℝ) ^ (2 * s)) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := fractionalModelKernel_integral_bounds hs hs₁ hn₁
  rw [fractionalSpectralWeight_scale hs hs₁ hn]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.1 (Real.rpow_nonneg (by linarith) _)
  · apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg (by linarith) _)

/-- The comparison includes negative frequencies and the zero mode. -/
theorem fractionalSpectralWeight_bounds {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) (n : ℤ) :
    ENNReal.ofReal (fractionalLowerConstant s * |(n : ℝ)| ^ (2 * s)) ≤ fractionalSpectralWeight s n ∧
      fractionalSpectralWeight s n ≤ ENNReal.ofReal (fractionalUpperConstant s * |(n : ℝ)| ^ (2 * s)) := by
  have hp (m : ℤ) (hm : 0 < m) :
      ENNReal.ofReal (fractionalLowerConstant s * |(m : ℝ)| ^ (2 * s)) ≤ fractionalSpectralWeight s m ∧
        fractionalSpectralWeight s m ≤ ENNReal.ofReal (fractionalUpperConstant s * |(m : ℝ)| ^ (2 * s)) := by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    simpa only [abs_of_pos hm'] using fractionalSpectralWeight_bounds_pos hs hs₁ hm
  rcases lt_trichotomy n 0 with hn | hn | hn
  · simpa only [Int.cast_neg, abs_neg, fractionalSpectralWeight_neg] using hp (-n) (neg_pos.mpr hn)
  · subst n
    have he : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs.ne'
    simp [Real.zero_rpow he]
  · exact hp n hn

/-- Every fractional spectral weight is finite throughout `0 < s < 1`. -/
theorem fractionalSpectralWeight_lt_top {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) (n : ℤ) :
    fractionalSpectralWeight s n < ⊤ :=
  ((fractionalSpectralWeight_bounds hs hs₁ n).2).trans_lt ENNReal.ofReal_lt_top

/-- Exactly the nonzero frequencies have positive spectral weight. -/
theorem fractionalSpectralWeight_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) {n : ℤ} (hn : n ≠ 0) :
    0 < fractionalSpectralWeight s n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact (ENNReal.ofReal_pos.mpr (mul_pos (fractionalLowerConstant_pos hs hs₁)
    (Real.rpow_pos_of_pos (abs_pos.mpr hn') _))).trans_le (fractionalSpectralWeight_bounds hs hs₁ n).1

/-- Homogeneous Fourier energy with the conventional fractional power of frequency. -/
def homogeneousFourierEnergy (s : ℝ) (f : CircleL2) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (|(n : ℝ)| ^ (2 * s) * ‖fourierCoeff f n‖ ^ 2)

/-- The physical fractional energy and homogeneous Fourier energy control each other. -/
theorem fractionalTranslationEnergy_bounds {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) (f : CircleL2) :
    ENNReal.ofReal (fractionalLowerConstant s) * homogeneousFourierEnergy s f ≤
        fractionalTranslationEnergy s f ∧
      fractionalTranslationEnergy s f ≤
        ENNReal.ofReal (fractionalUpperConstant s) * homogeneousFourierEnergy s f := by
  rw [fractionalTranslationEnergy_eq_tsum, homogeneousFourierEnergy]
  constructor
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    have hn := mul_le_mul' (fractionalSpectralWeight_bounds hs hs₁ n).1
      (le_refl (ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2)))
    simpa only [ENNReal.ofReal_mul (fractionalLowerConstant_pos hs hs₁).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), mul_assoc] using hn
  · rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro n
    have hn := mul_le_mul' (fractionalSpectralWeight_bounds hs hs₁ n).2
      (le_refl (ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2)))
    simpa only [ENNReal.ofReal_mul (fractionalUpperConstant_pos hs hs₁).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), mul_assoc] using hn

/-- Finiteness of the physical seminorm is exactly homogeneous Fourier energy finiteness. -/
theorem hasFractionalPeriodicRegularity_iff_homogeneous {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) : HasFractionalPeriodicRegularity s f ↔ homogeneousFourierEnergy s f < ⊤ := by
  have hb := fractionalTranslationEnergy_bounds hs hs₁ f
  constructor
  · intro hf
    have hc : 0 < ENNReal.ofReal (fractionalLowerConstant s) :=
      ENNReal.ofReal_pos.mpr (fractionalLowerConstant_pos hs hs₁)
    rcases ENNReal.mul_lt_top_iff.mp (hb.1.trans_lt hf) with hh | hh | hh
    · exact hh.2
    · exact (hc.ne' hh).elim
    · rw [hh]
      exact ENNReal.zero_lt_top
  · intro hf
    exact hb.2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

/-- The physical regularity criterion as ordinary summability of weighted squared coefficients. -/
theorem hasFractionalPeriodicRegularity_iff_summable {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) : HasFractionalPeriodicRegularity s f ↔
      Summable (fun n : ℤ => |(n : ℝ)| ^ (2 * s) * ‖fourierCoeff f n‖ ^ 2) := by
  rw [hasFractionalPeriodicRegularity_iff_homogeneous hs hs₁, homogeneousFourierEnergy]
  constructor
  · intro hf
    simpa only [ENNReal.toReal_ofReal
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))] using ENNReal.summable_toReal hf.ne
  · exact fun hf => hf.tsum_ofReal_lt_top

/-- Every single Fourier mode has finite physical fractional energy in the fractional range. -/
theorem hasFractionalPeriodicRegularity_single {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (n : ℤ) (z : ℂ) : HasFractionalPeriodicRegularity s (l2Synthesis (lp.single 2 n z)) := by
  rw [HasFractionalPeriodicRegularity, fractionalTranslationEnergy_single]
  exact ENNReal.mul_lt_top (fractionalSpectralWeight_lt_top hs hs₁ n) ENNReal.ofReal_lt_top

end NLS.Fourier
