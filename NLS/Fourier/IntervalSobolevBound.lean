import NLS.Fourier.FractionalHardyBound
import NLS.Fourier.IntervalFourierLebesgue

/-!
# Uniform intrinsic bounds for interval Fourier coefficients

The explicit Hardy and periodization bounds combine with the lower Fourier
energy estimate. The resulting weighted Hilbert estimate retains the physical
square-integral term and applies to arbitrary representatives on `[0,2]`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Nonnegative Parseval with the exact period-two normalization. -/
theorem ofReal_norm_sq_periodTwoL2Coefficients (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    ENNReal.ofReal (‖periodTwoL2Coefficients f hf‖ ^ 2) =
      ENNReal.ofReal (1 / 2 : ℝ) * intervalSquareEnergy 2 f := by
  rw [norm_sq_periodTwoL2Coefficients, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), integral_Ioc_eq_integral_Ioo]
  have hi : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using
      hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  exact ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- The combined Hardy and periodization energy constant. -/
def intervalPeriodizationConstant (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (9 / 2 : ℝ) * (1 + 2 * fractionalExteriorBoundConstant s 2)

theorem intervalPeriodizationConstant_lt_top {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) :
    intervalPeriodizationConstant s < ⊤ := by
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨by norm_num, ENNReal.mul_lt_top (by norm_num) (fractionalExteriorBoundConstant_lt_top hs hs₁ 2)⟩)

/-- Uniform periodization energy bound in the original intrinsic interval data. -/
theorem fractionalTranslationEnergy_le_intrinsic {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    fractionalTranslationEnergy s (l2Synthesis (periodTwoL2Coefficients f hf)) ≤
      intervalPeriodizationConstant s * intrinsicIntervalEnergy s 2 f := by
  have hf' : MemLp f 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  have he : fractionalIntervalEnergy s 2 f ≤ intrinsicIntervalEnergy s 2 f := le_add_left le_rfl
  calc
    _ ≤ ENNReal.ofReal (9 / 2 : ℝ) * (fractionalIntervalEnergy s 2 f + 2 * fractionalExteriorEnergy s 2 f) :=
      fractionalTranslationEnergy_periodTwoL2Coefficients_le s f hf
    _ ≤ ENNReal.ofReal (9 / 2 : ℝ) * (intrinsicIntervalEnergy s 2 f +
        2 * (fractionalExteriorBoundConstant s 2 * intrinsicIntervalEnergy s 2 f)) :=
      mul_le_mul' le_rfl (add_le_add he (mul_le_mul' le_rfl
        (fractionalExteriorEnergy_le_intrinsic hs hs₁ (by norm_num) f hf')))
    _ = _ := by simp only [intervalPeriodizationConstant, add_mul, one_mul, mul_assoc, mul_add]

/-- Actual weighted Fourier coefficients of subcritical interval data. -/
def intervalSobolevCoefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) : WeightedCoeff (Weight.sobolev s) 2 :=
  ⟨periodTwoCoefficient f, memlp_sobolev_periodTwoCoefficient_of_interval hs hs₁ f hf hE⟩

@[simp] theorem intervalSobolevCoefficients_apply {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) (n : ℤ) :
    (intervalSobolevCoefficients hs hs₁ f hf hE).val n = periodTwoCoefficient f n := rfl

@[simp] theorem sobolevL2Synthesis_intervalSobolevCoefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    sobolevL2Synthesis hs.le (intervalSobolevCoefficients hs hs₁ f hf hE) =
      l2Synthesis (periodTwoL2Coefficients f hf) := by
  apply fourierBasis.repr.injective
  ext n
  simp only [fourierBasis_repr, fourierCoeff_sobolevL2Synthesis,
    intervalSobolevCoefficients_apply, fourierCoeff_l2Synthesis, periodTwoL2Coefficients_apply]

/-- The finite constant combining the lower spectral estimate, Parseval, and periodization. -/
def intervalSobolevBoundConstant (s : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (fractionalLowerConstant s))⁻¹ * ENNReal.ofReal ((2 : ℝ) ^ (2 * s)) *
    (ENNReal.ofReal (fractionalLowerConstant s) * ENNReal.ofReal (1 / 2 : ℝ) + intervalPeriodizationConstant s)

theorem intervalSobolevBoundConstant_lt_top {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) :
    intervalSobolevBoundConstant s < ⊤ := by
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (fractionalLowerConstant_pos hs (by linarith))))
    ENNReal.ofReal_lt_top) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, intervalPeriodizationConstant_lt_top hs hs₁⟩)

/-- The complete weighted coefficient square bound in intrinsic interval energy. -/
theorem ofReal_norm_sq_intervalSobolevCoefficients_le {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    ENNReal.ofReal (‖intervalSobolevCoefficients hs hs₁ f hf hE‖ ^ 2) ≤
      intervalSobolevBoundConstant s * intrinsicIntervalEnergy s 2 f := by
  have hc := fractionalLowerConstant_pos hs (show s < 1 by linarith)
  have h := sobolev_norm_sq_le_physical_energy hs (by linarith)
    (intervalSobolevCoefficients hs hs₁ f hf hE)
  rw [sobolevL2Synthesis_intervalSobolevCoefficients, norm_l2Synthesis,
    ENNReal.ofReal_mul hc.le, ENNReal.ofReal_mul hc.le, ofReal_norm_sq_periodTwoL2Coefficients] at h
  have hN : intervalSquareEnergy 2 f ≤ intrinsicIntervalEnergy s 2 f := le_add_right le_rfl
  have hp := fractionalTranslationEnergy_le_intrinsic hs hs₁ f hf
  have hb := h.trans (mul_le_mul' le_rfl (add_le_add
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hN)) hp))
  have hn := (ENNReal.mul_le_iff_le_inv (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top).mp hb
  simpa only [intervalSobolevBoundConstant, add_mul, mul_add, mul_assoc] using hn

/-- Uniform bound in the actual intrinsic fractional interval size. -/
theorem norm_intervalSobolevCoefficients_le {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    ‖intervalSobolevCoefficients hs hs₁ f hf hE‖ ≤
      Real.sqrt (intervalSobolevBoundConstant s).toReal * intrinsicIntervalSize s 2 f := by
  have hf' : MemLp f 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hf
  exact norm_le_sqrt_energy _ (intervalSobolevBoundConstant_lt_top hs hs₁)
    (intrinsicIntervalEnergy_lt_top f hf' hE) (ofReal_norm_sq_intervalSobolevCoefficients_le hs hs₁ f hf hE)

end NLS.Fourier
