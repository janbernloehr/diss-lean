import NLS.Fourier.IntervalSobolevIdentification

/-!
# Two-sided intrinsic interval and weighted Fourier norm bounds

The reverse restriction estimate controls intrinsic interval size by the
weighted Fourier norm for `0<s<1`. Below half it combines with periodization
to give two-sided bounds for arbitrary interval representatives.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Circle normalization converts the full physical period square integral into twice the `L²` norm. -/
theorem intervalSquareEnergy_circlePullback (f : CircleL2) :
    intervalSquareEnergy 2 (circlePullback f) = 2 * ENNReal.ofReal (‖f‖ ^ 2) := by
  have he : periodTwoL2Coefficients (circlePullback f) (memLp_circlePullback f) = fourierBasis.repr f := by
    ext n
    simp only [periodTwoL2Coefficients_apply, periodTwoCoefficient_circlePullback, fourierBasis_repr]
  have h := ofReal_norm_sq_periodTwoL2Coefficients (circlePullback f) (memLp_circlePullback f)
  rw [he, LinearIsometryEquiv.norm_map] at h
  rw [h, ← mul_assoc]
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [htwo, one_mul]

/-- A finite restriction constant retaining the constant mode and the kernel tail. -/
def intervalRestrictionConstant (s : ℝ) : ℝ≥0∞ :=
  2 + 2 * (ENNReal.ofReal (fractionalUpperConstant s) + ENNReal.ofReal (4 / s))

theorem intervalRestrictionConstant_lt_top (s : ℝ) : intervalRestrictionConstant s < ⊤ := by
  exact ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.mul_lt_top (by norm_num)
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)⟩

/-- Weighted periodic Sobolev coefficients control the full intrinsic interval energy. -/
theorem intrinsicIntervalEnergy_sobolevL2Synthesis_le {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    intrinsicIntervalEnergy s 2 (circlePullback (sobolevL2Synthesis hs.le a)) ≤
      intervalRestrictionConstant s * ENNReal.ofReal (‖a‖ ^ 2) := by
  have hp : ‖sobolevL2Synthesis hs.le a‖ ^ 2 ≤ ‖a‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_sobolevL2Synthesis_le hs.le a)
  have hN : intervalSquareEnergy 2 (circlePullback (sobolevL2Synthesis hs.le a)) ≤ 2 * ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [intervalSquareEnergy_circlePullback]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hp)
  have hT : ENNReal.ofReal (4 / s * ‖sobolevL2Synthesis hs.le a‖ ^ 2) ≤
      ENNReal.ofReal (4 / s * ‖a‖ ^ 2) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp (by positivity))
  calc
    _ ≤ 2 * ENNReal.ofReal (‖a‖ ^ 2) + 2 *
        (ENNReal.ofReal (fractionalUpperConstant s * ‖a‖ ^ 2) + ENNReal.ofReal (4 / s * ‖a‖ ^ 2)) :=
      add_le_add hN ((fractionalIntervalEnergy_le_periodic hs _).trans
        (mul_le_mul' le_rfl (add_le_add (fractionalTranslationEnergy_sobolevL2Synthesis_le hs hs₁ a) hT)))
    _ = _ := by
      rw [ENNReal.ofReal_mul (fractionalUpperConstant_pos hs hs₁).le,
        ENNReal.ofReal_mul (by positivity : 0 ≤ 4 / s)]
      simp only [intervalRestrictionConstant, add_mul, mul_add, mul_assoc]

/-- The reverse bound in real intrinsic interval size, for every fractional periodic index below one. -/
theorem intrinsicIntervalSize_sobolevL2Synthesis_le {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    intrinsicIntervalSize s 2 (circlePullback (sobolevL2Synthesis hs.le a)) ≤
      Real.sqrt (intervalRestrictionConstant s).toReal * ‖a‖ := by
  have h := intrinsicIntervalEnergy_sobolevL2Synthesis_le hs hs₁ a
  have hI := h.trans_lt (ENNReal.mul_lt_top (intervalRestrictionConstant_lt_top s) ENNReal.ofReal_lt_top)
  have hh : ENNReal.ofReal (‖intrinsicIntervalSize s 2 (circlePullback (sobolevL2Synthesis hs.le a))‖ ^ 2) ≤
      intervalRestrictionConstant s * ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg _ _ _), intrinsicIntervalSize_sq,
      ENNReal.ofReal_toReal hI.ne]
    exact h
  simpa only [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg _ _ _),
    ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] using
      norm_le_sqrt_energy _ (intervalRestrictionConstant_lt_top s) ENNReal.ofReal_lt_top hh

/-- The reverse norm bound applies to the original arbitrary interval representative below half. -/
theorem intrinsicIntervalSize_le_intervalSobolevCoefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    intrinsicIntervalSize s 2 f ≤
      Real.sqrt (intervalRestrictionConstant s).toReal * ‖intervalSobolevCoefficients hs hs₁ f hf hE‖ := by
  have he : circlePullback (sobolevL2Synthesis hs.le (intervalSobolevCoefficients hs hs₁ f hf hE))
      =ᵐ[volume.restrict (Ioo 0 2)] f := by
    rw [sobolevL2Synthesis_intervalSobolevCoefficients]
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using circlePullback_periodTwoL2Coefficients f hf
  have hsize : intrinsicIntervalSize s 2 (circlePullback (sobolevL2Synthesis hs.le (intervalSobolevCoefficients hs hs₁ f hf hE))) =
      intrinsicIntervalSize s 2 f := congrArg (fun E : ℝ≥0∞ => Real.sqrt E.toReal) (intrinsicIntervalEnergy_congr he)
  rw [← hsize]
  exact intrinsicIntervalSize_sobolevL2Synthesis_le hs (by linarith) _

/-- Explicit two-sided equivalence of the intrinsic interval size and its actual weighted Fourier norm. -/
theorem intervalSobolev_norm_equivalence {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    ‖intervalSobolevCoefficients hs hs₁ f hf hE‖ ≤
        Real.sqrt (intervalSobolevBoundConstant s).toReal * intrinsicIntervalSize s 2 f ∧
      intrinsicIntervalSize s 2 f ≤
        Real.sqrt (intervalRestrictionConstant s).toReal * ‖intervalSobolevCoefficients hs hs₁ f hf hE‖ :=
  ⟨norm_intervalSobolevCoefficients_le hs hs₁ f hf hE,
    intrinsicIntervalSize_le_intervalSobolevCoefficients hs hs₁ f hf hE⟩

end NLS.Fourier
