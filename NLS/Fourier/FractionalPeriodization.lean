import NLS.Fourier.PeriodizationIncrement
import NLS.Fourier.IntervalL2Realization
import NLS.Fourier.FractionalSobolevIdentification

/-!
# Periodization of subcritical fractional interval data

Physical periodic energy is controlled by the translation energy of the zero
extension. Fractional Hardy control and actual interval Fourier reconstruction
therefore put arbitrary interval data in the weighted periodic Sobolev space
for `0<s<1/2`, without requiring matching endpoint values.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

theorem measurable_circlePullback (f : CircleL2) : Measurable (circlePullback f) :=
  (Lp.stronglyMeasurable f).measurable.comp (AddCircle.measurePreserving_mk 2 0).measurable

theorem periodic_circlePullback (f : CircleL2) : Function.Periodic (circlePullback f) 2 := by
  intro x
  change f ((x + 2 : ℝ) : AddCircle (2 : ℝ)) = f (x : AddCircle (2 : ℝ))
  rw [AddCircle.coe_add_period]

/-- The periodic energy in real-distance kernel form, with the singular zero displacement handled explicitly. -/
theorem fractionalTranslationEnergy_eq_real_kernel (s : ℝ) (f : CircleL2) :
    fractionalTranslationEnergy s f = ENNReal.ofReal (1 / 2 : ℝ) *
      ∫⁻ t : ℝ in Icc (-1) 1, ∫⁻ x : ℝ in Ioo 0 2,
        ENNReal.ofReal (‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) *
          ENNReal.ofReal (|t| ^ (-(1 + 2 * s))) := by
  rw [fractionalTranslationEnergy, translationEnergy_eq_double_lintegral]
  congr 1
  apply lintegral_congr
  intro t
  have he : volume.restrict (Ioc (0 : ℝ) 2) = volume.restrict (Ioo (0 : ℝ) 2) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [he]
  apply lintegral_congr
  intro x
  by_cases ht : t = 0
  · simp [ht]
  · rw [fractionalTranslationKernel, ENNReal.ofReal_rpow_of_pos (abs_pos.mpr ht), mul_comm]

/-- A uniform physical comparison with real-line zero-extension translation energy. -/
theorem fractionalTranslationEnergy_le_zeroExtension (s : ℝ) (f : CircleL2) :
    fractionalTranslationEnergy s f ≤ ENNReal.ofReal (9 / 2 : ℝ) *
      fractionalLineTranslationEnergy s (intervalZeroExtension 2 (circlePullback f)) := by
  let g := intervalZeroExtension 2 (circlePullback f)
  let w := fun t : ℝ => ENNReal.ofReal (|t| ^ (-(1 + 2 * s)))
  have hi : (∫⁻ t : ℝ in Icc (-1) 1, ∫⁻ x : ℝ in Ioo 0 2,
      ENNReal.ofReal (‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) * w t) ≤
      9 * fractionalLineTranslationEnergy s g := by
    calc
      _ ≤ ∫⁻ t : ℝ in Icc (-1) 1, 9 * ∫⁻ x : ℝ, ENNReal.ofReal (‖g (t + x) - g x‖ ^ 2) * w t := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
        exact mul_le_mul' (periodic_increment_square_le_line (circlePullback f)
          (periodic_circlePullback f) (measurable_circlePullback f) ht) le_rfl
      _ = 9 * ∫⁻ t : ℝ in Icc (-1) 1, ∫⁻ x : ℝ, ENNReal.ofReal (‖g (t + x) - g x‖ ^ 2) * w t :=
        lintegral_const_mul' _ _ (by norm_num)
      _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
  rw [fractionalTranslationEnergy_eq_real_kernel]
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (9 * fractionalLineTranslationEnergy s g) := mul_le_mul' le_rfl hi
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num

/-- Intrinsic interval regularity of a periodic `L²` representative implies its physical periodic regularity below half. -/
theorem hasFractionalPeriodicRegularity_of_interval {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : CircleL2) (hE : fractionalIntervalEnergy s 2 (circlePullback f) < ⊤) :
    HasFractionalPeriodicRegularity s f := by
  have hf₂ : MemLp (circlePullback f) 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using memLp_circlePullback f
  exact (fractionalTranslationEnergy_le_zeroExtension s f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (fractionalLineTranslationEnergy_zeroExtension_lt_top hs hs₁ (by norm_num) (circlePullback f) ⟨hf₂, hE⟩))

/-- Actual interval Fourier reconstruction has periodic fractional regularity below half, without endpoint matching. -/
theorem hasFractionalPeriodicRegularity_periodTwoL2Coefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    HasFractionalPeriodicRegularity s (l2Synthesis (periodTwoL2Coefficients f hf₂)) := by
  apply hasFractionalPeriodicRegularity_of_interval hs hs₁
  have he : circlePullback (l2Synthesis (periodTwoL2Coefficients f hf₂)) =ᵐ[volume.restrict (Ioo 0 2)] f := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using circlePullback_periodTwoL2Coefficients f hf₂
  rw [fractionalIntervalEnergy_congr he]
  exact hE

/-- Physical interval regularity gives weighted square summability of the actual Fourier integrals. -/
theorem memlp_sobolev_periodTwoCoefficient_of_interval {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2)))
    (hE : fractionalIntervalEnergy s 2 f < ⊤) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ) * periodTwoCoefficient f n) 2 := by
  have h := (hasFractionalPeriodicRegularity_iff_memlp hs (by linarith)
    (l2Synthesis (periodTwoL2Coefficients f hf₂))).mp
    (hasFractionalPeriodicRegularity_periodTwoL2Coefficients hs hs₁ f hf₂ hE)
  simpa only [fourierCoeff_l2Synthesis, periodTwoL2Coefficients_apply] using h

/-- Quantitative periodization bound expressed entirely in the original interval data. -/
theorem fractionalTranslationEnergy_periodTwoL2Coefficients_le (s : ℝ) (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    fractionalTranslationEnergy s (l2Synthesis (periodTwoL2Coefficients f hf₂)) ≤
      ENNReal.ofReal (9 / 2 : ℝ) * (fractionalIntervalEnergy s 2 f + 2 * fractionalExteriorEnergy s 2 f) := by
  let P := l2Synthesis (periodTwoL2Coefficients f hf₂)
  have he : circlePullback P =ᵐ[volume.restrict (Ioo 0 2)] f := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using circlePullback_periodTwoL2Coefficients f hf₂
  have hp : MemLp (circlePullback P) 2 (volume.restrict (Ioo 0 2)) := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ioc] using memLp_circlePullback P
  have h := fractionalTranslationEnergy_le_zeroExtension s P
  rw [fractionalLineTranslationEnergy_zeroExtension s _ hp,
    fractionalIntervalEnergy_congr he, fractionalExteriorEnergy_congr he] at h
  exact h

end NLS.Fourier
