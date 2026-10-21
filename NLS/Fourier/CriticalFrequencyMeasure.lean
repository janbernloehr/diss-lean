import NLS.Fourier.HomogeneousNLSScaling
import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # The critical spectral measure and its dilation Jacobian

This implements the critical full-line dilation statement from the introduction, printed p. 10.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The locally finite spectral measure |xi| dxi models the critical negative-half norm. -/
def criticalFrequencyMeasure : Measure ℝ := volume.withDensity (fun ξ : ℝ => ENNReal.ofReal ‖ξ‖)

instance criticalFrequencyMeasure_locallyFinite : IsLocallyFiniteMeasure criticalFrequencyMeasure :=
  IsLocallyFiniteMeasure.withDensity_ofReal (μ := volume) continuous_norm

/-- The critical spectral measure has temperate growth, so its Lp classes give
actual tempered distributions through the standard integral pairing. -/
instance criticalFrequencyMeasure_temperate : criticalFrequencyMeasure.HasTemperateGrowth := by
  refine ⟨3,?_⟩
  change Integrable (fun x : ℝ => (1+‖x‖)^(-(3:ℝ)))
    (volume.withDensity (fun x : ℝ => ENNReal.ofReal ‖x‖))
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _),smul_eq_mul]
  have hi : Integrable (fun x : ℝ => (1+‖x‖)^(-(2:ℝ))) volume :=
    integrable_one_add_norm (by norm_num)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  rw [norm_mul,Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    _ ≤ (1+‖x‖)*(1+‖x‖)^(-(3:ℝ)) := by gcongr; linarith
    _ = _ := by
      calc
        (1+‖x‖)*(1+‖x‖)^(-(3:ℝ)) = (1+‖x‖)^((1:ℝ)+(-3)) := by
          rw [Real.rpow_add (by positivity),Real.rpow_one]
        _ = _ := by norm_num

/-- Integration against the critical measure is the literal |xi| weighted integral. -/
theorem lintegral_criticalFrequencyMeasure (F : ℝ → ℝ≥0∞) :
    (∫⁻ ξ : ℝ, F ξ ∂criticalFrequencyMeasure) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal ‖ξ‖*F ξ :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable volume (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) F

/-- The critical measure has the exact quadratic dilation Jacobian. -/
theorem lintegral_criticalFrequencyMeasure_dilation {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ≥0∞) :
    (∫⁻ ξ : ℝ, F (c*ξ) ∂criticalFrequencyMeasure) =
      (ENNReal.ofReal c⁻¹)^2 * ∫⁻ ξ : ℝ, F ξ ∂criticalFrequencyMeasure := by
  have hunit : ENNReal.ofReal c⁻¹*ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),inv_mul_cancel₀ hc.ne']
    norm_num
  simp only [lintegral_criticalFrequencyMeasure]
  calc
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ ξ : ℝ, ENNReal.ofReal ‖c*ξ‖*F (c*ξ) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro ξ
      simp only [norm_mul,Real.norm_of_nonneg hc.le,ENNReal.ofReal_mul hc.le,
        ← mul_assoc,hunit,one_mul]
    _ = ENNReal.ofReal c⁻¹ *
        (ENNReal.ofReal c⁻¹ * ∫⁻ ξ : ℝ, ENNReal.ofReal ‖ξ‖*F ξ) := by
      rw [lintegral_line_dilation hc (fun ξ : ℝ => ENNReal.ofReal ‖ξ‖*F ξ)]
    _ = _ := by ring

/-- Dilation preserves the critical measure with its exact scaled target. -/
theorem measurePreserving_criticalFrequency_dilation {c : ℝ} (hc : 0 < c) :
    MeasurePreserving (fun x : ℝ => c*x) criticalFrequencyMeasure
      ((ENNReal.ofReal c⁻¹)^2 • criticalFrequencyMeasure) := by
  refine ⟨by fun_prop,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,Measure.smul_apply,smul_eq_mul,
    ← lintegral_indicator_one (hs.preimage (by fun_prop)),← lintegral_indicator_one hs]
  have h := lintegral_criticalFrequencyMeasure_dilation hc (s.indicator 1)
  convert h using 1
  apply lintegral_congr
  intro x
  by_cases hx : c*x ∈ s <;> simp [Set.mem_preimage,hx]

end NLS.Fourier
