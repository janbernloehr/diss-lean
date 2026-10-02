import NLS.Fourier.SobolevDerivative
import NLS.FunctionalAnalysis.LinearVolterra

/-! # Restricting the Fourier H¹ representative to the unit interval

The constant extension used by the classical ODE agrees with Fourier
synthesis on the interval. Endpoint changes do not affect its derivative
integrals. All regularity and bounds follow from the weighted coefficients.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Fourier

/-- The continuous unit-interval representative of physical H¹ coefficients. -/
def sobolevUnitCurve (a : ScalarDomain 2) : Curve ℂ where
  toFun t := sobolevSynthesis (by simp) a (t.val : AddCircle (2 : ℝ))
  continuous_toFun := (sobolevSynthesis (by simp) a).continuous.comp
    (continuous_quotient_mk'.comp continuous_subtype_val)

/-- The restriction and constant extension preserve all values on `[0,1]`. -/
theorem extend_sobolevUnitCurve (a : ScalarDomain 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extend (sobolevUnitCurve a) t = sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ)) := by
  exact extend_coe (sobolevUnitCurve a) ⟨t,ht⟩

/-- A uniform bound depending only on the weighted Hilbert norm. -/
theorem norm_sobolevUnitCurve_le (a : ScalarDomain 2) : ‖sobolevUnitCurve a‖ ≤ 4*‖a‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  exact ((sobolevSynthesis (by simp) a).norm_coe_le_norm _).trans
    (by simpa only [ENNReal.toReal_ofNat, show (2 : ℝ)*2 = 4 by norm_num] using
      norm_sobolevSynthesis_le_two_mul (by simp) a)

/-- Fourier H¹ regularity supplies the absolute continuity required by integration by parts. -/
theorem absolutelyContinuous_extend_sobolevUnitCurve (a : ScalarDomain 2) :
    AbsolutelyContinuousOnInterval (extend (sobolevUnitCurve a)) 0 1 := by
  have h := (absolutelyContinuous_sobolevSynthesis a).mono
    (show uIcc (0 : ℝ) 1 ⊆ uIcc 0 2 by
      simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  apply NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_congr h
  intro t ht
  exact (extend_sobolevUnitCurve a (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)).symm

/-- The extension's derivative agrees almost everywhere with the physical Fourier derivative. -/
theorem deriv_extend_sobolevUnitCurve_ae (a : ScalarDomain 2) :
    deriv (extend (sobolevUnitCurve a)) =ᵐ[volume.restrict (Ioc 0 1)]
      circlePullback (sobolevDerivative a) := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (deriv_sobolevSynthesis_ae a)
  change ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
    deriv (extend (sobolevUnitCurve a)) t = circlePullback (sobolevDerivative a) t
  rw [ae_restrict_iff' measurableSet_Ioc] at h ⊢
  filter_upwards [h, (show ∀ᵐ t : ℝ, t ≠ (1 : ℝ) from by simp [ae_iff, measure_singleton])] with t ht ht1
  intro hti
  have he : extend (sobolevUnitCurve a) =ᶠ[𝓝 t]
      (fun s : ℝ => sobolevSynthesis (by simp) a (s : AddCircle (2 : ℝ))) := by
    filter_upwards [Ioo_mem_nhds hti.1 (lt_of_le_of_ne hti.2 ht1)] with s hs
    exact extend_sobolevUnitCurve a ⟨hs.1.le,hs.2.le⟩
  exact he.deriv_eq.trans (ht hti)

/-- The extension's actual derivative is square integrable on the unit interval. -/
theorem memLp_deriv_extend_sobolevUnitCurve (a : ScalarDomain 2) :
    MemLp (deriv (extend (sobolevUnitCurve a))) 2 (volume.restrict (Ioc 0 1)) :=
  (memLp_congr_ae (deriv_extend_sobolevUnitCurve_ae a)).mpr
    ((memLp_sobolevDerivative a).mono_measure
      (Measure.restrict_mono_set _ (Ioc_subset_Ioc_right (by norm_num))))

theorem intervalIntegrable_deriv_extend_sobolevUnitCurve (a : ScalarDomain 2) :
    IntervalIntegrable (deriv (extend (sobolevUnitCurve a))) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    ((memLp_deriv_extend_sobolevUnitCurve a).integrable (by norm_num))

/-- The derivative variation is controlled by the physical period-two Hilbert norm. -/
theorem integral_norm_deriv_extend_sobolevUnitCurve_le (a : ScalarDomain 2) :
    (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a)) t‖) ≤ 2*Real.pi*‖a‖ := by
  have he : (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a)) t‖) =
      ∫ t in (0 : ℝ)..1, ‖circlePullback (sobolevDerivative a) t‖ := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_congr_ae ((deriv_extend_sobolevUnitCurve_ae a).fun_comp norm)
  rw [he]
  calc
    _ ≤ ∫ t in (0 : ℝ)..2, ‖circlePullback (sobolevDerivative a) t‖ :=
      intervalIntegral.integral_mono_interval le_rfl (by norm_num) (by norm_num)
        (Eventually.of_forall (fun t => norm_nonneg _)) (intervalIntegrable_circlePullback _).norm
    _ ≤ 2*‖sobolevDerivative a‖ := integral_norm_circlePullback_le _
    _ ≤ 2*Real.pi*‖a‖ := by nlinarith [norm_sobolevDerivative_le a]

end NLS.Fourier
