import NLS.Fourier.UnitIntervalMemLpMoments

/-! # Physically bounded multipliers on interval L2 data

A bounded continuous physical multiplier preserves interval L2 membership and bounds the norm of the actual Fourier coefficients.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- A continuous bounded physical multiplier preserves interval L2 data.
Only its bound on the physical period is needed. -/
theorem memLp_unitInterval_bounded_mul (f P : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (hP : Continuous P)
    (K : ℝ) (hbound : ∀ x ∈ Icc (0:ℝ) 1, ‖P x‖ ≤ K) :
    MemLp (fun x => P x*f x) 2 (volume.restrict (Ioc 0 1)) := by
  apply (hf.norm.const_mul K).mono' (hP.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change ‖P x*f x‖ ≤ K*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le,hx.2⟩) (norm_nonneg _)

/-- The same physical multiplier bound controls the norm of the actual
Fourier coefficients, for arbitrary interval L2 densities. -/
theorem norm_unitIntervalMemLpCoefficients_bounded_mul_le (f P : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (hP : Continuous P)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ x ∈ Icc (0:ℝ) 1, ‖P x‖ ≤ K) :
    ‖unitIntervalMemLpCoefficients (fun x => P x*f x)
      (memLp_unitInterval_bounded_mul f P hf hP K hbound)‖ ≤
      K*‖unitIntervalMemLpCoefficients f hf‖ := by
  let hp := memLp_unitInterval_bounded_mul f P hf hP K hbound
  have hsq : ‖unitIntervalMemLpCoefficients (fun x => P x*f x) hp‖^2 ≤
      K^2*‖unitIntervalMemLpCoefficients f hf‖^2 := by
    rw [norm_sq_unitIntervalMemLpCoefficients,norm_sq_unitIntervalMemLpCoefficients,
      ← intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_ae (hp.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      ((hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (K^2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hbound x ⟨hx.1.le,hx.2⟩) 2) (sq_nonneg _)
  rw [← mul_pow] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp hsq

end NLS.Fourier
