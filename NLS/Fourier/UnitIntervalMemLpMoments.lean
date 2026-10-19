import NLS.Fourier.UnitIntervalFourierMoments

/-! # Physical Fourier moments of arbitrary interval L2 data

Moment multiplication preserves interval L2 membership and contracts the actual Fourier coefficient norm, without continuity or matching endpoint values.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Multiplication by a physical moment preserves arbitrary interval L2
membership; neither continuity nor matching endpoint values is needed. -/
theorem memLp_unitInterval_moment (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (k : ℕ) :
    MemLp (fun x : ℝ => (x:ℂ)^k*f x) 2 (volume.restrict (Ioc 0 1)) := by
  have hm : Continuous (fun x : ℝ => (x:ℂ)^k) := by fun_prop
  apply hf.norm.mono' (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change ‖(x:ℂ)^k*f x‖ ≤ ‖f x‖
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1]
  exact pow_le_one₀ hx.1.le hx.2

/-- The actual Fourier coefficients of a moment of arbitrary interval L2 data. -/
def unitIntervalMemLpMomentCoefficients (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (k : ℕ) : NLS.Coeff 2 :=
  unitIntervalMemLpCoefficients (fun x => (x:ℂ)^k*f x) (memLp_unitInterval_moment f hf k)

@[simp] theorem unitIntervalMemLpMomentCoefficients_apply (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (k : ℕ) (n : ℤ) :
    unitIntervalMemLpMomentCoefficients f hf k n = periodOneCoefficient (fun x => (x:ℂ)^k*f x) n :=
  unitIntervalMemLpCoefficients_eq_periodOneCoefficient _ _ _

/-- Each physical moment contracts the original interval Fourier L2 norm. -/
theorem norm_unitIntervalMemLpMomentCoefficients_le (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (k : ℕ) :
    ‖unitIntervalMemLpMomentCoefficients f hf k‖ ≤ ‖unitIntervalMemLpCoefficients f hf‖ := by
  have hm := memLp_unitInterval_moment f hf k
  have hsq : ‖unitIntervalMemLpMomentCoefficients f hf k‖^2 ≤ ‖unitIntervalMemLpCoefficients f hf‖^2 := by
    rw [unitIntervalMemLpMomentCoefficients,norm_sq_unitIntervalMemLpCoefficients,
      norm_sq_unitIntervalMemLpCoefficients]
    simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_ae (hm.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1]
    exact pow_le_one₀ hx.1.le hx.2
  nlinarith [norm_nonneg (unitIntervalMemLpMomentCoefficients f hf k),norm_nonneg (unitIntervalMemLpCoefficients f hf)]

end NLS.Fourier
