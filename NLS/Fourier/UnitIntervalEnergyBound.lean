import NLS.Fourier.SobolevEnergy
import NLS.Fourier.IntervalCoefficientScaling

/-! # Time-energy and Fourier bounds from pointwise unit-interval bounds

The Fourier coefficients use the unit interval and its actual `2πn`
frequencies. No endpoint matching is required for the Parseval estimate.
-/

noncomputable section
open Set MeasureTheory
namespace NLS.Fourier

/-- A supremum bound controls the unnormalized square energy on an interval of length one. -/
theorem integral_sq_unit_le (f : ℝ → ℂ) (hf : Continuous f) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A) :
    (∫ t in (0 : ℝ)..1, ‖f t‖^2) ≤ A^2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((hf.norm.pow 2).intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
    (fun t ht => (sq_le_sq₀ (norm_nonneg _) hA).mpr (hb t ht))
  simpa using h

/-- The actual H¹ energy is bounded by the separate function and derivative bounds. -/
theorem intervalH1Energy_unit_le (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) :
    intervalH1Energy f 0 1 ≤ A^2+D^2 :=
  add_le_add (integral_sq_unit_le f hf.continuous A hA hb)
    (integral_sq_unit_le (deriv f) (contDiff_one_iff_deriv.mp hf).2 D hD hd)

/-- A bound for the actual classical H¹ time norm. -/
theorem sqrt_intervalH1Energy_unit_le (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv f t‖ ≤ D) :
    Real.sqrt (intervalH1Energy f 0 1) ≤ A+D := by
  apply (Real.sqrt_le_left (add_nonneg hA hD)).mpr
  exact (intervalH1Energy_unit_le f hf A D hA hD hb hd).trans (by nlinarith)

/-- The actual unit-interval Fourier coefficients of a continuous function are square summable. -/
theorem memlp_unitIntervalFourierCoefficient (f : ℝ → ℂ) (hf : Continuous f) :
    Memℓp (intervalFourierCoefficient 1 f) 2 := by
  rw [← periodTwoCoefficient_intervalDilation_eq (by norm_num : (0 : ℝ) < 1)]
  exact memlp_periodTwoCoefficient (memLp_two_interval
    (hf.comp (continuous_const.mul continuous_id)) 0 2 (by norm_num))

/-- Square-summable coefficients of the original, possibly nonperiodic, unit-interval function. -/
def unitIntervalL2Coefficients (f : ℝ → ℂ) (hf : Continuous f) : Coeff 2 :=
  ⟨intervalFourierCoefficient 1 f,memlp_unitIntervalFourierCoefficient f hf⟩

@[simp] theorem unitIntervalL2Coefficients_apply (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) :
    unitIntervalL2Coefficients f hf n = intervalFourierCoefficient 1 f n := rfl

/-- Parseval turns a time supremum bound into a bound for the entire coefficient ℓ² norm. -/
theorem norm_unitIntervalL2Coefficients_le (f : ℝ → ℂ) (hf : Continuous f)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ A) :
    ‖unitIntervalL2Coefficients f hf‖ ≤ A := by
  let g := intervalDilation (1/2) f
  have hg : Continuous g := hf.comp (continuous_const.mul continuous_id)
  have hm := memLp_two_interval hg 0 2 (by norm_num)
  have he : unitIntervalL2Coefficients f hf = periodTwoL2Coefficients g hm := by
    ext n
    exact (periodTwoCoefficient_intervalDilation (by norm_num : (0 : ℝ) < 1) f n).symm
  rw [he]
  apply (sq_le_sq₀ (norm_nonneg _) hA).mp
  rw [norm_sq_periodTwoL2Coefficients]
  have hgb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : ‖g t‖ ≤ A := by
    simpa only [g,intervalDilation,div_eq_mul_inv,one_mul,mul_comm] using
      hb (t/2) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hi : (∫ t in (0 : ℝ)..2, ‖g t‖^2) ≤ 2*A^2 := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 2)
      ((hg.norm.pow 2).intervalIntegrable 0 2) (continuous_const.intervalIntegrable 0 2)
      (fun t ht => (sq_le_sq₀ (norm_nonneg _) hA).mpr (hgb t ht))
    simpa [g,intervalDilation,div_eq_mul_inv,one_mul,mul_comm] using h
  linarith

end NLS.Fourier
