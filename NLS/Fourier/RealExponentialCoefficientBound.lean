import NLS.Fourier.ShiftedExponentialFourier

/-! # Actual Fourier coefficients at arbitrary real exponential frequencies -/
noncomputable section
open Complex MeasureTheory
namespace NLS.Fourier

/-- The frequency difference in the unit-interval Fourier integral is r-2*pi*k. -/
theorem intervalFourierCoefficient_exponential_real (r : ℝ) (k : ℤ)
    (hr : r-2*Real.pi*k ≠ 0) :
    intervalFourierCoefficient 1 (unitIntervalExponential (r : ℂ)) k =
      (exp (I*((r-2*Real.pi*k : ℝ) : ℂ))-1)/(I*((r-2*Real.pi*k : ℝ) : ℂ)) := by
  have hc : I*((r-2*Real.pi*k : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hr)
  have he : (fun t : ℝ => unitIntervalExponential (r : ℂ) t*wave (-k) (2*t)) =
      fun t : ℝ => exp ((I*((r-2*Real.pi*k : ℝ) : ℂ))*t) := by
    funext t
    unfold unitIntervalExponential wave
    rw [← exp_add]
    congr 1
    push_cast
    ring
  simp only [intervalFourierCoefficient,div_one,Complex.ofReal_one,one_mul]
  rw [he]
  simpa using (integral_exp_mul_complex (a := 0) (b := 1) hc)

/-- Real frequencies separated from the Fourier mode have the sharp elementary 2/gap bound. -/
theorem norm_intervalFourierCoefficient_exponential_real_le (r : ℝ) (k : ℤ)
    (hr : r-2*Real.pi*k ≠ 0) :
    ‖intervalFourierCoefficient 1 (unitIntervalExponential (r : ℂ)) k‖ ≤
      2/|r-2*Real.pi*k| := by
  rw [intervalFourierCoefficient_exponential_real r k hr,norm_div,norm_mul,
    norm_I,one_mul,Complex.norm_real]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc
    _ ≤ ‖exp (I*((r-2*Real.pi*k : ℝ) : ℂ))‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp]

end NLS.Fourier
