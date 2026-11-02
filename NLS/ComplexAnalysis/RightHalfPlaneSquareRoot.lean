import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # The energy square root on a positive frequency chart -/
noncomputable section
namespace NLS.ComplexAnalysis

/-- Squaring and taking the principal root cancel in the open right
half-plane. This fixes the sign in frequency-to-energy contour pullbacks. -/
theorem sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) : Complex.sqrt (z^2) = z := by
  have hs : (Complex.sqrt (z^2))^2 = z^2 := by
    have h := Complex.cpow_nat_inv_pow (z^2) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · exact h
  have hr : 0 ≤ (Complex.sqrt (z^2)).re := by
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  rw [h, Complex.neg_re] at hr
  linarith

end NLS.ComplexAnalysis
