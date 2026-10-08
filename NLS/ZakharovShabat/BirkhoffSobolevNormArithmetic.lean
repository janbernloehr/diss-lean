import NLS.ZakharovShabat.SourceBirkhoffSobolevCoordinates

/-! # Passing from squared action estimates to the norm estimates of Theorem 23.1 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- A squared estimate yields a strictly positive uniform norm constant. -/
theorem norm_bound_of_two_squared_terms (x y z c : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hc : 0 ≤ c)
    (h : x^2 ≤ 2*c^2*(y^2+z^2)) : x ≤ (2*c+1)*(y+z) := by
  have hsum : 0 ≤ y^2+z^2 := by positivity
  have hsum2 : y^2+z^2 ≤ (y+z)^2 := by nlinarith [mul_nonneg hy hz]
  have hs : x^2 ≤ (2*c*(y+z))^2 := calc
    _ ≤ 2*c^2*(y^2+z^2) := h
    _ ≤ (2*c)^2*(y^2+z^2) := by nlinarith [mul_nonneg (sq_nonneg c) hsum]
    _ ≤ (2*c)^2*(y+z)^2 := mul_le_mul_of_nonneg_left hsum2 (sq_nonneg _)
    _ = _ := (mul_pow _ _ _).symm
  have hb : 0 ≤ 2*c*(y+z) := by positivity
  have hroot : x ≤ 2*c*(y+z) := by nlinarith
  nlinarith

/-- The bracket polynomial in the action bound is controlled by the Birkhoff H¹ norm. -/
theorem action_remainder_le_birkhoff_norm_sq (e : ℕ) (S M Q Q0 : ℝ)
    (hS : 0 ≤ S) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hQsq : Q^2 = 2*S) (hQ0sq : Q0^2 = 2*M) :
    (1+S)^e*M ≤ ((1+Q)^e*Q0)^2 := by
  have hbase : 1+S ≤ (1+Q)^2 := by nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+S) hbase e
  have hm : M ≤ Q0^2 := by nlinarith
  calc
    _ ≤ ((1+Q)^2)^e*Q0^2 := mul_le_mul hp hm hM (by positivity)
    _ = _ := by rw [mul_pow,← pow_mul,← pow_mul]; congr 1; congr 1; omega

end NLS.ZakharovShabat
