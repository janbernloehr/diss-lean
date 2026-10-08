import NLS.SequenceSpaces.SpectralWeightInterpolation

/-! # Explicit polynomial bounds for interpolated Sobolev weights -/
noncomputable section
namespace NLS.SpectralWeight

/-- Interpolation is bounded by the Sobolev weight at the next real argument. -/
theorem scaledSobolev_realExtension_le (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (t : ℝ) (ht : 0 ≤ t) :
    (scaledSobolev c s hc hs).realExtension t ≤ (1+c*(t+1))^s := by
  have h := ((scaledSobolev c s hc hs).realExtension_bounds t).2
  simp only [scaledSobolev_apply,abs_of_nonneg ht,Int.cast_add,Int.cast_natCast,Int.cast_one,
    abs_of_nonneg (by positivity : 0 ≤ (⌊t⌋₊:ℝ)+1)] at h
  apply h.trans (Real.rpow_le_rpow (by positivity) _ hs)
  have hf := Nat.floor_le ht
  nlinarith

/-- At the quadratic source cutoff the interpolated factor has the exact real exponent 2s. -/
theorem scaledSobolev_realExtension_sixteen_le (c s : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (P : ℝ) (hP : 0 ≤ P) :
    (scaledSobolev c s hc hs).realExtension (16*P^2) ≤ (1+17*c)^s*(1+P)^(2*s) := by
  have h := scaledSobolev_realExtension_le c s hc hs (16*P^2) (by positivity)
  have hbase : 1+c*(16*P^2+1) ≤ (1+17*c)*(1+P^2) := by
    nlinarith [mul_nonneg hc (sq_nonneg P)]
  have hquad : 1+P^2 ≤ (1+P)^2 := by nlinarith
  have hb := hbase.trans (mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 1+17*c))
  calc
    _ ≤ (1+c*(16*P^2+1))^s := h
    _ ≤ ((1+17*c)*(1+P)^2)^s := Real.rpow_le_rpow (by positivity) hb hs
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_natCast_mul (by positivity),Nat.cast_ofNat]

/-- The exact physical π-normalized Sobolev factor satisfies the same bound. -/
theorem piSobolev_realExtension_sixteen_le (s : ℝ) (hs : 0 ≤ s) (P : ℝ) (hP : 0 ≤ P) :
    (piSobolev s hs).realExtension (16*P^2) ≤ (1+17*Real.pi)^s*(1+P)^(2*s) :=
  scaledSobolev_realExtension_sixteen_le Real.pi s Real.pi_pos.le hs P hP

/-- Squaring the factor doubles the real exponent, with no rounding of the order. -/
theorem piSobolev_realExtension_sixteen_sq_le (s : ℝ) (hs : 0 ≤ s) (P : ℝ) (hP : 0 ≤ P) :
    ((piSobolev s hs).realExtension (16*P^2))^2 ≤
      ((1+17*Real.pi)^s)^2*(1+P)^(4*s) := by
  have h := pow_le_pow_left₀ ((piSobolev s hs).realExtension_pos _).le
    (piSobolev_realExtension_sixteen_le s hs P hP) 2
  have hp : ((1+P)^(2*s))^2 = (1+P)^(4*s) := by
    rw [← Real.rpow_mul_natCast (by positivity),Nat.cast_ofNat,show (2*s)*(2:ℝ)=4*s by ring]
  rw [mul_pow,hp] at h
  exact h

end NLS.SpectralWeight
