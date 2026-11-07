import NLS.SequenceSpaces.NegativeSpectralWeight

/-! Genuine polynomial source weights with a small finite head and the same
asymptotic Sobolev order. No minimum of submultiplicative weights is used. -/
noncomputable section
namespace NLS.SpectralWeight

theorem scaledSobolev_le_sobolev (c s : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hs : 0 ≤ s) (k : ℤ) :
    scaledSobolev c s hc hs k ≤ Weight.sobolev s k := by
  apply Real.rpow_le_rpow (by positivity) _ hs
  have hh := mul_le_mul_of_nonneg_right hc1 (abs_nonneg (k:ℝ))
  linarith

theorem mul_sobolev_le_scaledSobolev (c s : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hs : 0 ≤ s) (k : ℤ) :
    c^s*Weight.sobolev s k ≤ scaledSobolev c s hc.le hs k := by
  rw [Weight.sobolev_apply, ← Real.mul_rpow hc.le (by positivity)]
  apply Real.rpow_le_rpow (by positivity) _ hs
  nlinarith

/-- The combined negative-order weight is equivalent to the desired stronger
Sobolev weight,with explicit constants independent of frequency. -/
theorem scaledNegativeSobolev_bounds (c r t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (htr : t ≤ r) (k : ℤ) :
    c^(r-t)*Weight.sobolev (-t) k ≤ (scaledSobolev c (r-t) hc.le (by linarith)).negativeSobolev r k ∧
      (scaledSobolev c (r-t) hc.le (by linarith)).negativeSobolev r k ≤ Weight.sobolev (-t) k := by
  have hprod : Weight.sobolev (r-t) k*Weight.sobolev (-r) k = Weight.sobolev (-t) k := by
    simp only [Weight.sobolev_apply, ← Real.rpow_add (by positivity : 0 < 1+|(k:ℝ)|)]
    congr 1
    ring
  rw [negativeSobolev_eq_product]
  constructor
  · have hh := mul_le_mul_of_nonneg_right (mul_sobolev_le_scaledSobolev c (r-t) hc hc1 (by linarith) k)
      ((Weight.sobolev (-r)).positive k).le
    simpa only [mul_assoc, hprod] using hh
  · have hh := mul_le_mul_of_nonneg_right (scaledSobolev_le_sobolev c (r-t) hc.le hc1 (by linarith) k)
      ((Weight.sobolev (-r)).positive k).le
    simpa only [hprod] using hh

/-- An explicit scale for a given finite Fourier cutoff. -/
def inverseHeadScale (N : ℕ) : ℝ := 1/(2*(N:ℝ)+1)

theorem inverseHeadScale_pos_le_one (N : ℕ) : 0 < inverseHeadScale N ∧ inverseHeadScale N ≤ 1 := by
  unfold inverseHeadScale
  exact ⟨by positivity, (div_le_one (by positivity : 0 < 2*(N:ℝ)+1)).mpr (by linarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N])⟩

/-- Every finite head has a uniform factor-two bound,with a genuine source weight. -/
theorem scaledSobolev_inverseHeadScale_le_two (N : ℕ) (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (k : ℤ) (hk : |(k:ℝ)| ≤ 2*(N:ℝ)) :
    scaledSobolev (inverseHeadScale N) s (inverseHeadScale_pos_le_one N).1.le hs k ≤ 2 := by
  have hc := (inverseHeadScale_pos_le_one N).1
  have hh : inverseHeadScale N*|(k:ℝ)| ≤ 1 := by
    unfold inverseHeadScale
    rw [one_div_mul_eq_div]
    apply (div_le_one (by positivity : 0 < 2*(N:ℝ)+1)).mpr
    linarith
  exact (Real.rpow_le_self_of_one_le (by nlinarith [abs_nonneg (k:ℝ)]) hs1).trans (by linarith)

/-- The target negative order controls the doubled potential frequency by the
spectral gap frequency,with the original period-two normalization retained. -/
theorem scaledNegativeSobolev_double_le (c r t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : 0 ≤ t) (htr : t ≤ r) (n : ℕ) :
    (scaledSobolev c (r-t) hc.le (by linarith)).negativeSobolev r (2*(n:ℤ)) ≤ Weight.sobolev (-t) (n:ℤ) := by
  apply (scaledNegativeSobolev_bounds c r t hc hc1 htr (2*(n:ℤ))).2.trans
  change (1+|((2*(n:ℤ):ℤ):ℝ)|)^(-t) ≤ (1+|((n:ℤ):ℝ)|)^(-t)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith : -t ≤ 0)
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, abs_mul, abs_of_nonneg hnR]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

end NLS.SpectralWeight
