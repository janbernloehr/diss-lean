import NLS.Fourier.SobolevIdentification

/-!
# Physical Sobolev energy and the weighted Fourier norm

The physical energy uses ordinary Lebesgue measure and the actual classical
derivative. Parseval retains the factor two from the period length. The weight
`1 + |n|` is equivalent to the physical `H¹` norm, with explicit bounds.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier
open ZakharovShabat

/-- The unnormalized classical `H¹` energy on a physical interval. -/
def intervalH1Energy (f : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (∫ x in a..b, ‖f x‖ ^ 2) + ∫ x in a..b, ‖deriv f x‖ ^ 2

theorem intervalH1Energy_nonneg (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ intervalH1Energy f a b := by
  apply add_nonneg <;> exact intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)

/-- Physical energy only depends on the function on the interval, even for totalized derivatives. -/
theorem intervalH1Energy_congr {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hfg : EqOn f g (Icc a b)) : intervalH1Energy f a b = intervalH1Energy g a b := by
  have hi : EqOn f g (Ioo a b) := hfg.mono Ioo_subset_Icc_self
  unfold intervalH1Energy
  congr 1
  · exact intervalIntegral.integral_congr_Ioo_of_le hab (fun x hx => by rw [hi hx])
  · exact intervalIntegral.integral_congr_Ioo_of_le hab
      (fun x hx => by rw [hi.deriv isOpen_Ioo hx])

private theorem hasSum_sq (a : Coeff 2) : HasSum (fun n => ‖a n‖ ^ 2) (‖a‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a

/-- Parseval for the physical function with the unnormalized length-two measure. -/
theorem integral_sq_sobolevSynthesis (a : ScalarDomain 2) :
    (∫ x in (0 : ℝ)..2, ‖sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))‖ ^ 2) =
      2 * ‖scalarInclusion a‖ ^ 2 := by
  have h := hasSum_sq_periodTwoCoefficient
    (memLp_two_interval (continuous_sobolevSynthesis (by simp) a) 0 2 (by norm_num))
  simp only [periodTwoCoefficient_sobolevSynthesis] at h
  have hraw := hasSum_sq (scalarInclusion a)
  simp only [scalarInclusion_apply] at hraw
  have he := h.unique hraw
  nlinarith

/-- Parseval for the actual derivative, including its factor `π`. -/
theorem integral_sq_deriv_sobolevSynthesis (a : ScalarDomain 2) :
    (∫ x in (0 : ℝ)..2, ‖deriv
      (fun t : ℝ => sobolevSynthesis (by simp) a (t : AddCircle (2 : ℝ))) x‖ ^ 2) =
      2 * ‖derivative a‖ ^ 2 := by
  have h := hasSum_sq_periodTwoCoefficient (memLp_deriv_sobolevSynthesis a)
  simp only [periodTwoCoefficient_deriv_sobolevSynthesis] at h
  have he := h.unique (hasSum_sq (derivative a))
  nlinarith

/-- Exact physical energy in terms of the unweighted coefficients and derivative. -/
theorem intervalH1Energy_sobolevSynthesis (a : ScalarDomain 2) :
    intervalH1Energy (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 =
      2 * (‖scalarInclusion a‖ ^ 2 + ‖derivative a‖ ^ 2) := by
  rw [intervalH1Energy, integral_sq_sobolevSynthesis, integral_sq_deriv_sobolevSynthesis]
  ring

private theorem weighted_term (a : ScalarDomain 2) (n : ℤ) :
    ‖WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a n‖ ^ 2 =
      (1 + |(n : ℝ)|) ^ 2 * ‖a.val n‖ ^ 2 := by
  simp only [WeightedCoeff.weightEquiv_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Weight.sobolev_apply, Real.rpow_one,
    abs_of_nonneg (by positivity : 0 ≤ 1 + |(n : ℝ)|), mul_pow]

private theorem derivative_term (a : ScalarDomain 2) (n : ℤ) :
    ‖derivative a n‖ ^ 2 = Real.pi ^ 2 * |(n : ℝ)| ^ 2 * ‖a.val n‖ ^ 2 := by
  simp [derivative_apply, Complex.norm_intCast, Real.norm_eq_abs, mul_pow]

/-- The weighted norm is controlled by the physical function and derivative coefficients. -/
theorem norm_sq_le_two_mul_graphEnergy (a : ScalarDomain 2) :
    ‖a‖ ^ 2 ≤ 2 * (‖scalarInclusion a‖ ^ 2 + ‖derivative a‖ ^ 2) := by
  have hp : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  apply hasSum_le _ (hasSum_sq (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a))
    (((hasSum_sq (scalarInclusion a)).add (hasSum_sq (derivative a))).mul_left 2)
  intro n
  dsimp only
  rw [weighted_term, derivative_term, scalarInclusion_apply]
  have hn : (1 + |(n : ℝ)|) ^ 2 ≤ 2 * (1 + Real.pi ^ 2 * |(n : ℝ)| ^ 2) := by
    nlinarith [sq_nonneg (|(n : ℝ)| - 1), mul_le_mul_of_nonneg_right hp (sq_nonneg |(n : ℝ)|)]
  nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖a.val n‖)]

/-- The coefficient graph energy is controlled by the weighted norm. -/
theorem graphEnergy_le_pi_sq_mul_norm_sq (a : ScalarDomain 2) :
    ‖scalarInclusion a‖ ^ 2 + ‖derivative a‖ ^ 2 ≤ Real.pi ^ 2 * ‖a‖ ^ 2 := by
  have hp : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  apply hasSum_le _ ((hasSum_sq (scalarInclusion a)).add (hasSum_sq (derivative a)))
    ((hasSum_sq (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a)).mul_left (Real.pi ^ 2))
  intro n
  dsimp only
  rw [weighted_term, derivative_term, scalarInclusion_apply]
  have hn : 1 + Real.pi ^ 2 * |(n : ℝ)| ^ 2 ≤ Real.pi ^ 2 * (1 + |(n : ℝ)|) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (abs_nonneg (n : ℝ))]
  nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg ‖a.val n‖)]

/-- Two-sided comparison with the ordinary, unnormalized physical `H¹` energy. -/
theorem intervalH1Energy_sobolevSynthesis_bounds (a : ScalarDomain 2) :
    ‖a‖ ^ 2 ≤ intervalH1Energy
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 ∧
    intervalH1Energy
      (fun x : ℝ => sobolevSynthesis (by simp) a (x : AddCircle (2 : ℝ))) 0 2 ≤
      2 * Real.pi ^ 2 * ‖a‖ ^ 2 := by
  rw [intervalH1Energy_sobolevSynthesis]
  exact ⟨norm_sq_le_two_mul_graphEnergy a, by nlinarith [graphEnergy_le_pi_sq_mul_norm_sq a]⟩

/-- The same physical comparison applies directly to an arbitrary classical periodic function. -/
theorem intervalH1Energy_sobolevCoefficients_bounds (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f) :
    ‖sobolevCoefficients f hf‖ ^ 2 ≤ intervalH1Energy (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 0 2 ∧
    intervalH1Energy (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 0 2 ≤
      2 * Real.pi ^ 2 * ‖sobolevCoefficients f hf‖ ^ 2 := by
  simpa only [sobolevSynthesis_sobolevCoefficients] using
    intervalH1Energy_sobolevSynthesis_bounds (sobolevCoefficients f hf)

end NLS.Fourier
