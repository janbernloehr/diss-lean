import NLS.ZakharovShabat.NLSRiccatiTruncation
import NLS.ComplexAnalysis.PolynomialFunctionBounds

/-! # Uniform all-order Riccati residual estimates

Finite truncations are actual smooth functions. Their differential
residuals have the expected inverse-frequency order, uniformly in space
on one period and in all complex spectral directions.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The actual finite inverse-frequency expansion of the component ratio. -/
def nlsRiccatiApproximation (a b : ℝ → ℂ) (N : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, nlsRiccatiDensity a b k x*w^(k+1)

theorem nlsRiccatiApproximation_eq_eval (a b : ℝ → ℂ) (N : ℕ) (w : ℂ) (x : ℝ) :
    nlsRiccatiApproximation a b N w x =
      w*(nlsRiccatiTruncation a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w := by
  rw [nlsRiccatiApproximation,nlsRiccatiTruncation,PowerSeries.eval₂_trunc_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [nlsRiccatiSeries,PowerSeries.coeff_mk]
  change nlsRiccatiDensity a b k x*w^(k+1) = w*(nlsRiccatiDensity a b k x*w^k)
  ring

theorem hasDerivAt_nlsRiccatiApproximation (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (w : ℂ) (x : ℝ) :
    HasDerivAt (nlsRiccatiApproximation a b N w)
      (w*(nlsRiccatiDerivativeTruncation a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w) x := by
  have hd := HasDerivAt.fun_sum (u := Finset.range N) (fun k _ =>
    (((contDiff_infty_iff_deriv.mp (contDiff_nlsRiccatiDensity a b ha hb k)).1 x).hasDerivAt).mul_const (w^(k+1)))
  convert! hd using 1
  rw [nlsRiccatiDerivativeTruncation,PowerSeries.eval₂_trunc_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [nlsRiccatiDerivativeSeries,PowerSeries.coeff_mk]
  change w*(deriv (nlsRiccatiDensity a b k) x*w^k) = deriv (nlsRiccatiDensity a b k) x*w^(k+1)
  ring

private theorem continuous_coeff_C (f : ℝ → ℂ) (hf : Continuous f) (n : ℕ) :
    Continuous ((Polynomial.C f).coeff n) := by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hf
  · exact continuous_const

private theorem continuous_coeff_X_pow (m n : ℕ) :
    Continuous ((Polynomial.X^m : Polynomial (ℝ → ℂ)).coeff n) := by
  rw [Polynomial.coeff_X_pow]
  split_ifs <;> exact continuous_const

theorem continuous_coeff_nlsRiccatiTruncation (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N n : ℕ) :
    Continuous ((nlsRiccatiTruncation a b N).coeff n) := by
  rw [coeff_nlsRiccatiTruncation]
  split_ifs
  · exact (contDiff_nlsRiccatiDensity a b ha hb n).continuous
  · exact continuous_const

theorem continuous_coeff_nlsRiccatiResidualPolynomial (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N n : ℕ) :
    Continuous ((nlsRiccatiResidualPolynomial a b N).coeff n) := by
  have hR := continuous_coeff_nlsRiccatiTruncation a b ha hb N
  have hD (k : ℕ) : Continuous ((nlsRiccatiDerivativeTruncation a b N).coeff k) := by
    rw [coeff_nlsRiccatiDerivativeTruncation]
    split_ifs
    · exact (contDiff_infty_iff_deriv.mp (contDiff_nlsRiccatiDensity a b ha hb k)).2.continuous
    · exact continuous_const
  have hX (k : ℕ) : Continuous ((Polynomial.X : Polynomial (ℝ → ℂ)).coeff k) := by
    simpa only [pow_one] using continuous_coeff_X_pow 1 k
  have hDX := continuous_polynomial_function_coeff_mul _ _ hD hX n
  have hRR := continuous_polynomial_function_coeff_mul _ _ hR hR
  have hquad := continuous_polynomial_function_coeff_mul _ _ (continuous_coeff_C a ha.continuous) hRR
  have hquadX := continuous_polynomial_function_coeff_mul _ _ hquad (continuous_coeff_X_pow 2) n
  simpa only [nlsRiccatiResidualPolynomial,Polynomial.coeff_sub,Polynomial.coeff_add] using!
    (((hR n).add (continuous_coeff_C b hb.continuous n)).sub hDX).sub hquadX

/-- The exact differential residual is the evaluated residual polynomial. -/
theorem nlsRiccatiApproximation_residual_eq (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (w : ℂ) (hw : w ≠ 0) (x : ℝ) :
    deriv (nlsRiccatiApproximation a b N w) x - w⁻¹*nlsRiccatiApproximation a b N w x - b x +
      a x*(nlsRiccatiApproximation a b N w x)^2 =
      -(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w := by
  rw [(hasDerivAt_nlsRiccatiApproximation a b ha hb N w x).deriv,nlsRiccatiApproximation_eq_eval]
  simp only [nlsRiccatiResidualPolynomial,Polynomial.eval₂_sub,Polynomial.eval₂_add,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X]
  change _ = -(_ + b x - _*w - a x*(_*_)*w^2)
  field_simp
  ring

/-- A uniform error bound on the whole unit disc of inverse frequencies. -/
theorem exists_nlsRiccatiApproximation_residual_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 →
      ‖deriv (nlsRiccatiApproximation a b N w) x - w⁻¹*nlsRiccatiApproximation a b N w x - b x +
        a x*(nlsRiccatiApproximation a b N w x)^2‖ ≤ C*‖w‖^N := by
  obtain ⟨C,hC,hbound⟩ := exists_polynomial_function_power_bound _
    (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N) N (X_pow_dvd_nlsRiccatiResidualPolynomial a b N)
  refine ⟨C,hC,?_⟩
  intro x hx w hw hnorm
  rw [nlsRiccatiApproximation_residual_eq a b ha hb N w hw x,norm_neg]
  exact hbound x hx w hnorm

/-- The approximation itself is uniformly of first inverse-frequency order. -/
theorem exists_nlsRiccatiApproximation_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖nlsRiccatiApproximation a b N w x‖ ≤ C*‖w‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_polynomial_function_power_bound _
    (continuous_coeff_nlsRiccatiTruncation a b ha hb N) 0 (by simp)
  refine ⟨C,hC,?_⟩
  intro x hx w hw
  have he : ‖(nlsRiccatiTruncation a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖ ≤ C := by
    simpa only [pow_zero,mul_one] using hbound x hx w hw
  rw [nlsRiccatiApproximation_eq_eval,norm_mul]
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg w)).trans_eq (mul_comm _ _)

/-- The residual in the original spectral variable is uniformly
`O((2*|z|)^(-N))` over one spatial period, in every spectral direction. -/
theorem exists_nlsRiccatiApproximation_spectral_residual_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖deriv (nlsRiccatiApproximation a b N (2*I*z)⁻¹) x -
        2*I*z*nlsRiccatiApproximation a b N (2*I*z)⁻¹ x - b x +
        a x*(nlsRiccatiApproximation a b N (2*I*z)⁻¹ x)^2‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨C,hC,hbound⟩ := exists_nlsRiccatiApproximation_residual_bound a b ha hb N
  refine ⟨C,hC,?_⟩
  intro x hx z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw : (2*I*z)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz0)
  have hn : ‖(2*I*z)⁻¹‖ = (2*‖z‖)⁻¹ := by simp
  have hnorm : ‖(2*I*z)⁻¹‖ ≤ 1 := by
    rw [hn]
    apply inv_le_one_of_one_le₀
    linarith
  have h := hbound x hx _ hw hnorm
  simpa only [inv_inv,hn,div_eq_mul_inv,inv_pow] using h

end NLS.ZakharovShabat
