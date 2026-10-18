import NLS.ZakharovShabat.SobolevWKBLeadingForcedComparison

/-! # The explicit leading oscillatory integral

The free response is exactly the oscillatory integral of the top Riccati density, with a uniform integral norm bound.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The free exponential is bounded uniformly over the physical period
and a horizontal spectral strip. -/
theorem norm_exp_neg_I_mul_strip_le (z : ℂ) (H : ℝ) (hzH : |z.im| ≤ H)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖exp (-I*z*x)‖ ≤ Real.exp H := by
  rw [norm_exp]
  apply Real.exp_le_exp.mpr
  have hr : (-I*z*(x:ℂ)).re = z.im*x := by simp [Complex.mul_re]
  rw [hr]
  exact (le_abs_self _).trans (by
    rw [abs_mul,abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hx.2).trans hzH)

/-- The leading scalar forcing has the expected order-N integral bound
uniform on the original source ball. -/
theorem exists_uniform_nlsWKBLeadingScalar_integral_bound
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, |z.im| ≤ H →
        (∫ x in (0:ℝ)..1, ‖nlsWKBLeadingScalar a b N z x‖) ≤ K*‖(2*I*z)⁻¹‖^N := by
  obtain ⟨K,hK,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨K*Real.exp H,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzH
  let ρ := nlsRiccatiDensity a b N
  let w : ℂ := (2*I*z)⁻¹
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hiρ : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ K := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ‖ρ x‖*‖w‖^N*Real.exp H := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_nlsWKBLeadingScalar a b ha hb N z).norm.intervalIntegrable 0 1)
        ((hρ.norm.mul continuous_const |>.mul continuous_const).intervalIntegrable 0 1)
      intro x hx
      simp only [nlsWKBLeadingScalar,norm_mul,norm_neg,norm_I,one_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_exp_neg_I_mul_strip_le z H hzH x hx) (by positivity)
    _ = (∫ x in (0:ℝ)..1, ‖ρ x‖)*‖w‖^N*Real.exp H := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const]
    _ ≤ K*‖w‖^N*Real.exp H := by gcongr
    _ = _ := by ring

/-- The explicit free response to the leading forcing retains the actual
oscillatory integral of the top Riccati density. -/
theorem free_integral_nlsWKBLeadingScalar (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) :
    exp (I*z*t)*(∫ x in (0:ℝ)..t, exp (-I*z*x)*nlsWKBLeadingScalar a b N z x) =
      -I*((2*I*z)⁻¹)^N*exp (I*z*t)*(∫ x in (0:ℝ)..t, nlsRiccatiDensity a b N x*exp (-2*I*z*x)) := by
  have he (x : ℝ) : exp (-I*z*x)*nlsWKBLeadingScalar a b N z x =
      (-I*((2*I*z)⁻¹)^N)*(nlsRiccatiDensity a b N x*exp (-2*I*z*x)) := by
    rw [show -2*I*z*(x:ℂ) = -I*z*x+(-I*z*x) by ring,exp_add]
    unfold nlsWKBLeadingScalar
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

end NLS.ZakharovShabat
