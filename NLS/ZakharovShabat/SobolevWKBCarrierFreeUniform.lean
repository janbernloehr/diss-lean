import NLS.ZakharovShabat.SobolevWKBCarrierUniform
import Mathlib.Analysis.Complex.Exponential

/-! # Uniform comparison of WKB and free carriers

The difference from the free exponential has one inverse-frequency power uniformly on original Sobolev balls and horizontal strips.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The carrier differs from its free exponential by one inverse-frequency
power uniformly on an original Hs source ball and horizontal spectral strip. -/
theorem exists_uniform_nlsWKBCarrier_free_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ x ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖nlsWKBCarrier a b N z x-exp (-I*z*x)‖ ≤ C*‖(2*I*z)⁻¹‖ := by
  obtain ⟨A,hA,ha⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨B,hB,hb⟩ := exists_uniform_nlsRiccatiApproximation_bound s N hNs R hR
  refine ⟨Real.exp H*(A*B)*Real.exp (A*B),by positivity,?_⟩
  intro ab hab a b hca hcb hpa hpb hfa hfb x hx z hzn hzH
  let w : ℂ := (2*I*z)⁻¹
  have hw : ‖w‖ ≤ 1 := by
    change ‖(2*I*z)⁻¹‖ ≤ 1
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  let J : ℂ := ∫ t in (0:ℝ)..x, a t*nlsRiccatiApproximation a b N w t
  have hJ : ‖J‖ ≤ A*B*‖w‖ := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (C := A*B*‖w‖) (f := fun t => a t*nlsRiccatiApproximation a b N w t) (by
        intro t _
        rw [norm_mul]
        exact (mul_le_mul (ha ab hab a b hca hcb hpa hpb hfa hfb t)
          (hb ab hab a b hca hcb hpa hpb hfa hfb w hw t) (norm_nonneg _) hA).trans_eq (by ring))
    simp only [sub_zero,abs_of_nonneg hx.1] at hi
    exact hi.trans (mul_le_of_le_one_right (by positivity) hx.2)
  have hJ' : ‖J‖ ≤ A*B := hJ.trans (mul_le_of_le_one_right (mul_nonneg hA hB) hw)
  have he : ‖exp J-1‖ ≤ A*B*Real.exp (A*B)*‖w‖ := by
    have h := norm_exp_sub_sum_le_norm_mul_exp J 1
    simp only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,pow_one] at h
    exact h.trans ((mul_le_mul hJ (Real.exp_le_exp.mpr hJ') (Real.exp_pos _).le
      (by positivity)).trans_eq (by ring))
  have hf : ‖exp (-I*z*x)‖ ≤ Real.exp H := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hr : (-I*z*(x:ℂ)).re = z.im*x := by simp [Complex.mul_re]
    rw [hr]
    exact (le_abs_self _).trans (by
      rw [abs_mul,abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) hx.2).trans hzH)
  have hid : nlsWKBCarrier a b N z x-exp (-I*z*x) = exp (-I*z*x)*(exp J-1) := by
    rw [nlsWKBCarrier,exp_add]
    change exp (-I*z*x)*exp J-exp (-I*z*x) = _
    ring
  rw [hid,norm_mul]
  exact (mul_le_mul hf he (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)

end NLS.ZakharovShabat
