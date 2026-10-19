import NLS.ZakharovShabat.NLSWKBFirstCarrier
import NLS.ZakharovShabat.SobolevWKBSecondColumn

/-! # Uniform first-order expansion of both WKB carriers

Both carriers have the explicit signed mass corrections with quadratic inverse-frequency errors controlled by original Sobolev norms.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

private theorem nlsWKBFirstCarrier_linear_error
    (a b : ℝ → ℂ) (z : ℂ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
    (H K : ℝ) (hK : 0 ≤ K) (hz : 1 ≤ ‖z‖) (hzH : |z.im| ≤ H)
    (hP : ‖nlsWKBMassPrimitive a b x‖ ≤ K) :
    ‖nlsWKBCarrier a b 1 z x-exp (-I*z*x)*(1-(2*I*z)⁻¹*nlsWKBMassPrimitive a b x)‖ ≤
      (Real.exp H*K^2*Real.exp K)*‖(2*I*z)⁻¹‖^2 := by
  let w := (2*I*z)⁻¹
  let P := nlsWKBMassPrimitive a b x
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hJ : ‖-w*P‖ ≤ ‖w‖*K := by
    rw [norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
  have hJ' : ‖-w*P‖ ≤ K := hJ.trans (mul_le_of_le_one_left hK hw)
  have he : ‖exp (-w*P)-(1-w*P)‖ ≤ K^2*Real.exp K*‖w‖^2 := by
    have h := norm_exp_sub_sum_le_norm_mul_exp (-w*P) 2
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,
      Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,zero_add] at h
    have hsum : (1-w*P) = 1+(-w*P) := by ring
    rw [hsum]
    apply h.trans
    have hm := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hJ 2)
      (Real.exp_le_exp.mpr hJ') (Real.exp_pos _).le (by positivity : 0 ≤ (‖w‖*K)^2)
    exact hm.trans_eq (by ring)
  rw [nlsWKBCarrier_order_one,← mul_sub,norm_mul]
  exact (mul_le_mul (norm_exp_neg_I_mul_strip_le z H hzH x hx) he
    (norm_nonneg _) (Real.exp_pos H).le).trans_eq (by dsimp [w]; ring)

/-- Both first-order carriers have the exact signed mass-primitive
linear terms and uniform quadratic inverse-frequency errors on original
Sobolev balls. The primitive uses only the original Hs source norm. -/
theorem exists_uniform_nlsWKB_first_carrier_expansion_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ x ∈ Icc (0:ℝ) 1,
        ‖nlsWKBCarrier a b 1 z x-exp (-I*z*x)*(1-(2*I*z)⁻¹*nlsWKBMassPrimitive a b x)‖ ≤
          C*‖(2*I*z)⁻¹‖^2 ∧
        ‖nlsWKBCarrier (-b) (-a) 1 (-z) x-exp (I*z*x)*(1+(2*I*z)⁻¹*nlsWKBMassPrimitive a b x)‖ ≤
          C*‖(2*I*z)⁻¹‖^2 := by
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  refine ⟨Real.exp H*(A^2)^2*Real.exp (A^2),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH x hx
  have hP : ‖nlsWKBMassPrimitive a b x‖ ≤ A^2 := norm_nlsWKBMassPrimitive_le a b A hA
    (hpot ab hab a b ha hb hpa hpb hca hcb)
    (hpot (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab) b a hb ha hpb hpa hcb hca) x hx
  refine ⟨nlsWKBFirstCarrier_linear_error a b z x hx H (A^2) (sq_nonneg _) hz hzH hP,?_⟩
  have h := nlsWKBFirstCarrier_linear_error (-b) (-a) (-z) x hx H (A^2) (sq_nonneg _)
    (by simpa using hz) (by simpa using hzH) (by simpa using hP)
  simpa only [nlsWKBMassPrimitive_signedSwap,mul_neg,neg_mul,inv_neg,neg_neg,sub_neg_eq_add,norm_neg] using h

end NLS.ZakharovShabat
