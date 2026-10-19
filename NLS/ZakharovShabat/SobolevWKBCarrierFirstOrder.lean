import NLS.ZakharovShabat.SobolevRiccatiApproximationFirstOrder
import NLS.ZakharovShabat.SobolevWKBFirstCarrierExpansion

/-! # The first mass correction for every positive WKB carrier

Every positive-order WKB carrier has the same signed mass correction with a quadratic error on original Sobolev balls.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Every positive WKB truncation has the same first mass correction,
with a uniform quadratic inverse-frequency error on the original Hs ball.
This includes the maximal truncation order N=s. -/
theorem exists_uniform_nlsWKBCarrier_first_order_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ x ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖nlsWKBCarrier a b N z x-
          exp (-I*z*x)*(1-(2*I*z)⁻¹*nlsWKBMassPrimitive a b x)‖ ≤ C*‖(2*I*z)⁻¹‖^2 := by
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s (hN.trans hNs) R hR
  obtain ⟨B,hB,happrox⟩ := exists_uniform_nlsRiccatiApproximation_bound s N hNs R hR
  obtain ⟨C,hC,hfirst⟩ := exists_uniform_nlsRiccatiApproximation_first_order_bound s N hN hNs R hR
  refine ⟨Real.exp H*((A*B)^2*Real.exp (A*B)+A*C),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb x hx z hz hzH
  let w := (2*I*z)⁻¹
  let P := nlsWKBMassPrimitive a b x
  let J := ∫ t in (0:ℝ)..x, a t*nlsRiccatiApproximation a b N w t
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hJ : ‖J‖ ≤ A*B*‖w‖ := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (C := A*B*‖w‖) (f := fun t => a t*nlsRiccatiApproximation a b N w t) (by
        intro t _
        rw [norm_mul]
        exact (mul_le_mul (hpot ab hab a b ha hb hpa hpb hca hcb t)
          (happrox ab hab a b ha hb hpa hpb hca hcb w hw t) (norm_nonneg _) hA).trans_eq (by ring))
    simp only [sub_zero,abs_of_nonneg hx.1] at hi
    exact hi.trans (mul_le_of_le_one_right (by positivity) hx.2)
  have hJbound : ‖J‖ ≤ A*B := hJ.trans (mul_le_of_le_one_right (mul_nonneg hA hB) hw)
  have hJlinear : ‖J+w*P‖ ≤ A*C*‖w‖^2 := by
    have hr (k : ℕ) : Continuous (nlsRiccatiDensity a b k) := (contDiff_nlsRiccatiDensity a b ha hb k).continuous
    have happroxcont : Continuous (fun t => nlsRiccatiApproximation a b N w t) := by
      unfold nlsRiccatiApproximation
      fun_prop
    have hc₁ : Continuous (fun t => a t*nlsRiccatiApproximation a b N w t) := ha.continuous.mul happroxcont
    have hc₂ : Continuous (fun t => w*(a t*b t)) := continuous_const.mul (ha.continuous.mul hb.continuous)
    have hi : (∫ t in (0:ℝ)..x, a t*(nlsRiccatiApproximation a b N w t+b t*w)) = J+w*P := by
      have he (t : ℝ) : a t*(nlsRiccatiApproximation a b N w t+b t*w) =
          a t*nlsRiccatiApproximation a b N w t+w*(a t*b t) := by ring
      simp_rw [he]
      rw [intervalIntegral.integral_add (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
      rfl
    rw [← hi]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x)
      (C := A*C*‖w‖^2) (f := fun t => a t*(nlsRiccatiApproximation a b N w t+b t*w)) (by
        intro t _
        rw [norm_mul]
        exact (mul_le_mul (hpot ab hab a b ha hb hpa hpb hca hcb t)
          (hfirst ab hab a b ha hb hpa hpb hca hcb w hw t) (norm_nonneg _) hA).trans_eq (by ring))
    simp only [sub_zero,abs_of_nonneg hx.1] at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) hx.2)
  have hexp : ‖exp J-(1+J)‖ ≤ (A*B)^2*Real.exp (A*B)*‖w‖^2 := by
    have hh := norm_exp_sub_sum_le_norm_mul_exp J 2
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,
      Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,zero_add] at hh
    apply hh.trans
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hJ 2)
      (Real.exp_le_exp.mpr hJbound) (Real.exp_pos _).le (by positivity)).trans_eq (by ring)
  have hlin : ‖exp J-(1-w*P)‖ ≤ ((A*B)^2*Real.exp (A*B)+A*C)*‖w‖^2 := by
    have he : exp J-(1-w*P) = (exp J-(1+J))+(J+w*P) := by ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hexp hJlinear).trans_eq (by ring))
  have he : nlsWKBCarrier a b N z x-exp (-I*z*x)*(1-w*P) =
      exp (-I*z*x)*(exp J-(1-w*P)) := by
    rw [nlsWKBCarrier,exp_add]
    change exp (-I*z*x)*exp J-exp (-I*z*x)*(1-w*P) = _
    ring
  change ‖nlsWKBCarrier a b N z x-exp (-I*z*x)*(1-w*P)‖ ≤ _
  rw [he,norm_mul]
  exact (mul_le_mul (norm_exp_neg_I_mul_strip_le z H hzH x hx) hlin
    (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by ring)

end NLS.ZakharovShabat
