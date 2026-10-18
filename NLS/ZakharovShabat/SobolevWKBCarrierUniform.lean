import NLS.ZakharovShabat.SobolevRiccatiApproximationUniform
import NLS.ZakharovShabat.NLSWKBApproximation

/-! # Uniform WKB carriers on Sobolev balls

Carrier and inverse-carrier bounds hold uniformly for smooth periodic representatives of a fixed Hs source ball, for s >= 1 and N <= s.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Carrier and inverse carrier bounds depend only on the original Hs ball,
the truncation order and strip width, for smooth periodic representatives. -/
theorem exists_uniform_nlsWKBCarrier_strip_bounds (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s)
    (R : ℝ) (hR0 : 0 ≤ R) (H : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = NLS.Fourier.periodOneCoefficient a j) →
      (∀ j, ab.2.val j = NLS.Fourier.periodOneCoefficient b j) →
      ∀ x ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖nlsWKBCarrier a b N z x‖ ≤ B ∧ ‖(nlsWKBCarrier a b N z x)⁻¹‖ ≤ B := by
  obtain ⟨C,hC,hR⟩ := exists_uniform_nlsRiccatiApproximation_bound s N hNs R hR0
  obtain ⟨A,hA0,hA⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR0
  refine ⟨Real.exp (H+A*C),Real.exp_pos _,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb x hx z hz hstrip
  have hn : ‖(2*I*z)⁻¹‖ = (2*‖z‖)⁻¹ := by simp
  have hw : ‖(2*I*z)⁻¹‖ ≤ 1 := by
    rw [hn]
    apply inv_le_one_of_one_le₀
    linarith
  have hpoint (t : ℝ) :
      ‖a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t‖ ≤ A*C := by
    rw [norm_mul]
    have hRt := (hR ab hab a b ha hb hpa hpb hca hcb _ hw t).trans (mul_le_of_le_one_right hC hw)
    exact mul_le_mul (hA ab hab a b ha hb hpa hpb hca hcb t) hRt (norm_nonneg _) hA0
  have hint : ‖∫ t in (0 : ℝ)..x, a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t‖ ≤ A*C := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := A*C)
      (f := fun t => a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t) (by
        intro t _
        exact hpoint t)
    simp only [sub_zero,abs_of_nonneg hx.1] at h
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hA0 hC) hx.2)
  have hfree : |(-I*z*(x : ℂ)).re| ≤ H := by
    have he : (-I*z*(x : ℂ)).re = z.im*x := by simp [Complex.mul_re]
    rw [he,abs_mul,abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hx.2).trans hstrip
  constructor
  · rw [nlsWKBCarrier,norm_exp,add_re]
    apply Real.exp_le_exp.mpr
    exact add_le_add ((le_abs_self _).trans hfree) ((Complex.re_le_norm _).trans hint)
  · rw [norm_inv,nlsWKBCarrier,norm_exp,← Real.exp_neg,add_re]
    apply Real.exp_le_exp.mpr
    rw [neg_add]
    exact add_le_add ((neg_le_abs _).trans hfree)
      ((neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hint))

end NLS.ZakharovShabat
