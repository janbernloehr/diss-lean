import NLS.ZakharovShabat.NLSWKBApproximation

/-! # Carrier bounds retaining the exact free growth

The finite Riccati correction is uniformly bounded at every complex frequency
of modulus at least one. The carrier and reciprocal retain opposite free
exponential factors, rather than a common strip-dependent constant.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The exact free exponential factors control the carrier and its reciprocal
on the full complex frequency plane, uniformly on one spatial period. -/
theorem exists_nlsWKBCarrier_weighted_bounds (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖nlsWKBCarrier a b N z x‖ ≤ B * Real.exp (z.im*x) ∧
        ‖(nlsWKBCarrier a b N z x)⁻¹‖ ≤ B * Real.exp (-z.im*x) := by
  obtain ⟨C,hC,hR⟩ := exists_nlsRiccatiApproximation_bound a b ha hb N
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) ha.continuous.continuousOn
  have hA0 : 0 ≤ A := (norm_nonneg (a 0)).trans (hA 0 ⟨le_rfl,zero_le_one⟩)
  refine ⟨Real.exp (A*C),Real.exp_pos _,?_⟩
  intro x hx z hz
  have hn : ‖(2*I*z)⁻¹‖ = (2*‖z‖)⁻¹ := by simp
  have hw : ‖(2*I*z)⁻¹‖ ≤ 1 := by
    rw [hn]
    apply inv_le_one_of_one_le₀
    linarith
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t‖ ≤ A*C := by
    rw [norm_mul]
    have hRt := (hR t ht _ hw).trans (mul_le_of_le_one_right hC.le hw)
    exact mul_le_mul (hA t ht) hRt (norm_nonneg _) hA0
  have hint : ‖∫ t in (0 : ℝ)..x, a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t‖ ≤ A*C := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x) (C := A*C)
      (f := fun t => a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t) (by
        intro t ht
        rw [uIoc_of_le hx.1] at ht
        exact hpoint t ⟨ht.1.le,ht.2.trans hx.2⟩)
    simp only [sub_zero,abs_of_nonneg hx.1] at h
    exact h.trans (mul_le_of_le_one_right (mul_nonneg hA0 hC.le) hx.2)
  have hfree : (-I*z*(x : ℂ)).re = z.im*x := by simp [Complex.mul_re]
  constructor
  · rw [nlsWKBCarrier,norm_exp,add_re,hfree,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [(Complex.re_le_norm _).trans hint]
  · rw [norm_inv,nlsWKBCarrier,norm_exp,← Real.exp_neg,add_re,hfree,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [(neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hint)]

end NLS.ZakharovShabat
