import NLS.ComplexAnalysis.QuadraticGapActionRatio

/-! # Uniform bounds for the gap-division-free action ratio -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem norm_quadraticGapActionRatio_le (H : ℂ × A → ℂ) (t s : A → ℂ) (a : A)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ θ ∈ Icc (0 : ℝ) Real.pi,
      ‖deriv (fun w => H (w,a)) (t a+sqrt (s a)*(Real.cos θ : ℂ))‖ ≤ B) :
    ‖quadraticGapActionRatio H t s a‖ ≤ 2*B := by
  have hpoint (θ : ℝ) (hθ : θ ∈ uIoc (0 : ℝ) Real.pi) :
      ‖(Real.sin θ : ℂ)^2*deriv (fun w => H (w,a)) (t a+sqrt (s a)*(Real.cos θ : ℂ))‖ ≤ B := by
    have hθ' : θ ∈ Icc (0 : ℝ) Real.pi := by
      have h := hθ
      rw [uIoc_of_le Real.pi_pos.le] at h
      exact ⟨h.1.le,h.2⟩
    have hs : ‖(Real.sin θ : ℂ)‖ ≤ 1 := by
      simpa only [norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
    rw [norm_mul,norm_pow]
    apply (mul_le_mul_of_nonneg_left (hb θ hθ') (sq_nonneg _)).trans
    nlinarith [mul_nonneg hB (sub_nonneg.mpr (show ‖(Real.sin θ : ℂ)‖^2 ≤ 1 by nlinarith [norm_nonneg (Real.sin θ : ℂ)]))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [sub_zero,abs_of_pos Real.pi_pos] at hi
  rw [quadraticGapActionRatio,parametricSineSquareCosineMean,norm_mul,norm_div,norm_mul,norm_neg,
    norm_ofNat,norm_I,mul_one,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2/Real.pi)).trans_eq
  field_simp

end NLS.ComplexAnalysis
