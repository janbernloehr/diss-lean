import NLS.ComplexAnalysis.ComplexCircleTerminal
import NLS.ComplexAnalysis.QuadraticCosinePrimitive

/-! Real terminals fixing BOTH divisor coordinates on a closed segment.
Sine zeros at the two endpoints require no division by the root. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem exists_real_cosine_terminal_with_root (τ δ μ r : ℂ) (hδ : δ ≠ 0)
    (hμ : μ ∈ segment ℝ (τ-δ) (τ+δ))
    (hr : r^2 = quadraticRootPolynomial τ (δ^2) μ) :
    ∃ t : ℝ, cosineGapPoint τ δ (t:ℂ) = μ ∧ -I*δ*Complex.sin (t:ℂ) = r := by
  have hcircle : (I*r/δ)^2+((μ-τ)/δ)^2 = 1 := by
    rw [div_pow,div_pow,← add_div]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hδ)).mpr
    rw [mul_pow,I_sq]
    dsimp only [quadraticRootPolynomial] at hr
    linear_combination -hr
  obtain ⟨e,hsin,hcos⟩ := exists_angle_of_sine_sq_add_cosine_sq _ _ hcircle
  have hpoint : cosineGapPoint τ δ e = μ := by
    dsimp only [cosineGapPoint]
    rw [hcos,mul_div_cancel₀ _ hδ]
    ring
  have him : e.im = 0 := im_eq_zero_of_cosineGapPoint_mem_segment τ δ e hδ (hpoint ▸ hμ)
  have he : (e.re:ℂ) = e := by simpa [him] using Complex.re_add_im e
  refine ⟨e.re,he ▸ hpoint,?_⟩
  rw [he,hsin]
  field_simp [hδ]
  linear_combination -r*I_sq

theorem cosine_phase_terminal_mod_two_pi (τ δ μ r e f : ℂ) (hδ : δ ≠ 0)
    (he : cosineGapPoint τ δ e = μ) (hf : cosineGapPoint τ δ f = μ)
    (hre : -I*δ*Complex.sin e = r) (hrf : -I*δ*Complex.sin f = r) :
    ∃ k : ℤ, e-f = (k:ℂ)*(2*(Real.pi:ℂ)) := by
  have hcos : Complex.cos e = Complex.cos f := by
    apply mul_left_cancel₀ hδ
    dsimp only [cosineGapPoint] at he hf
    linear_combination he-hf
  have hsin : Complex.sin e = Complex.sin f :=
    mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hδ) (hre.trans hrf.symm)
  obtain ⟨k,hk⟩ := eq_mod_two_pi_of_cos_eq_of_sin_eq e f hcos hsin
  exact ⟨k,by linear_combination hk⟩

end NLS.ComplexAnalysis
