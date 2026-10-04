import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.CosineSegmentGeometry

/-! # Linear bounds for the boundary values of a quadratic-root primitive

The cosine substitution turns the quadratic Cauchy equation into an
ordinary derivative identity. The mean value estimate on [0, pi] then
bounds the sine-weighted primitive by pi times its numerator bound.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem norm_sine_mul_of_quadratic_equation
    (H g : ℂ → ℂ) (τ δ : ℂ) (Ω : Set ℂ)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hH : AnalyticOnNhd ℂ H Ω)
    (heq : ∀ z ∈ Ω, quadraticRootPolynomial τ (δ^2) z*deriv H z+(z-τ)*H z = g z)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z ∈ segment ℝ (τ-δ) (τ+δ), ‖g z‖ ≤ B)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    ‖δ*(Real.sin θ:ℂ)*H (τ+δ*(Real.cos θ:ℂ))‖ ≤ B*Real.pi := by
  let T : ℂ → ℂ := fun e => τ+δ*Complex.cos e
  let P : ℂ → ℂ := fun e => δ*Complex.sin e*H (T e)
  have hd (e : ℝ) : HasDerivAt P (g (T e)) (e:ℂ) := by
    have he : T (e:ℂ) ∈ Ω := by
      apply hgap
      simpa only [T,cosineGapPoint] using cosineGapPoint_real_mem_segment τ δ e
    have hder := ((Complex.hasDerivAt_sin (e:ℂ)).const_mul δ).mul
      (((hH (T e) he).differentiableAt.hasDerivAt).comp (e:ℂ)
        (((Complex.hasDerivAt_cos (e:ℂ)).const_mul δ).const_add τ))
    have hval : (δ*Complex.cos (e:ℂ))*H (T e)+δ*Complex.sin (e:ℂ)*(deriv H (T e)*(δ*(-Complex.sin (e:ℂ)))) = g (T e) := by
      rw [← heq (T e) he]
      dsimp only [T,quadraticRootPolynomial]
      linear_combination -(δ^2*deriv H (τ+δ*Complex.cos (e:ℂ)))*(Complex.sin_sq_add_cos_sq (e:ℂ))
    simpa only [Function.comp_apply, Pi.mul_apply, hval] using! hder
  have hreal (e : ℝ) (_he : e ∈ Icc (0:ℝ) Real.pi) :
      HasDerivWithinAt (fun t : ℝ => P (t:ℂ)) (g (T e)) (Icc (0:ℝ) Real.pi) e := (hd e).comp_ofReal.hasDerivWithinAt
  have hb (e : ℝ) (_he : e ∈ Icc (0:ℝ) Real.pi) : ‖g (T e)‖ ≤ B := by
    apply hbound
    simpa only [T,cosineGapPoint] using cosineGapPoint_real_mem_segment τ δ e
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hreal hb (convex_Icc (0:ℝ) Real.pi)
    (show Real.pi ∈ Icc (0:ℝ) Real.pi from ⟨Real.pi_pos.le,le_rfl⟩) hθ
  have hdist : ‖θ-Real.pi‖ ≤ Real.pi := by rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hθ.2)]; linarith [hθ.1]
  have hz : P (Real.pi:ℂ) = 0 := by simp only [P,← Complex.ofReal_sin,Real.sin_pi,ofReal_zero,mul_zero,zero_mul]
  rw [hz,sub_zero] at h
  simpa only [P,T,← Complex.ofReal_sin,← Complex.ofReal_cos] using h.trans (mul_le_mul_of_nonneg_left hdist hB)

end NLS.ComplexAnalysis
