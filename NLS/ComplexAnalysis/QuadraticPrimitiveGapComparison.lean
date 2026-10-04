import NLS.ComplexAnalysis.QuadraticPrimitiveGapBound

/-! # Comparing a quadratic-root primitive with a constant multiple of the root

Subtracting a constant from the analytic Cauchy quotient subtracts its
linear numerator from the quadratic differential equation. The boundary
error is therefore bounded directly by the numerator defect, without
division by the gap length. Collapsed gaps are included.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem norm_sine_mul_sub_of_quadratic_equation
    (H g : ℂ → ℂ) (τ δ c : ℂ) (Ω : Set ℂ)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hH : AnalyticOnNhd ℂ H Ω)
    (heq : ∀ z ∈ Ω, quadraticRootPolynomial τ (δ^2) z*deriv H z+(z-τ)*H z = g z)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ segment ℝ (τ-δ) (τ+δ), ‖g z-(z-τ)*c‖ ≤ B)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    ‖δ*(Real.sin θ:ℂ)*(H (τ+δ*(Real.cos θ:ℂ))-c)‖ ≤ B*Real.pi := by
  apply norm_sine_mul_of_quadratic_equation (fun z => H z-c)
    (fun z => g z-(z-τ)*c) τ δ Ω hgap
    (fun z hz => (hH z hz).sub analyticAt_const) _ B hB hbound θ hθ
  intro z hz
  rw [deriv_sub_const, ← heq z hz]
  ring

end NLS.ComplexAnalysis
