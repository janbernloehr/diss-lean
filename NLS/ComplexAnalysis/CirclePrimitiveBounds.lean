import NLS.ComplexAnalysis.CircleArcCurveIntegral
import NLS.ComplexAnalysis.CircleCauchyTransform
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Quantitative circle bounds for primitives and Cauchy transforms

A derivative bound on a circle controls the primitive's variation from
a fixed point by the length of a half circle. Cauchy projection then
bounds its normalized quotient on every smaller concentric disc.
The estimates use no information about the function inside the circle.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_sub_le_circle_derivative_bound
    (P g : ℂ → ℂ) (c : ℂ) (ρ M : ℝ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hP : ∀ w ∈ sphere c ρ, HasDerivAt P (g w) w)
    (hg : ∀ w ∈ sphere c ρ, ‖g w‖ ≤ M) (w : ℂ) (hw : w ∈ sphere c ρ) :
    ‖P w-P (c+ρ)‖ ≤ Real.pi*ρ*M := by
  let F : ℝ → ℂ := fun θ => P (circleMap c ρ θ)
  have hd (θ : ℝ) : HasDerivAt F ((circleMap 0 ρ θ*I)*g (circleMap c ρ θ)) θ := by
    have h := ((hP _ (circleMap_mem_sphere c hρ θ)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt
      θ (hasDerivAt_circleMap c ρ θ)
    exact h
  have hbound (θ : ℝ) : ‖deriv F θ‖ ≤ ρ*M := by
    rw [(hd θ).deriv,norm_mul,norm_mul,norm_circleMap_zero,norm_I,mul_one,abs_of_nonneg hρ]
    exact mul_le_mul_of_nonneg_left (hg _ (circleMap_mem_sphere c hρ θ)) hρ
  let θ := arg (w-c)
  have hθ : θ ∈ Icc (-Real.pi) Real.pi := ⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩
  have h0 : (0:ℝ) ∈ Icc (-Real.pi) Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (-Real.pi) Real.pi) => (hd t).differentiableAt)
    (fun t _ => hbound t) (convex_Icc (-Real.pi) Real.pi) h0 hθ
  have heq : circleMap c ρ θ = w := by
    have hn : ‖w-c‖ = ρ := by simpa only [dist_eq_norm,mem_sphere] using hw
    rw [← hn,circleMap_norm_arg]
    ring
  have hzero : circleMap c ρ 0 = c+ρ := by simp [circleMap]
  change ‖P (circleMap c ρ θ)-P (circleMap c ρ 0)‖ ≤ _ at hmv
  rw [heq,hzero,sub_zero,Real.norm_eq_abs] at hmv
  exact hmv.trans (by
    have h := mul_le_mul_of_nonneg_left (abs_arg_le_pi (w-c)) (mul_nonneg hρ hM)
    dsimp only [θ] at hmv ⊢
    nlinarith)

theorem norm_circleCauchyTransform_le_of_circle_bound
    (f : ℂ → ℂ) (c : ℂ) (ρ a M : ℝ) (hρ : 0 ≤ ρ) (haρ : a < ρ) (hM : 0 ≤ M)
    (hf : ∀ w ∈ sphere c ρ, ‖f w‖ ≤ M) (z : ℂ) (hz : z ∈ closedBall c a) :
    ‖circleCauchyTransform f c ρ z‖ ≤ ρ*M/(ρ-a) := by
  have hd : 0 < ρ-a := sub_pos.mpr haρ
  have hkernel (w : ℂ) (hw : w ∈ sphere c ρ) : ‖f w/(w-z)‖ ≤ M/(ρ-a) := by
    have htri := dist_triangle w z c
    have hwρ := mem_sphere.mp hw
    have hza := mem_closedBall.mp hz
    have hlow : ρ-a ≤ ‖w-z‖ := by
      rw [hwρ,dist_eq_norm w z] at htri
      linarith
    rw [norm_div]
    exact div_le_div₀ hM (hf w hw) hd hlow
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ hkernel
  change ‖circleCauchyTransform f c ρ z‖ ≤ ρ*(M/(ρ-a)) at h
  simpa only [mul_div_assoc] using h

/-- Removing a constant and dividing by a uniformly nonzero circle root
turns a primitive derivative bound into an explicit interior bound. -/
theorem norm_circleCauchyTransform_primitive_quotient_le
    (P g Q : ℂ → ℂ) (c : ℂ) (ρ a δ M : ℝ)
    (hρ : 0 ≤ ρ) (haρ : a < ρ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hP : ∀ w ∈ sphere c ρ, HasDerivAt P (g w) w)
    (hg : ∀ w ∈ sphere c ρ, ‖g w‖ ≤ M)
    (hQ : ∀ w ∈ sphere c ρ, δ ≤ ‖Q w‖) (z : ℂ) (hz : z ∈ closedBall c a) :
    ‖circleCauchyTransform (fun w => (P w-P (c+ρ))/Q w) c ρ z‖ ≤
      Real.pi*ρ^2*M/(δ*(ρ-a)) := by
  have hbound (w : ℂ) (hw : w ∈ sphere c ρ) :
      ‖(P w-P (c+ρ))/Q w‖ ≤ Real.pi*ρ*M/δ := by
    rw [norm_div]
    exact div_le_div₀ (by positivity)
      (norm_sub_le_circle_derivative_bound P g c ρ M hρ hM hP hg w hw) hδ (hQ w hw)
  have h := norm_circleCauchyTransform_le_of_circle_bound _ c ρ a (Real.pi*ρ*M/δ)
    hρ haρ (by positivity) hbound z hz
  convert h using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end NLS.ComplexAnalysis
