import NLS.ZakharovShabat.SourceStandardRootCauchyZero
import NLS.ZakharovShabat.SourceAngularCauchyEquation
import NLS.ComplexAnalysis.CirclePrimitiveBounds
import NLS.ComplexAnalysis.QuadraticRootBounds

/-! Quantitative bounds for ANY analytic solution of the actual
quadratic equation. The terminal need not be an ordinary Dirichlet
root. Constants depend on enclosing radii, never on the gap length. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem norm_sourceStandardRoot_ge_of_gap_enclosed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (a ρ : ℝ) (haρ : a < ρ)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c a)
    (w : ℂ) (hw : w ∈ sphere c ρ) :
    ρ-a ≤ ‖sourceStandardRoot hp hp1 ψ m w‖ := by
  have hsep (b : ℂ) (hb : b ∈ sourcePeriodicSegment hp hp1 ψ m) : ρ-a ≤ ‖b-w‖ := by
    have ht := dist_triangle w b c
    rw [mem_sphere.mp hw,dist_comm w b,dist_eq_norm b w] at ht
    have hb := mem_ball.mp (hgap hb)
    linarith
  have havoid : w ∉ sourcePeriodicSegment hp hp1 ψ m := by
    intro h
    have hd := mem_ball.mp (hgap h)
    rw [mem_sphere.mp hw] at hd
    linarith
  exact norm_ge_of_sq_eq_endpoint_product _ _ _ w (ρ-a) (sub_pos.mpr haρ).le
    (sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m w havoid)
    (hsep _ (left_mem_segment ℝ _ _)) (hsep _ (right_mem_segment ℝ _ _))

theorem norm_quadratic_solution_le_of_source_circle_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (H g : ℂ → ℂ) (c : ℂ) (a ρ M : ℝ) (hρ : 0 < ρ) (haρ : a < ρ) (hM : 0 ≤ M)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c a)
    (hH : AnalyticOnNhd ℂ H (closedBall c ρ))
    (heq : ∀ w ∈ sphere c ρ, sourceAngularSelectedPolynomial hp hp1 ψ m w*deriv H w+
      (w-sourceStandardRootMidpoint hp hp1 ψ m)*H w = g w)
    (hg : ∀ w ∈ sphere c ρ, ‖g w‖ ≤ M) (z : ℂ) (hz : z ∈ closedBall c a) :
    ‖H z‖ ≤ Real.pi*ρ^2*M/(ρ-a)^3 := by
  let Q := sourceStandardRoot hp hp1 ψ m
  let F : ℂ → ℂ := fun w => Q w*H w
  have hgapρ := hgap.trans (ball_subset_ball haρ.le)
  have havoid (w : ℂ) (hw : w ∈ sphere c ρ) : w ∉ sourcePeriodicSegment hp hp1 ψ m :=
    fun h => sphere_disjoint_ball.le_bot ⟨hw,hgapρ h⟩
  have hQa (w : ℂ) (hw : w ∈ sphere c ρ) := sourceStandardRoot_analyticAt hp hp1 ψ m w (havoid w hw)
  have hQne (w : ℂ) (hw : w ∈ sphere c ρ) := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m w (havoid w hw)
  have hFd (w : ℂ) (hw : w ∈ sphere c ρ) : HasDerivAt F (g w/Q w) w := by
    have hsq : (fun v => Q v^2) =ᶠ[𝓝 w]
        quadraticRootPolynomial (sourceStandardRootMidpoint hp hp1 ψ m)
          ((canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) m)^2/4) := by
      filter_upwards [(isClosed_sourcePeriodicSegment hp hp1 ψ m).isOpen_compl.mem_nhds (havoid w hw)] with v hv
      rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ m v hv]
      exact (sourceAngularSelectedPolynomial_eq_endpoint_factor hp hp1 ψ m v).symm
    exact hasDerivAt_root_mul_of_quadratic_equation Q H _ _ (g w) w (hQa w hw) (hQne w hw)
      hsq (hH w (sphere_subset_closedBall hw)) (heq w hw)
  have hF : ContinuousOn F (sphere c ρ) := fun w hw =>
    ((hQa w hw).mul (hH w (sphere_subset_closedBall hw))).continuousAt.continuousWithinAt
  have hQbound (w : ℂ) (hw : w ∈ sphere c ρ) : ρ-a ≤ ‖Q w‖ :=
    norm_sourceStandardRoot_ge_of_gap_enclosed hp hp1 ψ m c a ρ haρ hgap w hw
  have hfbound (w : ℂ) (hw : w ∈ sphere c ρ) : ‖g w/Q w‖ ≤ M/(ρ-a) := by
    rw [norm_div]
    exact div_le_div₀ hM (hg w hw) (sub_pos.mpr haρ) (hQbound w hw)
  have hzρ : z ∈ ball c ρ := mem_ball.mpr ((mem_closedBall.mp hz).trans_lt haρ)
  have he : circleCauchyTransform (fun w => (F w-F (c+ρ))/Q w) c ρ z = H z := by
    rw [circleCauchyTransform_div_sourceStandardRoot_sub_const hp hp1 ψ m c ρ hρ hgapρ F hF _ z hzρ]
    unfold circleCauchyTransform
    have hc : (∮ w in C(c,ρ), (F w/Q w)/(w-z)) = ∮ w in C(c,ρ), H w/(w-z) := by
      apply circleIntegral.integral_congr hρ.le
      intro w hw
      dsimp only [F]
      rw [mul_div_cancel_left₀ _ (hQne w hw)]
    rw [hc,circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty hzρ
      hH.continuousOn (fun w hw => (hH w (ball_subset_closedBall hw.1)).differentiableAt),
      ← mul_assoc,inv_mul_cancel₀ (by simp [Real.pi_ne_zero]),one_mul]
  have hb := norm_circleCauchyTransform_primitive_quotient_le F (fun w => g w/Q w) Q c ρ a
    (ρ-a) (M/(ρ-a)) hρ.le haρ (sub_pos.mpr haρ) (by positivity) hFd hfbound hQbound z hz
  rw [he] at hb
  convert hb using 1
  field_simp

end NLS.ZakharovShabat
