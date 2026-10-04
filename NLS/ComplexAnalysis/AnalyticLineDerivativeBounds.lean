import NLS.ComplexAnalysis.AnalyticLineDerivativeLinear

/-! # Quantitative bounds for analytic line derivatives

A bound on a source ball gives a linear bound in the direction and an
operator-norm bound for the constructed complex-linear directional map.
These estimates do not assume Fréchet differentiability.
-/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A Cauchy circle inside the bounded source ball controls every direction. -/
theorem norm_lineDeriv_le_of_ball_bound
    (f : E → F) (U : Set E) (hU : IsOpen U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U))
    (a : E) (R M : ℝ) (hR : 0 < R) (hball : ball a R ⊆ U)
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) (v : E) :
    ‖lineDeriv ℂ f a v‖ ≤ (2*M/R)*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, lineDeriv_zero]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let r : ℝ := R/(2*‖v‖)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrmul : r*‖v‖ = R/2 := by dsimp [r]; field_simp
  have hinto (t : ℂ) (ht : t ∈ closedBall 0 r) : a+t • v ∈ ball a R := by
    rw [mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul]
    have htn : ‖t‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using ht
    calc
      ‖t‖*‖v‖ ≤ r*‖v‖ := mul_le_mul_of_nonneg_right htn (norm_nonneg _)
      _ = R/2 := hrmul
      _ < R := by linarith
  have hopen : IsOpen ((fun t : ℂ => a+t • v) ⁻¹' U) :=
    hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have he := Complex.cderiv_eq_deriv hopen
    (hl a (hball (mem_ball_self hR)) v).differentiableOn hr
    (fun t ht => hball (hinto t ht))
  change ‖deriv (fun t : ℂ => f (a+t • v)) 0‖ ≤ _
  rw [← he]
  calc
    _ ≤ M/r := Complex.norm_cderiv_le hr (fun t ht => hb _ (hinto t (sphere_subset_closedBall ht)))
    _ = (2*M/R)*‖v‖ := by dsimp [r]; field_simp

/-- The bounded complex-linear directional derivative has the same
quantitative operator-norm estimate. -/
theorem norm_lineDerivativeCLM_le_of_ball_bound
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U))
    (a : E) (ha : a ∈ U) (R M : ℝ) (hR : 0 < R) (hball : ball a R ⊆ U)
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) :
    ‖lineDerivativeCLM f U hU hf hl a ha‖ ≤ 2*M/R := by
  have hM : 0 ≤ M := (norm_nonneg (f a)).trans (hb a (mem_ball_self hR))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_lineDeriv_le_of_ball_bound f U hU hl a R M hR hball hb

end NLS.ComplexAnalysis
