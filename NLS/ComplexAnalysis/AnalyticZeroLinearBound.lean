import NLS.ComplexAnalysis.UniformAnalyticBallVariation

/-! # A quantitative local linear norm bound for an analytic zero -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_analytic_zero_linear_bound [CompleteSpace F] (f : E → F)
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ AnalyticOnNhd ℂ f (ball (0 : E) δ) ∧
      ∀ x ∈ ball (0 : E) δ, ‖f x‖ ≤ C*‖x‖ := by
  obtain ⟨r,hr,han⟩ := hf.exists_ball_analyticOnNhd
  have hnb : ∀ᶠ x in nhds (0 : E), f x ∈ ball (0 : F) 1 := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [h0]
    exact ball_mem_nhds _ zero_lt_one
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp hnb
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  have hRa : AnalyticOnNhd ℂ f (ball (0 : E) R) := han.mono (ball_subset_ball (min_le_left _ _))
  have hb (x : E) (hx : x ∈ ball (0 : E) R) : ‖f x‖ ≤ 1 :=
    (mem_ball_zero_iff.mp (hsub (ball_subset_ball (min_le_right _ _) hx))).le
  refine ⟨R/2,4/R,by positivity,by positivity,hRa.mono (ball_subset_ball (by linarith)),?_⟩
  intro x hx
  have he := norm_sub_base_le_of_analytic_ball_bound f 0 hR hRa hb hx
  simpa only [h0,sub_zero,mul_one] using he

end NLS.ComplexAnalysis
