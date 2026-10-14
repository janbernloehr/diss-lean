import NLS.ComplexAnalysis.PiecewiseContourPeriod

/-! # Winding formulas expressed using the original outer circle -/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

/-- The outer boundary period computes every loop integral in the entire
cut disk. The enclosing inner radius is only used to construct a primitive. -/
theorem integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut
    (Γ : PiecewiseC1Loop) (f : ℂ → ℂ) (d c : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) (K : Set ℂ) (hKclosed : IsClosed K)
    (hc : c ∈ K) (hKstar : StarConvex ℝ c K) (hKinner : K ⊆ ball d r)
    (hf : AnalyticOnNhd ℂ f (closedBall d R \ K))
    (hΓ : Γ.Inside (ball d R \ K)) :
    Γ.integral f = (∮ z in C(d,R), f z)*Γ.windingIntegral c := by
  have hAnn : closedBall d R \ ball d r ⊆ closedBall d R \ K :=
    fun _ hz => ⟨hz.1,fun h => hz.2 (hKinner h)⟩
  have he := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR.le (s := ∅) countable_empty (hf.continuousOn.mono hAnn) (by
      intro z hz
      apply (hf z ?_).differentiableAt
      exact ⟨ball_subset_closedBall hz.1.1,fun h => hz.1.2 (ball_subset_closedBall (hKinner h))⟩)
  rw [he]
  exact Γ.integral_eq_circleIntegral_mul_winding_of_starConvex_cut
    f d c r R hr hrR K hKclosed hc hKstar hKinner hf hΓ

end PiecewiseC1Loop
end NLS.ComplexAnalysis
