import NLS.ComplexAnalysis.QuadraticEnergyLoop
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

/-! Every point inside a positive real-centered frequency disk has
winding one under the actual oriented quadratic image of its boundary. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem windingIntegral_quadraticEnergyCircle_one_of_positive
    (b R : ℝ) (c a : ℂ) (hpos : 0 < b-R) (ha : a ∈ ball (b:ℂ) R) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (b:ℂ) R) c).windingIntegral (a^2-c) = 1 := by
  have hare : 0 < a.re := by
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall ha)
    linarith [hb.1]
  have hna : -a ∉ closedBall (b:ℂ) R := by
    intro he
    have hb := re_bounds_of_mem_realCenteredClosedBall he
    simp only [neg_re] at hb
    linarith [hb.1]
  exact windingIntegral_quadraticEnergyCircle_one (b:ℂ) a c R ha hna

end NLS.ComplexAnalysis
