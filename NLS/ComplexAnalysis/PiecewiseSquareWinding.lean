import NLS.ComplexAnalysis.PiecewiseSquareContour
import NLS.ComplexAnalysis.PiecewiseContourPeriod
import NLS.ComplexAnalysis.PiecewiseContourCongruence
import NLS.ComplexAnalysis.RealCenteredPositiveDisc
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Winding of the actual squared contour

Partial fractions give its winding at w² as the sum of the original
windings at w and -w. A positive isolating circle therefore squares to a
counterclockwise circuit of its squared gap and excludes the origin.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis.PiecewiseC1Loop

theorem windingIntegral_square (Γ : PiecewiseC1Loop) (w : ℂ)
    (hΓ : Γ.Inside {z : ℂ | z ≠ w ∧ z ≠ -w}) :
    Γ.square.windingIntegral (w^2) = Γ.windingIntegral w+Γ.windingIntegral (-w) := by
  let D : Set ℂ := {z : ℂ | z ≠ w ∧ z ≠ -w}
  have hf : ContinuousOn (fun z : ℂ => (z-w)⁻¹) D :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz => sub_ne_zero.mpr hz.1)
  have hg : ContinuousOn (fun z : ℂ => (z-(-w))⁻¹) D :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz => sub_ne_zero.mpr hz.2)
  have he : Γ.integral (fun z => 2*z*(z^2-w^2)⁻¹) =
      Γ.integral (fun z => (z-w)⁻¹)+Γ.integral (fun z => (z-(-w))⁻¹) := by
    calc
      _ = Γ.integral (fun z => (z-w)⁻¹+(z-(-w))⁻¹) := by
        apply Γ.integral_congr hΓ
        intro z hz
        have hn1 : z-w ≠ 0 := sub_ne_zero.mpr hz.1
        have hn2 : z-(-w) ≠ 0 := sub_ne_zero.mpr hz.2
        have hn : z^2-w^2 ≠ 0 := by
          intro h
          rcases eq_or_eq_neg_of_sq_eq_sq _ _ (sub_eq_zero.mp h) with he | he
          · exact hz.1 he
          · exact hz.2 he
        dsimp only
        field_simp
        ring
      _ = _ := Γ.integral_add _ _ hf hg hΓ
  unfold windingIntegral normalizedIntegral
  rw [Γ.integral_square,he]
  ring

theorem windingIntegral_circle_of_not_mem_closedBall (c w : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hw : w ∉ closedBall c r) : (circle c r).windingIntegral w = 0 := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => (z-w)⁻¹) (closedBall c r) := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).inv (by
      intro he
      have heq : z = w := sub_eq_zero.mp he
      exact hw (heq ▸ hz))
  have hd := hf.differentiableOn
  have he := (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hr
  simp only [windingIntegral,normalizedIntegral,integral_circle,he,mul_zero]

theorem windingIntegral_square_circle_of_mem_ball (c w : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hw : w ∈ ball c r) (hnw : -w ∉ closedBall c r) :
    (circle c r).square.windingIntegral (w^2) = 1 := by
  have hΓ : (circle c r).Inside {z : ℂ | z ≠ w ∧ z ≠ -w} := by
    apply circle_inside_of_sphere_subset c r hr
    intro z hz
    constructor
    · intro he
      have hs : w ∈ sphere c r := he ▸ hz
      exact (mem_ball.mp hw).ne (mem_sphere.mp hs)
    · intro he
      exact hnw (sphere_subset_closedBall (he ▸ hz))
  rw [windingIntegral_square _ w hΓ,windingIntegral_circle _ _ _ hw,
    windingIntegral_circle_of_not_mem_closedBall _ _ _ hr hnw,add_zero]

theorem windingIntegral_square_circle_of_not_mem_closedBall (c w : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hw : w ∉ closedBall c r) (hnw : -w ∉ closedBall c r) :
    (circle c r).square.windingIntegral (w^2) = 0 := by
  have hΓ : (circle c r).Inside {z : ℂ | z ≠ w ∧ z ≠ -w} := by
    apply circle_inside_of_sphere_subset c r hr
    intro z hz
    exact ⟨fun he => hw (sphere_subset_closedBall (he ▸ hz)),
      fun he => hnw (sphere_subset_closedBall (he ▸ hz))⟩
  rw [windingIntegral_square _ w hΓ,windingIntegral_circle_of_not_mem_closedBall _ _ _ hr hw,
    windingIntegral_circle_of_not_mem_closedBall _ _ _ hr hnw,add_zero]

end NLS.ComplexAnalysis.PiecewiseC1Loop
