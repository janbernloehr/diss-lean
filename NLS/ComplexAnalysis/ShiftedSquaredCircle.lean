import NLS.ComplexAnalysis.PiecewiseC1Loop
import NLS.ComplexAnalysis.HolomorphicPathPullback
import NLS.ComplexAnalysis.RealCenteredCircleHomotopy

/-! # The actual shifted quadratic image of a frequency circle

The contour is an actual smooth closed path and its integral is the
ordinary curve integral. The exact differential 2z is proved by the
chain rule, including integrability equivalence.
-/
noncomputable section
open Set Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

def shiftedSquaredCirclePath (c : ℂ) (R : ℝ) (s : ℂ) :=
  (circlePath c R).map (show Continuous (fun z : ℂ => z^2-s) from
    (continuous_id.pow 2).sub continuous_const)

theorem shiftedSquaredCirclePath_contDiffOn (c : ℂ) (R : ℝ) (s : ℂ) :
    ContDiffOn ℝ 2 (shiftedSquaredCirclePath c R s).extend (Icc 0 1) := by
  apply (((circlePath_contDiffOn c R).pow 2).sub contDiffOn_const).congr
  intro t ht
  rw [Path.extend_apply _ ht,Path.extend_apply _ ht]
  rfl

def shiftedSquaredCircle (c : ℂ) (R : ℝ) (s : ℂ) : PiecewiseC1Loop :=
  PiecewiseC1Loop.ofPath (shiftedSquaredCirclePath c R s)
    ((shiftedSquaredCirclePath_contDiffOn c R s).of_le (by norm_num))

theorem shiftedSquaredCircle_integral (c : ℂ) (R : ℝ) (s : ℂ) (f : ℂ → ℂ) :
    (shiftedSquaredCircle c R s).integral f =
      ∮ z in C(c,R), f (z^2-s)*(2*z) := by
  rw [shiftedSquaredCircle,PiecewiseC1Loop.integral_ofPath]
  have hd (z : ℂ) : HasDerivAt (fun w : ℂ => w^2-s) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const s
  have he := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2-s)*(2*z)) (fun z : ℂ => z^2-s) (fun z : ℂ => 2*z)
    ((continuous_id.pow 2).sub continuous_const) (circlePath c R)
    ((circlePath_contDiffOn c R).of_le (by norm_num)) (fun _ _ => hd _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at he
  exact he

theorem shiftedSquaredCircle_inside (c : ℂ) (R : ℝ) (s : ℂ) {D : Set ℂ}
    (hR : 0 ≤ R) (hD : ∀ z ∈ Metric.sphere c R, z^2-s ∈ D) :
    (shiftedSquaredCircle c R s).Inside D := by
  intro i u
  exact hD (circleMap c R ((2*Real.pi)*(u:ℝ)))
    (circleMap_mem_sphere c hR _)

theorem shiftedSquaredCircle_winding (c R : ℝ) (s x : ℂ) (hR : 0 < R) (hRc : R < c)
    (hx : x ∈ Metric.ball (c:ℂ) R) :
    (shiftedSquaredCircle (c:ℂ) R s).windingIntegral (x^2-s) = 1 := by
  have hpos (z : ℂ) (hz : z ∈ Metric.closedBall (c:ℂ) R) : 0 < z.re := by
    have hb := re_bounds_of_mem_realCenteredClosedBall hz
    linarith
  have hxpos := hpos x (Metric.ball_subset_closedBall hx)
  let A := {z : ℂ | 0 < z.re}
  let f : ℂ → ℂ := fun z => (z-x)⁻¹
  let g : ℂ → ℂ := fun z => (z+x)⁻¹
  have hne (z : ℂ) (hz : z ∈ Metric.sphere (c:ℂ) R) : z-x ≠ 0 := by
    intro he
    have hzx := sub_eq_zero.mp he
    have hb := Metric.mem_ball.mp hx
    have hs := Metric.mem_sphere.mp hz
    rw [hzx] at hs
    linarith
  have hga : AnalyticOnNhd ℂ g A := by
    intro z hz
    have hn : z+x ≠ 0 := by
      intro he
      have hi := congrArg Complex.re he
      simp only [add_re,zero_re] at hi
      change 0 < z.re at hz
      linarith
    exact (analyticAt_id.add analyticAt_const).inv hn
  have hfi : CircleIntegrable f (c:ℂ) R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have ha : AnalyticAt ℂ f z := (analyticAt_id.sub analyticAt_const).inv (hne z hz)
    exact ha.continuousAt.continuousWithinAt
  have hgi : CircleIntegrable g (c:ℂ) R :=
    (hga.mono (fun z hz => hpos z (Metric.sphere_subset_closedBall hz))).continuousOn.circleIntegrable hR.le
  have hloop : (PiecewiseC1Loop.circle (c:ℂ) R).Inside A := by
    intro i u
    exact hpos (circleMap (c:ℂ) R ((2*Real.pi)*(u:ℝ)))
      (circleMap_mem_closedBall _ hR.le _)
  have hzero := (PiecewiseC1Loop.circle (c:ℂ) R).integral_eq_zero_of_convex g A
    (isOpen_lt continuous_const continuous_re) (convex_halfSpace_re_gt 0) hga.differentiableOn hloop
  rw [PiecewiseC1Loop.integral_circle] at hzero
  have he : EqOn (fun z : ℂ => (z^2-s-(x^2-s))⁻¹*(2*z))
      (fun z => f z+g z) (Metric.sphere (c:ℂ) R) := by
    intro z hz
    have hn : z+x ≠ 0 := by
      intro h
      have hi := congrArg Complex.re h
      simp only [add_re,zero_re] at hi
      linarith [hpos z (Metric.sphere_subset_closedBall hz)]
    have hm : z^2-s-(x^2-s) = (z-x)*(z+x) := by ring
    dsimp [f,g]
    rw [hm,mul_inv]
    field_simp [hne z hz,hn]
    ring
  rw [PiecewiseC1Loop.windingIntegral,PiecewiseC1Loop.normalizedIntegral,
    shiftedSquaredCircle_integral,circleIntegral.integral_congr hR.le he,
    circleIntegral.integral_add hfi hgi,circleIntegral.integral_sub_inv_of_mem_ball hx,hzero,add_zero]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])

end NLS.ComplexAnalysis
