import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.ContinuousSmoothLoopHomotopy

/-!
# Vertical recentering of circles

The radius changes with the imaginary part of the center so that the
circle's two intersections with the real axis remain fixed. This
provides a continuous family of smooth loops suited to real-axis cuts.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Move the center of a circle vertically toward its real part. -/
def verticalCircleCenter (c : ℂ) (t : ℝ) : ℂ :=
  (c.re : ℂ) + ((t*c.im : ℝ) : ℂ) * Complex.I

/-- Radius that preserves the real-axis cross-section when the center
moves vertically. -/
def verticalCircleRadius (c : ℂ) (q t : ℝ) : ℝ :=
  Real.sqrt (q^2 + (t*c.im)^2)

theorem verticalCircleCenter_zero (c : ℂ) :
    verticalCircleCenter c 0 = (c.re : ℂ) := by
  simp [verticalCircleCenter]

theorem verticalCircleCenter_one (c : ℂ) :
    verticalCircleCenter c 1 = c := by
  apply Complex.ext <;> simp [verticalCircleCenter]

theorem verticalCircleRadius_zero (c : ℂ) (q : ℝ) (hq : 0 ≤ q) :
    verticalCircleRadius c q 0 = q := by
  simp [verticalCircleRadius, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]

theorem verticalCircleRadius_one (c : ℂ) (q R : ℝ)
    (hR : 0 ≤ R) (hsq : q^2+c.im^2=R^2) :
    verticalCircleRadius c q 1 = R := by
  dsimp [verticalCircleRadius]
  simp only [one_mul]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hR]

/-- A circle containing a real point in its interior has a positive
real-axis cross-section radius. -/
theorem exists_verticalCircleRadius_of_real_point_mem_ball
    (c z : ℂ) (R : ℝ) (hz : z.im = 0)
    (hball : z ∈ ball c R) :
    ∃ q : ℝ, 0 < q ∧ q^2+c.im^2=R^2 := by
  have hdist : (dist z c)^2 = (z.re-c.re)^2+c.im^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  have hR : dist z c < R := mem_ball.mp hball
  have hsq : 0 < R^2-c.im^2 := by
    nlinarith [dist_nonneg (x := z) (y := c), sq_nonneg (z.re-c.re)]
  refine ⟨Real.sqrt (R^2-c.im^2), Real.sqrt_pos.2 hsq, ?_⟩
  rw [Real.sq_sqrt hsq.le]
  ring

/-- On the real axis, an off-axis disc has the same open
cross-section as its vertical projection. -/
theorem real_mem_ball_verticalCircle_iff
    (c z : ℂ) (q R : ℝ) (hz : z.im = 0)
    (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hsq : q^2+c.im^2=R^2) :
    z ∈ ball c R ↔ z ∈ ball (c.re:ℂ) q := by
  have hdist : (dist z c)^2 = (z.re-c.re)^2+c.im^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  have hdist0 : (dist z (c.re:ℂ))^2 = (z.re-c.re)^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  constructor
  · intro h
    apply mem_ball.mpr
    have hlt := mem_ball.mp h
    nlinarith [dist_nonneg (x := z) (y := c),
      dist_nonneg (x := z) (y := (c.re:ℂ))]
  · intro h
    apply mem_ball.mpr
    have hlt := mem_ball.mp h
    nlinarith [dist_nonneg (x := z) (y := c),
      dist_nonneg (x := z) (y := (c.re:ℂ))]

/-- The same cross-section identity for closed discs. -/
theorem real_mem_closedBall_verticalCircle_iff
    (c z : ℂ) (q R : ℝ) (hz : z.im = 0)
    (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hsq : q^2+c.im^2=R^2) :
    z ∈ closedBall c R ↔ z ∈ closedBall (c.re:ℂ) q := by
  have hdist : (dist z c)^2 = (z.re-c.re)^2+c.im^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  have hdist0 : (dist z (c.re:ℂ))^2 = (z.re-c.re)^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  constructor
  · intro h
    apply mem_closedBall.mpr
    have hle := mem_closedBall.mp h
    nlinarith [dist_nonneg (x := z) (y := c),
      dist_nonneg (x := z) (y := (c.re:ℂ))]
  · intro h
    apply mem_closedBall.mpr
    have hle := mem_closedBall.mp h
    nlinarith [dist_nonneg (x := z) (y := c),
      dist_nonneg (x := z) (y := (c.re:ℂ))]

/-- A real point lies on every intermediate circle exactly when it
lies on the terminal circle. -/
theorem verticalCircle_real_sphere_iff
    (c z : ℂ) (q R t : ℝ)
    (hz : z.im = 0) (hR : 0 ≤ R)
    (hsq : q^2+c.im^2=R^2) :
    z ∈ sphere (verticalCircleCenter c t) (verticalCircleRadius c q t) ↔
      z ∈ sphere c R := by
  have hct : (verticalCircleCenter c t).re = c.re := by
    simp [verticalCircleCenter]
  have hctim : (verticalCircleCenter c t).im = t*c.im := by
    simp [verticalCircleCenter]
  have hdistt : (dist z (verticalCircleCenter c t))^2 =
      (z.re-c.re)^2+(t*c.im)^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hct, hctim, hz, pow_two]
  have hdist : (dist z c)^2 = (z.re-c.re)^2+c.im^2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, hz, pow_two]
  have hrad : (verticalCircleRadius c q t)^2 =
      q^2+(t*c.im)^2 := by
    exact Real.sq_sqrt (by positivity)
  have hrnonneg : 0 ≤ verticalCircleRadius c q t := Real.sqrt_nonneg _
  constructor
  · intro h
    have ht := mem_sphere.mp h
    have hdc : dist z c = R := by
      nlinarith [dist_nonneg (x := z) (y := c)]
    exact mem_sphere.mpr hdc
  · intro h
    have hc := mem_sphere.mp h
    have hdt : dist z (verticalCircleCenter c t) =
        verticalCircleRadius c q t := by
      nlinarith [dist_nonneg (x := z) (y := verticalCircleCenter c t)]
    exact mem_sphere.mpr hdt

/-- Vertical recentering, parameterized as a homotopy of standard
counterclockwise circle paths. -/
def verticalCircleHomotopy (c : ℂ) (q R : ℝ)
    (hq : 0 ≤ q) (hR : 0 ≤ R)
    (hsq : q^2+c.im^2=R^2) :
    (circlePath (c.re : ℂ) q : C(I, ℂ)).Homotopy (circlePath c R) where
  toFun := fun x =>
    circleMap (verticalCircleCenter c (x.1:ℝ))
      (verticalCircleRadius c q (x.1:ℝ)) ((2*Real.pi)*(x.2:ℝ))
  continuous_toFun := by
    unfold verticalCircleCenter verticalCircleRadius circleMap
    fun_prop
  map_zero_left := by
    intro u
    change circleMap (verticalCircleCenter c 0) (verticalCircleRadius c q 0)
      ((2*Real.pi)*(u:ℝ)) = circleMap (c.re:ℂ) q ((2*Real.pi)*(u:ℝ))
    rw [verticalCircleCenter_zero, verticalCircleRadius_zero c q hq]
  map_one_left := by
    intro u
    change circleMap (verticalCircleCenter c 1) (verticalCircleRadius c q 1)
      ((2*Real.pi)*(u:ℝ)) = circleMap c R ((2*Real.pi)*(u:ℝ))
    rw [verticalCircleCenter_one, verticalCircleRadius_one c q R hR hsq]

theorem verticalCircleHomotopy_apply (c : ℂ) (q R : ℝ)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hsq : q^2+c.im^2=R^2)
    (s u : I) :
    verticalCircleHomotopy c q R hq hR hsq (s,u) =
      circleMap (verticalCircleCenter c (s:ℝ))
        (verticalCircleRadius c q (s:ℝ)) ((2*Real.pi)*(u:ℝ)) := rfl

theorem verticalCircleHomotopy_loop (c : ℂ) (q R : ℝ)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hsq : q^2+c.im^2=R^2)
    (s : I) :
    verticalCircleHomotopy c q R hq hR hsq (s,1) =
      verticalCircleHomotopy c q R hq hR hsq (s,0) := by
  rw [verticalCircleHomotopy_apply, verticalCircleHomotopy_apply]
  simp only [show ((1:I):ℝ)=1 by rfl, show ((0:I):ℝ)=0 by rfl,
    mul_one, mul_zero]
  simpa only [zero_add] using
    (periodic_circleMap (verticalCircleCenter c (s:ℝ))
      (verticalCircleRadius c q (s:ℝ)) 0)

theorem verticalCircleHomotopy_slice_contDiffOn (c : ℂ) (q R : ℝ)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hsq : q^2+c.im^2=R^2)
    (s : I) :
    ContDiffOn ℝ 2
      (homotopyLoop (verticalCircleHomotopy c q R hq hR hsq)
        (verticalCircleHomotopy_loop c q R hq hR hsq) s).extend
      (Icc 0 1) := by
  have hbase : verticalCircleHomotopy c q R hq hR hsq (s,0) =
      circleMap (verticalCircleCenter c (s:ℝ))
        (verticalCircleRadius c q (s:ℝ)) 0 := by
    rw [verticalCircleHomotopy_apply]
    simp
  have hpath : homotopyLoop (verticalCircleHomotopy c q R hq hR hsq)
      (verticalCircleHomotopy_loop c q R hq hR hsq) s =
      (circlePath (verticalCircleCenter c (s:ℝ))
        (verticalCircleRadius c q (s:ℝ))).cast hbase hbase := by
    apply Path.ext
    funext u
    rfl
  rw [hpath]
  simpa only [Path.extend_cast] using
    (circlePath_contDiffOn (verticalCircleCenter c (s:ℝ))
      (verticalCircleRadius c q (s:ℝ)))

end NLS.ComplexAnalysis
