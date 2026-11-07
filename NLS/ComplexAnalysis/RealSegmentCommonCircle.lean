import NLS.ComplexAnalysis.SegmentIsolatingCircles

/-! A real segment in two real-centered discs has a common nested
midpoint circle. The result includes a singleton segment. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem real_midpoint_halfLength_fit_ball (l u x R : ℝ)
    (hl : |l-x| < R) (hu : |u-x| < R) :
    |(l+u)/2-x|+|u-l|/2 < R := by
  have hl' := abs_lt.mp hl
  have hu' := abs_lt.mp hu
  by_cases hd : 0 ≤ u-l <;> by_cases hm : 0 ≤ (l+u)/2-x
  · rw [abs_of_nonneg hm,abs_of_nonneg hd]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge hm),abs_of_nonneg hd]
    linarith
  · rw [abs_of_nonneg hm,abs_of_nonpos (le_of_not_ge hd)]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge hm),abs_of_nonpos (le_of_not_ge hd)]
    linarith

theorem exists_common_circle_of_real_segment_in_two_balls
    (l u x y R S : ℝ)
    (hlx : (l:ℂ) ∈ ball (x:ℂ) R) (hux : (u:ℂ) ∈ ball (x:ℂ) R)
    (hly : (l:ℂ) ∈ ball (y:ℂ) S) (huy : (u:ℂ) ∈ ball (y:ℂ) S) :
    ∃ c : ℂ, ∃ r ρ : ℝ, 0 < r ∧ r < ρ ∧
      segment ℝ (l:ℂ) (u:ℂ) ⊆ ball c r ∧
      closedBall c ρ ⊆ ball (x:ℂ) R ∩ ball (y:ℂ) S := by
  let c : ℂ := (((l+u)/2:ℝ):ℂ)
  let d := |u-l|/2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hcx : dist c (x:ℂ)+d < R := by
    simpa only [c,d,mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
      real_midpoint_halfLength_fit_ball l u x R
        (by simpa only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hlx)
        (by simpa only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hux)
  have hcy : dist c (y:ℂ)+d < S := by
    simpa only [c,d,mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
      real_midpoint_halfLength_fit_ball l u y S
        (by simpa only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hly)
        (by simpa only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using huy)
  let T := min (R-dist c (x:ℂ)) (S-dist c (y:ℂ))
  have hdT : d < T := lt_min (by linarith) (by linarith)
  let r := (2*d+T)/3
  let ρ := (d+2*T)/3
  have hdr : d < r := by dsimp only [r]; linarith
  have hrρ : r < ρ := by dsimp only [r,ρ]; linarith
  have hρT : ρ < T := by dsimp only [ρ]; linarith
  have hld : dist (l:ℂ) c = d := by
    simp only [c,d,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [show l-(l+u)/2 = -(u-l)/2 by ring,abs_div,abs_neg]
    norm_num
  have hud : dist (u:ℂ) c = d := by
    simp only [c,d,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [show u-(l+u)/2 = (u-l)/2 by ring,abs_div]
    norm_num
  refine ⟨c,r,ρ,hd.trans_lt hdr,hrρ,?_,?_⟩
  · have hs := (convex_closedBall c d).segment_subset
      (mem_closedBall.mpr hld.le) (mem_closedBall.mpr hud.le)
    exact hs.trans (closedBall_subset_ball hdr)
  · intro w hw
    have hwρ := mem_closedBall.mp hw
    have htx := min_le_left (R-dist c (x:ℂ)) (S-dist c (y:ℂ))
    have hty := min_le_right (R-dist c (x:ℂ)) (S-dist c (y:ℂ))
    have hx := dist_triangle w c (x:ℂ)
    have hy := dist_triangle w c (y:ℂ)
    constructor <;> apply mem_ball.mpr <;> dsimp only [T] at hρT <;> linarith

end NLS.ComplexAnalysis
