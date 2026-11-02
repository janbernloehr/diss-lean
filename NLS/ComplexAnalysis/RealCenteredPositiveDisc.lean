import NLS.ComplexAnalysis.PiecewiseC1Loop

/-! # Positive real isolating discs

A real-centered disc excluding zero and containing a positive real point
lies entirely in the open right half-plane. This fixes the geometry
needed when an isolating frequency contour is squared.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem radius_lt_re_of_zero_excluded {c : ℂ} {r x : ℝ}
    (hc : c.im = 0) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hx : 0 < x) (hxc : (x : ℂ) ∈ ball c r) : r < c.re := by
  have he : (c.re : ℂ) = c := Complex.ext rfl (by simpa only [ofReal_im] using hc.symm)
  have hnorm : r < |c.re| := by
    have hn : r < dist (0 : ℂ) c := lt_of_not_ge hzero
    have hnC : ‖c‖ = |c.re| := by
      calc
        _ = ‖(c.re : ℂ)‖ := congrArg norm he.symm
        _ = _ := by simp only [Complex.norm_real,Real.norm_eq_abs]
    simpa only [dist_eq_norm,zero_sub,norm_neg,hnC] using hn
  have hdist : |x-c.re| < r := by
    have h := (Complex.abs_re_le_norm ((x : ℂ)-c)).trans_lt (show ‖(x : ℂ)-c‖ < r by
      simpa only [mem_ball,dist_eq_norm] using hxc)
    simpa only [sub_re,ofReal_re] using h
  have hp : 0 < c.re := by
    by_contra hn
    rw [abs_of_nonpos (le_of_not_gt hn)] at hnorm
    have h := (le_abs_self (x-c.re)).trans_lt hdist
    linarith
  rwa [abs_of_pos hp] at hnorm

theorem re_pos_on_closedBall_of_radius_lt_re {c : ℂ} {r : ℝ} (hc : r < c.re) :
    ∀ z ∈ closedBall c r, 0 < z.re := by
  intro z hz
  have h := (Complex.abs_re_le_norm (z-c)).trans (show ‖z-c‖ ≤ r by
    simpa only [mem_closedBall,dist_eq_norm] using hz)
  have hl : -r ≤ z.re-c.re := (abs_le.mp (by simpa only [sub_re] using h)).1
  linarith

namespace PiecewiseC1Loop

theorem circle_inside_of_sphere_subset (c : ℂ) (r : ℝ) {D : Set ℂ}
    (hr : 0 ≤ r) (hD : sphere c r ⊆ D) : (circle c r).Inside D := by
  intro i u
  apply hD
  change circleMap c r ((2*Real.pi)*(u : ℝ)) ∈ sphere c r
  exact circleMap_mem_sphere c hr _

end PiecewiseC1Loop
end NLS.ComplexAnalysis
