import NLS.ComplexAnalysis.PhysicalCutCubicSign
import NLS.ComplexAnalysis.AnalyticCutContour

/-! # Physical cubic signs on a free-centered enclosing circle

The real gap need not be centered at the original integration circle.
A nested-circle deformation moves to its midpoint without changing the
orientation or excluding a collapsed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_cubic_re_nonpos_of_real_endpoints
    (f g : ℂ → ℂ) (c l u R : ℝ) (hR : 0 < R) (hlu : l ≤ u)
    (hl : (l : ℂ) ∈ ball (c : ℂ) (R/32)) (hu : (u : ℂ) ∈ ball (c : ℂ) (R/32))
    (hf : AnalyticOnNhd ℂ f (ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ)))
    (hg : AnalyticOnNhd ℂ g (ball (c : ℂ) R))
    (hsq : ∀ z ∈ ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ), f z^2 = g z)
    (hreal : ∀ x ∈ Icc l u, (g (x : ℂ)).im = 0)
    (hnonneg : ∀ x ∈ Icc l u, 0 ≤ (g (x : ℂ)).re)
    (hupper : ∀ z ∈ ball (c : ℂ) R, 0 < z.im → 0 < (f z).re)
    (hlower : ∀ z ∈ ball (c : ℂ) R, z.im < 0 → (f z).re < 0) :
    (∮ z in C((c : ℂ),R/4), f z^3).re ≤ 0 ∧
      (∮ z in C((c : ℂ),R/4), f z^3).im = 0 := by
  let m : ℝ := (l+u)/2
  let d : ℝ := (u-l)/2
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hmd : m-d = l := by dsimp only [m,d]; ring
  have hmp : m+d = u := by dsimp only [m,d]; ring
  have hlabs : |l-c| < R/32 := by
    simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hl
  have huabs : |u-c| < R/32 := by
    simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hu
  have hla := abs_lt.mp hlabs
  have hua := abs_lt.mp huabs
  have hdm : d < R/32 := by dsimp only [d]; linarith
  have hmabs : |m-c| < R/32 := by
    apply abs_lt.mpr
    dsimp only [m]
    constructor <;> linarith
  have hmc : dist (m : ℂ) (c : ℂ) < R/32 := by
    simpa only [dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hmabs
  have hmid : ball (m : ℂ) (R/2) ⊆ ball (c : ℂ) R := by
    intro z hz
    have he := dist_triangle z (m : ℂ) (c : ℂ)
    have hh := mem_ball.mp hz
    exact mem_ball.mpr (by linarith)
  have hmidcut : ball (m : ℂ) (R/2) \ segment ℝ (l : ℂ) (u : ℂ) ⊆
      ball (c : ℂ) R \ segment ℝ (l : ℂ) (u : ℂ) := fun z hz => ⟨hmid hz.1,hz.2⟩
  have hsign := circleIntegral_cubic_re_nonpos_of_physical_cut_square f g m d (R/8) (R/2)
    hd (by linarith) (by linarith)
    (by simpa only [hmd,hmp] using hf.mono hmidcut) (hg.mono hmid)
    (by simpa only [hmd,hmp] using fun z hz => hsq z (hmidcut hz))
    (by simpa only [hmd,hmp] using hreal)
    (by simpa only [hmd,hmp] using hnonneg)
    (fun z hz hi => hupper z (hmid hz) hi) (fun z hz hi => hlower z (hmid hz) hi)
  have hsegmid : segment ℝ (l : ℂ) (u : ℂ) ⊆ ball (m : ℂ) (R/8) := by
    apply (convex_ball _ _).segment_subset
    · rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
      have he : l-m = -d := by dsimp only [m,d]; ring
      rw [he,abs_neg,abs_of_nonneg hd]
      linarith
    · rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
      have he : u-m = d := by dsimp only [m,d]; ring
      rw [he,abs_of_nonneg hd]
      linarith
  have hsegouter : segment ℝ (l : ℂ) (u : ℂ) ⊆ ball (c : ℂ) (R/4) :=
    ((convex_ball _ _).segment_subset hl hu).trans (ball_subset_ball (by linarith))
  have hnest : closedBall (m : ℂ) (R/8) ⊆ closedBall (c : ℂ) (R/4) := by
    intro z hz
    have he := dist_triangle z (m : ℂ) (c : ℂ)
    have hh := mem_closedBall.mp hz
    exact mem_closedBall.mpr (by linarith)
  have he := circleIntegral_eq_of_analytic_cut_nestedCircles (fun z => f z^3)
    (ball (c : ℂ) R) (segment ℝ (l : ℂ) (u : ℂ)) (fun z hz => (hf z hz).pow 3)
    (m : ℂ) (c : ℂ) (R/8) (R/4) (by positivity) (by positivity) hsegmid hsegouter hnest
    (closedBall_subset_ball (by linarith))
  rw [he] at hsign
  exact hsign

end NLS.ComplexAnalysis
