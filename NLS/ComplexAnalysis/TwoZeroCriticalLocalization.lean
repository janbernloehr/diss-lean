import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Critical points of a two-zero factor with a nearly constant unit

A whole-disc unit estimate and the stationary equation locate the critical
point at quadratic gap scale. The two zeros may coincide or be complex.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_critical_sub_midpoint_le_two_zero_gap
    (Q : ℂ → ℂ) (a c l u x : ℂ) (R epsilon : ℝ) (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (hepsilon16 : epsilon ≤ 1/16)
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R))
    (hl : l ∈ closedBall c (R/8)) (hu : u ∈ closedBall c (R/8))
    (hx : x ∈ closedBall c (R/8))
    (hbound : ∀ z ∈ closedBall c R, ‖a*Q z+1‖ ≤ epsilon)
    (hcritical : deriv (fun z => (z-l)*(z-u)*Q z) x = 0) :
    ‖x-(l+u)/2‖ ≤ 2*epsilon*‖l-u‖^2/R ∧ ‖x-(l+u)/2‖ ≤ ‖l-u‖/4 := by
  let f (z : ℂ) := a*Q z+1
  have hfa : AnalyticOnNhd ℂ f (closedBall c R) :=
    (analyticOnNhd_const.mul hQ).add analyticOnNhd_const
  have hxR : x ∈ closedBall c R := closedBall_subset_closedBall (by linarith) hx
  have hxhalf : x ∈ ball c (R/2) := closedBall_subset_ball (by linarith) hx
  have hfd := norm_fderiv_le_of_ball_bound f c x (R/2) (R/2) epsilon (by positivity)
    (by simpa only [show R/2+R/2 = R by ring] using hfa.differentiableOn.mono ball_subset_closedBall)
    (by simpa only [show R/2+R/2 = R by ring] using (fun z hz => hbound z (ball_subset_closedBall hz))) hxhalf
  have hdf : deriv f x = a*deriv Q x :=
    (((hQ x hxR).differentiableAt.hasDerivAt.const_mul a).add_const 1).deriv
  have had : ‖a*deriv Q x‖ ≤ 4*epsilon/R := by
    rw [← hdf,norm_deriv_eq_norm_fderiv]
    convert hfd using 1
    field_simp
    ring
  have hlow : 1/2 ≤ ‖a*Q x‖ := by
    have hh := norm_sub_le (a*Q x+1) (a*Q x)
    rw [show a*Q x+1-a*Q x = 1 by ring,norm_one] at hh
    linarith [hbound x hxR]
  have hprod := (((hasDerivAt_id x).sub_const l).mul ((hasDerivAt_id x).sub_const u)).mul
    (hQ x hxR).differentiableAt.hasDerivAt
  have hd := hprod.deriv
  change deriv (fun z => (z-l)*(z-u)*Q z) x =
    (1*(x-u)+(x-l)*1)*Q x+(x-l)*(x-u)*deriv Q x at hd
  rw [hcritical] at hd
  have he : 2*(x-(l+u)/2)*(a*Q x) =
      -(((x-(l+u)/2)^2-(l-u)^2/4)*(a*deriv Q x)) := by
    linear_combination -a*hd
  have hn : 2*‖x-(l+u)/2‖*‖a*Q x‖ = ‖(x-(l+u)/2)^2-(l-u)^2/4‖*‖a*deriv Q x‖ := by
    calc
      _ = ‖2*(x-(l+u)/2)*(a*Q x)‖ := by rw [norm_mul (2*(x-(l+u)/2)) (a*Q x),norm_mul (2 : ℂ),norm_ofNat]
      _ = _ := congrArg norm he
      _ = _ := by rw [norm_neg,norm_mul]
  have hb : ‖(x-(l+u)/2)^2-(l-u)^2/4‖ ≤ ‖x-(l+u)/2‖^2+‖l-u‖^2/4 := by
    have h := norm_sub_le (((x-(l+u)/2)^2) : ℂ) (((l-u)^2)/(4 : ℂ))
    rw [norm_pow,norm_div,norm_pow,norm_ofNat] at h
    exact h
  have hineq : ‖x-(l+u)/2‖ ≤ (‖x-(l+u)/2‖^2+‖l-u‖^2/4)*(4*epsilon/R) := by
    calc
      _ ≤ 2*‖x-(l+u)/2‖*‖a*Q x‖ := by nlinarith [norm_nonneg (x-(l+u)/2)]
      _ = _ := hn
      _ ≤ (‖x-(l+u)/2‖^2+‖l-u‖^2/4)*(4*epsilon/R) :=
        mul_le_mul hb had (norm_nonneg _) (by positivity)
  have hl' : ‖l-c‖ ≤ R/8 := mem_closedBall_iff_norm.mp hl
  have hu' : ‖u-c‖ ≤ R/8 := mem_closedBall_iff_norm.mp hu
  have hx' : ‖x-c‖ ≤ R/8 := mem_closedBall_iff_norm.mp hx
  have hm : ‖(l+u)/2-c‖ ≤ R/8 := by
    rw [show (l+u)/2-c = ((l-c)+(u-c))/2 by ring,norm_div]
    norm_num only [norm_ofNat]
    have hh := norm_add_le (l-c) (u-c)
    linarith
  have hh : ‖x-(l+u)/2‖ ≤ R/4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x c ((l+u)/2)
    rw [norm_sub_rev c ((l+u)/2)] at ht
    linarith
  have hg : ‖l-u‖ ≤ R/4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub l c u
    rw [norm_sub_rev c u] at ht
    linarith
  have hquad := mul_le_mul_of_nonneg_right hh (norm_nonneg (x-(l+u)/2))
  have hscaled : ‖x-(l+u)/2‖*R ≤ 4*epsilon*(‖x-(l+u)/2‖^2+‖l-u‖^2/4) := by
    apply (le_div_iff₀ hR).mp
    calc
      _ ≤ (‖x-(l+u)/2‖^2+‖l-u‖^2/4)*(4*epsilon/R) := hineq
      _ = _ := by ring
  have hscaled' : ‖x-(l+u)/2‖*R ≤ epsilon*(R*‖x-(l+u)/2‖)+epsilon*‖l-u‖^2 := by
    apply hscaled.trans
    calc
      _ ≤ 4*epsilon*((R/4)*‖x-(l+u)/2‖+‖l-u‖^2/4) := by
        gcongr
        nlinarith [hquad]
      _ = _ := by ring
  have hemul : epsilon*(R*‖x-(l+u)/2‖) ≤ (1/2)*(R*‖x-(l+u)/2‖) :=
    mul_le_mul_of_nonneg_right (by linarith : epsilon ≤ 1/2) (by positivity)
  have hresult : ‖x-(l+u)/2‖ ≤ 2*epsilon*‖l-u‖^2/R := by
    apply (le_div_iff₀ hR).mpr
    nlinarith
  refine ⟨hresult,hresult.trans ?_⟩
  have hgscale : ‖l-u‖^2/R ≤ ‖l-u‖/4 := by
    apply (div_le_iff₀ hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hg (norm_nonneg (l-u))]
  calc
    _ = (2*epsilon)*(‖l-u‖^2/R) := by ring
    _ ≤ (1 : ℝ)*(‖l-u‖/4) := mul_le_mul (by linarith : 2*epsilon ≤ 1) hgscale (by positivity) (by positivity)
    _ = _ := one_mul _

theorem gap_circle_critical_separation (l u x z : ℂ)
    (hx : ‖x-(l+u)/2‖ ≤ ‖l-u‖/4) (hz : z ∈ sphere ((l+u)/2) ‖l-u‖) :
    ‖l-u‖/2 ≤ ‖z-x‖ := by
  have hh := norm_sub_le_norm_sub_add_norm_sub z x ((l+u)/2)
  rw [mem_sphere_iff_norm.mp hz] at hh
  linarith [norm_nonneg (l-u)]

end NLS.ComplexAnalysis
