import NLS.KdV.ClassicalLocalPrimitive
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds
import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform potential variation of the actual Hill discriminant

The actual IVP trace bound on horizontal frequency strips and a Banach
Cauchy estimate give a source derivative bound independent of the real
frequency. The resulting Lipschitz estimates also control the radicand.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem norm_constantUpperPotential_le (q : NLS.LinearVolterra.Curve ℂ) :
    ‖constantUpperPotential q‖ ≤ 1+‖q‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖((-1 : ℂ),-q t)‖ ≤ 1+‖q‖
  simp only [Prod.norm_def,norm_neg,norm_one]
  exact max_le (le_add_of_nonneg_right (norm_nonneg q)) ((q.norm_coe_le_norm t).trans (by linarith [norm_nonneg q]))

theorem analyticOnNhd_classicalHillDiscriminant_source (z : ℂ) :
    AnalyticOnNhd ℂ (fun q : NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant q (z^2)) univ := by
  intro q _
  exact (analyticOnNhd_classicalHillDiscriminant_joint (z^2,q) (mem_univ _)).comp
    (f := fun a : NLS.LinearVolterra.Curve ℂ => (z^2,a)) (analyticAt_const.prod analyticAt_id)

/-- One explicit constant controls all source derivatives in the unit
potential ball and all real frequencies in the prescribed strip. -/
theorem norm_fderiv_classicalHillDiscriminant_source_le (H : ℝ) (z : ℂ) (hz : |z.im| ≤ H)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < 1) :
    ‖fderiv ℂ (fun a : NLS.LinearVolterra.Curve ℂ => classicalHillDiscriminant a (z^2)) q‖ ≤
      4*Real.exp (H+3) := by
  have ha := analyticOnNhd_classicalHillDiscriminant_source z
  have hbound (a : NLS.LinearVolterra.Curve ℂ) (ha : a ∈ ball 0 (1+1 : ℝ)) :
      ‖classicalHillDiscriminant a (z^2)‖ ≤ 2*Real.exp (H+3) := by
    rw [classicalHillDiscriminant_sq]
    apply norm_classicalDiscriminant_le_of_bounds _ _ 3 H _ hz
    have han : ‖a‖ < 2 := by simpa only [mem_ball,dist_zero_right,one_add_one_eq_two] using ha
    exact (norm_constantUpperPotential_le a).trans (by linarith)
  have he := norm_fderiv_le_of_ball_bound _ 0 q 1 1 (2*Real.exp (H+3)) (by norm_num)
    (ha.differentiableOn.mono (subset_univ _)) hbound
    (by simpa only [mem_ball,dist_zero_right] using hq)
  convert he using 1
  ring

theorem norm_classicalHillDiscriminant_sub_free_le (H : ℝ) (z : ℂ) (hz : |z.im| ≤ H)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < 1) :
    ‖classicalHillDiscriminant q (z^2)-classicalHillDiscriminant 0 (z^2)‖ ≤
      (4*Real.exp (H+3))*‖q‖ := by
  have ha := analyticOnNhd_classicalHillDiscriminant_source z
  have he := (convex_ball (0 : NLS.LinearVolterra.Curve ℂ) 1).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) (f := fun a => classicalHillDiscriminant a (z^2))
    (fun a _ => (ha a (mem_univ _)).differentiableAt)
    (fun a ha => norm_fderiv_classicalHillDiscriminant_source_le H z hz a
      (by simpa only [mem_ball,dist_zero_right] using ha))
    (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (by simpa only [mem_ball,dist_zero_right] using hq)
  simpa only [sub_zero] using he

/-- The same actual trace controls the branch radicand uniformly along
the full strip, including all selected positive frequency contours. -/
theorem norm_classicalHillRadicand_sub_free_le (H : ℝ) (z : ℂ) (hz : |z.im| ≤ H)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : ‖q‖ < 1) :
    ‖classicalHillRadicand (z^2,q)-classicalHillRadicand (z^2,0)‖ ≤
      (16*(Real.exp (H+3))^2)*‖q‖ := by
  have htrace (a : NLS.LinearVolterra.Curve ℂ) (ha : ‖a‖ < 1) :
      ‖classicalHillDiscriminant a (z^2)‖ ≤ 2*Real.exp (H+3) := by
    rw [classicalHillDiscriminant_sq]
    exact norm_classicalDiscriminant_le_of_bounds _ _ 3 H
      ((norm_constantUpperPotential_le a).trans (by linarith)) hz
  have hqtrace := htrace q hq
  have h0trace := htrace 0 (by norm_num)
  have hdiff := norm_classicalHillDiscriminant_sub_free_le H z hz q hq
  have he : classicalHillRadicand (z^2,q)-classicalHillRadicand (z^2,0) =
      (classicalHillDiscriminant q (z^2)-classicalHillDiscriminant 0 (z^2))*
        (classicalHillDiscriminant q (z^2)+classicalHillDiscriminant 0 (z^2)) := by
    dsimp only [classicalHillRadicand]
    ring
  rw [he,norm_mul]
  calc
    _ ≤ ((4*Real.exp (H+3))*‖q‖)*
        (‖classicalHillDiscriminant q (z^2)‖+‖classicalHillDiscriminant 0 (z^2)‖) :=
      mul_le_mul hdiff (norm_add_le _ _) (norm_nonneg _) (by positivity)
    _ ≤ ((4*Real.exp (H+3))*‖q‖)*(2*Real.exp (H+3)+2*Real.exp (H+3)) := by
      gcongr
    _ = _ := by ring

end NLS.KdV
