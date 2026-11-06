import NLS.KdV.HillL2WeightedTraceRemainder
import NLS.ComplexAnalysis.DiscBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- A mean-zero ORIGINAL complex unit-period L2 direction has one MORE
inverse frequency in the actual trace variation. The entire first mean
term is removed before applying the source Cauchy estimate. -/
theorem hillL2Discriminant_mean_zero_variation_bound
    (p h : Coeff 2) (hzero : h 0 = 0) (z : ℂ) (hz : z ≠ 0)
    (hsmall : 4*(‖p‖ + ‖h‖) ≤ ‖z‖) :
    ‖(fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant (Coeff.periodDouble a) (z^2)) p) h‖ ≤
      16 * Real.exp |z.im| * (‖p‖ + ‖h‖)^2 / ‖z‖^2 := by
  let T : Coeff 2 → ℂ := fun a => hillL2Discriminant (Coeff.periodDouble a) (z^2)
  have hT (a : Coeff 2) : AnalyticAt ℂ T a :=
    ((analyticOnNhd_hillL2Discriminant_joint (z^2,Coeff.periodDouble a) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (z^2,b)) (analyticAt_const.prod analyticAt_id)).comp
        (Coeff.periodDouble.toContinuousLinearMap.analyticAt a)
  let F : ℂ → ℂ := fun t => T (p+t • h) - 2*cos z - sin z/z * p 0
  have hL (t : ℂ) : AnalyticAt ℂ (fun w : ℂ => p+w • h) t :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => p) t).add
      ((analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) t).smul
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => h) t))
  have hF : Differentiable ℂ F := by
    intro t
    exact (((hT (p+t • h)).comp (f := fun w : ℂ => p+w • h) (hL t)).sub
      analyticAt_const |>.sub analyticAt_const).differentiableAt
  have hb (t : ℂ) (ht : ‖t-(0:ℂ)‖ ≤ 1) :
      ‖F t‖ ≤ 16 * Real.exp |z.im| * (‖p‖ + ‖h‖)^2 / ‖z‖^2 := by
    have ht1 : ‖t‖ ≤ 1 := by simpa only [sub_zero] using ht
    have hv : ‖p+t • h‖ ≤ ‖p‖ + ‖h‖ := by
      calc
        _ ≤ ‖p‖ + ‖t • h‖ := norm_add_le _ _
        _ = ‖p‖ + ‖t‖*‖h‖ := by rw [norm_smul]
        _ ≤ ‖p‖ + 1*‖h‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_right ht1 (norm_nonneg h))
        _ = _ := by rw [one_mul]
    have hv0 : (p+t • h) 0 = p 0 := by
      change p 0 + t * h 0 = p 0
      rw [hzero,mul_zero,add_zero]
    have hs : 4*‖p+t • h‖ ≤ ‖z‖ := by linarith
    have hh := hillL2Discriminant_first_order_remainder_bound (p+t • h) z hz hs
    rw [hv0] at hh
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg ‖z‖)
    have hsq : ‖p+t • h‖^2 ≤ (‖p‖+‖h‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hv 2
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hline : HasDerivAt (fun t : ℂ => p+t • h) h 0 := by
    simpa only [zero_add,one_smul] using!
      (hasDerivAt_const (0:ℂ) p).add ((hasDerivAt_id (0:ℂ)).smul_const h)
  have hTp : AnalyticAt ℂ T (p+(0:ℂ) • h) := by simpa only [zero_smul,add_zero] using hT p
  have hd := ((hTp.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline).sub_const
    (2*cos z)).sub_const (sin z/z * p 0)
  have hdF : HasDerivAt F ((fderiv ℂ T p) h) 0 := by
    simpa only [F,Function.comp_def,zero_smul,add_zero] using hd
  have hc := norm_deriv_le_of_closedDisc_bound hF (0:ℂ) (r := 0) (R := 1)
    (by norm_num) (16 * Real.exp |z.im| * (‖p‖ + ‖h‖)^2 / ‖z‖^2) hb
    (z := 0) (by norm_num)
  rw [hdF.deriv] at hc
  simpa only [sub_zero,div_one] using hc

end NLS.KdV
