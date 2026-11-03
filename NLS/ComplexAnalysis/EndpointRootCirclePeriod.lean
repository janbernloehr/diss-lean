import NLS.ComplexAnalysis.AnalyticTwoZeroRoot
import NLS.ComplexAnalysis.InversionCircleCoefficients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem mem_slitPlane_one_sub_of_norm_lt_one (w : ℂ) (hw : ‖w‖ < 1) : 1-w ∈ slitPlane := by
  apply mem_slitPlane_iff.mpr
  left
  simp only [sub_re,one_re]
  have hb := le_trans (le_abs_self w.re) (abs_re_le_norm w)
  linarith

theorem circleIntegral_inv_endpointRoot_midpoint (τ δ : ℂ) (R : ℝ) (hR : ‖δ‖ < R) :
    (∮ z in C(τ,R), (endpointRoot (τ-δ) (τ+δ) z)⁻¹) = -(2*(Real.pi : ℂ)*I) := by
  have hRp : 0 < R := (norm_nonneg δ).trans_lt hR
  let r := 2/(R+‖δ‖)
  have hr : 0 < r := div_pos (by norm_num) (by positivity)
  have hRr : R⁻¹ < r := by
    dsimp only [r]
    rw [inv_eq_one_div]
    apply (div_lt_div_iff₀ hRp (by positivity : 0 < R+‖δ‖)).mpr
    linarith
  have hslit (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : 1-δ^2*w^2 ∈ slitPlane := by
    apply mem_slitPlane_one_sub_of_norm_lt_one
    rw [norm_mul,norm_pow,norm_pow]
    have hwr : ‖w‖ < r := by simpa only [mem_ball,dist_zero_right] using hw
    have hdr : ‖δ‖*r < 1 := by
      dsimp only [r]
      rw [← mul_div_assoc]
      apply (div_lt_one (by positivity : 0 < R+‖δ‖)).mpr
      linarith
    have hdw : ‖δ‖*‖w‖ < 1 :=
      (mul_le_mul_of_nonneg_left hwr.le (norm_nonneg δ)).trans_lt hdr
    nlinarith [mul_nonneg (norm_nonneg δ) (norm_nonneg w)]
  let g : ℂ → ℂ := fun w => -w/Complex.sqrt (1-δ^2*w^2)
  have hg : AnalyticOnNhd ℂ g (ball 0 r) := by
    intro w hw
    have hrad : AnalyticAt ℂ (fun w : ℂ => 1-δ^2*w^2) w :=
      analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))
    have hsqrt := (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds (hslit w hw))).comp
      (f := fun w : ℂ => 1-δ^2*w^2) hrad
    have hn : Complex.sqrt (1-δ^2*w^2) ≠ 0 := by
      intro he
      have hsq : (Complex.sqrt (1-δ^2*w^2))^2 = 1-δ^2*w^2 := by
        have hh := Complex.cpow_nat_inv_pow (1-δ^2*w^2) (Nat.succ_ne_zero 1)
        norm_num at hh
        simpa only [Complex.sqrt,one_div] using hh
      rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hsq
      exact zero_notMem_slitPlane (hsq.symm ▸ hslit w hw)
    exact analyticAt_id.neg.div hsqrt hn
  have hder : deriv g 0 = -1 := by
    have hrad : AnalyticAt ℂ (fun w : ℂ => 1-δ^2*w^2) 0 :=
      analyticAt_const.sub (analyticAt_const.mul (analyticAt_id.pow 2))
    have hunit : AnalyticAt ℂ (fun w : ℂ => Complex.sqrt (1-δ^2*w^2)) 0 := by
      have hs : AnalyticAt ℂ Complex.sqrt (1-δ^2*(0 : ℂ)^2) := by
        simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,sub_zero] using
          (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds one_mem_slitPlane))
      exact hs.comp (f := fun w : ℂ => 1-δ^2*w^2) hrad
    have hd := ((hasDerivAt_id (0 : ℂ)).neg).div hunit.differentiableAt.hasDerivAt (by simp)
    simpa [g,Pi.div_def] using hd.deriv
  have he (z : ℂ) : (endpointRoot (τ-δ) (τ+δ) (τ+z))⁻¹ = g z⁻¹ := by
    have hmid : ((τ-δ)+(τ+δ))/2 = τ := by ring
    have hgap : ((τ+δ)-(τ-δ))^2 = 4*δ^2 := by ring
    rw [endpointRoot,hmid,hgap]
    unfold NLS.ZakharovShabat.normalizedStandardRoot g
    rw [show τ-(τ+z) = -z by ring]
    have harg : 1-(4*δ^2)/(4*(-z)^2) = 1-δ^2*(z⁻¹)^2 := by
      field_simp
    rw [harg]
    simp only [mul_inv_rev,inv_neg,div_eq_mul_inv]
    ring
  have hc := circleIntegral_comp_inv_eq g r R hr hRp hRr hg
  rw [hder] at hc
  have htrans : (∮ z in C(τ,R), (endpointRoot (τ-δ) (τ+δ) z)⁻¹) =
      ∮ z in C(0,R), (endpointRoot (τ-δ) (τ+δ) (τ+z))⁻¹ := by
    simp only [circleIntegral,circleMap,deriv_circleMap,zero_add]
  rw [htrans]
  simp_rw [he]
  simpa only [mul_neg,mul_one] using hc

end NLS.ComplexAnalysis
