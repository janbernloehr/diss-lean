import NLS.ComplexAnalysis.InverseSquareRootBounds
import NLS.ComplexAnalysis.EndpointRootCirclePeriod
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
/-! # Exact negative unit period of a centered normalized quadratic root

An inverse-frequency Taylor coefficient gives the period for arbitrary
complex endpoint pairs, including a collapsed pair, without endpoint labels.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.ComplexAnalysis

theorem circleIntegral_inv_centered_twoRoot (a b c : ℂ) (R : ℝ) (hR : 0 < R)
    (ha : ‖a-c‖ ≤ R/16) (hb : ‖b-c‖ ≤ R/16) :
    (∮ E in C(c,R), ((c-E)*sqrt (((E-a)*(E-b))/(E-c)^2))⁻¹) = -(2*(Real.pi : ℂ)*I) := by
  let r := 2/R
  let A := fun w : ℂ => (1-(a-c)*w)*(1-(b-c)*w)
  let g := fun w : ℂ => -w/sqrt (A w)
  have hr : 0 < r := by dsimp only [r];positivity
  have hRr : R⁻¹ < r := by dsimp only [r];rw [inv_eq_one_div];gcongr;norm_num
  have hsmall (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : ‖A w-1‖ ≤ 17/64 := by
    have hwbound : ‖w‖ ≤ r := (mem_ball_zero_iff.mp hw).le
    have haw : ‖(a-c)*w‖ ≤ 1/8 := by
      rw [norm_mul]
      calc
        _ ≤ (R/16)*r := mul_le_mul ha hwbound (norm_nonneg _) (by positivity)
        _ = _ := by dsimp only [r];(field_simp; norm_num)
    have hbw : ‖(b-c)*w‖ ≤ 1/8 := by
      rw [norm_mul]
      calc
        _ ≤ (R/16)*r := mul_le_mul hb hwbound (norm_nonneg _) (by positivity)
        _ = _ := by dsimp only [r];(field_simp; norm_num)
    calc
      _ = ‖(-(a-c)*w-(b-c)*w)+((a-c)*w)*((b-c)*w)‖ := by congr 1;dsimp only [A];ring
      _ ≤ ‖-(a-c)*w-(b-c)*w‖+‖((a-c)*w)*((b-c)*w)‖ := norm_add_le _ _
      _ ≤ ‖(a-c)*w‖+‖(b-c)*w‖+‖(a-c)*w‖*‖(b-c)*w‖ := by
        rw [norm_mul,neg_mul]
        have hh : ‖-((a-c)*w)-(b-c)*w‖ ≤ ‖(a-c)*w‖+‖(b-c)*w‖ := by
          simpa only [norm_neg] using norm_sub_le (-((a-c)*w)) ((b-c)*w)
        linarith
      _ ≤ 1/8+1/8+(1/8)*(1/8) := by gcongr
      _ = _ := by norm_num
  have hslit (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : A w ∈ slitPlane :=
    mem_slitPlane_of_norm_sub_one_le_half _ ((hsmall w hw).trans (by norm_num))
  have hAa (w : ℂ) : AnalyticAt ℂ A w := by
    exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).mul
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
  have hSa (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : AnalyticAt ℂ (fun v => sqrt (A v)) w :=
    (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds (hslit w hw))).comp
      (f := A) (hAa w)
  have hSn (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : sqrt (A w) ≠ 0 := by
    intro he
    have hs := sq_sqrt (A w)
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact zero_notMem_slitPlane (hs.symm ▸ hslit w hw)
  have hg : AnalyticOnNhd ℂ g (ball (0 : ℂ) r) := by
    intro w hw
    exact analyticAt_id.neg.div (hSa w hw) (hSn w hw)
  have hder : deriv g 0 = -1 := by
    have hd := ((hasDerivAt_id (0 : ℂ)).neg).div
      (hSa 0 (mem_ball_self hr)).differentiableAt.hasDerivAt (hSn 0 (mem_ball_self hr))
    simpa [g,A,Pi.div_def] using hd.deriv
  have he (z : ℂ) (hz : z ≠ 0) :
      ((c-(c+z))*sqrt ((((c+z)-a)*((c+z)-b))/((c+z)-c)^2))⁻¹ = g z⁻¹ := by
    have harg : (((c+z)-a)*((c+z)-b))/((c+z)-c)^2 = A z⁻¹ := by
      dsimp only [A]
      simp only [add_sub_cancel_left]
      field_simp [hz]
      ring
    rw [harg,show c-(c+z) = -z by ring]
    dsimp only [g]
    simp only [mul_inv_rev,inv_neg,div_eq_mul_inv]
    ring
  have hc := circleIntegral_comp_inv_eq g r R hr hR hRr hg
  rw [hder] at hc
  have htrans : (∮ E in C(c,R), ((c-E)*sqrt (((E-a)*(E-b))/(E-c)^2))⁻¹) =
      ∮ z in C(0,R), ((c-(c+z))*sqrt ((((c+z)-a)*((c+z)-b))/((c+z)-c)^2))⁻¹ := by
    simp only [circleIntegral,circleMap,deriv_circleMap,zero_add]
  rw [htrans]
  have hcongr : (∮ z in C(0,R), ((c-(c+z))*sqrt ((((c+z)-a)*((c+z)-b))/((c+z)-c)^2))⁻¹) =
      ∮ z in C(0,R), g z⁻¹ := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact he z (norm_pos_iff.mp (by rw [hn];exact hR))
  rw [hcongr]
  simpa only [mul_neg,mul_one] using hc
end NLS.ComplexAnalysis
