import NLS.KdV.HillHminusOneAllGapSquares
import NLS.KdV.HillHminusOneAllRealPeriods
import NLS.ComplexAnalysis.RealCutWeightedPowerIntegral

/-! # Literal real-profile formulas for all actual H^-1 canonical periods

The original counterclockwise Arnold and cubic periods are real integrals
of the actual arcosh gap profile. The formulas include every positive
index, central endpoints and collapsed gaps, without a L2 norm bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusRealGap_shifted_odd_period_eq_profile
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m k : ℕ) :
    (∮ z in C((hillHminusRealGapCenter q hr (n : ℕ) : ℂ),
        hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)),
      z^m*(hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi)^(2*k+1)) =
      -2*((∫ x in (hillHminusRealLabels q hr (2*(n : ℕ)-1))..(hillHminusRealLabels q hr (2*(n : ℕ))),
        x^m*hillHminusRealGapProfile q (n : ℕ) x^(2*k+1) : ℝ) : ℂ) := by
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillHminusRealGapContour_geometry q hr (n : ℕ) n.property
  let c := hillHminusRealGapCenter q hr (n : ℕ)
  let d := hillHminusRealGapHalfLength q hr (n : ℕ)
  let η := hillHminusRealGapCollar q hr (n : ℕ)
  have hcd : c-d = hillHminusRealLabels q hr (2*(n : ℕ)-1) := hl
  have hcp : c+d = hillHminusRealLabels q hr (2*(n : ℕ)) := hu
  let f : ℂ → ℂ := fun z => hillHminusRealCutPrimitive q z+I*(n : ℂ)*Real.pi
  let g := hillHminusRealGapPrimitiveSquare q (n : ℕ)
  let v := hillHminusRealGapProfile q (n : ℕ)
  have hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) (d+2*η) \ segment ℝ (hillHminusRealLabels q hr (2*(n : ℕ)-1) : ℂ)
        (hillHminusRealLabels q hr (2*(n : ℕ)) : ℂ)) :=
    ((analyticOnNhd_hillHminusRealCutPrimitive q hr).mono hsub).add analyticOnNhd_const
  have hg : AnalyticOnNhd ℂ g (ball (c : ℂ) (d+2*η)) :=
    analyticOnNhd_hillHminusRealGapPrimitiveSquare q hr (n : ℕ) n.property
  have hv : ContinuousOn v (Icc (c-d) (c+d)) := by
    simpa only [hcd,hcp] using continuousOn_hillHminusRealGapProfile q hr (n : ℕ) n.property
  have hupper (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (v x : ℂ)) := by
    have hx' : x ∈ Icc (hillHminusRealLabels q hr (2*(n : ℕ)-1))
        (hillHminusRealLabels q hr (2*(n : ℕ))) := by simpa only [hcd,hcp] using hx
    have ht := (tendsto_hillHminusContinuedPrimitive_gap_upper q hr (n : ℕ) n.property x hx').add_const
      (I*(n : ℂ)*Real.pi)
    simp only [sub_add_cancel] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [f,hillHminusRealCutPrimitive,if_neg hz.ne']
  have hlower (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-(v x : ℂ))) := by
    have hx' : x ∈ Icc (hillHminusRealLabels q hr (2*(n : ℕ)-1))
        (hillHminusRealLabels q hr (2*(n : ℕ))) := by simpa only [hcd,hcp] using hx
    have ht := (tendsto_hillHminusContinuedPrimitive_gap_lower q hr (n : ℕ) n.property x hx').add_const
      (I*(n : ℂ)*Real.pi)
    simp only [sub_add_cancel] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [f,hillHminusRealCutPrimitive,if_neg hz.ne]
  have he := circleIntegral_weighted_odd_power_eq_real_profile f g v c d (d+η) (d+2*η)
    hd (by linarith) (by linarith) (by simpa only [hcd,hcp] using hf) hg (fun _ _ => rfl)
    hv hlower hupper m k
  simpa only [hcd,hcp] using he

theorem hillHminusRealGapContourMoment_eq_profile_integral
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (m : ℕ) :
    hillHminusRealGapContourMoment q hr n m =
      (((2/Real.pi) * ∫ x in (hillHminusRealLabels q hr (2*(n : ℕ)-1))..(hillHminusRealLabels q hr (2*(n : ℕ))),
        x^m*hillHminusRealGapProfile q (n : ℕ) x : ℝ) : ℂ) := by
  let c : ℂ := hillHminusRealGapCenter q hr (n : ℕ)
  let r := hillHminusRealGapHalfLength q hr (n : ℕ)+hillHminusRealGapCollar q hr (n : ℕ)
  let s : ℂ := I*(n : ℂ)*Real.pi
  have hradius : 0 ≤ r := (hillHminusRealGapContourRadius_pos q hr n).le
  have hP : AnalyticOnNhd ℂ (fun z : ℂ => z^m*s) (closedBall c r) :=
    (analyticOnNhd_id.pow m).mul analyticOnNhd_const
  have hPzero : (∮ z in C(c,r), z^m*s) = 0 :=
    (DiffContOnCl.mk_ball (hP.differentiableOn.mono ball_subset_closedBall) hP.continuousOn).circleIntegral_eq_zero hradius
  have hPi : CircleIntegrable (fun z : ℂ => z^m*s) c r :=
    (hP.continuousOn.mono sphere_subset_closedBall).circleIntegrable hradius
  have hFi := circleIntegrable_hillHminusRealGapContourIntegrand q hr n m
  have hshift : (∮ z in C(c,r), z^m*(hillHminusRealCutPrimitive q z+s)) =
      ∮ z in C(c,r), z^m*hillHminusRealCutPrimitive q z := by
    simp_rw [mul_add]
    rw [circleIntegral.integral_add hFi hPi,hPzero,add_zero]
  have hi := hillHminusRealGap_shifted_odd_period_eq_profile q hr n m 0
  simp only [Nat.mul_zero,zero_add,pow_one] at hi
  rw [hshift] at hi
  change -(Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), z^m*hillHminusRealCutPrimitive q z) = _
  rw [hi,ofReal_mul,ofReal_div,ofReal_ofNat]
  ring

theorem hillHminusRealGapCubicContourMoment_eq_profile_integral
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusRealGapCubicContourMoment q hr n =
      (((-2/Real.pi) * ∫ x in (hillHminusRealLabels q hr (2*(n : ℕ)-1))..(hillHminusRealLabels q hr (2*(n : ℕ))),
        hillHminusRealGapProfile q (n : ℕ) x^3 : ℝ) : ℂ) := by
  have hi := hillHminusRealGap_shifted_odd_period_eq_profile q hr n 0 1
  simp only [show 2*1+1=3 by norm_num,pow_zero,one_mul] at hi
  unfold hillHminusRealGapCubicContourMoment
  rw [hi,ofReal_mul,ofReal_div,ofReal_neg,ofReal_ofNat]
  ring

end NLS.KdV
