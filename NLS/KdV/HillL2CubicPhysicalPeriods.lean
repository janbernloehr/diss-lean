import NLS.KdV.HillFreeQuarticContour
import NLS.KdV.HillHminusPhysicalArnoldActions
import NLS.ComplexAnalysis.RealCutWeightedPowerIntegral

/-! # Literal physical L2 cubic periods recover the intrinsic rough cubic moments -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2RealGap_shifted_odd_period_eq_profile
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ+) (m k : ℕ) :
    (∮ z in C((hillRealGapCenter q hq hr (n : ℕ) : ℂ),
        hillRealGapHalfLength q hq hr (n : ℕ)+hillRealGapCollar q hq hr (n : ℕ)),
      z^m*(hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi)^(2*k+1)) =
      -2*((∫ x in (hillRealLabels q hq hr (2*(n : ℕ)-1))..(hillRealLabels q hq hr (2*(n : ℕ))),
        x^m*hillRealGapProfile (SpectralWeight.one.toCoeff q) (n : ℕ) x^(2*k+1) : ℝ) : ℂ) := by
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillRealGapContour_geometry q hq hr (n : ℕ) n.property
  let c := hillRealGapCenter q hq hr (n : ℕ)
  let d := hillRealGapHalfLength q hq hr (n : ℕ)
  let η := hillRealGapCollar q hq hr (n : ℕ)
  have hcd : c-d = hillRealLabels q hq hr (2*(n : ℕ)-1) := hl
  have hcp : c+d = hillRealLabels q hq hr (2*(n : ℕ)) := hu
  let f : ℂ → ℂ := fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z+I*(n : ℂ)*Real.pi
  let g := hillL2RealGapPrimitiveSquare (SpectralWeight.one.toCoeff q) (n : ℕ)
  let v := hillRealGapProfile (SpectralWeight.one.toCoeff q) (n : ℕ)
  have hf : AnalyticOnNhd ℂ f
      (ball (c : ℂ) (d+2*η) \ segment ℝ (hillRealLabels q hq hr (2*(n : ℕ)-1) : ℂ)
        (hillRealLabels q hq hr (2*(n : ℕ)) : ℂ)) :=
    ((analyticOnNhd_hillL2RealCutPrimitive q hq hr).mono hsub).add analyticOnNhd_const
  have hg : AnalyticOnNhd ℂ g (ball (c : ℂ) (d+2*η)) :=
    analyticOnNhd_hillL2RealGapPrimitiveSquare q hq hr (n : ℕ) n.property
  have hv : ContinuousOn v (Icc (c-d) (c+d)) := by
    simpa only [hcd,hcp] using continuousOn_hillRealGapProfile q hq hr (n : ℕ) n.property
  have hupper (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (v x : ℂ)) := by
    have hx' : x ∈ Icc (hillRealLabels q hq hr (2*(n : ℕ)-1))
        (hillRealLabels q hq hr (2*(n : ℕ))) := by simpa only [hcd,hcp] using hx
    have ht := (tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr (n : ℕ) n.property x hx').add_const
      (I*(n : ℂ)*Real.pi)
    simp only [sub_add_cancel] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [f,hillL2RealCutPrimitive,if_neg hz.ne']
  have hlower (x : ℝ) (hx : x ∈ Icc (c-d) (c+d)) :
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-(v x : ℂ))) := by
    have hx' : x ∈ Icc (hillRealLabels q hq hr (2*(n : ℕ)-1))
        (hillRealLabels q hq hr (2*(n : ℕ))) := by simpa only [hcd,hcp] using hx
    have ht := (tendsto_hillL2ContinuedPrimitive_gap_lower q hq hr (n : ℕ) n.property x hx').add_const
      (I*(n : ℂ)*Real.pi)
    simp only [sub_add_cancel] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [f,hillL2RealCutPrimitive,if_neg hz.ne]
  have he := circleIntegral_weighted_odd_power_eq_real_profile f g v c d (d+η) (d+2*η)
    hd (by linarith) (by linarith) (by simpa only [hcd,hcp] using hf) hg (fun _ _ => rfl)
    hv hlower hupper m k
  simpa only [hcd,hcp] using he

theorem hillL2RealCubicContourMoment_eq_profile_integral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ+) :
    hillL2RealCubicContourMoment q hq hr (n : ℕ) =
      (((-2/Real.pi)*∫ x in (hillRealLabels q hq hr (2*(n : ℕ)-1))..(hillRealLabels q hq hr (2*(n : ℕ))),
        hillRealGapProfile (SpectralWeight.one.toCoeff q) (n : ℕ) x^3 : ℝ) : ℂ) := by
  have hi := hillL2RealGap_shifted_odd_period_eq_profile q hq hr n 0 1
  simp only [show 2*1+1=3 by norm_num,pow_zero,one_mul] at hi
  unfold hillL2RealCubicContourMoment cubicMoment
  rw [hi,ofReal_mul,ofReal_div,ofReal_neg,ofReal_ofNat]
  ring

theorem hillHminusRealGapCubicContourMoment_original_source
    (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillHminusRealGapCubicContourMoment (hillOriginalHminusSource p.val)
      (hillOriginalHminusSource_real p.val p.property.2) n =
      hillL2RealCubicContourMoment p.val p.property.1 p.property.2 (n : ℕ) := by
  rw [hillHminusRealGapCubicContourMoment_eq_profile_integral,
    hillL2RealCubicContourMoment_eq_profile_integral,hillHminusRealLabels_original_source p]
  apply congrArg Complex.ofReal
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  unfold hillHminusRealGapProfile hillRealGapProfile
  dsimp only
  rw [hillHminusDiscriminant_original_source_agreement p.val p.property.1]

end NLS.KdV
