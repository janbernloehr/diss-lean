import NLS.KdV.HillActionAngleFirstVariation
import NLS.KdV.HillActionAngleNativeAnalytic
import NLS.FunctionalAnalysis.LinearTargetDerivative

/-! The full Banach derivative of the actual native Cartesian map has the
computed Fourier coordinates. Its nonpositive coordinates vanish too. -/
noncomputable section
open Set Complex Filter Topology NLS.FunctionalAnalysis
namespace NLS.KdV

theorem fderiv_hillHminusNativeCartesianMap_fst_coordinate (h : PeriodOneHminusOne) (k : ℤ) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).fst.val k=
      (fderiv ℂ (fun q => (hillHminusNativeCartesianMap q).fst.val k) 0) h := by
  let W := Weight.positiveSobolev (-1/2)
  let L : WeightedCoeffPair W 2 →L[ℂ] ℂ := (WeightedCoeff.evalCLM W 2 k).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff W 2) (WeightedCoeff W 2)).comp
      (WeightedCoeffPair.toMax W 2).toContinuousLinearMap)
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  have hf := (analyticOnNhd_hillHminusNativeCartesianMap 0
    (real_mem_hillHminusActionAngleNativeDomain 0 hr)).differentiableAt
  exact (fderiv_comp_clm_apply hillHminusNativeCartesianMap L 0 h hf).symm

theorem fderiv_hillHminusNativeCartesianMap_snd_coordinate (h : PeriodOneHminusOne) (k : ℤ) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).snd.val k=
      (fderiv ℂ (fun q => (hillHminusNativeCartesianMap q).snd.val k) 0) h := by
  let W := Weight.positiveSobolev (-1/2)
  let L : WeightedCoeffPair W 2 →L[ℂ] ℂ := (WeightedCoeff.evalCLM W 2 k).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff W 2) (WeightedCoeff W 2)).comp
      (WeightedCoeffPair.toMax W 2).toContinuousLinearMap)
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  have hf := (analyticOnNhd_hillHminusNativeCartesianMap 0
    (real_mem_hillHminusActionAngleNativeDomain 0 hr)).differentiableAt
  exact (fderiv_comp_clm_apply hillHminusNativeCartesianMap L 0 h hf).symm

theorem fderiv_hillHminusNativeCartesianMap_positive_mean_zero (n : ℕ+)
    (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).fst.val ((n:ℕ):ℤ)=
      (h.val (-(n:ℤ))+h.val (n:ℤ))/(2*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) ∧
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).snd.val ((n:ℕ):ℤ)=
      (h.val (-(n:ℤ))-h.val (n:ℤ))/((2*I)*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusActionAngleNativeDomain 0 hr
  constructor
  · have he : (fun q => (hillHminusNativeCartesianMap q).fst.val ((n:ℕ):ℤ)) =ᶠ[𝓝 0]
        hillHminusActionAngleX n := by
      filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds h0] with q hq
      exact (hillHminusNativeCartesianMap_positive q hq n).1
    rw [fderiv_hillHminusNativeCartesianMap_fst_coordinate,he.fderiv_eq]
    exact fderiv_hillHminusActionAngleX_zero_mean_zero n h hh

  · have he : (fun q => (hillHminusNativeCartesianMap q).snd.val ((n:ℕ):ℤ)) =ᶠ[𝓝 0]
        hillHminusActionAngleY n := by
      filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds h0] with q hq
      exact (hillHminusNativeCartesianMap_positive q hq n).2
    rw [fderiv_hillHminusNativeCartesianMap_snd_coordinate,he.fderiv_eq]
    exact fderiv_hillHminusActionAngleY_zero_mean_zero n h hh

theorem fderiv_hillHminusNativeCartesianMap_nonpositive (h : PeriodOneHminusOne)
    (k : ℤ) (hk : k ≤ 0) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).fst.val k=0 ∧
      ((fderiv ℂ hillHminusNativeCartesianMap 0) h).snd.val k=0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  have h0 := real_mem_hillHminusActionAngleNativeDomain 0 hr
  constructor
  · have he : (fun q => (hillHminusNativeCartesianMap q).fst.val k) =ᶠ[𝓝 0]
        (fun _ : PeriodOneHminusOne => (0:ℂ)) := by
      filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds h0] with q hq
      exact (hillHminusNativeCartesianMap_nonpositive q hq k hk).1
    rw [fderiv_hillHminusNativeCartesianMap_fst_coordinate,he.fderiv_eq,fderiv_const_apply,zero_apply]
  · have he : (fun q => (hillHminusNativeCartesianMap q).snd.val k) =ᶠ[𝓝 0]
        (fun _ : PeriodOneHminusOne => (0:ℂ)) := by
      filter_upwards [isOpen_hillHminusActionAngleNativeDomain.mem_nhds h0] with q hq
      exact (hillHminusNativeCartesianMap_nonpositive q hq k hk).2
    rw [fderiv_hillHminusNativeCartesianMap_snd_coordinate,he.fderiv_eq,fderiv_const_apply,zero_apply]

end NLS.KdV
