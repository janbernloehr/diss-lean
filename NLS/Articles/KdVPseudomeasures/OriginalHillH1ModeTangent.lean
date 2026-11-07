import NLS.Articles.KdVPseudomeasures.OriginalHillNativeModeVector
import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionTangent

/-! The actual arbitrary selected-mode H1 inverse curve has exactly the
physical real linear combination of native-coordinate Gardner vectors,
including every collapsed selected mode. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hasDerivAt_hillH1ModeCurve_rough_zero (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    HasDerivAt (fun t : ℝ => hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ModeCurve n c q t)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ModeCurve n c q) 0))) 0 := by
  let L : RealSignedHilbert (signedStepOrder 0 1) →L[ℝ] PeriodOneHminusOne :=
    hillRealMeanZeroInclusion.comp (hillIntegerSourceInclusion 1)
  have hL : HasFDerivAt L L (hillH1ModeCurve n c q 0) := L.hasFDerivAt
  have hc := @DifferentiableAt.hasDerivAt ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance (hillH1ModeCurve n c q) 0
    (analyticAt_hillH1ModeCurve n c q 0).differentiableAt
  have hd := @HasFDerivAt.comp_hasDerivAt ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance
    PeriodOneHminusOne inferInstance inferInstance (hillH1ModeCurve n c q)
    (deriv (hillH1ModeCurve n c q) 0) 0 L L hL hc
  simpa only [Function.comp_def] using! hd

theorem hillH1ModeCurve_native_velocity (n : ℕ+) (c : ℂ) (q : RealSignedHilbert (signedStepOrder 0 1)) (k : ℤ) :
    (fderiv ℂ (hillHminusNativeCoordinate k) (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ModeCurve n c q) 0)))=
      (hillH1ModeCLM n c).val.val.val k := by
  let Q := hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)
  have hr : IsRealPeriodOneHminusOne Q := (hillIntegerSourceInclusion 1 q).property
  have hN := ((analyticOnNhd_hillHminusNativeCoordinate k Q
    (real_mem_hillHminusActionAngleNativeDomain Q hr)).differentiableAt.hasFDerivAt.restrictScalars ℝ)
  have hd := hN.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillH1ModeCurve_rough_zero n c q)
    (by rw [hillH1ModeCurve_zero])
  have he : (fun t : ℝ => hillHminusNativeCoordinate k
      (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (hillH1ModeCurve n c q t))))=
      (fun t : ℝ => ((hillIntegerSobolevEquiv 1).equiv q).val.val.val k+
        (t:ℂ)*(hillH1ModeCLM n c).val.val.val k) := by
    funext t
    rw [← hillIntegerSobolevEquiv_eq_nativeCoordinate,hillH1ModeCurve_native_image]
    rfl
  dsimp only [Function.comp_def] at hd
  rw [he] at hd
  have hl := ((Complex.ofRealCLM.hasDerivAt (x := (0:ℝ))).mul_const
    ((hillH1ModeCLM n c).val.val.val k)).const_add
      (((hillIntegerSobolevEquiv 1).equiv q).val.val.val k)
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using! hd.unique hl

theorem hillH1ModeCurve_tangent_eq_native_HamiltonianVector (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 (deriv (hillH1ModeCurve n c q) 0))=
      hillNativeModeHamiltonianVector n c (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) := by
  let r := hillIntegerSourceInclusion 1 q
  let Q := hillRealMeanZeroInclusion r
  let v : HillMeanZeroSource := (hillIntegerSourceInclusion 1 (deriv (hillH1ModeCurve n c q) 0)).val
  let g : HillMeanZeroSource := ⟨hillNativeModeHamiltonianVector n c Q,
    hillNativeModeHamiltonianVector_zero_mode n c Q⟩
  have hdomain := real_mem_hillMeanZeroComplexDomain r.val r.property
  have hv : (fderiv ℂ hillMeanZeroComplexMap r.val) v=(fderiv ℂ hillMeanZeroComplexMap r.val) g := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain v k,
      fderiv_hillMeanZeroComplexMap_coordinate r.val hdomain g k]
    exact (hillH1ModeCurve_native_velocity n c q k).trans
      (hillNativeModeHamiltonianVector_native_velocity n c r k).symm
  have he : v=g := (hillRealNativeJacobian_bijective r).1 hv
  exact congrArg (fun h : HillMeanZeroSource => h.val) he

theorem native_mode_HamiltonianVector_has_genuine_H1_representative (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    ∃ v : RealSignedHilbert (signedStepOrder 0 1),
      hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 v)=
        hillNativeModeHamiltonianVector n c (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)) :=
  ⟨deriv (hillH1ModeCurve n c q) 0,hillH1ModeCurve_tangent_eq_native_HamiltonianVector n c q⟩

end NLS.Articles.KdVPseudomeasures
