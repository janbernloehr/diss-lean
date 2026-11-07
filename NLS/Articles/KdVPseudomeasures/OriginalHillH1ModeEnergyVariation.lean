import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeTangent
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalEnergyReality

/-! Genuine physical energy variation along arbitrary selected-mode H1
inverse curves. ALL modes and complex mode directions are retained,
including collapsed modes; the frequency is the actual physical one. -/
noncomputable section
open Set Complex NLS.KdV NLS.Poisson NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hasDerivAt_hillH1ModeCurve_energy (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    HasDerivAt (fun t : ℝ => hillH1KdVHamiltonian (hillH1ModeCurve n c q t))
      (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)*
        (2*((starRingEnd ℂ) (((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ))*c).re)) 0 := by
  let z := (hillIntegerSobolevEquiv 1).equiv q
  have hd := @NLS.FunctionalAnalysis.hasDerivAt_differentiable_real_line
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    hillH1CanonicalHamiltonian z (hillH1ModeCLM n c) 0
    (by simpa only [zero_smul,add_zero] using (analyticAt_hillH1CanonicalHamiltonian z).differentiableAt)
  simpa only [zero_smul,add_zero,hillH1CanonicalHamiltonian_mode_gradient] using! hd

theorem hasDerivAt_hillH1ModeCurve_complex_energy (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    HasDerivAt (fun t : ℝ => periodOneKdVHamiltonian (signedOneRealToScalarDomain (hillH1ModeCurve n c q t)))
      ((hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)*
        (2*((starRingEnd ℂ) (((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ))*c).re):ℝ):ℂ) 0 := by
  simpa only [hillH1_complexEnergy_eq_realEnergy] using! (hasDerivAt_hillH1ModeCurve_energy n c q).ofReal_comp

theorem fderiv_physical_H1_energy_mode_tangent (n : ℕ+) (c : ℂ)
    (q : RealSignedHilbert (signedStepOrder 0 1)) :
    (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q))
      (signedOneRealToScalarDomain (deriv (hillH1ModeCurve n c q) 0))=
        ((hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)*
          (2*((starRingEnd ℂ) (((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ))*c).re):ℝ):ℂ) := by
  have hc := @DifferentiableAt.hasDerivAt ℝ inferInstance
    (RealSignedHilbert (signedStepOrder 0 1)) inferInstance inferInstance (hillH1ModeCurve n c q) 0
    (analyticAt_hillH1ModeCurve n c q 0).differentiableAt
  have hL := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp
    (RealSignedHilbert (signedStepOrder 0 1)) (ScalarDomain 2)
    inferInstance inferInstance inferInstance inferInstance signedOneRealToScalarDomain _ _ 0 hc
  have hd := ((analyticAt_periodOneKdVHamiltonian (signedOneRealToScalarDomain q)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq
    0 hL (by rw [hillH1ModeCurve_zero])
  exact hd.unique (hasDerivAt_hillH1ModeCurve_complex_energy n c q)

theorem energy_cotangent_on_native_mode_vector
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (L : PeriodOneHminusOne →L[ℂ] ℂ)
    (hL : ∀ h : RealSignedHilbert (signedStepOrder 0 1),
      L (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 h))=
        (fderiv ℂ periodOneKdVHamiltonian (signedOneRealToScalarDomain q)) (signedOneRealToScalarDomain h))
    (n : ℕ+) (c : ℂ) :
    L (hillNativeModeHamiltonianVector n c (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q)))=
      ((hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q)*
        (2*((starRingEnd ℂ) (((hillIntegerSobolevEquiv 1).equiv q).val.val.val (n:ℤ))*c).re):ℝ):ℂ) := by
  rw [← hillH1ModeCurve_tangent_eq_native_HamiltonianVector,hL]
  exact fderiv_physical_H1_energy_mode_tangent n c q

end NLS.Articles.KdVPseudomeasures
