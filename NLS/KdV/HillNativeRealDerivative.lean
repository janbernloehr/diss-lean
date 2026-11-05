import NLS.KdV.HillNativeRealSignedMap

/-! The actual physical real derivative is the restriction of the actual
complex derivative. Both source and target inclusions retain the correct
Fourier conjugation real forms and their original Banach norms. -/
noncomputable section
namespace NLS.KdV

theorem fderiv_hillRealSignedMap_coe (q h : HillRealMeanZeroSource) :
    ((fderiv ℝ hillRealSignedMap q) h : HillSignedComplexTarget)=
      (fderiv ℂ hillMeanZeroComplexMap q.val) h.val := by
  let S := WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2
  let T := WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2
  have hr := (analyticAt_hillRealSignedMap q).differentiableAt.hasFDerivAt
  have hc := (analyticOnNhd_hillMeanZeroComplexMap q.val
    (real_mem_hillMeanZeroComplexDomain q.val q.property)).differentiableAt.hasFDerivAt
  have hT : HasFDerivAt (T.subtypeL : HillRealSignedTarget →L[ℝ] HillSignedComplexTarget)
      T.subtypeL (hillRealSignedMap q) := _root_.ContinuousLinearMap.hasFDerivAt _
  have hS : HasFDerivAt (S.subtypeL : HillRealMeanZeroSource →L[ℝ] HillMeanZeroSource)
      S.subtypeL q := _root_.ContinuousLinearMap.hasFDerivAt _
  have hleft : HasFDerivAt
      (fun a : HillRealMeanZeroSource => T.subtypeL (hillRealSignedMap a))
      (T.subtypeL.comp (fderiv ℝ hillRealSignedMap q)) q := by
    exact @HasFDerivAt.comp ℝ inferInstance
      HillRealMeanZeroSource inferInstance inferInstance
      HillRealSignedTarget inferInstance inferInstance
      HillSignedComplexTarget inferInstance inferInstance
      hillRealSignedMap (fderiv ℝ hillRealSignedMap q) q _ _ hT hr
  have hright : HasFDerivAt (fun a : HillRealMeanZeroSource => hillMeanZeroComplexMap (S.subtypeL a))
      (((fderiv ℂ hillMeanZeroComplexMap q.val).restrictScalars ℝ).comp S.subtypeL) q :=
    (hc.restrictScalars ℝ).comp (𝕜 := ℝ) (E := HillRealMeanZeroSource)
      (F := HillMeanZeroSource) (G := HillSignedComplexTarget)
      (f := fun a : HillRealMeanZeroSource => a.val) q hS
  have he : (fun a : HillRealMeanZeroSource => T.subtypeL (hillRealSignedMap a))=
      (fun a : HillRealMeanZeroSource => hillMeanZeroComplexMap (S.subtypeL a)) := by
    funext a
    exact hillRealSignedMap_coe a
  rw [he] at hleft
  exact congrArg (fun L : HillRealMeanZeroSource →L[ℝ] HillSignedComplexTarget => L h)
    (hleft.unique hright)

theorem fderiv_hillRealSignedMap_inclusion (q : HillRealMeanZeroSource) :
    (WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2).subtypeL.comp
      (fderiv ℝ hillRealSignedMap q) =
    ((fderiv ℂ hillMeanZeroComplexMap q.val).restrictScalars ℝ).comp
      (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2).subtypeL := by
  apply ContinuousLinearMap.ext
  intro h
  exact fderiv_hillRealSignedMap_coe q h

end NLS.KdV
