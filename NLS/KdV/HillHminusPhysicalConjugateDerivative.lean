import NLS.KdV.HillOriginalSequencePhysicalDifferential

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- Physical conjugacy on the ORIGINAL real L2 source space determines
conjugacy of the complete H-minus-one differentials in every original
REAL source direction. No holomorphic extension of conjugation is used. -/
theorem hillHminusPhysicalGerm_fderiv_conj_real_source
    (q : hillRealSourceSubmodule) (Z W : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hW : AnalyticAt ℂ W (hillOriginalHminusSource q.val))
    (hM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val,q.property⟩ : RealPeriodOneHillPotential),
      W (hillOriginalHminusSource p.val) = conj (Z (hillOriginalHminusSource p.val)))
    (h : hillRealSourceSubmodule) :
    (fderiv ℂ W (hillOriginalHminusSource q.val)) (hillOriginalRealHminusInclusion h) =
      conj ((fderiv ℂ Z (hillOriginalHminusSource q.val)) (hillOriginalRealHminusInclusion h)) := by
  let L := hillOriginalRealHminusInclusion
  let K := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap
  have hZR : HasFDerivAt (fun r : hillRealSourceSubmodule => Z (L r))
      (((fderiv ℂ Z (hillOriginalHminusSource q.val)).restrictScalars ℝ).comp L) q :=
    (hZ.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp q L.hasFDerivAt
  have hWR : HasFDerivAt (fun r : hillRealSourceSubmodule => W (L r))
      (((fderiv ℂ W (hillOriginalHminusSource q.val)).restrictScalars ℝ).comp L) q :=
    (hW.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp q L.hasFDerivAt
  have hKZ := K.hasFDerivAt.comp q hZR
  have hQ : Continuous (fun r : hillRealSourceSubmodule =>
      (⟨r.val,r.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have he : (fun r : hillRealSourceSubmodule => W (L r)) =ᶠ[𝓝 q]
      (fun r => K (Z (L r))) := hQ.continuousAt.tendsto.eventually hM
  have hD := hWR.unique (hKZ.congr_of_eventuallyEq he)
  exact congrArg (fun A : hillRealSourceSubmodule →L[ℝ] ℂ => A h) hD

end NLS.KdV
