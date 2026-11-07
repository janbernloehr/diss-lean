import NLS.Articles.KdVConvexity.FourierLebesgueKdVCoordinateField
import NLS.KdV.PeriodOneClassicalKdVCurve

/-! # Every genuine strong classical KdV curve obeys the physical coordinate ODE -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem fourierLebesguePhaseEvolution_isClassicalKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) :
    IsPeriodOneClassicalKdVCurve (fun t => D.fourierLebesguePhaseEvolution B
      4 (by norm_num) 2 (by simp) (by norm_num) t q) :=
  ⟨(D.fourierLebesgueTrajectoryMap B 4 (by norm_num) 2 (by simp) (by norm_num) q).continuous,
    D.hasDerivAt_fourierLebesguePhaseEvolution_nativeKdV B q⟩

theorem classicalKdV_hasDerivAt_signedComponent
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (σ : Bool) (n : ℕ+) (t : ℝ) :
    HasDerivAt (fun r : ℝ => hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u r).val))
      (I*(signedPositiveFrequency
        (B.fourierLebesguePhysicalFrequency 4 (by norm_num) 2 (by simp) (by norm_num)
          (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u t)))
        (if σ then (n : ℤ) else -(n : ℤ)) : ℂ)*
        hillRoughSignedAbelianComponent D.signed σ n
          (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u t).val)) t := by
  let L := (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1) (p := 2)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt t (hu.2 t)
  have he : (fun r : ℝ => L (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u r).val))=
      (fun r : ℝ => fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u r).val) := by
    funext r
    apply Subtype.ext
    funext k
    change (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1)
      (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u r).val)).val k=_
    simp only [WeightedCoeff.sobolevInclusion_apply,fourierLebesgueSourceInclusion_apply]
  change HasDerivAt (fun r : ℝ => L (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) (u r).val)) _ t at hd
  rw [he] at hd
  have hreal := fourierLebesgueSourceInclusion_real 4 (by norm_num) 2 (by simp) (by norm_num) (u t)
  have hG := hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic σ n
    (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u t).val)
    (D.real_mem_domain _ hreal)
  have hchain := (hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hd
  change HasDerivAt _ ((fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n)
    (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u t).val))
    (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1)
      (periodOneKdVNativeVector (u t).val))) t at hchain
  rw [D.signedComponent_fderiv_nativeKdV B (u t) σ n] at hchain
  exact hchain

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
