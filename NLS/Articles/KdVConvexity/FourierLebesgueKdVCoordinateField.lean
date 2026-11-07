import NLS.Articles.KdVConvexity.FourierLebesgueStrongKdV

/-! # The actual KdV vector in every signed physical coordinate

The H1 differential equation and the independently verified scalar
phase derivatives agree at time zero. This determines the signed
Birkhoff differential on the literal KdV vector at every H4 potential.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem hasDerivAt_fourierLebesguePhaseEvolution_roughKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) (t : ℝ) :
    HasDerivAt (fun u : ℝ => fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num)
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val)
      (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1)
        (periodOneKdVNativeVector
          (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t q).val)) t := by
  let L := (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1) (p := 2)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt t
    (D.hasDerivAt_fourierLebesguePhaseEvolution_nativeKdV B q t)
  have he : (fun u : ℝ => L (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val))=
      (fun u : ℝ => fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num)
        (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val) := by
    funext u
    apply Subtype.ext
    funext k
    change (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1)
      (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
        (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val)).val k=_
    simp only [WeightedCoeff.sobolevInclusion_apply,fourierLebesgueSourceInclusion_apply]
  change HasDerivAt (fun u : ℝ => L (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val)) _ t at hd
  rwa [he] at hd

theorem signedComponent_fderiv_nativeKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (σ : Bool) (n : ℕ+) :
    (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n)
      (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) q.val))
      (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1) (periodOneKdVNativeVector q.val))=
      I*(signedPositiveFrequency
        (B.fourierLebesguePhysicalFrequency 4 (by norm_num) 2 (by simp) (by norm_num)
          (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) q))
        (if σ then (n : ℤ) else -(n : ℤ)) : ℂ)*
      hillRoughSignedAbelianComponent D.signed σ n
        (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) q.val) := by
  let U (u : ℝ) := fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num)
    (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val
  have hreal := fourierLebesgueSourceInclusion_real 4 (by norm_num) 2 (by simp) (by norm_num)
    (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) 0 q)
  have hG := hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic σ n
    (U 0) (D.real_mem_domain _ hreal)
  have hU := D.hasDerivAt_fourierLebesguePhaseEvolution_roughKdV B q 0
  have hphase := D.hasDerivAt_fourierLebesguePhaseEvolution_component B
    4 (by norm_num) 2 (by simp) (by norm_num) q σ n 0
  have hchain := (hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hU
  have he := hchain.unique hphase
  change (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) (U 0))
    (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤1) (periodOneKdVNativeVector
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) 0 q).val))=_ at he
  dsimp only [U] at he
  simpa only [D.fourierLebesguePhaseEvolution_zero] using he

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
