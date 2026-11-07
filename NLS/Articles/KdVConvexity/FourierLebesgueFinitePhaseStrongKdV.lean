import NLS.Articles.KdVConvexity.FourierLebesgueFinitePhaseKdVCoefficients
import NLS.KdV.PeriodOneKdVNativePhysical
import NLS.SequenceSpaces.FiniteSignedPositiveSupport

/-! # Finite physical phase orbits solve KdV in the actual H1 norm

The entire source orbit is real analytic in H4. Its H1 derivative is
identified from all literal Fourier coefficients with the continuous
native conservative KdV vector, without a scalar-only derivative claim.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem hasDerivAt_finitePhaseEvolution_nativeKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hf : (Function.support (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) q).val.val).Finite)
    (t : ℝ) :
    HasDerivAt (fun u : ℝ => WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
      (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q).val)
      (periodOneKdVNativeVector
        (D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t q).val) t := by
  let Φ : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2 :=
    fun u => D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) u q
  let L : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2 →L[ℝ]
      WeightedCoeff (Weight.sobolev 1) 2 :=
    ((WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2).subtypeL
  have hΦ : AnalyticAt ℝ Φ t :=
    D.analyticAt_fourierLebesguePhaseEvolution_of_finite_support B 4 (by norm_num) 2 (by simp) (by norm_num) q hf t
  have hd := L.hasFDerivAt.comp_hasDerivAt t hΦ.differentiableAt.hasDerivAt
  obtain ⟨S,hS⟩ := exists_finite_positive_support_of_finite_signed_support
    (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) q).val.val hf
  obtain ⟨f,hfa,hfp,hfc,hfk⟩ := D.finitePhaseEvolution_KdV_coefficients B
    4 (by norm_num) 2 (by simp) (by norm_num) q hf S hS t
  have he : L (deriv Φ t)=periodOneKdVNativeVector (Φ t).val := by
    apply Subtype.ext
    funext k
    let E := (WeightedCoeff.evalCLM (Weight.sobolev 1) 2 k).restrictScalars ℝ
    have hk := E.hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun u : ℝ => (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4)
      (Φ u).val).val k) ((L (deriv Φ t)).val k) t at hk
    simp only [WeightedCoeff.sobolevInclusion_apply] at hk
    have hvel := hk.unique (hfk k)
    exact hvel.trans (periodOneKdVNativeVector_coefficients (Φ t).val f hfa hfp hfc k).symm
  rw [he] at hd
  exact hd

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
