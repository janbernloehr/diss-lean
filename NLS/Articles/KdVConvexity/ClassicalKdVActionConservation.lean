import NLS.Articles.KdVConvexity.ClassicalKdVCoordinateEvolution
import NLS.ComplexAnalysis.GlobalScalarEvolution

/-! # Every strong classical KdV curve preserves the original physical actions -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem classicalKdV_physicalActions_constant
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) :
    fourierLebesguePhysicalActions 4 (by norm_num) 2 (by simp) (by norm_num)
      (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u t))=
    fourierLebesguePhysicalActions 4 (by norm_num) 2 (by simp) (by norm_num)
      (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u 0)) := by
  let g (σ : Bool) (n : ℕ+) (r : ℝ) := hillRoughSignedAbelianComponent D.signed σ n
    (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u r).val)
  let c (n : ℕ+) (r : ℝ) : ℂ := I*(B.fourierLebesguePhysicalFrequency 4 (by norm_num)
    2 (by simp) (by norm_num) (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u r)) n : ℂ)
  have hpair (n : ℕ+) : g true n t*g false n t=g true n 0*g false n 0 := by
    apply NLS.ComplexAnalysis.paired_scalar_evolution_product_constant (g true n) (g false n) (c n)
    · intro r
      have hd := D.classicalKdV_hasDerivAt_signedComponent B u hu true n r
      simpa only [Bool.true_eq,ite_true,signedPositiveFrequency_positive] using hd
    · intro r
      have hd := D.classicalKdV_hasDerivAt_signedComponent B u hu false n r
      simp only [Bool.false_eq_true,ite_false,signedPositiveFrequency_neg,signedPositiveFrequency_positive,ofReal_neg] at hd
      convert hd using 1
      dsimp only [g,c]
      ring
  apply Subtype.ext
  funext k
  rw [fourierLebesguePhysicalActions_apply,fourierLebesguePhysicalActions_apply,
    D.fourierLebesgueForward_apply,D.fourierLebesgueForward_apply,
    D.fourierLebesgueForward_apply,D.fourierLebesgueForward_apply]
  exact hpair (actionIndexEquiv k)

theorem classicalKdV_physicalFrequency_constant
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) :
    B.fourierLebesguePhysicalFrequency 4 (by norm_num) 2 (by simp) (by norm_num)
      (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u t))=
    B.fourierLebesguePhysicalFrequency 4 (by norm_num) 2 (by simp) (by norm_num)
      (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u 0)) := by
  funext n
  unfold BasePhysicalFrequencyExtension.fourierLebesguePhysicalFrequency
  rw [D.classicalKdV_physicalActions_constant B u hu t]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
