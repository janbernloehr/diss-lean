import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerRegularity
import NLS.KdV.HillNativeRealLocalInverse
import NLS.FunctionalAnalysis.DifferentialCommutingSquare

/-! The actual all-integer strong canonical maps and their inverses have
the SAME literal free half-Fourier derivatives as the original rough map.
The identities hold coefficientwise at every signed index. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerSobolevEquiv_zero (N : ℕ) : (hillIntegerSobolevEquiv N).equiv 0=0 := by
  apply hillIntegerTargetInclusion_injective N
  rw [hillIntegerSobolevEquiv_inclusion,map_zero,hillRealSignedMap_zero,map_zero]

theorem hillIntegerSobolevEquiv_symm_zero (N : ℕ) : (hillIntegerSobolevEquiv N).equiv.symm 0=0 := by
  apply (hillIntegerSobolevEquiv N).equiv.injective
  rw [(hillIntegerSobolevEquiv N).equiv.apply_symm_apply,hillIntegerSobolevEquiv_zero]

theorem fderiv_hillIntegerSobolevEquiv_inclusion (N : ℕ)
    (q h : RealSignedHilbert (signedStepOrder 0 N)) :
    hillIntegerTargetInclusion N ((fderiv ℝ (hillIntegerSobolevEquiv N).equiv q) h)=
      (fderiv ℝ hillRealSignedMap (hillIntegerSourceInclusion N q)) (hillIntegerSourceInclusion N h) :=
  @fderiv_commuting_square
    (RealSignedHilbert (signedStepOrder 0 N)) (RealSignedHilbert (signedStepOrder (1/2) N))
    HillRealMeanZeroSource HillRealSignedTarget
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillIntegerSobolevEquiv N).equiv hillRealSignedMap (hillIntegerSourceInclusion N)
    (hillIntegerTargetInclusion N) q h ((hillIntegerSobolevEquiv N).analytic q).differentiableAt
    (analyticAt_hillRealSignedMap _).differentiableAt (hillIntegerSobolevEquiv_inclusion N)

theorem fderiv_hillIntegerSobolevEquiv_zero_apply (N : ℕ)
    (h : RealSignedHilbert (signedStepOrder 0 N)) (k : ℤ) :
    ((fderiv ℝ (hillIntegerSobolevEquiv N).equiv 0) h).val.val.val k=
      halfFourierSymbol k*h.val.val.val k := by
  have he := congrArg (fun z => z.val.val.val k) (fderiv_hillIntegerSobolevEquiv_inclusion N 0 h)
  simpa only [hillIntegerTargetInclusion_apply,map_zero,fderiv_hillRealSignedMap_zero_apply,
    hillIntegerSourceInclusion_apply] using he

theorem fderiv_hillIntegerSobolevEquiv_symm_zero_apply (N : ℕ)
    (h : RealSignedHilbert (signedStepOrder (1/2) N)) (k : ℤ) :
    ((fderiv ℝ (hillIntegerSobolevEquiv N).equiv.symm 0) h).val.val.val k=
      halfFourierInverseSymbol k*h.val.val.val k := by
  have he := @fderiv_inverse_apply
    (RealSignedHilbert (signedStepOrder 0 N)) (RealSignedHilbert (signedStepOrder (1/2) N))
    inferInstance inferInstance inferInstance inferInstance
    (hillIntegerSobolevEquiv N).equiv (hillIntegerSobolevEquiv N).equiv.symm 0 h
    ((hillIntegerSobolevEquiv N).analytic _).differentiableAt
    ((hillIntegerSobolevEquiv N).analytic_symm 0).differentiableAt
    (hillIntegerSobolevEquiv N).equiv.apply_symm_apply
  rw [hillIntegerSobolevEquiv_symm_zero] at he
  have hk := congrArg (fun q => q.val.val.val k) he
  rw [fderiv_hillIntegerSobolevEquiv_zero_apply] at hk
  calc
    _ = (halfFourierInverseSymbol k*halfFourierSymbol k)*
        ((fderiv ℝ (hillIntegerSobolevEquiv N).equiv.symm 0) h).val.val.val k := by
      rw [mul_comm (halfFourierInverseSymbol k),halfFourierSymbol_mul_inverse,one_mul]
    _ = _ := by rw [mul_assoc,hk]

end NLS.Articles.KdVPseudomeasures
