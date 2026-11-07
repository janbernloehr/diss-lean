import NLS.Articles.KdVPseudomeasures.OriginalHillNegativeNativeMap
import NLS.FunctionalAnalysis.AnalyticCompactRestriction

/-! Every actual physical fractional native derivative is an invertible
compact perturbation of the exact half-Fourier equivalence. -/
noncomputable section
open Filter Topology NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

local instance negativeJacobianSourceNormed (r : ℝ) : NormedSpace ℝ (HillRealNegativeSource r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.sobolev (-r))
local instance negativeJacobianTargetNormed (r : ℝ) : NormedSpace ℝ (HillRealFractionalTarget r) :=
  fourierRealZeroSubmodule_normedSpace (Weight.signedSobolev (1/2-r))

theorem isCompactOperator_hillNegativeNativeJacobian_defect
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    IsCompactOperator (fderiv ℝ (hillNegativeNativeMap r hr hr1) q-
      (hillNegativeFreeFourierEquiv r hr).toContinuousLinearMap) := by
  let R := hillFractionalFourierDefect r hr hr1
  let I := hillNegativeSourceCoefficients r
  have hR := analyticAt_hillFractionalFourierDefect r hr hr1 (I q)
    (hillNegativeSourceCoefficients_real r hr1 q)
  have hd : fderiv ℝ R (I q) = (fderiv ℂ R (I q)).restrictScalars ℝ :=
    (hR.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv
  have hc : IsCompactOperator (fderiv ℝ R (I q)) := by
    rw [hd]
    exact isCompactOperator_fractionalFourierDefect_fderiv r hr hr1 (I q)
      (hillNegativeSourceCoefficients_real r hr1 q)
  have hRreal : DifferentiableAt ℝ R (I q) := hR.restrictScalars.differentiableAt
  exact @isCompactOperator_fderiv_linear_add_restricted_defect ℝ
    (HillRealNegativeSource r) (HillRealFractionalTarget r)
    (WeightedCoeff (Weight.sobolev (-r)) 2) (WeightedCoeff (Weight.signedSobolev (1/2-r)) 2)
    inferInstance inferInstance (negativeJacobianSourceNormed r)
    inferInstance (negativeJacobianTargetNormed r) inferInstance inferInstance inferInstance inferInstance
    (hillNegativeFreeFourierEquiv r hr).toContinuousLinearMap I
    (fourierRealZeroFullProjection (Weight.signedSobolev (1/2-r)) (Weight.signedSobolev_neg _))
    R q hRreal hc

theorem injective_hillNegativeNativeJacobian
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    Function.Injective (fderiv ℝ (hillNegativeNativeMap r hr hr1) q) :=
  @fderiv_injective_of_compatible_inclusions ℝ
    (HillRealNegativeSource r) (HillRealFractionalTarget r) HillRealMeanZeroSource HillRealSignedTarget
    inferInstance inferInstance (negativeJacobianSourceNormed r)
    inferInstance (negativeJacobianTargetNormed r) inferInstance inferInstance inferInstance inferInstance
    (hillNegativeNativeMap r hr hr1) hillRealSignedMap
    (hillNegativeSourceInclusion r hr1) (hillNegativeTargetInclusion r hr1)
    (hillNegativeSourceInclusion_injective r hr1) (hillNegativeNativeMap_inclusion r hr hr1) q
    (analyticAt_hillNegativeNativeMap r hr hr1 q).differentiableAt
    (analyticAt_hillRealSignedMap _).differentiableAt
    (hillPhysicalNativeJacobianEquiv _).injective

theorem exists_hillNegativeNativeJacobianEquiv
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    ∃ A : HillRealNegativeSource r ≃L[ℝ] HillRealFractionalTarget r,
      A.toContinuousLinearMap = fderiv ℝ (hillNegativeNativeMap r hr hr1) q :=
  @exists_equiv_of_injective_of_compact_sub_equiv ℝ
    (HillRealNegativeSource r) (HillRealFractionalTarget r)
    inferInstance inferInstance (negativeJacobianSourceNormed r) inferInstance
    inferInstance (negativeJacobianTargetNormed r) inferInstance
    (hillNegativeFreeFourierEquiv r hr)
    (fderiv ℝ (hillNegativeNativeMap r hr hr1) q)
    (isCompactOperator_hillNegativeNativeJacobian_defect r hr hr1 q)
    (injective_hillNegativeNativeJacobian r hr hr1 q)

theorem hillNegativeNativeMap_localInverse
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : HillRealNegativeSource r) :
    ∃ g : HillRealFractionalTarget r → HillRealNegativeSource r,
      AnalyticAt ℝ g (hillNegativeNativeMap r hr hr1 q) ∧
      g (hillNegativeNativeMap r hr hr1 q) = q ∧
      (∀ᶠ a in 𝓝 q, g (hillNegativeNativeMap r hr hr1 a) = a) ∧
      (∀ᶠ z in 𝓝 (hillNegativeNativeMap r hr hr1 q), hillNegativeNativeMap r hr hr1 (g z) = z) := by
  obtain ⟨A,hA⟩ := exists_hillNegativeNativeJacobianEquiv r hr hr1 q
  obtain ⟨g,hg,hqg,hl,hh,_⟩ := exists_localInverse_of_equiv_fderiv
    (analyticAt_hillNegativeNativeMap r hr hr1 q) A hA.symm
  exact ⟨g,hg,hqg,hl,hh⟩

end NLS.Articles.KdVPseudomeasures
