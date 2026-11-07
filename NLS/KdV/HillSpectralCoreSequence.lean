import NLS.KdV.HillIntrinsicDiagonalSequence
import NLS.KdV.HillOnIndexBoundedExponent
import NLS.SequenceSpaces.CompactZeroTailGauge

/-! The actual spectral core removes the on-index phase from the
intrinsic diagonal sequence. Its exact samples are the midpoint and
physical Dirichlet sheet polynomials with the original normalization.
The full complex derivative changes by an actual compact operator. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def physicalSpectralFactorPlus (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num)
      (P.sourcePsi q) ((n:ℕ):ℤ)-P.physicalDirichletRootCoefficient n q)

def physicalSpectralFactorMinus (P : HillProductEquationPatch) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
    (P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num)
      (P.sourcePsi q) ((n:ℕ):ℤ)+P.physicalDirichletRootCoefficient n q)

def physicalSpectralCoreMap (P : HillProductEquationPatch) :
    PeriodOneHminusOne → WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  WeightedCoeff.removeExponentialSymbol (Weight.signedSobolev (-1/2))
    P.physicalOnIndexSignedExponent hillHminusIntrinsicDiagonalMap

theorem analytic_physicalSpectralCoreMap (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    AnalyticOnNhd ℂ P.physicalSpectralCoreMap (P.physicalDirichletSource ∩ hillHminusActionAngleNativeDomain) := by
  intro q hq
  exact WeightedCoeff.analyticAt_removeExponentialSymbol _ _ _ q
    (P.analytic_physicalOnIndexSignedExponent H q hq.1)
    (analyticOnNhd_hillHminusIntrinsicDiagonalMap q hq.2)

theorem physicalSpectralCoreMap_zero_mode (P : HillProductEquationPatch) (q : PeriodOneHminusOne) :
    (P.physicalSpectralCoreMap q).val 0=0 := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (P.physicalOnIndexSignedExponent q)).symm
    (hillHminusIntrinsicDiagonalMap q)).val 0=0
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,hillHminusIntrinsicDiagonalMap_zero_mode,mul_zero]

theorem physicalSpectralCoreMap_positive (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+)
    (hc : hillHminusDiagonalCartesianMinus n q=P.physicalOnIndexCartesianMinus n q) :
    (P.physicalSpectralCoreMap q).val ((n:ℕ):ℤ) = P.physicalSpectralFactorMinus n q/
      (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (P.physicalOnIndexSignedExponent q)).symm
    (hillHminusIntrinsicDiagonalMap q)).val _ = _
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,P.physicalOnIndexSignedExponent_positive H q hq,
    hillHminusIntrinsicDiagonalMap_positive q hnative,hc]
  change Complex.exp (-(-I*P.physicalOnIndexAbelianCorrection n q))*
    (P.physicalSpectralFactorMinus n q*Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)/
      (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) = _
  have he : Complex.exp (-(-I*P.physicalOnIndexAbelianCorrection n q))*
      Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)=1 := by
    rw [← Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  calc
    _ = P.physicalSpectralFactorMinus n q*
      (Complex.exp (-(-I*P.physicalOnIndexAbelianCorrection n q))*Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q))/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by ring
    _ = _ := by rw [he,mul_one]

theorem physicalSpectralCoreMap_negative (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+)
    (hc : hillHminusDiagonalCartesianPlus n q=P.physicalOnIndexCartesianPlus n q) :
    (P.physicalSpectralCoreMap q).val (-((n:ℕ):ℤ)) = P.physicalSpectralFactorPlus n q/
      (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by
  change ((WeightedCoeff.exponentialSymbolEquiv _ (P.physicalOnIndexSignedExponent q)).symm
    (hillHminusIntrinsicDiagonalMap q)).val _ = _
  rw [WeightedCoeff.exponentialSymbolEquiv_symm_apply,P.physicalOnIndexSignedExponent_negative H q hq,
    hillHminusIntrinsicDiagonalMap_negative q hnative,hc]
  change Complex.exp (-(I*P.physicalOnIndexAbelianCorrection n q))*
    (P.physicalSpectralFactorPlus n q*Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)/
      (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ))) = _
  have he : Complex.exp (-(I*P.physicalOnIndexAbelianCorrection n q))*
      Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)=1 := by
    rw [← Complex.exp_add,neg_add_cancel,Complex.exp_zero]
  calc
    _ = P.physicalSpectralFactorPlus n q*
      (Complex.exp (-(I*P.physicalOnIndexAbelianCorrection n q))*Complex.exp (I*P.physicalOnIndexAbelianCorrection n q))/
        (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)*(Real.sqrt 2:ℂ)) := by ring
    _ = _ := by rw [he,mul_one]

theorem isCompactOperator_physicalOnIndexJacobianDifference (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hnative : q ∈ hillHminusActionAngleNativeDomain) :
    IsCompactOperator (fderiv ℂ hillHminusIntrinsicDiagonalMap q-fderiv ℂ P.physicalSpectralCoreMap q) :=
  WeightedCoeff.isCompactOperator_removeZeroTailExponentialSymbol_difference _ (by norm_num) _ _ q
    (P.analytic_physicalOnIndexSignedExponent H q hq)
    (analyticOnNhd_hillHminusIntrinsicDiagonalMap q hnative)
    (P.physicalOnIndexSignedExponent_zero_tail H q hq)

end NLS.KdV.HillProductEquationPatch
