import NLS.KdV.HillAbelianFourierSymbol
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates

/-! # The actual mean-zero Abelian derivative is the invertible Fourier operator -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem fderiv_meanZeroAbelianMap_eq
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZ : DifferentiableAt ℂ Z 0)
    (hF : ∀ h : Coeff 2, h 0 = 0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j = (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h j) :
    fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z) 0 =
      hillAbelianWeightedFourierEquiv.toContinuousLinearMap := by
  have hd := WeightedCoeff.hasFDerivAt_meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
    (fderiv ℂ Z 0) hZ.hasFDerivAt
  rw [hd.fderiv]
  ext h j
  by_cases hj : j = 0
  · subst j
    have hzero (a : DeletedCoeff 2 0) : a.val 0 = 0 := a.property
    exact (hzero _).trans (hzero _).symm
  · change Coeff.deleteCoordinate 0
      (WeightedCoeff.weightEquiv (hillAbelianTargetWeight SpectralWeight.one) 2 ((fderiv ℂ Z 0) h.val)) j = _
    rw [Coeff.deleteCoordinate_apply_other 0 j hj,WeightedCoeff.weightEquiv_apply,hF h.val h.property j]
    exact (hillAbelianWeightedFourierEquiv_apply h j).symm

theorem isUnit_fderiv_meanZeroAbelianMap
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZ : DifferentiableAt ℂ Z 0)
    (hF : ∀ h : Coeff 2, h 0 = 0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j = (Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h j) :
    IsUnit (fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z) 0) := by
  rw [fderiv_meanZeroAbelianMap_eq Z hZ hF]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr hillAbelianWeightedFourierEquiv.bijective

end NLS.KdV
