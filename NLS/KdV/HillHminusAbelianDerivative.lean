import NLS.KdV.HillMeanZeroAbelianDerivative
import NLS.SequenceSpaces.SobolevHalfWeights

/-! # The rough Abelian derivative reuses the same invertible Fourier operator

The H-minus-one source and H-minus-one-half target weights give exactly
the previously verified normalized Fourier multiplier. No new inverse or
multiplier estimate is required.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

private theorem rough_target_source_ratio (j : ℤ) :
    (Weight.sobolev (-1/2) j : ℂ)/(Weight.sobolev (-1) j : ℂ)=
      (hillAbelianTargetWeight SpectralWeight.one j : ℂ) := by
  rw [Weight.sobolev_neg_half_apply,Weight.sobolev_minus_one_apply,
    hillAbelianTargetWeight_one_sqrt,ofReal_inv,ofReal_inv,div_inv_eq_mul]
  have hsq : (Real.sqrt (1+|(j : ℝ)|) : ℂ)^2=((1+|(j : ℝ)| : ℝ) : ℂ) := by
    rw [← ofReal_pow,Real.sq_sqrt (by positivity)]
  have hs : (Real.sqrt (1+|(j : ℝ)|) : ℂ)≠0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [← hsq]
  field_simp

theorem fderiv_meanZeroHminusAbelianMap_eq
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZ : DifferentiableAt ℂ Z 0)
    (hF : ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) :
    fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
      (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))) 0=
        hillAbelianWeightedFourierEquiv.toContinuousLinearMap := by
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let J := (WeightedCoeff.weightIsometry v 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hZJ : HasFDerivAt Z (fderiv ℂ Z 0) (J 0) := by simpa only [map_zero] using hZ.hasFDerivAt
  have hDJ := hZJ.comp 0 J.hasFDerivAt
  have hd := WeightedCoeff.hasFDerivAt_meanZeroWeightedMap w (fun u => Z (J u))
    ((fderiv ℂ Z 0).comp J) hDJ
  change fderiv ℂ (WeightedCoeff.meanZeroWeightedMap w (fun u => Z (J u))) 0=_
  rw [hd.fderiv]
  ext h j
  by_cases hj : j=0
  · subst j
    have hzero (a : DeletedCoeff 2 0) : a.val 0=0 := a.property
    exact (hzero _).trans (hzero _).symm
  · have hmean : (J h.val).val 0=0 := by
      change h.val 0/(v 0 : ℂ)=0
      have h0 : h.val 0=0 := h.property
      rw [h0,zero_div]
    change Coeff.deleteCoordinate 0 (WeightedCoeff.weightEquiv w 2
      ((fderiv ℂ Z 0) (J h.val))) j=_
    rw [Coeff.deleteCoordinate_apply_other 0 j hj,WeightedCoeff.weightEquiv_apply,hF _ hmean j]
    change (w j : ℂ)*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*(J h.val).val j)=
      (hillAbelianWeightedFourierEquiv h).val j
    rw [hillAbelianWeightedFourierEquiv_apply]
    change (w j : ℂ)*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*(h.val j/(v j : ℂ)))=_
    calc
      _ = ((w j : ℂ)/(v j : ℂ))*((Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) := by ring
      _ = _ := by rw [rough_target_source_ratio]

theorem isUnit_fderiv_meanZeroHminusAbelianMap
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (hZ : DifferentiableAt ℂ Z 0)
    (hF : ∀ h : PeriodOneHminusOne, h.val 0=0 → ∀ j : ℤ,
      ((fderiv ℂ Z 0) h).val j=(Real.sqrt (2*(j.natAbs : ℝ)*Real.pi) : ℂ)⁻¹*h.val j) :
    IsUnit (fderiv ℂ (WeightedCoeff.meanZeroWeightedMap (Weight.sobolev (-1/2))
      (fun u => Z ((WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm u))) 0) := by
  rw [fderiv_meanZeroHminusAbelianMap_eq Z hZ hF]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr hillAbelianWeightedFourierEquiv.bijective

end NLS.KdV
