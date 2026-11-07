import NLS.KdV.HillSpectralCoreFourierPrincipal

/-! The actual native mean-zero complex Jacobian is a compact
perturbation of an explicit Banach equivalence at every physical source.
The reference includes the actual bounded off-index exponential symbol. -/
noncomputable section
open Complex
namespace NLS.KdV

/-- The genuine native reference equivalence at the same source. -/
def hillMeanZeroJacobianReference (q : HillMeanZeroSource) : HillMeanZeroSource ≃L[ℂ] HillSignedComplexTarget :=
  (WeightedCoeff.meanZeroHalfFourierEquiv 2).trans
    (WeightedCoeff.zeroModeExponentialSymbolEquiv (Weight.signedSobolev (-1/2))
      (hillHminusSignedOffIndexExponent q.val))

/-- The full actual native derivative is a compact perturbation of the
actual off-index multiplier composed with the exact original free Fourier map. -/
theorem isCompactOperator_hillMeanZeroJacobian_sub_reference (q : HillMeanZeroSource)
    (hr : IsRealPeriodOneHminusOne q.val) :
    IsCompactOperator (fderiv ℂ hillMeanZeroComplexMap q-
      (hillMeanZeroJacobianReference q).toContinuousLinearMap) := by
  obtain ⟨P,U,_,hqU,_,hcore,hcompact,hmean⟩ := exists_hillSpectralCore_compact_halfFourier_neighborhood q.val hr
  let S := WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2
  let Q := WeightedCoeff.zeroModeProjection (p := 2) (Weight.signedSobolev (-1/2))
  let F := (WeightedCoeff.meanZeroHalfFourierEquiv 2).toContinuousLinearMap
  let M := (WeightedCoeff.zeroModeExponentialSymbolEquiv (p := 2) (Weight.signedSobolev (-1/2))
    (hillHminusSignedOffIndexExponent q.val)).toContinuousLinearMap
  have hd : fderiv ℂ P.physicalMeanZeroSpectralCoreMap q =
      Q.comp ((fderiv ℂ P.physicalSpectralCoreMap q.val).comp S.subtypeL) := by
    exact (Q.hasFDerivAt.comp q ((hcore q.val hqU).differentiableAt.hasFDerivAt.comp q S.subtypeL.hasFDerivAt)).fderiv
  have hF : Q.comp ((WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap.comp S.subtypeL) = F := by
    apply ContinuousLinearMap.ext
    intro h
    apply Subtype.ext
    change (WeightedCoeff.zeroModeProjection (Weight.signedSobolev (-1/2))
      (WeightedCoeff.halfFourierEquiv 2 h.val) : WeightedCoeff (Weight.signedSobolev (-1/2)) 2) = _
    exact WeightedCoeff.zeroModeProjection_coe _ _ (by
      rw [WeightedCoeff.halfFourierEquiv_apply,show h.val.val 0=0 from h.property,mul_zero])
  have hC : IsCompactOperator (fderiv ℂ P.physicalMeanZeroSpectralCoreMap q-F) := by
    have he : fderiv ℂ P.physicalMeanZeroSpectralCoreMap q-F =
        Q.comp ((fderiv ℂ P.physicalSpectralCoreMap q.val-
          (WeightedCoeff.halfFourierEquiv 2).toContinuousLinearMap).comp S.subtypeL) := by
      rw [hd,← hF]
      apply ContinuousLinearMap.ext
      intro h
      simp only [ContinuousLinearMap.comp_apply,sub_apply,map_sub]
    rw [he]
    exact ((hcompact q.val hqU).comp_clm S.subtypeL).clm_comp Q
  have he : fderiv ℂ hillMeanZeroComplexMap q-(hillMeanZeroJacobianReference q).toContinuousLinearMap =
      P.physicalMeanZeroSpectralCoreRemainder q+M.comp (fderiv ℂ P.physicalMeanZeroSpectralCoreMap q-F) := by
    apply ContinuousLinearMap.ext
    intro h
    change (fderiv ℂ hillMeanZeroComplexMap q) h-M (F h) =
      ((fderiv ℂ hillMeanZeroComplexMap q) h-M ((fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) h))+
        M ((fderiv ℂ P.physicalMeanZeroSpectralCoreMap q) h-F h)
    rw [map_sub]
    abel
  rw [he]
  exact (hmean q hqU).add (hC.clm_comp M)

end NLS.KdV
