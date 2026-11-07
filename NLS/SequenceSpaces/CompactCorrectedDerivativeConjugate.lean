import NLS.SequenceSpaces.CompactAnalyticLinearTransport

/-! Conjugation by an exact Banach coordinate equivalence preserves
the full corrected derivative, including the literal scalar identity. -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS

theorem isCompactOperator_corrected_fderiv_conjugate
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E ≃L[ℂ] F) (f : E → E) (a : E) (c : ℂ)
    (hf : DifferentiableAt ℂ f a)
    (hc : IsCompactOperator (fderiv ℂ f a+c • ContinuousLinearMap.id ℂ E)) :
    IsCompactOperator (fderiv ℂ (fun b => L (f (L.symm b))) (L a)+
      c • ContinuousLinearMap.id ℂ F) := by
  have hd : HasFDerivAt (fun b => f b+c • b)
      (fderiv ℂ f a+c • ContinuousLinearMap.id ℂ E) a :=
    hf.hasFDerivAt.add ((hasFDerivAt_id a).const_smul c)
  have hcc : IsCompactOperator (fderiv ℂ (fun b => f b+c • b) a) := by rw [hd.fderiv];exact hc
  have hca := isCompactOperator_fderiv_linear_transport L.symm.toContinuousLinearMap
    L.toContinuousLinearMap (fun b => f b+c • b) (L a)
    (by simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hd.differentiableAt)
    (by simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using hcc)
  have he : (fun b => L (f (L.symm b)+c • L.symm b))=
      (fun b => L (f (L.symm b))+c • b) := by
    funext b
    rw [map_add,map_smul,L.apply_symm_apply]
  change IsCompactOperator (fderiv ℂ (fun b => L (f (L.symm b)+c • L.symm b)) (L a)) at hca
  rw [he] at hca
  have hg : DifferentiableAt ℂ (fun b => L (f (L.symm b))) (L a) :=
    L.differentiableAt.comp _ (by
      apply DifferentiableAt.comp _ _ L.symm.differentiableAt
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf)
  have hgder : HasFDerivAt (fun b => L (f (L.symm b))+c • b)
      (fderiv ℂ (fun b => L (f (L.symm b))) (L a)+c • ContinuousLinearMap.id ℂ F) (L a) :=
    hg.hasFDerivAt.add ((hasFDerivAt_id (L a)).const_smul c)
  rw [hgder.fderiv] at hca
  exact hca

end NLS
