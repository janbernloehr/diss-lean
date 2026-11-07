import NLS.FunctionalAnalysis.CompactDenseRange

/-! A compact perturbation of an explicit Banach equivalence with a
bounded right inverse is an equivalence with exactly that inverse.
The inverse differs compactly from the reference inverse as well. -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem bijective_of_compact_sub_equiv_rightInverse (e : E ≃L[ℂ] F)
    (A : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap))
    (hr : A.comp R=ContinuousLinearMap.id ℂ F) : Function.Bijective A := by
  let B := e.symm.toContinuousLinearMap.comp A
  have he : B-1 = e.symm.toContinuousLinearMap.comp (A-e.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro x
    change e.symm (A x)-x=e.symm (A x-e x)
    rw [map_sub,e.symm_apply_apply]
  have hB : Function.Surjective B := by
    intro x
    refine ⟨R (e x),?_⟩
    have h := congrArg (fun L : F →L[ℂ] F => L (e x)) hr
    change A (R (e x))=e x at h
    change e.symm (A (R (e x)))=x
    rw [h,e.symm_apply_apply]
  have hbij := bijective_of_denseRange_compact_sub_id B
    (by rw [he]; exact hc.clm_comp e.symm.toContinuousLinearMap) hB.denseRange
  refine ⟨fun x y h => hbij.1 (congrArg e.symm h),?_⟩
  intro y
  refine ⟨R y,?_⟩
  exact congrArg (fun L : F →L[ℂ] F => L y) hr

def equivOfCompactRightInverse (e : E ≃L[ℂ] F)
    (A : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap))
    (hr : A.comp R=ContinuousLinearMap.id ℂ F) : E ≃L[ℂ] F where
  toFun := A
  invFun := R
  map_add' := map_add A
  map_smul' := map_smul A
  left_inv x := by
    apply (bijective_of_compact_sub_equiv_rightInverse e A R hc hr).1
    exact congrArg (fun L : F →L[ℂ] F => L (A x)) hr
  right_inv y := congrArg (fun L : F →L[ℂ] F => L y) hr
  continuous_toFun := A.continuous
  continuous_invFun := R.continuous

theorem equivOfCompactRightInverse_symm (e : E ≃L[ℂ] F)
    (A : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap))
    (hr : A.comp R=ContinuousLinearMap.id ℂ F) :
    (equivOfCompactRightInverse e A R hc hr).symm.toContinuousLinearMap=R := rfl

omit [CompleteSpace E] in
theorem isCompactOperator_rightInverse_sub_equiv_inverse (e : E ≃L[ℂ] F)
    (A : E →L[ℂ] F) (R : F →L[ℂ] E)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap))
    (hr : A.comp R=ContinuousLinearMap.id ℂ F) :
    IsCompactOperator (R-e.symm.toContinuousLinearMap) := by
  have he : R-e.symm.toContinuousLinearMap =
      -(e.symm.toContinuousLinearMap.comp ((A-e.toContinuousLinearMap).comp R)) := by
    apply ContinuousLinearMap.ext
    intro y
    have h := congrArg (fun L : F →L[ℂ] F => L y) hr
    change A (R y)=y at h
    change R y-e.symm y = -e.symm (A (R y)-e (R y))
    rw [h,map_sub,e.symm_apply_apply]
    abel
  rw [he]
  exact ((hc.comp_clm R).clm_comp e.symm.toContinuousLinearMap).neg

end NLS.CompactSpectrum
