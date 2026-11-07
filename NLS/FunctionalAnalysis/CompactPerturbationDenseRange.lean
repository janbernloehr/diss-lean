import NLS.FunctionalAnalysis.CompactDenseRange

/-! Dense range upgrades a compact perturbation of an explicit Banach
space equivalence to an actual continuous linear equivalence. -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem bijective_of_compact_sub_equiv_denseRange (e : E ≃L[ℂ] F)
    (A : E →L[ℂ] F) (hc : IsCompactOperator (A-e.toContinuousLinearMap))
    (hd : DenseRange A) : Function.Bijective A := by
  let B := e.symm.toContinuousLinearMap.comp A
  have he : B-1 = e.symm.toContinuousLinearMap.comp (A-e.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro x
    change e.symm (A x)-x=e.symm (A x-e x)
    rw [map_sub,e.symm_apply_apply]
  have hBd : DenseRange B := by
    exact e.symm.surjective.denseRange.comp hd e.symm.continuous
  have hbij := bijective_of_denseRange_compact_sub_id B
    (by rw [he]; exact hc.clm_comp e.symm.toContinuousLinearMap) hBd
  refine ⟨fun x y h => hbij.1 (congrArg e.symm h),?_⟩
  intro y
  obtain ⟨x,hx⟩ := hbij.2 (e.symm y)
  exact ⟨x,e.symm.injective hx⟩

/-- The constructed equivalence is exactly the supplied actual operator. -/
def equivOfCompactDenseRange (e : E ≃L[ℂ] F) (A : E →L[ℂ] F)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap)) (hd : DenseRange A) : E ≃L[ℂ] F :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (bijective_of_compact_sub_equiv_denseRange e A hc hd).1)
    (LinearMap.range_eq_top.mpr (bijective_of_compact_sub_equiv_denseRange e A hc hd).2)

@[simp] theorem equivOfCompactDenseRange_toContinuousLinearMap (e : E ≃L[ℂ] F) (A : E →L[ℂ] F)
    (hc : IsCompactOperator (A-e.toContinuousLinearMap)) (hd : DenseRange A) :
    (equivOfCompactDenseRange e A hc hd).toContinuousLinearMap = A := rfl

end NLS.CompactSpectrum
