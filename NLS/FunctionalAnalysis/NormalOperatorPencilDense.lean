import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Dense ranges of normal-operator pencils with no eigenvectors -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An injective bounded normal operator has dense range. -/
theorem denseRange_of_isStarNormal_of_injective (A : E →L[ℂ] E)
    (hA : IsStarNormal A) (hi : Function.Injective A) : DenseRange A := by
  have hk : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
  have ho : A.range.orthogonal = ⊥ := by rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hA,hk]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (A.range.topologicalClosure_eq_top_iff.mpr ho)

/-- Shifting a normal operator by any complex scalar preserves normality. -/
theorem isStarNormal_boundedOperatorPencil (U : E →L[ℂ] E)
    (hU : IsStarNormal U) (ζ : ℂ) : IsStarNormal (U-ζ • (1 : E →L[ℂ] E)) := by
  let := hU
  apply Commute.isStarNormal_sub
  rw [star_smul,star_one]
  exact (Commute.one_right U).smul_right (star ζ)

/-- Absence of eigenvectors forces dense range at every complex pencil parameter. -/
theorem denseRange_boundedOperatorPencil_of_no_eigenvectors (U : E →L[ℂ] E)
    (hU : IsStarNormal U)
    (hno : ∀ (ζ : ℂ) (v : E), U v = ζ • v → v = 0) (ζ : ℂ) :
    DenseRange (U-ζ • (1 : E →L[ℂ] E)) := by
  apply denseRange_of_isStarNormal_of_injective _ (isStarNormal_boundedOperatorPencil U hU ζ)
  intro x y hxy
  have h : (U-ζ • (1 : E →L[ℂ] E)) (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  change U (x-y)-ζ • (x-y) = 0 at h
  exact sub_eq_zero.mp (hno ζ (x-y) (sub_eq_zero.mp h))

end NLS.FunctionalAnalysis
