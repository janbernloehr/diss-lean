import NLS.ComplexAnalysis.AnalyticEquivalentDerivativeInverse

/-! # Full analytic inverse neighborhoods at a normalized base point -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_analytic_inverse_neighborhoods_of_fderiv_equiv
    {f : E → F} (hf : AnalyticAt ℂ f 0) (L : E ≃L[ℂ] F)
    (hder : fderiv ℂ f 0 = L.toContinuousLinearMap) (hzero : f 0 = 0) :
    ∃ U : Set E, ∃ V : Set F, IsOpen U ∧ IsOpen V ∧ (0 : E) ∈ U ∧ (0 : F) ∈ V ∧
      f '' U = V ∧ BijOn f U V ∧ ∃ G : F → E,
        AnalyticOnNhd ℂ f U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (f a) = a) ∧ (∀ z ∈ V, G z ∈ U ∧ f (G z) = z) := by
  obtain ⟨P,hP,h0,hA,hG⟩ := exists_analytic_openPartialHomeomorph_of_fderiv_equiv hf L hder
  have h0V : (0 : F) ∈ P.target := by
    have h := P.map_source h0
    rwa [hP,hzero] at h
  refine ⟨P.source,P.target,P.open_source,P.open_target,h0,h0V,?_,?_,P.symm,hA,hG,?_,?_,?_⟩
  · rw [← hP]
    exact P.image_source_eq_target
  · rw [← hP]
    exact P.bijOn
  · have h := P.left_inv h0
    rwa [hP,hzero] at h
  · intro a ha
    rw [← hP]
    exact P.left_inv ha
  · intro z hz
    refine ⟨P.map_target hz,?_⟩
    rw [← hP]
    exact P.right_inv hz

end NLS.ComplexAnalysis
