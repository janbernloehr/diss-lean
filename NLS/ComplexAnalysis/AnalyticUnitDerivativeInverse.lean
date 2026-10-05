import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! # Analytic local inverses at invertible derivatives -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An analytic map with an invertible bounded derivative has an analytic
local inverse with both inverse identities and the inverse derivative. -/
theorem exists_localInverse_of_isUnit_fderiv
    {F : E → E} {x : E} (hF : AnalyticAt ℂ F x) (hu : IsUnit (fderiv ℂ F x)) :
    ∃ G : E → E, AnalyticAt ℂ G (F x) ∧ G (F x) = x ∧
      (∀ᶠ y in 𝓝 x, G (F y) = y) ∧
      (∀ᶠ z in 𝓝 (F x), F (G z) = z) ∧
      fderiv ℂ G (F x) = Ring.inverse (fderiv ℂ F x) := by
  obtain ⟨u,hu⟩ := hu
  let e := ContinuousLinearEquiv.ofUnit u
  have hs : HasStrictFDerivAt F e.toContinuousLinearMap x := by
    change HasStrictFDerivAt F (u : E →L[ℂ] E) x
    rw [hu]
    exact hF.hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : E → E) = F := hs.toOpenPartialHomeomorph_coe
  have hG : AnalyticAt ℂ P.symm (F x) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hF) (i := e) (by rw [hP]; exact hu.symm)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,hG,hs.localInverse_apply_image,
    hs.eventually_left_inverse,hs.eventually_right_inverse,?_⟩
  rw [hs.to_localInverse.hasFDerivAt.fderiv,← hu,Ring.inverse_unit]
  rfl

end NLS.ComplexAnalysis
