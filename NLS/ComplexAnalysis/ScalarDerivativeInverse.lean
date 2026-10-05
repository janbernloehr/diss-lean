import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # A local analytic inverse at a scalar derivative -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A nonzero scalar derivative at zero gives an actual two-sided analytic
local inverse, whose derivative is multiplication by the reciprocal scalar. -/
theorem exists_analytic_localInverse_of_scalar_derivative
    (F : E → E) (hF : AnalyticAt ℂ F 0) (hzero : F 0 = 0)
    (c : ℂ) (hc : c ≠ 0) (hd : fderiv ℂ F 0 = c • ContinuousLinearMap.id ℂ E) :
    ∃ G : E → E, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      (∀ᶠ x in 𝓝 (0 : E), G (F x) = x) ∧
      (∀ᶠ y in 𝓝 (0 : E), F (G y) = y) ∧
      fderiv ℂ G 0 = c⁻¹ • ContinuousLinearMap.id ℂ E := by
  let e : E ≃L[ℂ] E :=
    { LinearEquiv.smulOfNeZero ℂ E c hc with
      continuous_toFun := continuous_const_smul c
      continuous_invFun := continuous_const_smul c⁻¹ }
  have he : e.toContinuousLinearMap = c • ContinuousLinearMap.id ℂ E := by
    ext x
    rfl
  have hei : e.symm.toContinuousLinearMap = c⁻¹ • ContinuousLinearMap.id ℂ E := by
    ext x
    rfl
  have hs : HasStrictFDerivAt F e.toContinuousLinearMap 0 := by
    have h := hF.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
    rw [hd,← he] at h
    exact h
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : E → E) = F := hs.toOpenPartialHomeomorph_coe
  have hG : AnalyticAt ℂ P.symm (F 0) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hF) (i := e) (by rw [hP]; exact hd.trans he.symm)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,?_,?_,hs.eventually_left_inverse,?_,?_⟩
  · simpa only [hzero] using! hG
  · simpa only [hzero] using hs.localInverse_apply_image
  · simpa only [hzero] using hs.eventually_right_inverse
  · have h := hs.to_localInverse.hasFDerivAt.fderiv
    simpa only [hzero,hei] using h

end NLS.ComplexAnalysis
