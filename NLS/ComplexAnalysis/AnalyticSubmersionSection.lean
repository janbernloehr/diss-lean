import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse
import NLS.FunctionalAnalysis.FiniteCotangentProjection

/-! # Actual analytic local sections of finite-dimensional submersions

A bounded right inverse of the actual derivative supplies an affine
slice. The analytic inverse theorem on that slice gives a local section,
with its value and derivative prescribed, inside any chosen source
neighborhood. No local inverse or source section is assumed.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_analytic_section_of_derivative_rightInverse
    (f : E → F) (a : E) (hf : AnalyticAt ℂ f a) (R : F →L[ℂ] E)
    (hR : (fderiv ℂ f a).comp R = ContinuousLinearMap.id ℂ F)
    (U : Set E) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : F → E, ∃ V : Set F, IsOpen V ∧ f a ∈ V ∧
      AnalyticOnNhd ℂ g V ∧ g (f a) = a ∧ MapsTo g V U ∧
      (∀ z ∈ V, f (g z) = z) ∧ fderiv ℂ g (f a) = R := by
  let A : F → E := fun z => a+R (z-f a)
  have hAa : A (f a) = a := by simp [A]
  have hA (z : F) : AnalyticAt ℂ A z :=
    analyticAt_const.add ((R.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have hdA (z : F) : HasFDerivAt A R z := by
    have hd := (R.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (f a))).const_add a
    simpa only [A,Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using hd
  let H : F → F := f ∘ A
  have hH : AnalyticAt ℂ H (f a) := by
    have hfa : AnalyticAt ℂ f (A (f a)) := by rw [hAa]; exact hf
    exact hfa.comp (hA (f a))
  have hdH : fderiv ℂ H (f a) = ContinuousLinearMap.id ℂ F := by
    have hfa : HasFDerivAt f (fderiv ℂ f a) (A (f a)) := by rw [hAa]; exact hf.differentiableAt.hasFDerivAt
    exact (hfa.comp (f a) (hdA (f a))).fderiv.trans hR
  have hHa : H (f a) = f a := by simp only [H,Function.comp_def,hAa]
  have hu : IsUnit (fderiv ℂ H (f a)) := by rw [hdH]; exact isUnit_one
  obtain ⟨b,hb,hba,_,hr,hd⟩ := exists_localInverse_of_isUnit_fderiv hH hu
  rw [hHa] at hb hba hr hd
  have hdb : fderiv ℂ b (f a) = ContinuousLinearMap.id ℂ F := by
    rw [hd,hdH]
    exact Ring.inverse_one (F →L[ℂ] F)
  let g : F → E := A ∘ b
  have hga : g (f a) = a := by simp only [g,Function.comp_def,hba,hAa]
  have hg : AnalyticAt ℂ g (f a) := by
    apply (hA (b (f a))).comp hb
  have hdg : fderiv ℂ g (f a) = R := by
    have hh := (hdA (b (f a))).comp (f a) hb.differentiableAt.hasFDerivAt
    simpa only [g,hdb,ContinuousLinearMap.comp_id] using hh.fderiv
  have hmem : ∀ᶠ z in 𝓝 (f a), g z ∈ U :=
    hg.continuousAt.preimage_mem_nhds (by rw [hga]; exact hU.mem_nhds ha)
  obtain ⟨V,hV,hVo,hVa⟩ := mem_nhds_iff.mp (hg.eventually_analyticAt.and (hmem.and hr))
  exact ⟨g,V,hVo,hVa,fun z hz => (hV hz).1,hga,
    fun z hz => (hV hz).2.1,fun z hz => (hV hz).2.2,hdg⟩

end NLS.ComplexAnalysis
