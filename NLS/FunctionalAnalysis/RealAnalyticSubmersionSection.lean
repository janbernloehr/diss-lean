import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! # Real analytic local sections of split Banach submersions

The real analytic inverse theorem on a constructed affine slice supplies
an actual real-valued section, its base point and its prescribed actual
derivative. The source neighborhood can be chosen in advance.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An analytic map with an invertible bounded derivative has an analytic
local inverse with both inverse identities and the inverse derivative. -/
theorem exists_realAnalytic_localInverse_of_isUnit_fderiv
    {F : E → E} {x : E} (hF : AnalyticAt ℝ F x) (hu : IsUnit (fderiv ℝ F x)) :
    ∃ G : E → E, AnalyticAt ℝ G (F x) ∧ G (F x) = x ∧
      (∀ᶠ y in 𝓝 x, G (F y) = y) ∧
      (∀ᶠ z in 𝓝 (F x), F (G z) = z) ∧
      fderiv ℝ G (F x) = Ring.inverse (fderiv ℝ F x) := by
  obtain ⟨u,hu⟩ := hu
  let e := ContinuousLinearEquiv.ofUnit u
  have hs : HasStrictFDerivAt F e.toContinuousLinearMap x := by
    change HasStrictFDerivAt F (u : E →L[ℝ] E) x
    rw [hu]
    exact hF.hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : E → E) = F := hs.toOpenPartialHomeomorph_coe
  have hG : AnalyticAt ℝ P.symm (F x) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hF) (i := e) (by rw [hP]; exact hu.symm)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,hG,hs.localInverse_apply_image,
    hs.eventually_left_inverse,hs.eventually_right_inverse,?_⟩
  rw [hs.to_localInverse.hasFDerivAt.fderiv,← hu,Ring.inverse_unit]
  rfl



variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_realAnalytic_section_of_derivative_rightInverse
    (f : E → F) (a : E) (hf : AnalyticAt ℝ f a) (R : F →L[ℝ] E)
    (hR : (fderiv ℝ f a).comp R = ContinuousLinearMap.id ℝ F)
    (U : Set E) (hU : IsOpen U) (ha : a ∈ U) :
    ∃ g : F → E, ∃ V : Set F, IsOpen V ∧ f a ∈ V ∧
      AnalyticOnNhd ℝ g V ∧ g (f a) = a ∧ MapsTo g V U ∧
      (∀ z ∈ V, f (g z) = z) ∧ fderiv ℝ g (f a) = R := by
  let A : F → E := fun z => a+R (z-f a)
  have hAa : A (f a) = a := by simp [A]
  have hA (z : F) : AnalyticAt ℝ A z :=
    analyticAt_const.add ((R.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have hdA (z : F) : HasFDerivAt A R z := by
    have hd := (R.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const (f a))).const_add a
    simpa only [A,Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using hd
  let H : F → F := f ∘ A
  have hH : AnalyticAt ℝ H (f a) := by
    have hfa : AnalyticAt ℝ f (A (f a)) := by rw [hAa]; exact hf
    exact hfa.comp (hA (f a))
  have hdH : fderiv ℝ H (f a) = ContinuousLinearMap.id ℝ F := by
    have hfa : HasFDerivAt f (fderiv ℝ f a) (A (f a)) := by rw [hAa]; exact hf.differentiableAt.hasFDerivAt
    exact (hfa.comp (f a) (hdA (f a))).fderiv.trans hR
  have hHa : H (f a) = f a := by simp only [H,Function.comp_def,hAa]
  have hu : IsUnit (fderiv ℝ H (f a)) := by rw [hdH]; exact isUnit_one
  obtain ⟨b,hb,hba,_,hr,hd⟩ := exists_realAnalytic_localInverse_of_isUnit_fderiv hH hu
  rw [hHa] at hb hba hr hd
  have hdb : fderiv ℝ b (f a) = ContinuousLinearMap.id ℝ F := by
    rw [hd,hdH]
    exact Ring.inverse_one (F →L[ℝ] F)
  let g : F → E := A ∘ b
  have hga : g (f a) = a := by simp only [g,Function.comp_def,hba,hAa]
  have hg : AnalyticAt ℝ g (f a) := by
    apply (hA (b (f a))).comp hb
  have hdg : fderiv ℝ g (f a) = R := by
    have hh := (hdA (b (f a))).comp (f a) hb.differentiableAt.hasFDerivAt
    simpa only [g,hdb,ContinuousLinearMap.comp_id] using hh.fderiv
  have hmem : ∀ᶠ z in 𝓝 (f a), g z ∈ U :=
    hg.continuousAt.preimage_mem_nhds (by rw [hga]; exact hU.mem_nhds ha)
  obtain ⟨V,hV,hVo,hVa⟩ := mem_nhds_iff.mp (hg.eventually_analyticAt.and (hmem.and hr))
  exact ⟨g,V,hVo,hVa,fun z hz => (hV hz).1,hga,
    fun z hz => (hV hz).2.1,fun z hz => (hV hz).2.2,hdg⟩



end NLS.FunctionalAnalysis
