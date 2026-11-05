import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Analytic inverse neighborhoods between different Banach spaces

The derivative is an explicit continuous linear equivalence, so the
source and target need not be the same Banach space.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_analytic_openPartialHomeomorph_of_equiv_derivative
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {x : E} (hx : x ∈ U) (e : E ≃L[ℂ] F) (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ P : OpenPartialHomeomorph E F,
      (P : E → F) = f ∧ x ∈ P.source ∧ P.source ⊆ U ∧
      AnalyticOnNhd ℂ f P.source ∧ AnalyticOnNhd ℂ P.symm P.target := by
  have hs : HasStrictFDerivAt f e.toContinuousLinearMap x := by
    rw [← hd.fderiv]
    exact (hf x hx).hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph f
  have hP : (P : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hxP : x ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hG : AnalyticAt ℂ P.symm (f x) := by
    have h := P.analyticAt_symm' hxP (by rw [hP]; exact hf x hx)
      (i := e) (by rw [hP]; exact hd.fderiv)
    rwa [hP] at h
  let W := {y | AnalyticAt ℂ P.symm y}
  have hW : IsOpen W := isOpen_analyticAt ℂ P.symm
  let V := U ∩ (P.source ∩ P ⁻¹' W)
  have hV : IsOpen V := hU.inter (P.continuousOn.isOpen_inter_preimage P.open_source hW)
  let R := P.restrOpen V hV
  have hxR : x ∈ R.source :=
    ⟨hxP,hx,hxP,by simpa only [mem_preimage,mem_ofPred_eq,W,hP] using hG⟩
  have hsub : R.source ⊆ U := fun _ h => h.2.1
  refine ⟨R,hP,hxR,hsub,hf.mono hsub,?_⟩
  intro y hy
  have hr : R.symm y ∈ R.source := R.map_target hy
  have hw : P (R.symm y) ∈ W := hr.2.2.2
  have he : P (R.symm y) = y := R.right_inv hy
  rw [he] at hw
  exact hw

theorem exists_analytic_inverse_open_sets_of_equiv_derivative
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {x : E} (hx : x ∈ U) (e : E ≃L[ℂ] F) (hd : HasFDerivAt f e.toContinuousLinearMap x) :
    ∃ V : Set E, ∃ W : Set F,
      IsOpen V ∧ IsOpen W ∧ x ∈ V ∧ f x ∈ W ∧ V ⊆ U ∧
      f '' V = W ∧ Set.BijOn f V W ∧
      ∃ g : F → E, AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ g W ∧
        (∀ y ∈ V, g (f y) = y) ∧ (∀ z ∈ W, g z ∈ V ∧ f (g z) = z) := by
  obtain ⟨P,hP,hxP,hsub,hfP,hgP⟩ :=
    exists_analytic_openPartialHomeomorph_of_equiv_derivative hU hf hx e hd
  refine ⟨P.source,P.target,P.open_source,P.open_target,hxP,?_,hsub,?_,?_,P.symm,hfP,hgP,?_,?_⟩
  · rw [← hP]; exact P.map_source hxP
  · rw [← hP]; exact P.image_source_eq_target
  · rw [← hP]; exact P.bijOn
  · intro y hy
    rw [← hP]
    exact P.left_inv hy
  · intro z hz
    refine ⟨P.map_target hz,?_⟩
    rw [← hP]
    exact P.right_inv hz

end NLS.ComplexAnalysis
