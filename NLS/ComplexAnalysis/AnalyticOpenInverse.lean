import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! # Analytic inverse branches on explicit open neighborhoods

An invertible derivative gives an open partial homeomorphism whose source
lies in the original analytic domain, with forward and inverse maps
analytic throughout the source and target. Both inverse identities hold
on these sets, rather than only as germs at the base point.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An actual analytic diffeomorphism on open neighborhoods inside the given domain. -/
theorem exists_analytic_openPartialHomeomorph
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {x : E} (hx : x ∈ U) (hu : IsUnit (fderiv ℂ F x)) :
    ∃ P : OpenPartialHomeomorph E E,
      (P : E → E) = F ∧ x ∈ P.source ∧ P.source ⊆ U ∧
      AnalyticOnNhd ℂ F P.source ∧ AnalyticOnNhd ℂ P.symm P.target := by
  obtain ⟨u,hu⟩ := hu
  let e := ContinuousLinearEquiv.ofUnit u
  have hs : HasStrictFDerivAt F e.toContinuousLinearMap x := by
    change HasStrictFDerivAt F (u : E →L[ℂ] E) x
    rw [hu]
    exact (hF x hx).hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : E → E) = F := hs.toOpenPartialHomeomorph_coe
  have hxP : x ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hG : AnalyticAt ℂ P.symm (F x) := by
    have h := P.analyticAt_symm' hxP (by rw [hP]; exact hF x hx)
      (i := e) (by rw [hP]; exact hu.symm)
    rwa [hP] at h
  let W := {y | AnalyticAt ℂ P.symm y}
  have hW : IsOpen W := isOpen_analyticAt ℂ P.symm
  let V := U ∩ (P.source ∩ P ⁻¹' W)
  have hV : IsOpen V := hU.inter (P.continuousOn.isOpen_inter_preimage P.open_source hW)
  let R := P.restrOpen V hV
  have hR : (R : E → E) = F := hP
  have hxR : x ∈ R.source := ⟨hxP,hx,hxP,by simpa only [mem_preimage,mem_ofPred_eq,W,hP] using hG⟩
  have hsub : R.source ⊆ U := fun _ h => h.2.1
  refine ⟨R,hR,hxR,hsub,hF.mono hsub,?_⟩
  intro y hy
  have hr : R.symm y ∈ R.source := R.map_target hy
  have hw : P (R.symm y) ∈ W := hr.2.2.2
  have he : P (R.symm y) = y := R.right_inv hy
  rw [he] at hw
  exact hw

/-- Explicit open source and image sets, analytic inverse, and both exact inverse identities. -/
theorem exists_analytic_inverse_open_sets
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {x : E} (hx : x ∈ U) (hu : IsUnit (fderiv ℂ F x)) :
    ∃ V W : Set E, IsOpen V ∧ IsOpen W ∧ x ∈ V ∧ F x ∈ W ∧ V ⊆ U ∧
      F '' V = W ∧ Set.BijOn F V W ∧
      ∃ G : E → E, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ y ∈ V, G (F y) = y) ∧ (∀ z ∈ W, G z ∈ V ∧ F (G z) = z) := by
  obtain ⟨P,hP,hxP,hsub,hFP,hGP⟩ := exists_analytic_openPartialHomeomorph hU hF hx hu
  refine ⟨P.source,P.target,P.open_source,P.open_target,hxP,?_,hsub,?_,?_,P.symm,hFP,hGP,?_,?_⟩
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
