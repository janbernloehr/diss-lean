import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Analytic inverse charts between different Banach spaces

An actual derivative equal to a bounded linear equivalence gives an
analytic inverse on explicit open neighborhoods in the two native spaces.
No identification of source and target normed types is required.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A genuine analytic local chart with the prescribed native Banach target. -/
theorem exists_analytic_openPartialHomeomorph_of_fderiv_equiv
    {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (L : E ≃L[ℂ] F)
    (hder : fderiv ℂ f x = L.toContinuousLinearMap) :
    ∃ P : OpenPartialHomeomorph E F, (P : E → F) = f ∧ x ∈ P.source ∧
      AnalyticOnNhd ℂ f P.source ∧ AnalyticOnNhd ℂ P.symm P.target := by
  have hs : HasStrictFDerivAt f L.toContinuousLinearMap x := by
    rw [← hder]
    exact hf.hasStrictFDerivAt
  let P := hs.toOpenPartialHomeomorph f
  have hP : (P : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hxP : x ∈ P.source := hs.mem_toOpenPartialHomeomorph_source
  have hG : AnalyticAt ℂ P.symm (f x) := by
    have h := P.analyticAt_symm' hxP (by rw [hP]; exact hf) (i := L) (by rw [hP]; exact hder)
    rwa [hP] at h
  let A := {a | AnalyticAt ℂ f a}
  let B := {b | AnalyticAt ℂ P.symm b}
  have hA : IsOpen A := isOpen_analyticAt ℂ f
  have hB : IsOpen B := isOpen_analyticAt ℂ P.symm
  let U := A ∩ (P.source ∩ P ⁻¹' B)
  have hU : IsOpen U := hA.inter (P.continuousOn.isOpen_inter_preimage P.open_source hB)
  let R := P.restrOpen U hU
  have hR : (R : E → F) = f := hP
  have hxR : x ∈ R.source := ⟨hxP,hf,hxP,by simpa only [mem_preimage,mem_ofPred_eq,B,hP] using hG⟩
  refine ⟨R,hR,hxR,fun a ha => ha.2.1,?_⟩
  intro b hb
  have hr : R.symm b ∈ R.source := R.map_target hb
  have hw : P (R.symm b) ∈ B := hr.2.2.2
  have he : P (R.symm b) = b := R.right_inv hb
  rw [he] at hw
  exact hw

end NLS.ComplexAnalysis
