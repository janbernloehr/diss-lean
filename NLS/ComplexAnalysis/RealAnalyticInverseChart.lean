import NLS.ComplexAnalysis.RealInverseNeighborhoodAt

/-! # Actual analytic inverse charts preserving a fixed real form -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis

/-- At any fixed real base, an equivariant analytic local diffeomorphism
has an actual open partial homeomorphism whose inverse preserves reality
on its ENTIRE target. Both analytic maps and both inverse identities are
retained by restricting the target of the original inverse chart. -/
theorem exists_real_analytic_openPartialHomeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    {x : E} (hx : x ∈ U) (hu : IsUnit (fderiv ℂ F x))
    (J : E → E) (hJ : Isometry J) (hJx : J x = x)
    (hconj : ∀ y ∈ U, F (J y) = J (F y)) :
    ∃ P : OpenPartialHomeomorph E E,
      (P : E → E) = F ∧ x ∈ P.source ∧ P.source ⊆ U ∧
      AnalyticOnNhd ℂ F P.source ∧ AnalyticOnNhd ℂ P.symm P.target ∧
      ∀ y ∈ P.target, J y = y → J (P.symm y) = P.symm y := by
  obtain ⟨P,hP,hxP,hsub,hPa,hPia⟩ := exists_analytic_openPartialHomeomorph hU hF hx hu
  have hFx : F x ∈ P.target := by rw [←hP]; exact P.map_source hxP
  obtain ⟨W,hW,hFxW,hWP,hreal⟩ := exists_fixed_inverse_neighborhood_at
    F P.symm J J hJ P.source P.target P.open_source P.open_target x hxP hJx hFx
    hPia.continuousOn (by rw [←hP]; exact P.injOn)
    (fun y hy => by rw [←hP]; exact P.left_inv hy)
    (fun y hy => ⟨P.map_target hy,by rw [←hP]; exact P.right_inv hy⟩)
    (fun y hy => hconj y (hsub hy))
  let R := (P.symm.restrOpen W hW).symm
  have hR : (R : E → E) = F := hP
  have hxR : x ∈ R.source := ⟨hxP,by change P x ∈ W; rw [hP]; exact hFxW⟩
  have hRS : R.source ⊆ P.source := fun _ hy => hy.1
  have hRT : R.target ⊆ P.target := fun _ hy => hy.1
  refine ⟨R,hR,hxR,hRS.trans hsub,hPa.mono hRS,hPia.mono hRT,?_⟩
  intro y hy hJy
  exact hreal y hy.2 hJy

end NLS.ComplexAnalysis
