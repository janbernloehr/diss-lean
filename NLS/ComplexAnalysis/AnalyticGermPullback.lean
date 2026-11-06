import NLS.ComplexAnalysis.AnalyticQuadraticResolvent

/-! # Pulling back an analytic germ with exact retained properties -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis
variable {E F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem analytic_germ_pullback_properties
    (L : E →L[ℂ] H) (D : Set H) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U) (g : E → F) (hg : AnalyticOnNhd ℂ g U)
    (A : Set F) (hA : IsOpen A) (hgqA : g q∈A) (B : F → Y) (hB : AnalyticOnNhd ℂ B A)
    (P : E → Y → Prop) (hP : ∀ x, x∈U → g x∈A → L x∈D → P x (B (g x))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ G : E → Y,
      AnalyticOnNhd ℂ G V ∧ ∀ x∈V, P x (G x) := by
  let V := (U∩g ⁻¹' A)∩L ⁻¹' D
  have hV : IsOpen V := (hg.continuousOn.isOpen_inter_preimage hU hA).inter
    (hD.preimage L.continuous)
  refine ⟨V,hV,⟨⟨hqU,hgqA⟩,hqD⟩,(fun x => B (g x)),?_,?_⟩
  · intro x hx
    exact (hB (g x) hx.1.2).comp (hg x hx.1.1)
  · intro x hx
    exact hP x hx.1.1 hx.1.2 hx.2

/-- Pull back a bilinear expression and a bounded linear output map,
retaining arbitrary exact coefficient properties on the open intersection. -/
theorem analytic_bilinear_preimage_germ_properties
    {R Z : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (L : E →L[ℂ] H) (D : Set H) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U)
    (f : H → F) (hf : AnalyticOnNhd ℂ f D) (g : E → R) (hg : AnalyticOnNhd ℂ g U)
    (B : F →L[ℂ] R →L[ℂ] Y) (A : Y →L[ℂ] Z)
    (P : E → Z → Prop)
    (hP : ∀ x, x∈U → L x∈D → P x (A (B (f (L x)) (g x)))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ G : E → Z,
      AnalyticOnNhd ℂ G V ∧ ∀ x∈V, P x (G x) := by
  let V := U∩L ⁻¹' D
  refine ⟨V,hU.inter (hD.preimage L.continuous),⟨hqU,hqD⟩,
    (fun x => A (B (f (L x)) (g x))),?_,?_⟩
  · intro x hx
    have hfa := (hf (L x) hx.2).comp (L.analyticAt x)
    exact (A.analyticAt _).comp ((B.analyticAt_bilinear _).comp₂ hfa (hg x hx.1))
  · intro x hx
    exact hP x hx.1 hx.2

/-- Restrict a complex analytic germ through real bounded linear source
and target maps, in their actual native norms. -/
theorem analytic_real_linear_germ_transport
    {E0 F0 G0 H0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [NormedAddCommGroup F0] [NormedSpace ℂ F0] [NormedSpace ℝ F0] [IsScalarTower ℝ ℂ F0]
    [NormedAddCommGroup G0] [NormedSpace ℂ G0] [NormedSpace ℝ G0] [IsScalarTower ℝ ℂ G0]
    [NormedAddCommGroup H0] [NormedSpace ℝ H0]
    (J : E0 →L[ℝ] F0) (A : G0 →L[ℝ] H0) (f : F0 → G0) (a : E0)
    (hf : AnalyticAt ℂ f (J a)) : AnalyticAt ℝ (fun b => A (f (J b))) a := by
  exact (A.analyticAt _).comp (f := fun b => f (J b))
    ((hf.restrictScalars (𝕜 := ℝ)).comp (J.analyticAt a))

end NLS.ComplexAnalysis
