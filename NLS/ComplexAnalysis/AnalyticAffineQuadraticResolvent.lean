import NLS.ComplexAnalysis.AnalyticQuadraticResolvent

/-! # Analytic resolvents with a quadratic term, a linear term and a constant -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis
variable {E S H R Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup R] [NormedSpace ℂ R]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem affine_quadratic_resolvent_properties_preimage
    (L : E →L[ℂ] S) (J : R →L[ℂ] E) (K : H →L[ℂ] E) (M : E →L[ℂ] Y)
    (B : H →L[ℂ] H →L[ℂ] R) (k : E) (g : S → H) (W : Set S)
    (hW : IsOpen W) (hg : AnalyticOnNhd ℂ g W) (q : E) (hq : L q∈W)
    (P : E → Y → Prop)
    (hP : ∀ x, L x∈W → P x (M (x+k-J (B (g (L x)) (g (L x)))+K (g (L x))))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ F : E → Y,
      AnalyticOnNhd ℂ F V ∧ ∀ x∈V, P x (F x) := by
  refine ⟨L ⁻¹' W,hW.preimage L.continuous,hq,
    (fun x => M (x+k-J (B (g (L x)) (g (L x)))+K (g (L x)))),?_,hP⟩
  intro x hx
  have ha := (hg (L x) hx).comp (L.analyticAt x)
  have hb := (B.analyticAt_bilinear _).comp₂ ha ha
  exact (M.analyticAt _).comp
    (((analyticAt_id.add analyticAt_const).sub ((J.analyticAt _).comp hb)).add ((K.analyticAt _).comp ha))

end NLS.ComplexAnalysis
