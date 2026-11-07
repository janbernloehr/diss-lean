import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Analytic quadratic resolvents in different Banach norms -/
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

/-- An analytic germ in an auxiliary norm gives a quadratic resolvent
analytic in the desired target norm. Arbitrary exact recovery properties
are retained on the whole open preimage. -/
theorem quadratic_resolvent_properties_preimage
    (L : E →L[ℂ] S) (J : R →L[ℂ] E) (M : E →L[ℂ] Y)
    (B : H →L[ℂ] H →L[ℂ] R) (g : S → H) (W : Set S)
    (hW : IsOpen W) (hg : AnalyticOnNhd ℂ g W) (q : E) (hq : L q∈W)
    (P : E → Y → Prop)
    (hP : ∀ x, L x∈W → P x (M (x-J (B (g (L x)) (g (L x)))))) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ F : E → Y,
      AnalyticOnNhd ℂ F V ∧ ∀ x∈V, P x (F x) := by
  refine ⟨L ⁻¹' W,hW.preimage L.continuous,hq,
    (fun x => M (x-J (B (g (L x)) (g (L x))))),?_,hP⟩
  intro x hx
  have ha := (hg (L x) hx).comp (L.analyticAt x)
  have hb := (B.analyticAt_bilinear _).comp₂ ha ha
  exact (M.analyticAt _).comp (analyticAt_id.sub ((J.analyticAt _).comp hb))

/-- Restrict an analytic branch to an open source preimage, add a fixed
strong-target vector, and retain arbitrary exact recovery properties. -/
theorem analytic_add_const_properties_inter_preimage
    (L : E →L[ℂ] S) (W : Set S) (hW : IsOpen W) (V : Set E) (hV : IsOpen V)
    (g : E → Y) (hg : AnalyticOnNhd ℂ g V) (k : Y) (q : E)
    (hqV : q∈V) (hqW : L q∈W) (P : E → Y → Prop)
    (hP : ∀ x, x∈V → L x∈W → P x (g x+k)) :
    ∃ D : Set E, IsOpen D ∧ q∈D ∧ ∃ F : E → Y,
      AnalyticOnNhd ℂ F D ∧ ∀ x∈D, P x (F x) := by
  refine ⟨V ∩ L ⁻¹' W,hV.inter (hW.preimage L.continuous),⟨hqV,hqW⟩,
    (fun x => g x+k),(fun x hx => (hg x hx.1).add analyticAt_const),?_⟩
  intro x hx
  exact hP x hx.1 hx.2

end NLS.ComplexAnalysis
