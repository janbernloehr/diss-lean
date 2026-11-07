import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-! Transport an analytic packet between abstract Banach models.
The linear maps remain opaque while verifying the common open domain. -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS

theorem exists_analytic_linear_packet_transport
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (J : E →L[ℂ] X) (K : Y →L[ℂ] Z) (U : Set X) (F : X → Y)
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U) (C : Set E) (hC : ∀ a∈C, J a∈U) :
    ∃ V : Set E, ∃ G : E → Z, IsOpen V ∧ C⊆V ∧ AnalyticOnNhd ℂ G V ∧ (∀ a∈V, J a∈U) ∧
      ∀ a∈V, G a=K (F (J a)) := by
  refine ⟨J ⁻¹' U,(fun a => K (F (J a))),hU.preimage J.continuous,hC,?_,(fun _ ha => ha),fun _ _ => rfl⟩
  intro a ha
  exact (K.analyticAt _).comp ((hF _ ha).comp (J.analyticAt a))

end NLS
