import NLS.ComplexAnalysis.ScalarFamilyTransport

/-! # Adding fixed constants while transporting a common analytic family -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem analyticOnNhd_scalarFamily_add_preimage
    (L : F ≃L[ℂ] E) (c : ι → ℂ) (G : ι → E → ℂ) (V : Set E)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) V) (i : ι) :
    AnalyticOnNhd ℂ (fun b => G i (L b)+c i) (L ⁻¹' V) := by
  intro b hb
  exact ((hG i _ hb).comp (L.analyticAt b)).add analyticAt_const

theorem scalarFamily_add_properties_preimage
    (L : F ≃L[ℂ] E) (c : ι → ℂ) (G : ι → E → ℂ) (V : Set E) (hV : IsOpen V)
    (A : Set F) (A0 : Set E) (hA : ∀ b ∈ A, L b ∈ A0) (hcone : A0 ⊆ V)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) V) (P : Prop) (hP : P) :
    IsOpen (L ⁻¹' V) ∧ A ⊆ L ⁻¹' V ∧
      (∀ i, AnalyticOnNhd ℂ (fun b => G i (L b)+c i) (L ⁻¹' V)) ∧ P :=
  ⟨hV.preimage L.continuous,fun b hb => hcone (hA b hb),
    analyticOnNhd_scalarFamily_add_preimage L c G V hG,hP⟩

end NLS.ComplexAnalysis
