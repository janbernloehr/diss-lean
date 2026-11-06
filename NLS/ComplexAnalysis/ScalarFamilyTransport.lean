import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-! # Analytic scalar families and local bounds under a bounded equivalence -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ComplexAnalysis
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem analyticOnNhd_scalarFamily_div_preimage
    (L : F ≃L[ℂ] E) (c : ι → ℂ) (G : ι → E → ℂ) (V : Set E)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) V) (i : ι) :
    AnalyticOnNhd ℂ (fun b => G i (L b)/c i) (L ⁻¹' V) := by
  intro b hb
  exact ((hG i _ hb).comp (L.analyticAt b)).div_const

theorem scalarFamily_div_tail_bounds_preimage
    (L : F ≃L[ℂ] E) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (G : ι → E → ℂ) (J0 : ι → E → ℂ) (J : ι → F → ℂ)
    (hJ : ∀ i b, J0 i (L b) = J i b) (V : Set E)
    (hbound : ∀ b ∈ V, ∃ T : Set E, IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
      ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ d ∈ T, ∀ i ∉ s,
        ‖G i d‖ ≤ C*‖J0 i d‖^2) :
    ∀ b ∈ L ⁻¹' V, ∃ T : Set F, IsOpen T ∧ b ∈ T ∧ T ⊆ L ⁻¹' V ∧
      ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ d ∈ T, ∀ i ∉ s,
        ‖c i*(G i (L d)/c i)‖ ≤ C*‖J i d‖^2 := by
  intro b hb
  obtain ⟨T,hT,hbT,hTV,s,C,hC,hbnd⟩ := hbound (L b) hb
  refine ⟨L ⁻¹' T,hT.preimage L.continuous,hbT,fun d hd => hTV hd,s,C,hC,?_⟩
  intro d hd i hi
  rw [mul_div_cancel₀ _ (hc i)]
  have h := hbnd (L d) hd i hi
  rwa [hJ i d] at h

theorem scalarFamily_div_properties_preimage
    (L : F ≃L[ℂ] E) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (G : ι → E → ℂ) (J0 : ι → E → ℂ) (J : ι → F → ℂ)
    (hJ : ∀ i b, J0 i (L b) = J i b) (V : Set E) (hV : IsOpen V)
    (A : Set F) (A0 : Set E) (hA : ∀ b ∈ A, L b ∈ A0) (hcone : A0 ⊆ V)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) V)
    (hbound : ∀ b ∈ V, ∃ T : Set E, IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
      ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ d ∈ T, ∀ i ∉ s,
        ‖G i d‖ ≤ C*‖J0 i d‖^2)
    (P : Prop) (hP : P) :
    IsOpen (L ⁻¹' V) ∧ A ⊆ L ⁻¹' V ∧
      (∀ i, AnalyticOnNhd ℂ (fun b => G i (L b)/c i) (L ⁻¹' V)) ∧ P ∧
      ∀ b ∈ L ⁻¹' V, ∃ T : Set F, IsOpen T ∧ b ∈ T ∧ T ⊆ L ⁻¹' V ∧
        ∃ s : Finset ι, ∃ C : ℝ, 0 ≤ C ∧ ∀ d ∈ T, ∀ i ∉ s,
          ‖c i*(G i (L d)/c i)‖ ≤ C*‖J i d‖^2 :=
  ⟨hV.preimage L.continuous,fun b hb => hcone (hA b hb),
    analyticOnNhd_scalarFamily_div_preimage L c G V hG,hP,
    scalarFamily_div_tail_bounds_preimage L c hc G J0 J hJ V hbound⟩

end NLS.ComplexAnalysis
