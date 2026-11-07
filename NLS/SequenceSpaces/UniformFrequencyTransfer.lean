import NLS.SequenceSpaces.QuadraticFrequencyDecayTransfer
import NLS.SequenceSpaces.LinearFrequencyDecayPullback

/-! Fixed-neighborhood uniform tails pass through the open complex
quadratic action image and exact continuous linear source changes. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

theorem quadratic_action_image_uniform_frequency_tail
    (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U) (z₀ : Coeff 2 × Coeff 2) (hz₀ : z₀∈U)
    (f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ) (g : ℕ+ → Coeff 1 → ℂ)
    (he : ∀ n, ∀ z∈U, f n z=g n (quadraticActionsExponent (q := 1) z)) (w : ℤ → ℝ)
    (hb : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ z∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n z‖≤ε) :
    ∃ T : Set (Coeff 1), IsOpen T ∧ quadraticActionsExponent (q := 1) z₀∈T ∧
      T=quadraticActionsExponent (q := 1) '' U ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖g n a‖≤ε := by
  refine ⟨quadraticActionsExponent (q := 1) '' U,
    isOpenMap_quadraticActionsExponent (by norm_num : (2:ℝ≥0∞)≠⊤) U hU,
    mem_image_of_mem _ hz₀,rfl,?_⟩
  intro ε hε
  obtain ⟨K,hK⟩ := hb ε hε
  refine ⟨K,?_⟩
  rintro a ⟨z,hz,rfl⟩ n hn
  rw [← he n z hz]
  exact hK z hz n hn

theorem exists_linear_uniform_frequency_tail_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (N : E →L[ℂ] F) (f : ℕ+ → E → ℂ) (g : ℕ+ → F → ℂ)
    (he : ∀ n a, f n a=g n (N a)) (T : Set F) (hT : IsOpen T)
    (hg : ∀ n, AnalyticOnNhd ℂ (g n) T) (a₀ : E) (ha₀ : N a₀∈T) (w : ℤ → ℝ)
    (hb : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖g n a‖≤ε) :
    ∃ U : Set E, IsOpen U ∧ a₀∈U ∧ U⊆N ⁻¹' T ∧
      (∀ n, AnalyticOnNhd ℂ (f n) U) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n a‖≤ε := by
  refine ⟨N ⁻¹' T,hT.preimage N.continuous,ha₀,Subset.rfl,?_,?_⟩
  · intro n a ha
    apply ((hg n (N a) ha).comp (N.analyticAt a)).congr
    exact Filter.Eventually.of_forall (fun b => (he n b).symm)
  · intro ε hε
    obtain ⟨K,hK⟩ := hb ε hε
    exact ⟨K,fun a ha n hn => by rw [he];exact hK (N a) ha n hn⟩

end NLS.Coeff
