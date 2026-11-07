import NLS.SequenceSpaces.QuadraticActionLifting
import NLS.SequenceSpaces.WeightedFrequencyRemainders

/-! A common complex quadratic action image transfers an entire
frequency family and its weighted bounds, including at zero actions. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem quadratic_action_image_frequency_decay
    (U : Set (Coeff 2 × Coeff 2)) (hU : IsOpen U) (z₀ : Coeff 2 × Coeff 2) (hz₀ : z₀∈U)
    (f : ℕ+ → (Coeff 2 × Coeff 2) → ℂ) (g : ℕ+ → Coeff 1 → ℂ)
    (he : ∀ n, ∀ z∈U, f n z=g n (quadraticActionsExponent (q := 1) z))
    (w : ℤ → ℝ) (K : ℕ) (M : ℝ)
    (hb : ∀ z∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n z‖≤M) :
    ∃ T : Set (Coeff 1), IsOpen T ∧ quadraticActionsExponent (q := 1) z₀∈T ∧
      T=quadraticActionsExponent (q := 1) '' U ∧
      (∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖g n a‖≤M) ∧
      ((∀ z∈U, Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖f ⟨n+1,by omega⟩ z‖) atTop (𝓝 0)) →
        ∀ a∈T, Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖g ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  refine ⟨quadraticActionsExponent (q := 1) '' U,
    isOpenMap_quadraticActionsExponent (by norm_num : (2 : ℝ≥0∞)≠⊤) U hU,
    mem_image_of_mem _ hz₀,rfl,?_,?_⟩
  · rintro a ⟨z,hz,rfl⟩ n hn
    rw [← he n z hz]
    exact hb z hz n hn
  · intro hd a ha
    obtain ⟨z,hz,rfl⟩ := ha
    exact tendsto_positive_weighted_of_eq w (fun n => f n z)
      (fun n => g n (quadraticActionsExponent (q := 1) z)) (fun n => he n z hz) (hd z hz)

end NLS.Coeff
