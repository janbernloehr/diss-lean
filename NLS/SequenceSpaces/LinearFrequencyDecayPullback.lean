import NLS.SequenceSpaces.WeightedFrequencyRemainders
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! An exact continuous linear change of source coordinates transfers
common complex frequency bounds and pointwise tails in the source norm. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Coeff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_linear_frequency_decay_pullback
    (N : E →L[ℂ] F) (f : ℕ+ → E → ℂ) (g : ℕ+ → F → ℂ)
    (he : ∀ n a, f n a=g n (N a)) (T : Set F) (hT : IsOpen T)
    (hg : ∀ n, AnalyticOnNhd ℂ (g n) T) (a₀ : E) (ha₀ : N a₀∈T)
    (w : ℤ → ℝ) (K : ℕ) (M : ℝ)
    (hb : ∀ a∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖g n a‖≤M) :
    ∃ U : Set E, IsOpen U ∧ a₀∈U ∧ U⊆N ⁻¹' T ∧
      (∀ n, AnalyticOnNhd ℂ (f n) U) ∧
      (∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → w (n:ℤ)*‖f n a‖≤M) ∧
      ((∀ a∈T, Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖g ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) →
        ∀ a∈U, Tendsto (fun n : ℕ => w ((n+1:ℕ):ℤ)*‖f ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  refine ⟨N ⁻¹' T,hT.preimage N.continuous,ha₀,Subset.rfl,?_,?_,?_⟩
  · intro n a ha
    apply ((hg n (N a) ha).comp (N.analyticAt a)).congr
    exact Filter.Eventually.of_forall (fun b => (he n b).symm)
  · intro a ha n hn
    rw [he]
    exact hb (N a) ha n hn
  · intro hd a ha
    exact tendsto_positive_weighted_of_eq w (fun n => g n (N a)) (fun n => f n a)
      (fun n => (he n a).symm) (hd (N a) ha)

end NLS.Coeff
