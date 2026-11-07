import NLS.SequenceSpaces.PositiveScalarExtension

/-! A uniformly bounded positive scalar family has its literal zero
extension in the signed infinity sequence space. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.Coeff

theorem norm_positiveScalarExtension_le (u : ℕ+ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : ∀ n : ℕ+, ‖u n‖ ≤ R) (k : ℤ) : ‖positiveScalarExtension u k‖ ≤ R := by
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hk
    change ‖positiveScalarExtension u ((m:ℕ):ℤ)‖ ≤ R
    rw [positiveScalarExtension_apply]
    exact hu m
  · rw [positiveScalarExtension_zero_of_not_mem_range u k hk,norm_zero]
    exact hR

theorem memlp_positiveScalarExtension_infty (u : ℕ+ → ℂ)
    (hbound : ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℕ+, ‖u n‖ ≤ R) :
    Memℓp (positiveScalarExtension u) ⊤ := by
  obtain ⟨R,hR,hu⟩ := hbound
  exact memℓp_infty ⟨R,by rintro _ ⟨k,rfl⟩; exact norm_positiveScalarExtension_le u R hR hu k⟩

end NLS.Coeff
