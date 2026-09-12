import NLS.SequenceSpaces.PowerYoung

/-!
# The exponent conditions in Appendix B.3

The source's single reciprocal identity produces the two powered Young
relations needed for the nested convolution estimate.
-/

noncomputable section
namespace NLS

/-- The finite positive real exponents in the displayed mixed Young inequality. -/
structure MixedYoungRelation (α β γ p₁ p₂ p₃ : ℝ) : Prop where
  alpha_pos : 0 < α
  beta_pos : 0 < β
  beta_le_p₁ : β ≤ p₁
  p₁_le_gamma : p₁ ≤ γ
  alpha_le_p₂ : α ≤ p₂
  alpha_le_p₃ : α ≤ p₃
  relation : 1 / α + 1 / β + 1 / γ = 1 / p₁ + 1 / p₂ + 1 / p₃

namespace MixedYoungRelation
variable {α β γ p₁ p₂ p₃ : ℝ} (h : MixedYoungRelation α β γ p₁ p₂ p₃)
include h

theorem gamma_pos : 0 < γ := (h.beta_pos.trans_le h.beta_le_p₁).trans_le h.p₁_le_gamma

/-- The intermediate exponent exists with both exact scaled Young relations. -/
theorem exists_intermediate : ∃ q : ℝ,
    PowerYoungRelation p₂ p₃ q α ∧ PowerYoungRelation p₁ q γ β := by
  let d := 1 / β + 1 / γ - 1 / p₁
  have h₁ : 1 / p₁ ≤ 1 / β := one_div_le_one_div_of_le h.beta_pos h.beta_le_p₁
  have hγ : 1 / γ ≤ 1 / p₁ :=
    one_div_le_one_div_of_le (h.beta_pos.trans_le h.beta_le_p₁) h.p₁_le_gamma
  have h₂ : 1 / p₂ ≤ 1 / α := one_div_le_one_div_of_le h.alpha_pos h.alpha_le_p₂
  have h₃ : 1 / p₃ ≤ 1 / α := one_div_le_one_div_of_le h.alpha_pos h.alpha_le_p₃
  have hd : 0 < d := by dsimp [d]; linarith [one_div_pos.mpr h.gamma_pos]
  have hdβ : d ≤ 1 / β := by dsimp [d]; linarith
  have hdα : d ≤ 1 / α := by dsimp [d]; linarith [h.relation]
  have hβq : β ≤ 1 / d := by
    simpa only [one_div_one_div] using one_div_le_one_div_of_le hd hdβ
  have hαq : α ≤ 1 / d := by
    simpa only [one_div_one_div] using one_div_le_one_div_of_le hd hdα
  refine ⟨1 / d, ⟨h.alpha_pos, h.alpha_le_p₂, h.alpha_le_p₃, hαq, ?_⟩,
    ⟨h.beta_pos, h.beta_le_p₁, hβq, h.beta_le_p₁.trans h.p₁_le_gamma, ?_⟩⟩
  · simp only [one_div_one_div]
    dsimp [d]
    linarith [h.relation]
  · simp only [one_div_one_div]
    dsimp [d]
    ring

end MixedYoungRelation
end NLS
