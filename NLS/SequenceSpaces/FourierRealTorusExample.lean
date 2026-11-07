import NLS.SequenceSpaces.FourierRealTorusNoncompact
import NLS.SequenceSpaces.InfinityTruncation

/-! Explicit physical real, mean-zero endpoint coefficients whose
weighted tails do not vanish. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

def realInverseWeightCoefficients (w : Weight) (hw : ∀ k, w (-k)=w k) :
    fourierRealZeroSubmodule w ⊤ :=
  ⟨⟨eraseZeroModeCLM w (inverseWeightCoefficients w),by
    change (eraseZeroModeCLM w (inverseWeightCoefficients w)).val 0=0
    rw [eraseZeroModeCLM_apply,if_pos rfl]⟩,by
    intro k
    simp only [eraseZeroModeCLM_apply,inverseWeightCoefficients_val,neg_eq_zero,hw]
    by_cases hk : k=0
    · simp only [if_pos hk,map_zero]
    · simp only [if_neg hk,map_inv₀,Complex.conj_ofReal]⟩

theorem realInverseWeightCoefficients_apply (w : Weight) (hw : ∀ k, w (-k)=w k) (k : ℤ) :
    (realInverseWeightCoefficients w hw).val.val.val k=if k=0 then 0 else (w k:ℂ)⁻¹ := by
  rw [realInverseWeightCoefficients,eraseZeroModeCLM_apply,inverseWeightCoefficients_val]

theorem realInverseWeightCoefficients_weighted_norm (w : Weight) (hw : ∀ k, w (-k)=w k)
    (n : ℕ) (hn : 1≤n) : w n*‖(realInverseWeightCoefficients w hw).val.val.val n‖=1 := by
  rw [realInverseWeightCoefficients_apply,if_neg (by exact_mod_cast (show n≠0 by omega)),norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),mul_inv_cancel₀ (w.positive _).ne']

theorem not_positiveWeightedC0_realInverseWeightCoefficients (w : Weight) (hw : ∀ k, w (-k)=w k) :
    ¬PositiveWeightedC0 w (realInverseWeightCoefficients w hw) := by
  intro h
  obtain ⟨N,hN⟩ := h (1/2) (by norm_num)
  have hb := hN (max N 1) (le_max_left _ _)
  rw [realInverseWeightCoefficients_weighted_norm w hw _ (le_max_right _ _)] at hb
  norm_num at hb

end NLS.WeightedCoeff
