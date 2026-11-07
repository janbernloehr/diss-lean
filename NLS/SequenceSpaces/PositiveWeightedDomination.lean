import NLS.SequenceSpaces.WeightedRawDomination
import NLS.SequenceSpaces.PositiveScalarExtension
import NLS.SequenceSpaces.SandwichMajorant

/-! Literal positive-index scalar coefficients with a weighted bound
by two full signed lp sequences have an actual weighted zero extension. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_positiveScalarExtension_of_weighted_norm_le (w : Weight) (a b : Coeff p)
    (u : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n : ℕ+, ‖(w ((n:ℕ):ℤ):ℂ)*u n‖ ≤
      C*(‖a ((n:ℕ):ℤ)‖+‖b ((n:ℕ):ℤ)‖)) :
    ∃ d : WeightedCoeff w p, (∀ k, d.val k = positiveScalarExtension u k) ∧
      ‖d‖ ≤ C*(‖a‖+‖b‖) := by
  let A := Coeff.magnitude a+Coeff.magnitude b
  have hA (k : ℤ) : ‖A k‖ = ‖a k‖+‖b k‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  obtain ⟨d,hd,hbound⟩ := exists_of_weighted_norm_le w A (positiveScalarExtension u) C hC (by
    intro k
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨n,rfl⟩ := hk
      change ‖(w ((n:ℕ):ℤ):ℂ)*positiveScalarExtension u ((n:ℕ):ℤ)‖ ≤ C*‖A ((n:ℕ):ℤ)‖
      rw [positiveScalarExtension_apply,hA]
      exact hu n
    · rw [positiveScalarExtension_zero_of_not_mem_range u k hk,mul_zero,norm_zero]
      exact mul_nonneg hC (norm_nonneg _))
  refine ⟨d,hd,hbound.trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  exact (norm_add_le _ _).trans_eq (by rw [Coeff.norm_magnitude,Coeff.norm_magnitude])

end NLS.WeightedCoeff
