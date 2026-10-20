import NLS.SequenceSpaces.WeightedMultiplier

/-! # Weighted sequence realization by norm domination

Pointwise domination preserves membership and the norm bound in a weighted sequence space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise norm domination realizes a raw sequence in the same weighted
space with the corresponding norm bound, including exponent infinity. -/
theorem exists_of_norm_le (w : Weight) (a : WeightedCoeff w p)
    (f : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C*‖a.val n‖) :
    ∃ b : WeightedCoeff w p, (∀ n, b.val n = f n) ∧ ‖b‖ ≤ C*‖a‖ := by
  have hmem : Memℓp (fun n => (w n:ℂ)*f n) p := by
    apply ((lp.memℓp (weightEquiv w p a)).norm.const_mul C).mono
    intro n
    simp only [norm_mul,weightEquiv_apply,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (w.positive n)]
    nlinarith [mul_le_mul_of_nonneg_left (hf n) (w.positive n).le]
  let b : WeightedCoeff w p := ⟨f,hmem⟩
  refine ⟨b,fun _ => rfl,?_⟩
  have h : ‖weightEquiv w p b‖ ≤ ‖(C:ℂ) • weightEquiv w p a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro n
    change ‖(w n:ℂ)*f n‖ ≤ ‖(C:ℂ)*((w n:ℂ)*a.val n)‖
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (w.positive n),abs_of_nonneg hC]
    nlinarith [mul_le_mul_of_nonneg_left (hf n) (w.positive n).le]
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,← norm_eq] using h

end NLS.WeightedCoeff
