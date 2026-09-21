import NLS.SequenceSpaces.Truncation
import NLS.SequenceSpaces.SandwichMajorant

/-!
# Tail bounds under choices within pairs

A coefficient sequence obtained by choosing one of two entries at every
remaining index has tail norm bounded by the sum of the two original tail
norms. Choices may vary with the index; no continuity is needed.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise choices within pairs preserve a common small-tail bound. -/
theorem Coeff.norm_sub_truncate_le_of_mem_pair (a b c : Coeff p) (s : Finset ℤ)
    (hc : ∀ n ∉ s, c n = a n ∨ c n = b n) :
    ‖c-Coeff.truncate s c‖ ≤ ‖a-Coeff.truncate s a‖+‖b-Coeff.truncate s b‖ := by
  let A := a-Coeff.truncate s a
  let B := b-Coeff.truncate s b
  have hb (n : ℤ) : ‖(c-Coeff.truncate s c) n‖ ≤ ‖(Coeff.magnitude A+Coeff.magnitude B) n‖ := by
    simp only [lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    by_cases hn : n ∈ s
    · simp only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_pos hn,sub_self,norm_zero]
      positivity
    · simp only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hn,sub_zero]
      have ha : A n = a n := by simp [A,Coeff.truncate_apply,hn]
      have hb : B n = b n := by simp [B,Coeff.truncate_apply,hn]
      rw [ha,hb]
      rcases hc n hn with he | he
      · rw [he]; exact le_add_of_nonneg_right (norm_nonneg _)
      · rw [he]; exact le_add_of_nonneg_left (norm_nonneg _)
  exact (lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hb).trans
    ((norm_add_le _ _).trans (by simp only [Coeff.norm_magnitude]; rfl))

end NLS
