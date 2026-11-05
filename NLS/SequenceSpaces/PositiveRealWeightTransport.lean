import NLS.SequenceSpaces.PositiveWeightEquivalence

/-! # Reality under positive native weight transports -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w v : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

theorem positiveWeightEquiv_im (a : positiveSubmodule w p) (n : ℤ) :
    ((positiveWeightEquiv w v p a).val.val n).im = (w n/v n)*(a.val.val n).im := by
  rw [positiveWeightEquiv_apply]
  have he : ((w n : ℂ)*a.val.val n)/(v n : ℂ) = ((w n/v n : ℝ) : ℂ)*a.val.val n := by
    rw [Complex.ofReal_div]
    ring
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

theorem positiveWeightEquiv_im_zero_iff (a : positiveSubmodule w p) (n : ℤ) :
    ((positiveWeightEquiv w v p a).val.val n).im = 0 ↔ (a.val.val n).im = 0 := by
  rw [positiveWeightEquiv_im]
  exact mul_eq_zero.trans (or_iff_right (div_ne_zero (ne_of_gt (w.positive n)) (ne_of_gt (v.positive n))))

omit [Fact (1 ≤ p)] in
theorem positivePairMean_ext (a b : (positiveSubmodule w p × positiveSubmodule w p) × ℂ)
    (h : ∀ n : ℤ, 0 < n → (a.1.1.val.val n,a.1.2.val.val n) = (b.1.1.val.val n,b.1.2.val.val n))
    (hm : a.2 = b.2) : a = b := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.fst (h n hn)
      · exact (a.1.1.property n (by omega)).trans (b.1.1.property n (by omega)).symm
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.snd (h n hn)
      · exact (a.1.2.property n (by omega)).trans (b.1.2.property n (by omega)).symm
  · exact hm

end NLS.WeightedCoeff
