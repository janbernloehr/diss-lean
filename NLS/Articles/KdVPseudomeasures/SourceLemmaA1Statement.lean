import NLS.Articles.KdVPseudomeasures.SourceLemmaA1

/-! Literal source denominator and all three bounds in one statement. -/
noncomputable section
open NLS.ReciprocalSeries
namespace NLS.Articles.KdVPseudomeasures

/-- The printed reciprocal series, omitting precisely the indices m=±n. -/
def sourceQuadraticReciprocal (s : ℝ) (n : ℕ) (m : ℤ) : ℝ :=
  if m=(n:ℤ) ∨ m=-(n:ℤ) then 0 else 1/|(m:ℝ)^2-(n:ℝ)^2|^s

theorem sourceQuadraticReciprocal_eq_kernel (s : ℝ) (n : ℕ) :
    sourceQuadraticReciprocal s n=quadraticPowerKernel s n := by
  funext m
  unfold sourceQuadraticReciprocal quadraticPowerKernel
  split_ifs
  · rfl
  · have he : |(m:ℝ)^2-(n:ℝ)^2|=|(n:ℝ)+(m:ℝ)| * |(n:ℝ)-(m:ℝ)| := by
      rw [show (m:ℝ)^2-(n:ℝ)^2=-(((n:ℝ)+(m:ℝ))*((n:ℝ)-(m:ℝ))) by ring,
        abs_neg,abs_mul]
    rw [he,Real.mul_rpow (abs_nonneg _) (abs_nonneg _),one_div,
      Real.rpow_neg (abs_nonneg _),Real.rpow_neg (abs_nonneg _),mul_inv]

/-- Lemma A.1, including the sharp power on each side of the logarithmic
transition. A single constant for each exponent precedes all n≥1. -/
theorem sourceLemmaA_1 (s : ℝ) (hs : (1:ℝ)/2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (sourceQuadraticReciprocal s n) ∧
      (∑' m : ℤ, sourceQuadraticReciprocal s n m) ≤
        if s < 1 then C/(n:ℝ)^(2*s-1)
        else if s=1 then C*Real.log (1+(n:ℝ))/(n:ℝ) else C/(n:ℝ)^s := by
  by_cases hlt : s < 1
  · obtain ⟨C,hC,h⟩ := sourceLemmaA_1_subcritical s hs hlt
    refine ⟨C,hC,fun n hn => ?_⟩
    simpa only [sourceQuadraticReciprocal_eq_kernel,if_pos hlt] using h n hn
  · by_cases he : s=1
    · subst s
      obtain ⟨C,hC,h⟩ := sourceLemmaA_1_harmonic
      refine ⟨C,hC,fun n hn => ?_⟩
      simpa only [sourceQuadraticReciprocal_eq_kernel,lt_self_iff_false,if_false,ite_true]
        using h n hn
    · obtain ⟨C,hC,h⟩ := sourceLemmaA_1_supercritical s (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he))
      refine ⟨C,hC,fun n hn => ?_⟩
      simpa only [sourceQuadraticReciprocal_eq_kernel,if_neg hlt,if_neg he] using h n hn

end NLS.Articles.KdVPseudomeasures
