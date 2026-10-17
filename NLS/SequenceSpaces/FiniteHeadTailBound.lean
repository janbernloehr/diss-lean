import NLS.SequenceSpaces.TwoSequenceBound

/-! # Full norm bounds from a finite head and two tail majorants -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Retain a finite set of values, without requiring summability of the original function. -/
def finiteHead (S : Finset ℤ) (f : ℤ → ℂ) : Coeff p :=
  ∑ n ∈ S, lp.single p n (f n)

omit [Fact (1 ≤ p)] in
@[simp] theorem finiteHead_apply (S : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    finiteHead (p := p) S f n = if n ∈ S then f n else 0 := by
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n) (∑ j ∈ S, lp.single p j (f j)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]

/-- Uniform finite-head and tail bounds give actual membership and a full sequence norm bound. -/
theorem memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (f h : ℤ → ℂ) (S : Finset ℤ) (a b : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hhead : ∀ n ∈ S, ‖f n‖ ≤ ‖h n‖)
    (htail : ∀ n ∉ S, ‖f n‖ ≤ C*(‖a n‖+‖b n‖)) :
    Memℓp f p ∧ ‖ofFunctionOrZero p f‖ ≤ ‖finiteHead (p := p) S h‖+C*(‖a‖+‖b‖) := by
  let H : Coeff p := finiteHead S h
  let T : Coeff p := (C:ℂ) • (magnitude a+magnitude b)
  have hT (n : ℤ) : ‖T n‖ = C*(‖a n‖+‖b n‖) := by
    simp only [T,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply,
      magnitude_apply,← Complex.ofReal_add,← Complex.ofReal_mul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ C*(‖a n‖+‖b n‖))]
  have hb (n : ℤ) : ‖f n‖ ≤ 1*(‖H n‖+‖T n‖) := by
    rw [one_mul,hT]
    by_cases hn : n ∈ S
    · exact (hhead n hn).trans (by
        simp only [H,finiteHead_apply,if_pos hn]
        exact le_add_of_nonneg_right (mul_nonneg hC (add_nonneg (norm_nonneg _) (norm_nonneg _))))
    · simpa only [H,finiteHead_apply,if_neg hn,norm_zero,zero_add] using htail n hn
  obtain ⟨hmem,hbound⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound f H T 1 (by norm_num) hb
  have hTnorm : ‖T‖ ≤ C*(‖a‖+‖b‖) := by
    rw [show ‖T‖ = ‖(C:ℂ)‖*‖magnitude a+magnitude b‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (by simpa using norm_add_le (magnitude a) (magnitude b)) hC
  have hbound' : ‖ofFunctionOrZero p f‖ ≤ ‖H‖+‖T‖ := by simpa only [one_mul] using hbound
  exact ⟨hmem,hbound'.trans (add_le_add le_rfl hTnorm)⟩

end NLS.Coeff
