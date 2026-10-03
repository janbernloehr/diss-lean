import NLS.SequenceSpaces.Basic

/-! # Bounded factors in summable operator sequences -/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Every ℓp sequence has a common bound on its coordinate norms. -/
theorem exists_norm_bound_of_memlp {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f : ℤ → E} (hf : Memℓp f p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hf.of_exponent_ge le_top).bddAbove
  exact ⟨max C 0,le_max_right _ _,fun n => (hC ⟨n,rfl⟩).trans (le_max_left _ _)⟩

/-- A bounded scalar sequence preserves vector-valued ℓp membership. -/
theorem memlp_smul_of_bounded_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} (a : ℤ → ℂ) (f : ℤ → E) (hf : Memℓp f p)
    (C : ℝ) (hC : ∀ n, ‖a n‖ ≤ C) : Memℓp (fun n => a n • f n) p := by
  apply (hf.norm.const_mul C).mono
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

/-- A summable scalar sequence times bounded vectors remains summable. -/
theorem memlp_smul_of_bounded_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} (a : ℤ → ℂ) (f : ℤ → E) (ha : Memℓp a p)
    (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C) : Memℓp (fun n => a n • f n) p := by
  apply (ha.norm.const_mul C).mono
  intro n
  rw [norm_smul,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)

/-- Finite changes preserve vector-valued ℓp membership, including operator sequences. -/
theorem memlp_vector_of_eq_outside_finset {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} {f g : ℤ → E} (hg : Memℓp g p)
    (s : Finset ℤ) (he : ∀ n ∉ s, f n = g n) : Memℓp f p := by
  have hs : Set.Finite {n | f n-g n ≠ 0} := by
    apply s.finite_toSet.subset
    intro n hn
    by_contra hns
    exact hn (by rw [he n hns,sub_self])
  have hd : Memℓp (fun n => f n-g n) p := (memℓp_zero hs).of_exponent_ge zero_le
  have heq : f = (fun n => f n-g n)+g := by funext n; simp
  rw [heq]
  exact hd.add hg

end NLS
