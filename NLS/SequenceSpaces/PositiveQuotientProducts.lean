import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # A telescoping upper bound for positive quotient products. -/

noncomputable section
set_option autoImplicit false
namespace NLS.SequenceSpaces

theorem prod_range_div_telescope_le (a b : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (ha : ∀ k : ℕ, k < N → 0 ≤ a k) (hb : ∀ k : ℕ, k < N → 0 < b k)
    (hstep : ∀ k : ℕ, k+1 < N → a (k+1) ≤ b k) :
    (∏ k ∈ Finset.range N, a k/b k) ≤ a 0/b (N-1) := by
  have hgen : ∀ M : ℕ, 1 ≤ M → (∀ k : ℕ, k < M → 0 ≤ a k) →
      (∀ k : ℕ, k < M → 0 < b k) → (∀ k : ℕ, k+1 < M → a (k+1) ≤ b k) →
      (∏ k ∈ Finset.range M, a k/b k) ≤ a 0/b (M-1) := by
    intro M
    induction M with
    | zero => intro hM; omega
    | succ M ih =>
      intro hM hA hB hS
      by_cases hzero : M = 0
      · subst M
        simp
      · have hMp : 1 ≤ M := by omega
        have hprev := ih hMp (fun k hk => hA k (by omega)) (fun k hk => hB k (by omega))
          (fun k hk => hS k (by omega))
        have hAdj : a M ≤ b (M-1) := by
          simpa only [Nat.sub_add_cancel hMp] using hS (M-1) (by omega)
        change (∏ k ∈ Finset.range (M+1), a k/b k) ≤ a 0/b M
        rw [Finset.prod_range_succ]
        calc
          _ ≤ (a 0/b (M-1))*(a M/b M) :=
            mul_le_mul_of_nonneg_right hprev (div_nonneg (hA M (by omega)) (hB M (by omega)).le)
          _ ≤ (a 0/b (M-1))*(b (M-1)/b M) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hAdj (hB M (by omega)).le)
              (div_nonneg (hA 0 (by omega)) (hB (M-1) (by omega)).le)
          _ = a 0/b M := by
            field_simp [ne_of_gt (hB (M-1) (by omega)),ne_of_gt (hB M (by omega))]
  exact hgen N hN ha hb hstep

end NLS.SequenceSpaces
