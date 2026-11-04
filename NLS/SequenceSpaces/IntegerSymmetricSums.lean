import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Symmetric integer sums and paired nonnegative cutoffs in arbitrary additive commutative monoids. -/

noncomputable section
set_option autoImplicit false
namespace NLS.SequenceSpaces
theorem sum_symmetric_interval {A : Type*} [AddCommMonoid A] (f : ℤ → A) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n) =
      f 0 + ∑ j ∈ Finset.range N, (f ((j : ℤ)+1) + f (-((j : ℤ)+1))) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : Finset.Icc (-(↑(N+1) : ℤ)) (↑(N+1) : ℤ) =
        insert (-(↑(N+1) : ℤ)) (insert (↑(N+1) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hleft : -(↑(N+1) : ℤ) ∉ insert (↑(N+1) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hright : (↑(N+1) : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hs, Finset.sum_insert hleft, Finset.sum_insert hright, ih, Finset.sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one]
    ac_rfl

theorem sum_range_one_and_pairs {A : Type*} [AddCommMonoid A] (f : ℕ → A) (N : ℕ) :
    (∑ j ∈ Finset.range (2*N+1), f j) = f 0+∑ k ∈ Finset.range N, (f (2*k+1)+f (2*k+2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)+1 = (2*N+1)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    rw [show 2*N+1+1 = 2*N+2 by omega]
    ac_rfl

end NLS.SequenceSpaces
