import NLS.Fourier.ContinuousSynthesis
import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact finite correlation identities -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Fourier

/-- Group a strictly triangular finite sum by its positive lag. -/
theorem sum_triangular_by_lag (M : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ j ∈ Finset.range M, ∑ i ∈ Finset.range j, f i j) =
      ∑ r ∈ Finset.range M, ∑ n ∈ Finset.range (M-(r+1)), f n (n+r+1) := by
  cases M with
  | zero => simp
  | succ K =>
    rw [Finset.sum_range_succ' (fun j => ∑ i ∈ Finset.range j, f i j),
      Finset.sum_range_succ (fun r => ∑ n ∈ Finset.range (K+1-(r+1)), f n (n+r+1))]
    simp only [Finset.range_zero,Finset.sum_empty,Nat.sub_self,add_zero,
      Nat.add_sub_add_right]
    rw [← Finset.sum_range_diag_flip K (fun r n => f n (n+r+1))]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_range_reflect (fun i => f i (j+1)) (j+1)]
    apply Finset.sum_congr rfl
    intro r hr
    have hrj : r ≤ j := by have := Finset.mem_range.mp hr; omega
    simp only [Nat.add_sub_cancel,Nat.sub_add_cancel hrj]

/-- Squaring a finite complex sum gives the diagonal and strictly triangular terms. -/
theorem norm_sum_range_sq_triangular (z : ℕ → ℂ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, z n‖^2 =
      (∑ n ∈ Finset.range M, ‖z n‖^2)+
        2*(∑ j ∈ Finset.range M, ∑ i ∈ Finset.range j, z j*star (z i)).re := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,add_comm (∑ n ∈ Finset.range M, z n) (z M),
      Complex.sq_norm,Complex.normSq_add,← Complex.sq_norm,← Complex.sq_norm,ih,
      Finset.sum_range_succ,Finset.sum_range_succ]
    simp only [Complex.add_re,star_def,map_sum,Finset.mul_sum]
    ring

/-- The exact finite identity with all off-diagonal terms grouped by lag. -/
theorem norm_sum_range_sq_correlations (z : ℕ → ℂ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, z n‖^2 =
      (∑ n ∈ Finset.range M, ‖z n‖^2)+
        2*(∑ r ∈ Finset.range M, ∑ n ∈ Finset.range (M-(r+1)),
          z (n+r+1)*star (z n)).re := by
  rw [norm_sum_range_sq_triangular,sum_triangular_by_lag]

/-- Cancellation bounds on every correlation control the original sum. -/
theorem norm_sum_range_sq_le_correlations (z : ℕ → ℂ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, z n‖^2 ≤
      (∑ n ∈ Finset.range M, ‖z n‖^2)+
        2*(∑ r ∈ Finset.range M,
          ‖∑ n ∈ Finset.range (M-(r+1)), z (n+r+1)*star (z n)‖) := by
  rw [norm_sum_range_sq_correlations]
  gcongr
  exact (Complex.re_le_norm _).trans (norm_sum_le _ _)

end NLS.Fourier
