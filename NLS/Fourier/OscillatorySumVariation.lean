import NLS.Fourier.ContinuousSynthesis

/-! # Variation bounds for oscillatory sums

An algebraic summation-by-parts prerequisite for the printed A.5 series.
The actual phase estimates must still supply the multiplier hypotheses.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.Fourier

/-- Discrete integration by parts, with endpoints valid also for an empty sum. -/
theorem sum_range_mul_difference (z b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, b n*(z (n+1)-z n)) =
      b N*z N-b 0*z 0-
        ∑ n ∈ Finset.range N, (b (n+1)-b n)*z (n+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    ring

/-- A reciprocal-difference multiplier turns total variation into cancellation. -/
theorem norm_sum_range_le_of_multiplier_variation (z b : ℕ → ℂ) (N : ℕ)
    (B V : ℝ) (hz : ∀ n ≤ N, ‖z n‖ ≤ 1)
    (hb0 : ‖b 0‖ ≤ B) (hbN : ‖b N‖ ≤ B)
    (hrec : ∀ n < N, b n*(z (n+1)-z n) = z n)
    (hvar : ∑ n ∈ Finset.range N, ‖b (n+1)-b n‖ ≤ V) :
    ‖∑ n ∈ Finset.range N, z n‖ ≤ 2*B+V := by
  have he : (∑ n ∈ Finset.range N, z n) =
      b N*z N-b 0*z 0-∑ n ∈ Finset.range N, (b (n+1)-b n)*z (n+1) := by
    rw [← sum_range_mul_difference]
    exact Finset.sum_congr rfl fun n hn => (hrec n (Finset.mem_range.mp hn)).symm
  have hN : ‖b N*z N‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hz N le_rfl)).trans hbN
  have h0 : ‖b 0*z 0‖ ≤ B := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hz 0 (Nat.zero_le _))).trans hb0
  have hv : ‖∑ n ∈ Finset.range N, (b (n+1)-b n)*z (n+1)‖ ≤ V := by
    apply (norm_sum_le _ _).trans
    apply le_trans _ hvar
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (hz (n+1) (by have := Finset.mem_range.mp hn; omega))
  rw [he]
  have h := norm_sub_le (b N*z N-b 0*z 0)
    (∑ n ∈ Finset.range N, (b (n+1)-b n)*z (n+1))
  have hb := norm_sub_le (b N*z N) (b 0*z 0)
  linarith

end NLS.Fourier
