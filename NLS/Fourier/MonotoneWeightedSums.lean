import NLS.Fourier.OscillatorySumVariation

/-! # Decreasing positive weights preserve partial-sum cancellation -/
noncomputable section
set_option autoImplicit false
namespace NLS.Fourier

/-- Abel summation bounds positive decreasing weighted sums by the first weight. -/
theorem norm_sum_range_weighted_le (z : ℕ → ℂ) (a : ℕ → ℝ) (N : ℕ) (B : ℝ)
    (ha : ∀ n ≤ N, 0 ≤ a n) (hm : Antitone a)
    (hS : ∀ m ≤ N, ‖∑ n ∈ Finset.range m, z n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, (a n : ℂ)*z n‖ ≤ a 0*B := by
  let S : ℕ → ℂ := fun m => ∑ n ∈ Finset.range m, z n
  have hs (n : ℕ) : S (n+1)-S n = z n := by
    simp only [S,Finset.sum_range_succ,add_sub_cancel_left]
  have he := sum_range_mul_difference S (fun n => (a n : ℂ)) N
  simp only [hs,S,Finset.range_zero,Finset.sum_empty,mul_zero,sub_zero] at he
  have hN : ‖(a N : ℂ)*S N‖ ≤ a N*B := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha N le_rfl)]
    exact mul_le_mul_of_nonneg_left (hS N le_rfl) (ha N le_rfl)
  have hv : ‖∑ n ∈ Finset.range N, ((a (n+1) : ℂ)-a n)*S (n+1)‖ ≤
      (a 0-a N)*B := by
    apply (norm_sum_le _ _).trans
    have hb (n : ℕ) (hn : n ∈ Finset.range N) :
        ‖((a (n+1) : ℂ)-a n)*S (n+1)‖ ≤ (a n-a (n+1))*B := by
      rw [norm_mul,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (hm (by omega)))]
      have hnN := Finset.mem_range.mp hn
      have h := mul_le_mul_of_nonneg_left (hS (n+1) (by omega))
        (show 0 ≤ a n-a (n+1) from sub_nonneg.mpr (hm (by omega)))
      simpa only [neg_sub] using h
    calc
      _ ≤ ∑ n ∈ Finset.range N, (a n-a (n+1))*B := Finset.sum_le_sum hb
      _ = (a 0-a N)*B := by rw [← Finset.sum_mul,Finset.sum_range_sub']
  rw [he]
  have hb := norm_sub_le ((a N : ℂ)*S N)
    (∑ n ∈ Finset.range N, ((a (n+1) : ℂ)-a n)*S (n+1))
  change ‖(a N : ℂ)*S N-∑ n ∈ Finset.range N,
    ((a (n+1) : ℂ)-a n)*S (n+1)‖ ≤ a 0*B
  linarith

end NLS.Fourier
