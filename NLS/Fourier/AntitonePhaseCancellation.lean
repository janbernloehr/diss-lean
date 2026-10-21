import NLS.Fourier.PhaseReciprocalMultiplier

/-! # Cancellation for decreasing phase increments -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Fourier

/-- Along a decreasing phase, total multiplier variation telescopes exactly. -/
theorem sum_norm_phaseReciprocalMultiplier_differences_antitone (t : ℕ → ℝ) (N : ℕ)
    (ht : ∀ n ≤ N, t n ∈ Ioo 0 Real.pi) (hm : Antitone t) :
    (∑ n ∈ Finset.range N,
      ‖phaseReciprocalMultiplier (t (n+1))-phaseReciprocalMultiplier (t n)‖) =
      (phaseReciprocalMultiplier (t 0)).im-(phaseReciprocalMultiplier (t N)).im := by
  have he : (∑ n ∈ Finset.range N,
      ‖phaseReciprocalMultiplier (t (n+1))-phaseReciprocalMultiplier (t n)‖) =
      ∑ n ∈ Finset.range N,
        ((phaseReciprocalMultiplier (t n)).im-(phaseReciprocalMultiplier (t (n+1))).im) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnN := Finset.mem_range.mp hn
    rw [norm_sub_rev]
    exact norm_phaseReciprocalMultiplier_sub _ _ (ht (n+1) (by omega))
      (ht n (by omega)) (hm (by omega))
  rw [he]
  have htel (k : ℕ) : (∑ n ∈ Finset.range k,
        ((phaseReciprocalMultiplier (t n)).im-(phaseReciprocalMultiplier (t (n+1))).im)) =
      (phaseReciprocalMultiplier (t 0)).im-(phaseReciprocalMultiplier (t k)).im := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; ring
  exact htel N

/-- Uniform cancellation for decreasing half-increments separated from resonance. -/
theorem norm_sum_range_le_of_separated_antitone_half_increments
    (z : ℕ → ℂ) (t : ℕ → ℝ) (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (ht : ∀ n ≤ N, δ ≤ t n ∧ t n ≤ Real.pi-δ) (hm : Antitone t)
    (hz : ∀ n ≤ N, ‖z n‖ ≤ 1)
    (hstep : ∀ n < N, z (n+1) = Complex.exp ((2*t n : ℝ)*Complex.I)*z n) :
    ‖∑ n ∈ Finset.range N, z n‖ ≤ Real.pi/δ := by
  let b : ℕ → ℂ := fun n => phaseReciprocalMultiplier (t n)
  let B : ℝ := Real.pi/(4*δ)
  have hb (n : ℕ) (hn : n ≤ N) : ‖b n‖ ≤ B :=
    norm_phaseReciprocalMultiplier_le δ (t n) hδ (ht n hn).1 (ht n hn).2
  have hi (n : ℕ) (hn : n ≤ N) : t n ∈ Ioo 0 Real.pi := by
    have h := ht n hn
    exact ⟨by linarith,by linarith⟩
  have hv : (∑ n ∈ Finset.range N, ‖b (n+1)-b n‖) ≤ 2*B := by
    rw [show (∑ n ∈ Finset.range N, ‖b (n+1)-b n‖) =
      (b 0).im-(b N).im from sum_norm_phaseReciprocalMultiplier_differences_antitone t N hi hm]
    have hN := (neg_le_abs (b N).im).trans (Complex.abs_im_le_norm (b N))
    have h0 := (le_abs_self (b 0).im).trans (Complex.abs_im_le_norm (b 0))
    linarith [hb N le_rfl,hb 0 (Nat.zero_le _)]
  have hr (n : ℕ) (hn : n < N) : b n*(z (n+1)-z n) = z n := by
    rw [hstep n hn]
    have hid := phaseReciprocalMultiplier_mul (t n)
      (Real.sin_pos_of_pos_of_lt_pi (hi n hn.le).1 (hi n hn.le).2).ne'
    calc
      _ = (b n*(Complex.exp ((2*t n : ℝ)*Complex.I)-1))*z n := by ring
      _ = z n := by rw [hid,one_mul]
  have h := norm_sum_range_le_of_multiplier_variation z b N B (2*B) hz
    (hb 0 (Nat.zero_le _)) (hb N le_rfl) hr hv
  have he : 2*B+2*B = Real.pi/δ := by dsimp only [B]; ring
  exact h.trans_eq he

end NLS.Fourier
