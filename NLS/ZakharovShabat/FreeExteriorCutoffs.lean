import NLS.ZakharovShabat.FreeDerivativeZeroCounts

/-!
# Common cutoffs for free circles and exterior root confinement

These geometric statements depend only on a spectral threshold and disc radius,
so one cutoff can be used for an entire family of potentials.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- One positive integer moves every subsequent free center beyond the required margin. -/
theorem exists_free_center_cutoff (R r : ℝ) :
    ∃ N : ℕ, 0 < N ∧ R+r ≤ Real.pi*(N : ℝ) := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((R+r)/Real.pi)
  refine ⟨M+1, by omega, ?_⟩
  have h : (R+r)/Real.pi ≤ ((M+1 : ℕ) : ℝ) := by push_cast; linarith
  exact (div_le_iff₀ Real.pi_pos).mp h |>.trans_eq (mul_comm _ _)

/-- The margin at a free center bounds the norm of every point on its circle. -/
theorem norm_ge_of_mem_freeSphere {R r : ℝ} {N : ℕ}
    (hN : R+r ≤ Real.pi*(N : ℝ)) {n : ℤ} (hn : N ≤ n.natAbs)
    {z : ℂ} (hz : z ∈ sphere ((Real.pi : ℂ)*n) r) : R ≤ ‖z‖ := by
  have hd : ‖z-(Real.pi : ℂ)*n‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hz
  have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have ht := norm_sub_norm_le ((Real.pi : ℂ)*n) z
  rw [norm_sub_rev, hd, hnorm] at ht
  have hn' : (N : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
  nlinarith [Real.pi_pos]

/-- The same cutoff places every subsequent central circle beyond the threshold. -/
theorem threshold_le_centralCircleRadius {R r : ℝ} (hr : 0 ≤ r) {N K : ℕ}
    (hN : R+r ≤ Real.pi*(N : ℝ)) (hK : N ≤ K) : R ≤ centralCircleRadius K := by
  have hK' : (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  unfold centralCircleRadius
  nlinarith [Real.pi_pos]

/-- Exterior nonvanishing confines all zeros to the central and distant open discs. -/
theorem root_mem_central_or_distant_of_exterior_ne_zero {f : ℂ → ℂ} {R r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {N K : ℕ}
    (hN : R+r ≤ Real.pi*(N : ℝ)) (hK : N ≤ K)
    (hf : ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) → f z ≠ 0)
    {z : ℂ} (hz0 : f z = 0) :
    z ∈ ball 0 (centralCircleRadius K) ∨
      ∃ n : ℤ, K < n.natAbs ∧ z ∈ ball ((Real.pi : ℂ)*n) r := by
  by_cases hz : z ∈ ball 0 (centralCircleRadius K)
  · exact Or.inl hz
  have hzn : centralCircleRadius K ≤ ‖z‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hz
  have hzR := (threshold_le_centralCircleRadius hr.le hN hK).trans hzn
  have hsep : ¬ ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖ := fun h => hf z hzR h hz0
  push Not at hsep
  obtain ⟨n, hn⟩ := hsep
  refine Or.inr ⟨n, ?_, by simpa only [mem_ball, dist_eq_norm] using hn⟩
  by_contra h
  have hnK : (n.natAbs : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_of_not_gt h)
  have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
  have ht := norm_le_norm_sub_add z ((Real.pi : ℂ)*n)
  rw [hnorm] at ht
  unfold centralCircleRadius at hzn
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
