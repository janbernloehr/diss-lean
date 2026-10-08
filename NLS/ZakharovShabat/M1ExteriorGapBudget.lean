import NLS.ZakharovShabat.M1GapTailEstimate

/-! # The gap-square budget for Lemma 28.1's exterior product -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Proposition 25.5 at a valid cutoff gives the printed quadratic tail budget. -/
theorem M1_canonicalGap_tail_cutoff_budget (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2 else 0) ≤
      3*(1+(N:ℝ))^2 := by
  have h := (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).2
  have ht := pow_le_pow_left₀ (norm_nonneg _)
    (norm_weightedPairFourierTail_le (by simp) w.toWeight (2*N) φ) 2
  have hrem : 1152/(1+(N:ℝ))*‖φ‖^6 ≤ 144*‖φ‖^4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1+(N:ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg (norm_nonneg φ) 4)
    nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 8*‖φ‖^2) hN 2
  have hNN : 1+(N:ℝ) ≤ (1+(N:ℝ))^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  nlinarith

/-- Removing the linear weight leaves a uniform budget of three for every
finite subset of the exterior indices, including cutoff zero. -/
theorem M1_canonicalGap_finite_exterior_sq_le_three (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (s : Finset ℤ)
    (hs : ∀ n ∈ s, N ≤ n.natAbs) :
    (∑ n ∈ s, ‖canonicalPeriodicGap (by simp) (by norm_num)
      (weightedBaseToPair w φ) heven n‖^2) ≤ 3 := by
  let g : ℤ → ℝ := fun n => ‖canonicalPeriodicGap (by simp) (by norm_num)
    (weightedBaseToPair w φ) heven n‖
  let f : ℤ → ℝ := fun n => if N ≤ n.natAbs then (w (2*n)*g n)^2 else 0
  have hf := (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).1
  have hsum : (1+(N:ℝ))^2*(∑ n ∈ s, (g n)^2) ≤ ∑ n ∈ s, f n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hns
    have hn : (N:ℝ) ≤ |(n:ℝ)| := by
      have h : (N:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hs n hns
      simpa only [Nat.cast_natAbs,Int.cast_abs] using h
    have hw' := SpectralWeight.bracket_le_of_hasLinearFactor hw (2*n)
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hw'
    have hweight : 1+(N:ℝ) ≤ w (2*n) := by linarith [abs_nonneg (n:ℝ)]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(N:ℝ)) hweight 2
    dsimp [f]
    rw [if_pos (hs n hns),mul_pow]
    exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
  have hfinite : (∑ n ∈ s, f n) ≤ ∑' n, f n :=
    hf.sum_le_tsum s (fun n _ => by dsimp [f]; split_ifs <;> positivity)
  have hbound := M1_canonicalGap_tail_cutoff_budget w hw φ heven N hN
  have hall : (1+(N:ℝ))^2*(∑ n ∈ s, (g n)^2) ≤ (1+(N:ℝ))^2*3 := by
    nlinarith [hsum.trans (hfinite.trans hbound)]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (1+(N:ℝ))^2)).mp hall

end NLS.ZakharovShabat
