import NLS.ZakharovShabat.SourceH1HigherActionEstimates
import NLS.ZakharovShabat.SourceHilbertActionTrace

/-! # Pointwise and summed action bounds for Lemma 26.2

The high-index comparison costs 8^m times the level-(2m+1) action.
The remaining indices, including zero, cost the explicit central factor.
This positive majorant also proves absolute summability of weighted actions.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The literal summand of the source's weighted action ℓ¹ norm. -/
def sourceWeightedActionTerm (ψ : realTypeSourceSubmodule 2) (m : ℕ) (n : ℤ) : ℝ :=
  (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*‖sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n‖

theorem norm_sourceRealAction (ψ : realTypeSourceSubmodule 2) (n : ℤ) :
    ‖sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n‖ =
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re := by
  have h := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) ψ.val ψ.property n
  have he : sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n =
      ((sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re : ℂ) :=
    Complex.ext rfl (by simpa using h.2.1)
  conv_lhs => rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h.1]

/-- The central frequency weight is controlled by the exact source norm factor. -/
theorem central_action_weight_le (P : ℝ) (hP : 0 ≤ P) (n : ℤ)
    (hn : n = 0 ∨ 1+|(n:ℝ)| < 8*P^2) (m : ℕ) :
    (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m) ≤
      (1+16*Real.pi)^(2*m)*(1+P)^(4*m) := by
  have h1 : 1 ≤ (1+P)^2 := by nlinarith
  have hP2 : P^2 ≤ (1+P)^2 := by nlinarith
  have hbase : 1+|((2*n:ℤ):ℝ)*Real.pi| ≤ (1+16*Real.pi)*(1+P)^2 := by
    have hsmall : 1+|((2*n:ℤ):ℝ)*Real.pi| ≤ 1+16*Real.pi*P^2 := by
      rcases hn with rfl | hn
      · simp only [mul_zero,Int.cast_zero,zero_mul,abs_zero,add_zero]
        have hz : 0 ≤ 16*Real.pi*P^2 := by positivity
        linarith
      · simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
          abs_of_pos (by norm_num : (0:ℝ) < 2)]
        nlinarith [Real.pi_pos]
    have hmul := mul_le_mul_of_nonneg_left hP2 (by positivity : 0 ≤ 16*Real.pi)
    nlinarith
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|((2*n:ℤ):ℝ)*Real.pi|) hbase (2*m)
  calc
    _ ≤ ((1+16*Real.pi)*(1+P)^2)^(2*m) := h
    _ = _ := by
      rw [mul_pow (1+16*Real.pi) ((1+P)^2),← pow_mul]
      congr 2
      omega

/-- Every weighted action is dominated by a summable mass term and a higher-action term. -/
theorem sourceWeightedActionTerm_le (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (m : ℕ) (n : ℤ) :
    sourceWeightedActionTerm ψ m n ≤
      (1+16*Real.pi)^(2*m)*(1+‖φ‖)^(4*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re+
      8^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) := by
  have hI := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp)
    (by norm_num) ψ.val ψ.property n).1
  have hJ := sourceRealHigherAction_even_nonneg (by simp) (by norm_num) ψ n m
  rw [sourceWeightedActionTerm,norm_sourceRealAction]
  by_cases hn : n ≠ 0 ∧ 8*‖φ‖^2 ≤ 1+|(n:ℝ)|
  · have h := (sourceRealHigherAction_H1_exterior_bounds ψ φ hφ n hn.1 hn.2 m).1
    have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2:ℝ)^m)
    have hc : (2:ℝ)^m*((2:ℝ)⁻¹)^m = 1 := by rw [← mul_pow]; norm_num
    have he : (2:ℝ)^m*(4:ℝ)^m = 8^m := by rw [← mul_pow]; norm_num
    have ht : (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*m)*
        (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re ≤
        8^m*sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m) := by
      simpa only [← mul_assoc,hc,he,one_mul] using hh
    exact ht.trans (le_add_of_nonneg_left (by positivity))
  · have hlow : n = 0 ∨ 1+|(n:ℝ)| < 8*‖φ‖^2 := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      · exact Or.inr (lt_of_not_ge (fun h => hn ⟨h0,h⟩))
    exact (mul_le_mul_of_nonneg_right (central_action_weight_le ‖φ‖ (norm_nonneg _) n hlow m) hI).trans
      (le_add_of_nonneg_right (mul_nonneg (by positivity) hJ))

/-- Summability of the unweighted real actions, with no chosen Birkhoff family. -/
theorem sourceRealActions_summable (ψ : realTypeSourceSubmodule 2) :
    Summable (fun n : ℤ => (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re) := by
  obtain ⟨_,_,_,_,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact D.summable_hilbert_realActions ψ

/-- The weighted action sum is bounded once the actual higher-action series is summable. -/
theorem sourceWeightedAction_summable_and_le_higher_sum (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (m : ℕ) (hJ : Summable (fun n : ℤ => sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m))) :
    Summable (sourceWeightedActionTerm ψ m) ∧
    (∑' n : ℤ, sourceWeightedActionTerm ψ m n) ≤
      (1+16*Real.pi)^(2*m)*(1+‖φ‖)^(4*m)*(‖ψ.val‖^2/2)+
      8^m*(∑' n : ℤ, sourceRealHigherAction (by simp) (by norm_num) ψ n (2*m)) := by
  have hI := sourceRealActions_summable ψ
  have hmajor := (hI.mul_left ((1+16*Real.pi)^(2*m)*(1+‖φ‖)^(4*m))).add (hJ.mul_left ((8:ℝ)^m))
  have hs := hmajor.of_nonneg_of_le (fun n => by dsimp [sourceWeightedActionTerm]; positivity)
    (sourceWeightedActionTerm_le ψ φ hφ m)
  refine ⟨hs,?_⟩
  have h := hs.tsum_le_tsum (sourceWeightedActionTerm_le ψ φ hφ m) hmajor
  rwa [Summable.tsum_add (hI.mul_left _) (hJ.mul_left _),tsum_mul_left,tsum_mul_left,
    sourceHilbert_sum_actions_eq_half_norm_sq] at h

end NLS.ZakharovShabat
