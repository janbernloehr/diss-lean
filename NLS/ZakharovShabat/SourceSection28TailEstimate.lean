import NLS.ZakharovShabat.SourceSection28Original

/-! # A corrected weighted action tail for Theorem 23.4

Both sums retain the cutoff boundary. The positive factor 1+‖a‖² is
kept, and every action and gap belongs to the retained original family.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ZakharovShabat
namespace SourceSection28Data
variable {W₀ W V Wa B U T S : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- The actual weighted tail bound, with a common inclusive cutoff and the full factor. -/
theorem weighted_action_tail_corrected (Q : SourceSection28Data D A B U T S)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (ha : normalizedWeightedSource w a ∈ S) (N : ℕ) (hN : 8*‖a‖^2 ≤ 1+(N:ℝ)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ else 0) ≤
      4608*(1+‖a‖^2)*(∑' n : ℤ, if N ≤ n.natAbs then
        (w (2*n)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
          (normalizedWeightedSource w a) n‖)^2 else 0) := by
  let f : ℤ → ℝ := fun n => if N ≤ n.natAbs then (w (2*n))^2*
    ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ else 0
  let g : ℤ → ℝ := fun n => if N ≤ n.natAbs then
    (w (2*n)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (normalizedWeightedSource w a) n‖)^2 else 0
  let K : ℝ := 4608*(1+‖a‖^2)
  have hgs : Summable g := (sourceM1_gap_tail w hw a N hN).1
  have hmajor (n : ℤ) : f n ≤ K*g n := by
    by_cases hn : N ≤ n.natAbs
    · have hnr : (N:ℝ) ≤ |(n:ℝ)| := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using (Nat.cast_le.mpr hn : (N:ℝ) ≤ (n.natAbs:ℝ))
      have h := (Q.chi_action_bound w hw a ha n (by linarith)).2
      have h' := mul_le_mul_of_nonneg_left h (sq_nonneg (w (2*n)))
      simpa only [f,g,K,if_pos hn,mul_pow,mul_left_comm] using h'
    · simp only [f,g,if_neg hn,mul_zero,le_refl]
  have hs : Summable f := (hgs.mul_left K).of_nonneg_of_le (fun n => by dsimp [f]; positivity) hmajor
  exact ⟨hs,(hs.tsum_le_tsum hmajor (hgs.mul_left K)).trans_eq tsum_mul_left⟩

/-- Combining the corrected tail with Proposition 25.5 keeps the original Fourier tail. -/
theorem weighted_action_tail_budget (Q : SourceSection28Data D A B U T S)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (ha : normalizedWeightedSource w a ∈ S) (N : ℕ) (hN : 8*‖a‖^2 ≤ 1+(N:ℝ)) :
    (∑' n : ℤ, if N ≤ n.natAbs then (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ else 0) ≤
      4608*(1+‖a‖^2)*(6*‖sourceFourierTail N a‖^2+1152/(1+(N:ℝ))*‖a‖^6) := by
  exact (Q.weighted_action_tail_corrected w hw a ha N hN).2.trans
    (mul_le_mul_of_nonneg_left (sourceM1_gap_tail w hw a N hN).2 (by positivity))

end SourceSection28Data
end NLS.ZakharovShabat
