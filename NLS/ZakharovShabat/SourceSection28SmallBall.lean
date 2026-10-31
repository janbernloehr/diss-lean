import NLS.ZakharovShabat.SourceSection28TailEstimate

/-! # The weighted norm in the small-source estimate of Section 28 -/
noncomputable section
open Set
namespace NLS.ZakharovShabat.SourceSection28Data
variable {W₀ W V Wa B U T S : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- On the closed small-norm ball, the complete weighted action sum is controlled
by the same weighted source norm, with the printed constant 2^20. -/
theorem weighted_action_small_ball (Q : SourceSection28Data D A B U T S)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : CoeffPair 2)
    (ha : normalizedWeightedSource w a ∈ S) (hsmall : 8*‖a‖^2 ≤ 1) :
    Summable (fun n : ℤ => (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
    (∑' n : ℤ, (w (2*n))^2*
      ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
      (2:ℝ)^20*‖a‖^2 := by
  have hcut : 8*‖a‖^2 ≤ 1+(0:ℕ) := by simpa using hsmall
  have hs := (Q.weighted_action_tail_corrected w hw a ha 0 hcut).1
  have hb := Q.weighted_action_tail_budget w hw a ha 0 hcut
  simp only [Nat.zero_le,if_true] at hs hb
  have htail : sourceFourierTail 0 a = a := by
    apply WithLp.ofLp_injective
    ext n <;> simp [sourceFourierTail]
  rw [htail] at hb
  norm_num only [Nat.cast_zero,add_zero,div_one] at hb
  refine ⟨hs,hb.trans ?_⟩
  have hx : 0 ≤ ‖a‖^2 := sq_nonneg _
  have hu : ‖a‖^2 ≤ (1/8:ℝ) := by linarith
  have hp := pow_le_pow_left₀ hx hu 2
  norm_num only [div_pow,one_pow] at hp
  have h6 : ‖a‖^6 ≤ ‖a‖^2/64 := by
    have h := mul_le_mul_of_nonneg_right hp hx
    nlinarith [show (‖a‖^2)^2*‖a‖^2 = ‖a‖^6 by ring]
  have hrem : 6*‖a‖^2+1152*‖a‖^6 ≤ 24*‖a‖^2 := by linarith
  have hscale := mul_le_mul (show 1+‖a‖^2 ≤ (9/8:ℝ) by linarith) hrem
    (by positivity : 0 ≤ 6*‖a‖^2+1152*‖a‖^6) (by norm_num : (0:ℝ) ≤ 9/8)
  norm_num
  nlinarith

end NLS.ZakharovShabat.SourceSection28Data
