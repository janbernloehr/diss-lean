import NLS.SequenceSpaces.SobolevPowerMultiplier
import NLS.SequenceSpaces.WeightedDomination

/-! # Recovering root differences from phase differences

A small phase perturbation transfers Sobolev regularity to the root difference and gains one order in its inverse-index remainder.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A phase difference close to minus i times a root difference recovers
the root difference's Sobolev order; inverse-index error gains one order. -/
theorem exists_sobolev_phase_difference_remainder
    (r : ℝ) (a : WeightedCoeff (Weight.sobolev r) p) (d : ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ n, ‖a.val n+I*d n‖ ≤ (1/2:ℝ)*‖d n‖)
    (hdecay : ∀ n : ℤ, (1+|(n:ℝ)|)*‖a.val n+I*d n‖ ≤ C*‖d n‖) :
    ∃ b : WeightedCoeff (Weight.sobolev r) p,
      ∃ e : WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ n, b.val n = d n) ∧ (∀ n, e.val n = a.val n+I*d n) ∧
      ‖b‖ ≤ 2*‖a‖ ∧ ‖e‖ ≤ (2*C)*‖a‖ := by
  classical
  have hd (n : ℤ) : ‖d n‖ ≤ 2*‖a.val n‖ := by
    have h := norm_sub_le (a.val n+I*d n) (a.val n)
    simp only [add_sub_cancel_left,norm_mul,norm_I,one_mul] at h
    linarith [hsmall n]
  obtain ⟨b,hb,hbn⟩ := exists_of_norm_le _ a d 2 (by norm_num) hd
  let m (n : ℤ) : ℂ := if d n = 0 then 0 else (a.val n+I*d n)/d n
  have hm (n : ℤ) : (1+|(n:ℝ)|)*‖m n‖ ≤ C := by
    by_cases hn : d n = 0
    · simpa only [m,if_pos hn,norm_zero,mul_zero] using hC
    · simp only [m,if_neg hn,norm_div]
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr (hdecay n)
  obtain ⟨T,hT,hTn⟩ := exists_sobolev_power_multiplier (p := p) r 1 m C hC
    (by intro n; simpa only [Real.rpow_one] using hm n)
  refine ⟨b,T b,hb,?_,hbn,?_⟩
  · intro n
    rw [hT,hb n]
    by_cases hn : d n = 0
    · have ha0 : a.val n = 0 := norm_eq_zero.mp (le_antisymm
        (by simpa only [hn,mul_zero,add_zero,norm_zero] using hsmall n) (norm_nonneg _))
      simp [m,hn,ha0]
    · simp only [m,if_neg hn]
      exact div_mul_cancel₀ _ hn
  · exact (T.le_opNorm b).trans ((mul_le_mul hTn hbn (norm_nonneg _) hC).trans_eq (by ring))

end NLS.WeightedCoeff
