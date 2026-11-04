import NLS.SequenceSpaces.PositiveSobolevWeight
import NLS.SequenceSpaces.WeightedMultiplier

/-! The literal signed Sobolev bracket max(1,abs(n)), matching the
positive weight n^s on both nonzero half-lattices. -/
noncomputable section
namespace NLS.Weight

def signedSobolev (s : ℝ) : Weight :=
  ⟨fun k => (max 1 |(k:ℝ)|)^s,fun _k => Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) s⟩

theorem signedSobolev_neg (s : ℝ) (k : ℤ) : signedSobolev s (-k)=signedSobolev s k := by
  simp only [signedSobolev,Int.cast_neg,abs_neg]

theorem signedSobolev_zero (s : ℝ) : signedSobolev s 0=1 := by simp [signedSobolev]

theorem signedSobolev_positive (s : ℝ) (k : ℤ) (hk : 0 < k) :
    signedSobolev s k=positiveSobolev s k := by
  have hr : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
  simp only [signedSobolev,positiveSobolev,hk,if_pos,abs_of_nonneg (by linarith : (0:ℝ) ≤ k),max_eq_right hr]

end NLS.Weight
namespace NLS.WeightedCoeff
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def positiveToSignedCLM (s : ℝ) :
    WeightedCoeff (Weight.positiveSobolev s) p →L[ℂ] WeightedCoeff (Weight.signedSobolev s) p :=
  weightedMultiplierCLM _ _ (fun k => if 0 < k then 1 else 0) 1 zero_le_one (by
    intro k
    by_cases hk : 0 < k
    · simp only [if_pos hk,norm_one,mul_one,one_mul,Weight.signedSobolev_positive s k hk]
      exact le_rfl
    · simp only [if_neg hk,norm_zero,mul_zero,one_mul]
      exact (Weight.positiveSobolev s).positive k |>.le)

theorem positiveToSignedCLM_apply (s : ℝ) (a : WeightedCoeff (Weight.positiveSobolev s) p) (k : ℤ) :
    (positiveToSignedCLM s a).val k=if 0 < k then a.val k else 0 := by
  change (if 0 < k then (1:ℂ) else 0)*a.val k=_
  split_ifs <;> simp only [one_mul,zero_mul]

end NLS.WeightedCoeff
