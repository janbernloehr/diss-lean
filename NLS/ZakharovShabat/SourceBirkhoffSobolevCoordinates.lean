import NLS.ZakharovShabat.SourceActionSobolevLowerBound
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2
import NLS.SequenceSpaces.RealHilbertPairFromSquares

/-! # Exact physical Sobolev coordinates of the real Birkhoff map -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Every lower weighted action moment, including total mass, is summable. -/
theorem sourceWeightedAction_summable_lower_on_Hm (m : ℕ) (hm : 1 ≤ m)
    (k : ℕ) (hk : k ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    Summable (sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ k) := by
  apply (sourceWeightedAction_summable_on_Hm m hm a).of_nonneg_of_le
  · intro n
    unfold sourceWeightedActionTerm
    positivity
  · intro n
    unfold sourceWeightedActionTerm
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [abs_nonneg (((2*n:ℤ):ℝ)*Real.pi)]) (by omega)) (norm_nonneg _)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The actual weighted rectangular coordinates have twice the weighted action energy. -/
theorem real_map_weighted_radius
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℕ) (n : ℤ) :
    ((1+|((2*n:ℤ):ℝ)*Real.pi|)^k*(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1 n)^2+
      ((1+|((2*n:ℤ):ℝ)*Real.pi|)^k*(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2 n)^2 =
      2*sourceWeightedActionTerm φ k n := by
  simp only [mul_pow,← pow_mul,Nat.mul_comm k 2,sourceWeightedActionTerm,norm_sourceRealAction]
  rw [← mul_add,D.real_map_action_radius φ n]
  ring

/-- Weighted Birkhoff coordinates form an actual real Hilbert pair at every lower order. -/
def sobolevCoordinates
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    WithLp 2 (RealCoeff 2 × RealCoeff 2) :=
  realHilbertPairFromSquares
    (fun n => (1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s ⟨higherSobolevSourceInclusion m a.val,a.property⟩).1 n)
    (fun n => (1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s ⟨higherSobolevSourceInclusion m a.val,a.property⟩).2 n)
    (by
      have h := (sourceWeightedAction_summable_lower_on_Hm m hm k hk a).mul_left 2
      exact h.congr (fun n => (D.real_map_weighted_radius _ k n).symm))

@[simp] theorem sobolevCoordinates_fst
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m) (a : realTypeHigherSobolevSourceLocus m) (n : ℤ) :
    (D.sobolevCoordinates m hm k hk a).fst n = (1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s ⟨higherSobolevSourceInclusion m a.val,a.property⟩).1 n := rfl

@[simp] theorem sobolevCoordinates_snd
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m) (a : realTypeHigherSobolevSourceLocus m) (n : ℤ) :
    (D.sobolevCoordinates m hm k hk a).snd n = (1+|((2*n:ℤ):ℝ)*Real.pi|)^k*
      (sourceRealBirkhoffMap (by simp) (by norm_num) s ⟨higherSobolevSourceInclusion m a.val,a.property⟩).2 n := rfl

/-- Exact Parseval identity for each weighted real Birkhoff image. -/
theorem sobolevCoordinates_norm_sq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ‖D.sobolevCoordinates m hm k hk a‖^2 =
      2*(∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ k n) := by
  rw [sobolevCoordinates,realHilbertPairFromSquares_norm_sq,← tsum_mul_left]
  exact tsum_congr (fun n => D.real_map_weighted_radius _ k n)

/-- The unweighted Birkhoff norm is the original source L² norm. -/
theorem sobolevCoordinates_zero_norm
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖ = ‖higherSobolevSourceInclusion m a.val‖ := by
  have h := D.sobolevCoordinates_norm_sq m hm 0 (Nat.zero_le m) a
  let φ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  have he : (∑' n : ℤ, sourceWeightedActionTerm φ 0 n) = ‖φ.val‖^2/2 := by
    simp only [sourceWeightedActionTerm,Nat.mul_zero,pow_zero,one_mul,norm_sourceRealAction]
    exact sourceHilbert_sum_actions_eq_half_norm_sq φ
  change ‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖^2 =
    2*(∑' n : ℤ, sourceWeightedActionTerm φ 0 n) at h
  rw [he] at h
  nlinarith [norm_nonneg (D.sobolevCoordinates m hm 0 (Nat.zero_le m) a),
    norm_nonneg (higherSobolevSourceInclusion m a.val)]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
